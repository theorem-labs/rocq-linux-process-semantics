(* Written by the OSS-Fuzz proof collaborators. *)
(* plan syntax + check (Module AP); spec nodes PMmap/PMmapIn/PMprotect/PSpin *)
(** * AsanPlan — reflective PLAN CHECKER for the ASan-instrumented targets.

    Module [AP] = [AsanPlanCore.APC] (checker state, node checkers, initial
    state, address tables; see its header) + the PLAN syntax ([snode],
    [xnode], [plan]), the node dispatchers [node_sys] / [node_x], and the
    checker [check] itself.  New node families: add the node function to a
    file imported here (it only needs AsanPlanCore), a constructor to
    [snode]/[xnode]/[plan], a dispatch line, and one Section hypothesis in
    AsanPlanSound. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Common Require Import PropExec.
From LinuxProcessSemantics.Common Require Import AxSymExec3.
From LinuxProcessSemantics.Common Require Export AsanPlanCore.
Import ListNotations.
Open Scope Z_scope.

Module AP.
Include APC.
Import AX2.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.     (** variables below nx0 are the INITIAL ones (splits / shapes may only mention those) *)
Variable LIMIT : Z.     (** the run's backing budget (vm_limit): target_alloc_limit *)

(* ######################################################################### *)
(** * 7. Plans                                                                *)
(* ######################################################################### *)

(** one-child (deterministic) syscall nodes.
    mmap and mprotect are NOT deterministic (every arm may be refused) and
    have their own plan constructors [PMmap] / [PMmapIn] / [PMprotect]. *)
Inductive snode : Type :=
| YMunmap      (** munmap of a tracked entry *)
| YBrk         (** brk query (a0 = 0) or a PROVABLY BLOCKED grow *)
| YSetTid.     (** set_tid_address *)

(** extension nodes (no syscall; model unchanged) *)
Inductive xnode : Type :=
| XIMemset     (** sanitizer internal_memset(s, c, n) *)
| XIMemcpy     (** sanitizer internal_memcpy(d, s, n) *)
| XMemset      (** musl memset(s, c, n) *)
| XMemcpy      (** musl memcpy(d, s, n) *)
| XMemIsZero   (** sanitizer mem_is_zero(beg, size), one-sided (all zero) *)
| XEnvScan     (** musl __init_libc: for (i=0; envp[i]; i++); *)
| XPnScan      (** musl __init_libc: program-name scan over argv[0] *)
| XLayout      (** facts about the initial stack image (argument block) *)
| XIStrncpy    (** sanitizer internal_strncpy(dst, "<sealed>", 4095) *)
| XPopFree     (** allocator PopulateFreeArray fill loop; args = [ELit K]: describe the K top cells *)
| XSniff.      (** the library call pni_sniff_header (a summary specific to one target binary) *)

Inductive plan : Type :=
| PRun (stops : list Z) (k : plan)           (** run a block (to an ecall / stop pc / undecidable instruction), then k *)
| PSplit (e : expr) (mid : Z) (k1 k2 : plan) (** value of e <= mid / > mid (e over initial variables) *)
| PCase2 (e : expr) (mid : Z) (k1 k2 : plan) (** the same for ANY e: both children must yield the SAME shape *)
| PCaseDisj (b1 b2 : expr) (k1 k2 : plan)  (** the two sides of a recorded KDisj between ranges based at b1 / b2; same shape *)
| PShDisj (b1 n1 b2 n2 : expr) (k : plan)  (** add: the shadows of the apart 8-aligned app ranges [b1,+n1) [b2,+n2) are apart *)
| PContra                                    (** the knowledge is contradictory (dead branch) *)
| PFact (K : kentry) (k : plan)              (** add a fact the checker verifies from the knowledge *)
| PJoin (b : expr) (off : Z) (n : nat) (k : plan)  (** add KWord (b+off) n (literal) joined from n known literal bytes *)
| PForget (ixs : list nat) (k : plan)        (** drop the knowledge entries at these positions *)
| PDropRange (b : expr) (n : expr) (k : plan) (** drop every memory fact not provably apart from [b, b+n) *)
| PGcKeep (ws : list (expr * expr)) (k : plan) (** drop the content facts outside the keep windows of their base ([kn_keep]) *)
| PBump (m : nat) (k : plan)                 (** raise the next-variable counter to m (>= nxt) *)
| PHavoc (rs : list nat) (k : plan)          (** the listed registers := fresh variables *)
| PHavocBig (K : nat) (k : plan)             (** every register / KWord value with more than K expression nodes := fresh variable *)
| PFresh (r : nat) (logc : Z) (base : option expr) (k : plan)  (** re-spell register r as base + 2^logc * (fresh variable) *)
| PSys (y : snode) (k : plan)                (** one-child syscall node at an ecall *)
| PMmap (krefused kgranted : plan)           (** mmap NULL-hint or FIXED over a free range: -ENOMEM child / grant child *)
| PMmapIn (kkept kok kdestroyed : plan)      (** mmap FIXED inside one tracked entry: -ENOMEM (entry kept) / ok / -ENOMEM (range destroyed) *)
| PMprotect (krefused kgranted : plan)       (** mprotect rw of a PROT_NONE slice: -ENOMEM child / grant child *)
| PBrk2 (kblocked kgranted : plan)           (** brk grow with both outcomes *)
| PX (x : xnode) (args : list expr) (k : plan)   (** extension node *)
| PExt (id : nat) (args : list expr) (k : plan)  (** HOOKED extension node: [XN id args] (node functions supplied to [check]
                                                 by other files: argument-string nodes, file IO ...) *)
| PEmit (id : nat) (args : list expr) (k : plan) (** HOOKED emitting node: [XE id args] = (fd, pieces, state); shape [SEmitP] *)
| PExt2 (id : nat) (args : list expr) (k1 k2 : plan) (** HOOKED two-child node: [XB id args] = (state1, state2); shape [SAlt2] *)
| PLoop (J : nat) (N : expr) (inv : acs) (body k : plan)  (** counted loop: iteration variable EVar J in [0,N),
                                                 invariant template [inv] (havoc registers = EVar v, J < v < nxt inv),
                                                 [body] from inv (+ 0 <= J < N) must reach [PNext] leaves entailing
                                                 inv[J := J+1]; then [k] from inv[J := N] *)
| PNext                                      (** leaf inside a loop body: back at the head, next iteration *)
| PHandoff (h : nat)                         (** hand-off leaf: the state entails the stored state [HS h] *)
| PExit                                      (** exit / exit_group leaf *)
| PSpin                                      (** leaf: the pc holds the sealed runtime's self-loop [jal x0,0] *)
| PFog (i : nat) (sz : Z) (k : plan)          (** fog: tracked entry i becomes a "0 or 1 entry of size <= sz" token *)
| PFogNew (i : nat) (sz : Z) (k : plan)       (** fog: insert such a token (denoting no entry) at position i *)
| PGhost (b n : expr) (k : plan)              (** add the app range [b, b+n) to the budgeted ghost set *)
| PUnvis (b n : expr) (k : plan)              (** the visible range (b, n) becomes a ghost range (shadow must read zero) *)
| PHavocBrk (lo hi : Z) (k : plan)            (** forget the program break: a_brk := fresh variable in [lo, hi] *)
| PIntro (lo hi : Z) (k : plan)               (** introduce a fresh variable known to lie in [lo, hi] (meet-stable facts) *)
| PDiamond (joinpc : Z) (rs : list nat) (k : plan)  (** undecidable conditional branch at pc: run both arms to joinpc, re-join
                                                 (differing registers and [rs] := fresh variables), continue with k *)
| PRename (m : list (nat * nat)) (k : plan)   (** injective renaming of variables >= the GC bound (sources,targets) *)
| PCompact (k : plan)                         (** the canonical dense renaming (first-occurrence order) *)
| PVia (j : nat) (js : acs) (lo : nat) (karms k : plan)  (** INLINE JOIN: check [k] ONCE from the offline join state [js];
                                                 then [karms] from the current state, whose [PMerge j] leaves must entail [js]
                                                 ([entails_h lo (nxt js)]: registers EVar v, lo <= v < nxt js, are havoc slots) *)
| PMerge (j : nat)                            (** leaf inside the arms of [PVia j]: re-join; yields the continuation's shape *)
| PAbstractCell (b : expr) (n : Z) (k : plan) (** the off-image range [b, b+n) covered by the knowledge becomes one KUnk entry *)
| PHavocWords (bs : list expr) (k : plan)    (** the value of the (first) KWord fact at each listed address := fresh variable *)
| PRespell (r : nat) (e : expr) (k : plan)    (** register r := e when the knowledge proves reg r = e ([node_respell]) *)
| PMmapInH (kkept kok kdestroyed : plan).     (** [PMmapIn] whose refused-DESTROYED children remember the punched range as a
                                                 FREE hole (KHOLE token).  No arm maps over the hole any more
                                                 ([APC.mmap_fixed_free] lost its hole path with the vDSO pair) *)

(* ######################################################################### *)
(** * 8'. Node dispatch                                                       *)
(* ######################################################################### *)

Definition node_sys (y : snode) (cs : acs) : option acs :=
  match y with
  | YMunmap => node_munmap A cs
  | YBrk => node_brk1 A cs
  | YSetTid => node_settid nx0 cs
  end.

Definition node_x (x : xnode) (args : list expr) (cs : acs) : option acs :=
  match x with
  | XIMemset => summary_fill A nx0 cs (x_imemset A) 256       (* internal_memset replicates the raw a1: needs c < 256 *)
  | XMemset => summary_fill A nx0 cs (x_memset A) two64
  | XIMemcpy => summary_copy segs A nx0 cs (x_imemcpy A)
  | XMemcpy => summary_copy segs A nx0 cs (x_memcpy A)
  | XMemIsZero => summary_miz A nx0 cs
  | XEnvScan => node_envscan A cs
  | XPnScan => node_pnscan A nx0 cs
  | XLayout => node_layout cs args
  | XIStrncpy => summary_istrncpy A nx0 cs
  | XPopFree => summary_popfree A nx0 cs args
  | XSniff => summary_sniff segs A nx0 cs
  end.

(* ######################################################################### *)
(** * 9. The checker                                                          *)
(* ######################################################################### *)

(** Result of checking: the shape, or a diagnostic (code, remaining plan,
    state): 0 fuel, 1 block run failed (carry side conditions; state = START
    of the block), 2 not at an ecall, 3 node arguments rejected, 4 unknown hole. *)
Inductive cres : Type := COk (s : shape) | CErr (code : Z) (where_ : plan) (cs : acs).

Section Check.
Variable XN : nat -> list expr -> acs -> option acs.                      (** hooked extension nodes [PExt] *)
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).  (** hooked emitting nodes [PEmit] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).              (** hooked two-child nodes [PExt2] *)
Variable HS : nat -> option acs.   (** the stored hand-off states *)
Variable KC : nat.                 (** register cap for the extension-mode executor (0 = off) *)
Variable bfuel : nat.              (** executor fuel per block *)

(** result codes: 0 fuel, 1 block run failed, 2 not at an ecall (PSpin: not at the self-loop), 3 node rejected, 4 unknown hole,
    6 PCase2/PCaseDisj children shapes differ, 7 loop body shape not SNext, 8 PNext outside a loop / PMerge outside its PVia,
    9 variable counter below the loop's havoc range / the PVia's frozen bound *)
(** run the (same) child plan on every state of a non-empty list; all must
    succeed with syntactically equal shapes (used for the destroyed-case list
    of [PMmapIn]); code 6 = shapes differ, 3 = empty list *)
Definition check_all (chk : acs -> plan -> cres) (k : plan) (css : list acs) : cres :=
  match css with
  | [] => CErr 3 k (init_acs_of A)
  | cs0 :: rest =>
      match chk cs0 k with
      | COk s0 =>
          fold_left (fun acc cs => match acc with
                                   | COk s => match chk cs k with
                                              | COk s' => if shape_eqb s s' then COk s else CErr 6 k cs
                                              | err => err
                                              end
                                   | err => err
                                   end) rest (COk s0)
      | err => err
      end
  end.

Fixpoint check (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) {struct fuel} : cres :=
  match fuel with
  | O => CErr 0 p cs
  | S f =>
  let check_in := check in
  let check (f : nat) := check_in f lc in
  (* inside a loop body the variables below the havoc range must stay allocated (and are protected from GC) *)
  let gcb := match lc with Some c => lc_bnd c | None => nx0 end in
  if negb match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end then CErr 9 p cs else
  match p with
  | PRun stops k =>
      match run_block_gc segs IT gcb KC bfuel (stops ++ STOPS A) cs with
      | Some cs' => check f cs' k
      | None => CErr 1 p cs
      end
  | PSplit e mid k1 k2 =>
      if expr_vars_lt nx0 e then
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            match check f (set_kn cs (KRange e lo mid :: kn cs)) k1 with
            | COk s1 =>
                match check f (set_kn cs (KRange e (mid + 1) hi :: kn cs)) k2 with
                | COk s2 => COk (SCase e mid s1 s2)
                | err => err
                end
            | err => err
            end
          else (* decided by range: only the live child, its shape as is *)
            if Z.leb hi mid then check f cs k1 else check f cs k2
      | None => CErr 3 p cs
      end
      else CErr 3 p cs
  | PCase2 e mid k1 k2 =>
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if negb (Z.leb lo mid && Z.ltb mid hi)%bool then (if Z.leb hi mid then check f cs k1 else check f cs k2) else
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            let cs1 := set_kn cs (KRange e lo mid :: kn cs) in
            let cs2 := set_kn cs (KRange e (mid + 1) hi :: kn cs) in
            (* a child whose range fact is contradictory is unreachable: the other's shape *)
            if kn_contra (kn cs1) then check f cs2 k2
            else if kn_contra (kn cs2) then check f cs1 k1
            else
            match check f cs1 k1 with
            | COk s1 =>
                match check f cs2 k2 with
                | COk s2 => if shape_eqb s1 s2 then COk s1 else CErr 6 p cs
                | err => err
                end
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  | PCaseDisj b1 b2 k1 k2 =>
      match node_casedisj cs b1 b2 with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk s1 => match check f csb k2 with
                      | COk s2 => if shape_eqb s1 s2 then COk s1 else CErr 6 p cs
                      | err => err
                      end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PShDisj b1 n1 b2 n2 k => match node_shdisj A cs b1 n1 b2 n2 with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PContra => if kn_contra (kn cs) then COk SNil else CErr 3 p cs
  | PFact K k => if fact_ok (kn cs) K then check f (add_kn cs [K]) k else CErr 3 p cs
  | PJoin b off n k => match node_join segs cs b off n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PForget ixs k => check f (set_kn cs (drop_ixs ixs 0 (kn cs))) k
  | PDropRange b n k => check f (node_droprange cs b n) k
  | PGcKeep ws k => check f (set_kn cs (kn_keep (kn cs) ws)) k
  | PBump m k => match node_bump cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavoc rs k => match node_havoc nx0 cs rs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocBig K k => match node_havocbig nx0 cs K with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PFresh r logc base k => match node_fresh nx0 cs r logc base with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PSys y k =>
      if is_ecall_at segs cs then
        match node_sys y cs with Some cs' => check f cs' k | None => CErr 3 p cs end
      else CErr 2 p cs
  | PBrk2 ka kb =>
      if is_ecall_at segs cs then
        match node_brk2 A LIMIT cs with
        | Some (csa, csb) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => COk (salt2 sa sb)
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmap ka kb =>
      if is_ecall_at segs cs then
        match node_mmap2 A nx0 LIMIT cs with
        | Some (csa, csb) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => COk (salt2 sa sb)
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmapIn ka kb kc =>
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT false cs with
        | Some (csa, csb, cscs) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => match check_all (check f) kc cscs with
                                    | COk sc => COk (salt2 sa (salt2 sb sc))
                                    | err => err
                                    end
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmapInH ka kb kc =>      (* as PMmapIn, destroyed children with the hole token *)
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT true cs with
        | Some (csa, csb, cscs) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => match check_all (check f) kc cscs with
                                    | COk sc => COk (salt2 sa (salt2 sb sc))
                                    | err => err
                                    end
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMprotect ka kb =>
      if is_ecall_at segs cs then
        match node_mprotect2 A LIMIT cs with
        | Some (csa, csb) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => COk (salt2 sa sb)
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PX x args k => match node_x x args cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PExt id args k => match XN id args cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PEmit id args k =>
      match XE id args cs with
      | Some (fd, ps, cs') => match check f cs' k with COk s => COk (SEmitP fd ps s) | err => err end
      | None => CErr 3 p cs
      end
  | PExt2 id args k1 k2 =>
      match XB id args cs with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk sa => match check f csb k2 with COk sb => COk (SAlt2 sa sb) | err => err end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PLoop J N inv body k =>
      match loop_ok nx0 cs J N inv with
      | Some nhi =>
          let lo := S J in let hi := nxt inv in
          if (Z.eqb (pc inv) (pc cs) && entails_h A lo hi cs (inst inv J (ELit 0)))%bool then
            match check_in f (Some (LC (pc cs) (inst inv J (eaddz (EVar J) 1)) lo hi)) (loop_body_state J N nhi inv) body with
            | COk SNext => check f (inst inv J N) k
            | COk _ => CErr 7 p cs
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  | PNext =>
      match lc with
      | Some (LC h nx lo hi) =>
          if (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool then COk SNext else CErr 3 p cs
      | _ => CErr 8 p cs
      end
  | PHandoff h =>
      match HS h with
      | Some ch => if entails cs ch then COk (SHole h) else CErr 3 p cs
      | None => CErr 4 p cs
      end
  | PExit =>
      if is_ecall_at segs cs then
        match node_exit cs with Some code => COk (SExit code) | None => CErr 3 p cs end
      else CErr 2 p cs
  | PSpin => if node_spin segs cs then COk SNil else CErr 2 p cs
  | PFog i sz k => match node_fog cs i sz with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PFogNew i sz k => match node_fognew cs i sz with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PGhost b n k => match node_ghost LIMIT cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PUnvis b n k => match node_unvis A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocBrk lo hi k => match node_havocbrk nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PIntro lo hi k => match node_intro nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PRename m k => match node_rename gcb cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PCompact k => match node_compact gcb cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PVia j js lo karms k =>
      if via_ok nx0 cs js lo then
        match check f js k with
        | COk sk => check_in f (Some (JC j js sk (nxt cs) lo)) cs karms
        | err => err
        end
      else CErr 3 p cs
  | PMerge j =>
      match lc with
      | Some (JC j' js sk b lo) =>
          if (Nat.eqb j j' && Z.eqb (pc cs) (pc js) && shape_vars_lt nx0 sk && entails_h A lo (nxt js) cs js)%bool
          then COk sk else CErr 3 p cs
      | _ => CErr 8 p cs
      end
  | PAbstractCell b n k => match node_abstractcell A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocWords bs k => match node_havocwords nx0 cs bs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PRespell r e k => match node_respell cs r e with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PDiamond joinpc rs k =>
      match branch_probe IT cs with
      | Some e =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              (* decided after all (by range): ONE arm = [PRun [joinpc] k] *)
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs with
                | Some cs' => if Z.eqb (pc cs') joinpc then check f cs' k else CErr 3 p cs'
                | None => CErr 1 p cs
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs1 with
                | Some ca =>
                    match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs2 with
                    | Some cb =>
                        match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                        | Some csj => check f csj k
                        | None => CErr 3 p ca    (* arms do not re-join: state = end of arm 1 (probe = 0) *)
                        end
                    | None => CErr 1 p cs2
                    end
                | None => CErr 1 p cs1
                end
          | None => CErr 3 p cs
          end
      | None => CErr 2 p cs                  (* not at a conditional branch *)
      end
  end
  end.
End Check.

End WithSegs.
End AP.
