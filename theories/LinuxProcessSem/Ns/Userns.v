(** * LinuxProcessSem.Ns.Userns — user namespaces, their id maps, and capabilities over them

    Pure functions over the table of user namespaces.

    Linux 6.18.44 sources:
    - an id seen through a map: [map_id_range_down], [map_id_range_down_base]
      (kernel/user_namespace.c); [map_id] is the one-id case, [map_range]
      the range case that [map_write] uses;
    - a capability over a namespace: [cap_capable] and [cap_capable_helper]
      (security/commoncap.c): the credential's effective set when the
      target is its own namespace; nothing when the target is not below it;
      everything when the target's parent is the credential's namespace and
      the target is owned by the credential's euid; else the same question
      of the target's parent;
    - a write to [uid_map] or [gid_map]: [proc_uid_map_write],
      [proc_gid_map_write], [map_write], [mappings_overlap],
      [new_idmap_permitted], [verify_root_map] (kernel/user_namespace.c),
      with [simple_strtoul] (lib/vsprintf.c) and [isspace] (lib/ctype.c) for
      the parse: the checks in kernel order, the map installed once, the
      lower ids stored as kernel ids;
    - a write to [setgroups]: [proc_setgroups_write];
    - a new user namespace: [create_user_ns] refuses a parent above level 32
      with ENOSPC, starts with no maps, copies the parent's setgroups state
      and records whether the creator held CAP_SETFCAP
      ([parent_could_setfcap]).  The per-user count limit, the chrooted and
      unmapped-owner refusals read state this table does not hold and
      belong to the arm.

    A write's copy from user memory ([memdup_user_nul], [copy_from_user])
    is the arm's: these functions take the bytes. *)

From Stdlib Require Import List PArith ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables.
Import ListNotations.
Local Open Scope Z_scope.

Inductive NsResult (A : Type) :=
  | NsOk  (x : A)
  | NsErr (e : Z).
Arguments NsOk {A} x.
Arguments NsErr {A} e.

Definition U32 : Z := 4294967296.
Definition INT_MAX : Z := 2147483647.

(** The id [x] maps to, through the first extent that holds it. *)
Fixpoint map_id (exts : list IdExtent) (x : Z) : option Z :=
  match exts with
  | [] => None
  | e :: r =>
      if (ext_first e <=? x) && (x <? ext_first e + ext_count e)
      then Some (ext_lower e + (x - ext_first e))
      else map_id r x
  end.

(** [map_id_range_down]: the range [x, x + n) through the first extent that
    holds all of it; [None] for (u32) -1, which the kernel also reads as
    failure. *)
Fixpoint map_range (exts : list IdExtent) (x n : Z) : option Z :=
  match exts with
  | [] => None
  | e :: r =>
      if (ext_first e <=? x) && (x + n - 1 <? ext_first e + ext_count e)
      then let y := ext_lower e + (x - ext_first e) in
           if y =? U32 - 1 then None else Some y
      else map_range r x n
  end.

Definition find_userns (U : list UserNs) (i : positive) : option UserNs :=
  find (fun u => Pos.eqb (uns_id u) i) U.

(* =========================================================================
   Capabilities over a namespace
   ========================================================================= *)

Definition CAP_SETGID : Z := 6.
Definition CAP_SETUID : Z := 7.
Definition CAP_SYS_ADMIN : Z := 21.
Definition CAP_SETFCAP : Z := 31.

Fixpoint cap_capable_fuel (fuel : nat) (U : list UserNs) (c : IdCred) (target : positive) (cap : Z)
    : bool :=
  match fuel with
  | O => false
  | Datatypes.S f =>
      if Pos.eqb target (ic_ns c) then Z.testbit (ic_effective c) cap
      else match find_userns U target, find_userns U (ic_ns c) with
           | Some t, Some cn =>
               if Nat.leb (uns_level t) (uns_level cn) then false
               else match uns_parent t with
                    | Some p =>
                        if Pos.eqb p (ic_ns c) && (uns_owner t =? ic_euid c) then true
                        else cap_capable_fuel f U c p cap
                    | None => false
                    end
           | _, _ => false
           end
  end.

(** [cap_capable]: does [c] hold [cap] over namespace [target]?  The fuel,
    one more than the table's length, outlasts any chain of parents. *)
Definition cap_capable (U : list UserNs) (c : IdCred) (target : positive) (cap : Z) : bool :=
  cap_capable_fuel (Datatypes.S (length U)) U c target cap.

(* =========================================================================
   The parse of a written map
   ========================================================================= *)

(** [isspace] of the kernel's [_ctype] table: space, the five controls from
    tab to carriage return, and 0xa0. *)
Definition is_space (c : Z) : bool := (c =? 32) || ((9 <=? c) && (c <=? 13)) || (c =? 160).

Fixpoint skip_spaces (l : list Z) : list Z :=
  match l with
  | c :: r => if is_space c then skip_spaces r else l
  | [] => []
  end.

(** [simple_strtoul] in base 10: the digits from the start, the value
    modulo 2^64, and what follows them. *)
Fixpoint strtoul (acc : Z) (l : list Z) : Z * list Z :=
  match l with
  | c :: r =>
      if (48 <=? c) && (c <=? 57) then strtoul ((acc * 10 + (c - 48)) mod 2 ^ 64) r
      else (acc, l)
  | [] => (acc, [])
  end.

(** The kernel's buffer ends at the first NUL ([memdup_user_nul] adds one
    after the written bytes). *)
Fixpoint upto_nul (l : list Z) : list Z :=
  match l with
  | c :: r => if c =? 0 then [] else c :: upto_nul r
  | [] => []
  end.

(** The line before the first newline, and what follows the newline. *)
Fixpoint split_line (l : list Z) : list Z * option (list Z) :=
  match l with
  | c :: r =>
      if c =? 10 then ([], Some r)
      else let (a, b) := split_line r in (c :: a, b)
  | [] => ([], None)
  end.

Definition head_space (l : list Z) : bool :=
  match l with c :: _ => is_space c | [] => false end.

(** One line: three numbers, each followed by white space but the last,
    and nothing after the last but white space. *)
Definition parse_line (l : list Z) : option IdExtent :=
  let (a, p1) := strtoul 0 (skip_spaces l) in
  if negb (head_space p1) then None else
  let (b, p2) := strtoul 0 (skip_spaces p1) in
  if negb (head_space p2) then None else
  let (n, p3) := strtoul 0 (skip_spaces p2) in
  match p3 with
  | c :: _ => if is_space c then
                match skip_spaces p3 with
                | [] => Some (mkExtent (a mod U32) (b mod U32) (n mod U32))
                | _ :: _ => None
                end
              else None
  | [] => Some (mkExtent (a mod U32) (b mod U32) (n mod U32))
  end.

(** [mappings_overlap]: the new extent's upper or lower range meets one of
    an earlier extent. *)
Definition extents_meet (e prev : IdExtent) : bool :=
  ((ext_first prev <=? ext_first e + ext_count e - 1)
   && (ext_first e <=? ext_first prev + ext_count prev - 1))
  || ((ext_lower prev <=? ext_lower e + ext_count e - 1)
      && (ext_lower e <=? ext_lower prev + ext_count prev - 1)).

(** The checks [map_write] makes on one parsed line against the extents
    before it: neither start is (u32) -1, neither range wraps 32 bits (a
    count of 0 counts as wrapping), no overlap. *)
Definition extent_admitted (prev : list IdExtent) (e : IdExtent) : bool :=
  negb (ext_first e =? U32 - 1) && negb (ext_lower e =? U32 - 1)
  && (ext_first e <? (ext_first e + ext_count e) mod U32)
  && (ext_lower e <? (ext_lower e + ext_count e) mod U32)
  && negb (existsb (extents_meet e) prev).

Fixpoint parse_lines (fuel : nat) (prev : list IdExtent) (l : list Z) : option (list IdExtent) :=
  match fuel with
  | O => None
  | Datatypes.S f =>
      let (line, rest) := split_line l in
      let next := match rest with Some (_ :: _) => rest | _ => None end in
      match parse_line line with
      | None => None
      | Some e =>
          if negb (extent_admitted prev e) then None
          else if Nat.eqb (Datatypes.S (length prev)) 340 && match next with Some _ => true | None => false end
          then None
          else match next with
               | None => Some (prev ++ [e])
               | Some r => parse_lines f (prev ++ [e]) r
               end
      end
  end.

(** The extents a write's bytes give, or [None] where [map_write] answers
    EINVAL. *)
Definition parse_map (bytes : list Z) : option (list IdExtent) :=
  parse_lines (Datatypes.S (length bytes)) [] (upto_nul bytes).

(* =========================================================================
   Map writes
   ========================================================================= *)

Inductive MapKind := UidMap | GidMap.

Definition the_map (k : MapKind) (u : UserNs) : option (list IdExtent) :=
  match k with UidMap => uns_uid_map u | GidMap => uns_gid_map u end.

Definition set_map (k : MapKind) (u : UserNs) (m : list IdExtent) : UserNs :=
  mkUserNs (uns_id u) (uns_parent u) (uns_level u) (uns_owner u)
           (match k with UidMap => Some m | GidMap => uns_uid_map u end)
           (match k with GidMap => Some m | UidMap => uns_gid_map u end)
           (uns_setgroups_allowed u) (uns_parent_could_setfcap u) (uns_max_userns u) (uns_sealed u).

Definition written (o : option (list IdExtent)) : bool :=
  match o with Some (_ :: _) => true | _ => false end.

Definition replace_userns (U : list UserNs) (u : UserNs) : list UserNs :=
  map (fun x => if Pos.eqb (uns_id x) (uns_id u) then u else x) U.

(** [verify_root_map]: a map that sends some id to lower id 0 needs the
    namespace's creator to have held CAP_SETFCAP, when the opener is in
    the namespace, or else the opener to hold CAP_SETFCAP over the parent. *)
Definition verify_root_map (U : list UserNs) (ns : UserNs) (opener : IdCred)
    (m : list IdExtent) : bool :=
  if negb (existsb (fun e => ext_lower e =? 0) m) then true
  else if Pos.eqb (uns_id ns) (ic_ns opener) then uns_parent_could_setfcap ns
  else match uns_parent ns with
       | Some p => cap_capable U opener p CAP_SETFCAP
       | None => false
       end.

(** [new_idmap_permitted], for a namespace with parent [parent]. *)
Definition new_idmap_permitted (U : list UserNs) (ns parent : UserNs) (k : MapKind)
    (opener writer : IdCred) (m : list IdExtent) : bool :=
  let cap := match k with UidMap => CAP_SETUID | GidMap => CAP_SETGID end in
  if (match k with UidMap => negb (verify_root_map U ns opener m) | GidMap => false end)
  then false
  else if (match m with
           | [e] => (ext_count e =? 1) && (uns_owner ns =? ic_euid opener)
                    && (match k with
                        | UidMap =>
                            match option_map (fun pm => map_id pm (ext_lower e)) (uns_uid_map parent) with
                            | Some (Some x) => x =? ic_euid opener
                            | _ => false
                            end
                        | GidMap =>
                            negb (uns_setgroups_allowed ns)
                            && match option_map (fun pm => map_id pm (ext_lower e)) (uns_gid_map parent) with
                               | Some (Some x) => x =? ic_egid opener
                               | _ => false
                               end
                        end)
           | _ => false
           end)
  then true
  else cap_capable U writer (uns_id parent) cap && cap_capable U opener (uns_id parent) cap.

(** Every lower range through the parent's map, or [None] when one is not
    mapped. *)
Fixpoint lower_to_kernel (pm : list IdExtent) (m : list IdExtent) : option (list IdExtent) :=
  match m with
  | [] => Some []
  | e :: r =>
      match map_range pm (ext_lower e) (ext_count e), lower_to_kernel pm r with
      | Some y, Some r' => Some (mkExtent (ext_first e) y (ext_count e) :: r')
      | _, _ => None
      end
  end.

(** A write of [bytes] at offset [ppos] to the [k] map file of namespace
    [target], opened by [opener] and written by [writer]: the new table, or
    the errno, in [proc_uid_map_write]'s and [map_write]'s order. *)
Definition map_write (U : list UserNs) (target : positive) (k : MapKind) (opener writer : IdCred)
    (ppos : Z) (bytes : list Z) : NsResult (list UserNs) :=
  match find_userns U target with
  | None => NsErr EINVAL
  | Some ns =>
      match uns_parent ns with
      | None => NsErr EPERM
      | Some pid =>
          match find_userns U pid with
          | None => NsErr EINVAL
          | Some parent =>
              if negb (Pos.eqb (ic_ns opener) target || Pos.eqb (ic_ns opener) pid) then NsErr EPERM
              else if negb (ppos =? 0) || (4096 <=? Z.of_nat (length bytes)) then NsErr EINVAL
              else if written (the_map k ns) then NsErr EPERM
              else if negb (cap_capable U opener target CAP_SYS_ADMIN) then NsErr EPERM
              else match parse_map bytes with
                   | None => NsErr EINVAL
                   | Some m =>
                       if negb (new_idmap_permitted U ns parent k opener writer m) then NsErr EPERM
                       else match the_map k parent with
                            | None => NsErr EPERM
                            | Some pm =>
                                match lower_to_kernel pm m with
                                | None => NsErr EPERM
                                | Some m' => NsOk (replace_userns U (set_map k ns m'))
                                end
                            end
                   end
          end
      end
  end.

(** A map write that succeeds installs the map in the target namespace,
    whose map of that kind was not written before. *)
Theorem map_write_installs : forall U target k opener writer ppos bytes U',
  map_write U target k opener writer ppos bytes = NsOk U' ->
  exists ns m, find_userns U target = Some ns /\ written (the_map k ns) = false
               /\ In (set_map k ns m) U'.
Proof.
  intros U target k opener writer ppos bytes U'. unfold map_write.
  destruct (find_userns U target) as [ns|] eqn:Hf; cbv beta iota; [|intros Hc; discriminate Hc].
  destruct (uns_parent ns) as [pid|]; cbv beta iota; [|intros Hc; discriminate Hc].
  destruct (find_userns U pid) as [parent|]; cbv beta iota; [|intros Hc; discriminate Hc].
  destruct (negb (Pos.eqb (ic_ns opener) target || Pos.eqb (ic_ns opener) pid)); cbv beta iota;
    [intros Hc; discriminate Hc|].
  destruct (negb (ppos =? 0) || (4096 <=? Z.of_nat (length bytes))); cbv beta iota;
    [intros Hc; discriminate Hc|].
  destruct (written (the_map k ns)) eqn:Hw; cbv beta iota; [intros Hc; discriminate Hc|].
  destruct (negb (cap_capable U opener target CAP_SYS_ADMIN)); cbv beta iota;
    [intros Hc; discriminate Hc|].
  destruct (parse_map bytes) as [m|]; cbv beta iota; [|intros Hc; discriminate Hc].
  destruct (negb (new_idmap_permitted U ns parent k opener writer m)); cbv beta iota;
    [intros Hc; discriminate Hc|].
  destruct (the_map k parent) as [pm|]; cbv beta iota; [|intros Hc; discriminate Hc].
  destruct (lower_to_kernel pm m) as [m'|]; cbv beta iota; [|intros Hc; discriminate Hc].
  intros H. injection H as HU. subst U'.
  exists ns, m'. split; [first [reflexivity | exact Hf]|]. split; [exact Hw|].
  unfold find_userns in Hf. apply find_some in Hf. destruct Hf as [Hin Hid].
  cbv beta in Hid. apply Pos.eqb_eq in Hid.
  unfold replace_userns. apply in_map_iff. exists ns. split; [|exact Hin]. cbv beta.
  replace (uns_id (set_map k ns m')) with (uns_id ns) by reflexivity.
  rewrite Pos.eqb_refl. reflexivity.
Qed.

(* =========================================================================
   The setgroups file
   ========================================================================= *)

Definition set_setgroups (u : UserNs) (b : bool) : UserNs :=
  mkUserNs (uns_id u) (uns_parent u) (uns_level u) (uns_owner u) (uns_uid_map u) (uns_gid_map u)
           b (uns_parent_could_setfcap u) (uns_max_userns u) (uns_sealed u).

Definition starts_with (pre l : list Z) : option (list Z) :=
  if Nat.leb (length pre) (length l) && forallb (fun p => fst p =? snd p) (combine pre l)
  then Some (skipn (length pre) l) else None.

(** [proc_setgroups_write]: "allow" or "deny", then only white space;
    allow is refused once denied, deny once the gid map is written. *)
Definition setgroups_write (U : list UserNs) (target : positive) (ppos : Z) (bytes : list Z)
    : NsResult (list UserNs) :=
  if negb (ppos =? 0) || (8 <=? Z.of_nat (length bytes)) then NsErr EINVAL
  else
    let s := upto_nul bytes in
    let req := match starts_with [97; 108; 108; 111; 119] s with
               | Some r => Some (true, r)
               | None => match starts_with [100; 101; 110; 121] s with
                         | Some r => Some (false, r)
                         | None => None
                         end
               end in
    match req with
    | None => NsErr EINVAL
    | Some (allow, rest) =>
        match skip_spaces rest with
        | _ :: _ => NsErr EINVAL
        | [] =>
            match find_userns U target with
            | None => NsErr EINVAL
            | Some ns =>
                if allow then (if uns_setgroups_allowed ns then NsOk U else NsErr EPERM)
                else if written (uns_gid_map ns) then NsErr EPERM
                else NsOk (replace_userns U (set_setgroups ns false))
            end
        end
    end.

(* =========================================================================
   A new user namespace
   ========================================================================= *)

Definition max_userns_id (U : list UserNs) : positive :=
  fold_left (fun acc u => Pos.max acc (uns_id u)) U 1%positive.

(** [create_user_ns] under [parent], owned by kuid [owner];
    [could_setfcap] is whether the creator's effective set holds
    CAP_SETFCAP. *)
Definition create_user_ns (U : list UserNs) (parent : positive) (owner : Z) (could_setfcap : bool)
    : NsResult (positive * list UserNs) :=
  match find_userns U parent with
  | None => NsErr EINVAL
  | Some p =>
      if Nat.ltb 32%nat (uns_level p) then NsErr ENOSPC
      else NsOk (Pos.succ (max_userns_id U),
                 mkUserNs (Pos.succ (max_userns_id U)) (Some parent)
                          (Datatypes.S (uns_level p)) owner None None
                          (uns_setgroups_allowed p) could_setfcap INT_MAX true :: U)
  end.

(** A created namespace is a child of the parent, one level below it, owned
    by the creator, with no maps, and with the parent's setgroups state. *)
Theorem create_user_ns_child : forall U parent owner fc i U',
  create_user_ns U parent owner fc = NsOk (i, U') ->
  exists p, find_userns U parent = Some p
    /\ find_userns U' i
       = Some (mkUserNs i (Some parent) (Datatypes.S (uns_level p)) owner None None
                        (uns_setgroups_allowed p) fc INT_MAX true).
Proof.
  intros U parent owner fc i U'. unfold create_user_ns.
  destruct (find_userns U parent) as [p|]; [|intros Hc; discriminate Hc].
  destruct (Nat.ltb 32%nat (uns_level p)); [intros Hc; discriminate Hc|].
  intros H. injection H as Hi HU. subst i U'.
  exists p. split; [reflexivity|].
  unfold find_userns. cbn [find uns_id]. rewrite Pos.eqb_refl. reflexivity.
Qed.

(** A parent above level 32 gets ENOSPC. *)
Theorem create_user_ns_too_deep : forall U parent owner fc p,
  find_userns U parent = Some p -> (32 < uns_level p)%nat ->
  create_user_ns U parent owner fc = NsErr ENOSPC.
Proof.
  intros U parent owner fc p Hf Hl. unfold create_user_ns. rewrite Hf. cbv iota.
  apply Nat.ltb_lt in Hl. rewrite Hl. reflexivity.
Qed.

(* =========================================================================
   The count of user namespaces ([inc_ucount], kernel/ucount.c)
   ========================================================================= *)

(** [x] and its ancestors, [x] first. *)
Fixpoint ancestry_fuel (fuel : nat) (U : list UserNs) (x : UserNs) : list UserNs :=
  match fuel with
  | O => []
  | Datatypes.S f =>
      x :: match uns_parent x with
           | Some p => match find_userns U p with Some px => ancestry_fuel f U px | None => [] end
           | None => []
           end
  end.

Definition ancestry (U : list UserNs) (x : UserNs) : list UserNs :=
  ancestry_fuel (Datatypes.S (length U)) U x.

(** The (namespace, kuid) pairs [inc_ucount] charges for a new namespace
    under [parent] owned by [owner]: (parent, owner), then for each
    ancestor-or-self [a] of [parent] that has a parent, (that parent, the
    owner of [a]). *)
Definition charge_chain (U : list UserNs) (parent : UserNs) (owner : Z) : list (UserNs * Z) :=
  (parent, owner)
  :: flat_map (fun a => match uns_parent a with
                        | Some p => match find_userns U p with Some pa => [(pa, uns_owner a)] | None => [] end
                        | None => []
                        end) (ancestry U parent).

(** The user namespaces of [xs] charged to ([t], [uid]): those with an
    ancestor-or-self whose parent is [t] and whose owner is [uid]. *)
Definition charged_among (U xs : list UserNs) (t : positive) (uid : Z) : Z :=
  Z.of_nat (length (List.filter
    (fun x => existsb (fun a => match uns_parent a with
                                | Some p => Pos.eqb p t && (uns_owner a =? uid)
                                | None => false
                                end) (ancestry U x)) xs)).

(** The count [inc_ucount] meets at ([t], [uid]) lies between two bounds.
    The model keeps every namespace it made, but Linux frees a namespace
    when nothing holds it, so the table's count is an upper bound
    ([charged_count]).  The caller's own namespace and its ancestors are
    held (the caller is in the first, each holds its parent), so those of
    them that are charged are a lower bound ([charged_alive]). *)
Definition charged_count (U : list UserNs) (t : positive) (uid : Z) : Z := charged_among U U t uid.

Definition charged_alive (U : list UserNs) (caller : positive) (t : positive) (uid : Z) : Z :=
  match find_userns U caller with
  | Some c => charged_among U (ancestry U c) t uid
  | None => 0
  end.

(** [inc_ucount]'s answer for a new namespace made by a task in user
    namespace [caller]: every charge fits ([atomic_long_inc_below]: the
    count below the limit) when each level is sealed and even the table's
    count is below its limit; ENOSPC when at some sealed level the held
    namespaces alone reach the limit; else either, the count of a level
    not being known. *)
Inductive Charge := ChargeOk | ChargeFull | ChargeEither.

Definition ucount_check (U : list UserNs) (caller : positive) (parent : UserNs) (owner : Z) : Charge :=
  let chain := charge_chain U parent owner in
  if existsb (fun p => uns_sealed (fst p)
                       && negb (charged_alive U caller (uns_id (fst p)) (snd p) <? uns_max_userns (fst p)))
             chain
  then ChargeFull
  else if forallb (fun p => uns_sealed (fst p)
                            && (charged_count U (uns_id (fst p)) (snd p) <? uns_max_userns (fst p)))
                  chain
  then ChargeOk
  else ChargeEither.

(** [kuid_has_mapping] / [kgid_has_mapping]: some extent's lower range
    holds the kernel id; an unwritten map holds none. *)
Definition kid_has_mapping (o : option (list IdExtent)) (x : Z) : bool :=
  match o with
  | Some exts => existsb (fun e => (ext_lower e <=? x) && (x <? ext_lower e + ext_count e)) exts
  | None => false
  end.

Definition set_max_userns (u : UserNs) (v : Z) : UserNs :=
  mkUserNs (uns_id u) (uns_parent u) (uns_level u) (uns_owner u) (uns_uid_map u) (uns_gid_map u)
           (uns_setgroups_allowed u) (uns_parent_could_setfcap u) v (uns_sealed u).
