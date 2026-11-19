(** * Common.FileSim — union-of-resolutions glue for file-copying binaries.

    TRUST BOUNDARY: shared proof library, not the trusted specification.
    Image-INDEPENDENT.

    Conventions:

    - outcomes are [(word * Fs.Fs)] pairs (exit code is a [word]); the
      masked exit code is [bv_and (ms_gpr ms 0) (Z_to_bv 64 255)];
    - syscall numbers are Z-characterized: the pending number [x8] is
      quantified with [bv_unsigned x8 = 56/57/63/64%Z] (mirroring
      CatSim's [tw_write] / StreamSim's [read0_*]);
    - errnos are [Z] ([Te : Z -> _]); fds are [word]s bounded by
      [(bv_unsigned fd < 2^31)%Z]; open-flag arithmetic is [Z.ldiff]
      over [bv_unsigned];
    - the raw-ecall records carry the [ms_resv := None] field and a
      [bvmap 5 word] register file ([reg_get regs 10/11/12] are
      a0/a1/a2, [getr regs 17] is a7); post-syscall states collapse to
      [mkst ... (v_addi pc 4) ...];
    - file offsets/counts are [word]s bridged with [word_to_nat]; the
      read-effect return value is [len_word bs] and offsets advance by
      [bv] addition ([off + len_word bs], the Specs.v spelling).

    A binary whose only observables are its exit code and the FINAL FILE
    SYSTEM (no channel I/O at all: openat/close and file read/write emit
    no trace events) has as behavior a UNION over syscall resolutions of
    (exit code, final fs) outcomes.  This file provides:

    - [to_fout segs ms model U]: from machine state [ms] and model
      [model], the reachable set of (code, fs) outcomes is EXACTLY [U].
      Leaves are exit ecalls; interior nodes are event-free,
      never-halting, never-erroring syscalls branching over every
      admissible resolution ([tfo_sys]).
    - the trace characterization ([fout_obs_iff]): [obs_trace] is
      exactly the prefixes of [[ExitEv code fs]] for the outcomes in
      [U]; plus no-error ([fout_no_error_run]) and the
      [Equivalence.equiv]-level glue ([fout_strong_equiv]).
    - per-syscall decoding through the verified checker for the
      file-system surface: openat (O_RDONLY hit/miss and
      O_WRONLY|O_CREAT|O_TRUNC), file read, file write, close — as
      ergonomic [to_fout] nodes.
    - [read_cstr] bridges (path strings out of argv stack memory),
      fs/fd-table algebra, and [file_read]/[file_write] arithmetic for
      the copy-loop bookkeeping.
    - may-error reachability helpers ([msteps_spec_err_error],
      [reaches_error_star]) plus the stronger universal-error helper
      [msteps_spec_err_all_traces_error] for deterministic Unmodeled paths.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Common Require Import SimInv ExitSim PropExec CatSim CatExec ErrEscape SeqExec StreamExec StreamSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.

Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* ========================================================================= *)
(* Model plumbing                                                            *)
(* ========================================================================= *)

Lemma with_fds_fs : forall f m, m_fs (with_fds f m) = m_fs m.
Proof. reflexivity. Qed.
Lemma with_fds_halted : forall f m, m_halted (with_fds f m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_fds_fds : forall f m, m_fds (with_fds f m) = f.
Proof. reflexivity. Qed.
Lemma with_fs_fs : forall f m, m_fs (with_fs f m) = f.
Proof. reflexivity. Qed.
Lemma with_fs_halted : forall f m, m_halted (with_fs f m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_fs_fds : forall f m, m_fds (with_fs f m) = m_fds m.
Proof. reflexivity. Qed.

(** The argument-register index lemmas [arg_reg_0/1/2] live in
    [Common.PropExec] (imported above), so they are shared across the
    Common sim/exec files and every FileSim-based example. *)

(** advance-past-svc of a ret-only effect at the raw ecall record. *)
Lemma adv_eff_ret : forall regs pc x8 mem rom r,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
  intros regs pc x8 mem rom r.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes apply_zeros].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(** Copy-in provenance does not change the machine-state transition. *)
Lemma adv_eff_ret_copyins : forall regs pc x8 mem rom r copyins,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (with_copyins copyins (mkEffect r [] [])))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
  intros regs pc x8 mem rom r copyins.
  unfold with_copyins.
  apply adv_eff_ret.
Qed.

(* ========================================================================= *)
(* sys_input projections                                                     *)
(* ========================================================================= *)

Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Lemma in_arg0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
Lemma in_arg1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma in_arg2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
Lemma in_wmem_si : forall segs ms x8,
  in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(* fs algebra (fs_set / fs_lookup)                                           *)
(* ========================================================================= *)

Lemma path_eqb_neq : forall p q, p <> q -> path_eqb p q = false.
Proof.
  intros p q Hne. destruct (path_eqb p q) eqn:E; [|reflexivity].
  apply path_eqb_eq in E. congruence.
Qed.

(** A PLAIN NAME IS NOT A KEY of a well-formed image.  Every key is an
    absolute canonical path, so it begins with "/"; a plain name has no
    separator at all ([Sys.Fs.Open.openat_plain_name]).  The
    pre-namespace arms look a raw pathname up as a key, so under
    [Fs.wf_fs] such a lookup MISSES -- the arms lane is what replaces
    the raw lookup with [Fs.resolve], and until it does, this is why an
    example's "the source is present" branch cannot be reached.  Issue
    #1011. *)
Lemma plain_name_not_a_key : forall fs p e,
  Fs.wf_fs fs -> openat_plain_name p = true -> Fs.fs_lookup fs p = Some e -> False.
Proof.
  intros fs p e Hwf Hpn Hlk.
  pose proof (Fs.wf_fs_key_canonical fs p e Hwf Hlk) as Hcan.
  destruct (Fs.canonical_key_head_slash p Hcan) as [r ->].
  pose proof (openat_plain_name_noslash _ Hpn) as Hns.
  unfold path_has_slash in Hns. cbn [existsb] in Hns.
  rewrite slash_byte_is_path_slash_byte, Fs.bv_eqb_refl in Hns.
  discriminate.
Qed.

Lemma fs_lookup_set_eq : forall fs p d, fs_lookup (fs_set fs p d) p = Some d.
Proof. intros fs p d. apply Fs.fs_lookup_set_eq. Qed.

Lemma fs_lookup_set_neq : forall fs p d q, q <> p ->
  fs_lookup (fs_set fs p d) q = fs_lookup fs q.
Proof. intros fs p d q Hne. apply Fs.fs_lookup_set_neq. now apply path_eqb_neq. Qed.

Lemma path_ltb_irrefl : forall p, path_ltb p p = false.
Proof.
  induction p as [|a p IH]; cbn; [reflexivity|].
  unfold bv_ltu. rewrite Z.ltb_irrefl, bv_eqb_refl, IH. reflexivity.
Qed.

Lemma tree_set_set : forall t p d d',
  Fs.tree_set (Fs.tree_set t p d) p d' = Fs.tree_set t p d'.
Proof.
  induction t as [|[q dq] t IH]; intros p d d'; cbn.
  - rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
  - destruct (path_ltb p q) eqn:EL; cbn.
    + rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
    + destruct (path_eqb p q) eqn:EE; cbn.
      * rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
      * rewrite EL, EE, IH. reflexivity.
Qed.

Lemma fs_set_set : forall fs p d d', fs_set (fs_set fs p d) p d' = fs_set fs p d'.
Proof.
  intros [t inos ds] p d d'. unfold fs_set, Fs.fs_with_tree. cbn [Fs.fs_tree Fs.fs_inodes Fs.fs_dirs].
  now rewrite tree_set_set.
Qed.

(** The inode table's own overwrite law, and the file-level one it gives:
    the second write of a file's bytes is the only one that shows. *)
Lemma itab_put_put : forall t i n n',
  Fs.itab_put (Fs.itab_put t i n) i n' = Fs.itab_put t i n'.
Proof.
  induction t as [|[j m] t IH]; intros i n n'; cbn [Fs.itab_put].
  - rewrite Z.ltb_irrefl, Z.eqb_refl. reflexivity.
  - destruct (Z.ltb i j) eqn:EL; cbn [Fs.itab_put].
    + rewrite Z.ltb_irrefl, Z.eqb_refl. reflexivity.
    + destruct (Z.eqb i j) eqn:EE; cbn [Fs.itab_put].
      * rewrite Z.ltb_irrefl, Z.eqb_refl. reflexivity.
      * rewrite EL, EE, IH. reflexivity.
Qed.

Lemma fs_set_ino_data_twice : forall fs i d d',
  Fs.fs_set_ino_data (Fs.fs_set_ino_data fs i d) i d' = Fs.fs_set_ino_data fs i d'.
Proof.
  intros [t inos ds] i d d'.
  unfold Fs.fs_set_ino_data, Fs.fs_put_inode, Fs.fs_with_inodes, Fs.fs_inode.
  cbn [Fs.fs_tree Fs.fs_inodes Fs.fs_dirs].
  rewrite Fs.itab_find_put_eq. cbn [Fs.ino_outside].
  now rewrite itab_put_put.
Qed.

(** A file [Fs.fs_create_file] makes holds the bytes it was made with,
    at the fresh inode. *)
Lemma fs_ino_data_create_file : forall fs k d,
  Fs.fs_ino_data (Fs.fs_create_file fs k d) (Fs.fs_fresh_ino fs) = d.
Proof.
  intros fs k d. unfold Fs.fs_create_file. cbv zeta.
  rewrite Fs.fs_ino_data_set_name.
  unfold Fs.fs_ino_data, Fs.fs_put_inode, Fs.fs_inode.
  cbn [Fs.fs_inodes Fs.fs_with_inodes].
  now rewrite Fs.itab_find_put_eq.
Qed.

(* ========================================================================= *)
(* R22: THE NAMESPACE LAWS COMMON CONSUMES (#1011 sections 3, 4 and 7)       *)
(* ========================================================================= *)

(** TWO LEVELS OF LAW live in this file, and which is which is what
    decides which of them R22 changes.

    AT THE KEY LEVEL, [fs_lookup_set_eq] and [fs_lookup_set_neq] above
    speak about a name the tree holds.  Every file read and write
    reaches its bytes through a descriptor, which carries the file's
    INODE ([State.FdFile]), never through a name, so a write moves
    [Fs.fs_set_ino_data] and leaves the name tree alone.

    AT THE PATH LEVEL a pathname is RESOLVED rather than looked up, and
    the walk reads the name tree and nothing else ([Fs.resolve_same_tree]),
    so A WRITE THROUGH A DESCRIPTOR CHANGES NO RESOLUTION
    ([resolve_model_same_tree]); and a create at the key a create walk
    found missing is seen by the next walk of the same pathname
    ([resolve_model_create], [Fs.resolve_missing_create]).  What this
    file adds is their lift to the MODEL a [to_fout] node carries,
    because a node writes with [State.with_fs] and a consumer that
    re-derives [m_cwd (with_fs ...)] at every step pays the ergonomic
    cost these remove. *)

Lemma m_cwd_with_fds : forall f m, m_cwd (with_fds f m) = m_cwd m.
Proof. reflexivity. Qed.

Lemma m_cwd_with_fs' : forall f m, m_cwd (with_fs f m) = m_cwd m.
Proof. reflexivity. Qed.

(** AN IMAGE WITH THE SAME NAMES RESOLVES EVERY PATHNAME THE SAME WAY,
    under every walk end. *)
Lemma resolve_model_same_tree : forall md (m : Model) (fs' : Fs.Fs) (p : Fs.path),
  Fs.fs_tree fs' = Fs.fs_tree (m_fs m) ->
  Fs.resolve md (m_fs (with_fs fs' m)) (m_cwd (with_fs fs' m)) p
  = Fs.resolve md (m_fs m) (m_cwd m) p.
Proof.
  intros md m fs' p Ht. rewrite with_fs_fs, m_cwd_with_fs'.
  now apply Fs.resolve_same_tree.
Qed.

(** A CREATE AT THE KEY A CREATE WALK FOUND MISSING is what the next
    walk of the same pathname finds, with the same last component and
    separator.  [Fs.resolve_missing_create] over the model. *)
Lemma resolve_model_create :
  forall f (m : Model) (p par nm : Fs.path) lk ts (e : Fs.Entry),
  Fs.wf_fs (m_fs m) -> Fs.path_nul_free p = true ->
  Fs.canonical_key (m_cwd m) = true ->
  Fs.resolve (Fs.WalkCreate f) (m_fs m) (m_cwd m) p = (Fs.RMissing par nm, lk, ts) ->
  Fs.entry_is_link e = false ->
  Fs.resolve (Fs.WalkCreate f)
    (m_fs (with_fs (Fs.fs_set (m_fs m) (Fs.child_key par nm) e) m))
    (m_cwd (with_fs (Fs.fs_set (m_fs m) (Fs.child_key par nm) e) m)) p
  = (Fs.RFound (Fs.child_key par nm) e, lk, ts).
Proof.
  intros f m p par nm lk ts e Hwf Hnul Hcwd Hr Hl.
  rewrite with_fs_fs, m_cwd_with_fs'.
  exact (proj2 (Fs.resolve_missing_create f (m_fs m) (m_cwd m) p par nm lk ts e
                  Hwf Hnul Hcwd Hr Hl)).
Qed.

(** THE DESCRIPTOR TABLE IS NOT THE NAMESPACE: minting or dropping a
    descriptor cannot change how any pathname resolves.  Trivial, and
    stated because the open nodes below thread a [with_fds] through
    every success branch and would otherwise re-prove it each time. *)
Lemma resolve_model_with_fds : forall md (m : Model) f (p : Fs.path),
  Fs.resolve md (m_fs (with_fds f m)) (m_cwd (with_fds f m)) p
  = Fs.resolve md (m_fs m) (m_cwd m) p.
Proof. reflexivity. Qed.

Lemma resolve_res_model_with_fds : forall md (m : Model) f (p : Fs.path),
  Fs.resolve_res md (m_fs (with_fds f m)) (m_cwd (with_fds f m)) p
  = Fs.resolve_res md (m_fs m) (m_cwd m) p.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(* The plain name every collaborator target opens                           *)
(* ------------------------------------------------------------------------ *)

(** [Sys.Fs.Open.openat_plain_name] AND [Fs.plain_name] ARE NOT THE SAME
    PREDICATE, and the gap between them is the work this bridge does
    rather than hides.

    [openat_plain_name] is the ARM's guard: no separator, and not "."
    or "..".  [Fs.plain_name] is what [Fs.resolve_plain_name] needs: a
    nameable COMPONENT, which is all of that AND non-empty, AND free of
    NUL, AND within [Fs.name_max].

    Three hypotheses therefore stand between them, and each is
    discharged where the harness proof already stands:

    - NON-EMPTY: every path-taking arm tests the empty pathname ahead
      of any walk ([Sys.Fs.Open.check_openat_body]'s [path_eqb p []]
      gate, which is [getname_flags]' own -ENOENT), so the proof has
      the test's [false] branch in hand;
    - NUL-FREE: the pathname came out of [read_cstr], which stops AT
      the NUL and never includes one -- [read_cstr_no_nul];
    - WITHIN [Fs.name_max]: a 300-byte argv entry with no separator is
      a component the walk looks up as a file system with a larger
      limit would, with -ENAMETOOLONG admitted beside every answer
      ([Fs.wr_long]).  [Run.valid_argv] does not bound a component's
      length, so a caller that opens an argv entry carries the bound as
      a hypothesis of its own, as this lemma does. *)
Lemma openat_plain_name_plain : forall a,
  openat_plain_name a = true ->
  Fs.path_eqb a [] = false ->
  existsb (fun b => bv_eqb b Fs.path_nul_byte) a = false ->
  (length a <= Fs.name_max)%nat ->
  Fs.plain_name a = true.
Proof.
  intros a Hpn Hne Hnul Hlen.
  pose proof (openat_plain_name_noslash _ Hpn) as Hsl.
  pose proof (openat_plain_name_nodirref _ Hpn) as Hdr.
  unfold path_is_dirref in Hdr. apply orb_false_iff in Hdr as [Hdot Hdd].
  unfold Fs.plain_name, Fs.comp_ok.
  rewrite Bool.andb_true_iff. split.
  - rewrite !Bool.andb_true_iff. repeat split.
    + unfold Fs.comp_nonempty. apply Bool.negb_true_iff.
      apply Nat.eqb_neq. intros Hz.
      apply length_zero_iff_nil in Hz. subst a.
      cbn in Hne. discriminate.
    + apply Bool.negb_true_iff. exact Hdot.
    + apply Bool.negb_true_iff. exact Hdd.
    + apply Bool.negb_true_iff. unfold path_has_slash in Hsl.
      rewrite slash_byte_is_path_slash_byte in Hsl. exact Hsl.
    + apply Bool.negb_true_iff. exact Hnul.
  - apply Bool.negb_true_iff. apply Nat.ltb_ge. exact Hlen.
Qed.

(* ========================================================================= *)
(* The namespace perimeter a plain-name proof stands inside                  *)
(* ========================================================================= *)

(** WHAT THE NAMESPACE ADDS TO A PLAIN-NAME CASE ANALYSIS, AND WHAT IS
    EXCLUDED HERE RATHER THAN PROVED.

    A flat map from byte strings to bytes lets an argv operand denote
    exactly two things: a key that is there, or a key that is not.  A
    namespace admits more, and each of the extra shapes is a real run:

    - A NAME LONGER THAN [Fs.name_max].  The walk looks it up as a file
      system with a larger limit would and admits -ENAMETOOLONG beside
      every answer ([Fs.wr_long]).  [Run.valid_argv] admits such an
      operand, so the bound is a conjunct here ([ns_operand_ordinary])
      and a hypothesis of every lemma below that resolves an operand.

    - A SYMBOLIC LINK AT AN OPERAND.  An open that follows it lands
      wherever its body leads, and a following walk admits -ELOOP
      beside every answer ([Fs.wr_followed]).  The perimeter's last
      conjunct excludes it, and the splits below take it as a
      hypothesis.

    - A DEVICE AT AN OPERAND.  Every valid input's image HOLDS the two
      devices, under /dev, and a working directory of "/dev" with an
      operand of "null" is a valid input.  Opening it mints a device
      descriptor and the copy runs against the device's answer table,
      which is a different outcome set.  [operand_is_not_a_device]
      excludes it from a working directory off the root and outside the
      /dev subtree.

    - A DIRECTORY AT THE SOURCE.  [open(dir, O_RDONLY)] succeeds and
      yields a [State.FdDir]; the read that follows is the directory
      lane, not the file lane a copy loop is about.

    - A WORKING DIRECTORY AT THE ROOT.  [Fs.resolve] puts a first
      component "proc" or "sys" LOOKED UP AT THE ROOT outside the model
      ([Fs.ROutside]), every arm declines it, and [Run.valid_input]
      admits [in_cwd] of "/" beside an argv entry of "proc".  Off the
      root the guard cannot fire whatever the operand is, because it is
      a WALK-STATE test and the walk's first lookup is not at the root;
      so the perimeter's first conjunct is on the working directory, and
      the lemmas below take it as a hypothesis.

    - A WORKING DIRECTORY IN THE "/dev" SUBTREE.  An absent operand
      there is an ordinary [Fs.RMissing], as anywhere else, but a
      PRESENT one may be a device; the second conjunct is what
      [operand_is_not_a_device] reads.

    THE PREDICATE ITSELF HAS NO CONSUMER.  Its conjuncts are what a
    re-proof SPLITS ON or assumes: [ns_operand_file_or_absent] and
    [ns_dst_cases] below are the splits, and they take the device and
    directory facts as hypotheses of their own.  The predicate is kept
    as the one place a reviewer reads the perimeter in one piece. *)
(** The operand's own condition: within [Fs.name_max]. *)
Definition ns_operand_ordinary (fs0 : Fs.Fs) (cwd a : Fs.path) : Prop :=
  (length a <= Fs.name_max)%nat.

Definition ns_perimeter (fs0 : Fs.Fs) (cwd src dst : Fs.path) : Prop :=
  Fs.path_eqb cwd Fs.root = false
  /\ Fs.in_dev_subtree cwd = false
  /\ ns_operand_ordinary fs0 cwd src
  /\ ns_operand_ordinary fs0 cwd dst
  /\ Fs.fs_lookup fs0 (Fs.child_key cwd src) <> Some Fs.EDir
  /\ (forall b, Fs.fs_lookup fs0 (Fs.child_key cwd src) <> Some (Fs.ELink b))
  /\ (forall b, Fs.fs_lookup fs0 (Fs.child_key cwd dst) <> Some (Fs.ELink b)).

(** The five entry shapes an operand's key can hold, with the three the
    perimeter excludes already gone: a regular file (by its inode), or
    nothing.  This is the case split the example proofs actually
    perform, and it is stated once so that they perform the same one. *)
Lemma ns_operand_file_or_absent : forall fs0 cwd a,
  (forall dk, Fs.fs_lookup fs0 (Fs.child_key cwd a) <> Some (Fs.EDev dk)) ->
  Fs.fs_lookup fs0 (Fs.child_key cwd a) <> Some Fs.EDir ->
  (forall b, Fs.fs_lookup fs0 (Fs.child_key cwd a) <> Some (Fs.ELink b)) ->
  (exists i, Fs.fs_lookup fs0 (Fs.child_key cwd a) = Some (Fs.EFile i))
  \/ Fs.fs_lookup fs0 (Fs.child_key cwd a) = None.
Proof.
  intros fs0 cwd a Hdev Hdir Hlnk.
  destruct (Fs.fs_lookup fs0 (Fs.child_key cwd a)) as [[i| |dk|b]|] eqn:E.
  - left. now exists i.
  - now exfalso; apply Hdir.
  - now exfalso; apply (Hdev dk).
  - now exfalso; apply (Hlnk b).
  - now right.
Qed.

(** THE DESTINATION IS ALLOWED TO BE A DIRECTORY -- that is the -EISDIR
    lane the example already has -- so the destination's split has
    three arms, not two, and this names them. *)
Lemma ns_dst_cases : forall fs0 cwd a,
  (forall dk, Fs.fs_lookup fs0 (Fs.child_key cwd a) <> Some (Fs.EDev dk)) ->
  (forall b, Fs.fs_lookup fs0 (Fs.child_key cwd a) <> Some (Fs.ELink b)) ->
  (exists i, Fs.fs_lookup fs0 (Fs.child_key cwd a) = Some (Fs.EFile i))
  \/ Fs.fs_lookup fs0 (Fs.child_key cwd a) = Some Fs.EDir
  \/ Fs.fs_lookup fs0 (Fs.child_key cwd a) = None.
Proof.
  intros fs0 cwd a Hdev Hlnk.
  destruct (Fs.fs_lookup fs0 (Fs.child_key cwd a)) as [[i| |dk|b]|] eqn:E.
  - left. now exists i.
  - right; now left.
  - now exfalso; apply (Hdev dk).
  - now exfalso; apply (Hlnk b).
  - right; now right.
Qed.

(* ------------------------------------------------------------------------ *)
(* Where an open of an operand leaves the model                             *)
(* ------------------------------------------------------------------------ *)

(** THE TWO OPEN ARMS A COPY PROGRAM CALLS, AND EXACTLY WHERE THEY
    DECLINE.  [openat_read_spec] (O_RDONLY) declines a walk that ends
    [Fs.ROutside] or [Fs.RParent] and a device entry away from its own
    name ([dev_at_home]); [openat_create_spec]
    (O_WRONLY|O_CREAT|O_TRUNC) declines [Fs.ROutside] and the same
    devices.  Every other outcome is an answer: an errno, or a
    descriptor, and the success shapes [open_result_spec] and
    [create_wronly] have no [Unmodeled] outcome.  The read walk never
    ends [Fs.RParent] ([read_walk_not_parent]), so both opens decline on
    the same two shapes, which [openat_operand_answers_iff] states. *)
Lemma err_ret_answers : forall e si m', ~ err_ret e si m' Unmodeled.
Proof. intros e si m' H. unfold err_ret, ret_only, pure in H. discriminate H. Qed.

Lemma open_result_spec_answers : forall m mk si m',
  ~ open_result_spec m mk si m' Unmodeled.
Proof.
  intros m mk si m' H. unfold open_result_spec in H. sys_unfold.
  cbv iota in H. inv_ok.
Qed.

Lemma create_wronly_answers : forall fs' i m si m',
  ~ create_wronly fs' i m si m' Unmodeled.
Proof.
  intros fs' i m si m' H. unfold create_wronly in H. sys_unfold.
  cbv iota in H. inv_ok.
Qed.

(** The -ETXTBSY beside a write open of an existing file
    ([open_write_existing]) declines nothing the open does not. *)
Lemma open_write_existing_answers : forall m i (s : Sys SyscallEffect) si m',
  ~ s si m' Unmodeled -> ~ open_write_existing m i s si m' Unmodeled.
Proof.
  intros m i s si m' Hs H. unfold open_write_existing in H.
  destruct (ino_write_held (m_fds m) i); [exact (Hs H)|].
  destruct H as [H|H]; [exact (err_ret_answers _ _ _ H) | exact (Hs H)].
Qed.

(** The walk [open] takes without O_CREAT never stops in front of a
    last name: only the parent end ([Fs.we_parent_root],
    [Fs.we_parent]) and the O_CREAT end ([Fs.we_create_slash]) answer
    [Fs.RParent]. *)
Lemma read_walk_not_parent : forall fs cwd p dir nm,
  fst (fst (Fs.resolve (Fs.WalkFull true false) fs cwd p)) <> Fs.RParent dir nm.
Proof.
  intros fs cwd p dir nm. unfold Fs.resolve. cbn [fst].
  pose proof (proj1 (Fs.resolve_spec (Fs.WalkFull true false) fs cwd p _) eq_refl) as Hr.
  revert Hr.
  generalize (Fs.resolve_res (Fs.WalkFull true false) fs cwd p) as w.
  generalize (Fs.walk_init (Fs.WalkFull true false) Fs.link_max
                (Fs.resolve_start cwd p) p) as s.
  intros s w Hr. revert Hr.
  induction 1 as [s w He | s s' w _ _ IH]; intros Hw; [|exact (IH Hw)].
  destruct He; cbn [Fs.wr_res Fs.mode_parent Fs.mode_create] in *;
    try discriminate; try (destruct (Fs.comps_done r); discriminate).
Qed.

(** A pathname with no separator is not "/proc/self/fd/N", so the open
    goes to the walk. *)
Lemma proc_self_fd_no_slash : forall p,
  path_has_slash p = false -> proc_self_fd p = None.
Proof.
  intros p Hs. unfold proc_self_fd.
  destruct (path_strip_prefix proc_self_fd_prefix p) as [rest|] eqn:Hp;
    [|reflexivity].
  apply path_strip_prefix_app in Hp. subst p.
  vm_compute in Hs. discriminate Hs.
Qed.

(** [Run.valid_argv]'s fifth clause, the separator half, at an index
    after argv[0] (see [CatExec.valid_argv_str_plain]). *)
Lemma valid_argv_no_slash : forall av k, valid_argv av ->
  (S k < length av)%nat ->
  path_has_slash (nth (S k) av []) = false.
Proof.
  intros av k [_ [_ [_ [_ Hpl]]]] Hk.
  assert (Hnth : nth (S k) av [] = nth k (tl av) []).
  { destruct av as [|a av']; [cbn in Hk; lia | reflexivity]. }
  assert (Hk' : (k < length (tl av))%nat).
  { destruct av as [|a av']; cbn in *; lia. }
  rewrite Forall_forall in Hpl.
  destruct (Hpl _ (nth_In (tl av) [] Hk')) as [Hsl _].
  rewrite Hnth. exact Hsl.
Qed.

Lemma openat_read_spec_answers_iff : forall r m si m',
  (forall dir nm, r <> Fs.RParent dir nm) ->
  ~ openat_read_spec r m si m' Unmodeled <->
  match r with
  | Fs.ROutside => False
  | Fs.RFound k (Fs.EDev d) => dev_at_home k d = true
  | _ => True
  end.
Proof.
  intros r m si m' Hnp. unfold openat_read_spec.
  destruct r as [k e|par nm|k|pre| | |dir nm]; cbv beta iota.
  - destruct e as [i| |d|b]; cbv beta iota.
    + split; [intros _; exact I | intros _; apply open_result_spec_answers].
    + split; [intros _; exact I | intros _; apply open_result_spec_answers].
    + destruct d; cbv beta iota; [unfold open_devnull | unfold open_urandom];
        [destruct (dev_at_home k DevNull) | destruct (dev_at_home k DevUrandom)];
        cbn [negb]; split.
      all: first [ intros _; reflexivity
                 | intros _; apply open_result_spec_answers
                 | intros Hn; exfalso; apply Hn; exact eq_refl
                 | intros Hq; discriminate Hq ].
    + split; [intros _; exact I | intros _; apply err_ret_answers].
  - split; [intros _; exact I | intros _; apply err_ret_answers].
  - split; [intros _; exact I | intros _; apply err_ret_answers].
  - split; [intros _; exact I | intros _; apply err_ret_answers].
  - split; [intros _; exact I | intros _; apply err_ret_answers].
  - split; [intros Hn; exfalso; apply Hn; exact eq_refl | intros []].
  - exfalso. exact (Hnp dir nm eq_refl).
Qed.

Lemma openat_create_spec_answers_iff : forall r m si m',
  ~ openat_create_spec r m si m' Unmodeled <->
  match r with
  | Fs.ROutside => False
  | Fs.RFound k (Fs.EDev d) => dev_at_home k d = true
  | _ => True
  end.
Proof.
  intros r m si m'. unfold openat_create_spec.
  destruct r as [k e|par nm|k|pre| | |dir nm]; cbv beta iota.
  - destruct e as [i| |d|b]; cbv beta iota.
    + split; [intros _; exact I | intros _].
      apply open_write_existing_answers. apply create_wronly_answers.
    + split; [intros _; exact I | intros _; apply err_ret_answers].
    + destruct d; cbv beta iota; [unfold open_devnull | unfold open_urandom];
        [destruct (dev_at_home k DevNull) | destruct (dev_at_home k DevUrandom)];
        cbn [negb]; split.
      all: first [ intros _; reflexivity
                 | intros _; apply open_result_spec_answers
                 | intros Hn; exfalso; apply Hn; exact eq_refl
                 | intros Hq; discriminate Hq ].
    + split; [intros _; exact I | intros _; apply err_ret_answers].
  - split; [intros _; exact I | intros _; apply create_wronly_answers].
  - split; [intros _; exact I | intros _; apply err_ret_answers].
  - split; [intros _; exact I | intros _; apply err_ret_answers].
  - split; [intros _; exact I | intros _; apply err_ret_answers].
  - split; [intros Hn; exfalso; apply Hn; exact eq_refl | intros []].
  - split; [intros _; exact I | intros _; apply err_ret_answers].
Qed.

(** AN OPERAND'S OPEN ANSWERS EXACTLY WHEN ITS WALK STAYS IN THE MODEL:
    for a pathname with no separator, the O_RDONLY open (walk
    [Fs.WalkFull true false]) and the O_WRONLY|O_CREAT|O_TRUNC open
    (walk [Fs.WalkCreate true]) have an [Unmodeled] outcome exactly
    when the walk ends [Fs.ROutside] or at a device entry away from its
    own name. *)
Lemma openat_operand_answers_iff : forall p fl md m si,
  path_has_slash p = false ->
  (fl = Z_to_bv 64 0 /\ md = Fs.WalkFull true false
   \/ fl = Z_to_bv 64 577 /\ md = Fs.WalkCreate true) ->
  ~ openat_resolved_spec p fl m si m Unmodeled <->
  match fst (fst (Fs.resolve md (m_fs m) (m_cwd m) p)) with
  | Fs.ROutside => False
  | Fs.RFound k (Fs.EDev d) => dev_at_home k d = true
  | _ => True
  end.
Proof.
  intros p fl md m si Hsl Hfl.
  unfold openat_resolved_spec. rewrite (proc_self_fd_no_slash p Hsl).
  cbv beta iota zeta.
  destruct Hfl as [[-> ->] | [-> ->]].
  - change (open_walk_mode (Z_to_bv 64 0)) with (Fs.WalkFull true false).
    change (open_shape (Z_to_bv 64 0)) with 0%Z.
    pose proof (read_walk_not_parent (m_fs m) (m_cwd m) p) as Hnp. revert Hnp.
    destruct (Fs.resolve (Fs.WalkFull true false) (m_fs m) (m_cwd m) p) as [[r lk] ts].
    intros Hnp. cbv beta iota. rewrite Z.eqb_refl. cbv beta iota.
    cbn [fst] in Hnp |- *.
    apply openat_read_spec_answers_iff. exact Hnp.
  - change (open_walk_mode (Z_to_bv 64 577)) with (Fs.WalkCreate true).
    change (open_shape (Z_to_bv 64 577)) with wr_create_flags.
    destruct (Fs.resolve (Fs.WalkCreate true) (m_fs m) (m_cwd m) p) as [[r lk] ts].
    cbv beta iota.
    change (Z.eqb wr_create_flags 0) with false. rewrite Z.eqb_refl. cbv beta iota.
    cbn [fst].
    apply openat_create_spec_answers_iff.
Qed.

(* ------------------------------------------------------------------------ *)
(* A plain name, resolved, with the side conditions a harness proof has     *)
(* ------------------------------------------------------------------------ *)

(** A PLAIN NAME RESOLVES AS ONE LOOKUP.  [Fs.resolve_plain_name] is the
    walk-level statement and carries the three side conditions the walk
    needs; the lemmas below are the same fact with those discharged
    against the hypotheses a harness proof already stands on, so an
    agent proof that opens [argv[1]] re-derives its open in ONE REWRITE
    rather than re-deriving the walk.

    THE WORKING DIRECTORY clause comes free: [Run.valid_image] says the
    declared cwd resolves to a directory, which is what the walk needs
    to start a relative pathname.

    THE /proc AND /sys GUARD DOES NOT COME FREE, and it is in the
    statement rather than buried in the proof.  [Fs.resolve] puts a
    first component "proc" or "sys" LOOKED UP AT THE ROOT outside the
    model ([Fs.ROutside]), and nothing in [Run.valid_input] forbids a
    working directory of "/" together with an argv entry of "proc".  A
    caller whose working directory is not the root discharges the guard
    by computation -- [Fs.default_cwd] is "/work" -- and a caller that
    allows the root has a case to split.  See
    [resolve_plain_name_valid_offroot] for the first. *)
(** NUL-FREEDOM, from the form [Run.valid_argv] states it in.  An
    argv entry carries the clause as a [Prop] over [In]; the walk wants
    the boolean.  One bridge, so no caller writes it twice. *)
Lemma no_nul_existsb : forall a,
  ~ In (Z_to_bv 8 0) a ->
  existsb (fun b => bv_eqb b Fs.path_nul_byte) a = false.
Proof.
  intros a Hni. apply Bool.not_true_iff_false. intros He.
  apply existsb_exists in He as (b & HIn & Heq).
  apply bv_eqb_eq in Heq. subst b. exact (Hni HIn).
Qed.

(** THE WORKHORSE: a plain name resolved, with the working directory
    given directly rather than read off an input.  The three lemmas
    below are this one with its side conditions discharged from
    progressively more specific hypotheses; every consumer in the tree
    reaches one of the four. *)
Lemma resolve_plain_name_open : forall md fs cwd a,
  Fs.mode_parent md = false -> Fs.mode_dir md = false ->
  Fs.fs_lookup fs cwd = Some Fs.EDir ->
  Fs.path_eqb cwd Fs.root = false ->
  openat_plain_name a = true ->
  Fs.path_eqb a [] = false ->
  ~ In (Z_to_bv 8 0) a ->
  (length a <= Fs.name_max)%nat ->
  (forall b, Fs.fs_lookup fs (Fs.child_key cwd a) <> Some (Fs.ELink b)) ->
  Fs.resolve md fs cwd a
  = (match Fs.fs_lookup fs (Fs.child_key cwd a) with
     | Some e => Fs.RFound (Fs.child_key cwd a) e
     | None => Fs.RMissing cwd a
     end, Fs.LastNorm, false).
Proof.
  intros md fs cwd a Hp Hd Hcwd Hroot Hpn Hne Hnul Hlen Hlnk.
  apply Fs.resolve_plain_name;
    [exact Hp | exact Hd | exact Hcwd | | unfold Fs.at_outside; now rewrite Hroot
    | intros b Hb; exfalso; exact (Hlnk b Hb)].
  apply openat_plain_name_plain; try assumption.
  now apply no_nul_existsb.
Qed.

Lemma resolve_plain_name_valid : forall md inp a,
  Fs.mode_parent md = false -> Fs.mode_dir md = false ->
  Run.valid_input inp ->
  openat_plain_name a = true ->
  Fs.path_eqb a [] = false ->
  existsb (fun b => bv_eqb b Fs.path_nul_byte) a = false ->
  (length a <= Fs.name_max)%nat ->
  (Fs.path_eqb (in_cwd inp) Fs.root
   && (Fs.path_eqb a Fs.proc_comp || Fs.path_eqb a Fs.sys_comp)) = false ->
  (forall b, Fs.fs_lookup (in_fs inp) (Fs.child_key (in_cwd inp) a) <> Some (Fs.ELink b)) ->
  Fs.resolve md (in_fs inp) (in_cwd inp) a
  = (match Fs.fs_lookup (in_fs inp) (Fs.child_key (in_cwd inp) a) with
     | Some e => Fs.RFound (Fs.child_key (in_cwd inp) a) e
     | None => Fs.RMissing (in_cwd inp) a
     end, Fs.LastNorm, false).
Proof.
  intros md inp a Hp Hd Hvi Hpn Hne Hnul Hlen Hout Hlnk.
  destruct Hvi as (_ & _ & (_ & _ & Hcwd & _ & _ & _ & _) & _).
  apply Fs.resolve_plain_name;
    [exact Hp | exact Hd | exact Hcwd | | exact Hout
    | intros b Hb; exfalso; exact (Hlnk b Hb)].
  now apply openat_plain_name_plain.
Qed.

(** [Fs.in_dev_subtree] OF A CHILD KEY: a child key is in the /dev
    subtree only if its parent is, or it is /dev itself.
    [Fs.key_chain] of a child is the parent's chain with the child
    appended, so the [existsb] that decides [Fs.in_dev_subtree] splits
    exactly there. *)
Lemma inits_snoc : forall {A} (l : list A) (x : A),
  inits (l ++ [x]) = inits l ++ [l ++ [x]].
Proof.
  induction l as [|y l IH]; intro x; cbn [inits app]; [reflexivity|].
  rewrite IH, map_app. cbn [map app]. reflexivity.
Qed.

Lemma in_dev_subtree_child : forall k c,
  Fs.canonical_key k = true -> Fs.comp_ok c = true ->
  Fs.in_dev_subtree (Fs.child_key k c)
  = (Fs.in_dev_subtree k || Fs.path_eqb Fs.dev_dir (Fs.child_key k c))%bool.
Proof.
  intros k c Hk Hc.
  unfold Fs.in_dev_subtree, Fs.key_chain.
  assert (Hcomps : Fs.key_comps (Fs.child_key k c) = Fs.key_comps k ++ [c]).
  { unfold Fs.child_key. apply Fs.key_comps_of_comps.
    apply Forall_app. split; [now apply Fs.key_comps_ok | now constructor]. }
  rewrite Hcomps, inits_snoc, map_app, existsb_app.
  cbn [map existsb orb].
  unfold Fs.child_key. rewrite Bool.orb_false_r. reflexivity.
Qed.

(** [Fs.plain_name] is [Fs.comp_ok] plus the length bound, so the
    nameability half comes off it by projection.  Named because
    [operand_is_not_a_device] asks for [Fs.comp_ok] and every caller
    holds the arm's guard instead. *)
Lemma plain_name_comp_ok : forall a,
  Fs.plain_name a = true -> Fs.comp_ok a = true.
Proof.
  intros a H. unfold Fs.plain_name in H.
  now apply Bool.andb_true_iff in H as [Hc _].
Qed.

(** AN OPERAND RESOLVED FROM A WORKING DIRECTORY OFF THE ROOT AND
    OUTSIDE THE /dev SUBTREE NEVER NAMES A DEVICE.

    Every device the image declares is INSIDE the subtree
    ([Run.devices_in_dev_subtreeb]), and the working directory is
    outside it, so the child key an operand resolves to can only enter
    the subtree by BEING /dev -- and it cannot be: [Fs.dev_dir] has a
    single component, so a child key equal to it would need the ROOT
    as its parent.  The two working-directory facts are hypotheses,
    because [Run.valid_input] admits a working directory of "/" and of
    "/dev"; a caller standing at [Fs.default_cwd] discharges both by
    computation. *)
Lemma operand_is_not_a_device : forall inp a dk,
  Run.valid_input inp ->
  Fs.path_eqb (in_cwd inp) Fs.root = false ->
  Fs.in_dev_subtree (in_cwd inp) = false ->
  Fs.comp_ok a = true ->
  Fs.fs_lookup (in_fs inp) (Fs.child_key (in_cwd inp) a) <> Some (Fs.EDev dk).
Proof.
  intros inp a dk Hvi Hnr Hout Ha Hlk.
  assert (Hcan : Fs.canonical_key (in_cwd inp) = true)
    by (destruct Hvi as (_ & _ & (_ & Hc & _) & _); exact Hc).
  assert (Hdev : Run.devices_in_dev_subtreeb (in_fs inp) = true)
    by (destruct Hvi as (_ & _ & (_ & _ & _ & Hd & _) & _); exact Hd).
  pose proof (Run.devices_in_dev_subtreeb_sound _ Hdev _ _ Hlk) as Hin.
  rewrite (in_dev_subtree_child _ _ Hcan Ha) in Hin.
  rewrite Hout in Hin.
  cbn [orb] in Hin.
  (* the child would have to BE /dev, which needs the root as its parent *)
  apply Fs.path_eqb_eq in Hin.
  assert (Hroot : in_cwd inp = Fs.root).
  { assert (Hp : Fs.path_parent (Fs.child_key (in_cwd inp) a) = in_cwd inp)
      by (apply Fs.path_parent_child; assumption).
    rewrite <- Hp, <- Hin. reflexivity. }
  rewrite Hroot, Fs.path_eqb_refl in Hnr. discriminate.
Qed.


(** THE SAME, WITH THE /proc GUARD DISCHARGED from a working directory
    off the root.  Off the root the guard cannot fire whatever the name
    is, because it is a WALK-STATE test and the walk's first lookup is
    not at the root.  [resolve_plain_name_valid] above keeps the guard
    explicit, for a caller whose working directory may be the root. *)
Lemma resolve_plain_name_valid_offroot : forall md inp a,
  Fs.mode_parent md = false -> Fs.mode_dir md = false ->
  Run.valid_input inp ->
  Fs.path_eqb (in_cwd inp) Fs.root = false ->
  openat_plain_name a = true ->
  Fs.path_eqb a [] = false ->
  existsb (fun b => bv_eqb b Fs.path_nul_byte) a = false ->
  (length a <= Fs.name_max)%nat ->
  (forall b, Fs.fs_lookup (in_fs inp) (Fs.child_key (in_cwd inp) a) <> Some (Fs.ELink b)) ->
  Fs.resolve md (in_fs inp) (in_cwd inp) a
  = (match Fs.fs_lookup (in_fs inp) (Fs.child_key (in_cwd inp) a) with
     | Some e => Fs.RFound (Fs.child_key (in_cwd inp) a) e
     | None => Fs.RMissing (in_cwd inp) a
     end, Fs.LastNorm, false).
Proof.
  intros md inp a Hp Hd Hvi Hnr Hpn Hne Hnul Hlen Hlnk.
  apply resolve_plain_name_valid; try assumption.
  now rewrite Hnr.
Qed.

(** "." RESOLVES TO THE WORKING DIRECTORY, in the spelling the Example
    proofs have.  [Fs.resolve_dot] is the general statement over
    [Fs.dot_comp]; the callers hold a [Fs.path_eqb] against
    [Sys.Uapi.dot_path], which is the same one-byte list under the other
    module's name.  One bridge, so neither example writes it twice. *)
Lemma resolve_dot_path : forall md (m : Model) (p : Fs.path),
  Fs.mode_parent md = false ->
  Fs.path_eqb p dot_path = true ->
  Fs.fs_lookup (m_fs m) (m_cwd m) = Some Fs.EDir ->
  Fs.resolve md (m_fs m) (m_cwd m) p
    = (Fs.RFound (m_cwd m) Fs.EDir, Fs.LastDot, false).
Proof.
  intros md m p Hp Hdot Hcwd.
  apply Fs.path_eqb_eq in Hdot. subst p.
  change dot_path with Fs.dot_comp.
  exact (Fs.resolve_dot md (m_fs m) (m_cwd m) Hp Hcwd).
Qed.

(** THE ARGV OPERAND'S RESOLUTION, IN ONE REWRITE: an agent proof that
    opens [argv[1]] does not re-derive the walk, it applies this.

    The NUL-freedom is stated in the [Prop] form [Run.valid_argv]'s
    fourth clause uses.  What the caller owns is the working directory
    off the root, the [Fs.name_max] bound (which [Run.valid_argv] does
    not carry), and the pair its own case split decides: the operand is
    not empty, and it is not a directory reference. *)
Lemma resolve_argv_operand : forall md inp a,
  Fs.mode_parent md = false -> Fs.mode_dir md = false ->
  Run.valid_input inp ->
  Fs.path_eqb (in_cwd inp) Fs.root = false ->
  openat_plain_name a = true ->
  Fs.path_eqb a [] = false ->
  ~ In (Z_to_bv 8 0) a ->
  (length a <= Fs.name_max)%nat ->
  (forall b, Fs.fs_lookup (in_fs inp) (Fs.child_key (in_cwd inp) a) <> Some (Fs.ELink b)) ->
  Fs.resolve md (in_fs inp) (in_cwd inp) a
  = (match Fs.fs_lookup (in_fs inp) (Fs.child_key (in_cwd inp) a) with
     | Some e => Fs.RFound (Fs.child_key (in_cwd inp) a) e
     | None => Fs.RMissing (in_cwd inp) a
     end, Fs.LastNorm, false).
Proof.
  intros md inp a Hp Hd Hvi Hnr Hpn Hne Hnul Hlen Hlnk.
  apply resolve_plain_name_valid_offroot; try assumption.
  now apply no_nul_existsb.
Qed.

(* ------------------------------------------------------------------------ *)
(* The standard-root premise, and the device answer it buys                 *)
(* ------------------------------------------------------------------------ *)

(** THE PREMISE OF #1011 SECTION 15 QUESTION 1, READ OFF A VALID INPUT.
    The question is decided as recommended --
    [Run.valid_input_requires_standard_root] is [true] -- so the
    premise is a conjunct of every validity variant.

    THE SWITCH EQUATION IS A HYPOTHESIS HERE rather than a
    [reflexivity] inside the proof, and that is deliberate.  Flipping
    the switch should break the proofs that actually RELY on a device
    being present, which are the call sites, and it should not break
    this lemma, which is true under either answer.  A reader who wants
    to know what the premise buys reads the call sites. *)
Lemma valid_input_standard_root : forall inp,
  Run.valid_input_requires_standard_root = true ->
  Run.valid_input inp -> Fs.standard_root_present (in_fs inp).
Proof.
  intros inp Hsw Hvi.
  destruct Hvi as (_ & _ & (_ & _ & _ & _ & _ & Hpr & _) & _).
  unfold Run.standard_root_premise in Hpr. rewrite Hsw in Hpr. exact Hpr.
Qed.

(** THE TWO DEVICES RESOLVE DETERMINISTICALLY, FROM ANY WORKING
    DIRECTORY, under that premise.  This is the lemma #1011 section 7's
    retire table retires the collaborators' -ENOENT items on /dev/null
    and /dev/urandom against: an agent proof opens the device by its
    absolute name and cites this instead of carrying a premise of its
    own, and what it gets back is TODAY'S ANSWER -- the device entry,
    which the open arm mints into today's descriptor kind with its
    answer table untouched.

    "From any working directory" is not a convenience: both keys are
    absolute, so the walk starts at the root whatever [cwd] is, and the
    statement says so by quantifying over it. *)
Lemma resolve_standard_dev : forall md fs cwd,
  Fs.mode_parent md = false -> Fs.mode_dir md = false ->
  Fs.wf_fs fs ->
  Fs.standard_root_present fs ->
  Fs.resolve md fs cwd Fs.devnull_key
    = (Fs.RFound Fs.devnull_key (Fs.EDev Fs.DevNull), Fs.LastNorm, false)
  /\ Fs.resolve md fs cwd Fs.urandom_key
    = (Fs.RFound Fs.urandom_key (Fs.EDev Fs.DevUrandom), Fs.LastNorm, false).
Proof.
  intros md fs cwd Hp Hd Hwf Hsr.
  destruct Hsr as (Hdev & _ & Hnull & Hrnd).
  destruct Hwf as (_ & _ & Hroot & _).
  split.
  - now apply Fs.resolve_devnull.
  - now apply Fs.resolve_urandom.
Qed.

(** The two put together, in the form an agent proof uses: from
    [Run.valid_input] alone, plus the switch. *)
Corollary resolve_standard_dev_valid : forall md inp cwd,
  Fs.mode_parent md = false -> Fs.mode_dir md = false ->
  Run.valid_input_requires_standard_root = true ->
  Run.valid_input inp ->
  Fs.resolve md (in_fs inp) cwd Fs.devnull_key
    = (Fs.RFound Fs.devnull_key (Fs.EDev Fs.DevNull), Fs.LastNorm, false)
  /\ Fs.resolve md (in_fs inp) cwd Fs.urandom_key
    = (Fs.RFound Fs.urandom_key (Fs.EDev Fs.DevUrandom), Fs.LastNorm, false).
Proof.
  intros md inp cwd Hp Hd Hsw Hvi.
  apply resolve_standard_dev; [exact Hp | exact Hd | |].
  - destruct Hvi as (_ & _ & (Hwf & _) & _). exact Hwf.
  - now apply valid_input_standard_root.
Qed.

(* ========================================================================= *)
(* fd-table algebra                                                          *)
(* ========================================================================= *)

Lemma fd_lookup_cons_eq : forall fds fd e, fd_lookup ((fd, e) :: fds) fd = Some e.
Proof. intros. cbn. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma fd_lookup_cons_neq : forall fds k e fd, k <> fd ->
  fd_lookup ((k, e) :: fds) fd = fd_lookup fds fd.
Proof.
  intros fds k e fd Hne. cbn.
  rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.

Lemma fd_lookup_cons_None : forall fds k e fd,
  fd_lookup ((k, e) :: fds) fd = None -> k <> fd /\ fd_lookup fds fd = None.
Proof.
  intros fds k e fd H. cbn in H.
  destruct (bv_eqb k fd) eqn:E; [discriminate|].
  split; [|exact H].
  intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma fd_filter_id : forall fds fd,
  fd_lookup fds fd = None ->
  List.filter (fun p => negb (bv_eqb (fst p) fd)) fds = fds.
Proof.
  induction fds as [|[k e] fds IH]; intros fd H; [reflexivity|].
  apply fd_lookup_cons_None in H. destruct H as [Hne H].
  cbn [List.filter fst]. rewrite (bv_eqb_neq k fd Hne). cbn [negb].
  rewrite IH by exact H. reflexivity.
Qed.

Lemma fd_insert_fresh : forall fds fd e,
  fd_lookup fds fd = None -> fd_insert fds fd e = (fd, e) :: fds.
Proof.
  intros fds fd e H. unfold fd_insert. rewrite fd_filter_id by exact H.
  reflexivity.
Qed.

Lemma fd_lookup_filter_neq : forall fds fd fd', fd' <> fd ->
  fd_lookup (List.filter (fun p => negb (bv_eqb (fst p) fd)) fds) fd' = fd_lookup fds fd'.
Proof.
  induction fds as [|[k e] fds IH]; intros fd fd' Hne; [reflexivity|].
  cbn [List.filter fst].
  destruct (bv_eqb k fd) eqn:Hk.
  - apply bv_eqb_eq in Hk. subst k.
    cbn [negb]. rewrite IH by exact Hne. cbn [fd_lookup].
    rewrite bv_eqb_neq by congruence. reflexivity.
  - cbn [negb fd_lookup]. destruct (bv_eqb k fd'); [reflexivity | apply IH; exact Hne].
Qed.

Lemma fd_lookup_insert_eq : forall fds fd e, fd_lookup (fd_insert fds fd e) fd = Some e.
Proof. intros. unfold fd_insert. apply fd_lookup_cons_eq. Qed.

Lemma fd_lookup_insert_neq : forall fds fd e fd', fd' <> fd ->
  fd_lookup (fd_insert fds fd e) fd' = fd_lookup fds fd'.
Proof.
  intros fds fd e fd' Hne. unfold fd_insert.
  rewrite fd_lookup_cons_neq by congruence.
  apply fd_lookup_filter_neq. exact Hne.
Qed.

Lemma fd_lookup_remove_neq : forall fds fd fd', fd' <> fd ->
  fd_lookup (fd_remove fds fd) fd' = fd_lookup fds fd'.
Proof. intros. unfold fd_remove. apply fd_lookup_filter_neq. assumption. Qed.

Lemma fd_lookup_some_none_neq : forall fds a b ea,
  fd_lookup fds a = Some ea -> fd_lookup fds b = None -> a <> b.
Proof. intros fds a b ea Ha Hb ->. congruence. Qed.

(** A concrete free fd after one open over the three standard channels
    (stdin/stdout/stderr already occupied). *)
Lemma free_fd_after_open : forall x y z fdin e,
  exists w, fd_lookup (fd_insert
      [(Z_to_bv 64 0, x); (Z_to_bv 64 1, y); (Z_to_bv 64 2, z)] fdin e) w = None
    /\ (bv_unsigned w < 2 ^ 31)%Z.
Proof.
  intros x y z fdin e.
  destruct (decide (fdin = Z_to_bv 64 3)) as [->|Hne].
  - exists (Z_to_bv 64 4). split.
    + rewrite fd_lookup_insert_neq
        by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
      reflexivity.
    + change (bv_unsigned (Z_to_bv 64 4)) with 4%Z. lia.
  - exists (Z_to_bv 64 3). split.
    + rewrite fd_lookup_insert_neq by congruence. reflexivity.
    + change (bv_unsigned (Z_to_bv 64 3)) with 3%Z. lia.
Qed.

Lemma filter_fd_cons_keep : forall {B} (fds : list (word * B)) k (e : B) fd,
  k <> fd ->
  List.filter (fun p => negb (bv_eqb (fst p) fd)) ((k, e) :: fds)
  = (k, e) :: List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
  intros B fds k e fd Hne. cbn [List.filter fst].
  rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.

Lemma filter_fd_cons_drop : forall {B} (fds : list (word * B)) fd (e : B),
  List.filter (fun p => negb (bv_eqb (fst p) fd)) ((fd, e) :: fds)
  = List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
  intros B fds fd e. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity.
Qed.

(* ========================================================================= *)
(* file_read / file_write arithmetic                                         *)
(* ========================================================================= *)

Lemma length_file_read : forall data off count,
  length (file_read data off count)
  = Nat.min (word_to_nat count) (length data - word_to_nat off)%nat.
Proof.
  intros data off count. rewrite file_read_unguarded.
  rewrite length_firstn, length_skipn. reflexivity.
Qed.

Lemma file_read_nil : forall data off count,
  (length data <= word_to_nat off)%nat -> file_read data off count = [].
Proof.
  intros data off count H. rewrite file_read_unguarded.
  rewrite skipn_all2 by exact H. apply firstn_nil.
Qed.

(** Appending write: writing at exactly the end of the file. *)
Lemma file_write_append : forall data off bs,
  word_to_nat off = length data -> file_write data off bs = data ++ bs.
Proof.
  intros data off bs Hoff. unfold file_write, file_extend.
  destruct bs as [|b bs]; [now rewrite app_nil_r|]. cbv zeta.
  rewrite Hoff, Nat.sub_diag. cbn [repeat]. rewrite app_nil_r.
  rewrite firstn_all.
  rewrite skipn_all2 by lia.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma firstn_add {A} : forall (l : list A) n m,
  firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  induction l as [|x l IH]; intros n m.
  - rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
  - destruct n as [|n]; [reflexivity|].
    cbn [firstn skipn Nat.add app]. rewrite IH. reflexivity.
Qed.

(** One copy step: current content [firstn (word_to_nat off) data]
    extended by the chunk just read at [off].  The fd offset is a [word],
    and the equation is hypothesis-free. *)
Lemma copy_step : forall data (off count : word),
  firstn (word_to_nat off) data ++ file_read data off count
  = firstn (word_to_nat off
            + Nat.min (word_to_nat count) (length data - word_to_nat off)) data.
Proof.
  intros data off count. rewrite file_read_unguarded.
  rewrite firstn_add. f_equal.
  destruct (Nat.le_ge_cases (word_to_nat count)
              (length data - word_to_nat off)) as [H|H].
  - rewrite Nat.min_l by exact H. reflexivity.
  - rewrite Nat.min_r by exact H.
    rewrite firstn_all2 by (rewrite length_skipn; lia).
    rewrite firstn_all2 by (rewrite length_skipn; lia).
    reflexivity.
Qed.

(* ========================================================================= *)
(* read_cstr bridges (through the rdn merged view)                           *)
(* ========================================================================= *)

(** The merged read view [rdn] chains over — equal to [ms_read_byte] of a
    state whose rom is [seg_rom segs]. *)
Definition mrb (segs : list Segment) (mem : word -> option byte)
    : word -> option byte :=
  fun a => match mem a with Some b => Some b | None => seg_rom segs a end.

Lemma ms_read_byte_mrb : forall segs regs pc mem,
  ms_read_byte (mkst regs pc mem (seg_rom segs)) = mrb segs mem.
Proof. reflexivity. Qed.

Lemma ms_read_byte_rec_mrb : forall segs regs fr pc sv rv fc mem,
  ms_read_byte {| ms_regs := regs; ms_fregs := fr; ms_pc_val := pc; ms_svc_pending := sv;
                  ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := seg_rom segs |}
  = mrb segs mem.
Proof. reflexivity. Qed.

(** The first byte read by [rdn] is exactly the [mrb] value at [a]. *)
Lemma mrb_first : forall segs mem a n b rest,
  rdn segs mem a (S n) = Some (b :: rest) -> mrb segs mem a = Some b.
Proof.
  intros segs mem a n b rest H. unfold mrb. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; congruence.
Qed.

(** The remaining bytes read by [rdn]. *)
Lemma rdn_tail : forall segs mem a n b rest,
  rdn segs mem a (S n) = Some (b :: rest) -> rdn segs mem (a + 1) n = Some rest.
Proof.
  intros segs mem a n b rest H. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; reflexivity.
Qed.

(** THE [TASK_SIZE] PREMISE on the four lemmas below is a repair, not a
    weakening.  They were true of the unguarded walk.  [State.read_cstr_aux]
    now tests [State.access_okb a 1] at every byte it steps, and they
    are false of it exactly where a name's bytes sit at or above
    [TASK_SIZE] — a range [strncpy_from_user] refuses
    (lib/strncpy_from_user.c, [strncpy_from_user]: [max_addr =
    TASK_SIZE_MAX], -EFAULT at or past it; [State.read_cstr_aux] says
    the rest).  Each premise is the weakest that makes its lemma true:
    the last byte the walk steps — the NUL, or the last of [fuel]
    non-NUL bytes — lies below [TASK_SIZE].  Below [TASK_SIZE] the walk's
    [a + 1] does not wrap, so that one bound puts every stepped byte
    there; nothing is assumed about the rest of memory. *)
Lemma read_cstr_aux_of_rdn : forall segs str fuel mem a,
  (length str < fuel)%nat -> ~ In (Z_to_bv 8 0) str ->
  (bv_unsigned a + Z.of_nat (length str) < TASK_SIZE)%Z ->
  rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
  read_cstr_aux (mrb segs mem) a fuel = CstrOk str.
Proof.
  intros segs str; induction str as [|b str IH]; intros fuel mem a Hf Hnz Hlo Hr.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    assert (Hb0 : mrb segs mem a = Some (Z_to_bv 8 0))
      by (apply (mrb_first segs mem a 0 (Z_to_bv 8 0) []); exact Hr).
    rewrite read_cstr_aux_accepted
      by (rewrite access_okb_one; apply Z.ltb_lt; lia).
    rewrite Hb0. reflexivity.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    rewrite read_cstr_aux_accepted
      by (rewrite access_okb_one; apply Z.ltb_lt; lia).
    cbn [app] in Hr.
    assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
    assert (Hfirst : mrb segs mem a = Some b)
      by (apply (mrb_first segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    assert (Htail : rdn segs mem (a + 1) (length str + 1)
                    = Some (str ++ [Z_to_bv 8 0]))
      by (apply (rdn_tail segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z)
      by (apply bv_unsigned_succ_below_task_size; lia).
    rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
    rewrite (IH fuel mem (a + 1) ltac:(lia)
               ltac:(intro; apply Hnz; right; assumption) ltac:(lia) Htail).
    reflexivity.
Qed.

Lemma read_cstr_of_rdn : forall segs mem a str,
  (length str <= 4095)%nat -> ~ In (Z_to_bv 8 0) str ->
  (bv_unsigned a + Z.of_nat (length str) < TASK_SIZE)%Z ->
  rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
  read_cstr (mrb segs mem) a = CstrOk str.
Proof.
  intros segs mem a str Hlen Hnz Hlo Hr.
  unfold read_cstr. apply read_cstr_aux_of_rdn; [|exact Hnz|exact Hlo|exact Hr].
  change path_max with 4096%nat. lia.
Qed.

(** [fuel] readable non-NUL bytes: the scan runs out of bound, which is
    [CstrTooLong] — the -ENAMETOOLONG case, NOT a fault.  The bound
    premise is stated for [fuel <> 0] because at [fuel = 0] the walk
    steps no byte and the lemma holds wherever [a] is. *)
Lemma read_cstr_aux_toolong_of_rdn : forall segs fuel bs mem a,
  length bs = fuel -> ~ In (Z_to_bv 8 0) bs ->
  (fuel <> 0%nat -> (bv_unsigned a + Z.of_nat fuel <= TASK_SIZE)%Z) ->
  rdn segs mem a fuel = Some bs ->
  read_cstr_aux (mrb segs mem) a fuel = CstrTooLong.
Proof.
  intros segs fuel; induction fuel as [|fuel IH]; intros bs mem a Hlen Hnz Hlo Hr;
    [reflexivity|].
  specialize (Hlo ltac:(lia)).
  destruct bs as [|b bs]; [cbn in Hlen; lia|].
  rewrite read_cstr_aux_accepted
    by (rewrite access_okb_one; apply Z.ltb_lt; lia).
  assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
  assert (Hfirst : mrb segs mem a = Some b)
    by (apply (mrb_first segs mem a fuel b bs); exact Hr).
  assert (Htail : rdn segs mem (a + 1) fuel = Some bs)
    by (apply (rdn_tail segs mem a fuel b bs); exact Hr).
  assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z)
    by (apply bv_unsigned_succ_below_task_size; lia).
  rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
  rewrite (IH bs mem (a + 1) ltac:(cbn in Hlen; lia)
             ltac:(intro; apply Hnz; right; assumption)
             ltac:(intro; lia) Htail).
  reflexivity.
Qed.

Lemma read_cstr_toolong_of_rdn : forall segs mem a bs,
  length bs = 4096%nat -> ~ In (Z_to_bv 8 0) bs ->
  (bv_unsigned a + 4096 <= TASK_SIZE)%Z ->
  rdn segs mem a 4096%nat = Some bs ->
  read_cstr (mrb segs mem) a = CstrTooLong.
Proof.
  intros segs mem a bs Hlen Hnz Hlo Hr.
  unfold read_cstr. change path_max with 4096%nat.
  eapply read_cstr_aux_toolong_of_rdn; [exact Hlen|exact Hnz| |exact Hr].
  intros _. change (Z.of_nat 4096) with 4096%Z. lia.
Qed.

(* ========================================================================= *)
(* argv strings as NUL-terminated byte runs and prefixes                     *)
(* ========================================================================= *)

Lemma read_argv_cstr_k :
  forall v segs inp mbase ph entry (sp brk : word) draw k,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
      (length (nth k (in_argv inp) []) + 1)
  = Some (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]).
Proof.
  intros v segs inp mbase ph entry sp brk draw k Hlaunch Hk.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch)
    as Hnw.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
    pre (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) post
    (length (nth k (in_argv inp) []) + 1)) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
             (in_execfn inp) k)
    with (sp + nat_to_word
                 (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                    (in_argv inp) (in_envp inp) (in_execfn inp)
                  + total_arg_bytes_nat (firstn k (in_argv inp)))).
  2:{ rewrite (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [exact E | | exact Hnw].
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma read_argv_prefix_k :
  forall v segs inp mbase ph entry (sp brk : word) draw k n,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  (n <= length (nth k (in_argv inp) []))%nat ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k) n
  = Some (firstn n (nth k (in_argv inp) [])).
Proof.
  intros v segs inp mbase ph entry sp brk draw k n Hlaunch Hk Hn.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch)
    as Hnw.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
    pre (firstn n (nth k (in_argv inp) []))
    ((skipn n (nth k (in_argv inp) []) ++ [Z_to_bv 8 0]) ++ post) n) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
             (in_execfn inp) k)
    with (sp + nat_to_word
                 (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                    (in_argv inp) (in_envp inp) (in_execfn inp)
                  + total_arg_bytes_nat (firstn k (in_argv inp)))).
  2:{ rewrite (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [| |exact Hnw].
  - rewrite E. rewrite <- !app_assoc.
    rewrite (app_assoc (firstn n (nth k (in_argv inp) []))
               (skipn n (nth k (in_argv inp) []))).
    rewrite firstn_skipn. reflexivity.
  - apply firstn_length_le. exact Hn.
Qed.

(* ========================================================================= *)
(* to_fout: the exact (exit code, final fs) outcome set                      *)
(* ========================================================================= *)

Definition fout_trace (o : word * Fs.Fs) : list event := [ExitEv (fst o) (Fs.fs_observe (snd o))].

Section WithSegs.
Variable segs : list Segment.

Inductive to_fout : machine_state -> Model -> ((word * Fs.Fs) -> Prop) -> Prop :=
| tfo_exit : forall ms model x8 (U : (word * Fs.Fs) -> Prop),
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    (forall o, U o <-> o = (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model)) ->
    to_fout ms model U
| tfo_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_fout ms' model U ->
    to_fout ms model U
| tfo_sys : forall ms model x8
    (T : SyscallEffect -> Model -> (word * Fs.Fs) -> Prop)
    (U : (word * Fs.Fs) -> Prop),
    ms_svc_pending ms = Some x8 ->
    ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
    (exists eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) ->
    (forall eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
        evs = [] /\ m_halted model' = None /\ m_vm_lazy model' = []) ->
    (forall eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
        to_fout (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_fout ms model U.

(** Prepend a deterministic instruction run. *)
Lemma tfo_msteps : forall ms ms' model U,
  msteps segs ms ms' -> to_fout ms' model U -> to_fout ms model U.
Proof.
  intros ms ms' model U H; induction H; [auto|].
  intro Ht. eapply tfo_step; eauto.
Qed.

(** Rewire the outcome set along an extensional equivalence. *)
Lemma tfo_equiv : forall ms model U V,
  to_fout ms model U ->
  (forall o, V o <-> U o) ->
  to_fout ms model V.
Proof.
  intros ms model U V Hto; revert V.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
    intros V HV.
  - apply (tfo_exit ms model x8); [exact Hsvc | exact Hx8 |].
    intro o. rewrite (HV o). apply HU.
  - eapply tfo_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
  - apply (tfo_sys ms model x8 T V);
      [exact Hsvc | exact Hne | exact Hrec | exact Hshape | exact Hcont |].
    intro o. rewrite (HV o). apply HU.
Qed.

(** Every [to_fout] outcome set is inhabited. *)
Lemma to_fout_nonempty : forall ms model U,
  to_fout ms model U -> exists o, U o.
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ].
  - exists (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model).
    apply HU. reflexivity.
  - exact IH.
  - destruct Hrec as (eff & model' & evs & Hspec).
    destruct (IH eff model' evs Hspec) as [o Ho].
    exists o. apply HU. exists eff, model', evs. auto.
Qed.

(** One-step inversion at a [tfo_sys] ecall. *)
Lemma sstep_fsys_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff model' evs',
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs') ->
      evs' = [] /\ m_halted model' = None /\ m_vm_lazy model' = []) ->
  sstep segs (mkCfg ms model) evs st ->
  exists eff model',
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []) /\
    evs = [] /\
    st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (Hshape eff model' evs0 H3) as (He & _ & Hlazy');
      subst evs0;
      match goal with
      | Hmat : materialize_model_accesses model' _ = Some ?model'' |- _ =>
          rewrite (materialize_model_accesses_no_lazy model' _ Hlazy') in Hmat;
          inversion Hmat; subst model''
      end;
      exists eff, model'; auto
    end.
  - (* sstep_syscall_materialization_fault *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (Hshape eff model' evs0 H3) as (_ & _ & Hlazy');
      rewrite (materialize_model_accesses_no_lazy model' _ Hlazy') in Hmat;
      discriminate
    end.
  - (* sstep_exit: excluded by the never-halts shape *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (Hshape eff model' evs0 H3) as (_ & Hm & _);
      congruence
    end.
  - (* sstep_killed: the same shape excludes it, through
       [State.m_killed_of_m_halted_none] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (Hshape eff model' evs0 H3) as (_ & Hm & _);
      assert (Hhn : m_halted model' = None) by congruence;
      rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
    end.
Qed.

(* ------------------------------------------------------------------------- *)
(* Trace characterization.                                                    *)
(* ------------------------------------------------------------------------- *)

(** The omni reading of a file-copying run: every execution halts with
    one of the outcomes, having emitted exactly its exit event.  One
    induction over [to_fout]; at a syscall node the successors are
    exactly the admissible resolutions ([sstep_fsys_inv]), each covered
    by the induction hypothesis at its post-model. *)
Definition fout_post (U : (word * Fs.Fs) -> Prop) : post :=
  fun tr o => exists out, U out /\ tr = fout_trace out /\ exits_with (fst out) tr o.

Lemma to_fout_exec : forall ms model U,
  to_fout ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  OmniRun.exec segs (mkCfg ms model) (fout_post U).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
    intros Hh Hlazy.
  - (* tfo_exit *)
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (Fs.fs_observe (m_fs model))]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (Fs.fs_observe (m_fs model))]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (Fs.fs_observe (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_si. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold fout_post. cbn beta.
        exists (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model).
        split; [apply HU; reflexivity |].
        split; [unfold fout_trace; cbn [fst snd app]; reflexivity |].
        cbn [exits_with cfg_model fst]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* tfo_step *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hh Hlazy) |]. intros tr o H. cbn [app]. exact H.
  - (* tfo_sys: every admissible resolution is a successor *)
    apply exec_step; [exact Hh | | |].
    + destruct Hrec as (eff & model' & evs & Hspec).
      destruct (Hshape eff model' evs Hspec) as (-> & Hh' & Hlazy').
      eexists; eexists.
      apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
      rewrite (materialize_model_accesses_no_lazy model' _ Hlazy'). reflexivity.
    + intros evs Hss.
      destruct (sstep_fsys_inv ms model x8 evs SError Hh Hlazy Hsvc Hne Hshape Hss)
        as (eff & model' & _ & _ & Habs). discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_fsys_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hne Hshape Hss)
        as (eff & model' & Hspec & -> & Hc'). injection Hc' as ->.
      destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
      eapply exec_conseq; [exact (IH eff model' [] Hspec Hh' Hlazy') |].
      intros tr o (out & Hout & Heq & Hx). exists out.
      split; [apply HU; exists eff, model', []; split; [exact Hspec | exact Hout] |].
      split; [cbn [app]; exact Heq | exact Hx].
Qed.

Lemma to_fout_star_only : forall ms model U,
  to_fout ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    exists o, U o /\ is_prefix tr (fout_trace o).
Proof.
  intros ms model U Hto Hh Hlazy tr c Hstar.
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_fout_exec ms model U Hto Hh Hlazy) Hstar))
    as (tr' & o & _ & (out & Hout & Heq & _)).
  exists out. split; [exact Hout |]. rewrite <- Heq. apply is_prefix_app.
Qed.

Lemma to_fout_star_admits : forall ms model U,
  to_fout ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall o, U o ->
    exists c, star segs (mkCfg ms model) (fout_trace o) c.
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
    intros Hh Hlazy o Ho.
  - (* tfo_exit *)
    apply HU in Ho. subst o. unfold fout_trace; cbn [fst snd].
    exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
    apply star_one.
    replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (Fs.fs_observe (m_fs model))]
      with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                     (Fs.fs_observe (m_fs (with_halted
                              (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)))])
      by (cbn; reflexivity).
    apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
             (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
             (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
    + exact Hh.
    + exact Hsvc.
    + apply (exit_dispatch_ok (sys_input segs ms x8) model).
      rewrite in_sysno_si. exact Hx8.
    + cbn. reflexivity.
    + apply m_killed_with_halted.
  - (* tfo_step *)
    destruct (IH Hh Hlazy o Ho) as [c Hstar].
    exists c.
    replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
    eapply star_step; [|exact Hstar].
    apply (sstep_instr segs ms model ms' model); try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - (* tfo_sys *)
    apply HU in Ho.
    destruct Ho as (eff & model' & evs & Hspec & Ht).
    destruct (Hshape eff model' evs Hspec) as (He & Hh' & Hlazy'). subst evs.
    destruct (IH eff model' [] Hspec Hh' Hlazy' o Ht) as [c Hstar].
    exists c.
    replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
    eapply star_step; [|exact Hstar].
    apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
    rewrite (materialize_model_accesses_no_lazy model' _ Hlazy'). reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* No-error characterization.                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma to_fout_progress : forall ms model U,
  to_fout ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall evs st, sstep segs (mkCfg ms model) evs st ->
  exists ms' model', st = SNext (mkCfg ms' model') /\
    (m_halted model' <> None \/
     (m_halted model' = None /\ m_vm_lazy model' = [] /\
      exists U', to_fout ms' model' U')).
Proof.
  intros ms model U Hto Hh Hlazy evs st Hss.
  revert evs st Hss.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
    intros evs st Hss.
  - (* tfo_exit *)
    destruct (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss)
      as [_ Hst]. subst st.
    do 2 eexists. split; [reflexivity|]. left. cbn. discriminate.
  - (* tfo_step *)
    destruct (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss)
      as [_ Hst]. subst st.
    do 2 eexists. split; [reflexivity|]. right.
    repeat split; try assumption. exists U. exact Hto.
  - (* tfo_sys *)
    destruct (sstep_fsys_inv ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss)
      as (eff & model' & Hspec & _ & Hst). subst st.
    destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
    do 2 eexists. split; [reflexivity|]. right.
    repeat split; try assumption.
    exists (T eff model'). exact (Hcont eff model' [] Hspec).
Qed.

Definition fon_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None
   /\ m_vm_lazy (cfg_model c) = []
   /\ exists U, to_fout (cfg_ms c) (cfg_model c) U)
  \/ m_halted (cfg_model c) <> None.

Lemma fon_path_step : forall c evs c',
  fon_path c -> sstep segs c evs (SNext c') -> fon_path c'.
Proof.
  intros [ms model] evs [ms' model'] Hop Hss.
  unfold fon_path in *; cbn in Hop |- *.
  destruct Hop as [(Hh & Hlazy & U & Hto) | Hh].
  - destruct (to_fout_progress ms model U Hto Hh Hlazy evs _ Hss)
      as (ms'' & model'' & Hst & Hcase).
    inversion Hst; subst.
    destruct Hcase as [Hhz | (Hhz & Hlazy' & U' & Hto')].
    + right. exact Hhz.
    + left. repeat split; try assumption. exists U'; exact Hto'.
  - exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.

Lemma fon_path_no_error : forall c evs, fon_path c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hop Hss.
  unfold fon_path in Hop; cbn in Hop.
  destruct Hop as [(Hh & Hlazy & U & Hto) | Hh].
  - destruct (to_fout_progress ms model U Hto Hh Hlazy evs _ Hss)
      as (ms'' & model'' & Hst & _). discriminate.
  - inversion Hss; subst; cbn in Hh; congruence.
Qed.

Lemma star_fon_path : forall c tr c',
  fon_path c -> star segs c tr c' -> fon_path c'.
Proof. exact (star_inv segs fon_path fon_path_step). Qed.

Lemma to_fout_no_error : forall ms model U,
  to_fout ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model U Hto Hh Hlazy. apply exec_no_error.
  eapply exec_conseq; [exact (to_fout_exec ms model U Hto Hh Hlazy) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* ------------------------------------------------------------------------- *)
(* Escape plumbing: reach a syscall-Unmodeled through a star with silent syscalls.  *)
(* ------------------------------------------------------------------------- *)

Lemma star_syscall_nil : forall ms model x8 eff model',
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ->
  m_halted model' = None ->
  m_vm_lazy model' = [] ->
  star segs (mkCfg ms model) []
       (mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof.
  intros ms model x8 eff model' Hh Hsvc Hspec Hh' Hlazy.
  apply star_one.
  apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
  rewrite (materialize_model_accesses_no_lazy model' _ Hlazy). reflexivity.
Qed.

Lemma reaches_error_star : forall c tr c',
  star segs c tr c' -> reaches_error segs c' -> reaches_error segs c.
Proof.
  intros c tr c' Hstar (tr2 & c2 & evs & Hstar2 & Hss).
  exists (tr ++ tr2), c2, evs. split; [eapply star_trans; eauto | exact Hss].
Qed.

Lemma spec_err_error : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model Unmodeled ->
  reaches_error segs (mkCfg ms model).
Proof.
  intros ms model x8 Hh Hsvc Hspec.
  exists [], (mkCfg ms model), []. split; [apply star_refl|].
  eapply sstep_syscall_unmodeled; eassumption.
Qed.

Lemma msteps_spec_err_error : forall ms ms' model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = Some x8 ->
  syscall_spec (sys_input segs ms' x8) model Unmodeled ->
  reaches_error segs (mkCfg ms model).
Proof.
  intros ms ms' model x8 Hh Hlazy Hm Hsvc Hspec.
  eapply reaches_error_star.
  - apply msteps_star_nil; eassumption.
  - eapply spec_err_error; eassumption.
Qed.

(** A syscall configuration whose relational spec is [Unmodeled] has no
    successful successor.  Completeness of the executable checker makes
    that exclusion explicit: [CheckUnmodeled] for every proposed effect cannot
    simultaneously be [CheckOk]. *)
Lemma spec_err_all_traces_error : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model Unmodeled ->
  all_traces_error segs (mkCfg ms model).
Proof.
  intros ms model x8 Hh Hsvc Hspec.
  assert (Hno_ok : forall eff model' events,
      ~ syscall_spec (sys_input segs ms x8) model
          (Ok eff model' events)).
  { intros eff model' events Hok.
    pose proof Hspec as Herr.
    apply (check_syscall_complete_unmodeled _ _ eff) in Herr.
    apply check_syscall_complete_ok in Hok.
    rewrite Herr in Hok. discriminate Hok. }
  constructor.
  - exists [], SError. eapply sstep_syscall_unmodeled; eassumption.
  - intros evs c' Hnext. inversion Hnext; subst; try congruence.
    all: exfalso;
      match goal with
      | Hno : forall (eff0 : SyscallEffect) (model0 : Model)
                       (events0 : list event),
          ~ syscall_spec (sys_input ?segs0 ?ms0 ?expected) ?m0
              (Ok eff0 model0 events0),
        Hexpected : ms_svc_pending ?ms0 = Some ?expected,
        Hactual : ms_svc_pending ?ms0 = Some ?actual,
        Hok : syscall_spec (sys_input ?segs0 ?ms0 ?actual) ?m0
                (Ok ?eff ?model' ?events) |- _ =>
          assert (actual = expected) by congruence; subst actual;
          exact (Hno eff model' events Hok)
      end.
Qed.

(** Deterministic ordinary instructions followed by a syscall-spec Unmodeled
    prove the universal source escape, not merely existential
    reachability. *)
Lemma msteps_spec_err_all_traces_error : forall ms ms' model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = Some x8 ->
  syscall_spec (sys_input segs ms' x8) model Unmodeled ->
  all_traces_error segs (mkCfg ms model).
Proof.
  intros ms ms' model x8 Hh Hlazy Hm Hsvc Hspec.
  eapply msteps_all_traces_error; [exact Hh | exact Hlazy | exact Hm |].
  eapply spec_err_all_traces_error; eassumption.
Qed.

(* ------------------------------------------------------------------------- *)
(* Ergonomic nodes.                                                           *)
(* ------------------------------------------------------------------------- *)

(** Exit leaf with a small literal code. *)
Lemma tfo_exit_code : forall ms model x8 code,
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  ms_gpr ms 0 = code ->
  bv_and code (Z_to_bv 64 255) = code ->
  to_fout ms model (fun o => o = (code, m_fs model)).
Proof.
  intros ms model x8 code Hsvc Hx8 Hg Hland.
  apply (tfo_exit ms model x8); [exact Hsvc | exact Hx8 |].
  intro o. rewrite Hg, Hland. tauto.
Qed.

(** A syscall with a UNIQUE admissible outcome (file read/write, close,
    open-ENOENT): sequential composition. *)
Lemma tfo_sys_det : forall ms model x8 eff model' U,
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ->
  (forall eff2 m2 evs2,
      syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) ->
      eff2 = eff /\ m2 = model' /\ evs2 = []) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  m_halted model' = None ->
  m_vm_lazy model' = [] ->
  to_fout (advance_past_svc (apply_effect ms eff)) model' U ->
  to_fout ms model U.
Proof.
  intros ms model x8 eff model' U Hsvc Hok Huniq Hne Hh' Hlazy' Hcont.
  apply (tfo_sys ms model x8 (fun _ _ => U) U); [exact Hsvc | exact Hne | | | |].
  - exists eff, model', []. exact Hok.
  - intros eff2 m2 evs2 Hs.
    destruct (Huniq eff2 m2 evs2 Hs) as (_ & -> & ->).
    repeat split; assumption.
  - intros eff2 m2 evs2 Hs.
    destruct (Huniq eff2 m2 evs2 Hs) as (-> & -> & _). exact Hcont.
  - intro o. split.
    + intro Ho. exists eff, model', []. auto.
    + intros (e2 & m2 & ev2 & _ & Ht). exact Ht.
Qed.

(** A syscall every admissible outcome of which leaves the model as it
    was and returns no event, but whose RETURN is not unique (an errno
    and the walk's own refusals beside it): one continuation per
    admitted effect, all into the same outcome set. *)
Lemma tfo_sys_same_model : forall ms model x8 eff0 U,
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff0 model []) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall eff2 m2 evs2,
      syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) ->
      m2 = model /\ evs2 = []
      /\ to_fout (advance_past_svc (apply_effect ms eff2)) model U) ->
  to_fout ms model U.
Proof.
  intros ms model x8 eff0 U Hsvc Hok Hne Hh Hlazy Hall.
  apply (tfo_sys ms model x8 (fun _ _ => U) U); [exact Hsvc | exact Hne | | | |].
  - exists eff0, model, []. exact Hok.
  - intros eff2 m2 evs2 Hs.
    destruct (Hall eff2 m2 evs2 Hs) as (-> & -> & _).
    repeat split; assumption.
  - intros eff2 m2 evs2 Hs.
    destruct (Hall eff2 m2 evs2 Hs) as (-> & _ & Ht). exact Ht.
  - intro o. split.
    + intro Ho. exists eff0, model, []. auto.
    + intros (e2 & m2 & ev2 & _ & Ht). exact Ht.
Qed.

End WithSegs.

(* ========================================================================= *)
(* Syscall decoding through the verified checker                             *)
(* ========================================================================= *)

(* ----- dispatch (Z-characterized syscall numbers) ----- *)

Lemma check_syscall_56 : forall segs ms x8 eff m,
  bv_unsigned x8 = 56%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_openat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
                 (ms_gpr ms 2) eff m.
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

Lemma check_syscall_57 : forall segs ms x8 eff m,
  bv_unsigned x8 = 57%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_close (fd32 (ms_gpr ms 0)) eff m.
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

Lemma check_syscall_63 : forall segs ms x8 eff m,
  bv_unsigned x8 = 63%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
               (ms_gpr ms 2) eff m.
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

Lemma check_syscall_64 : forall segs ms x8 eff m,
  bv_unsigned x8 = 64%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_write (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
                (ms_gpr ms 2) eff m.
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

(* ----- open-result algebra ----- *)

(** An in-range fd is never an error-encoded return. *)
Lemma fd_not_error : forall fd : word,
  (bv_unsigned fd < 2 ^ 31)%Z -> addr_is_error_b fd = false.
Proof.
  intros fd H. unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge. lia.
Qed.

(** Recover the errno from an errno-encoded return value. *)
Lemma errno_ret_recover : forall e,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  (two_pow_64 - bv_unsigned (errno_ret e))%Z = e.
Proof.
  intros e H1 H2. rewrite (errno_ret_unsigned e H1 H2). lia.
Qed.

(** Membership and range facts for openat's injectable errno set. *)
Lemma ENOMEM_in_openat_errnos : In ENOMEM openat_errnos.
Proof. left. reflexivity. Qed.

Lemma openat_errno_range : forall e,
  In e openat_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range openat_errnos e eq_refl HIn). Qed.

Lemma check_open_result_never_unmodeled : forall eff m mk,
  check_open_result eff m mk <> CheckUnmodeled.
Proof.
  intros [ret ws zs us cs copyins] m mk.
  unfold check_open_result, check_new_fd_result.
  destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?];
    destruct copyins as [|? ?];
    try discriminate.
  destruct (errno_ret_in openat_errnos ret); [discriminate|].
  destruct (fd_lookup (m_fds m) ret); [discriminate|].
  destruct (bv_eqb ret (alloc_fd (m_fds m))); discriminate.
Qed.

Lemma check_open_result_ok_iff : forall eff m (mk : word -> Model) m' evs,
  check_open_result eff m mk = CheckOk m' evs <->
  ((exists e, In e openat_errnos /\ eff = mkEffect (errno_ret e) [] []
              /\ m' = m /\ evs = [])
   \/ (exists fd, fd_lookup (m_fds m) fd = None /\ fd = alloc_fd (m_fds m)
                  /\ eff = mkEffect fd [] [] /\ m' = mk fd /\ evs = [])).
Proof.
  intros [ret ws zs us cs copyins] m mk m' evs.
  unfold check_open_result, check_new_fd_result. split.
  - intro H.
    destruct ws as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (errno_ret_in openat_errnos ret) eqn:Herr; try rewrite Herr in H.
    + inversion H; subst.
      apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
      left. exists e. auto.
    + destruct (fd_lookup (m_fds m) ret) eqn:Hlk; try rewrite Hlk in H;
        [discriminate|].
      destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; try rewrite Heq in H;
        [|discriminate].
      inversion H; subst.
      right. exists ret. apply bv_eqb_eq in Heq. auto.
  - intros [ (e & HIn & Heff & -> & ->)
           | (fd & Hlk & Heq & Heff & -> & ->) ].
    + inversion Heff; subst.
      rewrite (errno_ret_in_intro _ e HIn). reflexivity.
    + inversion Heff; subst.
      rewrite errno_ret_in_alloc_fd by reflexivity.
      rewrite Hlk, bv_eqb_refl. reflexivity.
Qed.

Definition open_copyins (ms : machine_state) : list (word * nat) :=
  [(ms_gpr ms 1,
    cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)].

Definition check_open_result_copyins (reads : list (word * nat))
    (eff : SyscallEffect) (m : Model) (mk : word -> Model) : check_result :=
  check_copyins reads eff (check_open_result (clear_copyins eff) m mk).

Lemma effect_from_copyins_and_clear : forall eff reads core,
  eff_copyins eff = reads -> clear_copyins eff = core ->
  eff = with_copyins reads core.
Proof.
  intros [ret ws zs us cs copyins] reads core Hreads Hcore.
  cbn [eff_copyins] in Hreads. subst copyins.
  unfold clear_copyins, with_copyins in Hcore |- *.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies] in Hcore |- *.
  inversion Hcore. reflexivity.
Qed.

Lemma check_open_result_copyins_never_unmodeled : forall reads eff m mk,
  check_open_result_copyins reads eff m mk <> CheckUnmodeled.
Proof.
  intros reads eff m mk.
  unfold check_open_result_copyins, check_copyins.
  destruct (access_ranges_eqb (eff_copyins eff) reads);
    [apply check_open_result_never_unmodeled|discriminate].
Qed.

Lemma check_open_result_copyins_ok_iff :
  forall reads eff m (mk : word -> Model) m' evs,
  check_open_result_copyins reads eff m mk = CheckOk m' evs <->
  ((exists e, In e openat_errnos /\
      eff = with_copyins reads (mkEffect (errno_ret e) [] []) /\
      m' = m /\ evs = [])
   \/ (exists fd, fd_lookup (m_fds m) fd = None /\
      fd = alloc_fd (m_fds m) /\
      eff = with_copyins reads (mkEffect fd [] []) /\
      m' = mk fd /\ evs = [])).
Proof.
  intros reads eff m mk m' evs.
  unfold check_open_result_copyins, check_copyins.
  destruct (access_ranges_eqb (eff_copyins eff) reads) eqn:Hreads.
  - apply access_ranges_eqb_eq in Hreads.
    rewrite check_open_result_ok_iff. split.
    + intros [(e & HIn & Hcore & -> & ->)
             | (fd & Hlk & Heq & Hcore & -> & ->)].
      * left. exists e. repeat split; try assumption.
        eapply effect_from_copyins_and_clear; eassumption.
      * right. exists fd. repeat split; try assumption.
        eapply effect_from_copyins_and_clear; eassumption.
    + intros [(e & HIn & Heff & -> & ->)
             | (fd & Hlk & Heq & Heff & -> & ->)].
      * left. exists e. repeat split; try assumption.
        rewrite Heff. reflexivity.
      * right. exists fd. repeat split; try assumption.
        rewrite Heff. reflexivity.
  - split; [discriminate|].
    intros [(e & _ & Heff & _)
           | (fd & _ & _ & Heff & _)].
    all: rewrite Heff in Hreads; cbn [eff_copyins with_copyins] in Hreads;
      pose proof (proj2 (access_ranges_eqb_eq reads reads) eq_refl) as Htrue;
      congruence.
Qed.

Lemma check_copyins_after_ret_only : forall reads eff r m evs,
  Prelude.check_copyins_after reads eff
      (check_ret_only (clear_copyins eff) r m evs) =
  check_ret_only_copyins reads eff r m evs.
Proof.
  intros reads eff r m evs.
  unfold Prelude.check_copyins_after, check_ret_only_copyins.
  destruct (check_ret_only (clear_copyins eff) r m evs) eqn:Hresult.
  - reflexivity.
  - unfold check_copyins.
    destruct (access_ranges_eqb (eff_copyins eff) reads); reflexivity.
  - exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.

(* ========================================================================= *)
(* R22: THE OPEN ARM'S CONTRACT -- the holes this lane leaves open           *)
(* ========================================================================= *)

(** WHAT IS OPEN HERE, WHY IT IS OPEN, AND WHO CLOSES IT.

    #1011 section 5 rewrites every path-taking arm into "a match on
    [Fs.resolve] plus its existing flag ladder".  That rewrite is a
    SEPARATE LANE.  At this commit the open arm still looks a RAW
    PATHNAME up as a key: [Open.check_openat_read] and
    [Open.check_openat_create] call [fs_lookup (m_fs m) p] on the
    pathname the program passed.

    Under [Fs.wf_fs] that lookup CANNOT SUCCEED for a plain name.
    Every key of a well-formed image is absolute and a plain name has
    no separator at all, which is [plain_name_not_a_key] above.  So the
    checker-level open answers below cannot be both TRUE OF THE ARM AS
    IT STANDS and STATED OVER RESOLUTION -- and stated over resolution
    is what every consumer of them needs, now and after the merge.
    Stating them over the raw lookup instead would keep them provable
    and make them VACUOUS, and would have to be undone at the arms
    merge regardless.

    THE HOLES ARE THEREFORE STATED, not assumed quietly.  Each is one
    named [Prop] about [Open.check_openat_resolved] AND NOTHING ELSE.
    That function's type -- pathname, flag word, effect, model, to a
    [check_result] -- is the one the arms lane keeps: the dispatcher
    still receives the raw pathname, because resolving it against
    [m_cwd] is its own job, so these four statements are well typed on
    both sides of the merge.

    EVERYTHING OUTSIDE THAT DISPATCHER IS PROVED HERE and is not a
    hole: the syscall dispatch on [x8], the modeled-flag gate (which
    runs BEFORE the pathname is fetched, as [build_open_flags] runs
    before [getname]), the pathname copy-in and its ledger, the empty
    pathname's -ENOENT, and the [AT_FDCWD] gate.  Each lemma below
    therefore does the work it always did MINUS EXACTLY ONE STEP.

    WHO CLOSES THEM: the arms lane, by proving these four [Prop]s of
    its rewritten dispatcher.  Nothing else in the tree may assume
    them, and nothing else does -- grep [openat_arm_] for every place
    this lane is conditional.

    SAID FLATLY, BECAUSE IT IS THE THING A READER MUST NOT MISS: at
    this head all four are FALSE of [Open.check_openat_resolved], not
    merely unproved.  Take a plain name [p] resolving to
    [RFound k (EFile d)]; the arm reaches [Open.check_openat_read],
    which looks [p] itself up, misses, and answers -ENOENT, where
    [openat_arm_read_found] demands a descriptor on [k].  So every
    [_ns] lemma below is VACUOUSLY TRUE, and nothing in this file tests
    any of them.

    WHAT DOES CONSTRAIN THEM, and it is not nothing: each [_ns] lemma
    rewrites with its contract and must then match its OWN conclusion,
    so the right-hand side is pinned by the proof even though the
    hypotheses are not.  A contract that disagreed with the answer its
    lemma claims -- a wrong descriptor kind, a wrong key, a model that
    was written when it should not be -- would fail to compile.  What
    a green build here does NOT show is that the four match the arm the
    other lane writes; that is the arms lane's obligation, and it is
    the whole of what is owed. *)

(** O_RDONLY, and the resolution FOUND A REGULAR FILE: the read-open
    success builder, ON THE FILE'S INODE.  The descriptor carries [i],
    the identity the key [k] names, not the pathname [p] the program
    spelled: [stat("./x")] and [stat("x")] name one file and share one
    inode and one stat pin.  The walk is the one the flag word asks for
    ([Open.open_walk_mode]); the arm is chosen by the word's shape
    ([Open.open_shape]). *)
Definition openat_arm_read_found : Prop :=
  forall (p k : Fs.path) (i : Fs.ino) (flags : word)
         (eff : SyscallEffect) (m : Model),
    open_shape flags = 0%Z ->
    Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p
      = (Fs.RFound k (Fs.EFile i), Fs.LastNorm, false) ->
    Open.check_openat_resolved p flags eff m
    = check_open_result eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd
                               (FdFile i (Z_to_bv 64 0))) m).

(** O_RDONLY, and the resolution FOUND A DIRECTORY: a descriptor on the
    resolved key, in the shape [State.FdDir] takes it.

    THIS IS WHERE "." AND ".." WENT.  The pre-namespace arm settled both
    out of a magic-name table and minted a descriptor on a key it
    computed for the spelling; the walk settles them out of itself, so
    [openat(".", O_RDONLY)] is a descriptor on the WORKING DIRECTORY and
    [openat("..", O_RDONLY)] one on its parent.  It is also where
    [openat("/work", O_RDONLY)] lands, which the old arm could not
    answer at all.  [may_open]'s S_IFDIR arm refuses only MAY_WRITE,
    which O_RDONLY does not carry, so Linux succeeds here.

    THE LAST KIND IS QUANTIFIED rather than pinned to [Fs.LastNorm],
    and that is the difference from the three contracts beside it.  The
    read arm reads the outcome alone, so a directory reached as "."
    ([Fs.LastDot]) and one reached as a name ([Fs.LastNorm]) take the
    same row -- and a consumer of "." needs exactly that, since
    [Fs.resolve_dot] hands back [Fs.LastDot]. *)
Definition openat_arm_read_dir : Prop :=
  forall (p k : Fs.path) (lk : Fs.LastKind) (flags : word)
         (eff : SyscallEffect) (m : Model),
    open_shape flags = 0%Z ->
    Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p
      = (Fs.RFound k Fs.EDir, lk, false) ->
    Open.check_openat_resolved p flags eff m
    = check_open_result eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd (FdDir k)) m).

(** O_RDONLY, and the LAST COMPONENT IS ABSENT under a directory that
    resolved: -ENOENT.  [Fs.RMissing] is the shape #1011 section 5
    gives this row, and it is strictly more informative than the old
    absent lookup: every prefix WAS a directory, which is what
    distinguishes it from [Fs.RAbsent]. *)
Definition openat_arm_read_missing : Prop :=
  forall (p par nm : Fs.path) (flags : word) (eff : SyscallEffect) (m : Model),
    open_shape flags = 0%Z ->
    Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p
      = (Fs.RMissing par nm, Fs.LastNorm, false) ->
    Open.check_openat_resolved p flags eff m
    = check_ret_only eff (errno_ret ENOENT) m [].

(** THE KEY AN O_CREAT|O_TRUNC OPEN WRITES WHEN IT CREATES.  The
    write-create arm has two ways in: the name was absent and is made,
    or a regular file was there and is truncated.  Only the first is
    this contract's.  A name that was absent is a fresh file at the key
    the walk reached ([Open.create_file_fs] at [Fs.child_key par nm],
    inode [Open.create_file_ino]), and the open's branch set is the
    fresh-descriptor acceptor's alone.  A regular file that was there
    admits a third branch beside the descriptor and the injected
    errnos: the -ETXTBSY of a file something executes
    ([Open.open_write_existing]), so its branch set is not this
    acceptor's; a consumer that opens an existing destination reads
    that open through [Common.FileSimWalk.open_arm], as the copy
    examples do.

    THE TRAILING-SLASH FLAG IS [false]: a trailing slash with O_CREAT is
    -EISDIR BEFORE any lookup, so the create walk stops in front of
    such a name ([Fs.RParent]), a different row. *)
Definition resolve_create_target (m : Model) (flags : word) (p : Fs.path)
    (fs' : Fs.Fs) (i : Fs.ino) : Prop :=
  exists par nm,
    Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p
      = (Fs.RMissing par nm, Fs.LastNorm, false)
    /\ fs' = create_file_fs (m_fs m) (Fs.child_key par nm)
    /\ i = create_file_ino (m_fs m).

Definition openat_arm_create : Prop :=
  forall (p : Fs.path) (flags : word) (eff : SyscallEffect) (m : Model)
         (fs' : Fs.Fs) (i : Fs.ino),
    open_shape flags = wr_create_flags ->
    resolve_create_target m flags p fs' i ->
    Open.check_openat_resolved p flags eff m
    = check_open_result eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd
                               (FdFileW i (Z_to_bv 64 0)))
                     (with_fs fs' m)).

(** O_WRONLY|O_CREAT|O_TRUNC on a DIRECTORY: -EISDIR, model untouched.

    THIS ROW GETS STRICTLY BETTER UNDER R22 and the improvement is
    worth naming.  The old arm could not see a directory, so it
    INFERRED one from the image -- [fs_under], "some key lives under
    this name" -- which missed an empty directory entirely and was the
    reason directory existence was a derived notion at all (#1011
    section 1).  With [Fs.EDir] an entry, the test is the entry's kind,
    and an empty directory answers -EISDIR like any other. *)
(** THE LAST KIND IS QUANTIFIED HERE TOO: the create arm reads the
    outcome alone, so the -EISDIR this contract names is the DIRECTORY
    row whatever kind the walk left.  A caller who resolved "." reaches
    the same answer through the same row, which is what lets the dot
    case share this contract instead of carrying one of its own. *)
(** MINTING A DESCRIPTOR CANNOT CHANGE A CREATE TARGET, because it
    cannot change how a pathname resolves -- [resolve_model_with_fds]
    says the second part and this carries it through.  The image a
    create leaves is the original's, which the descriptor table does not
    touch.  Named because a proof that has already opened the source and
    is opening the destination holds the target at the ORIGINAL model
    and needs it at the one with the first descriptor in it. *)
Lemma resolve_create_target_with_fds : forall m g flags p fs' i,
  resolve_create_target m flags p fs' i ->
  resolve_create_target (with_fds g m) flags p fs' i.
Proof.
  intros m g flags p fs' i (par & nm & Hr & Hfs & Hi).
  exists par, nm. rewrite resolve_model_with_fds. auto.
Qed.

Definition openat_arm_create_isdir : Prop :=
  forall (p k : Fs.path) (lk : Fs.LastKind) (flags : word)
         (eff : SyscallEffect) (m : Model),
    open_shape flags = wr_create_flags ->
    Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p
      = (Fs.RFound k Fs.EDir, lk, false) ->
    Open.check_openat_resolved p flags eff m
    = check_ret_only eff (errno_ret EISDIR) m [].

(* ========================================================================= *)
(* THE FOUR CONTRACTS, DISCHARGED                                            *)
(* ========================================================================= *)

(** THE HANDSHAKE THIS FILE WAS WRITTEN FOR.  The four [Prop]s above
    were stated by the Common lane as the one thing it could not prove:
    each is a claim about the resolved-open dispatcher, and at that head
    the dispatcher still looked a raw pathname up as a key, so each was
    FALSE rather than merely unproved.  The arms lane replaced that
    dispatcher with a match on [Fs.resolve], and the four are now what
    the arm does, one branch of its flag ladder each.

    THE PROOFS ARE COMPUTATION AND NOTHING ELSE, which is the shape a
    contract of this kind should have: unfold the dispatcher, rewrite
    with the resolution the contract hands over, reduce the flag ladder
    to the branch the flag word selects, and read off that branch.  No
    lemma about the file system is used and none should be -- a
    contract that needed one would be making a claim about the image
    rather than about the arm.

    WHAT CHANGES FOR A READER: the four [_ns] lemmas below are no longer
    vacuous.  Each still takes its contract as a hypothesis, because
    that is how they were written and rewriting them is the Example
    re-proof's business rather than this lane's, but every call site can
    now discharge the hypothesis with the matching lemma here. *)

Local Lemma wr_create_flags_not_rd : Z.eqb wr_create_flags 0 = false.
Proof. vm_compute. reflexivity. Qed.

(** A PATHNAME THE WALK FOUND OR FOUND MISSING IS NOT "/proc/self/fd/N".
    The open arm tests [proc_self_fd] on the raw pathname ahead of the
    walk; every such pathname starts at the root with the component
    "proc", which the walk answers [Fs.ROutside] (or [Fs.RNotDir] /
    [Fs.RAbsent] on an image with no directory at the root), so a
    resolution the contracts below hand over rules it out. *)
Lemma proc_self_fd_none_of_found_or_missing : forall md fs cwd p r lk ts,
  Fs.resolve md fs cwd p = (r, lk, ts) ->
  match r with Fs.RFound _ _ | Fs.RMissing _ _ => True | _ => False end ->
  proc_self_fd p = None.
Proof.
  intros md fs cwd p r lk ts Hres Hr.
  destruct (proc_self_fd p) as [n|] eqn:H; [exfalso | reflexivity].
  unfold proc_self_fd in H.
  destruct (path_strip_prefix proc_self_fd_prefix p) as [rest|] eqn:Hs;
    [|discriminate H].
  apply path_strip_prefix_app in Hs. subst p.
  unfold Fs.resolve, Fs.resolve_res, Fs.walk_from in Hres.
  assert (Hst : Fs.resolve_start cwd (proc_self_fd_prefix ++ rest) = Fs.root)
    by (vm_compute; reflexivity).
  rewrite Hst in Hres.
  destruct (Fs.fs_lookup fs Fs.root) as [e|].
  - destruct md; destruct e; vm_compute in Hres;
      injection Hres as Hr' _ _; subst r; exact Hr.
  - injection Hres as Hr' _ _. subst r. exact Hr.
Qed.

(** O_RDONLY onto a regular file: the descriptor carries the file's
    INODE, never the pathname [p] the program spelled. *)
Lemma openat_arm_read_found_holds : openat_arm_read_found.
Proof.
  intros p k i flags eff m Hfl Hres.
  unfold Open.check_openat_resolved.
  rewrite (proc_self_fd_none_of_found_or_missing _ _ _ _ _ _ _ Hres I).
  rewrite Hres. cbv beta iota zeta.
  rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read. cbv beta iota.
  unfold Open.check_open_result_mk. reflexivity.
Qed.

(** O_RDONLY onto a DIRECTORY: a descriptor on the resolved key.
    Computation on the same dispatcher, with the last kind left
    quantified because the read arm does not read it. *)
Lemma openat_arm_read_dir_holds : openat_arm_read_dir.
Proof.
  intros p k lk flags eff m Hfl Hres.
  unfold Open.check_openat_resolved.
  rewrite (proc_self_fd_none_of_found_or_missing _ _ _ _ _ _ _ Hres I).
  rewrite Hres. cbv beta iota zeta.
  rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read. cbv beta iota.
  unfold Open.check_open_result_mk. reflexivity.
Qed.

(** O_RDONLY onto a last component that is ABSENT under a directory
    that resolved: -ENOENT, and the model is untouched. *)
Lemma openat_arm_read_missing_holds : openat_arm_read_missing.
Proof.
  intros p par nm flags eff m Hfl Hres.
  unfold Open.check_openat_resolved.
  rewrite (proc_self_fd_none_of_found_or_missing _ _ _ _ _ _ _ Hres I).
  rewrite Hres. cbv beta iota zeta.
  rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read. reflexivity.
Qed.

(** O_WRONLY|O_CREAT|O_TRUNC onto a name that was absent: the
    fresh-descriptor acceptor, a new inode at [Fs.child_key par nm]. *)
Lemma openat_arm_create_holds : openat_arm_create.
Proof.
  intros p flags eff m fs' i Hfl Htgt.
  unfold Open.check_openat_resolved.
  destruct Htgt as (par & nm & Hres & Hfs & Hi); subst fs' i;
    rewrite (proc_self_fd_none_of_found_or_missing _ _ _ _ _ _ _ Hres I);
    rewrite Hres; cbv beta iota zeta;
    rewrite Hfl, wr_create_flags_not_rd; cbv beta iota;
    rewrite Z.eqb_refl; cbv beta iota;
    unfold Open.check_openat_create; cbv beta iota;
    unfold check_create_wronly; reflexivity.
Qed.

(** O_WRONLY|O_CREAT|O_TRUNC onto a DIRECTORY: -EISDIR, model
    untouched.  The test is the entry's kind now, where the old arm had
    to infer a directory from the keys underneath it. *)
Lemma openat_arm_create_isdir_holds : openat_arm_create_isdir.
Proof.
  intros p k lk flags eff m Hfl Hres.
  unfold Open.check_openat_resolved.
  rewrite (proc_self_fd_none_of_found_or_missing _ _ _ _ _ _ _ Hres I).
  rewrite Hres. cbv beta iota zeta.
  rewrite Hfl, wr_create_flags_not_rd. cbv beta iota.
  rewrite Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_create. reflexivity.
Qed.

(** THE WALK'S OWN REFUSALS AN OPEN OF [p] ADMITS ([Fs.Namei.walk_errnos]
    of the walk the flag word asks for). *)
Definition open_walk_errnos (flags : word) (m : Model) (p : Fs.path) : list Z :=
  walk_errnos (Fs.path_last_kind p)
    (Fs.resolve_res (open_walk_mode flags) (m_fs m) (m_cwd m) p).

(** Every walk a call is handed can refuse with -ENOMEM, so its
    refusals cover [getname_flags]' own errno ([Fs.Namei.getname_errnos]). *)
Lemma walk_errnos_enomem : forall lk w, In ENOMEM (walk_errnos lk w).
Proof. intros [| | |] w; left; reflexivity. Qed.

(** A PLAIN OPEN WALK refuses only with errnos the fresh-descriptor
    acceptor already takes: a walk that followed no link
    ([Fs.wr_followed]), handed no over-long name to a lookup
    ([Fs.wr_long]) and stayed inside the image admits only -ENOMEM and
    -EACCES, both in [Fs.Open.openat_errnos].  A walk that followed a
    link also admits -ELOOP, which an open that returns a descriptor
    does not otherwise answer, so a success node needs this premise to
    state its outcome set exactly. *)
Definition open_walk_plain (flags : word) (m : Model) (p : Fs.path) : Prop :=
  incl (open_walk_errnos flags m p) openat_errnos.

(** The two flag words the record-level nodes below take, and the walks
    they ask for ([Open.open_walk_mode]): O_RDONLY follows a last link
    and asks for no folder; O_WRONLY|O_CREAT|O_TRUNC is a create walk
    that follows one. *)
Lemma open_walk_mode_rd : open_walk_mode (Z_to_bv 64 0) = Fs.WalkFull true false.
Proof. vm_compute. reflexivity. Qed.

Lemma open_walk_mode_wr : open_walk_mode (Z_to_bv 64 577) = Fs.WalkCreate true.
Proof. vm_compute. reflexivity. Qed.

(** The walk's own refusals ([Checks.Sys.Prelude.check_walk_refusals])
    add nothing to an open that can return a descriptor when every one
    of them is among [Fs.Open.openat_errnos], which the fresh-descriptor
    acceptor already takes. *)
Lemma walk_refusals_open_result : forall md i pathp eff m mk,
  (forall es, walk_reached md i m pathp = Some es -> incl es openat_errnos) ->
  check_walk_refusals md i pathp eff m (check_open_result eff m mk)
  = check_open_result eff m mk.
Proof.
  intros md i pathp eff m mk Hw. unfold check_walk_refusals.
  destruct (check_open_result eff m mk) eqn:Hr; try reflexivity.
  destruct (walk_reached md i m pathp) as [es|] eqn:Hes; [|reflexivity].
  destruct eff as [r ws zs us cs ci]; destruct ws, zs, us, cs, ci; try reflexivity.
  destruct (errno_ret_in es r) eqn:He; [|reflexivity].
  exfalso. unfold check_open_result, check_new_fd_result in Hr.
  apply errno_ret_in_true in He. destruct He as (e & Hin & ->).
  assert (Hin' : In e openat_errnos) by exact (Hw es eq_refl e Hin).
  rewrite (errno_ret_in_intro _ _ Hin') in Hr. discriminate.
Qed.

(** What a reached walk refuses with, read off the pathname and the
    walk. *)
Lemma walk_reached_si : forall md segs ms x8 model p,
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  walk_reached md (sys_input segs ms x8) model (ms_gpr ms 1)
  = Some (walk_errnos (Fs.path_last_kind p)
            (Fs.resolve_res md (m_fs model) (m_cwd model) p)).
Proof.
  intros md segs ms x8 model p Hpath Hpe. unfold walk_reached.
  rewrite in_mem_si, Hpath, Hpe. reflexivity.
Qed.

Lemma walk_refusals_open_result_si : forall segs ms x8 model p eff mk,
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  open_walk_plain (ms_gpr ms 2) model p ->
  check_walk_refusals (open_walk_mode (ms_gpr ms 2)) (sys_input segs ms x8)
    (ms_gpr ms 1) eff model (check_open_result eff model mk)
  = check_open_result eff model mk.
Proof.
  intros segs ms x8 model p eff mk Hpath Hpe Hplain.
  apply walk_refusals_open_result. intros es Hes.
  rewrite (walk_reached_si _ segs ms x8 model p Hpath Hpe) in Hes.
  injection Hes as <-. exact Hplain.
Qed.

(** THE ARM-INDEPENDENT HALF OF EVERY OPEN, proved once so that the
    four lemmas below differ from each other in exactly one rewrite.

    Everything here runs before [Open.check_openat_resolved] is
    reached: the flag word is judged first ([build_open_flags] before
    [getname]), then the pathname is fetched and its copy-in range
    recorded, then the empty pathname is -ENOENT ([getname_flags]
    returns it before any walk), then a table with no free descriptor
    would be answered ([Open.openat_core_spec]; the table here has one),
    then the dirfd gate.  Around all of it stand [getname_flags]' own
    refusals ([check_getname_refusals]). *)
Lemma openat_reduces_to_resolved : forall segs ms x8 model p eff,
  bv_unsigned x8 = 56%Z ->
  modeled_open_flags (ms_gpr ms 2) = true ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  check_syscall (sys_input segs ms x8) eff model
  = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
      (Prelude.check_copyins_after (open_copyins ms) eff
         (check_walk_refusals (open_walk_mode (ms_gpr ms 2)) (sys_input segs ms x8)
            (ms_gpr ms 1) (clear_copyins eff) model
            (Open.check_openat_resolved p (ms_gpr ms 2) (clear_copyins eff) model))).
Proof.
  intros segs ms x8 model p eff Hno Hfl Hdirfd Hpath Hpe Hfree.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite Hfl. cbn [negb]. cbv beta iota.
  unfold openat_name_fetched, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hpe, (lowest_fd_none_free _ Hfree). cbn [negb andb]. cbv beta iota.
  rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
  reflexivity.
Qed.

(** The two modeled open shapes reduce the checker to
    [check_open_result] with the respective success-model builder, and
    the two deterministic-errno shapes to [check_ret_only].  Each takes
    its arm contract above, and nothing else about the arm; the success
    shapes also take [open_walk_plain], since a walk that followed a
    link admits -ELOOP beside the descriptor. *)
Lemma openat_rd_check_ns : forall segs ms x8 model p k i,
  openat_arm_read_found ->
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  open_shape (ms_gpr ms 2) = 0%Z ->
  Fs.resolve (open_walk_mode (ms_gpr ms 2)) (m_fs model) (m_cwd model) p
    = (Fs.RFound k (Fs.EFile i), Fs.LastNorm, false) ->
  open_walk_plain (ms_gpr ms 2) model p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
        (check_open_result_copyins (open_copyins ms) eff model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFile i (Z_to_bv 64 0))) model)).
Proof.
  intros segs ms x8 model p k i Harm Hno Hdirfd Hpath Hpe Hfl Hres Hplain Hfree eff.
  rewrite (openat_reduces_to_resolved segs ms x8 model p eff Hno
             (modeled_open_flags_rd _ Hfl) Hdirfd Hpath Hpe Hfree).
  rewrite (Harm p k i (ms_gpr ms 2) (clear_copyins eff) model Hfl Hres).
  rewrite (walk_refusals_open_result_si segs ms x8 model p _ _ Hpath Hpe Hplain).
  unfold Prelude.check_copyins_after, check_open_result_copyins.
  destruct (check_open_result (clear_copyins eff) model
    (fun fd : word =>
       with_fds
         (fd_insert (m_fds model) fd (FdFile i (Z_to_bv 64 0))) model))
    eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

(** O_RDONLY OF A DIRECTORY: the same branch set as the file case with
    the descriptor kind changed, and the last kind left quantified so
    that a caller who resolved "." ([Fs.LastDot]) reaches it. *)
Lemma openat_rd_dir_check_ns : forall segs ms x8 model p k lk,
  openat_arm_read_dir ->
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  open_shape (ms_gpr ms 2) = 0%Z ->
  Fs.resolve (open_walk_mode (ms_gpr ms 2)) (m_fs model) (m_cwd model) p
    = (Fs.RFound k Fs.EDir, lk, false) ->
  open_walk_plain (ms_gpr ms 2) model p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
        (check_open_result_copyins (open_copyins ms) eff model
           (fun fd => with_fds (fd_insert (m_fds model) fd (FdDir k)) model)).
Proof.
  intros segs ms x8 model p k lk Harm Hno Hdirfd Hpath Hpe Hfl Hres Hplain Hfree eff.
  rewrite (openat_reduces_to_resolved segs ms x8 model p eff Hno
             (modeled_open_flags_rd _ Hfl) Hdirfd Hpath Hpe Hfree).
  rewrite (Harm p k lk (ms_gpr ms 2) (clear_copyins eff) model Hfl Hres).
  rewrite (walk_refusals_open_result_si segs ms x8 model p _ _ Hpath Hpe Hplain).
  unfold Prelude.check_copyins_after, check_open_result_copyins.
  destruct (check_open_result (clear_copyins eff) model
    (fun fd : word => with_fds (fd_insert (m_fds model) fd (FdDir k)) model))
    eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

(** O_RDONLY of an absent last component: the deterministic -ENOENT, on
    a table with a free descriptor (with none, -EMFILE comes first). *)
Lemma openat_rd_enoent_check_ns : forall segs ms x8 model p par nm,
  openat_arm_read_missing ->
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  open_shape (ms_gpr ms 2) = 0%Z ->
  Fs.resolve (open_walk_mode (ms_gpr ms 2)) (m_fs model) (m_cwd model) p
    = (Fs.RMissing par nm, Fs.LastNorm, false) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
        (Prelude.check_copyins_after (open_copyins ms) eff
           (check_walk_refusals (open_walk_mode (ms_gpr ms 2)) (sys_input segs ms x8)
              (ms_gpr ms 1) (clear_copyins eff) model
              (check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []))).
Proof.
  intros segs ms x8 model p par nm Harm Hno Hdirfd Hpath Hpe Hfl Hres Hfree eff.
  rewrite (openat_reduces_to_resolved segs ms x8 model p eff Hno
             (modeled_open_flags_rd _ Hfl) Hdirfd Hpath Hpe Hfree).
  rewrite (Harm p par nm (ms_gpr ms 2) (clear_copyins eff) model Hfl Hres).
  reflexivity.
Qed.

(** The write-create open: the branch set of a create, at the image and
    inode [resolve_create_target] names. *)
Lemma openat_wr_check_ns : forall segs ms x8 model p fs' i,
  openat_arm_create ->
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  open_shape (ms_gpr ms 2) = wr_create_flags ->
  resolve_create_target model (ms_gpr ms 2) p fs' i ->
  open_walk_plain (ms_gpr ms 2) model p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
        (check_open_result_copyins (open_copyins ms) eff model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFileW i (Z_to_bv 64 0)))
                        (with_fs fs' model))).
Proof.
  intros segs ms x8 model p fs' i Harm Hno Hdirfd Hpath Hpe Hfl Hres Hplain Hfree eff.
  rewrite (openat_reduces_to_resolved segs ms x8 model p eff Hno
             (modeled_open_flags_wr _ Hfl) Hdirfd Hpath Hpe Hfree).
  rewrite (Harm p (ms_gpr ms 2) (clear_copyins eff) model fs' i Hfl Hres).
  rewrite (walk_refusals_open_result_si segs ms x8 model p _ _ Hpath Hpe Hplain).
  unfold Prelude.check_copyins_after, check_open_result_copyins.
  destruct (check_open_result (clear_copyins eff) model
    (fun fd : word =>
       with_fds
         (fd_insert (m_fds model) fd (FdFileW i (Z_to_bv 64 0)))
         (with_fs fs' model)))
    eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

(** The write-create open of a pathname that resolves to a DIRECTORY:
    the checker reduces to the deterministic -EISDIR return and the
    model is untouched, on a table with a free descriptor.
    [Open.openat_create_spec] carries the
    derivation ([do_open]'s [d_is_dir], fs/namei.c:3951-3952); this is
    the proof-side handle on it, the twin of [openat_wr_check_ns] for
    the resolution the other cannot take. *)
Lemma openat_wr_isdir_check_ns : forall segs ms x8 model p k lk,
  openat_arm_create_isdir ->
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  open_shape (ms_gpr ms 2) = wr_create_flags ->
  Fs.resolve (open_walk_mode (ms_gpr ms 2)) (m_fs model) (m_cwd model) p
    = (Fs.RFound k Fs.EDir, lk, false) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
        (Prelude.check_copyins_after (open_copyins ms) eff
           (check_walk_refusals (open_walk_mode (ms_gpr ms 2)) (sys_input segs ms x8)
              (ms_gpr ms 1) (clear_copyins eff) model
              (check_ret_only (clear_copyins eff) (errno_ret EISDIR) model []))).
Proof.
  intros segs ms x8 model p k lk Harm Hno Hdirfd Hpath Hpe Hfl Hres Hfree eff.
  rewrite (openat_reduces_to_resolved segs ms x8 model p eff Hno
             (modeled_open_flags_wr _ Hfl) Hdirfd Hpath Hpe Hfree).
  rewrite (Harm p k lk (ms_gpr ms 2) (clear_copyins eff) model Hfl Hres).
  reflexivity.
Qed.

(** A call [walk_reached] gives no refusals takes none.  (The pathname
    arms reach that on every fetch the walk is not handed: a fault, no
    NUL within PATH_MAX, the empty name.) *)
Lemma check_walk_refusals_unreached : forall md i pathp eff m c,
  walk_reached md i m pathp = None -> check_walk_refusals md i pathp eff m c = c.
Proof.
  intros md i pathp eff m c H. unfold check_walk_refusals.
  destruct c; [reflexivity| |reflexivity]. rewrite H. reflexivity.
Qed.

(** A deterministic errno under the walk's refusals: what is accepted is
    that errno or, on a pathname the walk was handed, one of the
    refusals of that walk, each a bare return that leaves the model
    alone, with the pathname's copy-in on the ledger. *)
Lemma walk_refusals_ret_only_ok_iff : forall md i pathp reads eff r m m' evs,
  Prelude.check_copyins_after reads eff
    (check_walk_refusals md i pathp (clear_copyins eff) m
       (check_ret_only (clear_copyins eff) r m [])) = CheckOk m' evs <->
  m' = m /\ evs = []
  /\ (eff = with_copyins reads (mkEffect r [] [])
      \/ exists es e, walk_reached md i m pathp = Some es /\ In e es
                      /\ eff = with_copyins reads (mkEffect (errno_ret e) [] [])).
Proof.
  intros md i pathp reads [ret ws zs us cs ci] r m m' evs.
  rewrite Prelude.check_copyins_after_ok_iff.
  unfold clear_copyins, with_copyins.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
  destruct ws as [|w ws];
    [destruct zs as [|z zs];
      [destruct us as [|u us]; [destruct cs as [|c cs]|]|]|];
    cbn [check_ret_only].
  2-5: unfold check_walk_refusals;
       destruct (walk_reached md i m pathp); cbv beta iota;
       (split; [intros (_ & H); discriminate
               |intros (_ & _ & [H | (? & ? & _ & _ & H)]); discriminate]).
  destruct (bv_eqb ret r) eqn:Er.
  - apply bv_eqb_eq in Er; subst ret. cbn [check_walk_refusals]. split.
    + intros (-> & H). inversion H; subst. auto.
    + intros (-> & -> & [H | (es & e & _ & _ & H)]); inversion H; subst; auto.
  - unfold check_walk_refusals.
    destruct (walk_reached md i m pathp) as [es|] eqn:Hw.
    + destruct (errno_ret_in es ret) eqn:He; cbv beta iota.
      * split.
        -- intros (-> & H). inversion H; subst.
           apply errno_ret_in_true in He. destruct He as (e & Hin & ->).
           split; [reflexivity|split; [reflexivity|]].
           right. exists es, e. auto.
        -- intros (-> & -> & [H | (es' & e & _ & _ & H)]); inversion H; subst; auto.
      * split.
        -- intros (_ & H). discriminate.
        -- intros (-> & -> & [H | (es' & e & Hw' & Hin & H)]); inversion H; subst.
           ++ rewrite bv_eqb_refl in Er. discriminate.
           ++ injection Hw' as <-.
              rewrite (errno_ret_in_intro _ _ Hin) in He. discriminate.
    + cbv beta iota. split.
      * intros (_ & H). discriminate.
      * intros (-> & -> & [H | (es' & e & Hw' & _ & H)]).
        -- inversion H; subst. rewrite bv_eqb_refl in Er. discriminate.
        -- discriminate.
Qed.

Lemma walk_refusals_ret_only_no_unmodeled : forall md i pathp reads eff r m,
  Prelude.check_copyins_after reads eff
    (check_walk_refusals md i pathp (clear_copyins eff) m
       (check_ret_only (clear_copyins eff) r m [])) <> CheckUnmodeled.
Proof.
  intros md i pathp reads eff r m H.
  apply Prelude.check_copyins_after_unmodeled, check_walk_refusals_unmodeled in H.
  exact (check_ret_only_no_unmodeled _ _ _ _ H).
Qed.

(** THE EMPTY PATHNAME'S -ENOENT, which no arm ever sees: Linux's
    [getname_flags] returns -ENOENT for it BEFORE any walk, so the test
    is in the body ahead of the dispatcher and this lemma needs NO ARM
    CONTRACT.  It is the one open answer that survives the arms lane
    untouched, and #1011 section 3 pins the empty path per arm for the
    same reason.  Beside it stands [getname_flags]' -ENOMEM, raised
    before the copy that finds the name empty
    ([check_getname_refusals]).

    No dirfd hypothesis: the pathname is fetched before the dirfd is
    resolved, exactly as [getname] runs before [path_init]'s
    [fdget_raw]. *)
Lemma openat_empty_enoent_check : forall segs ms x8 model p,
  bv_unsigned x8 = 56%Z ->
  modeled_open_flags (ms_gpr ms 2) = true ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = true ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
        (Prelude.check_copyins_after (open_copyins ms) eff
           (check_walk_refusals (open_walk_mode (ms_gpr ms 2)) (sys_input segs ms x8)
              (ms_gpr ms 1) (clear_copyins eff) model
              (check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []))).
Proof.
  intros segs ms x8 model p Hno Hfl Hpath Hpe eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite Hfl. cbn [negb]. cbv beta iota.
  unfold openat_name_fetched, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hpe. cbn [negb andb]. cbv beta iota.
  reflexivity.
Qed.

(* ========================================================================= *)
(* THE PRE-NAMESPACE OPEN FAMILY, kept because its consumers are proved     *)
(* ========================================================================= *)

(** These are the open lemmas as they were before #1011, stated over the
    RAW LOOKUP the arm still performs.  They are kept, and the reason is
    not sentiment.

    THE TWO EXAMPLES' TOP-LEVEL THEOREMS HAVE NO ROOM FOR A CONTRACT.
    [Equivalence.strong_universal_T] applied to two images is a CLOSED
    statement -- it quantifies over entries and inputs and takes no
    further premise -- so a proof of it cannot be made conditional on
    [openat_arm_read_found] or any of its three siblings.  The namespace
    family above is therefore unusable by [Examples.cp_ns] and
    [Examples.headcp_ns] until the arms lane discharges the contracts,
    and until then those two theorems are proved the only way they can
    be: against the arm as it stands.

    So this file carried BOTH families at once, deliberately and for one
    release.  THIS IS THE ARMS MERGE, and here is what it did to them.

    The contracts became lemmas ([openat_arm_read_found_holds] and its
    three siblings above), so the [_ns] family is no longer vacuous.
    These four are retained with NO CALL SITE OUTSIDE THE RETIRED FAMILY,
    as [theories/Examples/PROOF_GUIDE.md] prescribes for a superseded combinator
    and as AGENTS.md's ban on deleting a proof requires.  The wording is
    exact on purpose: they DO have call sites, from [tfo_open_rd_rec]
    and its siblings here and from [tfm_open_rd_rec] and its sibling in
    [Common.FileMixSim], and those callers are themselves retired and
    thread the same dead premise upward.  Nothing live reaches any of
    them; a reader who greps for a call site finds those and should stop
    there.  Hence the phrase, everywhere it appears in this tree: no
    call site OUTSIDE THE RETIRED FAMILY, never a bare "no call site".

    RETAINING THEM TOOK ONE CHANGE TO EACH STATEMENT, and a reader
    should know why it was not optional.  "Retained unchanged" is only
    available for a lemma that is still TRUE, and two of these were not:
    [openat_wr_check]'s premise ([fs_under] false) and
    [tfo_openat_enoent]'s ([fs_lookup] None) are both satisfiable under
    [Fs.wf_fs], while their conclusions -- a create at the PATHNAME, an
    -ENOENT from a raw miss -- are what the resolving arm no longer
    does.  A pathname that misses as a key can resolve to a file that is
    there, and then the arm opens it.  So each of the six gained the
    premise that says the walk lands where the old statement assumed it
    did: the resolution names the PATHNAME ITSELF as the key.  With that
    premise each is again exactly what it always claimed, and each is
    now proved by applying its [_ns] twin at [k := p].

    That premise is what makes them unusable rather than merely unused,
    and deliberately so: under [Fs.wf_fs] a resolved key is absolute and
    a plain name is not, so no well-formed image can supply it.  The
    lemmas are kept and true, and dead in the sense above: reachable
    only from the retired nodes that thread the same premise.  That is
    the honest shape for a superseded proof

    A READER SHOULD NOT TAKE THESE AS A STATEMENT ABOUT R22.  Under
    [Fs.wf_fs] the lookup they are stated over cannot succeed for a
    plain name ([plain_name_not_a_key]), which is exactly why the
    examples' "the source is present" branch is currently unreachable
    and why the namespace family had to be written at all.

    THE SAME GOES FOR [Fs.Namei.fs_under], through a different premise.
    [openat_wr_isdir_check] and [tfo_open_wr_isdir_rec] ask for
    [fs_under (m_fs model) p = true], and no key of a well-formed image
    lives under a plain name either, since every key is absolute.  So
    that pair is vacuous for the same reason the read pair is, and the
    advice their own comments give -- that a proof reaching the create
    splits on [fs_under] -- is dead under R22: the split has one live
    branch.  Those comments also still argue from [Fs.valid_fs], which
    the core removed from [Run.valid_input]; read them as the R21
    documents they are. *)

(** The two modeled open shapes reduce the checker to
    [check_open_result] with the respective success-model builder. *)
Lemma openat_rd_check : forall segs ms x8 model p i,
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  open_shape (ms_gpr ms 2) = 0%Z ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = Some (EFile i) ->
  Fs.resolve (open_walk_mode (ms_gpr ms 2)) (m_fs model) (m_cwd model) p
    = (Fs.RFound p (Fs.EFile i), Fs.LastNorm, false) ->
  open_walk_plain (ms_gpr ms 2) model p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
        (check_open_result_copyins (open_copyins ms) eff model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFile i (Z_to_bv 64 0))) model)).
Proof.
  intros segs ms x8 model p i Hno Hdirfd Hpath Hpe Hfl Hdot Hfs Hres Hplain Hfree eff.
  exact (openat_rd_check_ns segs ms x8 model p p i
           openat_arm_read_found_holds Hno Hdirfd Hpath Hpe Hfl Hres Hplain Hfree eff).
Qed.

(** The write-create open of a plain name NOTHING LIVES UNDER: the
    branch set of a create.  The [fs_under] premise is the R21 image-side
    half of what [openat_plain_name] says about the path: under R21 a
    plain name some key lived under was an implied directory, and the
    create arm answered it -EISDIR instead ([openat_wr_isdir_check]
    below).  Under [Fs.wf_fs] every key is absolute, so no key lives
    under a plain name and the premise always holds. *)
Lemma openat_wr_check : forall segs ms x8 model p fs' i,
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  open_shape (ms_gpr ms 2) = wr_create_flags ->
  openat_plain_name p = true ->
  fs_under (m_fs model) p = false ->
  resolve_create_target model (ms_gpr ms 2) p fs' i ->
  open_walk_plain (ms_gpr ms 2) model p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
        (check_open_result_copyins (open_copyins ms) eff model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFileW i (Z_to_bv 64 0)))
                        (with_fs fs' model))).
Proof.
  intros segs ms x8 model p fs' i Hno Hdirfd Hpath Hpe Hfl Hdot Hun Hres Hplain Hfree eff.
  exact (openat_wr_check_ns segs ms x8 model p fs' i
           openat_arm_create_holds Hno Hdirfd Hpath Hpe Hfl Hres Hplain Hfree eff).
Qed.

(** The write-create open of a plain name SOME KEY LIVES UNDER: the
    checker reduces to the deterministic -EISDIR return, and the model
    is untouched.  [Open.openat_create_spec] carries the derivation
    ([do_open]'s [d_is_dir] on the positive dentry the lookup finds,
    fs/namei.c:3951-3952, Linux v6.18.46); this is the proof-side handle
    on it, the twin of [openat_wr_check] for the image the other cannot
    take. *)
Lemma openat_wr_isdir_check : forall segs ms x8 model p,
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  open_shape (ms_gpr ms 2) = wr_create_flags ->
  openat_plain_name p = true ->
  fs_under (m_fs model) p = true ->
  Fs.resolve (open_walk_mode (ms_gpr ms 2)) (m_fs model) (m_cwd model) p
    = (Fs.RFound p Fs.EDir, Fs.LastNorm, false) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
        (Prelude.check_copyins_after (open_copyins ms) eff
           (check_walk_refusals (open_walk_mode (ms_gpr ms 2)) (sys_input segs ms x8)
              (ms_gpr ms 1) (clear_copyins eff) model
              (check_ret_only (clear_copyins eff) (errno_ret EISDIR) model []))).
Proof.
  intros segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hun Hres Hfree eff.
  exact (openat_wr_isdir_check_ns segs ms x8 model p p Fs.LastNorm
           openat_arm_create_isdir_holds Hno Hdirfd Hpath Hpe Hfl Hres Hfree eff).
Qed.

(** An over-PATH_MAX path reduces the checker to the deterministic
    -ENAMETOOLONG return, under [getname_flags]' own refusals
    ([check_getname_refusals]: the allocations fail before the copy
    that fills PATH_MAX; the walk is never handed the name), with NO
    dirfd hypothesis: [openat_spec] fetches the pathname before it
    resolves the dirfd, exactly as Linux's [getname()] runs before
    [path_init]'s [fdget_raw].  The FLAG word is still required,
    because [build_open_flags()] runs BEFORE [getname()]: a combination
    the model does not interpret is declined before the pathname is
    ever looked at. *)
Lemma openat_toolong_check : forall segs ms x8 model,
  bv_unsigned x8 = 56%Z ->
  modeled_open_flags (ms_gpr ms 2) = true ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrTooLong ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
        (Prelude.check_copyins_after (open_copyins ms) eff
           (check_walk_refusals (open_walk_mode (ms_gpr ms 2)) (sys_input segs ms x8)
              (ms_gpr ms 1) (clear_copyins eff) model
              (check_ret_only (clear_copyins eff) (errno_ret ENAMETOOLONG) model []))).
Proof.
  intros segs ms x8 model Hno Hfl Hpath eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite Hfl. cbn [negb]. cbv beta iota.
  unfold openat_name_fetched, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota.
  reflexivity.
Qed.

(** What an open node's checker accepts once [getname_flags]' own
    refusals stand around it ([check_getname_refusals]): the node's own
    effects, or a bare -ENOMEM ([getname_errnos], one of
    [openat_errnos]) with a ledger of its own and the model unchanged.
    That one's machine successor is the bare return's with the pathname
    ledger, since [apply_effect] reads no copy-in. *)
Lemma check_open_result_getname_ok_inv : forall i lead pathp reads eff m mk m' evs,
  check_getname_refusals i lead pathp eff m (check_open_result_copyins reads eff m mk)
    = CheckOk m' evs ->
  (exists e, In e openat_errnos /\ eff_ret eff = errno_ret e /\ m' = m /\ evs = []
     /\ forall ms, apply_effect ms eff
                   = apply_effect ms (with_copyins reads (mkEffect (errno_ret e) [] [])))
  \/ (exists fd, fd_lookup (m_fds m) fd = None /\ fd = alloc_fd (m_fds m)
     /\ eff = with_copyins reads (mkEffect fd [] []) /\ m' = mk fd /\ evs = []).
Proof.
  intros i lead pathp reads eff m mk m' evs H.
  apply check_getname_refusals_ok_inv in H.
  destruct H as [H | (-> & -> & e & ci & He & ->)].
  - apply check_open_result_copyins_ok_iff in H.
    destruct H as [(e & HIn & -> & -> & ->) | Hfd]; [left | right; exact Hfd].
    exists e. split; [exact HIn|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. intro ms0. reflexivity.
  - left. exists e.
    assert (HIn : In e openat_errnos)
      by (cbn [getname_errnos In] in He; destruct He as [<- | []];
          apply ENOMEM_in_openat_errnos).
    split; [exact HIn|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. intro ms0. reflexivity.
Qed.

Section OpenNodes.
Variable segs : list Segment.

(** Core open node over an abstract success-model builder [mk].  Errnos
    are [Z] ([Te : Z -> _]); fds are [word]s below [2^31].  The checker
    is the node's under [getname_flags]' own refusals, whose -ENOMEM
    takes the continuation of the node's own. *)
Lemma tfo_open_core : forall ms model (mk : word -> Model) x8 reads
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  ms_svc_pending ms = Some x8 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
                   (check_open_result_copyins reads eff model mk)) ->
  (forall fd, m_halted (mk fd) = None /\ m_vm_lazy (mk fd) = []) ->
  (forall e, In e openat_errnos ->
     to_fout segs (advance_past_svc
                     (apply_effect ms
                       (with_copyins reads (mkEffect (errno_ret e) [] []))))
             model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout segs (advance_past_svc
                    (apply_effect ms (with_copyins reads (mkEffect fd [] []))))
             (mk fd) (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout segs ms model U.
Proof.
  intros ms model mk x8 reads Te Ts U Hsvc Hh Hlazy Hchk Hmk Herr Hok HU.
  apply (tfo_sys segs ms model x8
    (fun eff model' =>
       if addr_is_error_b (eff_ret eff)
       then Te ((two_pow_64 - bv_unsigned (eff_ret eff))%Z)
       else Ts (eff_ret eff)) U); [exact Hsvc | | | | |].
  - (* no Unmodeled *)
    intro Hspec.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []))
      in Hspec.
    rewrite Hchk in Hspec. apply check_getname_refusals_unmodeled in Hspec.
    exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hspec).
  - (* receptive: ENOMEM *)
    exists (with_copyins reads (mkEffect (errno_ret ENOMEM) [] [])), model, [].
    apply check_syscall_ok_iff. rewrite Hchk. apply check_getname_refusals_of_ok.
    apply check_open_result_copyins_ok_iff. left. exists ENOMEM.
    repeat split; try reflexivity. apply ENOMEM_in_openat_errnos.
  - (* shape *)
    intros eff model' evs Hspec.
    apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
    apply check_open_result_getname_ok_inv in Hspec.
    destruct Hspec as [ (e & _ & _ & -> & -> & _)
                      | (fd & _ & _ & _ & -> & ->) ].
    + repeat split; assumption.
    + destruct (Hmk fd) as [Hhalt Hlazy']. repeat split; assumption.
  - (* continuations *)
    intros eff model' evs Hspec.
    apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
    apply check_open_result_getname_ok_inv in Hspec.
    destruct Hspec as [ (e & HIn & Hret & -> & _ & Happ)
                      | (fd & Hlk & Heq & -> & -> & _) ].
    + destruct (openat_errno_range e HIn) as [He1 He2].
      cbv beta. rewrite Hret.
      rewrite (errno_ret_error_b e He1 He2).
      rewrite (errno_ret_recover e He1 He2).
      rewrite (Happ ms). apply Herr; assumption.
    + cbn [eff_ret with_copyins].
      assert (Hne : addr_is_error_b fd = false)
        by (rewrite Heq; apply alloc_fd_not_error_b).
      rewrite Hne.
      apply Hok; assumption.
  - (* outcome set *)
    intro o. rewrite HU. split.
    + intros [ (e & HIn & Ht) | (fd & Hlk & Heq & Ht) ].
      * destruct (openat_errno_range e HIn) as [He1 He2].
        exists (with_copyins reads (mkEffect (errno_ret e) [] [])), model, [].
        split.
        { apply check_syscall_ok_iff. rewrite Hchk. apply check_getname_refusals_of_ok.
          apply check_open_result_copyins_ok_iff. left. exists e. auto. }
        { cbn [eff_ret with_copyins]. rewrite (errno_ret_error_b e He1 He2).
          rewrite (errno_ret_recover e He1 He2). exact Ht. }
      * exists (with_copyins reads (mkEffect fd [] [])), (mk fd), [].
        split.
        { apply check_syscall_ok_iff. rewrite Hchk. apply check_getname_refusals_of_ok.
          apply check_open_result_copyins_ok_iff. right. exists fd. auto. }
        { cbn [eff_ret with_copyins].
          assert (Hne : addr_is_error_b fd = false)
            by (rewrite Heq; apply alloc_fd_not_error_b).
          rewrite Hne. exact Ht. }
    + intros (eff & model' & evs & Hspec & Ht).
      apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
      apply check_open_result_getname_ok_inv in Hspec.
      destruct Hspec as [ (e & HIn & Hret & -> & _ & _)
                        | (fd & Hlk & Heq & -> & -> & _) ].
      * destruct (openat_errno_range e HIn) as [He1 He2].
        cbv beta in Ht. rewrite Hret in Ht.
        rewrite (errno_ret_error_b e He1 He2) in Ht.
        rewrite (errno_ret_recover e He1 He2) in Ht.
        left. exists e. auto.
      * cbn [eff_ret with_copyins] in Ht.
        assert (Hne : addr_is_error_b fd = false)
          by (rewrite Heq; apply alloc_fd_not_error_b).
        rewrite Hne in Ht.
        right. exists fd. auto.
Qed.

(** A concrete successful open resolution (used by the escape path). *)
Lemma open_ok_fd : forall ms model (mk : word -> Model) x8 reads fd,
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
                   (check_open_result_copyins reads eff model mk)) ->
  fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (with_copyins reads (mkEffect fd [] [])) (mk fd) []).
Proof.
  intros ms model mk x8 reads fd Hchk Hlk Hlt.
  apply check_syscall_ok_iff. rewrite Hchk. apply check_getname_refusals_of_ok.
  apply check_open_result_copyins_ok_iff. right. exists fd. auto.
Qed.

(** An open whose own answer is the one errno [E], under the walk's
    refusals and [getname_flags]' own: [E], or one of [es], each with
    the model unchanged and one continuation apiece.  [es] holds every
    refusal the walk [md] hands that call ([walk_reached]) and
    [getname_flags]' -ENOMEM ([getname_errnos]), whose ledger is its
    own; [apply_effect] reads no copy-in, so its continuation is the
    one the bare return with the pathname ledger takes. *)
Lemma tfo_open_ret_or_refusals : forall md ms model x8 es E U,
  ms_svc_pending ms = Some x8 ->
  (forall es', walk_reached md (sys_input segs ms x8) model (ms_gpr ms 1) = Some es' ->
     incl es' es) ->
  incl getname_errnos es ->
  (forall eff,
     check_syscall (sys_input segs ms x8) eff model
     = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
         (Prelude.check_copyins_after (open_copyins ms) eff
            (check_walk_refusals md (sys_input segs ms x8) (ms_gpr ms 1)
               (clear_copyins eff) model
               (check_ret_only (clear_copyins eff) (errno_ret E) model [])))) ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (advance_past_svc
                  (apply_effect ms
                    (with_copyins (open_copyins ms)
                      (mkEffect (errno_ret E) [] []))))
          model U ->
  (forall e, In e es ->
     to_fout segs (advance_past_svc
                     (apply_effect ms
                       (with_copyins (open_copyins ms)
                         (mkEffect (errno_ret e) [] []))))
             model U) ->
  to_fout segs ms model U.
Proof.
  intros md ms model x8 es E U Hsvc Hes Hgn Hchk Hh Hlazy Hcont Hwalk.
  apply (tfo_sys_same_model segs ms model x8
           (with_copyins (open_copyins ms) (mkEffect (errno_ret E) [] [])) U);
    [exact Hsvc | | | exact Hh | exact Hlazy |].
  - apply check_syscall_ok_iff. rewrite Hchk. apply check_getname_refusals_of_ok.
    apply walk_refusals_ret_only_ok_iff. auto.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs. apply check_getname_refusals_unmodeled in Hs.
    exact (walk_refusals_ret_only_no_unmodeled _ _ _ _ _ _ _ Hs).
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_getname_refusals_ok_inv in Hs.
    destruct Hs as [Hs | (-> & -> & e & ci & He & ->)].
    + apply walk_refusals_ret_only_ok_iff in Hs.
      destruct Hs as (-> & -> & [-> | (es' & e & Hw & Hin & ->)]).
      * auto.
      * split; [reflexivity|]. split; [reflexivity|].
        exact (Hwalk e (Hes es' Hw e Hin)).
    + split; [reflexivity|]. split; [reflexivity|].
      change (apply_effect ms (mkEffectU (errno_ret e) [] [] [] [] ci))
        with (apply_effect ms (with_copyins (open_copyins ms)
                                (mkEffect (errno_ret e) [] []))).
      exact (Hwalk e (Hgn e He)).
Qed.

(** An over-PATH_MAX pathname: -ENAMETOOLONG, whatever the dirfd is, for
    any flag word the model interprets, or [getname_flags]' -ENOMEM
    beside it ([Fs.Namei.getname_errnos], the second continuation).  The
    model says what Linux says. *)
Lemma tfo_openat_toolong : forall ms model x8 U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 56%Z ->
  modeled_open_flags (ms_gpr ms 2) = true ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrTooLong ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (advance_past_svc
                  (apply_effect ms
                    (with_copyins (open_copyins ms)
                      (mkEffect (errno_ret ENAMETOOLONG) [] []))))
          model U ->
  (forall e, In e getname_errnos ->
     to_fout segs (advance_past_svc
                     (apply_effect ms
                       (with_copyins (open_copyins ms)
                         (mkEffect (errno_ret e) [] []))))
             model U) ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 U Hsvc Hno Hfl Hpath Hh Hlazy Hcont Hnomem.
  apply (tfo_open_ret_or_refusals (open_walk_mode (ms_gpr ms 2)) ms model x8
           getname_errnos ENAMETOOLONG U Hsvc);
    [ intros es' Hw; unfold walk_reached in Hw; rewrite in_mem_si, Hpath in Hw;
      discriminate Hw
    | apply incl_refl
    | exact (openat_toolong_check segs ms x8 model Hno Hfl Hpath)
    | exact Hh | exact Hlazy | exact Hcont | exact Hnomem ].
Qed.

(** An open whose own answer is the one errno [E], under the refusals
    of the walk [md] and [getname_flags]' own: [E], or on the pathname
    the walk was handed one of that walk's refusals, each with the model
    unchanged and one continuation apiece.  [getname_flags]' -ENOMEM is
    among the walk's ([walk_errnos_enomem]), so it takes the same
    continuation. *)
Lemma tfo_open_ret_or_walk : forall md ms model x8 p E U,
  ms_svc_pending ms = Some x8 ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  (forall eff,
     check_syscall (sys_input segs ms x8) eff model
     = check_getname_refusals (sys_input segs ms x8) [] (ms_gpr ms 1) eff model
         (Prelude.check_copyins_after (open_copyins ms) eff
            (check_walk_refusals md (sys_input segs ms x8) (ms_gpr ms 1)
               (clear_copyins eff) model
               (check_ret_only (clear_copyins eff) (errno_ret E) model [])))) ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (advance_past_svc
                  (apply_effect ms
                    (with_copyins (open_copyins ms)
                      (mkEffect (errno_ret E) [] []))))
          model U ->
  (forall e, In e (walk_errnos (Fs.path_last_kind p)
                     (Fs.resolve_res md (m_fs model) (m_cwd model) p)) ->
     to_fout segs (advance_past_svc
                     (apply_effect ms
                       (with_copyins (open_copyins ms)
                         (mkEffect (errno_ret e) [] []))))
             model U) ->
  to_fout segs ms model U.
Proof.
  intros md ms model x8 p E U Hsvc Hpath Hpe Hchk Hh Hlazy Hcont Hwalk.
  apply (tfo_open_ret_or_refusals md ms model x8
           (walk_errnos (Fs.path_last_kind p)
              (Fs.resolve_res md (m_fs model) (m_cwd model) p)) E U Hsvc);
    [ intros es' Hw; rewrite (walk_reached_si md segs ms x8 model p Hpath Hpe) in Hw;
      injection Hw as <-; apply incl_refl
    | intros e He; cbn [getname_errnos In] in He; destruct He as [<- | []];
      apply walk_errnos_enomem
    | exact Hchk | exact Hh | exact Hlazy | exact Hcont | exact Hwalk ].
Qed.

(** O_RDONLY open whose LAST COMPONENT IS ABSENT under a directory
    that resolved: -ENOENT, or one of the walk's own refusals (the
    second continuation).  [Fs.RMissing] is what the
    old absent lookup becomes, and it says strictly more: every prefix
    was a directory.  A pathname whose PREFIX is absent is
    [Fs.RAbsent], a different row of #1011 section 5 that also answers
    -ENOENT but through a different premise, and this node does not
    cover it. *)
Lemma tfo_openat_enoent_ns : forall ms model x8 p par nm U,
  openat_arm_read_missing ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  open_shape (ms_gpr ms 2) = 0%Z ->
  Fs.resolve (open_walk_mode (ms_gpr ms 2)) (m_fs model) (m_cwd model) p
    = (Fs.RMissing par nm, Fs.LastNorm, false) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (advance_past_svc
                  (apply_effect ms
                    (with_copyins (open_copyins ms)
                      (mkEffect (errno_ret ENOENT) [] []))))
          model U ->
  (forall e, In e (open_walk_errnos (ms_gpr ms 2) model p) ->
     to_fout segs (advance_past_svc
                     (apply_effect ms
                       (with_copyins (open_copyins ms)
                         (mkEffect (errno_ret e) [] []))))
             model U) ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 p par nm U Harm Hsvc Hno Hdirfd Hpath Hpe Hfl Hres Hfree
    Hh Hlazy Hcont Hwalk.
  exact (tfo_open_ret_or_walk _ ms model x8 p ENOENT U Hsvc Hpath Hpe
           (openat_rd_enoent_check_ns segs ms x8 model p par nm Harm Hno
              Hdirfd Hpath Hpe Hfl Hres Hfree)
           Hh Hlazy Hcont Hwalk).
Qed.

(** THE EMPTY PATHNAME, which needs no arm contract: the -ENOENT is
    decided ahead of the dispatcher, with [getname_flags]' -ENOMEM
    beside it ([Fs.Namei.getname_errnos], the second continuation).
    This used to be a branch INSIDE the lemma above; it is its own node
    now because the two answers stop sharing a premise once the other
    one is about resolution. *)
Lemma tfo_openat_empty_enoent : forall ms model x8 p U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 56%Z ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = true ->
  modeled_open_flags (ms_gpr ms 2) = true ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (advance_past_svc
                  (apply_effect ms
                    (with_copyins (open_copyins ms)
                      (mkEffect (errno_ret ENOENT) [] []))))
          model U ->
  (forall e, In e getname_errnos ->
     to_fout segs (advance_past_svc
                     (apply_effect ms
                       (with_copyins (open_copyins ms)
                         (mkEffect (errno_ret e) [] []))))
             model U) ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 p U Hsvc Hno Hpath Hpe Hfl Hh Hlazy Hcont Hnomem.
  apply (tfo_open_ret_or_refusals (open_walk_mode (ms_gpr ms 2)) ms model x8
           getname_errnos ENOENT U Hsvc);
    [ intros es' Hw; unfold walk_reached in Hw; rewrite in_mem_si, Hpath, Hpe in Hw;
      discriminate Hw
    | apply incl_refl
    | exact (openat_empty_enoent_check segs ms x8 model p Hno Hfl Hpath Hpe)
    | exact Hh | exact Hlazy | exact Hcont | exact Hnomem ].
Qed.

(** O_RDONLY open of an absent file: -ENOENT, or on a non-empty
    pathname one of the walk's own refusals, and on the empty one
    [__getname]'s -ENOMEM. *)
Lemma tfo_openat_enoent : forall ms model x8 p par nm U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  open_shape (ms_gpr ms 2) = 0%Z ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = None ->
  (path_eqb p [] = false ->
     Fs.resolve (open_walk_mode (ms_gpr ms 2)) (m_fs model) (m_cwd model) p
       = (Fs.RMissing par nm, Fs.LastNorm, false)) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (advance_past_svc
                  (apply_effect ms
                    (with_copyins (open_copyins ms)
                      (mkEffect (errno_ret ENOENT) [] []))))
          model U ->
  (path_eqb p [] = false ->
   forall e, In e (open_walk_errnos (ms_gpr ms 2) model p) ->
     to_fout segs (advance_past_svc
                     (apply_effect ms
                       (with_copyins (open_copyins ms)
                         (mkEffect (errno_ret e) [] []))))
             model U) ->
  (path_eqb p [] = true ->
   forall e, In e getname_errnos ->
     to_fout segs (advance_past_svc
                     (apply_effect ms
                       (with_copyins (open_copyins ms)
                         (mkEffect (errno_ret e) [] []))))
             model U) ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 p par nm U Hsvc Hno Hdirfd Hpath Hfl Hdot Hfs Hres Hfree
    Hh Hlazy Hcont Hwalk Hnomem.
  destruct (path_eqb p []) eqn:Hpe.
  - exact (tfo_openat_empty_enoent ms model x8 p U Hsvc Hno Hpath Hpe
             (modeled_open_flags_rd _ Hfl) Hh Hlazy Hcont (Hnomem eq_refl)).
  - exact (tfo_openat_enoent_ns ms model x8 p par nm U
             openat_arm_read_missing_holds Hsvc Hno Hdirfd Hpath Hpe Hfl
             (Hres eq_refl) Hfree Hh Hlazy Hcont (Hwalk eq_refl)).
Qed.

(* ----- file read (63) ----- *)

Lemma tfo_read_file : forall ms model x8 p off data w U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFile p off) ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  Fs.fs_ino_data (m_fs model) p = data ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some w ->
  (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
  (0 < bv_unsigned (ms_gpr ms 2))%Z ->
  (* the range passes [access_ok]: [vfs_read] tests it before the file
     is consulted *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs
    (advance_past_svc (apply_effect ms
       (mkEffect (len_word (file_read data off (ms_gpr ms 2)))
                 (delivered_writes (ms_gpr ms 1)
                    (file_read data off (ms_gpr ms 2))) [])))
    (with_fds
       (fd_insert (m_fds model) (ms_gpr ms 0)
          (FdFile p (off + len_word (file_read data off (ms_gpr ms 2)))))
       model)
    U ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 p off data w U Hsvc Hno Hfd Hfd32 Hfs Hw Hcnt Hpos Haok Hh Hlazy Hcont.
  set (bs := file_read data off (ms_gpr ms 2)).
  assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
                <= bv_unsigned (ms_gpr ms 2))%Z).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (ms_gpr ms 2)) as Hc.
    rewrite length_file_read, Nat2Z.inj_min.
    unfold word_to_nat.
    rewrite Z.mod_small; lia. }
  assert (Hchk : forall eff m' evs,
    check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
    (eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []
     /\ m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
               (FdFile p (off + len_word bs))) model
     /\ evs = [])).
  { intros eff m' evs.
    rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite Haok. cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta.
    rewrite in_wmem_si.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
    unfold bs.
    destruct (file_read data off (ms_gpr ms 2)) as [|b bsr].
    - (* zero-byte read (at or past end-of-file) *)
      cbv beta iota.
      rewrite check_ret_only_ok_iff. cbn [delivered_writes length].
      tauto.
    - destruct eff as [ret ws zs us cs copyins]. split.
      + intro H.
        destruct ws as [|[a bs'] [|? ?]]; try discriminate.
        destruct zs as [|? ?]; [|discriminate].
        destruct us as [|? ?]; [|discriminate].
        destruct cs as [|? ?]; [|discriminate].
        destruct copyins as [|? ?]; [|discriminate].
        destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr)
                  && bv_eqb ret (len_word (b :: bsr)))
          eqn:Hb; try rewrite Hb in H; [|discriminate].
        apply andb_true_iff in Hb as [Hb Hr].
        apply andb_true_iff in Hb as [Ha Hbs].
        apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
        inversion H; subst. cbn [delivered_writes].
        repeat split; congruence.
      + intros (Heff & -> & ->). cbn [delivered_writes] in Heff.
        inversion Heff; subst.
        rewrite bv_eqb_refl.
        rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
        rewrite bv_eqb_refl. cbn [andb]. reflexivity. }
  apply (tfo_sys_det segs ms model x8
           (mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) [])
           (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
              (FdFile p (off + len_word bs))) model) U);
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. apply Hchk. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. apply Hchk in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite (check_syscall_63 segs ms x8 _ model Hno) in Hs.
    unfold check_read in Hs.
    rewrite Hfd32, Hfd in Hs. cbv beta iota in Hs.
    rewrite Haok in Hs. cbn [negb] in Hs. cbv beta iota in Hs.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned in Hs.
    rewrite Hfs in Hs. cbv beta iota zeta in Hs.
    rewrite in_wmem_si in Hs.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs.
    cbv beta iota in Hs.
    revert Hs.
    destruct (file_read data off (ms_gpr ms 2)) as [|b0 bsr]; intro Hs.
    + exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
    + discriminate.
Qed.

(* ----- file write (64) ----- *)

Lemma tfo_write_file : forall ms model x8 p off data bs U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFileW p off) ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs ->
  (* THE RANGE [vfs_write]'s [access_ok] ACCEPTS, a premise this lemma did
     not used to carry.  The [FdFileW] arm now asks [access_ok] on the
     named count before it reads the source, so the statement was true of
     an arm that judged the write by a walk that could wrap at 2^64 and is
     false of one that does not, exactly where the buffer leaves the user
     address space: there the answer is -EFAULT and the file is not
     written.  A repair of a statement that had become false, not a
     weakening *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
  Fs.fs_ino_data (m_fs model) p = data ->
  (* the guard itself, not the inequality that implies it: a zero-length
     write opens no hole and is judged at ANY offset ([modeled_file_gap]),
     and this premise says exactly that much and no more *)
  negb (modeled_file_gap data off bs) = false ->
  (* a positive count really reads the buffer, so the copy-in ledger is the
     singleton range the readable prefix came from.  A zero-length write
     reads no user byte and carries an empty ledger instead; that is
     [tfo_write_file_zero] *)
  w_is0 (ms_gpr ms 2) = false ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs
    (advance_past_svc (apply_effect ms
      (with_copyins [(ms_gpr ms 1, length bs)]
        (mkEffect (ms_gpr ms 2) [] []))))
    (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                 (FdFileW p (off + ms_gpr ms 2)))
       (with_fs (Fs.fs_set_ino_data (m_fs model) p (file_write data off bs)) model))
    U ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hok Hcnt Hfs Hgap Hnz Hh Hlazy Hcont.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
  { rewrite in_mem_si. exact Hrd. }
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only_copyins [(ms_gpr ms 1, length bs)] eff (ms_gpr ms 2)
        (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                     (FdFileW p (off + ms_gpr ms 2)))
           (with_fs (Fs.fs_set_ino_data (m_fs model) p (file_write data off bs)) model)) []).
  { intro eff.
    rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
    rewrite Hok. cbn [negb]. cbv beta iota.
    rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
    pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
    assert (Hret : len_word bs = ms_gpr ms 2).
    { unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
    assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
    { destruct (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) eqn:Hg'; [|reflexivity].
      exfalso. apply andb_prop in Hg' as [Hnz' Hz].
      apply Nat.eqb_eq in Hz. apply negb_true_iff in Hnz'.
      rewrite Hz in Hlen. cbn in Hlen.
      assert (Hzero : ms_gpr ms 2 = Z_to_bv 64 0).
      { rewrite <- (Z_to_bv_bv_unsigned 64 (ms_gpr ms 2)). rewrite <- Hlen. reflexivity. }
      unfold w_is0 in Hnz'. rewrite Hzero, bv_eqb_refl in Hnz'. discriminate. }
    rewrite Hgate. cbv beta iota.
    rewrite Hfs. cbv beta iota.
    rewrite Hgap. cbv beta iota.
    rewrite Hret.
    rewrite Hnz. reflexivity. }
  apply (tfo_sys_det segs ms model x8
           (with_copyins [(ms_gpr ms 1, length bs)]
             (mkEffect (ms_gpr ms 2) [] []))
           (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                        (FdFileW p (off + ms_gpr ms 2)))
              (with_fs (Fs.fs_set_ino_data (m_fs model) p (file_write data off bs)) model)));
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

(** The [count = 0] half of [tfo_write_file]: no user byte is read, so the
    effect carries no copy-in range at all (the checker rejects a singleton
    zero-length one), and [access_ok]'s range verdict is the whole of what
    the write does; see [Uaccess.access_ok_zero]. *)
Lemma tfo_write_file_zero : forall ms model x8 p off data bs U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFileW p off) ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs ->
  (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
  Fs.fs_ino_data (m_fs model) p = data ->
  (* the guard itself, not the inequality that implies it: a zero-length
     write opens no hole and is judged at ANY offset ([modeled_file_gap]) *)
  negb (modeled_file_gap data off bs) = false ->
  w_is0 (ms_gpr ms 2) = true ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs
    (advance_past_svc (apply_effect ms (mkEffect (ms_gpr ms 2) [] [])))
    (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                 (FdFileW p (off + ms_gpr ms 2)))
       (with_fs (Fs.fs_set_ino_data (m_fs model) p (file_write data off bs)) model))
    U ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hcnt Hfs Hgap Hz Hok Hh Hlazy Hcont.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
  { rewrite in_mem_si. exact Hrd. }
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only eff (ms_gpr ms 2)
        (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                     (FdFileW p (off + ms_gpr ms 2)))
           (with_fs (Fs.fs_set_ino_data (m_fs model) p (file_write data off bs)) model)) []).
  { intro eff.
    rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
    rewrite Hok. cbn [negb]. cbv beta iota.
    rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
    pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
    assert (Hret : len_word bs = ms_gpr ms 2).
    { unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
    assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
    { rewrite Hz. reflexivity. }
    rewrite Hgate. cbv beta iota.
    rewrite Hfs. cbv beta iota.
    rewrite Hgap. cbv beta iota.
    rewrite Hret.
    rewrite Hz. cbv beta iota.
    unfold check_access_ok_zero. rewrite Hok. reflexivity. }
  apply (tfo_sys_det segs ms model x8
           (mkEffect (ms_gpr ms 2) [] [])
           (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                        (FdFileW p (off + ms_gpr ms 2)))
              (with_fs (Fs.fs_set_ino_data (m_fs model) p (file_write data off bs)) model)));
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.

(* ----- close (57) ----- *)

Lemma tfo_close : forall ms model x8 e U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 57%Z ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some e ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs
    (advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 0) [] [])))
    (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model)
    U ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 e U Hsvc Hno Hfd Hfd32 Hh Hlazy Hcont.
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only eff (Z_to_bv 64 0)
        (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) []).
  { intro eff.
    rewrite (check_syscall_57 segs ms x8 eff model Hno). unfold check_close.
    rewrite Hfd32, Hfd. reflexivity. }
  apply (tfo_sys_det segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
           (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model));
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.

(* ========================================================================= *)
(* Ergonomic "at the raw ecall record" wrappers around the [tfo_*] core       *)
(* nodes above: unpack a record's [ms_regs]/[ms_svc_pending] fields once      *)
(* via [record_gpr], so per-binary proofs don't reprove the [ms_gpr]          *)
(* projections at every fd/read/write/open/close/exit call site.  The        *)
(* records carry the ecall post-state shape [step_ecall] leaves:             *)
(* [ms_svc_pending := Some (getr regs 17)], [ms_resv := None]; register      *)
(* hypotheses are [reg_get regs 10/11/12] (a0/a1/a2), and the syscall        *)
(* number is Z-characterized ([bv_unsigned (getr regs 17) = ...%Z]).         *)
(* ========================================================================= *)

Lemma record_gpr : forall regs fr pc sv rv fc mem rom k,
  ms_gpr {| ms_regs := regs; ms_fregs := fr; ms_pc_val := pc; ms_svc_pending := sv;
            ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := rom |} k
  = reg_get regs (Z_to_bv 5 (10 + Z.of_nat k)).
Proof. reflexivity. Qed.

(** Exit leaf. *)
Lemma tfo_exit_rec : forall regs pc mem rom model code fsv,
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = code -> (bv_unsigned code < 256)%Z ->
  m_fs model = fsv ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
          model (fun o => o = (code, fsv)).
Proof.
  intros regs pc mem rom model code fsv H17 H10 Hc Hfs.
  subst fsv.
  eapply (tfo_exit segs _ model (getr regs 17)).
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
  - intro o. rewrite record_gpr, arg_reg_0.
    rewrite H10, (land_255_small code Hc). tauto.
Qed.

(** File read of [cnt] bytes: deterministic, fills the buffer, advances
    the offset. *)
Lemma tfo_read_rec : forall regs pc mem rom model fdv p off data buf cnt U,
  bv_unsigned (getr regs 17) = 63%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdFile p off) ->
  fd32 fdv = fdv ->
  Fs.fs_ino_data (m_fs model) p = data ->
  wseg_ok segs buf (word_to_nat cnt) = true ->
  (bv_unsigned cnt <= rw_bytes_max)%Z ->
  (0 < bv_unsigned cnt)%Z ->
  (* the range passes [access_ok]: passed straight through to
     [tfo_read_file] *)
  access_okb buf (bv_unsigned cnt) = true ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs
    (mkst (regupd regs 10 (len_word (file_read data off cnt))) (v_addi pc 4)
          (write_to_mem mem buf (file_read data off cnt)) rom)
    (with_fds (fd_insert (m_fds model) fdv
        (FdFile p (off + len_word (file_read data off cnt)))) model)
    U ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} model U.
Proof.
  intros regs pc mem rom model fdv p off data buf cnt U
    H17 H10 H11 H12 Hfd Hfd32 Hfs Hwseg Hcnt Hpos Haok Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  destruct (wseg_ok_wdef segs buf cnt ms Hwseg) as [w Hw].
  apply (tfo_read_file ms model (getr regs 17) p off data w U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - rewrite Hg0. exact Hfd.
  - rewrite Hg0. exact Hfd32.
  - exact Hfs.
  - rewrite Hg1, Hg2. exact Hw.
  - rewrite Hg2. exact Hcnt.
  - rewrite Hg2. exact Hpos.
  - rewrite Hg1, Hg2. exact Haok.
  - exact Hh.
  - exact Hlazy.
  - rewrite Hg0, Hg1, Hg2. unfold ms.
    rewrite adv_apply_delivered. exact Hcont.
Qed.

(** File write: deterministic full write of the readable buffer bytes. *)
Lemma tfo_write_rec : forall regs pc mem model fdv p off data bs buf cnt U,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdFileW p off) ->
  fd32 fdv = fdv ->
  rdn segs mem buf (word_to_nat cnt) = Some bs ->
  (bv_unsigned cnt <= rw_bytes_max)%Z ->
  Fs.fs_ino_data (m_fs model) p = data ->
  (* the guard itself, not the inequality that implies it: a zero-length
     write opens no hole and is judged at ANY offset ([modeled_file_gap]),
     and this premise says exactly that much and no more *)
  negb (modeled_file_gap data off bs) = false ->
  (* the range [vfs_write]'s [access_ok] accepts, on EVERY count.  This
     premise used to be [access_okb buf (bv_unsigned cnt) = true \/
     (0 < bv_unsigned cnt)%Z], on the argument that a positive-count write
     needs no range premise because the mapping settles the copy.  That
     argument held of a walk that could wrap at 2^64 and does not hold of
     the [FdFileW] arm, which asks [access_ok] on the named count before
     it reads a byte; see [tfo_write_file]. *)
  access_okb buf (bv_unsigned cnt) = true ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 cnt) (v_addi pc 4) mem (seg_rom segs))
    (with_fds (fd_insert (m_fds model) fdv (FdFileW p (off + cnt)))
       (with_fs (Fs.fs_set_ino_data (m_fs model) p (file_write data off bs)) model)) U ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model fdv p off data bs buf cnt U
    H17 H10 H11 H12 Hfd Hfd32 Hrd Hcnt Hfs Hgap Hok Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  destruct (w_is0 cnt) eqn:Hz.
  - (* count = 0: no user byte is read, so the effect carries no copy-in
       range and [access_ok]'s verdict is all that is checked *)
    apply (tfo_write_file_zero ms model (getr regs 17) p off data bs U).
    + unfold ms. cbn [ms_svc_pending]. reflexivity.
    + exact H17.
    + rewrite Hg0. exact Hfd.
    + rewrite Hg0. exact Hfd32.
    + rewrite Hg1, Hg2.
      rewrite read_bytes_map_read_byte.
      rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
      exact Hrd.
    + rewrite Hg2. exact Hcnt.
    + exact Hfs.
    + exact Hgap.
    + rewrite Hg2. exact Hz.
    + rewrite Hg1, Hg2. exact Hok.
    + exact Hh.
    + exact Hlazy.
    + rewrite Hg0, Hg2. unfold ms.
      rewrite adv_eff_ret. exact Hcont.
  - (* positive count: the delivered bytes are the copy-in ledger *)
    apply (tfo_write_file ms model (getr regs 17) p off data bs U).
    + unfold ms. cbn [ms_svc_pending]. reflexivity.
    + exact H17.
    + rewrite Hg0. exact Hfd.
    + rewrite Hg0. exact Hfd32.
    + rewrite Hg1, Hg2.
      rewrite read_bytes_map_read_byte.
      rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
      exact Hrd.
    + rewrite Hg1, Hg2. exact Hok.
    + rewrite Hg2. exact Hcnt.
    + exact Hfs.
    + exact Hgap.
    + rewrite Hg2. exact Hz.
    + exact Hh.
    + exact Hlazy.
    + rewrite Hg0, Hg2. unfold ms.
      rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

(** close: deterministic, removes the fd. *)
Lemma tfo_close_rec : forall regs pc mem rom model fdv e U,
  bv_unsigned (getr regs 17) = 57%Z ->
  reg_get regs 10 = fdv ->
  fd_lookup (m_fds model) fdv = Some e ->
  fd32 fdv = fdv ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
    (with_fds (fd_remove (m_fds model) fdv) model) U ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} model U.
Proof.
  intros regs pc mem rom model fdv e U H17 H10 Hfd Hfd32 Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  apply (tfo_close ms model (getr regs 17) e U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - rewrite Hg0. exact Hfd.
  - rewrite Hg0. exact Hfd32.
  - exact Hh.
  - exact Hlazy.
  - rewrite Hg0. unfold ms. rewrite adv_eff_ret. exact Hcont.
Qed.

(** O_RDONLY openat of an absent file, on a table with a free
    descriptor: -ENOENT, or one of the walk's own refusals. *)
Lemma tfo_open_enoent_ns_rec : forall regs pc mem model p par nm U,
  openat_arm_read_missing ->
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  Fs.resolve (Fs.WalkFull true false) (m_fs model) (m_cwd model) p
    = (Fs.RMissing par nm, Fs.LastNorm, false) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4)
                     mem (seg_rom segs))
          model U ->
  (forall e, In e (open_walk_errnos (Z_to_bv 64 0) model p) ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model U) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p par nm U Harm H17 H10 H12 Hpath Hpe Hres Hfree
    Hh Hlazy Hcont Hwalk.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg2 : ms_gpr ms 2 = Z_to_bv 64 0)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  apply (tfo_openat_enoent_ns ms model (getr regs 17) p par nm U).
  - exact Harm.
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
  - unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
  - exact Hpe.
  - rewrite Hg2. vm_compute. reflexivity.
  - rewrite Hg2, open_walk_mode_rd. exact Hres.
  - exact Hfree.
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
  - intros e He. rewrite Hg2 in He.
    unfold ms. rewrite adv_eff_ret_copyins. exact (Hwalk e He).
Qed.

(** The empty pathname from the raw ecall record: no arm contract, and
    [__getname]'s -ENOMEM beside the -ENOENT. *)
Lemma tfo_open_empty_enoent_rec : forall regs pc mem model p U,
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 12 = Z_to_bv 64 0 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = true ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4)
                     mem (seg_rom segs))
          model U ->
  (forall e, In e getname_errnos ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model U) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p U H17 H12 Hpath Hpe Hh Hlazy Hcont Hnomem.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfo_openat_empty_enoent ms model (getr regs 17) p U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
  - exact Hpe.
  - unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
    apply modeled_open_flags_rd. vm_compute. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
  - intros e He. unfold ms. rewrite adv_eff_ret_copyins. exact (Hnomem e He).
Qed.

(** The read-open success node, ON THE INODE THE RESOLVED KEY NAMES:
    the descriptor carries [i], which is what makes two spellings of one
    file share a descriptor's file and a stat pin (#1011 section 2).
    The walk's refusals must be among the fresh-descriptor errnos
    ([open_walk_plain]): a walk that followed a link admits -ELOOP too,
    and this node's outcome set would not name it. *)
Lemma tfo_open_rd_ns_rec : forall regs pc mem model p k i
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  openat_arm_read_found ->
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  Fs.resolve (Fs.WalkFull true false) (m_fs model) (m_cwd model) p
    = (Fs.RFound k (Fs.EFile i), Fs.LastNorm, false) ->
  open_walk_plain (Z_to_bv 64 0) model p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall e, In e openat_errnos ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
             (with_fds (fd_insert (m_fds model) fd
                          (FdFile i (Z_to_bv 64 0))) model) (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p k i Te Ts U
    Harm H17 H10 H12 Hpath Hpe Hres Hplain Hfree Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg2 : ms_gpr ms 2 = Z_to_bv 64 0)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  apply (tfo_open_core ms model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFile i (Z_to_bv 64 0))) model)
           (getr regs 17) (open_copyins ms) Te Ts U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - intro eff. apply (openat_rd_check_ns segs ms (getr regs 17) model p k i).
    + exact Harm.
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    + exact Hpe.
    + rewrite Hg2. vm_compute. reflexivity.
    + rewrite Hg2, open_walk_mode_rd. exact Hres.
    + rewrite Hg2. exact Hplain.
    + exact Hfree.
  - intro fd. split; [rewrite with_fds_halted; exact Hh | exact Hlazy].
  - intros e HIn.
    unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
  - intros fd Hlk Hlt.
    unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
  - exact HU.
Qed.

(** THE DIRECTORY READ-OPEN NODE, which the namespace family did not
    have and the Example re-proof needs twice: once for an operand that
    is a directory, and once for the "." the walk now settles onto the
    working directory.  The descriptor names the RESOLVED KEY, so a
    caller who opened "." holds a descriptor on [m_cwd model] and not on
    a key computed from the spelling. *)
Lemma tfo_open_rd_dir_ns_rec : forall regs pc mem model p k lk
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  openat_arm_read_dir ->
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  Fs.resolve (Fs.WalkFull true false) (m_fs model) (m_cwd model) p
    = (Fs.RFound k Fs.EDir, lk, false) ->
  open_walk_plain (Z_to_bv 64 0) model p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall e, In e openat_errnos ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
             (with_fds (fd_insert (m_fds model) fd (FdDir k)) model) (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p k lk Te Ts U
    Harm H17 H10 H12 Hpath Hpe Hres Hplain Hfree Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg2 : ms_gpr ms 2 = Z_to_bv 64 0)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  apply (tfo_open_core ms model
           (fun fd => with_fds (fd_insert (m_fds model) fd (FdDir k)) model)
           (getr regs 17) (open_copyins ms) Te Ts U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - intro eff. apply (openat_rd_dir_check_ns segs ms (getr regs 17) model p k lk).
    + exact Harm.
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    + exact Hpe.
    + rewrite Hg2. vm_compute. reflexivity.
    + rewrite Hg2, open_walk_mode_rd. exact Hres.
    + rewrite Hg2. exact Hplain.
    + exact Hfree.
  - intro fd. split; [rewrite with_fds_halted; exact Hh | exact Hlazy].
  - intros e HIn.
    unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
  - intros fd Hlk Hlt.
    unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
  - exact HU.
Qed.

(** The create node.  The file is made where the walk settled -- a new
    inode at the missing name -- and the descriptor carries that inode.
    See [resolve_create_target], which says why an existing destination
    is not this node's. *)
Lemma tfo_open_wr_ns_rec : forall regs pc mem model p fs' i
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  openat_arm_create ->
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 577 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  resolve_create_target model (Z_to_bv 64 577) p fs' i ->
  open_walk_plain (Z_to_bv 64 577) model p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall e, In e openat_errnos ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
             (with_fds (fd_insert (m_fds model) fd
                          (FdFileW i (Z_to_bv 64 0)))
                (with_fs fs' model)) (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p fs' i Te Ts U
    Harm H17 H10 H12 Hpath Hpe Hres Hplain Hfree Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg2 : ms_gpr ms 2 = Z_to_bv 64 577)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  apply (tfo_open_core ms model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFileW i (Z_to_bv 64 0)))
                        (with_fs fs' model))
           (getr regs 17) (open_copyins ms) Te Ts U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - intro eff. apply (openat_wr_check_ns segs ms (getr regs 17) model p fs' i).
    + exact Harm.
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    + exact Hpe.
    + rewrite Hg2. vm_compute. reflexivity.
    + rewrite Hg2. exact Hres.
    + rewrite Hg2. exact Hplain.
    + exact Hfree.
  - intro fd. split.
    + rewrite with_fds_halted, with_fs_halted. exact Hh.
    + exact Hlazy.
  - intros e HIn.
    unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
  - intros fd Hlk Hlt.
    unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
  - exact HU.
Qed.

(** The -EISDIR node, beside the walk's own refusals (the second
    continuation), on a table with a free descriptor.  The premise is
    now the ENTRY KIND, not the [fs_under] inference the old arm had to
    make, so an EMPTY directory answers here too. *)
Lemma tfo_open_wr_isdir_ns_rec : forall regs pc mem model p k lk U,
  openat_arm_create_isdir ->
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 577 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  Fs.resolve (Fs.WalkCreate true) (m_fs model) (m_cwd model) p
    = (Fs.RFound k Fs.EDir, lk, false) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4)
                     mem (seg_rom segs))
          model U ->
  (forall e, In e (open_walk_errnos (Z_to_bv 64 577) model p) ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model U) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p k lk U Harm H17 H10 H12 Hpath Hpe Hres Hfree Hh Hlazy
    Hcont Hwalk.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg2 : ms_gpr ms 2 = Z_to_bv 64 577)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  assert (Hpath' : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p).
  { unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath. }
  apply (tfo_open_ret_or_walk (open_walk_mode (ms_gpr ms 2)) ms model
           (getr regs 17) p EISDIR U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hpath'.
  - exact Hpe.
  - intro eff. apply (openat_wr_isdir_check_ns segs ms (getr regs 17) model p k lk).
    + exact Harm.
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + exact Hpath'.
    + exact Hpe.
    + rewrite Hg2. vm_compute. reflexivity.
    + rewrite Hg2, open_walk_mode_wr. exact Hres.
    + exact Hfree.
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
  - intros e He. rewrite Hg2 in He.
    unfold ms. rewrite adv_eff_ret_copyins. exact (Hwalk e He).
Qed.

Lemma tfo_open_enoent_rec : forall regs pc mem model p par nm U,
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = None ->
  (path_eqb p [] = false ->
     Fs.resolve (Fs.WalkFull true false) (m_fs model) (m_cwd model) p
       = (Fs.RMissing par nm, Fs.LastNorm, false)) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4)
                     mem (seg_rom segs))
          model U ->
  (path_eqb p [] = false ->
   forall e, In e (open_walk_errnos (Z_to_bv 64 0) model p) ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model U) ->
  (path_eqb p [] = true ->
   forall e, In e getname_errnos ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model U) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p par nm U H17 H10 H12 Hpath Hdot Hfs Hres Hfree
    Hh Hlazy Hcont Hwalk Hnomem.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg2 : ms_gpr ms 2 = Z_to_bv 64 0)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  apply (tfo_openat_enoent ms model (getr regs 17) p par nm U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
  - unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
  - rewrite Hg2. vm_compute. reflexivity.
  - exact Hdot.
  - exact Hfs.
  - rewrite Hg2, open_walk_mode_rd. exact Hres.
  - exact Hfree.
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
  - intros Hpe e He. rewrite Hg2 in He.
    unfold ms. rewrite adv_eff_ret_copyins. exact (Hwalk Hpe e He).
  - intros Hpe e He.
    unfold ms. rewrite adv_eff_ret_copyins. exact (Hnomem Hpe e He).
Qed.

(** O_RDONLY openat of a present file: errno branch or the lowest free
    fd. *)
Lemma tfo_open_rd_rec : forall regs pc mem model p i
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = Some (EFile i) ->
  Fs.resolve (Fs.WalkFull true false) (m_fs model) (m_cwd model) p
    = (Fs.RFound p (Fs.EFile i), Fs.LastNorm, false) ->
  open_walk_plain (Z_to_bv 64 0) model p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall e, In e openat_errnos ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
             (with_fds (fd_insert (m_fds model) fd
                          (FdFile i (Z_to_bv 64 0))) model) (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p i Te Ts U
    H17 H10 H12 Hpath Hpe Hdot Hfs Hres Hplain Hfree Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg2 : ms_gpr ms 2 = Z_to_bv 64 0)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  apply (tfo_open_core ms model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFile i (Z_to_bv 64 0))) model)
           (getr regs 17) (open_copyins ms) Te Ts U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - intro eff. apply (openat_rd_check segs ms (getr regs 17) model p i).
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    + exact Hpe.
    + rewrite Hg2. vm_compute. reflexivity.
    + exact Hdot.
    + exact Hfs.
    + rewrite Hg2, open_walk_mode_rd. exact Hres.
    + rewrite Hg2. exact Hplain.
    + exact Hfree.
  - intro fd. split; [rewrite with_fds_halted; exact Hh | exact Hlazy].
  - intros e HIn.
    unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
  - intros fd Hlk Hlt.
    unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
  - exact HU.
Qed.

(** O_WRONLY|O_CREAT|O_TRUNC openat of a plain name nothing lives
    under: errno branch or create-empty at the lowest free fd.

    READ THIS AS THE R21 DOCUMENT IT IS.  The [fs_under] premise was
    what selected this node over [tfo_open_wr_isdir_rec], and the
    advice that went with it -- that a proof reaching a create on an
    argv-derived name splits on that premise -- argued from
    [Fs.valid_fs], which the R22 core removed from [Run.valid_input].
    Under [Fs.wf_fs] no key of a well-formed image lives under a plain
    name, so the split has one live branch and this node is retired:
    see "the pre-namespace open family" above for the premise it gained
    and why. *)
Lemma tfo_open_wr_rec : forall regs pc mem model p fs' i
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 577 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  openat_plain_name p = true ->
  fs_under (m_fs model) p = false ->
  resolve_create_target model (Z_to_bv 64 577) p fs' i ->
  open_walk_plain (Z_to_bv 64 577) model p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall e, In e openat_errnos ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
             (with_fds (fd_insert (m_fds model) fd (FdFileW i (Z_to_bv 64 0)))
                (with_fs fs' model)) (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p fs' i Te Ts U
    H17 H10 H12 Hpath Hpe Hdot Hun Hres Hplain Hfree Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg2 : ms_gpr ms 2 = Z_to_bv 64 577)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  apply (tfo_open_core ms model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFileW i (Z_to_bv 64 0)))
                        (with_fs fs' model))
           (getr regs 17) (open_copyins ms) Te Ts U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - intro eff. apply (openat_wr_check segs ms (getr regs 17) model p fs' i).
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    + exact Hpe.
    + rewrite Hg2. vm_compute. reflexivity.
    + exact Hdot.
    + exact Hun.
    + rewrite Hg2. exact Hres.
    + rewrite Hg2. exact Hplain.
    + exact Hfree.
  - intro fd. split.
    + rewrite with_fds_halted, with_fs_halted. exact Hh.
    + exact Hlazy.
  - intros e HIn.
    unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
  - intros fd Hlk Hlt.
    unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
  - exact HU.
Qed.

(** O_WRONLY|O_CREAT|O_TRUNC openat of a plain name SOME KEY LIVES
    UNDER: the -EISDIR continuation, or one of the walk's own refusals,
    model untouched.

    READ THIS AS THE R21 DOCUMENT IT IS, like its twin above.  The two
    nodes covered between them every image [Fs.valid_fs] admitted for a
    plain name, and [Fs.valid_fs] is gone: under [Fs.wf_fs] this node's
    [fs_under] premise cannot be satisfied at all, since every key is
    absolute.  Retired with the rest of the family. *)
Lemma tfo_open_wr_isdir_rec : forall regs pc mem model p U,
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 577 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  openat_plain_name p = true ->
  fs_under (m_fs model) p = true ->
  Fs.resolve (Fs.WalkCreate true) (m_fs model) (m_cwd model) p
    = (Fs.RFound p Fs.EDir, Fs.LastNorm, false) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4)
                     mem (seg_rom segs))
          model U ->
  (forall e, In e (open_walk_errnos (Z_to_bv 64 577) model p) ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model U) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p U H17 H10 H12 Hpath Hpe Hdot Hun Hres Hfree
    Hh Hlazy Hcont Hwalk.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg2 : ms_gpr ms 2 = Z_to_bv 64 577)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  assert (Hpath' : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p).
  { unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath. }
  apply (tfo_open_ret_or_walk (open_walk_mode (ms_gpr ms 2)) ms model
           (getr regs 17) p EISDIR U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hpath'.
  - exact Hpe.
  - intro eff. apply (openat_wr_isdir_check segs ms (getr regs 17) model p).
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + exact Hpath'.
    + exact Hpe.
    + rewrite Hg2. vm_compute. reflexivity.
    + exact Hdot.
    + exact Hun.
    + rewrite Hg2, open_walk_mode_wr. exact Hres.
    + exact Hfree.
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
  - intros e He. rewrite Hg2 in He.
    unfold ms. rewrite adv_eff_ret_copyins. exact (Hwalk e He).
Qed.

(** openat on a path with no NUL within PATH_MAX: -ENAMETOOLONG in a0,
    or [__getname]'s -ENOMEM beside it, independent of the dirfd, for
    any open mode the model interprets ([modeled_open_flags] — the
    kernel validates the flags before it fetches the pathname).  The
    record-shaped counterpart of [tfo_openat_toolong], for the
    symbolic-execution scripts. *)

Lemma tfo_open_toolong_rec : forall regs pc mem model U,
  bv_unsigned (getr regs 17) = 56%Z ->
  modeled_open_flags (reg_get regs 12) = true ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrTooLong ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4)
                     mem (seg_rom segs))
          model U ->
  (forall e, In e getname_errnos ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model U) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model U H17 Hfl Hpath Hh Hlazy Hcont Hnomem.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfo_openat_toolong ms model (getr regs 17) U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms. rewrite record_gpr, arg_reg_2. exact Hfl.
  - unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
  - intros e He. unfold ms. rewrite adv_eff_ret_copyins. exact (Hnomem e He).
Qed.

End OpenNodes.

(* ========================================================================= *)
(* Run-level packaging and the equivalence glue                              *)
(* ========================================================================= *)

(** The run-level omni judgment of a file-copying run. *)
Lemma fout_omni_run : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_fout (run_segments segs inp sp mb)
          (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
          (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
             (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) U ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (fout_post U).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto.
  cbn [omni_run]. unfold init_config.
  exact (to_fout_exec (run_segments segs inp sp mb) _ _ U Hto eq_refl eq_refl).
Qed.

Lemma fout_obs_iff : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_fout (run_segments segs inp sp mb)
          (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
          (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
             (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) U ->
  forall tr, obs_trace (run_segments segs inp sp mb)
               (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
    <-> exists o, U o /\ is_prefix tr (fout_trace o).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto tr.
  unfold init_config.
  set (ms := init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) in *.
  set (m0 := with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
               (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) in *.
  assert (Hh : m_halted m0 = None) by reflexivity.
  assert (Hlazy : m_vm_lazy m0 = []) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (to_fout_star_only (run_segments segs inp sp mb) ms _ U Hto Hh Hlazy tr' c Hstar)
      as (o & Ho & Hp').
    exists o. split; [exact Ho | eapply is_prefix_trans; eauto].
  - intros (o & Ho & Hp).
    destruct (to_fout_star_admits (run_segments segs inp sp mb) ms _ U Hto Hh Hlazy o Ho)
      as [c Hstar].
    exists (fout_trace o), c. split; assumption.
Qed.

Lemma fout_no_error_run : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_fout (run_segments segs inp sp mb)
          (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
          (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
             (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) U ->
  ~ reaches_error (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto. apply exec_no_error.
  eapply exec_conseq; [exact (fout_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(** The omni equivalence for two file-copying binaries with the SAME
    outcome set [U], at the two role budgets. *)
Lemma fout_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp,
  to_fout (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
          source_alloc_limit inp)) U ->
  to_fout (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
          target_alloc_limit inp)) U ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
    Hsource Htarget.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (fout_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource) |].
    intros tr o (out & _ & _ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).
    rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (fout_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget).
Qed.

(** The [Equivalence]-level equivalence for two file-copying binaries with
    the SAME outcome set [U]. *)
Lemma fout_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp,
  to_fout (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
          rlim inp)) U ->
  to_fout (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
          alim inp)) U ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp
    Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (fout_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).
    rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).
    reflexivity.
  - cbn. apply (fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget).
Qed.

(** SOURCE-ERROR ESCAPE at the Equivalence level.  The premise is
    deliberately universal: a chosen [star]/[reaches_error] witness is
    insufficient when another source resolution avoids error. *)
Lemma spec_err_escape_equiv :
  forall segs pc ph sp brk0 mb rnd lim inp (target : behavior),
  all_traces_error (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) ->
  Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) target.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp target Hall.
  left. exact Hall.
Qed.
End WithFP1.
