(** * Common.FileSimWalk — the open of an operand the walk resolves, and
    the reads and writes on the descriptors it hands back.

    TRUST BOUNDARY: shared proof library, not the trusted specification.
    Image-INDEPENDENT.

    [FileSim]'s open nodes each take one resolution of the pathname and,
    for a descriptor, a walk that counted fewer than 21 links and handed
    no name over [Fs.name_max] to a lookup ([FileSim.open_walk_plain]).
    A program that opens a name it was handed meets every resolution: a
    symbolic link at the name (-ELOOP beside the answer once the walk
    has counted 21 links, [Namei.walk_errnos]), a name over
    [Fs.name_max] (-ENAMETOOLONG beside it), a folder, /dev/null and
    /dev/urandom.  This file gives:

    - [open_arm]: what the O_RDONLY open and the O_WRONLY|O_CREAT|O_TRUNC
      open of a walked pathname answer, one errno or one descriptor entry
      with the image a create leaves, read off [Fs.resolve]
      ([check_openat_resolved_arm] is the checker's own arm);
    - [tfo_open_signed_rec]: that open as a program that tests only the
      SIGN of the return sees it.  Every errno the call admits (the arm's
      own, [Open.openat_errnos] beside a descriptor, the walk's refusals)
      takes one continuation, the one descriptor the other;
    - the deterministic reads of a folder (-EISDIR), /dev/null (0) and
      /dev/urandom (the declared stream), and the deterministic writes of
      /dev/null and /dev/urandom (the whole count). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Common Require Import SimInv ExitSim PropExec CatSim CatExec ErrEscape SeqExec StreamExec StreamSim FileSim.
From LinuxProcessSemantics.Common Require StepTac.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.

Import ListNotations.
Open Scope bv_scope.

Section WithFP.
Context {fx : FPState}.

(* ========================================================================= *)
(* Small facts                                                               *)
(* ========================================================================= *)

Lemma eff_ret_mk : forall r, eff_ret (mkEffect r [] []) = r.
Proof. reflexivity. Qed.

Lemma eff_ret_copyins_mk : forall reads r,
  eff_ret (with_copyins reads (mkEffect r [] [])) = r.
Proof. reflexivity. Qed.

Lemma delivered_writes_ne : forall (buf : word) (bs : list byte),
  bs <> [] -> delivered_writes buf bs = [(buf, bs)].
Proof. intros buf [|b bs] H; [exfalso; exact (H eq_refl) | reflexivity]. Qed.

Lemma open_shape_rd0 : open_shape (Z_to_bv 64 0) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma open_shape_wr577 : open_shape (Z_to_bv 64 577) = wr_create_flags.
Proof. vm_compute. reflexivity. Qed.

Lemma wr_create_flags_ne0 : Z.eqb wr_create_flags 0 = false.
Proof. vm_compute. reflexivity. Qed.

(** Every refusal of the walk is an errno in range: the five
    [Namei.walk_errnos] can name are -ENOMEM, -EACCES, -ELOOP, -ENOENT
    and -ENAMETOOLONG. *)
Lemma walk_errnos_range : forall lk w e,
  In e (walk_errnos lk w) -> (1 <= e <= 4095)%Z.
Proof.
  intros lk w e H. unfold walk_errnos in H.
  rewrite !in_app_iff in H.
  destruct H as [H | [H | [H | H]]];
    [ destruct lk
    | match type of H with context [if ?b then _ else _] => destruct b end
    | destruct (Fs.wr_res w)
    | match type of H with context [if ?b then _ else _] => destruct b end ];
    cbn [In] in H;
    repeat match goal with
           | H : _ \/ _ |- _ => destruct H as [H|H]
           | H : False |- _ => contradiction
           | H : _ = e |- _ => subst e
           end;
    cbv [ENOMEM EACCES ELOOP ENOENT ENAMETOOLONG]; lia.
Qed.

(* ========================================================================= *)
(* What the open of a walked pathname answers                                *)
(* ========================================================================= *)

(** [rd] is the O_RDONLY open (flag word 0, walk [Fs.WalkFull true
    false]); [rd = false] is the O_WRONLY|O_CREAT|O_TRUNC open (flag word
    577, walk [Fs.WalkCreate true]).  [open_arm] mirrors
    [Open.openat_read_spec] and [Open.openat_create_spec] row for row:
    [inl (fe, ofs)] is a descriptor entry [fe] and, for a create that
    writes the image, the image it leaves; [inr e] is the arm's one
    errno.  The rows the model declines are [open_answered]'s; [open_arm]
    gives them a placeholder no lemma below uses. *)
Definition open_walk (rd : bool) : Fs.WalkMode :=
  if rd then Fs.WalkFull true false else Fs.WalkCreate true.

Definition open_flag_word (rd : bool) : word :=
  if rd then Z_to_bv 64 0 else Z_to_bv 64 577.

Definition open_arm (rd : bool) (fs : Fs.Fs) (cwd p : Fs.path)
    : (FdEntry * option Fs.Fs) + Z :=
  match fst (fst (Fs.resolve (open_walk rd) fs cwd p)) with
  | Fs.RFound k e =>
      match e with
      | Fs.EDir => if rd then inl (FdDir k, None) else inr EISDIR
      | Fs.EFile i =>
          if rd then inl (FdFile i (Z_to_bv 64 0), None)
          else inl (FdFileW i (Z_to_bv 64 0), Some (Fs.fs_set_ino_data fs i []))
      | Fs.EDev Fs.DevNull => inl (FdDevNull rd (negb rd), None)
      | Fs.EDev Fs.DevUrandom => inl (FdUrandom rd (negb rd), None)
      | Fs.ELink _ => inr ELOOP
      end
  | Fs.RMissing par nm =>
      if rd then inr ENOENT
      else inl (FdFileW (create_file_ino fs) (Z_to_bv 64 0),
                Some (create_file_fs fs (Fs.child_key par nm)))
  | Fs.RNotDir _ => inr ENOTDIR
  | Fs.RAbsent _ => inr ENOENT
  | Fs.RLoop => inr ELOOP
  | Fs.RParent _ _ => inr EISDIR
  | Fs.ROutside => inr ENOENT
  end.

(** The walk ends the model answers: not outside it, and not the
    O_CREAT end on a read.  A device entry is answered at any key. *)
Definition open_answered (rd : bool) (fs : Fs.Fs) (cwd p : Fs.path) : Prop :=
  match fst (fst (Fs.resolve (open_walk rd) fs cwd p)) with
  | Fs.ROutside => False
  | Fs.RParent _ _ => rd = false
  | _ => True
  end.

Definition open_ok (rd : bool) (fs : Fs.Fs) (cwd p : Fs.path) : bool :=
  match open_arm rd fs cwd p with inl _ => true | inr _ => false end.

(** The model a descriptor open leaves: a device descriptor's number
    drops its old stat pin first, as [Open.open_devnull] and
    [Open.open_urandom] do ([State.with_fd_unpinned]). *)
Definition open_model (m : Model) (fd : word) (fe : FdEntry) (ofs : option Fs.Fs)
    : Model :=
  with_fds (fd_insert (m_fds m) fd fe)
    (match ofs with
     | Some fs' => with_fs fs' m
     | None => match entry_dev_kind fe with
               | Some _ => with_fd_unpinned fd m
               | None => m
               end
     end).

(** Does [open_arm]'s descriptor entry stand beside a -ETXTBSY, and for
    which inode?  Exactly the write-create open of a regular file the
    walk found ([Open.open_write_existing], which then asks whether a
    descriptor writes that inode): a created file and every read-only
    open do not. *)
Definition open_arm_txtbsy (rd : bool) (fs : Fs.Fs) (cwd p : Fs.path) : option Fs.ino :=
  match fst (fst (Fs.resolve (open_walk rd) fs cwd p)) with
  | Fs.RFound _ (Fs.EFile i) => if rd then None else Some i
  | _ => None
  end.

Definition open_arm_check (rd : bool) (m : Model) (p : Fs.path) (eff : SyscallEffect)
    : check_result :=
  match open_arm rd (m_fs m) (m_cwd m) p with
  | inl (fe, ofs) =>
      match open_arm_txtbsy rd (m_fs m) (m_cwd m) p with
      | Some i =>
          check_open_write_existing i eff m
            (check_open_result eff m (fun fd => open_model m fd fe ofs))
      | None => check_open_result eff m (fun fd => open_model m fd fe ofs)
      end
  | inr e => check_ret_only eff (errno_ret e) m []
  end.

Lemma open_arm_errno_range : forall rd fs cwd p e,
  open_arm rd fs cwd p = inr e -> (1 <= e <= 4095)%Z.
Proof.
  intros rd fs cwd p e H. unfold open_arm in H.
  destruct (fst (fst (Fs.resolve (open_walk rd) fs cwd p)))
    as [k en|par nm|k|pre| | |dd nm];
    [ destruct en as [i| |dk|b]; [ | | destruct dk | ] | | | | | | ];
    destruct rd; cbv beta iota in H; try discriminate H; injection H as <-;
    cbv [ENOENT ENOTDIR ELOOP EISDIR]; lia.
Qed.

(** What an O_RDONLY open hands out: a regular file at offset 0, a
    folder, or one of the two devices opened for reading; it never writes
    the image. *)
Lemma open_arm_rd_cases : forall fs cwd p fe ofs,
  open_arm true fs cwd p = inl (fe, ofs) ->
  ofs = None /\
  ((exists i, fe = FdFile i (Z_to_bv 64 0)) \/ (exists k, fe = FdDir k)
   \/ fe = FdDevNull true false \/ fe = FdUrandom true false).
Proof.
  intros fs cwd p fe ofs H. unfold open_arm in H.
  destruct (fst (fst (Fs.resolve (open_walk true) fs cwd p)))
    as [k en|par nm|k|pre| | |dd nm];
    [ destruct en as [i| |dk|b]; [ | | destruct dk | ] | | | | | | ];
    cbv beta iota in H; try discriminate H; injection H as <- <-;
    (split; [reflexivity|]).
  - left. exists i. reflexivity.
  - right. left. exists k. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. reflexivity.
Qed.

(** What an O_WRONLY|O_CREAT|O_TRUNC open hands out: a regular file at
    offset 0, empty in the image the open leaves (truncated, or created
    empty), or one of the two devices opened for writing, the image
    untouched. *)
Lemma open_arm_wr_cases : forall fs cwd p fe ofs,
  open_arm false fs cwd p = inl (fe, ofs) ->
  (exists j, fe = FdFileW j (Z_to_bv 64 0)
             /\ Fs.fs_ino_data (match ofs with Some f => f | None => fs end) j = [])
  \/ (fe = FdDevNull false true /\ ofs = None)
  \/ (fe = FdUrandom false true /\ ofs = None).
Proof.
  intros fs cwd p fe ofs H. unfold open_arm in H.
  destruct (fst (fst (Fs.resolve (open_walk false) fs cwd p)))
    as [k en|par nm|k|pre| | |dd nm];
    [ destruct en as [i| |dk|b]; [ | | destruct dk | ] | | | | | | ];
    cbv beta iota in H; try discriminate H; injection H as <- <-.
  - left. exists i. split; [reflexivity|]. cbv beta iota.
    apply Fs.fs_ino_data_set_eq.
  - right. left. split; reflexivity.
  - right. right. split; reflexivity.
  - left. exists (create_file_ino fs). split; [reflexivity|]. cbv beta iota.
    unfold create_file_fs, create_file_ino. apply fs_ino_data_create_file.
Qed.

(** The hypothesis a program's statement names for an operand (the walk
    end is not outside the model) is [open_answered]: the O_RDONLY walk
    never ends at the O_CREAT end ([FileSim.read_walk_not_parent]). *)
Lemma open_answered_of_inside : forall (rd : bool) fs cwd p,
  match fst (fst (Fs.resolve (open_walk rd) fs cwd p)) with
  | Fs.ROutside => False
  | _ => True
  end ->
  open_answered rd fs cwd p.
Proof.
  intros rd fs cwd p H. unfold open_answered.
  destruct rd; cbn [open_walk] in H |- *.
  - pose proof (read_walk_not_parent fs cwd p) as Hnp.
    destruct (fst (fst (Fs.resolve (Fs.WalkFull true false) fs cwd p)))
      as [k en|par nm|k|pre| | |dd nm] eqn:Hr;
      try exact H; try exact I.
    exfalso. first [exact (Hnp _ _ Hr) | exact (Hnp _ _ eq_refl)].
  - destruct (fst (fst (Fs.resolve (Fs.WalkCreate true) fs cwd p)))
      as [k en|par nm|k|pre| | |dd nm];
      first [exact H | exact I | reflexivity].
Qed.

Lemma open_model_fds : forall m fd fe ofs,
  m_fds (open_model m fd fe ofs) = fd_insert (m_fds m) fd fe.
Proof. intros m fd fe [f|]; unfold open_model; [|destruct (entry_dev_kind fe)]; reflexivity. Qed.

Lemma open_model_fs : forall m fd fe ofs,
  m_fs (open_model m fd fe ofs) = match ofs with Some f => f | None => m_fs m end.
Proof. intros m fd fe [f|]; unfold open_model; [|destruct (entry_dev_kind fe)]; reflexivity. Qed.

Lemma open_model_cwd : forall m fd fe ofs,
  m_cwd (open_model m fd fe ofs) = m_cwd m.
Proof. intros m fd fe [f|]; unfold open_model; [|destruct (entry_dev_kind fe)]; reflexivity. Qed.

Lemma open_model_urandom : forall m fd fe ofs,
  m_urandom (open_model m fd fe ofs) = m_urandom m.
Proof. intros m fd fe [f|]; unfold open_model; [|destruct (entry_dev_kind fe)]; reflexivity. Qed.

Lemma open_model_halted : forall m fd fe ofs,
  m_halted (open_model m fd fe ofs) = m_halted m.
Proof. intros m fd fe [f|]; unfold open_model; [|destruct (entry_dev_kind fe)]; reflexivity. Qed.

Lemma open_model_lazy : forall m fd fe ofs,
  m_vm_lazy (open_model m fd fe ofs) = m_vm_lazy m.
Proof. intros m fd fe [f|]; unfold open_model; [|destruct (entry_dev_kind fe)]; reflexivity. Qed.

(** A pathname that reaches the walk: not empty, and its NUL within
    PATH_MAX ([Open.openat_body_spec] answers the other two before any
    lookup). *)
Definition op_walked (p : Fs.path) : bool :=
  negb (path_eqb p []) && Nat.ltb (length p) path_max.

Lemma op_walked_true : forall p,
  op_walked p = true -> p <> [] /\ (length p < path_max)%nat.
Proof.
  intros p H. unfold op_walked in H. apply andb_true_iff in H as [H1 H2].
  split.
  - intro He. rewrite He in H1. vm_compute in H1. discriminate H1.
  - apply Nat.ltb_lt. exact H2.
Qed.

(** THE CHECKER'S ARM IS [open_arm]: for a pathname that is not
    "/proc/self/fd/N" and a walk end the model answers, the resolved
    open's checker is the fresh-descriptor acceptor over [open_arm]'s
    entry, or the bare return of its errno. *)
Lemma check_openat_resolved_arm : forall rd p eff m,
  proc_self_fd p = None ->
  open_answered rd (m_fs m) (m_cwd m) p ->
  Open.check_openat_resolved p (open_flag_word rd) eff m = open_arm_check rd m p eff.
Proof.
  intros rd p eff m Hpsf Hans.
  unfold Open.check_openat_resolved. rewrite Hpsf.
  unfold open_arm_check, open_arm_txtbsy, open_arm, open_answered, open_model in *.
  destruct rd; cbn [open_flag_word open_walk] in *.
  - rewrite open_walk_mode_rd. revert Hans.
    destruct (Fs.resolve (Fs.WalkFull true false) (m_fs m) (m_cwd m) p)
      as [[r lk] ts].
    intros Hans. cbn [fst] in Hans |- *. cbv beta iota zeta.
    rewrite open_shape_rd0, Z.eqb_refl. cbv beta iota.
    unfold Open.check_openat_read.
    destruct r as [k e|par nm|k|pre| | |dd nm]; cbv beta iota in Hans |- *;
      try reflexivity; try contradiction; try discriminate Hans.
    destruct e as [i| |dk|b]; cbv beta iota in Hans |- *; try reflexivity.
    all: destruct dk; cbv beta iota in Hans |- *;
      [ unfold Open.check_open_devnull | unfold Open.check_open_urandom ]; reflexivity.
  - rewrite open_walk_mode_wr. revert Hans.
    destruct (Fs.resolve (Fs.WalkCreate true) (m_fs m) (m_cwd m) p)
      as [[r lk] ts].
    intros Hans. cbn [fst] in Hans |- *. cbv beta iota zeta.
    rewrite open_shape_wr577, wr_create_flags_ne0. cbv beta iota.
    rewrite Z.eqb_refl. cbv beta iota.
    unfold Open.check_openat_create.
    destruct r as [k e|par nm|k|pre| | |dd nm]; cbv beta iota in Hans |- *;
      try reflexivity; try contradiction.
    destruct e as [i| |dk|b]; cbv beta iota in Hans |- *; try reflexivity.
    all: destruct dk; cbv beta iota in Hans |- *;
      [ unfold Open.check_open_devnull | unfold Open.check_open_urandom ]; reflexivity.
Qed.

Lemma check_random_write_no_unmodeled : forall n l led eff m,
  check_random_write n l led eff m <> CheckUnmodeled.
Proof.
  intros n l led [ret ws zs us cs ci] m H.
  rewrite check_random_write_eq in H.
  destruct (Z.eqb n 0).
  - exact (check_ret_only_no_unmodeled _ _ _ _ H).
  - destruct ws; [|discriminate H]. destruct zs; [|discriminate H].
    destruct us; [|discriminate H]. destruct cs; [|discriminate H].
    cbv beta iota in H.
    repeat match type of H with context [if ?b then _ else _] => destruct b end;
      discriminate H.
Qed.

(* ========================================================================= *)
(* A call a program reads only the sign of                                   *)
(* ========================================================================= *)

Section Signed.
Variable segs : list Segment.

(** A CALL THAT ANSWERS AN ERRNO OR ONE DESCRIPTOR, AS A PROGRAM THAT TESTS
    ONLY THE SIGN OF THE RETURN SEES IT.  [c] is the call's acceptor once
    the copy-in ledger [reads] is set aside; every effect it accepts is a
    bare return, either error-encoded with the model unchanged or, when
    [ok], the lowest free descriptor with the model [mk] builds.  Around
    the ledger stand [getname_flags]' own refusals on [pathp]
    ([check_getname_refusals]), a bare errno with a ledger of its own,
    whose machine successor is the bare return's: [apply_effect] reads no
    copy-in.  Every error-encoded return takes the continuation [Uf]; the
    descriptor takes [Us]. *)
Lemma tfo_sys_signed : forall ms model x8 pathp reads (c : SyscallEffect -> check_result)
    (mk : word -> Model) (ok : bool) (Uf Us U : (word * Fs.Fs) -> Prop),
  ms_svc_pending ms = Some x8 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_getname_refusals (sys_input segs ms x8) [] pathp eff model
                   (Prelude.check_copyins_after reads eff (c (clear_copyins eff)))) ->
  (forall eff, c eff <> CheckUnmodeled) ->
  (exists r0, addr_is_error_b r0 = true /\ c (mkEffect r0 [] []) = CheckOk model []) ->
  (forall eff m' evs, c eff = CheckOk m' evs ->
     evs = [] /\
     ((addr_is_error_b (eff_ret eff) = true /\ m' = model
       /\ eff = mkEffect (eff_ret eff) [] [])
      \/ (ok = true /\ eff = mkEffect (alloc_fd (m_fds model)) [] []
          /\ m' = mk (alloc_fd (m_fds model))))) ->
  (ok = true -> c (mkEffect (alloc_fd (m_fds model)) [] [])
                = CheckOk (mk (alloc_fd (m_fds model))) []) ->
  m_halted (mk (alloc_fd (m_fds model))) = None ->
  m_vm_lazy (mk (alloc_fd (m_fds model))) = [] ->
  (forall r, addr_is_error_b r = true ->
     to_fout segs (advance_past_svc (apply_effect ms (with_copyins reads (mkEffect r [] []))))
       model Uf) ->
  (ok = true ->
     to_fout segs (advance_past_svc (apply_effect ms
                     (with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] []))))
       (mk (alloc_fd (m_fds model))) Us) ->
  (forall o, U o <-> Uf o \/ (ok = true /\ Us o)) ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 pathp reads c mk ok Uf Us U Hsvc Hh Hlazy Hchk Hnu Hex Hshape Hokc
    Hmkh Hmkl Herr Hok HU.
  assert (Hinv : forall eff m' evs,
    syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
    evs = [] /\
    ((addr_is_error_b (eff_ret eff) = true /\ m' = model
      /\ apply_effect ms eff
         = apply_effect ms (with_copyins reads (mkEffect (eff_ret eff) [] [])))
     \/ (ok = true
         /\ eff = with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] [])
         /\ m' = mk (alloc_fd (m_fds model))))).
  { intros eff m' evs Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_getname_refusals_ok_inv in Hs.
    destruct Hs as [Hs | (-> & -> & e & ci & He & ->)].
    - apply Prelude.check_copyins_after_ok_iff in Hs as [Hreads Hc].
      destruct (Hshape _ _ _ Hc) as [Hev [(He & Hm & Heq) | (Hokt & Heq & Hm)]].
      + split; [exact Hev|]. left. split; [exact He|]. split; [exact Hm|].
        f_equal. apply effect_from_copyins_and_clear; [exact Hreads | exact Heq].
      + split; [exact Hev|]. right. split; [exact Hokt|]. split; [|exact Hm].
        apply effect_from_copyins_and_clear; [exact Hreads | exact Heq].
    - split; [reflexivity|]. left.
      assert (HeR : (1 <= e <= 4095)%Z)
        by (cbn [getname_errnos In] in He; destruct He as [<- | []]; cbv [ENOMEM]; lia).
      destruct HeR as [He1 He2].
      split; [exact (errno_ret_error_b e He1 He2)|]. split; reflexivity. }
  assert (Hokw : forall r m1, c (mkEffect r [] []) = CheckOk m1 [] ->
    syscall_spec (sys_input segs ms x8) model
      (Ok (with_copyins reads (mkEffect r [] [])) m1 [])).
  { intros r m1 Hc. apply check_syscall_ok_iff. rewrite Hchk.
    apply check_getname_refusals_of_ok.
    apply Prelude.check_copyins_after_ok_iff. split; [reflexivity | exact Hc]. }
  apply (tfo_sys segs ms model x8
           (fun eff _ => if addr_is_error_b (eff_ret eff) then Uf else Us) U).
  - exact Hsvc.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    apply check_getname_refusals_unmodeled in Hs.
    apply Prelude.check_copyins_after_unmodeled in Hs.
    exact (Hnu _ Hs).
  - destruct Hex as (r0 & _ & Hr0).
    exists (with_copyins reads (mkEffect r0 [] [])), model, [].
    exact (Hokw r0 model Hr0).
  - intros eff m' evs Hs.
    destruct (Hinv _ _ _ Hs) as [Hev [(_ & Hm & _) | (_ & _ & Hm)]];
      subst m' evs.
    + split; [reflexivity|]. split; assumption.
    + split; [reflexivity|]. split; assumption.
  - intros eff m' evs Hs. cbv beta.
    destruct (Hinv _ _ _ Hs) as [_ [(He & Hm & Heq) | (Hokt & Heq & Hm)]];
      subst m'.
    + rewrite He. rewrite Heq. apply Herr. exact He.
    + rewrite Heq, eff_ret_copyins_mk, alloc_fd_not_error_b. exact (Hok Hokt).
  - intro o. rewrite HU. split.
    + intros [Hf | (Hokt & Hs)].
      * destruct Hex as (r0 & Hr0e & Hr0).
        exists (with_copyins reads (mkEffect r0 [] [])), model, [].
        split; [exact (Hokw r0 model Hr0)|]. cbv beta.
        rewrite eff_ret_copyins_mk, Hr0e. exact Hf.
      * exists (with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] [])),
          (mk (alloc_fd (m_fds model))), [].
        split; [exact (Hokw _ _ (Hokc Hokt))|]. cbv beta.
        rewrite eff_ret_copyins_mk, alloc_fd_not_error_b. exact Hs.
    + intros (eff & m' & evs & Hs & HT). cbv beta in HT.
      destruct (Hinv _ _ _ Hs) as [_ [(He & _ & _) | (Hokt & Heq & _)]].
      * left. rewrite He in HT. exact HT.
      * right. split; [exact Hokt|].
        rewrite Heq, eff_ret_copyins_mk, alloc_fd_not_error_b in HT. exact HT.
Qed.

(** THE OPEN OF A WALKED OPERAND, AS A SIGN-TESTING PROGRAM SEES IT.  The
    pathname reaches the walk (fetched, not empty, [AT_FDCWD]), is not
    "/proc/self/fd/N", and its walk ends where the model answers
    ([open_answered]).  Then every outcome is an error-encoded return
    with the model unchanged -- [open_arm]'s own errno, one of
    [Open.openat_errnos] beside a descriptor, or one of the walk's
    refusals ([Namei.walk_errnos]: -ELOOP after a walk of 21 links or
    more, -ENAMETOOLONG after a long name) -- or, when [open_arm] gives an
    entry, the lowest free descriptor on it. *)
Lemma tfo_open_signed_rec : forall regs pc mem model p (rd : bool)
    (Uf Us U : (word * Fs.Fs) -> Prop),
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD ->
  reg_get regs 12 = open_flag_word rd ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  proc_self_fd p = None ->
  open_answered rd (m_fs model) (m_cwd model) p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall r, addr_is_error_b r = true ->
     to_fout segs (mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs)) model Uf) ->
  (forall fe ofs, open_arm rd (m_fs model) (m_cwd model) p = inl (fe, ofs) ->
     to_fout segs (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem
                        (seg_rom segs))
       (open_model model (alloc_fd (m_fds model)) fe ofs) Us) ->
  (forall o, U o <-> Uf o \/ (open_ok rd (m_fs model) (m_cwd model) p = true /\ Us o)) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p rd Uf Us U H17 H10 H12 Hpath Hpe Hpsf Hans Hfree
    Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg0 : ms_gpr ms 0 = AT_FDCWD)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg2 : ms_gpr ms 2 = open_flag_word rd)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  assert (Hpath' : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p).
  { unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath. }
  assert (Hfl : modeled_open_flags (ms_gpr ms 2) = true)
    by (rewrite Hg2; destruct rd; vm_compute; reflexivity).
  pose (c := fun e => check_walk_refusals (open_walk_mode (open_flag_word rd))
                        (sys_input segs ms (getr regs 17)) (ms_gpr ms 1) e model
                        (open_arm_check rd model p e)).
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = check_getname_refusals (sys_input segs ms (getr regs 17)) [] (ms_gpr ms 1) eff model
        (Prelude.check_copyins_after (open_copyins ms) eff (c (clear_copyins eff)))).
  { intro eff. unfold c.
    rewrite (openat_reduces_to_resolved segs ms (getr regs 17) model p eff
               H17 Hfl Hg0 Hpath' Hpe Hfree).
    rewrite Hg2.
    rewrite (check_openat_resolved_arm rd p (clear_copyins eff) model Hpsf Hans).
    reflexivity. }
  assert (Hwr : forall es,
    walk_reached (open_walk_mode (open_flag_word rd)) (sys_input segs ms (getr regs 17))
      model (ms_gpr ms 1) = Some es ->
    forall e, In e es -> (1 <= e <= 4095)%Z).
  { intros es Hes e He.
    rewrite (walk_reached_si (open_walk_mode (open_flag_word rd)) segs ms (getr regs 17)
               model p Hpath' Hpe) in Hes.
    injection Hes as <-. exact (walk_errnos_range _ _ e He). }
  assert (Hnu : forall eff, c eff <> CheckUnmodeled).
  { intros eff Hc. unfold c in Hc. cbv beta in Hc.
    apply check_walk_refusals_unmodeled in Hc.
    unfold open_arm_check in Hc.
    destruct (open_arm rd (m_fs model) (m_cwd model) p) as [[fe ofs]|e].
    - destruct (open_arm_txtbsy rd (m_fs model) (m_cwd model) p);
        [apply check_open_write_existing_unmodeled in Hc|];
        exact (check_open_result_never_unmodeled _ _ _ Hc).
    - exact (check_ret_only_no_unmodeled _ _ _ _ Hc). }
  (* What [c] accepts outside the arm: a bare errno of the walk. *)
  assert (Hrej : forall eff m' evs,
    open_arm_check rd model p eff = CheckReject ->
    c eff = CheckOk m' evs ->
    evs = [] /\ addr_is_error_b (eff_ret eff) = true /\ m' = model
    /\ eff = mkEffect (eff_ret eff) [] []).
  { intros eff m' evs Ha Hc. unfold c in Hc. cbv beta in Hc.
    unfold check_walk_refusals in Hc. rewrite Ha in Hc.
    destruct (walk_reached (open_walk_mode (open_flag_word rd))
                (sys_input segs ms (getr regs 17)) model (ms_gpr ms 1)) as [es|] eqn:Hw;
      [|discriminate Hc].
    destruct eff as [r ws zs us cs ci].
    destruct ws; [|discriminate Hc]. destruct zs; [|discriminate Hc].
    destruct us; [|discriminate Hc]. destruct cs; [|discriminate Hc].
    destruct ci; [|discriminate Hc].
    destruct (errno_ret_in es r) eqn:Hin; [|discriminate Hc].
    injection Hc as <- <-.
    apply errno_ret_in_true in Hin. destruct Hin as (e & HIn & ->).
    assert (HeR : (1 <= e <= 4095)%Z)
      by first [exact (Hwr es Hw e HIn) | exact (Hwr es eq_refl e HIn)].
    destruct HeR as [He1 He2].
    split; [reflexivity|]. split; [|split; reflexivity].
    cbn [eff_ret]. exact (errno_ret_error_b e He1 He2). }
  destruct (open_arm rd (m_fs model) (m_cwd model) p) as [[fe ofs]|e] eqn:Harm.
  - (* a descriptor, or an errno beside it, -ETXTBSY among them on an
       existing file's write open *)
    assert (Hacok : forall eff m1 evs1, open_arm_check rd model p eff = CheckOk m1 evs1 ->
              check_open_result eff model (fun fd => open_model model fd fe ofs)
                = CheckOk m1 evs1
              \/ (eff = mkEffect (errno_ret ETXTBSY) [] [] /\ m1 = model /\ evs1 = [])).
    { intros eff m1 evs1 Ha. unfold open_arm_check in Ha. rewrite Harm in Ha.
      destruct (open_arm_txtbsy rd (m_fs model) (m_cwd model) p);
        [exact (check_open_write_existing_ok_cases _ _ _ _ _ _ Ha) | left; exact Ha]. }
    assert (Haclift : forall eff m1 evs1,
              check_open_result eff model (fun fd => open_model model fd fe ofs)
                = CheckOk m1 evs1 ->
              open_arm_check rd model p eff = CheckOk m1 evs1).
    { intros eff m1 evs1 Ho. unfold open_arm_check. rewrite Harm.
      destruct (open_arm_txtbsy rd (m_fs model) (m_cwd model) p);
        [exact (check_open_write_existing_lift _ _ _ _ _ _ Ho) | exact Ho]. }
    apply (tfo_sys_signed ms model (getr regs 17) (ms_gpr ms 1) (open_copyins ms) c
             (fun fd => open_model model fd fe ofs) true Uf Us U).
    + unfold ms. reflexivity.
    + exact Hh.
    + exact Hlazy.
    + exact Hchk.
    + exact Hnu.
    + exists (errno_ret ENOMEM).
      destruct (openat_errno_range ENOMEM ENOMEM_in_openat_errnos) as [He1 He2].
      split; [exact (errno_ret_error_b _ He1 He2)|].
      unfold c. cbv beta.
      rewrite (Haclift _ model []); [reflexivity|].
      apply (proj2 (check_open_result_ok_iff _ _ _ model [])).
      left; exists ENOMEM; repeat split; try reflexivity;
        apply ENOMEM_in_openat_errnos.
    + intros eff m' evs Hc.
      destruct (open_arm_check rd model p eff) as [m1 evs1| |] eqn:Ha.
      * unfold c in Hc. cbv beta in Hc. rewrite Ha in Hc. cbn [check_walk_refusals] in Hc.
        injection Hc as <- <-.
        destruct (Hacok _ _ _ Ha) as [Ha' | (Heff & Hm & Hev)].
        -- apply check_open_result_ok_iff in Ha'.
           destruct Ha' as [(e & HIn & Heff & Hm & Hev) | (fd & Hlk & Hfd & Heff & Hm & Hev)].
           ++ split; [exact Hev|]. left.
              destruct (openat_errno_range e HIn) as [He1 He2].
              subst eff. rewrite eff_ret_mk.
              split; [exact (errno_ret_error_b e He1 He2)|]. split; [exact Hm | reflexivity].
           ++ split; [exact Hev|]. right. subst fd.
              split; [reflexivity|]. split; [exact Heff | exact Hm].
        -- split; [exact Hev|]. left.
           subst eff. rewrite eff_ret_mk.
           split; [exact (errno_ret_error_b ETXTBSY ltac:(cbv [ETXTBSY]; lia)
                            ltac:(cbv [ETXTBSY]; lia))|].
           split; [exact Hm | reflexivity].
      * destruct (Hrej eff m' evs Ha Hc) as (Hev & He & Hm & Heq).
        split; [exact Hev|]. left. exact (conj He (conj Hm Heq)).
      * unfold c in Hc. cbv beta in Hc. rewrite Ha in Hc. discriminate Hc.
    + intros _. unfold c. cbv beta.
      rewrite (Haclift _ (open_model model (alloc_fd (m_fds model)) fe ofs) []);
        [reflexivity|].
      apply (proj2 (check_open_result_ok_iff _ _ _
                      (open_model model (alloc_fd (m_fds model)) fe ofs) [])).
      right; exists (alloc_fd (m_fds model)); repeat split; try reflexivity;
        exact Hfree.
    + unfold open_model. destruct ofs; [|destruct (entry_dev_kind fe)]; exact Hh.
    + unfold open_model. destruct ofs; [|destruct (entry_dev_kind fe)]; exact Hlazy.
    + intros r Hr. unfold ms. rewrite adv_eff_ret_copyins. exact (Herr r Hr).
    + intros _. unfold ms. rewrite adv_eff_ret_copyins.
      first [exact (Hok fe ofs Harm) | exact (Hok fe ofs eq_refl)].
    + intro o. rewrite HU. unfold open_ok. rewrite Harm. cbv beta iota. tauto.
  - (* the arm's own errno *)
    destruct (open_arm_errno_range rd (m_fs model) (m_cwd model) p e Harm) as [He1 He2].
    assert (Hac : forall eff, open_arm_check rd model p eff
                              = check_ret_only eff (errno_ret e) model []).
    { intro eff. unfold open_arm_check. rewrite Harm. reflexivity. }
    apply (tfo_sys_signed ms model (getr regs 17) (ms_gpr ms 1) (open_copyins ms) c
             (fun _ => model) false Uf Us U).
    + unfold ms. reflexivity.
    + exact Hh.
    + exact Hlazy.
    + exact Hchk.
    + exact Hnu.
    + exists (errno_ret e). split; [exact (errno_ret_error_b e He1 He2)|].
      unfold c. cbv beta. rewrite Hac.
      rewrite (proj2 (check_ret_only_ok_iff _ _ _ _ model []))
        by (repeat split; reflexivity).
      reflexivity.
    + intros eff m' evs Hc.
      destruct (open_arm_check rd model p eff) as [m1 evs1| |] eqn:Ha.
      * unfold c in Hc. cbv beta in Hc. rewrite Ha in Hc. cbn [check_walk_refusals] in Hc.
        injection Hc as <- <-.
        rewrite Hac in Ha. apply check_ret_only_ok_iff in Ha.
        destruct Ha as (Heff & Hm & Hev).
        split; [exact Hev|]. left. subst eff. rewrite eff_ret_mk.
        split; [exact (errno_ret_error_b e He1 He2)|]. split; [exact Hm | reflexivity].
      * destruct (Hrej eff m' evs Ha Hc) as (Hev & He & Hm & Heq).
        split; [exact Hev|]. left. exact (conj He (conj Hm Heq)).
      * unfold c in Hc. cbv beta in Hc. rewrite Ha in Hc. discriminate Hc.
    + intros Hf. discriminate Hf.
    + exact Hh.
    + exact Hlazy.
    + intros r Hr. unfold ms. rewrite adv_eff_ret_copyins. exact (Herr r Hr).
    + intros Hf. discriminate Hf.
    + intro o. rewrite HU. unfold open_ok. rewrite Harm. cbv beta iota. tauto.
Qed.

(** THE OPEN OF AN ARGV OPERAND, whatever its length.  The fetch of the
    pathname gives the string itself when its NUL is within PATH_MAX and
    [CstrTooLong] otherwise.  An empty pathname is -ENOENT and one that
    does not fit is -ENAMETOOLONG, both before any walk
    ([Open.openat_body_spec]); a pathname that reaches the walk is
    [tfo_open_signed_rec]'s.  Every errno takes [Uf], the one descriptor
    [Us]. *)
Lemma tfo_open_operand_rec : forall regs pc mem model p (rd : bool)
    (Uf Us U : (word * Fs.Fs) -> Prop),
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD ->
  reg_get regs 12 = open_flag_word rd ->
  read_cstr (mrb segs mem) (reg_get regs 11)
    = (if Nat.ltb (length p) path_max then CstrOk p else CstrTooLong) ->
  (op_walked p = true -> proc_self_fd p = None) ->
  (op_walked p = true -> open_answered rd (m_fs model) (m_cwd model) p) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall r, addr_is_error_b r = true ->
     to_fout segs (mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs)) model Uf) ->
  (forall fe ofs, open_arm rd (m_fs model) (m_cwd model) p = inl (fe, ofs) ->
     to_fout segs (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem
                        (seg_rom segs))
       (open_model model (alloc_fd (m_fds model)) fe ofs) Us) ->
  (forall o, U o <-> Uf o \/ (op_walked p = true
                             /\ open_ok rd (m_fs model) (m_cwd model) p = true /\ Us o)) ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p rd Uf Us U H17 H10 H12 Hpath Hpsf Hans Hfree Hh Hlazy
    Herr Hok HU.
  assert (Hfl : modeled_open_flags (reg_get regs 12) = true)
    by (rewrite H12; destruct rd; vm_compute; reflexivity).
  destruct (Nat.ltb (length p) path_max) eqn:Hlt;
    rewrite ?Hlt in Hpath; cbv beta iota in Hpath.
  - destruct (path_eqb p []) eqn:Hpe.
    + (* the empty pathname: -ENOENT before the walk *)
      assert (Hw : op_walked p = false)
        by (unfold op_walked; rewrite Hpe; reflexivity).
      apply (tfo_equiv segs _ _ Uf U).
      2:{ intro o. rewrite HU, Hw. split;
            [ intros [Ho | (Hf & _)]; [exact Ho | discriminate Hf]
            | intros Ho; left; exact Ho ]. }
      set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                    ms_svc_pending := Some (getr regs 17);
                    ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem;
                    ms_rom := seg_rom segs |}).
      apply (tfo_openat_empty_enoent segs ms model (getr regs 17) p Uf).
      * unfold ms. reflexivity.
      * exact H17.
      * unfold ms. rewrite record_gpr, arg_reg_1.
        rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
      * exact Hpe.
      * unfold ms. rewrite record_gpr, arg_reg_2. exact Hfl.
      * exact Hh.
      * exact Hlazy.
      * unfold ms. rewrite adv_eff_ret_copyins.
        apply Herr. apply errno_ret_error_b; cbv [ENOENT]; lia.
      * intros e He. unfold ms. rewrite adv_eff_ret_copyins.
        apply Herr. cbn [getname_errnos In] in He.
        destruct He as [<- | []]. apply errno_ret_error_b; cbv [ENOMEM]; lia.
    + (* the walk *)
      assert (Hw : op_walked p = true)
        by (unfold op_walked; rewrite Hpe, Hlt; reflexivity).
      apply (tfo_open_signed_rec regs pc mem model p rd Uf Us U H17 H10 H12 Hpath
               Hpe (Hpsf Hw) (Hans Hw) Hfree Hh Hlazy Herr Hok).
      intro o. rewrite HU, Hw. split.
      * intros [Ho | (_ & Ho)]; [left; exact Ho | right; exact Ho].
      * intros [Ho | Ho]; [left; exact Ho | right; split; [reflexivity | exact Ho]].
  - (* no NUL within PATH_MAX: -ENAMETOOLONG before the walk *)
    assert (Hw : op_walked p = false)
      by (unfold op_walked; rewrite Hlt, andb_false_r; reflexivity).
    apply (tfo_equiv segs _ _ Uf U).
    2:{ intro o. rewrite HU, Hw. split;
          [ intros [Ho | (Hf & _)]; [exact Ho | discriminate Hf]
          | intros Ho; left; exact Ho ]. }
    apply (tfo_open_toolong_rec segs regs pc mem model Uf H17 Hfl Hpath Hh Hlazy).
    + apply Herr. apply errno_ret_error_b; cbv [ENAMETOOLONG]; lia.
    + intros e He. apply Herr. cbn [getname_errnos In] in He.
      destruct He as [<- | []]. apply errno_ret_error_b; cbv [ENOMEM]; lia.
Qed.

(* ========================================================================= *)
(* Reads and writes on a folder and on the two devices                       *)
(* ========================================================================= *)

(** A call whose checker accepts exactly one bare return [r] and the
    model [model'] ([check_ret_only]). *)
Lemma tfo_det_ret : forall ms model x8 r model' U,
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only eff r model' []) ->
  m_halted model' = None ->
  m_vm_lazy model' = [] ->
  to_fout segs (advance_past_svc (apply_effect ms (mkEffect r [] []))) model' U ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 r model' U Hsvc Hchk Hh Hlazy Hcont.
  apply (tfo_sys_det segs ms model x8 (mkEffect r [] []) model' U);
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk. apply check_ret_only_ok_iff. auto.
  - intros eff2 m2 evs2 Hs. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs. exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.

(** read(2) of a FOLDER descriptor: -EISDIR ([generic_read_dir]),
    once [vfs_read]'s [access_ok] passes. *)
Lemma tfo_read_dir_rec : forall regs pc mem rom model fdv k buf cnt U,
  bv_unsigned (getr regs 17) = 63%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdDir k) ->
  fd32 fdv = fdv ->
  access_okb buf (bv_unsigned cnt) = true ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) model U ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} model U.
Proof.
  intros regs pc mem rom model fdv k buf cnt U H17 H10 H11 H12 Hfd Hfd32 Haok
    Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  apply (tfo_det_ret ms model (getr regs 17) (errno_ret EISDIR) model U);
    [unfold ms; reflexivity | | exact Hh | exact Hlazy |].
  - intro eff.
    rewrite (check_syscall_63 segs ms _ eff model H17). unfold check_read.
    rewrite Hg0, Hfd32, Hfd, Hg1, Hg2. cbv beta iota.
    rewrite Haok. reflexivity.
  - unfold ms. rewrite adv_eff_ret. exact Hcont.
Qed.

(** read(2) of /dev/null opened for reading: 0 ([read_null]). *)
Lemma tfo_read_null_rec : forall regs pc mem rom model fdv wr buf cnt U,
  bv_unsigned (getr regs 17) = 63%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdDevNull true wr) ->
  fd32 fdv = fdv ->
  access_okb buf (bv_unsigned cnt) = true ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom) model U ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} model U.
Proof.
  intros regs pc mem rom model fdv wr buf cnt U H17 H10 H11 H12 Hfd Hfd32 Haok
    Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  apply (tfo_det_ret ms model (getr regs 17) (Z_to_bv 64 0) model U);
    [unfold ms; reflexivity | | exact Hh | exact Hlazy |].
  - intro eff.
    rewrite (check_syscall_63 segs ms _ eff model H17). unfold check_read.
    rewrite Hg0, Hfd32, Hfd, Hg1, Hg2. cbv beta iota. cbn [negb].
    unfold check_access_ok_zero. rewrite Haok. reflexivity.
  - unfold ms. rewrite adv_eff_ret. exact Hcont.
Qed.

(** write(2) to /dev/null opened for writing: the count ([write_null]),
    no byte read. *)
Lemma tfo_write_null_rec : forall regs pc mem rom model fdv rd buf cnt U,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdDevNull rd true) ->
  fd32 fdv = fdv ->
  access_okb buf (bv_unsigned cnt) = true ->
  (bv_unsigned cnt <= rw_bytes_max)%Z ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 cnt) (v_addi pc 4) mem rom) model U ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} model U.
Proof.
  intros regs pc mem rom model fdv rd buf cnt U H17 H10 H11 H12 Hfd Hfd32 Haok Hcnt
    Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  apply (tfo_det_ret ms model (getr regs 17) cnt model U);
    [unfold ms; reflexivity | | exact Hh | exact Hlazy |].
  - intro eff.
    rewrite (check_syscall_64 segs ms _ eff model H17). unfold check_write.
    rewrite Hg0, Hfd32, Hfd, Hg1, Hg2. cbv beta iota. cbn [negb].
    unfold modeled_rw_range. rewrite Haok, orb_true_r. cbn [negb].
    unfold check_access_ok_zero. rewrite Haok.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned. reflexivity.
  - unfold ms. rewrite adv_eff_ret. exact Hcont.
Qed.

(** No page multiple lies strictly between 0 and a count of at most a
    page, so /dev/urandom serves such a count whole. *)
Lemma random_page_stopb_small : forall n k,
  (n <= page_size)%Z -> random_page_stopb n k = false.
Proof.
  intros n k Hn. unfold random_page_stopb.
  destruct (Z.ltb 0 k) eqn:H1; [|reflexivity].
  destruct (Z.ltb k n) eqn:H2; [|reflexivity].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. cbn [andb].
  unfold page_size in *.
  rewrite Z.mod_small by lia. apply Z.eqb_neq. lia.
Qed.

Lemma random_write_countb_full : forall n r,
  (0 < n <= page_size)%Z ->
  random_write_countb n n r = Z.eqb r n.
Proof.
  intros n r Hn. unfold random_write_countb. cbv zeta.
  rewrite Z.min_id.
  rewrite (random_page_stopb_small n r) by lia.
  destruct (Z.eqb r n); reflexivity.
Qed.

(** write(2) to /dev/urandom opened for writing, from a buffer every
    byte of which reads: the whole count ([random_write_iter] takes a
    readable request of at most a page whole), the range read as the
    copy-in; a count of 0 moves nothing. *)
Lemma tfo_write_urandom_rec : forall regs pc mem model fdv rd buf cnt bs U,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdUrandom rd true) ->
  fd32 fdv = fdv ->
  rdn segs mem buf (word_to_nat cnt) = Some bs ->
  access_okb buf (bv_unsigned cnt) = true ->
  (bv_unsigned cnt <= page_size)%Z ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 cnt) (v_addi pc 4) mem (seg_rom segs)) model U ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model fdv rd buf cnt bs U H17 H10 H11 H12 Hfd Hfd32 Hrd Haok Hpg
    Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  assert (Hcnt : (bv_unsigned cnt <= rw_bytes_max)%Z)
    by (unfold rw_bytes_max, page_size in *; lia).
  assert (Hrb : read_bytes_map (ms_read_byte ms) buf cnt = Some bs).
  { rewrite read_bytes_map_read_byte.
    rewrite (ms_read_bytes_rdn segs ms) by reflexivity. exact Hrd. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (u64_range cnt) as Hrange.
  (* the device arm, down to [check_random_write] *)
  assert (Hdev : forall eff,
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = check_random_write (bv_unsigned cnt) (bv_unsigned cnt)
        (fun r => [(buf, Z.to_nat r)]) eff model).
  { intro eff.
    rewrite (check_syscall_64 segs ms _ eff model H17). unfold check_write.
    rewrite Hg0, Hfd32, Hfd, Hg1, Hg2. cbv beta iota. cbn [negb].
    unfold modeled_rw_range. rewrite Haok, orb_true_r. cbn [negb].
    unfold check_access_ok_zero. rewrite Haok.
    rewrite in_mem_si.
    rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
    rewrite (rw_count_clamp_of_rw _ Hcnt), Hlen. reflexivity. }
  destruct (Z.eqb (bv_unsigned cnt) 0) eqn:Hz.
  - (* count 0: no byte moves *)
    apply Z.eqb_eq in Hz.
    assert (Hc0 : cnt = Z_to_bv 64 0)
      by (rewrite <- (Z_to_bv_bv_unsigned 64 cnt), Hz; reflexivity).
    apply (tfo_det_ret ms model (getr regs 17) cnt model U);
      [unfold ms; reflexivity | | exact Hh | exact Hlazy |].
    + intro eff. rewrite Hdev, check_random_write_eq, Hz. cbn [Z.eqb].
      rewrite Hc0. reflexivity.
    + unfold ms. rewrite adv_eff_ret. exact Hcont.
  - (* a positive count: all of it *)
    apply Z.eqb_neq in Hz.
    assert (Hn0 : Z.eqb (bv_unsigned cnt) 0 = false) by (apply Z.eqb_neq; exact Hz).
    assert (H0n : Z.eqb 0 (bv_unsigned cnt) = false) by (apply Z.eqb_neq; lia).
    assert (Hiff : forall eff m' evs,
      check_syscall (sys_input segs ms (getr regs 17)) eff model = CheckOk m' evs <->
      (eff = with_copyins [(buf, Z.to_nat (bv_unsigned cnt))] (mkEffect cnt [] [])
       /\ m' = model /\ evs = [])).
    { intros [ret ws zs us cs ci] m' evs.
      rewrite Hdev, check_random_write_eq, Hn0.
      destruct ws as [|w ws];
        [| split; [intro H; discriminate H | intros (H & _); discriminate H]].
      destruct zs as [|z zs];
        [| split; [intro H; discriminate H | intros (H & _); discriminate H]].
      destruct us as [|u us];
        [| split; [intro H; discriminate H | intros (H & _); discriminate H]].
      destruct cs as [|c cs];
        [| split; [intro H; discriminate H | intros (H & _); discriminate H]].
      cbv beta iota.
      rewrite (random_write_countb_full (bv_unsigned cnt) (bv_unsigned ret)) by lia.
      rewrite (random_write_countb_full (bv_unsigned cnt) 0) by lia.
      rewrite H0n, !andb_false_r. cbn [andb].
      destruct (Z.eqb (bv_unsigned ret) (bv_unsigned cnt)) eqn:Hr.
      - apply Z.eqb_eq in Hr. apply bv_eq in Hr. subst ret.
        rewrite (w_is0_pos cnt) by lia. cbn [negb andb].
        destruct (access_ranges_eqb ci [(buf, Z.to_nat (bv_unsigned cnt))]) eqn:Hci.
        + apply access_ranges_eqb_eq in Hci. subst ci. split.
          * intro H. injection H as <- <-. split; [reflexivity|]. split; reflexivity.
          * intros (_ & -> & ->). reflexivity.
        + split; [intro H; discriminate H|].
          intros (H & _). apply (f_equal eff_copyins) in H. cbn in H. subst ci.
          rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl) in Hci. discriminate Hci.
      - rewrite andb_false_r. cbn [andb]. split; [intro H; discriminate H|].
        intros (H & _). apply (f_equal eff_ret) in H. cbn in H. subst ret.
        rewrite Z.eqb_refl in Hr. discriminate Hr. }
    apply (tfo_sys_det segs ms model (getr regs 17)
             (with_copyins [(buf, Z.to_nat (bv_unsigned cnt))] (mkEffect cnt [] []))
             model U).
    + unfold ms. reflexivity.
    + apply check_syscall_ok_iff. apply Hiff. auto.
    + intros eff2 m2 evs2 Hs. apply check_syscall_ok_iff in Hs. apply Hiff in Hs. exact Hs.
    + intro Hs.
      apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
      rewrite Hdev in Hs. exact (check_random_write_no_unmodeled _ _ _ _ _ Hs).
    + exact Hh.
    + exact Hlazy.
    + unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

(** read(2) of /dev/urandom opened for reading, a count of at most a
    page into a buffer whose every byte is writable: the whole count off
    the front of the run's declared stream ([read_urandom]; an endless
    stream, [Run.valid_urandom]), the stream advanced past it. *)
Lemma tfo_read_urandom_rec : forall regs pc mem rom model fdv wr buf cnt U,
  bv_unsigned (getr regs 17) = 63%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdUrandom true wr) ->
  fd32 fdv = fdv ->
  wseg_ok segs buf (word_to_nat cnt) = true ->
  (0 < bv_unsigned cnt <= page_size)%Z ->
  access_okb buf (bv_unsigned cnt) = true ->
  stream_infinite (m_urandom model) ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs
    (mkst (regupd regs 10 cnt) (v_addi pc 4)
          (write_to_mem mem buf (fst (stream_take_z (m_urandom model) (bv_unsigned cnt))))
          rom)
    (with_urandom (snd (stream_take_z (m_urandom model) (bv_unsigned cnt))) model) U ->
  to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} model U.
Proof.
  intros regs pc mem rom model fdv wr buf cnt U H17 H10 H11 H12 Hfd Hfd32 Hwseg Hpos
    Haok Hinf Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
  assert (Hcnt : (bv_unsigned cnt <= rw_bytes_max)%Z)
    by (unfold rw_bytes_max, page_size in *; lia).
  assert (Hlenz : Z.of_nat (length (fst (stream_take_z (m_urandom model) (bv_unsigned cnt))))
                  = bv_unsigned cnt)
    by (apply stream_take_z_infinite_length; [exact Hinf | lia]).
  assert (Hlw : len_word (fst (stream_take_z (m_urandom model) (bv_unsigned cnt))) = cnt).
  { unfold len_word. rewrite Hlenz. apply Z_to_bv_bv_unsigned. }
  assert (Hbs_ne : fst (stream_take_z (m_urandom model) (bv_unsigned cnt)) <> []).
  { intro He. rewrite He in Hlenz. cbn in Hlenz. lia. }
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  destruct (wseg_ok_wdef segs buf cnt ms Hwseg) as [w Hw].
  assert (Hw1 : exists w1, read_bytes_map (ms_writable_byte segs ms) buf (Z_to_bv 64 1)
                          = Some w1).
  { eexists. apply (read_bytes_map_prefix _ _ cnt _ w); [|exact Hw].
    change (bv_unsigned (Z_to_bv 64 1)) with 1%Z. lia. }
  destruct Hw1 as [w1 Hw1].
  (* the device arm, down to the acceptor over the effect *)
  assert (Hdev : forall eff,
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = match eff with
      | mkEffectU ret [(a, bs')] [] [] [] [] =>
          if (bv_eqb a buf
              && (Z.eqb (Z.of_nat (length bs')) (bv_unsigned cnt)
                  || random_page_stopb (bv_unsigned cnt) (Z.of_nat (length bs')))
              && bv_eqb ret (len_word bs')
              && listN_eqb bs' (fst (stream_take_z (m_urandom model)
                                       (Z.of_nat (length bs')))))%bool
          then CheckOk (with_urandom (snd (stream_take_z (m_urandom model)
                                             (Z.of_nat (length bs')))) model) []
          else CheckReject
      | _ => CheckReject
      end).
  { intro eff.
    rewrite (check_syscall_63 segs ms _ eff model H17). unfold check_read.
    rewrite Hg0, Hfd32, Hfd, Hg1, Hg2. cbv beta iota. cbn [negb].
    rewrite Haok. cbn [negb]. cbv beta iota.
    unfold check_read_urandom.
    rewrite (w_is0_pos cnt) by lia. cbv beta iota.
    rewrite in_wmem_si, Hw1. cbv beta iota zeta.
    rewrite (rw_count_clamp_of_rw _ Hcnt).
    rewrite Hlenz, Z.eqb_refl. cbn [negb]. cbv beta iota.
    rewrite Hlw, Hw. cbv beta iota. reflexivity. }
  assert (Hchk : forall eff m' evs,
    check_syscall (sys_input segs ms (getr regs 17)) eff model = CheckOk m' evs <->
    (eff = mkEffect cnt (delivered_writes buf
                           (fst (stream_take_z (m_urandom model) (bv_unsigned cnt)))) []
     /\ m' = with_urandom (snd (stream_take_z (m_urandom model) (bv_unsigned cnt))) model
     /\ evs = [])).
  { intros eff m' evs. rewrite Hdev.
    rewrite (delivered_writes_ne buf _ Hbs_ne).
    destruct eff as [ret ws zs us cs ci]. split.
    - intro H.
      destruct ws as [|[a bs'] [|? ?]]; try discriminate H.
      destruct zs as [|? ?]; [|discriminate H].
      destruct us as [|? ?]; [|discriminate H].
      destruct cs as [|? ?]; [|discriminate H].
      destruct ci as [|? ?]; [|discriminate H].
      rewrite (random_page_stopb_small (bv_unsigned cnt)) in H by lia.
      rewrite orb_false_r in H.
      match type of H with
      | (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate H]
      end.
      injection H as <- <-.
      repeat rewrite andb_true_iff in Hb. destruct Hb as [[[Ha Hk] Hr] Hl].
      apply bv_eqb_eq in Ha. apply Z.eqb_eq in Hk.
      apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hl.
      rewrite Hk in Hl. subst a. rewrite Hk. rewrite <- Hl.
      rewrite Hr. rewrite Hl, Hlw.
      split; [reflexivity|]. split; reflexivity.
    - intros (Heff & -> & ->).
      injection Heff as -> -> -> -> -> ->.
      rewrite Hlenz.
      rewrite (random_page_stopb_small (bv_unsigned cnt)) by lia.
      rewrite Hlw, !bv_eqb_refl, Z.eqb_refl.
      rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
      reflexivity. }
  apply (tfo_sys_det segs ms model (getr regs 17)
           (mkEffect cnt (delivered_writes buf
                            (fst (stream_take_z (m_urandom model) (bv_unsigned cnt)))) [])
           (with_urandom (snd (stream_take_z (m_urandom model) (bv_unsigned cnt))) model) U).
  - unfold ms. reflexivity.
  - apply check_syscall_ok_iff. apply Hchk. auto.
  - intros eff2 m2 evs2 Hs. apply check_syscall_ok_iff in Hs. apply Hchk in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hdev in Hs. discriminate Hs.
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_apply_delivered. exact Hcont.
Qed.

End Signed.

End WithFP.

(** Argv string [k] and its NUL end at or below [State.TASK_SIZE]: they
    end below the stack VMA's end [ed_top] (the arithmetic of
    [SeqExec.argv_ptr_bounds]), and under Sv48 [ed_top] is at most
    [sp_window_hi], which is [TASK_SIZE].  So a pathname fetch of the
    string ([read_cstr]) reads user memory only. *)
Lemma argv_str_task : forall inp mbase (sp brk : word) draw,
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  forall k, (k < length (in_argv inp))%nat ->
  (bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
   + Z.of_nat (length (nth k (in_argv inp) [])) + 1 <= TASK_SIZE)%Z.
Proof.
  intros inp mbase sp brk draw Hlau k Hk.
  pose proof (launch_string_base_arith Sv48 inp mbase sp brk draw Hlau) as HA.
  pose proof (u_cat_string_base Sv48 inp mbase sp brk draw Hlau) as Hu.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  pose proof (total_arg_bytes_firstn_within (in_argv inp) k Hk) as Hw.
  assert (Htop : (bv_unsigned (ed_top draw) <= TASK_SIZE)%Z).
  { destruct Hlau as ((_ & Ht & _) & _ & _). cbn [va_stack_top] in Ht.
    unfold TASK_SIZE. unfold sp_window_hi in Ht. lia. }
  assert (Hstr : (Z.of_nat (total_arg_bytes_nat (firstn k (in_argv inp)))
                  + Z.of_nat (length (nth k (in_argv inp) [])) + 1
                  <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)))%Z).
  { unfold launch_string_bytes. rewrite (length_flatten_strings (in_argv inp)). lia. }
  rewrite (cat_argv_ptr_offset (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k Hk).
  rewrite StepTac.word_add_nat, Hu.
  rewrite StepTac.u_Z2bv by lia.
  lia.
Qed.

(** THE PATHNAME FETCH OF ARGV STRING [k], from any memory that reads as
    the launch's above [sp]: the string itself when it fits in PATH_MAX
    with its NUL, [CstrTooLong] otherwise ([Run.valid_argv]: no string
    holds a NUL). *)
Lemma read_cstr_argv : forall segs mem inp mbase ph entry (sp brk : word) draw k,
  valid_argv (in_argv inp) ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  (forall (a : word) n, (bv_unsigned sp <= bv_unsigned a)%Z ->
     (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
     rdn segs mem a n = rdn segs (wrap_mem inp mbase ph entry sp draw) a n) ->
  read_cstr (mrb segs mem)
    (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
  = if Nat.ltb (length (nth k (in_argv inp) [])) path_max
    then CstrOk (nth k (in_argv inp) []) else CstrTooLong.
Proof.
  intros segs mem inp mbase ph entry sp brk draw k Hva Hlau Hk Hmem.
  destruct (argv_ptr_bounds Sv48 inp mbase sp brk draw k Hlau Hk) as [Hplo Hphi].
  pose proof (argv_str_task inp mbase sp brk draw Hlau k Hk) as Htask.
  pose proof (valid_argv_str_nz (in_argv inp) k Hva Hk) as Hnz.
  destruct (Nat.ltb (length (nth k (in_argv inp) [])) path_max) eqn:Hlt;
    cbv beta iota.
  - apply Nat.ltb_lt in Hlt. change path_max with 4096%nat in Hlt.
    apply read_cstr_of_rdn; [lia | exact Hnz | lia |].
    rewrite Hmem by lia. rewrite rdn_wrap_stack_above by lia.
    exact (read_argv_cstr_k Sv48 segs inp mbase ph entry sp brk draw k Hlau Hk).
  - apply Nat.ltb_ge in Hlt. change path_max with 4096%nat in Hlt.
    apply (read_cstr_toolong_of_rdn segs mem _
             (firstn 4096 (nth k (in_argv inp) []))).
    + apply firstn_length_le. exact Hlt.
    + intro Hin. apply Hnz.
      rewrite <- (firstn_skipn 4096 (nth k (in_argv inp) [])).
      apply in_or_app. left. exact Hin.
    + lia.
    + rewrite Hmem by lia. rewrite rdn_wrap_stack_above by lia.
      exact (read_argv_prefix_k Sv48 segs inp mbase ph entry sp brk draw k 4096
               Hlau Hk Hlt).
Qed.
