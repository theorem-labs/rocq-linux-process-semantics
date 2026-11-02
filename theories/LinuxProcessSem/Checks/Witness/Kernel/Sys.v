(** * LinuxProcessSem.Checks.Witness.Kernel.Sys — the getpid (172), getppid (173), gettid (178), setsid (157), getsid (156), uname (160), prctl (167), prlimit64 (261) witnesses, and their proofs

    Mirrors [Sys/Kernel/Sys.v], which answers to Linux [kernel/sys.c]:
    this file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude Kernel.Fork.

(** getpid witness: the same witness as set_tid_address's, because
    [Kernel.Sys.getpid_spec] is the same relation. *)

Definition getpid_witness : Model -> outcome SyscallEffect :=
  set_tid_address_witness.

Lemma getpid_witness_ok : forall i m, getpid_spec i m (getpid_witness m).
Proof. exact set_tid_address_witness_ok. Qed.

(** gettid witness: the same witness again, because
    [Kernel.Sys.gettid_spec] is the same relation. *)

Definition gettid_witness : Model -> outcome SyscallEffect :=
  set_tid_address_witness.

Lemma gettid_witness_ok : forall i m, gettid_spec i m (gettid_witness m).
Proof. exact set_tid_address_witness_ok. Qed.

(** getppid witness: 0, the answer for a parent outside the caller's pid
    namespace, which is inside [Kernel.Sys.getppid_spec]'s range and
    leaves the model alone. *)
Definition getppid_witness (m : Model) : outcome SyscallEffect :=
  ret_outcome (Z_to_bv 64 0) m.

Lemma getppid_witness_ok : forall i m, getppid_spec i m (getppid_witness m).
Proof.
  intros. unfold getppid_spec, getppid_witness.
  eapply bind_step;
    [apply (choose_ok _ (Z_to_bv 64 0)); vm_compute; reflexivity|].
  apply pure_ok.
Qed.

(** setsid witness: -EPERM, which is admissible whatever the model
    believes — it is the only answer once a setsid has succeeded, and
    [Kernel.Sys.setsid_spec]'s untracked-environment arm before that.  It
    also leaves the model alone, which is why this witness needs no
    case split. *)
Definition setsid_witness (m : Model) : outcome SyscallEffect :=
  ret_outcome (errno_ret EPERM) m.

Lemma setsid_witness_ok : forall i m, setsid_spec i m (setsid_witness m).
Proof.
  intros. unfold setsid_spec, setsid_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (m_setsid_succeeded m); cbv iota;
    [apply pure_ok | apply alt_l; apply pure_ok].
Qed.

(** getsid witness: the spec's own answer where it has one -- the tid
    after a successful setsid -- and otherwise [getppid_witness]'s 0,
    which is inside [Kernel.Sys.getsid_spec]'s fresh range (a session led
    from an ancestor pid namespace).  It declines where the spec does. *)
Definition getsid_witness (pid : word) (m : Model) : outcome SyscallEffect :=
  if negb (getsid_pid_ok pid (m_tid m)) then Unmodeled
  else if m_setsid_succeeded m then
    match m_tid m with
    | Some t => ret_outcome t m
    | None => Unmodeled
    end
  else getppid_witness m.

Lemma getsid_witness_ok : forall pid i m, getsid_spec pid i m (getsid_witness pid m).
Proof.
  intros. unfold getsid_spec, getsid_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (getsid_pid_ok pid (m_tid m))); [apply unmodeled_intro|].
  destruct (m_setsid_succeeded m).
  - destruct (m_tid m) as [t|]; [apply pure_ok|apply unmodeled_intro].
  - exact (getppid_witness_ok i m).
Qed.

(** ioctl witness: -EBADF on a closed fd, -ENOTTY on a terminal-only
    request, [Unmodeled] on any other request. *)

(* =========================================================================
   fsync (82) / fdatasync (83) — deterministic and, on success, inert:
   0 for any file or directory fd, -EINVAL for a channel, -EBADF
   otherwise.  No arm is [Unmodeled].
   ========================================================================= *)

(** One utsname inside [Kernel.Sys.utsname_wf]'s envelope: the two
    members the kernel source pins, and NUL for the four it does not.
    That is a name a real kernel can hold — [sethostname(name, 0)] and
    [setdomainname(name, 0)] each clear their member outright — but the
    witness does not need it to be: it exhibits ONE admissible outcome so
    that progress has something to step to, exactly as [rlim64_zero] does
    for the limit pair. *)
Definition utsname_default : list byte :=
  uts_literal uts_sysname_chars
  ++ uts_literal [] ++ uts_literal [] ++ uts_literal []
  ++ uts_literal uts_machine_chars
  ++ uts_literal [].

Lemma utsname_default_wf : utsname_wf utsname_default = true.
Proof. vm_compute. reflexivity. Qed.

Definition uname_witness (name : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if negb (access_okb name NEW_UTSNAME_SIZE)
  then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map (in_wmem i) name (Z_to_bv 64 NEW_UTSNAME_SIZE) with
    | None => Unmodeled
    | Some _ =>
        match m_utsname m with
        | Some bs => Ok (mkEffect (Z_to_bv 64 0) [(name, bs)] []) m []
        | None =>
            Ok (mkEffect (Z_to_bv 64 0) [(name, utsname_default)] [])
               (with_utsname utsname_default m) []
        end
    end.

Lemma uname_witness_ok : forall name i m,
  uname_spec name i m (uname_witness name i m).
Proof.
  intros name i m. unfold uname_spec, uname_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb name NEW_UTSNAME_SIZE)); [apply pure_ok|].
  destruct (read_bytes_map (in_wmem i) name (Z_to_bv 64 NEW_UTSNAME_SIZE))
    as [bs1|]; [|apply unmodeled_intro].
  destruct (m_utsname m) as [bs|]; [apply pure_ok|].
  eapply bind_step;
    [apply (choose_ok _ utsname_default); exact utsname_default_wf|].
  eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.

Definition rlim64_zero : list byte := repeat (Z_to_bv 8 0) 16.

Lemma rlim64_zero_wf : rlim64_wf rlim64_zero = true.
Proof. reflexivity. Qed.

Definition prlimit64_witness (pid resource new_rlim old_rlim : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if negb (w_is0 pid) then Unmodeled
  else if negb (Z.eqb (bv_unsigned resource) RLIMIT_CORE) then Unmodeled
  else if (w_is0 new_rlim && w_is0 old_rlim)%bool then Unmodeled
  else if (negb (w_is0 new_rlim) && negb (w_is0 old_rlim))%bool then Unmodeled
  else if w_is0 new_rlim then
    match copy_bytes_map (in_wmem i) old_rlim 16 with
    | None =>
        if negb (access_okb old_rlim 16)
        then ret_outcome (errno_ret EFAULT) m else Unmodeled
    | Some _ =>
        match m_rlimit_core m with
        | Some bs => Ok (mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] []) m []
        | None =>
            Ok (mkEffect (Z_to_bv 64 0) [(old_rlim, rlim64_zero)] [])
               (with_rlimit_core rlim64_zero m) []
        end
    end
  else
    match m_rlimit_core m with
    | None => Unmodeled
    | Some bs0 =>
        match copy_bytes_map (in_mem i) new_rlim 16 with
        | None =>
            if negb (access_okb new_rlim 16)
            then ret_outcome (errno_ret EFAULT) m else Unmodeled
        | Some nb =>
            outcome_copyins [(new_rlim, 16%nat)]
            (
            if (bv_unsigned (rlim64_hard nb) <? bv_unsigned (rlim64_soft nb))%Z
            then ret_outcome (errno_ret EINVAL) m
            else if negb (bv_eqb (rlim64_hard nb) (rlim64_hard bs0))
            then Unmodeled
            else ret_outcome (Z_to_bv 64 0) (with_rlimit_core nb m))
        end
    end.

Lemma prlimit64_witness_ok : forall pid resource new_rlim old_rlim i m,
  prlimit64_spec pid resource new_rlim old_rlim i m
    (prlimit64_witness pid resource new_rlim old_rlim i m).
Proof.
  intros pid resource new_rlim old_rlim i m.
  unfold prlimit64_spec, prlimit64_witness.
  destruct (negb (w_is0 pid)); [apply unmodeled_intro|].
  destruct (negb (Z.eqb (bv_unsigned resource) RLIMIT_CORE));
    [apply unmodeled_intro|].
  destruct (w_is0 new_rlim && w_is0 old_rlim)%bool; [apply unmodeled_intro|].
  destruct (negb (w_is0 new_rlim) && negb (w_is0 old_rlim))%bool;
    [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (w_is0 new_rlim).
  - destruct (copy_bytes_map (in_wmem i) old_rlim 16) as [bs1|].
    + destruct (m_rlimit_core m) as [bs|]; [apply pure_ok|].
      eapply bind_step; [apply (choose_ok _ rlim64_zero); exact rlim64_zero_wf|].
      eapply bind_step; [apply modify_ok|]. apply pure_ok.
    + destruct (negb (access_okb old_rlim 16));
        [apply pure_ok|apply unmodeled_intro].
  - destruct (m_rlimit_core m) as [bs0|]; [|apply unmodeled_intro].
    destruct (copy_bytes_map (in_mem i) new_rlim 16) as [nb|].
    + apply record_copyins_outcome.
      destruct ((bv_unsigned (rlim64_hard nb)
                 <? bv_unsigned (rlim64_soft nb))%Z); [apply pure_ok|].
      destruct (negb (bv_eqb (rlim64_hard nb) (rlim64_hard bs0)));
        [apply unmodeled_intro|].
      eapply bind_step; [apply modify_ok|]. apply pure_ok.
    + destruct (negb (access_okb new_rlim 16));
        [apply pure_ok|apply unmodeled_intro].
Qed.

(* =========================================================================
   The dispatcher
   ========================================================================= *)

(* =========================================================================
   ftruncate (46) — every arm is deterministic, so the witness is just the
   spec's own answer: there is no [alt] and no [errno_from] to choose a
   branch of, and receptivity needs no inhabitation lemma.
   ========================================================================= *)

(* =========================================================================
   Credentials — one admissible outcome for each of the eight id calls.
   ========================================================================= *)

Lemma In_ENOMEM_setid_errnos : forall b, In ENOMEM (setid_errnos b).
Proof. destruct b; simpl; auto. Qed.

(** The readers are total: the stored id, and no model step. *)
Definition getid_witness (sel : Creds -> word) (m : Model)
    : outcome SyscallEffect :=
  ret_outcome (sel (m_creds m)) m.

Lemma getid_witness_ok : forall sel i m, getid_spec sel i m (getid_witness sel m).
Proof.
  intros. unfold getid_spec, getid_witness.
  eapply bind_step; [apply get_model_ok|]. apply pure_ok.
Qed.

(** [getresuid]/[getresgid]: the spec makes no choice, so the witness is
    its one outcome, computed by the same [put_user_ids]. *)
Definition getresid_witness (get : Creds -> IdTriple) (rp ep sp : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match put_user_ids (in_wmem i) (getresid_puts (get (m_creds m)) rp ep sp) with
  | None => Unmodeled
  | Some (r, ws) => Ok (mkEffect r ws []) m []
  end.

Lemma getresid_witness_ok : forall get rp ep sp i m,
  getresid_spec get rp ep sp i m (getresid_witness get rp ep sp i m).
Proof.
  intros. unfold getresid_spec, getresid_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (put_user_ids (in_wmem i) (getresid_puts (get (m_creds m)) rp ep sp))
    as [[r ws]|]; [apply pure_ok|apply unmodeled_intro].
Qed.

(** [setuid]/[setgid]: -EINVAL for [(uid_t)-1], and otherwise the
    -ENOMEM every other branch admits — [prepare_creds] can fail on all
    three of them, so one witness covers the whole spec without deciding
    which branch the credentials take. *)
Definition setid_witness (v : word) (m : Model) : outcome SyscallEffect :=
  if bv_eqb v ID_MINUS_ONE then ret_outcome (errno_ret EINVAL) m
  else ret_outcome (errno_ret ENOMEM) m.

Lemma setid_witness_ok : forall get put user v i m,
  setid_spec get put user v i m (setid_witness v m).
Proof.
  intros. unfold setid_spec, setid_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  repeat match goal with
         | |- context [ if ?b then _ else _ ] => destruct b eqn:?; cbv beta iota zeta
         end;
  first [ apply pure_ok
        | apply alt_l;
          (eapply bind_step;
            [ apply errno_from_witness; apply In_ENOMEM_setid_errnos
            | apply pure_ok ]) ].
Qed.

(** [setresuid]/[setresgid]: the no-op fast path and the -EPERM refusal
    are both total, and every remaining branch admits -ENOMEM, so the
    witness has to follow the spec's first two tests and can stop
    there. *)
Definition setresid_witness (get : Creds -> IdTriple) (r e s : word) (m : Model)
    : outcome SyscallEffect :=
  let t := get (m_creds m) in
  let pick (a : word) (cur : word) := if bv_eqb a ID_MINUS_ONE then cur else a in
  let nr := pick r (id_real t) in
  let ne := pick e (id_eff t) in
  let ns := pick s (id_saved t) in
  if andb (andb (bv_eqb nr (id_real t)) (bv_eqb ne (id_eff t)))
          (bv_eqb ns (id_saved t)) then
    ret_outcome (Z_to_bv 64 0) m
  else
    let is_old (x : word) :=
      orb (orb (bv_eqb x (id_real t)) (bv_eqb x (id_eff t))) (bv_eqb x (id_saved t)) in
    if andb (negb (andb (andb (is_old nr) (is_old ne)) (is_old ns)))
            (negb (creds_privileged (m_creds m))) then
      ret_outcome (errno_ret EPERM) m
    else
      ret_outcome (errno_ret ENOMEM) m.

Lemma setresid_witness_ok : forall get put user r e s i m,
  setresid_spec get put user r e s i m (setresid_witness get r e s m).
Proof.
  intros. unfold setresid_spec, setresid_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  repeat match goal with
         | |- context [ if ?b then _ else _ ] => destruct b eqn:?; cbv beta iota zeta
         end;
  first [ apply pure_ok
        | apply alt_l;
          (eapply bind_step;
            [ apply errno_from_witness; apply In_ENOMEM_setid_errnos
            | apply pure_ok ]) ].
Qed.

(** prctl witness: the arm's own answer.  [Kernel.Sys.prctl_spec] has no
    [choose] and one [alt], [PR_CAPBSET_READ]'s 0 or 1 for a capability
    outside [capbset_assumed]; the witness takes its 1, the answer the
    arm gives every valid capability.  An option outside
    [prctl_modeled_options] declines, and each of the five answers by a
    test on its arguments alone ([i] supplies a2..a4 for
    [PR_SET_NO_NEW_PRIVS]), on the stored parent-death signal and on
    [i]'s writable memory ([PR_GET_PDEATHSIG]), so otherwise the witness
    is the spec with the monad erased: [PR_SET_PDEATHSIG] stores its
    argument, and [PR_GET_PDEATHSIG]'s store is [put_user_ids]'s. *)
Definition prctl_witness (i : SyscallInput) (option_ arg2 : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (existsb (Z.eqb (bv_unsigned option_)) prctl_modeled_options)
  then Unmodeled
  else if Z.eqb (bv_unsigned option_) PR_CAPBSET_READ then
    (if (CAP_LAST_CAP <? bv_unsigned arg2)%Z
     then ret_outcome (errno_ret EINVAL) m
     else ret_outcome (Z_to_bv 64 1) m)
  else if Z.eqb (bv_unsigned option_) PR_SET_PDEATHSIG then
    (if (64 <? bv_unsigned arg2)%Z
     then ret_outcome (errno_ret EINVAL) m
     else ret_outcome (Z_to_bv 64 0) (with_pdeath_signal arg2 m))
  else if Z.eqb (bv_unsigned option_) PR_GET_PDEATHSIG then
    (match put_user_ids (in_wmem i) [(arg2, m_pdeath_signal m)] with
     | None => Unmodeled
     | Some (r, ws) => Ok (mkEffect r ws []) m []
     end)
  else if Z.eqb (bv_unsigned option_) PR_SET_DUMPABLE then
    (if (1 <? bv_unsigned arg2)%Z
     then ret_outcome (errno_ret EINVAL) m
     else ret_outcome (Z_to_bv 64 0) m)
  else if Z.eqb (bv_unsigned option_) PR_SET_NO_NEW_PRIVS then
    (if (bv_eqb arg2 (Z_to_bv 64 1) && w_is0 (in_arg i 2)
         && w_is0 (in_arg i 3) && w_is0 (in_arg i 4))%bool
     then ret_outcome (Z_to_bv 64 0) m
     else ret_outcome (errno_ret EINVAL) m)
  else Unmodeled.

Lemma prctl_witness_ok : forall i option_ arg2 m,
  prctl_spec option_ arg2 i m (prctl_witness i option_ arg2 m).
Proof.
  intros i option_ arg2 m. unfold prctl_spec, prctl_witness.
  destruct (negb (existsb (Z.eqb (bv_unsigned option_)) prctl_modeled_options));
    [apply unmodeled_intro|].
  destruct (Z.eqb (bv_unsigned option_) PR_CAPBSET_READ).
  { destruct ((CAP_LAST_CAP <? bv_unsigned arg2)%Z); [apply pure_ok|].
    destruct (capbset_assumed (bv_unsigned arg2));
      [apply pure_ok | apply alt_r; apply pure_ok]. }
  destruct (Z.eqb (bv_unsigned option_) PR_SET_PDEATHSIG).
  { destruct ((64 <? bv_unsigned arg2)%Z); [apply pure_ok|].
    eapply bind_step; [apply modify_ok|]. apply pure_ok. }
  destruct (Z.eqb (bv_unsigned option_) PR_GET_PDEATHSIG).
  { eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|]. cbv beta.
    destruct (put_user_ids (in_wmem i) [(arg2, m_pdeath_signal m)])
      as [[r ws]|]; [apply pure_ok|apply unmodeled_intro]. }
  destruct (Z.eqb (bv_unsigned option_) PR_SET_DUMPABLE).
  { destruct ((1 <? bv_unsigned arg2)%Z); apply pure_ok. }
  destruct (Z.eqb (bv_unsigned option_) PR_SET_NO_NEW_PRIVS);
    [|apply unmodeled_intro].
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (bv_eqb arg2 (Z_to_bv 64 1) && w_is0 (in_arg i 2)
            && w_is0 (in_arg i 3) && w_is0 (in_arg i 4))%bool;
    apply pure_ok.
Qed.
