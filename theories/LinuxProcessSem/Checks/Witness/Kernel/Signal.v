(** * LinuxProcessSem.Checks.Witness.Kernel.Signal — the rt_sigaction (134) and rt_sigprocmask (135) witnesses, and their proofs

    Mirrors [Sys/Kernel/Signal.v], which answers to Linux
    [kernel/signal.c]: this file holds the witnesses for the syscalls
    defined there, and no others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

(** The spec is deterministic — no [choose], no [alt] — so the witness is
    its arm structure read as a function. *)
Definition sigaltstack_witness (uss uoss : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if m_sigaltstack_installed m then Unmodeled
  else if negb (w_is0 uoss) then Unmodeled
  else if w_is0 uss then ret_outcome (Z_to_bv 64 0) m
  else
    match sigaltstack_at (in_mem i) uss with
    | None => ret_outcome (errno_ret EFAULT) m
    | Some bs =>
        if negb (ss_mode_ok (ss_flags_of bs))
        then ret_outcome (errno_ret EINVAL) m
        else if ss_disabling (ss_flags_of bs)
        then ret_outcome (Z_to_bv 64 0) m
        else if (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs))%bool
        then Unmodeled
        else if (bv_unsigned (ss_size_of bs) <? MINSIGSTKSZ)%Z
        then ret_outcome (errno_ret ENOMEM) m
        else ret_outcome (Z_to_bv 64 0) (with_sigaltstack_installed m)
    end.

Lemma sigaltstack_witness_ok : forall uss uoss i m,
  sigaltstack_spec uss uoss i m (sigaltstack_witness uss uoss i m).
Proof.
  intros. unfold sigaltstack_spec, sigaltstack_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (m_sigaltstack_installed m) eqn:Hw; cbv beta iota.
  { apply unmodeled_intro. }
  destruct (negb (w_is0 uoss)) eqn:Ho; cbv beta iota.
  { apply unmodeled_intro. }
  destruct (w_is0 uss) eqn:Hu; cbv beta iota.
  { unfold ret_only, ret_outcome. apply pure_ok. }
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (sigaltstack_at (in_mem i) uss) as [bs|] eqn:Hbs; cbv beta iota.
  2:{ unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (negb (ss_mode_ok (ss_flags_of bs))) eqn:Hmode; cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (ss_disabling (ss_flags_of bs)) eqn:Hdis; cbv beta iota.
  { unfold ret_outcome, ret_only. apply pure_ok. }
  destruct (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs))%bool eqn:Hzero;
    cbv beta iota.
  { apply unmodeled_intro. }
  destruct (bv_unsigned (ss_size_of bs) <? MINSIGSTKSZ)%Z eqn:Hsz;
    cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  unfold ret_outcome. eapply bind_step; [apply modify_ok|].
  unfold ret_only. apply pure_ok.
Qed.

Definition rt_sigaction_witness (sig act oact ss : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (bv_eqb ss (Z_to_bv 64 8)) then ret_outcome (errno_ret EINVAL) m
  else if negb (w_is0 oact) then Unmodeled
  else if w_is0 act
  then (if sig_valid sig then ret_outcome (Z_to_bv 64 0) m
        else ret_outcome (errno_ret EINVAL) m)
  else
    match sigaction_flags (in_mem i) act with
    | None => ret_outcome (errno_ret EFAULT) m
    | Some fl =>
        if negb (sig_valid sig) then ret_outcome (errno_ret EINVAL) m
        else if sig_kernel_only sig then ret_outcome (errno_ret EINVAL) m
        else if negb (sa_flags_ok fl) then Unmodeled
        else if sigaction_accepted sig then ret_outcome (Z_to_bv 64 0) m
        else if sigabrt_dfl_install sig (in_mem i) act then ret_outcome (Z_to_bv 64 0) m
        else Unmodeled
    end.

Lemma rt_sigaction_witness_ok : forall sig act oact ss i m,
  rt_sigaction_spec sig act oact ss i m
    (rt_sigaction_witness sig act oact ss i m).
Proof.
  intros. unfold rt_sigaction_spec, rt_sigaction_witness.
  destruct (negb (bv_eqb ss (Z_to_bv 64 8))) eqn:Hss; cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (negb (w_is0 oact)) eqn:Hoact; cbv beta iota.
  { apply unmodeled_intro. }
  destruct (w_is0 act) eqn:Hact; cbv beta iota.
  { destruct (sig_valid sig) eqn:Hv; cbv beta iota;
      unfold err_ret, ret_only, ret_outcome; apply pure_ok. }
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (sigaction_flags (in_mem i) act) as [fl|] eqn:Hfl; cbv beta iota.
  2:{ unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (negb (sig_valid sig)) eqn:Hv; cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (sig_kernel_only sig) eqn:Hk; cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (negb (sa_flags_ok fl)) eqn:Hfo; cbv beta iota.
  { apply unmodeled_intro. }
  destruct (sigaction_accepted sig) eqn:Ha; cbv beta iota.
  { unfold ret_only, ret_outcome. apply pure_ok. }
  destruct (sigabrt_dfl_install sig (in_mem i) act) eqn:Hd; cbv beta iota.
  - unfold ret_only, ret_outcome. apply pure_ok.
  - apply unmodeled_intro.
Qed.

(** The spec is deterministic — no [choose], no [alt] — so the witness
    is the spec's own arm structure read as a function.  The [oset]
    copy-out is factored out the way the spec factors it, so the two
    stay in step arm for arm. *)
Definition write_oset_witness (oset old : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if negb (access_okb oset NSIG_BYTES)
  then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES) with
    | None => Unmodeled
    | Some _ =>
        Ok (mkEffect (Z_to_bv 64 0)
              [(oset, Z_to_le_bytes (Z.to_nat NSIG_BYTES) (bv_unsigned old))]
              []) m []
    end.

Lemma write_oset_witness_ok : forall oset old i m,
  write_oset oset old i m (write_oset_witness oset old i m).
Proof.
  intros. unfold write_oset, write_oset_witness.
  destruct (negb (access_okb oset NSIG_BYTES)) eqn:Ha; cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES)) eqn:Hw;
    cbv beta iota.
  - apply pure_ok.
  - apply unmodeled_intro.
Qed.

Definition rt_sigprocmask_witness (how nset oset ss : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))
  then ret_outcome (errno_ret EINVAL) m
  else
    let old := m_sigmask m in
    if w_is0 nset
    then (if w_is0 oset then ret_outcome (Z_to_bv 64 0) m
          else write_oset_witness oset old i m)
    else
      match sigset_at (in_mem i) nset with
      | None => ret_outcome (errno_ret EFAULT) m
      | Some raw =>
          outcome_copyins [(nset, Z.to_nat NSIG_BYTES)]
          (if negb (how_valid how) then ret_outcome (errno_ret EINVAL) m
           else
             let m' := sigmask_deliver_model
                         (sigmask_apply how old (sigmask_strip raw)) m in
             if w_is0 oset then ret_outcome (Z_to_bv 64 0) m'
             else write_oset_witness oset old i m')
      end.

Lemma rt_sigprocmask_witness_ok : forall how nset oset ss i m,
  rt_sigprocmask_spec how nset oset ss i m
    (rt_sigprocmask_witness how nset oset ss i m).
Proof.
  intros. unfold rt_sigprocmask_spec, rt_sigprocmask_witness.
  destruct (negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))) eqn:Hss; cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
  destruct (w_is0 nset) eqn:Hn; cbv beta iota.
  { destruct (w_is0 oset) eqn:Ho; cbv beta iota.
    - unfold ret_only, ret_outcome. apply pure_ok.
    - apply write_oset_witness_ok. }
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (sigset_at (in_mem i) nset) as [raw|] eqn:Hr; cbv beta iota.
  2:{ unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  apply record_copyins_outcome.
  destruct (negb (how_valid how)) eqn:Hh; cbv beta iota zeta.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  eapply bind_step; [apply modify_ok|]. cbv beta.
  destruct (w_is0 oset) eqn:Ho; cbv beta iota.
  - unfold ret_only, ret_outcome. apply pure_ok.
  - apply write_oset_witness_ok.
Qed.

(* =========================================================================
   tkill (130) and tgkill (131)
   ========================================================================= *)

(** The witness follows the spec's own branch structure, including the
    declaration gate at the head: with the declaration off every shape is
    [Unmodeled], which is the witness the dispatcher's progress theorem
    wants for a number the model declines. *)
Definition send_sigabrt_witness (m : Model) : outcome SyscallEffect :=
  if sigabrt_blocked (m_sigmask m)
  then ret_outcome (Z_to_bv 64 0) (with_sigabrt_pending m)
  else ret_outcome (Z_to_bv 64 0) (with_killed (Z_to_bv 64 SIGABRT) m).

Lemma send_sigabrt_witness_ok : forall i m,
  send_sigabrt i m (send_sigabrt_witness m).
Proof.
  intros i m. unfold send_sigabrt, send_sigabrt_witness.
  rewrite bind_get_model.
  destruct (sigabrt_blocked (m_sigmask m)) eqn:Hb; cbv beta iota;
    (eapply bind_step;
     [ unfold set_sigabrt_pending, set_killed; apply modify_ok
     | cbv beta; unfold ret_only, ret_outcome; apply pure_ok ]).
Qed.

Definition tkill_self_witness (pid sig : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (m_abort_terminal m) then Unmodeled
  else
    match m_tid m with
    | None => Unmodeled
    | Some t =>
        if negb (bv_eqb pid t) then Unmodeled
        else if negb (tkill_sig_valid sig) then ret_outcome (errno_ret EINVAL) m
        else if bv_eqb sig (Z_to_bv 64 SIGABRT) then send_sigabrt_witness m
        else Unmodeled
    end.

Lemma tkill_self_witness_ok : forall pid sig i m,
  tkill_self pid sig i m (tkill_self_witness pid sig m).
Proof.
  intros pid sig i m. unfold tkill_self, tkill_self_witness.
  rewrite bind_get_model.
  destruct (negb (m_abort_terminal m)); cbv beta iota; [apply unmodeled_intro|].
  destruct (m_tid m) as [t|]; cbv beta iota; [|apply unmodeled_intro].
  destruct (negb (bv_eqb pid t)); cbv beta iota; [apply unmodeled_intro|].
  destruct (negb (tkill_sig_valid sig)); cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (bv_eqb sig (Z_to_bv 64 SIGABRT)); cbv beta iota;
    [apply send_sigabrt_witness_ok | apply unmodeled_intro].
Qed.

Definition tkill_witness (pid sig : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (m_abort_terminal m) then Unmodeled
  else if negb (pid_positive pid) then ret_outcome (errno_ret EINVAL) m
  else tkill_self_witness pid sig m.

Lemma tkill_witness_ok : forall pid sig i m,
  tkill_spec pid sig i m (tkill_witness pid sig m).
Proof.
  intros pid sig i m. unfold tkill_spec, tkill_witness.
  rewrite bind_get_model.
  destruct (negb (m_abort_terminal m)); cbv beta iota; [apply unmodeled_intro|].
  destruct (negb (pid_positive pid)); cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  apply tkill_self_witness_ok.
Qed.

Definition tgkill_witness (tgid pid sig : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (m_abort_terminal m) then Unmodeled
  else if negb (pid_positive pid && pid_positive tgid)%bool
  then ret_outcome (errno_ret EINVAL) m
  else
    match m_tid m with
    | None => Unmodeled
    | Some t =>
        if negb (bv_eqb pid t) then Unmodeled
        else if negb (bv_eqb tgid t) then ret_outcome (errno_ret ESRCH) m
        else tkill_self_witness pid sig m
    end.

Lemma tgkill_witness_ok : forall tgid pid sig i m,
  tgkill_spec tgid pid sig i m (tgkill_witness tgid pid sig m).
Proof.
  intros tgid pid sig i m. unfold tgkill_spec, tgkill_witness.
  rewrite bind_get_model.
  destruct (negb (m_abort_terminal m)); cbv beta iota; [apply unmodeled_intro|].
  destruct (negb (pid_positive pid && pid_positive tgid)%bool); cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (m_tid m) as [t|]; cbv beta iota; [|apply unmodeled_intro].
  destruct (negb (bv_eqb pid t)); cbv beta iota; [apply unmodeled_intro|].
  destruct (negb (bv_eqb tgid t)); cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  apply tkill_self_witness_ok.
Qed.
