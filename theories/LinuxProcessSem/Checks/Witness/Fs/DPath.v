(** * LinuxProcessSem.Checks.Witness.Fs.DPath — the getcwd (17) witness, and its proof

    Mirrors [Sys/Fs/DPath.v], which answers to Linux [fs/d_path.c]: this
    file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export Prelude.

(** The witness takes the INJECTED -ENOMEM on every branch that has
    one.  It is the single answer available under all four of them, so
    the witness needs no case analysis on the working directory, the
    size or the destination; the deterministic answers beside it are
    exhibited by [Checks.Cases.Fs.DPath] instead, where they can be
    computed against a literal model.

    Where the destination faults mid-copy the spec declines outright,
    and failing closed is itself the admissible outcome. *)
Definition getcwd_witness (i : SyscallInput) (buf size : word) (m : Model)
    : outcome SyscallEffect :=
  let cwd := m_cwd m in
  let bs := getcwd_bytes cwd in
  let len := getcwd_len cwd in
  if Nat.ltb path_max len then ret_outcome (errno_ret ENOMEM) m
  else if (bv_unsigned size <? Z.of_nat len)%Z then
    ret_outcome (errno_ret ENOMEM) m
  else if negb (access_okb buf (Z.of_nat len)) then
    ret_outcome (errno_ret ENOMEM) m
  else
    match read_bytes_map (in_wmem i) buf (len_word bs) with
    | None => Unmodeled
    | Some _ => ret_outcome (errno_ret ENOMEM) m
    end.

Lemma getcwd_inject_enomem : forall (c : Sys SyscallEffect) i m,
  alt (e <- errno_from getcwd_errnos ;; err_ret e) c
      i m (ret_outcome (errno_ret ENOMEM) m).
Proof.
  intros c i m. apply alt_l.
  eapply bind_step; [apply (errno_head_witness ENOMEM [])|].
  unfold err_ret, ret_only, ret_outcome. apply pure_ok.
Qed.

Lemma getcwd_witness_ok : forall i buf size m,
  getcwd_spec buf size i m (getcwd_witness i buf size m).
Proof.
  intros i buf size m. unfold getcwd_spec, getcwd_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
  destruct (Nat.ltb path_max (getcwd_len (m_cwd m))); cbv iota;
    [apply getcwd_inject_enomem|].
  destruct (bv_unsigned size <? Z.of_nat (getcwd_len (m_cwd m)))%Z;
    cbv iota; [apply getcwd_inject_enomem|].
  destruct (negb (access_okb buf (Z.of_nat (getcwd_len (m_cwd m)))));
    cbv iota; [apply getcwd_inject_enomem|].
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (getcwd_bytes (m_cwd m)))); cbv iota;
    [apply getcwd_inject_enomem|apply unmodeled_intro].
Qed.
