(** * LinuxProcessSem.Checks.Sys.Fs.Readdir — the getdents64 (61) checker, and its proofs

    Mirrors [Sys/Fs/Readdir.v], which answers to Linux [fs/readdir.c]:
    this file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.

(** [getdents64] (61): -EBADF on a closed fd, -ENOTDIR on every fd that
    is not a directory, and on a directory fd either -EINVAL or the one
    injectable errno when the buffer cannot hold the smallest possible
    entry.  Every larger buffer on a directory fd is [CheckUnmodeled].
    Mirrors [Fs.Readdir.getdents64_spec] arm for arm — read that spec
    for why the listing itself is declined, and why the [dirent]
    pointer is not an argument here either.

    All the admitted answers are a bare return with FIVE EMPTY LEDGERS:
    the kernel reaches [user_write_access_begin] only after the
    [reclen > ctx->count] test has failed the call, so nothing this spec
    admits writes, zeroes, unmaps or copies a byte.  A kernel that
    claimed a write alongside one of these returns is rejected on the
    ledger rather than on the return value. *)
Definition check_getdents64 (fd count : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdFile _ _)  => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdFileW _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdFileA _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdFileRW _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdPipe _ _)  => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdSocket _)  => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdStream _ _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdDevNull _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some FdUrandom => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some FdDir =>
      if getdents64_no_room count then
        match eff with
        | mkEffectU ret [] [] [] [] [] =>
            if errno_ret_in getdents64_errnos ret then CheckOk m []
            else if bv_eqb ret (errno_ret EINVAL) then CheckOk m []
            else CheckReject
        | _ => CheckReject
        end
      else CheckUnmodeled
  end.

Lemma check_getdents64_sound_ok : forall fd count eff m m' evs i,
  check_getdents64 fd count eff m = CheckOk m' evs ->
  getdents64_spec fd count i m (Ok eff m' evs).
Proof.
  intros fd count eff m m' evs i H.
  unfold check_getdents64 in H. unfold getdents64_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
    (* the -ENOTDIR arms and the -EBADF one are plain returns *)
    try (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
         apply pure_ok).
  (* the directory arm *)
  destruct (getdents64_no_room count) eqn:Hroom; [|discriminate].
  destruct eff as [ret ws zs us cs cis]; destruct ws as [|w ws'];
    [destruct zs as [|z zs']|]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct cis as [|? ?]; try discriminate.
  destruct (errno_ret_in getdents64_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    apply pure_ok.
  - destruct (bv_eqb ret (errno_ret EINVAL)) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq; subst ret.
    apply alt_r. unfold err_ret, ret_only. apply pure_ok.
Qed.

(** The one decline is the directory arm's roomy half — the listing the
    model cannot produce.  Inside the small-buffer half every effect
    shape is either accepted or rejected, never declined, and so is
    every non-directory fd. *)
Lemma check_getdents64_sound_unmodeled : forall fd count eff m i,
  check_getdents64 fd count eff m = CheckUnmodeled ->
  getdents64_spec fd count i m Unmodeled.
Proof.
  intros fd count eff m i H.
  unfold check_getdents64 in H. unfold getdents64_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    try (now apply check_ret_only_no_unmodeled in H).
  eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota; srw Hfd.
  destruct (getdents64_no_room count) eqn:Hroom; [|apply unmodeled_intro].
  exfalso.
  destruct eff as [ret ws zs us cs cis]; destruct ws; [destruct zs|];
    destruct us; destruct cs; destruct cis; try discriminate.
  destruct (errno_ret_in getdents64_errnos ret); [discriminate|].
  destruct (bv_eqb ret (errno_ret EINVAL)); discriminate.
Qed.

Lemma check_getdents64_complete_ok : forall fd count eff m m' evs i,
  getdents64_spec fd count i m (Ok eff m' evs) ->
  check_getdents64 fd count eff m = CheckOk m' evs.
Proof.
  intros fd count eff m m' evs i H.
  unfold getdents64_spec in H. unfold check_getdents64. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    hall Hfd.
  (* THE DIRECTORY ARM (sixth: [State.FdEntry]'s constructors are
     [FdChannel], [FdFile], [FdFileW], [FdFileA], [FdFileRW], [FdDir],
     [FdSocket], [FdPipe], [FdDevNull], [FdUrandom], [FdStream], then
     the closed fd).  THE INDEX MOVES WITH
     THE TYPE: every constructor added ahead of [FdDir] shifts it, and
     the goal this selects is silently a different arm if it is not
     moved with it.  [getdents64_errnos] IS UNFOLDED BEFORE
     [inv_ok] runs, and that is load-bearing rather than tidiness:
     [errno_from]'s [choose] leaves [In e getdents64_errnos] with [e]
     still a variable, [inv_ok] matches [_ \/ _] syntactically and a
     [In] over a constant name is not one, so [e] survives to the
     [vm_compute] below -- which then has to normalize
     [errno_ret e = Z_to_bv 64 (- e)] with a SYMBOLIC [e], including its
     well-formedness proof, and does not come back.  Unfolding the list
     turns the [In] into the disjunction [inv_ok] does see, [e] is
     substituted, and what is left is closed. *)
  6: { destruct (getdents64_no_room count) eqn:Hroom; cbv iota in *;
       unfold getdents64_errnos in *; cbn [In] in *; inv_ok;
       try contradiction; vm_compute; reflexivity. }
  (* the ten plain returns.  Delta is restricted to the acceptor, for
     the same reason: [getdents64_no_room count] is over a variable
     count, and a full-delta [cbn] descends into it. *)
  all: inv_ok; cbn [check_ret_only]; rewrite bv_eqb_refl; reflexivity.
Qed.

Lemma check_getdents64_complete_unmodeled : forall fd count m i eff,
  getdents64_spec fd count i m Unmodeled ->
  check_getdents64 fd count eff m = CheckUnmodeled.
Proof.
  intros fd count m i eff H.
  unfold getdents64_spec in H. unfold check_getdents64. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    hall Hfd.
  all: try (exfalso; inv_ok; discriminate).
  destruct (getdents64_no_room count) eqn:Hroom; cbv iota in *;
    [|reflexivity].
  (* Neither arm of the [alt] can be [Unmodeled]: a [choose] bound to a
     [pure] admits only [Ok]. *)
  exfalso. inv_ok.
Qed.
