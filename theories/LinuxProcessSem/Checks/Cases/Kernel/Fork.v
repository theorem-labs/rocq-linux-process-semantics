(** * LinuxProcessSem.Checks.Cases.Kernel.Fork — worked examples over set_tid_address (96), clone (220) and clone3 (435)

    Mirrors [Sys/Kernel/Fork.v], which answers to Linux [kernel/fork.c]:
    this file holds the worked examples for the syscalls defined there,
    and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ProcessCreation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude Fs.ReadWrite.

Lemma set_tid_address_first_choice_is_within_modeled_envelope :
  forall i m eff m' evs,
  m_tid m = None ->
  set_tid_address_spec i m (Ok eff m' evs) ->
  exists tid,
    (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z /\
    eff = mkEffect tid [] [] /\
    m' = with_tid tid m /\
    evs = [].
Proof.
  intros i m eff m' evs Htid Hspec.
  apply check_set_tid_address_complete_ok in Hspec.
  unfold check_set_tid_address in Hspec.
  destruct eff as [ret ws zs us cs copyins].
  destruct ws as [|w ws]; [|discriminate].
  destruct zs as [|z zs]; [|discriminate].
  destruct us as [|u us]; [|discriminate].
  destruct cs as [|c cs]; [|discriminate].
  destruct copyins as [|copyin copyins]; [|discriminate].
  rewrite Htid in Hspec.
  destruct ((0 <? bv_unsigned ret)%Z &&
            (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:Hvalid;
    [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hvalid as [Hlo Hhi].
  apply Z.ltb_lt in Hlo. apply Z.ltb_lt in Hhi.
  exists ret. repeat split; try reflexivity; assumption.
Qed.

(* =========================================================================
   clone3 (435): THE ARGUMENT BLOCK THAT WALKED OFF THE TOP OF THE
   ADDRESS SPACE

   [Fork.clone3_spec] read its 88-byte [struct clone_args] with
   [State.read_bytes_map] bare, a walk that wraps at 2^64 (see
   [State.copy_bytes_map]'s note), so a [uargs] in the last bytes of the
   address space whose range was backed at both ends was RESOLVED: the
   fields were judged and the call answered with the struct in the
   ledger.  Linux refuses the range before a byte moves:
   [copy_clone_args_from_user] (kernel/fork.c) reads the struct with
   [copy_struct_from_user], whose [copy_from_user] tests [access_ok] in
   [_inline_copy_from_user] (include/linux/uaccess.h).  The arm now asks
   the same through [State.copy_bytes_map] and answers -EFAULT with an
   empty ledger.

   The group is the refusal, the control that the bare walk really would
   have passed — and read a fork-shaped struct — and a neighbour at the
   top of what [State.access_okb] accepts that is still resolved.  The
   memories map exactly their own range.
   ========================================================================= *)

Definition clone3_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

Definition clone3_wrap_uargs : word := Z_to_bv 64 (2 ^ 64 - 8).

(** Eight bytes below the top and eighty from 0: the 88-byte walk covers
    both halves.  Every byte is zero but the one at address 24, which is
    offset 32 of the struct — [exit_signal] — and holds SIGCHLD, so what
    the bare walk reads back is the ONE struct [Fork.clone3_fork_args_b]
    admits. *)
Definition clone3_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 80)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (if bv_eqb a (Z_to_bv 64 24) then Z_to_bv 8 SIGCHLD
                      else Z_to_bv 8 0)
           else None.

Definition clone3_wrap_call : SyscallInput :=
  mkInput 435 [clone3_wrap_uargs; Z_to_bv 64 CLONE_ARGS_SIZE; 0; 0; 0; 0]
    clone3_wrap_mem (fun _ => None).

Example clone3_wrap_would_pass_the_bare_walk :
  read_bytes_map clone3_wrap_mem clone3_wrap_uargs (Z_to_bv 64 CLONE_ARGS_SIZE)
    <> None
  (* ...and what it reads back is the fork-shaped struct *)
  /\ option_map clone3_fork_args_b
       (read_bytes_map clone3_wrap_mem clone3_wrap_uargs
          (Z_to_bv 64 CLONE_ARGS_SIZE))
     = Some true.
Proof. split; vm_compute; [discriminate | reflexivity]. Qed.

Example clone3_wrap_args_are_not_copyable :
  copy_bytes_map clone3_wrap_mem clone3_wrap_uargs CLONE_ARGS_SIZE = None.
Proof. vm_compute. reflexivity. Qed.

(** -EFAULT with an EMPTY ledger is the answer.  The -EAGAIN resolution
    the bare walk reached, with the struct in its ledger, is refused, and
    so is an -EFAULT that claims the struct was read. *)
Example clone3_wrapping_args_is_efault :
  check_syscall clone3_wrap_call (mkEffect (errno_ret EFAULT) [] []) clone3_model
  = CheckOk clone3_model []
  /\ check_syscall clone3_wrap_call
       (mkEffectU (errno_ret EAGAIN) [] [] [] []
                  [(clone3_wrap_uargs, CLONE_ARGS_SIZE_nat)])
       clone3_model
     = CheckReject
  /\ check_syscall clone3_wrap_call
       (mkEffectU (errno_ret EFAULT) [] [] [] []
                  [(clone3_wrap_uargs, CLONE_ARGS_SIZE_nat)])
       clone3_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** THE NEIGHBOUR, and the half that says the arm still works: the last
    88 bytes [State.access_okb] accepts, mapped end to end, holding the
    same fork-shaped struct.  The call is still resolved — the -EAGAIN
    [kernel_clone] can always answer and a pid, each with the 88-byte
    ledger, the pid recording the child — and -EFAULT is refused there. *)
Definition clone3_top_uargs : word := Z_to_bv 64 (TASK_SIZE - CLONE_ARGS_SIZE).

Definition clone3_top_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - CLONE_ARGS_SIZE <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (if bv_eqb a (clone3_top_uargs + Z_to_bv 64 32)
                      then Z_to_bv 8 SIGCHLD else Z_to_bv 8 0)
           else None.

Definition clone3_top_call : SyscallInput :=
  mkInput 435 [clone3_top_uargs; Z_to_bv 64 CLONE_ARGS_SIZE; 0; 0; 0; 0]
    clone3_top_mem (fun _ => None).

Example clone3_at_the_top_still_resolves :
  check_syscall clone3_top_call
    (mkEffectU (errno_ret EAGAIN) [] [] [] []
               [(clone3_top_uargs, CLONE_ARGS_SIZE_nat)])
    clone3_model
  = CheckOk clone3_model []
  /\ check_syscall clone3_top_call
       (mkEffectU (Z_to_bv 64 4242) [] [] [] []
                  [(clone3_top_uargs, CLONE_ARGS_SIZE_nat)])
       clone3_model
     = CheckOk (with_child (Z_to_bv 64 4242) clone3_model) []
  /\ check_syscall clone3_top_call (mkEffect (errno_ret EFAULT) [] []) clone3_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** A range [State.access_okb] ADMITS with nothing behind it is declined,
    not answered -EFAULT: the house rule [Kernel.Sys.prlimit64_spec]'s
    note states, which keeps -EFAULT for the ranges [access_ok] refuses. *)
Example clone3_admitted_but_unbacked_declines :
  check_syscall (mkInput 435 [clone3_top_uargs; Z_to_bv 64 CLONE_ARGS_SIZE;
                              0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) clone3_model
  = CheckUnmodeled.
Proof. check_eq. Qed.

(* -------------------------------------------------------------------------
   clone (220) with namespace flags: the parent's view

   PAIRED TEST.  Before [Kernel.Fork.clone_ns_flags_b], [clone_spec]
   answered the single word SIGCHLD and declined every other, so the
   namespace word below was [CheckUnmodeled].  The case is that word,
   now answered with a pid (the child recorded) or any errno.  The
   controls are words the old text and the new one treat alike: the
   plain fork word answers in both, and a CLONE_VM word declines in
   both.
   ------------------------------------------------------------------------- *)

Definition clone_in (flags : word) : SyscallInput :=
  mkInput 220 [flags; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** No descriptor at all, so [Kernel.Fork.clone_no_shared_file_b] lets
    every call through. *)
Definition clone_case_model : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

(** bubblewrap 0.13.1's flag word: SIGCHLD | CLONE_NEWNS | CLONE_NEWUSER
    | CLONE_NEWPID | CLONE_NEWNET | CLONE_NEWIPC | CLONE_NEWUTS. *)
Definition bwrap_clone_flags : word :=
  Z_to_bv 64 (SIGCHLD + CLONE_NEWNS + CLONE_NEWUSER + CLONE_NEWPID
              + CLONE_NEWNET + CLONE_NEWIPC + CLONE_NEWUTS).

(** The case: a pid, recorded with [with_child]; -EPERM (which is not
    in [Fork.clone_errnos]) and -ENOSPC, with the model unchanged; and
    0, the child's own return, refused. *)
Example clone_namespace_word_answers_a_pid :
  check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
    clone_case_model = CheckOk (with_child (Z_to_bv 64 4242) clone_case_model) []
  /\ check_syscall (clone_in bwrap_clone_flags)
       (mkEffect (errno_ret EPERM) [] []) clone_case_model
       = CheckOk clone_case_model []
  /\ check_syscall (clone_in bwrap_clone_flags)
       (mkEffect (errno_ret 28) [] []) clone_case_model
       = CheckOk clone_case_model []
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect 0 [] [])
       clone_case_model = CheckReject.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** THE PID IS RECORDED, in order.  Each successful clone appends the
    pid it returned to [State.procst_child_pids], so two clones leave
    the two pids oldest first ([copy_process]'s [list_add_tail],
    kernel/fork.c, read at v6.18.44; identical at v6.18.46), and an
    errno answer leaves the list alone.  Before this the success branch
    set only the child bit and the list stayed [].  THE CONTROL is the
    errno answer, which leaves the model unchanged in both texts. *)
Example clone_records_the_pid :
  let m1 := with_child (Z_to_bv 64 4242) clone_case_model in
  m_child_pids m1 = [Z_to_bv 64 4242]
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4243 [] []) m1
     = CheckOk (with_child (Z_to_bv 64 4243) m1) []
  /\ m_child_pids (with_child (Z_to_bv 64 4243) m1)
     = [Z_to_bv 64 4242; Z_to_bv 64 4243]
  (* the control *)
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect (errno_ret EPERM) [] [])
       m1 = CheckOk m1 [].
Proof. cbv zeta. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** The controls.  [clone(SIGCHLD)] answers a pid in both texts, and
    keeps its four errnos (-EPERM is not one of them); [clone(CLONE_VM
    | SIGCHLD)] declines in both, and so does the namespace word with
    CLONE_VM added, and a namespace bit without SIGCHLD. *)
Example clone_controls_fork_word_and_clone_vm :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
    clone_case_model = CheckOk (with_child (Z_to_bv 64 4242) clone_case_model) []
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD))
       (mkEffect (errno_ret EPERM) [] []) clone_case_model = CheckReject
  /\ check_syscall (clone_in (Z_to_bv 64 (CLONE_VM + SIGCHLD)))
       (mkEffect 4242 [] []) clone_case_model = CheckUnmodeled
  /\ check_syscall (clone_in (bwrap_clone_flags + Z_to_bv 64 CLONE_VM))
       (mkEffect 4242 [] []) clone_case_model = CheckUnmodeled
  /\ check_syscall (clone_in (Z_to_bv 64 CLONE_NEWUSER))
       (mkEffect 4242 [] []) clone_case_model = CheckUnmodeled.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** The descriptor gate is the fork word's: a regular file open declines
    the namespace word too. *)
Example clone_namespace_word_keeps_the_descriptor_gate :
  check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
    (with_fds [(3, FdFile [] 0)] clone_case_model) = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** THE GATE PASSES FOUR OF THE SEVEN OPAQUE KINDS, for both words, end
    to end: [OProcPath], [OProcFile], [OEventFd] and [ONsFile].
    [clone_opaque_model] is the table bubblewrap's parent holds at its
    clone (channels 0-2, the O_PATH descriptor on "/proc" at fd 3, its
    two eventfds at 4 and 5), and [clone_all_opaque_model] adds the
    modeled [overflowuid] sysctl file and a namespace and mount model
    descriptor.  Before [State.FdOpaque] the model held none of these,
    so it could not reach this clone at all.  THE CONTROL is
    [clone_namespace_word_keeps_the_descriptor_gate] above: a regular
    file still declines both words.  Two other kinds decline
    ([clone_declines_procfd_dir_and_signalfd] below).  An inherited
    file passes when it holds no offset, and with a live one either
    word takes its offset from the caller
    ([Checks.Cases.Fs.Inherited]). *)
Definition clone_opaque_model : Model :=
  with_fds [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
            (3, FdOpaque (OProcPath proc_root_path));
            (4, FdOpaque (OEventFd (Z_to_bv 64 0x80800)));
            (5, FdOpaque (OEventFd (Z_to_bv 64 0x80000)))] clone_case_model.

Definition clone_all_opaque_model : Model :=
  with_fds (fd_insert (fd_insert (m_fds clone_opaque_model) 6
                         (FdOpaque (OProcFile proc_sys_overflowuid_path)))
                      7 (FdOpaque (ONsFile 7))) clone_opaque_model.

Example clone_passes_the_opaque_kinds :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
    clone_opaque_model = CheckOk (with_child (Z_to_bv 64 4242) clone_opaque_model) []
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
       clone_opaque_model = CheckOk (with_child (Z_to_bv 64 4242) clone_opaque_model) []
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
       clone_all_opaque_model = CheckOk (with_child (Z_to_bv 64 4242) clone_all_opaque_model) []
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
       clone_all_opaque_model = CheckOk (with_child (Z_to_bv 64 4242) clone_all_opaque_model) []
  (* the namespace word's errno: any but -EINTR *)
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect (errno_ret EPERM) [] [])
       clone_opaque_model = CheckOk clone_opaque_model []
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect (errno_ret EINTR) [] [])
       clone_opaque_model = CheckReject.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** TWO OTHER OPAQUE KINDS DECLINE, for both words: the
    /proc/self/fd directory ([State.OProcFdDir]), whose [f_pos] the
    child would share while the model holds it in the parent's entry,
    and a signalfd ([State.OSignalFd]), whose mask either process may
    change ([Sys.Kernel.Fork] gives each reason).  Each is added to
    [clone_opaque_model].  THE CONTROL is [clone_passes_the_opaque_kinds]
    above, which the text before the gate's two declining arms answers
    the same way. *)
Definition clone_procfd_model : Model :=
  with_fds (fd_insert (m_fds clone_opaque_model) 6
              (FdOpaque (OProcFdDir (Z_to_bv 64 0x98900) (Some (Z_to_bv 64 0)))))
    clone_opaque_model.

Definition clone_signalfd_model : Model :=
  with_fds (fd_insert (m_fds clone_opaque_model) 6
              (FdOpaque (OSignalFd (Z_to_bv 64 0x10000) (Z_to_bv 64 0x80800))))
    clone_opaque_model.

Example clone_declines_procfd_dir_and_signalfd :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
    clone_procfd_model = CheckUnmodeled
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
       clone_procfd_model = CheckUnmodeled
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
       clone_signalfd_model = CheckUnmodeled
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
       clone_signalfd_model = CheckUnmodeled.
Proof. repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity. Qed.

(* -------------------------------------------------------------------------
   clone (220) and clone3 (435): the argument-only -EINVAL checks

   PAIRED TEST.  Before [Kernel.Fork.clone_arg_checks] every word but the
   fork word and the namespace word declined, so each refused word below
   was [CheckUnmodeled].  The cases are those words, now answered -EINVAL
   and nothing else (kernel/fork.c, Linux v6.18.46).  The controls are
   words the old text and the new one treat alike: a thread word no check
   refuses declines in both, and so does a word with a bit above 31.
   ------------------------------------------------------------------------- *)

(** The -EINVAL a refused word answers: the one admitted outcome. *)
Definition einval_eff : SyscallEffect := mkEffect (errno_ret EINVAL) [] [].

(** A refused [clone] word answers -EINVAL with the model as it was;
    the fork word's -EAGAIN and a pid are refused for it. *)
Definition clone_einval_only (flags : Z) : Prop :=
  check_syscall (clone_in (Z_to_bv 64 flags)) einval_eff clone_case_model
    = CheckOk clone_case_model []
  /\ check_syscall (clone_in (Z_to_bv 64 flags)) (mkEffect (errno_ret EAGAIN) [] [])
       clone_case_model = CheckReject
  /\ check_syscall (clone_in (Z_to_bv 64 flags)) (mkEffect 4242 [] [])
       clone_case_model = CheckReject.

(** SIGCHLD with CLONE_SIGHAND: C4, fork.c:1969-1970. *)
Example clone_sighand_without_vm_einval :
  clone_einval_only (SIGCHLD + CLONE_SIGHAND)%Z.
Proof. unfold clone_einval_only. repeat split; check_eq. Qed.

(** SIGCHLD with CLONE_THREAD: C3, fork.c:1961-1962. *)
Example clone_thread_without_sighand_einval :
  clone_einval_only (SIGCHLD + CLONE_THREAD)%Z.
Proof. unfold clone_einval_only. repeat split; check_eq. Qed.

(** CLONE_NEWNS with CLONE_FS: C1, fork.c:1951-1952. *)
Example clone_newns_with_fs_einval :
  clone_einval_only (SIGCHLD + CLONE_NEWNS + CLONE_FS)%Z.
Proof. unfold clone_einval_only. repeat split; check_eq. Qed.

(** CLONE_NEWUSER with CLONE_FS: C2, fork.c:1954-1955. *)
Example clone_newuser_with_fs_einval :
  clone_einval_only (SIGCHLD + CLONE_NEWUSER + CLONE_FS)%Z.
Proof. unfold clone_einval_only. repeat split; check_eq. Qed.

(** CLONE_PIDFD with CLONE_PARENT_SETTID: K0, fork.c:2588-2591.
    Legacy [clone] passes a2 as both pointers (2744, 2746), whatever a2
    holds. *)
Example clone_pidfd_with_parent_settid_einval :
  clone_einval_only (SIGCHLD + CLONE_PIDFD + CLONE_PARENT_SETTID)%Z
  /\ check_syscall (mkInput 220 [Z_to_bv 64 (SIGCHLD + CLONE_PIDFD + CLONE_PARENT_SETTID);
                                0; Z_to_bv 64 0x2000; 0; Z_to_bv 64 0x3000; 0]
                      (fun _ => None) (fun _ => None))
       einval_eff clone_case_model = CheckOk clone_case_model [].
Proof. unfold clone_einval_only. repeat split; check_eq. Qed.

(** CLONE_PIDFD with CLONE_DETACHED: C7, fork.c:1992-1999. *)
Example clone_pidfd_with_detached_einval :
  clone_einval_only (SIGCHLD + CLONE_PIDFD + CLONE_DETACHED)%Z.
Proof. unfold clone_einval_only. repeat split; check_eq. Qed.

(** CLONE_VM, CLONE_SIGHAND and CLONE_THREAD with CLONE_NEWPID: C6a,
    fork.c:1986-1987. *)
Example clone_thread_with_newpid_einval :
  clone_einval_only (CLONE_VM + CLONE_SIGHAND + CLONE_THREAD + CLONE_NEWPID)%Z.
Proof. unfold clone_einval_only. repeat split; check_eq. Qed.

(** CLONE_PARENT with CLONE_SIGHAND and no CLONE_VM: C4 refuses it,
    whatever C5 (CLONE_PARENT from an unkillable group) would say. *)
Example clone_parent_sighand_einval :
  clone_einval_only (SIGCHLD + CLONE_PARENT + CLONE_SIGHAND)%Z.
Proof. unfold clone_einval_only. repeat split; check_eq. Qed.

(** The controls: CLONE_VM, CLONE_SIGHAND and CLONE_THREAD alone
    pass every check and decline; CLONE_PARENT alone, which only C5 could
    refuse, declines; and a0 = 0x1_00000811, SIGCHLD with
    CLONE_SIGHAND and bit 32 set, declines: the raw-input guard. *)
Example clone_unrefused_words_decline :
  check_syscall (clone_in (Z_to_bv 64 (CLONE_VM + CLONE_SIGHAND + CLONE_THREAD)))
    einval_eff clone_case_model = CheckUnmodeled
  /\ check_syscall (clone_in (Z_to_bv 64 (SIGCHLD + CLONE_PARENT)))
       einval_eff clone_case_model = CheckUnmodeled
  /\ check_syscall (clone_in (Z_to_bv 64 0x100000811))
       einval_eff clone_case_model = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.

(** The restated statements at one word each:
    [Checks.ProcessCreation.clone_arg_checks_einval] at SIGCHLD with
    CLONE_SIGHAND, and [Checks.ProcessCreation.clone_sharing_flags_unmodeled]
    at CLONE_VM, CLONE_SIGHAND and CLONE_THREAD. *)
Example clone_restated_statements_at_one_word :
  (forall o, clone_spec (Z_to_bv 64 (SIGCHLD + CLONE_SIGHAND))
               (clone_in (Z_to_bv 64 (SIGCHLD + CLONE_SIGHAND))) clone_case_model o
             <-> o = Ok einval_eff clone_case_model [])
  /\ clone_spec (Z_to_bv 64 (CLONE_VM + CLONE_SIGHAND + CLONE_THREAD))
       (clone_in (Z_to_bv 64 (CLONE_VM + CLONE_SIGHAND + CLONE_THREAD)))
       clone_case_model Unmodeled.
Proof.
  split.
  - intros o.
    apply (ProcessCreation.clone_arg_checks_einval _ _ _
             (mkCloneArgs CLONE_SIGHAND SIGCHLD (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0)));
      check_eq.
  - apply (ProcessCreation.clone_sharing_flags_unmodeled _ _ _
             (mkCloneArgs (CLONE_VM + CLONE_SIGHAND + CLONE_THREAD)%Z 0%Z (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)));
      [check_eq | check_eq | intro Hc; vm_compute in Hc; discriminate Hc].
Qed.

(** THE DESCRIPTOR GATE, a deliberate narrowing against Linux
    ([Kernel.Fork.clone_einval]): with a regular file open, a refused
    [clone] word declines, as [clone_open_file_unmodeled] says for every
    word.  [clone3] has no such gate (below). *)
Example clone_einval_keeps_the_descriptor_gate :
  check_syscall (clone_in (Z_to_bv 64 (SIGCHLD + CLONE_SIGHAND))) einval_eff
    (with_fds [(3, FdFile [] 0)] clone_case_model) = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** A [struct clone_args] image of eleven fields at [clone3_args_base]. *)
Definition clone3_args_base : word := Z_to_bv 64 0x1000.

Definition clone3_args_mem (fields : list Z) : word -> option byte :=
  let bs := flat_map (Z_to_le_bytes 8) fields in
  fun a => let off := (bv_unsigned a - 0x1000)%Z in
           if ((0 <=? off)%Z && (off <? CLONE_ARGS_SIZE)%Z)%bool
           then nth_error bs (Z.to_nat off) else None.

Definition clone3_args_call (fields : list Z) : SyscallInput :=
  mkInput 435 [clone3_args_base; Z_to_bv 64 CLONE_ARGS_SIZE; 0; 0; 0; 0]
    (clone3_args_mem fields) (fun _ => None).

(** [clone3]'s -EINVAL carries the struct in its ledger. *)
Definition clone3_einval_eff : SyscallEffect :=
  mkEffectU (errno_ret EINVAL) [] [] [] []
    [(clone3_args_base, CLONE_ARGS_SIZE_nat)].

(** clone3, CLONE_PIDFD with CLONE_PARENT_SETTID at two different
    pointers: not K0, and the word declines (the model does not answer
    CLONE_PIDFD).  The control: the same two at ONE pointer is K0,
    -EINVAL with the ledger, and an -EINVAL without the ledger is refused.
    Fields: flags, pidfd, child_tid, parent_tid, exit_signal, stack,
    stack_size, tls, set_tid, set_tid_size, cgroup. *)
Example clone3_pidfd_parent_settid_two_pointers :
  check_syscall
    (clone3_args_call [(CLONE_PIDFD + CLONE_PARENT_SETTID)%Z; (0x2000)%Z; 0%Z; (0x3000)%Z; (SIGCHLD)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z])
    clone3_einval_eff clone3_model = CheckUnmodeled
  /\ check_syscall
       (clone3_args_call [(CLONE_PIDFD + CLONE_PARENT_SETTID)%Z; (0x2000)%Z; 0%Z; (0x2000)%Z; (SIGCHLD)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z])
       clone3_einval_eff clone3_model = CheckOk clone3_model []
  /\ check_syscall
       (clone3_args_call [(CLONE_PIDFD + CLONE_PARENT_SETTID)%Z; (0x2000)%Z; 0%Z; (0x2000)%Z; (SIGCHLD)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z])
       einval_eff clone3_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(** [clone3] answers the copy_process checks and its own: SIGCHLD with
    CLONE_SIGHAND (C4), an exit signal of 65 (fork.c:2794-2796), and
    CLONE_THREAD with CLONE_SIGHAND, CLONE_VM and a non-zero exit signal
    (fork.c:2871-2873); and with a regular file open, unlike [clone]. *)
Example clone3_einval_words :
  check_syscall (clone3_args_call [(CLONE_SIGHAND)%Z; 0%Z; 0%Z; 0%Z; (SIGCHLD)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z])
    clone3_einval_eff clone3_model = CheckOk clone3_model []
  /\ check_syscall (clone3_args_call [0%Z; 0%Z; 0%Z; 0%Z; 65%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z])
       clone3_einval_eff clone3_model = CheckOk clone3_model []
  /\ check_syscall
       (clone3_args_call [(CLONE_VM + CLONE_SIGHAND + CLONE_THREAD)%Z; 0%Z; 0%Z; 0%Z; (SIGCHLD)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z])
       clone3_einval_eff clone3_model = CheckOk clone3_model []
  /\ check_syscall (clone3_args_call [(CLONE_SIGHAND)%Z; 0%Z; 0%Z; 0%Z; (SIGCHLD)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z])
       clone3_einval_eff (with_fds [(3, FdFile [] 0)] clone3_model)
     = CheckOk (with_fds [(3, FdFile [] 0)] clone3_model) [].
Proof. repeat split; check_eq. Qed.

(** clone3 with CLONE_NEWTIME and exit signal 17: declines, and the
    struct gives no record, so no reader ever sees the merged word 145
    (0x80 | 17) that would read as exit signal 145 (fork.c:2864-2865).
    The control: the fork image still resolves. *)
Example clone3_newtime_declines :
  check_syscall (clone3_args_call [(CLONE_NEWTIME)%Z; 0%Z; 0%Z; 0%Z; (SIGCHLD)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z])
    clone3_einval_eff clone3_model = CheckUnmodeled
  /\ option_map clone3_pre
       (copy_bytes_map (clone3_args_mem [(CLONE_NEWTIME)%Z; 0%Z; 0%Z; 0%Z; (SIGCHLD)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z])
          clone3_args_base CLONE_ARGS_SIZE) = Some CdDecline
  /\ check_syscall (clone3_args_call [0%Z; 0%Z; 0%Z; 0%Z; (SIGCHLD)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z])
       (mkEffectU (errno_ret EAGAIN) [] [] [] [] [(clone3_args_base, CLONE_ARGS_SIZE_nat)])
       clone3_model = CheckOk clone3_model [].
Proof. repeat split; check_eq. Qed.

(** AN AF_UNIX SEQUENCED-PACKET END DECLINES THE CLONE
    ([State.FdSeqpacket]; [Kernel.Fork.clone_no_shared_file_b]): the
    child's second reference names the same socket, so a close in one
    process would no longer release it, and [State.seq_peer], which reads
    the peer off this process's table, would answer "closed" while the
    other process still holds it.  [clone_seqpacket_model] holds the three
    channels and the two ends and nothing else, so the ends are the only
    entries that can make the gate refuse.  THE CONTROL: the same three
    channels without the ends are admitted. *)
Definition clone_seqpacket_model : Model :=
  with_fds [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
            (3, FdSeqpacket 0 false seq_fresh);
            (4, FdSeqpacket 0 true seq_fresh)] clone_case_model.

Definition clone_channels_model : Model :=
  with_fds [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2)] clone_case_model.

Example clone_with_a_seqpacket_end_open_declines :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
    clone_seqpacket_model = CheckUnmodeled
  /\ clone_no_shared_file_b [(0, FdChannel 0); (3, FdSeqpacket 0 false seq_fresh)]
     = false
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
       clone_channels_model
     = CheckOk (with_child (Z_to_bv 64 4242) clone_channels_model) [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(* -------------------------------------------------------------------------
   clone (220) and clone3 (435): CLONE_SYSVSEM and the four tid bits,
   without CLONE_VM

   PAIRED TEST.  Before [Kernel.Fork.clone_class] every word below
   declined, but for the [clone3] row with stack 0 and stack_size 8, a
   control that answers -EINVAL before and after.  Each other word now
   gets a child, with the caller's [CLONE_PARENT_SETTID] store in the
   answer; gets an errno and no child (CLONE_NEWIPC with CLONE_SYSVSEM);
   or declines where the model does not state a store (kernel/fork.c,
   Linux v6.18.46).  The child's registers and memory are
   [Checks.Cases.Kernel.ProcsCloneTid]'s.
   ------------------------------------------------------------------------- *)

Definition tid_pid_model : Model := with_child 4242 (forfeit_model clone_case_model).

(** Four zero bytes at [lo, hi). *)
Definition tid_slot_mem (lo hi : Z) : word -> option byte :=
  fun a => if ((lo <=? bv_unsigned a) && (bv_unsigned a <? hi))%Z
           then Some (Z_to_bv 8 0) else None.

(** [clone] with the parent-tid and the child-tid pointer both [p]. *)
Definition tid_call (flags : Z) (p : word) (rd wr : word -> option byte) : SyscallInput :=
  mkInput 220 [Z_to_bv 64 flags; 0; p; 0; p; 0] rd wr.

Definition tid_p : word := Z_to_bv 64 0x2000.
Definition tid_full : word -> option byte := tid_slot_mem 0x2000 0x2004.

(** CLONE_SYSVSEM: a child, and nothing else changes; its -ENOMEM
    ([get_undo_list], from [copy_semundo], ipc/sem.c:1855-1858) is one of
    [Fork.clone_errnos].  CLONE_CHILD_CLEARTID: no change. *)
Example clone_sysvsem_and_cleartid_child :
  check_syscall (clone_in (Z_to_bv 64 (SIGCHLD + CLONE_SYSVSEM))) (mkEffect 4242 [] [])
    clone_case_model = CheckOk tid_pid_model []
  /\ check_syscall (clone_in (Z_to_bv 64 (SIGCHLD + CLONE_SYSVSEM)))
       (mkEffect (errno_ret ENOMEM) [] []) clone_case_model = CheckOk clone_case_model []
  /\ check_syscall (clone_in (Z_to_bv 64 (SIGCHLD + CLONE_CHILD_CLEARTID)))
       (mkEffect 4242 [] []) clone_case_model = CheckOk tid_pid_model [].
Proof. repeat split; check_eq. Qed.

(** CLONE_PARENT_SETTID.  A writable a2: the pid's
    four bytes there, and the answer without them is refused; a failure
    stores nothing; an a2 [access_ok] refuses, or one in a read-only
    mapping: a child, nothing written; an a2 the memory backs in part:
    declines. *)
Example clone_parent_settid_cases :
  check_syscall (tid_call (SIGCHLD + CLONE_PARENT_SETTID) tid_p tid_full tid_full)
    (mkEffect 4242 [(tid_p, le32_bytes 4242)] []) clone_case_model
    = CheckOk tid_pid_model []
  /\ check_syscall (tid_call (SIGCHLD + CLONE_PARENT_SETTID) tid_p tid_full tid_full)
       (mkEffect 4242 [] []) clone_case_model = CheckReject
  /\ check_syscall (tid_call (SIGCHLD + CLONE_PARENT_SETTID) tid_p tid_full tid_full)
       (mkEffect (errno_ret EAGAIN) [] []) clone_case_model = CheckOk clone_case_model []
  /\ check_syscall (tid_call (SIGCHLD + CLONE_PARENT_SETTID) (Z_to_bv 64 (2 ^ 64 - 2))
                      (fun _ => None) (fun _ => None))
       (mkEffect 4242 [] []) clone_case_model = CheckOk tid_pid_model []
  /\ check_syscall (tid_call (SIGCHLD + CLONE_PARENT_SETTID) tid_p tid_full (fun _ => None))
       (mkEffect 4242 [] []) clone_case_model = CheckOk tid_pid_model []
  /\ check_syscall (tid_call (SIGCHLD + CLONE_PARENT_SETTID) tid_p
                      (tid_slot_mem 0x2000 0x2002) (tid_slot_mem 0x2000 0x2002))
       (mkEffect 4242 [] []) clone_case_model = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.

(** CLONE_CHILD_SETTID: a writable a4 gets the child's store in the
    child's copy, so the caller's answer writes nothing; a read-only a4,
    where the core's store from the read view would differ from Linux's,
    declines; and with CLONE_NEWPID, where the child's own pid is the
    namespace extension's, declines. *)
Example clone_child_settid_cases :
  check_syscall (tid_call (SIGCHLD + CLONE_CHILD_SETTID) tid_p tid_full tid_full)
    (mkEffect 4242 [] []) clone_case_model = CheckOk tid_pid_model []
  /\ check_syscall (tid_call (SIGCHLD + CLONE_CHILD_SETTID) tid_p tid_full (fun _ => None))
       (mkEffect 4242 [] []) clone_case_model = CheckUnmodeled
  /\ check_syscall (tid_call (SIGCHLD + CLONE_CHILD_SETTID + CLONE_NEWPID) tid_p tid_full tid_full)
       (mkEffect 4242 [] []) clone_case_model = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.

(** A namespace word with CLONE_SYSVSEM gets a child; CLONE_NEWIPC with
    CLONE_SYSVSEM gets none (kernel/nsproxy.c:161-162, 171-173): an errno
    is admitted and a pid refused.  Which errno, -EPERM or -EINVAL, is
    the namespace tables'. *)
Example clone_ns_sysvsem_cases :
  check_syscall (clone_in (Z_to_bv 64 (SIGCHLD + CLONE_NEWNS + CLONE_SYSVSEM)))
    (mkEffect 4242 [] []) clone_case_model = CheckOk tid_pid_model []
  /\ check_syscall (clone_in (Z_to_bv 64 (SIGCHLD + CLONE_NEWIPC + CLONE_SYSVSEM)))
       (mkEffect 4242 [] []) clone_case_model = CheckReject
  /\ check_syscall (clone_in (Z_to_bv 64 (SIGCHLD + CLONE_NEWIPC + CLONE_SYSVSEM)))
       (mkEffect (errno_ret EPERM) [] []) clone_case_model = CheckOk clone_case_model []
  /\ check_syscall (clone_in (Z_to_bv 64 (SIGCHLD + CLONE_NEWIPC + CLONE_SYSVSEM)))
       (mkEffect (errno_ret EINVAL) [] []) clone_case_model = CheckOk clone_case_model [].
Proof. repeat split; check_eq. Qed.

(** clone3 with stack 0x8000 and stack_size 0x1000: a child,
    and the record's stack is 0x9000, the child's sp
    (fork.c:2845-2847); with stack 0 and stack_size 8: -EINVAL
    (fork.c:2835-2837). *)
Example clone3_stack_cases :
  check_syscall
    (clone3_args_call [0%Z; 0%Z; 0%Z; 0%Z; (SIGCHLD)%Z; 0x8000%Z; 0x1000%Z; 0%Z; 0%Z; 0%Z; 0%Z])
    (mkEffectU 4242 [] [] [] [] [(clone3_args_base, CLONE_ARGS_SIZE_nat)]) clone3_model
    = CheckOk (with_child 4242 (forfeit_model clone3_model)) []
  /\ option_map (fun bs => match clone3_pre bs with
                           | CdArgs r => bv_unsigned (cla_stack r)
                           | _ => 0%Z
                           end)
       (copy_bytes_map
          (clone3_args_mem [0%Z; 0%Z; 0%Z; 0%Z; (SIGCHLD)%Z; 0x8000%Z; 0x1000%Z; 0%Z; 0%Z; 0%Z; 0%Z])
          clone3_args_base CLONE_ARGS_SIZE) = Some 0x9000%Z
  /\ check_syscall
       (clone3_args_call [0%Z; 0%Z; 0%Z; 0%Z; (SIGCHLD)%Z; 0%Z; 8%Z; 0%Z; 0%Z; 0%Z; 0%Z])
       clone3_einval_eff clone3_model = CheckOk clone3_model [].
Proof. repeat split; check_eq. Qed.

(* =========================================================================
   clone3 (435): SIZES OTHER THAN 88

   [Fork.clone3_copy] answers the size tests of
   [copy_clone_args_from_user] (kernel/fork.c:2772-2775) and the copy of
   [copy_struct_from_user] (include/linux/uaccess.h:400-411) in the
   kernel's order: above [PAGE_SIZE] -E2BIG and below
   [CLONE_ARGS_SIZE_VER0] -EINVAL, nothing read; a short struct is
   zero-filled; a long struct's tail is tested ([check_zeroed_user],
   lib/usercopy.c:45-81) BEFORE its head is read.  The structs below
   sit at a page boundary where it matters, so that "unreadable" is what
   it is on a real process: a whole page with nothing mapped.
   ========================================================================= *)

(** [len] bytes at [base], byte [off] being [byte_at off]. *)
Definition c3_mem (base len : Z) (byte_at : Z -> option byte) : word -> option byte :=
  fun a => let off := (bv_unsigned a - base)%Z in
           if ((0 <=? off)%Z && (off <? len)%Z)%bool then byte_at off else None.

Definition c3_call (uargs : word) (usize : Z) (mem : word -> option byte) : SyscallInput :=
  mkInput 435 [uargs; Z_to_bv 64 usize; 0; 0; 0; 0] mem (fun _ => None).

(** Byte [off] of the fork image: [exit_signal] (offset 32) is SIGCHLD,
    every other byte 0. *)
Definition c3_fork_byte (off : Z) : byte :=
  if Z.eqb off 32 then Z_to_bv 8 SIGCHLD else Z_to_bv 8 0.

Definition c3_err (en : Z) (reads : list (word * nat)) : SyscallEffect :=
  mkEffectU (errno_ret en) [] [] [] [] reads.

(** [size] 4097, one past [PAGE_SIZE]: -E2BIG, nothing read, whatever the
    struct (kernel/fork.c:2772-2773). *)
Example clone3_size_4097_e2big :
  check_syscall (c3_call clone3_args_base 4097 (c3_mem 0x1000 4097 (fun o => Some (c3_fork_byte o))))
    (c3_err E2BIG []) clone3_model = CheckOk clone3_model []
  /\ check_syscall (c3_call clone3_args_base 4097 (c3_mem 0x1000 4097 (fun o => Some (c3_fork_byte o))))
       (c3_err E2BIG [(clone3_args_base, CLONE_ARGS_SIZE_nat)]) clone3_model = CheckReject
  /\ check_syscall (c3_call clone3_args_base 4097 (c3_mem 0x1000 4097 (fun o => Some (c3_fork_byte o))))
       (mkEffectU 4242 [] [] [] [] [(clone3_args_base, CLONE_ARGS_SIZE_nat)]) clone3_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** [size] 63, one below [CLONE_ARGS_SIZE_VER0]: -EINVAL, nothing read
    (kernel/fork.c:2774-2775). *)
Example clone3_size_63_einval :
  check_syscall (c3_call clone3_args_base 63 (c3_mem 0x1000 88 (fun o => Some (c3_fork_byte o))))
    (c3_err EINVAL []) clone3_model = CheckOk clone3_model []
  /\ check_syscall (c3_call clone3_args_base 63 (c3_mem 0x1000 88 (fun o => Some (c3_fork_byte o))))
       (c3_err E2BIG []) clone3_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(** [size] 80 ([CLONE_ARGS_SIZE_VER1]) with the fork image in its first
    80 bytes and nothing mapped past them: zero-filled, a child, exactly
    as the 88-byte image at the same address (with 88 bytes mapped)
    gives; only the ledger differs, 80 bytes read against 88
    (include/linux/uaccess.h:400-401, 408-409). *)
Example clone3_size_80_fork_image :
  check_syscall (c3_call clone3_args_base 80 (c3_mem 0x1000 80 (fun o => Some (c3_fork_byte o))))
    (mkEffectU 4242 [] [] [] [] [(clone3_args_base, 80%nat)]) clone3_model
  = CheckOk (with_child 4242 (forfeit_model clone3_model)) []
  /\ check_syscall (c3_call clone3_args_base 88 (c3_mem 0x1000 88 (fun o => Some (c3_fork_byte o))))
       (mkEffectU 4242 [] [] [] [] [(clone3_args_base, CLONE_ARGS_SIZE_nat)]) clone3_model
     = CheckOk (with_child 4242 (forfeit_model clone3_model)) []
  /\ check_syscall (c3_call clone3_args_base 80 (c3_mem 0x1000 80 (fun o => Some (c3_fork_byte o))))
       (mkEffectU (errno_ret EAGAIN) [] [] [] [] [(clone3_args_base, 80%nat)]) clone3_model
     = CheckOk clone3_model []
  /\ check_syscall (c3_call clone3_args_base 80 (c3_mem 0x1000 80 (fun o => Some (c3_fork_byte o))))
       (mkEffectU 4242 [] [] [] [] [(clone3_args_base, CLONE_ARGS_SIZE_nat)]) clone3_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** The one test that reads the size: CLONE_INTO_CGROUP in a struct
    shorter than [CLONE_ARGS_SIZE_VER2] is -EINVAL (kernel/fork.c:
    2798-2800), where the same 88-byte struct with cgroup 0 passes that
    test and declines (CLONE_INTO_CGROUP is outside the model). *)
Example clone3_size_80_into_cgroup_einval :
  check_syscall
    (c3_call clone3_args_base 80
       (c3_mem 0x1000 80 (fun o => Some (if Z.eqb o 4 then Z_to_bv 8 2 else c3_fork_byte o))))
    (c3_err EINVAL [(clone3_args_base, 80%nat)]) clone3_model = CheckOk clone3_model []
  /\ check_syscall
       (c3_call clone3_args_base 88
          (c3_mem 0x1000 88 (fun o => Some (if Z.eqb o 4 then Z_to_bv 8 2 else c3_fork_byte o))))
       (c3_err EINVAL [(clone3_args_base, CLONE_ARGS_SIZE_nat)]) clone3_model = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.

(** Design row S2, case 11, and the owner's case: [size] 96, a non-zero
    byte (90) in the tail, bytes 88 to 95, and an unreadable head: the
    struct sits so that its 88 head bytes end a page with nothing mapped
    and its tail begins the next, mapped, page.  The tail test runs first
    and answers -E2BIG having read the tail's one word; the head is never
    read, so -EFAULT is refused (include/linux/uaccess.h:402-405).  THE
    SAME WITH A MISALIGNED TAIL: at [uargs] 0x2FFF only the struct's first
    byte lies on the unmapped page 0x2000, and the tail starts at 0x3057,
    7 bytes into its word, so [check_zeroed_user] widens the range down to
    0x3050 (lib/usercopy.c:53-57), masks the 7 bytes below the tail off
    its first word (59-61), and finds byte 90 in the second word: -E2BIG,
    the tail's 8 bytes read. *)
Example clone3_size_96_tail_before_head :
  check_syscall
    (c3_call (Z_to_bv 64 0x2FA8) 96
       (c3_mem 0x2FA8 96 (fun o => if (o <? 88)%Z then None
                                   else Some (if Z.eqb o 90 then Z_to_bv 8 1 else Z_to_bv 8 0))))
    (c3_err E2BIG [(Z_to_bv 64 0x3000, 8%nat)]) clone3_model = CheckOk clone3_model []
  /\ check_syscall
       (c3_call (Z_to_bv 64 0x2FA8) 96
          (c3_mem 0x2FA8 96 (fun o => if (o <? 88)%Z then None
                                      else Some (if Z.eqb o 90 then Z_to_bv 8 1 else Z_to_bv 8 0))))
       (c3_err EFAULT []) clone3_model = CheckReject
  /\ check_syscall
       (c3_call (Z_to_bv 64 0x2FA8) 96
          (c3_mem 0x2FA8 96 (fun o => if (o <? 88)%Z then None
                                      else Some (if Z.eqb o 90 then Z_to_bv 8 1 else Z_to_bv 8 0))))
       (c3_err EFAULT [(Z_to_bv 64 0x3000, 8%nat)]) clone3_model = CheckReject
  /\ check_syscall
       (c3_call (Z_to_bv 64 0x2FFF) 96
          (c3_mem 0x2FFF 96 (fun o => if Z.eqb o 0 then None
                                      else Some (if Z.eqb o 90 then Z_to_bv 8 1 else c3_fork_byte o))))
       (c3_err E2BIG [(Z_to_bv 64 0x3057, 8%nat)]) clone3_model = CheckOk clone3_model []
  /\ check_syscall
       (c3_call (Z_to_bv 64 0x2FFF) 96
          (c3_mem 0x2FFF 96 (fun o => if Z.eqb o 0 then None
                                      else Some (if Z.eqb o 90 then Z_to_bv 8 1 else c3_fork_byte o))))
       (c3_err EFAULT []) clone3_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(** Design row S2, case 15: [size] 200, the struct placed so that its
    byte 96 starts a page with nothing mapped.  The tail's first word,
    bytes 88 to 95, is readable and the second faults.  A non-zero byte
    at 90: -E2BIG at the first word, the second never read.  Bytes 88 to
    95 zero: the walk reaches the second word, which faults: -EFAULT,
    the first word in the ledger (lib/usercopy.c:53-81). *)
Example clone3_size_200_tail_order :
  check_syscall
    (c3_call (Z_to_bv 64 0x1FA0) 200
       (c3_mem 0x1FA0 96 (fun o => Some (if Z.eqb o 90 then Z_to_bv 8 1 else c3_fork_byte o))))
    (c3_err E2BIG [(Z_to_bv 64 0x1FF8, 8%nat)]) clone3_model = CheckOk clone3_model []
  /\ check_syscall
       (c3_call (Z_to_bv 64 0x1FA0) 200
          (c3_mem 0x1FA0 96 (fun o => Some (if Z.eqb o 90 then Z_to_bv 8 1 else c3_fork_byte o))))
       (c3_err EFAULT [(Z_to_bv 64 0x1FF8, 8%nat)]) clone3_model = CheckReject
  /\ check_syscall
       (c3_call (Z_to_bv 64 0x1FA0) 200 (c3_mem 0x1FA0 96 (fun o => Some (c3_fork_byte o))))
       (c3_err EFAULT [(Z_to_bv 64 0x1FF8, 8%nat)]) clone3_model = CheckOk clone3_model []
  /\ check_syscall
       (c3_call (Z_to_bv 64 0x1FA0) 200 (c3_mem 0x1FA0 96 (fun o => Some (c3_fork_byte o))))
       (c3_err E2BIG [(Z_to_bv 64 0x1FF8, 8%nat)]) clone3_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(** A long struct whose tail is zero is the 88-byte struct after the
    tail's reads: [size] 96 with the fork image and a zero tail is a
    child, the tail and then the head in the ledger. *)
Example clone3_size_96_zero_tail_fork_image :
  check_syscall (c3_call clone3_args_base 96 (c3_mem 0x1000 96 (fun o => Some (c3_fork_byte o))))
    (mkEffectU 4242 [] [] [] []
       [(Z_to_bv 64 0x1058, 8%nat); (clone3_args_base, CLONE_ARGS_SIZE_nat)]) clone3_model
  = CheckOk (with_child 4242 (forfeit_model clone3_model)) [].
Proof. check_eq. Qed.
