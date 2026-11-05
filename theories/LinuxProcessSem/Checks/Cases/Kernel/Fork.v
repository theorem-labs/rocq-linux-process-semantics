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
     = CheckOk (clone_child_made (Z_to_bv 64 4242) clone3_model) []
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
    clone_case_model = CheckOk (clone_child_made (Z_to_bv 64 4242) clone_case_model) []
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
  let m1 := clone_child_made (Z_to_bv 64 4242) clone_case_model in
  m_child_pids m1 = [Z_to_bv 64 4242]
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4243 [] []) m1
     = CheckOk (clone_child_made (Z_to_bv 64 4243) m1) []
  /\ m_child_pids (clone_child_made (Z_to_bv 64 4243) m1)
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
    clone_case_model = CheckOk (clone_child_made (Z_to_bv 64 4242) clone_case_model) []
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

(** THE GATE PASSES FOUR OF THE SEVEN OPAQUE KINDS AND THE EVENTFDS, for
    both words, end to end: [OProcPath], [OProcFile], [OEventFd] and
    [ONsFile], and [State.FdEventfd].  [clone_opaque_model] is the table
    bubblewrap's parent holds at its clone (channels 0-2, the O_PATH
    descriptor on "/proc" at fd 3, its two eventfds at 4 and 5, made with
    0x80800 and 0x80000), and [clone_all_opaque_model] adds the modeled
    [overflowuid] sysctl file and a namespace and mount model descriptor.
    Before [State.FdOpaque] the model held none of the opaque kinds, so
    it could not reach this clone at all.

    A SUCCESSFUL CLONE SHARES THE TWO EVENTFDS ([Fork.clone_child_made]):
    each [State.FdEventfd] becomes [State.FdOpaque (State.OEventFd w)],
    with w the O_NONBLOCK bit for the 0x80800 one and 0 for the other
    (EFD_CLOEXEC is not part of w), and the child's pid is recorded.  An
    errno leaves the table as it was, counters included.  THE CONTROL is
    [clone_namespace_word_keeps_the_descriptor_gate] above: a regular
    file still declines both words.  Two other kinds decline
    ([clone_declines_procfd_dir_and_signalfd] below).  An inherited
    file passes when it holds no offset, and with a live one either
    word takes its offset from the caller
    ([Checks.Cases.Fs.Inherited]). *)
Definition clone_opaque_model : Model :=
  with_fds [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
            (3, FdOpaque (OProcPath proc_root_path));
            (4, FdEventfd (mkEventfdCtx 0 false true));
            (5, FdEventfd (mkEventfdCtx 0 false false))] clone_case_model.

Definition clone_all_opaque_model : Model :=
  with_fds (fd_insert (fd_insert (m_fds clone_opaque_model) 6
                         (FdOpaque (OProcFile proc_sys_overflowuid_path)))
                      7 (FdOpaque (ONsFile 7))) clone_opaque_model.

Example clone_passes_the_opaque_kinds :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
    clone_opaque_model = CheckOk (clone_child_made (Z_to_bv 64 4242) clone_opaque_model) []
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
       clone_opaque_model = CheckOk (clone_child_made (Z_to_bv 64 4242) clone_opaque_model) []
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
       clone_all_opaque_model = CheckOk (clone_child_made (Z_to_bv 64 4242) clone_all_opaque_model) []
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
       clone_all_opaque_model = CheckOk (clone_child_made (Z_to_bv 64 4242) clone_all_opaque_model) []
  (* the two eventfds after the clone: the shared kind, w from the context *)
  /\ m_fds (clone_child_made (Z_to_bv 64 4242) clone_opaque_model)
     = [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
        (3, FdOpaque (OProcPath proc_root_path));
        (4, FdOpaque (OEventFd (Z_to_bv 64 O_NONBLOCK)));
        (5, FdOpaque (OEventFd (Z_to_bv 64 0)))]
  /\ m_has_children (clone_child_made (Z_to_bv 64 4242) clone_opaque_model) = true
  /\ m_child_pids (clone_child_made (Z_to_bv 64 4242) clone_opaque_model)
     = m_child_pids clone_opaque_model ++ [Z_to_bv 64 4242]
  (* the namespace word's errno: any but -EINTR, and the table unchanged *)
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
     = CheckOk (clone_child_made (Z_to_bv 64 4242) clone_channels_model) [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(* -------------------------------------------------------------------------
   ONE TABLE THAT HOLDS BOTH KINDS A CLONE CONVERTS

   [Kernel.Fork.clone_child_made] forfeits each live inherited offset
   ([forfeit_inherited]) and shares each eventfd ([share_eventfds]) in
   the caller's table, and the child's table is the caller's table before
   the call with only the sharing applied ([Procs.child_entry]).  The
   table below holds one of each kind and an entry neither conversion
   touches, at distinct numbers: fd 3 a live inherited file (the bytes
   "key\n" at offset 1), fd 4 a non-blocking eventfd with counter 5, fd 5
   an O_PATH descriptor on "/proc".  The controls below fail if either
   half of the conversion is lost, on either side.
   ------------------------------------------------------------------------- *)

Definition clone_mixed_fds : list (word * FdEntry) :=
  [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
   (3, FdOpaque (OInherited (Some ([107; 101; 121; 10], 1))));
   (4, FdEventfd (mkEventfdCtx 5 false true));
   (5, FdOpaque (OProcPath proc_root_path))].

Definition clone_mixed_model : Model := with_fds clone_mixed_fds clone_case_model.

(** The caller's table after a successful clone: fd 3 holds no offset,
    fd 4 is the shared kind with O_NONBLOCK, fd 5 and the channels as
    they were, every number in its place. *)
Definition clone_mixed_parent_fds : list (word * FdEntry) :=
  [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
   (3, FdOpaque (OInherited None));
   (4, FdOpaque (OEventFd (Z_to_bv 64 O_NONBLOCK)));
   (5, FdOpaque (OProcPath proc_root_path))].

(** The child's table: fd 3 keeps the bytes and the offset exactly, fd 4
    is the shared kind, as in the caller. *)
Definition clone_mixed_child_fds : list (word * FdEntry) :=
  [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
   (3, FdOpaque (OInherited (Some ([107; 101; 121; 10], 1))));
   (4, FdOpaque (OEventFd (Z_to_bv 64 O_NONBLOCK)));
   (5, FdOpaque (OProcPath proc_root_path))].

Definition clone3_mixed_model : Model := with_fds clone_mixed_fds clone3_model.

(** A SUCCESS OF EACH WORD, through the executable checker: the fork
    word, the namespace word and a valid [clone3] each return an
    admissible pid, and the caller's table is [clone_mixed_parent_fds],
    with no [FdEventfd] left.  The child pid is recorded, and the
    unrelated fields are unchanged. *)
Example clone_mixed_table_success :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] []) clone_mixed_model
  = CheckOk (clone_child_made (Z_to_bv 64 4242) clone_mixed_model) []
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] []) clone_mixed_model
     = CheckOk (clone_child_made (Z_to_bv 64 4242) clone_mixed_model) []
  /\ check_syscall clone3_top_call
       (mkEffectU (Z_to_bv 64 4242) [] [] [] []
                  [(clone3_top_uargs, CLONE_ARGS_SIZE_nat)])
       clone3_mixed_model
     = CheckOk (clone_child_made (Z_to_bv 64 4242) clone3_mixed_model) []
  /\ m_fds (clone_child_made (Z_to_bv 64 4242) clone_mixed_model) = clone_mixed_parent_fds
  /\ m_fds (clone_child_made (Z_to_bv 64 4242) clone3_mixed_model) = clone_mixed_parent_fds
  /\ map fst (m_fds (clone_child_made (Z_to_bv 64 4242) clone_mixed_model))
     = map fst clone_mixed_fds
  /\ m_child_pids (clone_child_made (Z_to_bv 64 4242) clone_mixed_model) = [Z_to_bv 64 4242]
  /\ m_has_children (clone_child_made (Z_to_bv 64 4242) clone_mixed_model) = true
  /\ m_pipes (clone_child_made (Z_to_bv 64 4242) clone_mixed_model) = m_pipes clone_mixed_model
  /\ m_vmmaps (clone_child_made (Z_to_bv 64 4242) clone_mixed_model)
     = m_vmmaps clone_mixed_model
  /\ m_creds (clone_child_made (Z_to_bv 64 4242) clone_mixed_model) = m_creds clone_mixed_model
  /\ share_eventfds clone_mixed_fds = clone_mixed_child_fds.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** THE CONTROLS, each of which one lost half of the conversion would
    make true.  The caller's table is neither the eventfd-only table (fd 3
    would still hold its offset) nor the forfeit-only table (fd 4 would
    still hold its counter).  The child's table is neither a copy of the
    caller's new table (fd 3 would have lost its offset) nor the table
    without the sharing (fd 4 would still hold its counter). *)
Example clone_mixed_table_controls :
  clone_mixed_parent_fds <> share_eventfds clone_mixed_fds
  /\ clone_mixed_parent_fds <> forfeit_inherited clone_mixed_fds
  /\ clone_mixed_child_fds <> share_eventfds (forfeit_inherited clone_mixed_fds)
  /\ clone_mixed_child_fds <> clone_mixed_fds.
Proof.
  repeat split; intros H; vm_compute in H; discriminate H.
Qed.

(** A FAILURE CONVERTS NOTHING.  An admitted errno of either word leaves
    the model exactly as it was: both original entries, so an eventfd read
    before the clone still answers from the counter 5 and an inherited
    read from offset 1, and no child recorded.  An invalid pid, the
    child's own 0, a namespace -EINTR and a [clone3] answer without its
    ledger are rejected, never accepted with a converted table. *)
Example clone_mixed_table_failure :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret EAGAIN) [] [])
    clone_mixed_model = CheckOk clone_mixed_model []
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect (errno_ret EAGAIN) [] [])
       clone_mixed_model = CheckOk clone_mixed_model []
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect (errno_ret EPERM) [] [])
       clone_mixed_model = CheckOk clone_mixed_model []
  /\ check_syscall clone3_top_call
       (mkEffectU (errno_ret EAGAIN) [] [] [] []
                  [(clone3_top_uargs, CLONE_ARGS_SIZE_nat)])
       clone3_mixed_model
     = CheckOk clone3_mixed_model []
  /\ m_child_pids clone_mixed_model = []
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 0 [] []) clone_mixed_model
     = CheckReject
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect (errno_ret EINTR) [] [])
       clone_mixed_model = CheckReject
  /\ check_syscall clone3_top_call (mkEffect (Z_to_bv 64 4242) [] []) clone3_mixed_model
     = CheckReject.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** A DISALLOWED KIND BESIDE THEM STILL DECLINES, for both words, with no
    update: a pipe end, a stream-pair end, a datagram socket, an unnamed
    file.  And the conversions are idempotent: a table that holds only an
    inherited file without its offset and an already shared eventfd is
    the caller's table again after a clone. *)
Example clone_mixed_table_declines_and_idempotent :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
    (with_fds (clone_mixed_fds ++ [(6, FdPipe 0 false)]) clone_case_model)
  = CheckUnmodeled
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
       (with_fds (clone_mixed_fds ++ [(6, FdStream 0 false (stream_fresh false 4608 2304))])
          clone_case_model)
     = CheckUnmodeled
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
       (with_fds (clone_mixed_fds ++ [(6, FdDgram 1)]) clone_case_model)
     = CheckUnmodeled
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
       (with_fds (clone_mixed_fds ++ [(6, FdAnon 0 (mkAnonFile [] 0 true true false None))])
          clone_case_model)
     = CheckUnmodeled
  /\ m_fds (clone_child_made (Z_to_bv 64 4242)
              (with_fds clone_mixed_parent_fds clone_case_model))
     = clone_mixed_parent_fds.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.
