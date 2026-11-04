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
From LinuxProcessSemantics.LinuxProcessSem Require Procs.
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
   The host's clone refusers ([State.CloneRefusers])

   One case per launch value.  With the value present, a clone answers an
   errno outside the model's lists; with every value at its default,
   [State.no_clone_refusers], the same call has today's answer.  The
   models are [clone_case_model] (no descriptor, so the gate is open) with
   the refuser set by [State.with_clone_refusers], as [State.init_model]
   sets it from [State.ProcInput.in_clone_refusers].
   ------------------------------------------------------------------------- *)

Definition perf_refusers : CloneRefusers := mkCloneRefusers true false false.
Definition bpf_refusers : CloneRefusers := mkCloneRefusers false true false.
Definition scx_refusers : CloneRefusers := mkCloneRefusers false false true.

(** A model built without a launch input has no refuser, and a launch
    the launch predicates admit starts with none ([Run.valid_input]'s pin
    reaches the model through [State.init_model]). *)
Example clone_case_model_has_no_refuser :
  m_clone_refusers clone_case_model = no_clone_refusers.
Proof. reflexivity. Qed.

Example valid_launch_has_no_refuser : forall reserved brk0 mbase sp lim inp,
  valid_input inp ->
  m_clone_refusers (init_model reserved brk0 mbase sp lim inp) = no_clone_refusers.
Proof.
  intros reserved brk0 mbase sp lim inp Hv.
  rewrite m_clone_refusers_init_model. exact (valid_input_no_clone_refusers inp Hv).
Qed.

(** THE LAUNCH PATH: a launch that declares a refuser reaches the model
    with it, and the clone then admits the refuser's errno.  THE CONTROL:
    the same launch at the default refuses it. *)
Example clone_launch_with_perf_refuser_admits_einval :
  let inp := with_inherited_fds [] (demo_input [] IEof) in
  let inp' := mkProcInput_full (in_argv inp) (in_envp inp) (in_image_fs inp)
                (in_stdin inp) (in_uid inp) (in_gid inp) (in_groups inp)
                (in_net inp) (in_nofile inp) (in_sigmask inp) (in_hwcap inp)
                (in_abort_terminal inp) (in_va_size inp) (in_urandom inp)
                (in_tmp inp) (in_kernel inp) (in_execfn inp)
                (in_channel_reader inp) (in_sigpipe_default inp)
                (in_sigpipe_terminal inp) (in_ppid inp) (in_cap_inheritable inp)
                (in_inherited_fds inp) (in_selfkill_terminal inp)
                (in_cgroup_bpf_setsockopt inp) perf_refusers in
  let m := init_model [] 0 0 demo_sp demo_limit inp' in
  let m0 := init_model [] 0 0 demo_sp demo_limit inp in
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret EINVAL) [] []) m
  = CheckOk m []
  (* the control *)
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret EINVAL) [] []) m0
     = CheckReject.
Proof. cbv zeta. split; check_eq. Qed.

(** (1) INHERITABLE PERF EVENTS: the fork word admits -EINVAL,
    [perf_event_init_task]'s own ([State.cr_perf_inherit]); so does
    [clone3]'s fork image, with its ledger.  THE CONTROL: at the default
    -EINVAL is not in [Fork.clone_errnos] and the fork word refuses it. *)
Example clone_perf_events_admit_einval :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret EINVAL) [] [])
    (with_clone_refusers perf_refusers clone_case_model)
  = CheckOk (with_clone_refusers perf_refusers clone_case_model) []
  /\ check_syscall clone3_top_call
       (mkEffectU (errno_ret EINVAL) [] [] [] []
                  [(clone3_top_uargs, CLONE_ARGS_SIZE_nat)])
       (with_clone_refusers perf_refusers clone3_model)
     = CheckOk (with_clone_refusers perf_refusers clone3_model) []
  (* the control *)
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret EINVAL) [] [])
       clone_case_model = CheckReject
  /\ check_syscall clone3_top_call
       (mkEffectU (errno_ret EINVAL) [] [] [] []
                  [(clone3_top_uargs, CLONE_ARGS_SIZE_nat)])
       clone3_model = CheckReject.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** (2) A BPF PROGRAM ON [task_alloc]: ANY errno from 1 to 4095, for both
    words ([State.cr_bpf_task_alloc]), stated over every errno at the spec
    and read off at the checker for -EPERM on the fork word and -EINTR on
    the namespace word.  THE CONTROL: at the default the fork word refuses
    -EPERM and the namespace word refuses -EINTR. *)
Definition bpf_model : Model := with_clone_refusers bpf_refusers clone_case_model.

Example clone_bpf_task_alloc_any_errno : forall e i,
  (1 <= e <= 4095)%Z ->
  clone_spec (Z_to_bv 64 SIGCHLD) i bpf_model
    (Ok (mkEffect (errno_ret e) [] []) bpf_model [])
  /\ clone_spec bwrap_clone_flags i bpf_model
       (Ok (mkEffect (errno_ret e) [] []) bpf_model []).
Proof.
  intros e i He. split; unfold clone_spec;
    (apply clone_refusable_refused;
     [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
     | apply clone_refused_fail_ok; exact He]).
Qed.

Example clone_bpf_task_alloc_at_the_checker :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret EPERM) [] [])
    bpf_model = CheckOk bpf_model []
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect (errno_ret EINTR) [] [])
       bpf_model = CheckOk bpf_model []
  (* the control *)
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret EPERM) [] [])
       clone_case_model = CheckReject
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect (errno_ret EINTR) [] [])
       clone_case_model = CheckReject.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** (3) A SCHED_EXT SCHEDULER, which the host can attach during the run
    ([State.cr_sched_ext]): any errno at every clone, the one after a
    successful clone included (the model then holds the child, and still
    the refuser).  THE CONTROL: at the default the same later clone
    refuses -E2BIG (7). *)
Definition scx_model : Model := with_clone_refusers scx_refusers clone_case_model.

Example clone_sched_ext_at_every_clone :
  let m1 := with_child (Z_to_bv 64 4242) scx_model in
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] []) scx_model
    = CheckOk m1 []
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret 7) [] []) m1
     = CheckOk m1 []
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret 4095) [] []) m1
     = CheckOk m1 []
  (* the control *)
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret 7) [] [])
       (with_child (Z_to_bv 64 4242) clone_case_model) = CheckReject.
Proof. cbv zeta. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** A refuser adds no answer where the model declines: a word outside
    both classes, and the descriptor gate, still decline. *)
Example clone_refusers_keep_the_declines :
  check_syscall (clone_in (Z_to_bv 64 (CLONE_VM + SIGCHLD)))
    (mkEffect (errno_ret EINVAL) [] []) bpf_model = CheckUnmodeled
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret EINVAL) [] [])
       (with_fds [(3, FdFile [] 0)] bpf_model) = CheckUnmodeled.
Proof. split; vm_compute; reflexivity. Qed.

(** IN A CHILD TOO.  In a run of the multi-process core every clone is a
    step of one entry, a child the core made included, and the child's
    model is [Procs.child_proc] of its parent's, which copies the
    refusers.  So a child of a parent whose host has a BPF program on
    [task_alloc] gets the widened answer at its own clone: -EPERM on the
    fork word.  THE CONTROL: the child of a parent at the default refuses
    it.  [Checks.ProcsCloneRefusers.clone_refusers_reachable] is the same
    fact for every entry of every reachable state. *)
Example clone_child_sees_the_refuser : forall (e : Procs.ProcessEntry) c c' q,
  Procs.pe_model e = bpf_model -> Procs.pe_pid e = Z_to_bv 64 1 ->
  let m := Procs.pe_model (Procs.child_entry e c c' q) in
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret EPERM) [] []) m
  = CheckOk m [].
Proof.
  intros e c c' q He Hp. cbv zeta. unfold Procs.child_entry. cbn [Procs.pe_model].
  rewrite He, Hp. check_eq.
Qed.

Example clone_child_at_the_default_refuses : forall (e : Procs.ProcessEntry) c c' q,
  Procs.pe_model e = clone_case_model -> Procs.pe_pid e = Z_to_bv 64 1 ->
  let m := Procs.pe_model (Procs.child_entry e c c' q) in
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect (errno_ret EPERM) [] []) m
  = CheckReject.
Proof.
  intros e c c' q He Hp. cbv zeta. unfold Procs.child_entry. cbn [Procs.pe_model].
  rewrite He, Hp. check_eq.
Qed.

