(** * LinuxProcessSem.Checks.Cases.KernelPin — the plain launch is on the kernel of record

    [Run.valid_input] pins [State.in_kernel] to [State.default_kernel],
    and so does every named launch beside it ([Run.valid_input_kernel]
    and its kin).  The published statements were written about that one
    build; the pin keeps them about it.

    The case here is the build the pin turns on: a kernel built without
    [CONFIG_RSEQ].  Its auxiliary vector is two pairs shorter (27 rather
    than 29: no AT_RSEQ_FEATURE_SIZE and no AT_RSEQ_ALIGN), so the entry
    block, the argument strings and every address the start-up code reads
    off the stack move by 32 bytes.  [rseq_off_launch] is
    [ordinary_launch] with that one field changed, and every named launch
    refuses it.  No predicate admits it: no statement in this tree names
    a build without [CONFIG_RSEQ]. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Run StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples.
Import ListNotations.
Open Scope bv_scope.

(** [Checks.Examples.demo_input_valid]'s input: the ordinary launch. *)
Definition ordinary_launch : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

(** [State.default_kernel] with [kb_rseq] cleared and nothing else. *)
Definition rseq_off_kernel : KernelBuild :=
  mkKernelBuild false 1%N true 256%N 0%N false 0%N cache_view_absent
                224%N 212992%N 212992%N 4194304%N 4194304%N.

(** The ordinary launch on that kernel: the kernel is the only field
    that differs. *)
Definition rseq_off_launch : ProcInput :=
  mkProcInput_full [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48
                   default_urandom [] rseq_off_kernel default_execfn
                   true true false.

Lemma ordinary_launch_valid : valid_input ordinary_launch.
Proof. exact demo_input_valid. Qed.

(** The two builds differ in [kb_rseq] alone (compare [rseq_off_kernel]
    with [State.default_kernel] field by field), and that bit is what moves
    the entry block: 29 auxv pairs on the kernel of record, 27 without
    [CONFIG_RSEQ]. *)
Example rseq_off_differs_in_rseq_alone :
  kb_rseq (in_kernel ordinary_launch) = true
  /\ kb_rseq (in_kernel rseq_off_launch) = false
  /\ auxv_count (kb_rseq (in_kernel ordinary_launch)) = 29%nat
  /\ auxv_count (kb_rseq (in_kernel rseq_off_launch)) = 27%nat.
Proof. repeat split; reflexivity. Qed.

(** The kernel pin, fired: the build is not the kernel of record, so the
    plain launch refuses it.  It is the pin that refuses it, read through
    its accessor; no other clause is consulted. *)
Example plain_launch_refuses_rseq_off :
  ~ valid_input rseq_off_launch.
Proof.
  intros Hv. apply valid_input_kernel in Hv.
  apply (f_equal kb_rseq) in Hv. vm_compute in Hv. discriminate Hv.
Qed.

(** Every named launch refuses it too, the ones that leave a declaration
    open included: none of them leaves the kernel open. *)
Example every_named_launch_refuses_rseq_off :
  ~ valid_input_abort rseq_off_launch
  /\ ~ valid_input_either rseq_off_launch
  /\ ~ valid_input_sigpipe_ignored rseq_off_launch
  /\ ~ valid_input_sigpipe_either rseq_off_launch
  /\ ~ valid_input_channel_closed rseq_off_launch
  /\ ~ valid_input_channel_either rseq_off_launch
  /\ ~ valid_input_sigpipe_kills rseq_off_launch
  /\ ~ valid_input_sv39 rseq_off_launch
  /\ ~ valid_input_sv57 rseq_off_launch
  /\ ~ valid_input_va_any rseq_off_launch
  /\ ~ valid_input_hwcap_rv64gc rseq_off_launch
  /\ ~ valid_input_hwcap_rv64gcv rseq_off_launch
  /\ ~ valid_input_abort_hwcap_rv64gc rseq_off_launch
  /\ ~ valid_input_abort_hwcap_rv64gcv rseq_off_launch.
Proof.
  repeat split; intros Hv;
    first [ apply valid_input_abort_kernel in Hv
          | apply valid_input_either_kernel in Hv
          | apply valid_input_sigpipe_ignored_kernel in Hv
          | apply valid_input_sigpipe_either_kernel in Hv
          | apply valid_input_channel_closed_kernel in Hv
          | apply valid_input_channel_either_kernel in Hv
          | apply valid_input_sigpipe_kills_kernel in Hv
          | apply valid_input_sv39_kernel in Hv
          | apply valid_input_sv57_kernel in Hv
          | apply valid_input_va_any_kernel in Hv
          | apply valid_input_hwcap_rv64gc_kernel in Hv
          | apply valid_input_hwcap_rv64gcv_kernel in Hv
          | apply valid_input_abort_hwcap_rv64gc_kernel in Hv
          | apply valid_input_abort_hwcap_rv64gcv_kernel in Hv ];
    apply (f_equal kb_rseq) in Hv; vm_compute in Hv; discriminate Hv.
Qed.
