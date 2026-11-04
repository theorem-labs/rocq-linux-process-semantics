(** * LinuxProcessSem.Checks.Cases.KernelPin — the plain launch is on the kernel of record

    [Run.valid_input], and every named launch beside it, ends with
    [in_kernel inp = Run.recorded_kernel (in_kernel inp)]: the nine
    fields the published statements had one answer for are
    [State.default_kernel]'s, and the four launch facts -- [kb_thp],
    [kb_aslr], [kb_guard], [kb_rnd_bits] -- are free.  The two cases here
    are one of each kind, each the ordinary launch with only its kernel
    changed.

    - [rseq_off_launch] runs on a kernel built without [CONFIG_RSEQ].
      Its auxiliary vector is two pairs shorter (27 rather than 29: no
      AT_RSEQ_FEATURE_SIZE and no AT_RSEQ_ALIGN), so the entry block,
      the argument strings and every address start-up code reads off the
      stack move by 32 bytes.  Every named launch refuses it, each
      through its own [_rseq] accessor.
    - [launch_facts_launch] runs on a kernel that differs from the
      default in all four launch facts at once: transparent huge pages,
      no randomisation, a guard gap of 0 pages and a [vm.mmap_rnd_bits]
      encoding of 15 (33 bits under Sv48).  [Run.valid_input] admits it,
      because the released model covered each of those. *)

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

(** The ordinary launch on [kb]: the kernel is the only field that
    differs. *)
Definition launch_on (kb : KernelBuild) : ProcInput :=
  mkProcInput_full [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48
                   default_urandom [] kb default_execfn
                   true true false.

Lemma ordinary_launch_valid : valid_input ordinary_launch.
Proof. exact demo_input_valid. Qed.

(* -------------------------------------------------------------------------
   A pinned field: the build without CONFIG_RSEQ is refused
   ------------------------------------------------------------------------- *)

(** [State.default_kernel] with [kb_rseq] cleared and nothing else. *)
Definition rseq_off_kernel : KernelBuild :=
  mkKernelBuild false 1%N true 256%N 0%N false 0%N cache_view_absent
                224%N 212992%N 212992%N 4194304%N 4194304%N.

Definition rseq_off_launch : ProcInput := launch_on rseq_off_kernel.

(** The two builds differ in [kb_rseq] alone (compare [rseq_off_kernel]
    with [State.default_kernel] field by field), and that bit is what
    moves the entry block: 29 auxv pairs on the kernel of record, 27
    without [CONFIG_RSEQ]. *)
Example rseq_off_differs_in_rseq_alone :
  kb_rseq (in_kernel ordinary_launch) = true
  /\ kb_rseq (in_kernel rseq_off_launch) = false
  /\ auxv_count (kb_rseq (in_kernel ordinary_launch)) = 29%nat
  /\ auxv_count (kb_rseq (in_kernel rseq_off_launch)) = 27%nat.
Proof. repeat split; reflexivity. Qed.

(** The pin, fired: the plain launch refuses the build, and it is the
    rseq field's accessor that refuses it. *)
Example plain_launch_refuses_rseq_off :
  ~ valid_input rseq_off_launch.
Proof.
  intros Hv. apply valid_input_rseq in Hv. vm_compute in Hv. discriminate Hv.
Qed.

(** Every named launch refuses it too, the ones that leave a declaration
    open included: none of them leaves the pinned fields open. *)
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
    first [ apply valid_input_abort_rseq in Hv
          | apply valid_input_either_rseq in Hv
          | apply valid_input_sigpipe_ignored_rseq in Hv
          | apply valid_input_sigpipe_either_rseq in Hv
          | apply valid_input_channel_closed_rseq in Hv
          | apply valid_input_channel_either_rseq in Hv
          | apply valid_input_sigpipe_kills_rseq in Hv
          | apply valid_input_sv39_rseq in Hv
          | apply valid_input_sv57_rseq in Hv
          | apply valid_input_va_any_rseq in Hv
          | apply valid_input_hwcap_rv64gc_rseq in Hv
          | apply valid_input_hwcap_rv64gcv_rseq in Hv
          | apply valid_input_abort_hwcap_rv64gc_rseq in Hv
          | apply valid_input_abort_hwcap_rv64gcv_rseq in Hv ];
    vm_compute in Hv; discriminate Hv.
Qed.

(* -------------------------------------------------------------------------
   The free fields: a launch that changes all four launch facts is admitted
   ------------------------------------------------------------------------- *)

(** [State.default_kernel] with transparent huge pages, no
    randomisation, a guard gap of 0 pages and a [vm.mmap_rnd_bits]
    encoding of 15, and nothing else changed. *)
Definition launch_facts_kernel : KernelBuild :=
  mkKernelBuild true 1%N false 0%N 15%N true 0%N cache_view_absent
                224%N 212992%N 212992%N 4194304%N 4194304%N.

Definition launch_facts_launch : ProcInput := launch_on launch_facts_kernel.

(** Each of the four differs from the default, and the encoding is 33
    bits under Sv48, above the released 24. *)
Example launch_facts_differ_in_each :
  kb_thp launch_facts_kernel <> kb_thp default_kernel
  /\ kb_aslr launch_facts_kernel <> kb_aslr default_kernel
  /\ kb_guard launch_facts_kernel <> kb_guard default_kernel
  /\ kb_rnd_bits launch_facts_kernel <> kb_rnd_bits default_kernel
  /\ mmap_rnd_bits Sv48 launch_facts_kernel = 33%Z.
Proof.
  repeat split; try (intro Hc; vm_compute in Hc; discriminate Hc);
    reflexivity.
Qed.

(** Every clause but the kernel's is [demo_input_valid]'s, taken without
    counting conjuncts; the kernel clause closes by computation, because
    [Run.recorded_kernel] copies the four launch facts from the build it
    is given. *)
Example plain_launch_admits_launch_facts :
  valid_input launch_facts_launch.
Proof.
  pose proof demo_input_valid as H. red in H |- *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; try assumption;
    reflexivity.
Qed.

(** And the pinned fields still read back as the default's on it. *)
Example launch_facts_launch_pinned_fields :
  kb_rseq (in_kernel launch_facts_launch) = true
  /\ kb_vdso (in_kernel launch_facts_launch) = 1%N
  /\ launch_cache_words (in_kernel launch_facts_launch)
     = launch_cache_words default_kernel.
Proof.
  pose proof plain_launch_admits_launch_facts as Hv.
  split; [| split].
  - exact (valid_input_rseq _ Hv).
  - exact (valid_input_vdso _ Hv).
  - exact (valid_input_cache_words _ Hv).
Qed.
