(** * LinuxProcessSem.Checks.Cases.KernelPin — which kernel fields the named launches fix

    [Run.valid_input], and every named launch beside it, ends with
    [in_kernel inp = Run.recorded_kernel (in_kernel inp)].  Eight fields
    are [State.default_kernel]'s — [kb_vdso], [kb_vlenb], [kb_cache],
    [kb_skb_head] and the four socket sysctls, the ones the published
    statements had a single answer for — and five are free: [kb_thp],
    [kb_aslr], [kb_guard], [kb_rnd_bits] and [kb_rseq], each of which
    the released model covered as a range.

    Three cases, one per kind, each the ordinary launch with its kernel
    changed and nothing else:

    - [vlenb_launch] runs on a kernel whose [kb_vlenb] is not the
      default.  That cell is published as AT_MINSIGSTKSZ
      ([State.min_sigframe_size]), a word the released auxv did not
      carry at all, so it is pinned and every named launch refuses this
      build.
    - [launch_facts_launch] changes all five free fields at once:
      transparent huge pages, no randomisation, a guard gap of 0 pages,
      a [vm.mmap_rnd_bits] encoding of 15 (33 bits under Sv48) and no
      [CONFIG_RSEQ].  [Run.valid_input] admits it.
    - The rseq case is the one the pin turns on, so it is measured
      rather than only admitted.  Without [CONFIG_RSEQ] the auxv is 27
      pairs instead of 29, so the entry block is 32 bytes shorter and
      Linux's entry stack pointer sits 32 bytes higher.  On the ordinary
      argument vector the highest admitted stack pointer is
      [STACK_TOP - 528] with the flag and [STACK_TOP - 496] without it;
      [rseq_off_sp_is_32_above] computes both, and
      [rseq_off_launch_entry_valid] proves the launch at the higher one
      is a launch [Run.valid_entry] admits.  Pinning the flag on would
      have deleted every one of those stack pointers from the published
      statements. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Run StackLayout MemImageType.
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
   A pinned field: a build with another vector unit is refused
   ------------------------------------------------------------------------- *)

(** [State.default_kernel] with [kb_vlenb] changed and nothing else. *)
Definition vlenb_kernel : KernelBuild :=
  mkKernelBuild false 1%N true 256%N 0%N true 3%N cache_view_absent
                224%N 212992%N 212992%N 4194304%N 4194304%N.

Definition vlenb_launch : ProcInput := launch_on vlenb_kernel.

(** The cell is published, so the build is a different launch: under the
    vector-capable hart the signal frame AT_MINSIGSTKSZ announces moves. *)
Example vlenb_launch_moves_the_sigframe :
  kb_vlenb (in_kernel vlenb_launch) <> kb_vlenb default_kernel
  /\ min_sigframe_size (in_kernel vlenb_launch) hwcap_rv64gcv
     <> min_sigframe_size default_kernel hwcap_rv64gcv.
Proof.
  split; intro Hc; vm_compute in Hc; discriminate Hc.
Qed.

(** The pin, fired: the plain launch refuses the build, and it is the
    vector cell's accessor that refuses it. *)
Example plain_launch_refuses_vlenb :
  ~ valid_input vlenb_launch.
Proof.
  intros Hv. apply valid_input_vlenb in Hv. vm_compute in Hv. discriminate Hv.
Qed.

(** Every named launch refuses it too, the ones that leave a declaration
    open included: none of them leaves a pinned field open. *)
Example every_named_launch_refuses_vlenb :
  ~ valid_input_abort vlenb_launch
  /\ ~ valid_input_either vlenb_launch
  /\ ~ valid_input_sigpipe_ignored vlenb_launch
  /\ ~ valid_input_sigpipe_either vlenb_launch
  /\ ~ valid_input_channel_closed vlenb_launch
  /\ ~ valid_input_channel_either vlenb_launch
  /\ ~ valid_input_sigpipe_kills vlenb_launch
  /\ ~ valid_input_sv39 vlenb_launch
  /\ ~ valid_input_sv57 vlenb_launch
  /\ ~ valid_input_va_any vlenb_launch
  /\ ~ valid_input_hwcap_rv64gc vlenb_launch
  /\ ~ valid_input_hwcap_rv64gcv vlenb_launch
  /\ ~ valid_input_abort_hwcap_rv64gc vlenb_launch
  /\ ~ valid_input_abort_hwcap_rv64gcv vlenb_launch.
Proof.
  repeat split; intros Hv;
    first [ apply valid_input_abort_vlenb in Hv
          | apply valid_input_either_vlenb in Hv
          | apply valid_input_sigpipe_ignored_vlenb in Hv
          | apply valid_input_sigpipe_either_vlenb in Hv
          | apply valid_input_channel_closed_vlenb in Hv
          | apply valid_input_channel_either_vlenb in Hv
          | apply valid_input_sigpipe_kills_vlenb in Hv
          | apply valid_input_sv39_vlenb in Hv
          | apply valid_input_sv57_vlenb in Hv
          | apply valid_input_va_any_vlenb in Hv
          | apply valid_input_hwcap_rv64gc_vlenb in Hv
          | apply valid_input_hwcap_rv64gcv_vlenb in Hv
          | apply valid_input_abort_hwcap_rv64gc_vlenb in Hv
          | apply valid_input_abort_hwcap_rv64gcv_vlenb in Hv ];
    vm_compute in Hv; discriminate Hv.
Qed.

(* -------------------------------------------------------------------------
   The free fields: a launch that changes all five is admitted
   ------------------------------------------------------------------------- *)

(** [State.default_kernel] with transparent huge pages, no
    randomisation, a guard gap of 0 pages, a [vm.mmap_rnd_bits] encoding
    of 15 and no [CONFIG_RSEQ], and nothing else changed. *)
Definition launch_facts_kernel : KernelBuild :=
  mkKernelBuild true 1%N false 0%N 15%N false 0%N cache_view_absent
                224%N 212992%N 212992%N 4194304%N 4194304%N.

Definition launch_facts_launch : ProcInput := launch_on launch_facts_kernel.

(** Each of the five differs from the default, and the encoding is 33
    bits under Sv48, above the 24 the released floor was derived from. *)
Example launch_facts_differ_in_each :
  kb_thp launch_facts_kernel <> kb_thp default_kernel
  /\ kb_aslr launch_facts_kernel <> kb_aslr default_kernel
  /\ kb_guard launch_facts_kernel <> kb_guard default_kernel
  /\ kb_rnd_bits launch_facts_kernel <> kb_rnd_bits default_kernel
  /\ kb_rseq launch_facts_kernel <> kb_rseq default_kernel
  /\ mmap_rnd_bits Sv48 launch_facts_kernel = 33%Z.
Proof.
  repeat split; try (intro Hc; vm_compute in Hc; discriminate Hc);
    reflexivity.
Qed.

(** Every clause but the kernel's is [demo_input_valid]'s, taken without
    counting conjuncts; the kernel clause closes by computation, because
    [Run.recorded_kernel] copies the five launch facts from the build it
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
  kb_vdso (in_kernel launch_facts_launch) = 1%N
  /\ kb_vlenb (in_kernel launch_facts_launch) = 0%N
  /\ launch_cache_words (in_kernel launch_facts_launch)
     = launch_cache_words default_kernel.
Proof.
  pose proof plain_launch_admits_launch_facts as Hv.
  split; [| split].
  - exact (valid_input_vdso _ Hv).
  - exact (valid_input_vlenb _ Hv).
  - exact (valid_input_cache_words _ Hv).
Qed.

(* -------------------------------------------------------------------------
   The stack pointer only the rseq-off layout gives
   ------------------------------------------------------------------------- *)

(** [State.default_kernel] with [kb_rseq] cleared and nothing else: the
    27-pair auxv. *)
Definition rseq_off_kernel : KernelBuild :=
  mkKernelBuild false 1%N true 256%N 0%N false 0%N cache_view_absent
                224%N 212992%N 212992%N 4194304%N 4194304%N.

Definition rseq_off_launch : ProcInput := launch_on rseq_off_kernel.

Example rseq_off_launch_valid : valid_input rseq_off_launch.
Proof.
  pose proof demo_input_valid as H. red in H |- *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; try assumption;
    reflexivity.
Qed.

(** The two auxv layouts, and the stack pointers they give.  [launch_sp_hi]
    is [align_down16 (top - 8 - L) - C]: the argument vector is the same,
    so the whole difference is the auxv's 32 bytes. *)
Example rseq_off_sp_is_32_above :
  auxv_count (kb_rseq (in_kernel ordinary_launch)) = 29%nat
  /\ auxv_count (kb_rseq (in_kernel rseq_off_launch)) = 27%nat
  /\ launch_sp_hi (Z_to_bv 64 (va_stack_top Sv48)) ordinary_launch
     = (va_stack_top Sv48 - 528)%Z
  /\ launch_sp_hi (Z_to_bv 64 (va_stack_top Sv48)) rseq_off_launch
     = (va_stack_top Sv48 - 496)%Z.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** And that stack pointer is a launch the model admits: the entry
    [Run.launch_entry_va] computes for the rseq-off input sits at
    [STACK_TOP - 496], and [Run.valid_entry] holds of it.  No input
    [Run.valid_input] admits reaches it with [CONFIG_RSEQ] on, so the
    freed flag is what keeps these launches inside the published
    statements. *)
Example rseq_off_launch_entry_valid :
  forall segs pc ph brk rnd vd,
  valid_brk segs brk ->
  bv_unsigned (en_sp (launch_entry_va Sv48 rseq_off_launch brk rnd vd))
    = (va_stack_top Sv48 - 496)%Z
  /\ valid_entry (mkImage segs pc ph)
       (launch_entry_va Sv48 rseq_off_launch brk rnd vd) rseq_off_launch.
Proof.
  intros segs pc ph brk rnd vd Hbrk.
  split.
  - cbn [launch_entry_va en_sp]. vm_compute. reflexivity.
  - unfold valid_entry.
    replace (in_va_size rseq_off_launch) with Sv48 by reflexivity.
    apply launch_entry_va_valid; try exact Hbrk.
    + exact (valid_input_argv _ rseq_off_launch_valid).
    + exact (valid_input_envp _ rseq_off_launch_valid).
    + exact (valid_input_launch _ rseq_off_launch_valid).
Qed.
