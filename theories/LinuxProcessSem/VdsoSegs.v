(** * LinuxProcessSem.VdsoSegs — the permissions of the pair [execve] installs,
      and the address the auxv names for its text

    [Run.vdso_segments] builds the vDSO's two mappings with [seg_perms] of
    ["r--"], so neither is executable and neither is writable.  A proof about
    a run's segment list reaches for that fact whenever it has to say what
    the appended pair can do — the W^X and NX side conditions over
    [Run.run_segments] are the usual callers — and reaching for it otherwise
    means making [Run.vdso_segments] transparent at the use site, which the
    note under [Run.vdso_segments] says costs a [vm_compute] of the measured
    image.  Stated here, the cost is paid once.

    The same holds for where the text is: [launch_auxv_sysinfo_ehdr_is_the_text]
    says the AT_SYSINFO_EHDR the launch publishes is the base of the text
    segment [Run.vdso_segments] places, for every launch.

    [Run.vdso_segments] is [Global Opaque]; the [Local Transparent] below is
    confined to this file.

    PURE ADDITION: this file changes no existing statement. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType StackLayout Vdso State Run.
Import ListNotations.
Open Scope bv_scope.

Local Transparent vdso_segments.

(** Neither mapping of the pair is executable.  A jump into the VVAR pages
    is an NX fault; a jump into the TEXT is not, and the difference matters:
    [RiscvSemantics.fetch_failure] tests [vdso_text_at] ahead of any
    permission (RiscvSemantics.v:1158-1170) and answers [MachineUnmodeled],
    the model declining, rather than [MachineFault].  [Run.sstep]'s vDSO
    arms override that at an exported ENTRY.  So this lemma is about the
    PERMISSION the pair carries, not about what a fetch there does. *)
Lemma vdso_segments_nx : forall kb (sp mbase : word) s,
  In s (vdso_segments kb sp mbase) -> seg_executable s = false.
Proof.
  intros kb sp mbase s H. unfold vdso_segments in H. cbn zeta in H.
  destruct (_ <? page_size)%Z in H; [destruct H|].
  destruct H as [<- | [<- | []]]; reflexivity.
Qed.

(** And neither is writable: a store into either is [RiscvSemantics]'s
    SIGSEGV. *)
Lemma vdso_segments_nw : forall kb (sp mbase : word) s,
  In s (vdso_segments kb sp mbase) -> seg_writable s = false.
Proof.
  intros kb sp mbase s H. unfold vdso_segments in H. cbn zeta in H.
  destruct (_ <? page_size)%Z in H; [destruct H|].
  destruct H as [<- | [<- | []]]; reflexivity.
Qed.

(** AT_SYSINFO_EHDR NAMES THE TEXT THE LAUNCH MAPS.  For every input,
    stack pointer and mmap base, the address [Run.launch_auxv] publishes
    as AT_SYSINFO_EHDR is the base of the [SegVdsoText] segment
    [Run.vdso_segments] places, whenever it places one: both read
    [Run.vdso_text_base].  A C library that looks the vDSO up through the
    auxiliary vector (musl's [__vdsosym]) therefore reads the text the run
    maps, on every launch, including those where [sp - stack_max_size] is
    below the mmap base and the pair sits below the base rather than
    directly under it.  [tests/VdsoAuxvBase.v] computes both on one launch
    of each kind. *)
Lemma launch_auxv_sysinfo_ehdr_is_the_text : forall inp (sp mbase : word) s,
  In s (vdso_segments (in_kernel inp) sp mbase) ->
  seg_kind s = SegVdsoText ->
  bv_unsigned (la_sysinfo_ehdr (launch_auxv inp sp mbase)) = Z.of_N (seg_base s).
Proof.
  intros inp sp mbase s H Hk. unfold vdso_segments in H. cbn zeta in H.
  destruct (_ <? page_size)%Z in H; [destruct H|].
  destruct H as [<- | [<- | []]]; [cbn in Hk; discriminate Hk|].
  cbn [seg_base la_sysinfo_ehdr launch_auxv].
  pose proof (bv_unsigned_in_range 64
                (vdso_text_base (in_kernel inp) sp mbase)) as Hr.
  rewrite Z2N.id; [reflexivity | lia].
Qed.
