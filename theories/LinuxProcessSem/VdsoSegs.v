(** * LinuxProcessSem.VdsoSegs — the permissions of the pair [execve] installs

    [Run.vdso_segments] builds the vDSO's two mappings with [seg_perms] of
    ["r--"], so neither is executable and neither is writable.  A proof about
    a run's segment list reaches for that fact whenever it has to say what
    the appended pair can do — the W^X and NX side conditions over
    [Run.run_segments] are the usual callers — and reaching for it otherwise
    means making [Run.vdso_segments] transparent at the use site, which
    Run.v:308-322 says costs a [vm_compute] of the measured image.  Stated
    here, the cost is paid once.

    [Run.vdso_segments] is [Global Opaque]; the [Local Transparent] below is
    confined to this file.

    PURE ADDITION: this file changes no existing statement. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType Vdso State Run.
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
