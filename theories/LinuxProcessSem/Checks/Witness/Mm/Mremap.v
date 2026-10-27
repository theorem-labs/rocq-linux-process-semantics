(** * LinuxProcessSem.Checks.Witness.Mm.Mremap — the mremap (216) witnesses, and their proofs

    Mirrors [Sys/Mm/Mremap.v], which answers to Linux [mm/mremap.c]:
    this file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

Definition mremap_witness (old old_size new_size flags : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE)
  then Unmodeled
  else if negb (Z.eqb (bv_unsigned old mod page_size) 0)
  then ret_outcome (errno_ret EINVAL) m
  else if page_align_is0_b new_size
  then ret_outcome (errno_ret EINVAL) m
  else if page_align_is0_b old_size
  then Unmodeled
  else
    let old_nZ := page_round_up_Z (bv_unsigned old_size) in
    let new_nZ := page_round_up_Z (bv_unsigned new_size) in
    let old_n := Z_to_bv 64 old_nZ in
    if negb (mremap_source_b (m_vmmaps m) old old_n old_nZ
             && mremap_backing_uniform_b m old old_n)
    then (if vdso_byte (m_vdso m) (bv_unsigned old)
          then (if Z.eqb old_nZ new_nZ then ret_outcome old m
                else if (old_nZ <? new_nZ)%Z then ret_outcome (errno_ret EFAULT) m
                else if vdso_split (m_vdso m) (bv_unsigned old + new_nZ)
                          (bv_unsigned old + old_nZ)
                then ret_outcome (errno_ret EINVAL) m
                else Unmodeled)
          else Unmodeled)
    else if Z.eqb old_nZ new_nZ
    then ret_outcome old m
    else ret_outcome (errno_ret witness_errno) m.

Lemma mremap_witness_ok : forall old old_size new_size flags i m,
  mremap_spec old old_size new_size flags i m
    (mremap_witness old old_size new_size flags m).
Proof.
  intros. unfold mremap_spec, mremap_witness.
  destruct (negb (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE)) eqn:Hshape;
    [apply unmodeled_intro|].
  destruct (negb (Z.eqb (bv_unsigned old mod page_size) 0)) eqn:Halign;
    [apply pure_ok|].
  destruct (page_align_is0_b new_size) eqn:Hnew; [apply pure_ok|].
  destruct (page_align_is0_b old_size) eqn:Hold; [apply unmodeled_intro|].
  eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
  destruct (negb (mremap_source_b (m_vmmaps m) old
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
    (page_round_up_Z (bv_unsigned old_size))
    && mremap_backing_uniform_b m old
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) eqn:Hsrc.
  { destruct (vdso_byte (m_vdso m) (bv_unsigned old)) eqn:Hvb;
      [|apply unmodeled_intro].
    cbv beta iota. unfold mremap_vdso_source.
    destruct (Z.eqb (page_round_up_Z (bv_unsigned old_size))
                    (page_round_up_Z (bv_unsigned new_size))); [apply pure_ok|].
    destruct ((page_round_up_Z (bv_unsigned old_size)
               <? page_round_up_Z (bv_unsigned new_size))%Z); [apply pure_ok|].
    destruct (vdso_split (m_vdso m)
                (bv_unsigned old + page_round_up_Z (bv_unsigned new_size))
                (bv_unsigned old + page_round_up_Z (bv_unsigned old_size)));
      [apply pure_ok | apply unmodeled_intro]. }
  destruct (Z.eqb (page_round_up_Z (bv_unsigned old_size))
                  (page_round_up_Z (bv_unsigned new_size))) eqn:Heq;
    [apply pure_ok|].
  apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
Qed.
