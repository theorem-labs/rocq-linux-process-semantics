(** * modprint-ns: instantiating the ADDRESS-PARAMETRIC musl [write]
      summary at this binary's addresses.

    PROTOTYPE / EXPLORATION.  PROOF-SIDE FILE.

    [modprint_ns_source.v] walks musl's [write] wrapper, [__syscall_cp],
    the [ecall] and [__syscall_ret] by hand: the region 0x11098..0x110d4
    costs ~90 lines of that file, and the same ~90 lines reappear in
    [cat1024_ns], [conditional_bug_ns], [grep_args_ns], [tail1_ns],
    [oob_read_bug_ns], [brk_rev_ns], [mmap_upper_ns] and
    [alloc_join_ns] at each binary's own addresses.

    [Common/MuslCall.v] proves that region ONCE, over an abstract load
    address.  All this file does is name the load address (0x11098) and
    hand over the binary's 26 [SF_*] fetch lemmas.  The whole call —
    including the syscall — then collapses to a single [eapply].

    A run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The summary is instantiated over [source_segs ++ vt] for any
    appended [vt], each fetch lemma carried there by
    [RunSegmentsLift.fetch_word_app], and the write's buffer range
    carries the [access_okb] premise [MuslCall.musl_write_wexit] takes. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare MuslCall RunSegmentsLift.
From LinuxProcessSemantics.Examples.modprint_ns Require Import modprint_ns_code.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The load address of the [write]/[__syscall_cp]/[__syscall_ret] blob
    in this binary. *)
Definition WB : word := 0x11098.

(** Rebase one generated fetch lemma onto [at_ WB d].  The address
    equation is between CLOSED words, so [bveq] settles it. *)
Lemma fetch_at : forall segs (b : word) (d : Z) (a : word) w,
  at_ b d = a -> fetch_word segs a = Some w -> fetch_word segs (at_ b d) = Some w.
Proof. intros segs b d a w Ha Hf. rewrite Ha. exact Hf. Qed.

Ltac fat SF :=
  refine (fetch_at _ _ _ _ _ _ (fetch_word_app _ _ _ _ SF)); unfold at_, WB; bveq.

Section RunList.
Context {fx : FPState}.

(** The segments appended after the image's own: the vDSO pair, at the
    run's list. *)
Variable vt : list Segment.

Lemma f00 : fetch_word (source_segs ++ vt) (at_ WB 0x00) = Some Wsp16m. Proof. fat SF_11098. Qed.
Lemma f04 : fetch_word (source_segs ++ vt) (at_ WB 0x04) = Some Wmv_a3a2. Proof. fat SF_1109c. Qed.
Lemma f08 : fetch_word (source_segs ++ vt) (at_ WB 0x08) = Some Wli_a6_0. Proof. fat SF_110a0. Qed.
Lemma f0c : fetch_word (source_segs ++ vt) (at_ WB 0x0c) = Some Wmv_a2a1. Proof. fat SF_110a4. Qed.
Lemma f10 : fetch_word (source_segs ++ vt) (at_ WB 0x10) = Some Wli_a5_0. Proof. fat SF_110a8. Qed.
Lemma f14 : fetch_word (source_segs ++ vt) (at_ WB 0x14) = Some Wmv_a1a0. Proof. fat SF_110ac. Qed.
Lemma f18 : fetch_word (source_segs ++ vt) (at_ WB 0x18) = Some Wli_a4_0. Proof. fat SF_110b0. Qed.
Lemma f1c : fetch_word (source_segs ++ vt) (at_ WB 0x1c) = Some Wli_a0_64. Proof. fat SF_110b4. Qed.
Lemma f20 : fetch_word (source_segs ++ vt) (at_ WB 0x20) = Some Wsd_ra8. Proof. fat SF_110b8. Qed.
Lemma f24 : fetch_word (source_segs ++ vt) (at_ WB 0x24) = Some Wjal_cp. Proof. fat SF_110bc. Qed.
Lemma f28 : fetch_word (source_segs ++ vt) (at_ WB 0x28) = Some Wld_ra8. Proof. fat SF_110c0. Qed.
Lemma f2c : fetch_word (source_segs ++ vt) (at_ WB 0x2c) = Some Wsp16p. Proof. fat SF_110c4. Qed.
Lemma f30 : fetch_word (source_segs ++ vt) (at_ WB 0x30) = Some Wj4. Proof. fat SF_110c8. Qed.
Lemma f34 : fetch_word (source_segs ++ vt) (at_ WB 0x34) = Some Wlui_a5. Proof. fat SF_110cc. Qed.
Lemma f38 : fetch_word (source_segs ++ vt) (at_ WB 0x38) = Some Wbltu. Proof. fat SF_110d0. Qed.
Lemma f3c : fetch_word (source_segs ++ vt) (at_ WB 0x3c) = Some Wret. Proof. fat SF_110d4. Qed.
Lemma f6c : fetch_word (source_segs ++ vt) (at_ WB 0x6c) = Some Wmv_a7a0. Proof. fat SF_11104. Qed.
Lemma f70 : fetch_word (source_segs ++ vt) (at_ WB 0x70) = Some Wmv_a0a1. Proof. fat SF_11108. Qed.
Lemma f74 : fetch_word (source_segs ++ vt) (at_ WB 0x74) = Some Wmv_a1a2. Proof. fat SF_1110c. Qed.
Lemma f78 : fetch_word (source_segs ++ vt) (at_ WB 0x78) = Some Wmv_a2a3. Proof. fat SF_11110. Qed.
Lemma f7c : fetch_word (source_segs ++ vt) (at_ WB 0x7c) = Some Wmv_a3a4. Proof. fat SF_11114. Qed.
Lemma f80 : fetch_word (source_segs ++ vt) (at_ WB 0x80) = Some Wmv_a4a5. Proof. fat SF_11118. Qed.
Lemma f84 : fetch_word (source_segs ++ vt) (at_ WB 0x84) = Some Wmv_a5a6. Proof. fat SF_1111c. Qed.
Lemma f88 : fetch_word (source_segs ++ vt) (at_ WB 0x88) = Some Wecall. Proof. fat SF_11120. Qed.
Lemma f8c : fetch_word (source_segs ++ vt) (at_ WB 0x8c) = Some Wret. Proof. fat SF_11124. Qed.
Lemma f90 : fetch_word (source_segs ++ vt) (at_ WB 0x90) = Some Wj_cpc. Proof. fat SF_11128. Qed.

(** The whole [write(1, out, 2)] call of [main], as one lemma: from the
    wrapper's entry to the return into [main] at 0x11034, with the write
    event already accounted for.

    Compare [modprint_ns_source.v] lines "musl write" .. "back in main":
    ~90 lines of hand-stepped chain, replaced by the [eapply] below. *)
Lemma modprint_write_call :
  forall (regs : bvmap 5 word) (mem : word -> option byte)
         (sp0 buf : word) (out : list byte)
         (bufs : list (list byte)) (code : word),
  getr regs 1 = (0x11034 : word) ->
  getr regs 2 = sp0 ->
  getr regs 10 = Z_to_bv 64 1 ->
  getr regs 11 = buf ->
  getr regs 12 = Z_to_bv 64 2 ->
  RiscvSemantics.store_ok (source_segs ++ vt) mem (at_ sp0 (-8)) 8%nat = true ->
  (bv_unsigned (at_ sp0 (-8)) + 8 <= 2^64)%Z ->
  rdn (source_segs ++ vt)
      (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 (0x11034 : word)))
      buf 2%nat = Some out ->
  (* the range [vfs_write]'s [access_ok] accepts *)
  access_okb buf (bv_unsigned (Z_to_bv 64 2)) = true ->
  (forall regs' n, (1 <= n)%nat -> (n <= length out)%nat ->
     getr regs' 1 = (0x11034 : word) ->
     getr regs' 2 = sp0 ->
     getr regs' 10 = len_word (firstn n out) ->
     to_wexit (source_segs ++ vt)
       (mkst regs' (0x11034 : word)
          (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 (0x11034 : word)))
          (seg_rom (source_segs ++ vt)))
       bufs code) ->
  to_wexit (source_segs ++ vt)
    (mkst regs (0x11098 : word) mem (seg_rom (source_segs ++ vt)))
    (out :: bufs) code.
Proof.
  intros regs mem sp0 buf out bufs code H1 H2 H10 H11 H12 Hok Hnw Hread Hacc Hcont.
  replace (0x11098 : word) with (at_ WB 0x00) by (unfold at_, WB; bveq).
  eapply (musl_write_wexit (source_segs ++ vt) WB
            f00 f04 f08 f0c f10 f14 f18 f1c f20 f24 f28 f2c f30 f34 f38 f3c f6c f70 f74 f78 f7c f80 f84 f88 f8c f90
            regs mem (seg_rom (source_segs ++ vt)) (0x11034 : word) sp0 buf
            (Z_to_bv 64 2) out bufs code);
    try assumption.
  - reflexivity.
  - apply ret_ok_even. vm_compute. reflexivity.
  - (* [at_ WB 0x28] is 0x110c0, the wrapper's own return point *)
    apply ret_ok_even. unfold at_, WB. vm_compute. reflexivity.
  - rewrite u_Z2bv by lia. lia.
  - (* nonemptiness: the buffer read back has length 2 *)
    rewrite (rdn_length _ _ _ _ _ Hread). lia.
Qed.

End RunList.
