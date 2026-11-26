(** * grep-args-ns — shared spec definitions and image-level facts.

    PROOF-SIDE FILE (not part of the trusted specification).  The shared
    observable-behavior spec ([grep_bufs] and friends) and the
    binary-independent arithmetic/image lemmas, split out of [Proof.v] so
    that the two binaries' stepping files compile separately.  See
    [Proof.v]'s header for the shape of the whole proof. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec WallSim StepTac MuslStrlen StreamSim StoreOk.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import grep_args_ns_code.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** [WallSim.to_wallexit] at fd 1, in [CatSim.to_wexit]'s argument order.
    [WallSim] states the same abbreviation inside its [WithFP1] section,
    so it ends with that section. *)
Abbreviation wexit1 segs ms bufs code :=
  (to_wallexit segs (Z_to_bv 64 1) bufs code ms).

(* ######################################################################### *)
(* The shared observable-behavior spec                                       *)
(* ######################################################################### *)

(* [byte_at] (byte [k] of string [s] as laid out in memory, [s] then a
   NUL) now lives in CatExec. *)

(** Do the bytes of [p] occur in [hay] starting at index [k]? *)
Fixpoint prefix_eqb (p : list byte) (hay : list byte) (k : nat) : bool :=
  match p with
  | [] => true
  | b :: p' => (bv_eqb (byte_at hay k) b && prefix_eqb p' hay (S k))%bool
  end.

(** Scan positions k, k+1, ... (fuel-bounded). *)
Fixpoint scan_from (hay pat : list byte) (k fuel : nat) : bool :=
  match fuel with
  | O => false
  | S f => (prefix_eqb pat hay k || scan_from hay pat (S k) f)%bool
  end.

(** [pat] occurs as a substring of [hay]. *)
Definition contains_b (hay pat : list byte) : bool :=
  if (length pat =? 0)%nat then true
  else if (length hay <? length pat)%nat then false
  else scan_from hay pat 0 (S (length hay - length pat)).

(** Write buffers one argument contributes: a matching argument is written
    then a newline; both binaries skip the zero-length write of an empty
    matching argument, so it contributes only the newline. *)
Definition arg_bufs (pat a : list byte) : list (list byte) :=
  if contains_b a pat
  then match a with [] => [[Z_to_bv 8 10]] | _ => [a; [Z_to_bv 8 10]] end
  else [].

Definition grep_bufs (pat : list byte) (args : list (list byte)) : list (list byte) :=
  flat_map (arg_bufs pat) args.

(** Every buffer the spec writes is short enough for the model to
    transfer it in one [write] ([CatSim.buf_modeled]): a matching argument
    is written whole, and [Run.valid_argv] caps a single argv string at
    131071 bytes — one under [Uaccess.rw_bytes_max] — while the only other
    buffer is the one-byte newline. *)
Lemma arg_bufs_modeled : forall pat a,
  (Z.of_nat (length a) <= 131071)%Z -> bufs_modeled (arg_bufs pat a).
Proof.
  intros pat a Ha. unfold arg_bufs.
  destruct (contains_b a pat); [| apply Forall_nil].
  assert (Hnl : buf_modeled [Z_to_bv 8 10])
    by (unfold buf_modeled, rw_bytes_max; cbn [length]; lia).
  destruct a as [|b a'].
  - apply Forall_cons; [exact Hnl | apply Forall_nil].
  - apply Forall_cons; [| apply Forall_cons; [exact Hnl | apply Forall_nil]].
    unfold buf_modeled, rw_bytes_max. lia.
Qed.

Lemma grep_bufs_modeled : forall pat args,
  Forall (fun a => (Z.of_nat (length a) <= 131071)%Z) args ->
  bufs_modeled (grep_bufs pat args).
Proof.
  intros pat args Hargs. unfold grep_bufs, bufs_modeled.
  apply Forall_flat_map.
  induction Hargs as [| a args' Ha Hargs' IH]; [apply Forall_nil |].
  apply Forall_cons; [apply arg_bufs_modeled; exact Ha | exact IH].
Qed.

(** [Run.valid_argv]'s per-argument bound survives dropping the leading
    program name and pattern. *)
Lemma Forall_skipn_argv : forall (P : list byte -> Prop) n args,
  Forall P args -> Forall P (skipn n args).
Proof.
  intros P n. induction n as [|n IH]; intros args H; [exact H |].
  destruct args as [|a args']; [apply Forall_nil |].
  cbn [skipn]. apply IH. inversion H; assumption.
Qed.

(* ######################################################################### *)
(* Shared small facts                                                        *)
(* ######################################################################### *)

(* nth_lt_byte_at, byte_at_len, byte_at_nz, byte_at_bound, and
   valid_argv_len/str_len/str_nz/str_bytes now live in CatExec. *)

(** Close a CLOSED word/byte equation by unsigned comparison. *)


(** [bv_unsigned] of a byte zero-extended into a word. *)


(* ######################################################################### *)
(* musl's word-at-a-time zero-byte test, the [bytes_le_to_Z] bridge, and the  *)
(* readability of the (NUL-straddling) 8-byte load now live in                *)
(* Common/MuslStrlen.v (imported above): module [HZ] ([Tz_nozero] /           *)
(* [Tz_haszero], the has-zero test proved exact), [v_haszero] /               *)
(* [zb_of_bytes] / [bytes_le_to_Z_range] (machine word <-> [Z] bytes), and    *)
(* [bsb_len_lower] / [total_arg_bytes_firstn_S] / [read_word_stack] /         *)
(* [argv_word_readable] (why reading up to 7 bytes PAST the NUL of an argv    *)
(* string never faults -- see that file's header for the warning that the     *)
(* argument does NOT transfer to a heap/brk/mmap buffer).                     *)
(* ######################################################################### *)



Lemma of_nat_word_to_nat : forall w : word,
  Z.of_nat (word_to_nat w) = bv_unsigned w.
Proof.
  intro w. unfold word_to_nat. pose proof (u64_range w). lia.
Qed.

Lemma v_slli3_nat : forall i : nat, (Z.of_nat i <= 1024)%Z ->
  v_slli (nat_to_word i) 3 = Z_to_bv 64 (8 * Z.of_nat i).
Proof.
  intros i Hi. apply bv_eq. rewrite Z_to_bv_unsigned.
  rewrite v_slli_3 by (rewrite u_ntw by lia; lia).
  rewrite u_ntw by lia.
  rewrite bv_wrap_small; [reflexivity|].
  change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Lemma word_to_nat_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  word_to_nat (nat_to_word n) = n.
Proof. intros n Hn. unfold word_to_nat. rewrite u_ntw by lia. lia. Qed.

(** [v_add] variants of the [nat_to_word] merge laws ([v_add] is the
    wrapping [bv] add by conversion, but [rewrite] keys on the head). *)
Lemma v_add_ntw_merge : forall (a : word) (m k : nat),
  v_add (a + nat_to_word m) (nat_to_word k) = a + nat_to_word (m + k).
Proof.
  intros a m k.
  change (v_add (a + nat_to_word m) (nat_to_word k))
    with (a + nat_to_word m + nat_to_word k).
  apply nat_to_word_add_merge.
Qed.

Lemma v_add_ntw : forall m k : nat,
  v_add (nat_to_word m) (nat_to_word k) = nat_to_word (m + k).
Proof.
  intros m k.
  change (v_add (nat_to_word m) (nat_to_word k))
    with (nat_to_word m + nat_to_word k).
  apply nat_to_word_merge.
Qed.

(* [c_eq_0_of_u] lives in Common/PropExec.v (imported above). *)

(** Byte comparison commutes with the zero-extension the machine loads
    bytes at. *)
Lemma bv_eqb_zext : forall b c : byte,
  bv_eqb (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (bv_unsigned c)) = bv_eqb b c.
Proof.
  intros b c. unfold bv_eqb at 1. rewrite !u_zext8. reflexivity.
Qed.

(** Sealed [Z.of_nat] equation for [valid_envp]'s large literal
    (companion of CatExec's [of_nat_131071]/[of_nat_2097152]). *)

(* ######################################################################### *)
(* Step-chaining tactics                                                     *)
(* ######################################################################### *)

(* [norm_pc]/[stepi]/[stepiv]/[stepj]/[sp_norm]/[wlit]/[wlits] now live in
   Common/StepTac.v (imported above). *)

(* ######################################################################### *)
(* sp-independent helper lemmas                                              *)
(* ######################################################################### *)

(* [v_addi_m16]/[v_addi_m64] (literal negative-immediate instances of
   [SeqExec.v_addi_m]) now live in Common/StepTac.v, in the canonical
   [Z_to_bv 64 (...)] form. *)

(* [sp_norm] now lives in Common/StepTac.v (imported above). *)

(* [step_sd_at] (value-precise store, pre-normalized address) lives in Common/SeqExec.v. *)

(** A store target above the read-only segments passes the
    read-only-avoidance check (the rw data segment is exempt).  After the
    [-z separate-code] relink there are THREE of them — r-- headers
    [0x10000, 0x11000), r-x text [0x11000, 0x12000) and r-- .rodata
    [0x12000, 0x13000) — so the rw- data segment, and the first writable
    address, start at 0x13000. *)
Lemma source_avoids_ro : forall (a : word) (n : Z), (0x13000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs source_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  unfold source_segs, SourceMemImage_loaded_segments, range_avoids_ro_segs.
  cbn [forallb].
  change (seg_writable SourceMemImage_segment_000) with false.
  change (seg_writable SourceMemImage_segment_001) with false.
  change (seg_writable SourceMemImage_segment_002) with false.
  change (seg_writable SourceMemImage_segment_003) with true.
  change (Z.of_N (seg_base SourceMemImage_segment_000)
          + Z.of_N (seg_size SourceMemImage_segment_000))%Z with 0x11000%Z.
  change (Z.of_N (seg_base SourceMemImage_segment_001)
          + Z.of_N (seg_size SourceMemImage_segment_001))%Z with 0x12000%Z.
  change (Z.of_N (seg_base SourceMemImage_segment_002)
          + Z.of_N (seg_size SourceMemImage_segment_002))%Z with 0x13000%Z.
  assert (H0 : Z.ltb (bv_unsigned a) 0x11000 = false) by (apply Z.ltb_ge; lia).
  assert (H1 : Z.ltb (bv_unsigned a) 0x12000 = false) by (apply Z.ltb_ge; lia).
  assert (H2 : Z.ltb (bv_unsigned a) 0x13000 = false) by (apply Z.ltb_ge; lia).
  rewrite H0, H1, H2. rewrite !andb_false_r.
  cbn [negb orb andb]. reflexivity.
Qed.

(** The source image's WRITABLE window: the rw- segment covers
    [0x13000, 0x14000) and the snapshot carries a byte for every address in
    it (.bss is zero-filled in the .hex), so [wview] is defined there
    whatever the overlay holds — a store into .data/.bss needs no
    prior write.  That is the [store_ok] side condition machine stores
    now carry; stack targets go through the RLIMIT_STACK window
    ([solve_store_ok]) instead. *)
Lemma source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_store_ok : forall (m : word -> option byte) (a : word) (n : nat),
  (0x13000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x14000)%Z ->
  store_ok source_segs m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply store_ok_window with (base := 0x13000%Z) (hi := 0x14000%Z);
    [ | | | exact source_data_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.


Lemma target_avoids_ro : forall (a : word) (n : Z), (0x1002000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs target_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  unfold target_segs, TargetMemImage_loaded_segments.
  apply range_avoids_two; apply Z.ltb_ge.
  - change (Z.of_N (seg_base TargetMemImage_segment_000)
            + Z.of_N (seg_size TargetMemImage_segment_000))%Z with 0x1001000%Z.
    lia.
  - change (Z.of_N (seg_base TargetMemImage_segment_001)
            + Z.of_N (seg_size TargetMemImage_segment_001))%Z with 0x1002000%Z.
    lia.
Qed.

(* [total_arg_bytes_firstn_S], [bsb_len_lower], [bsb_word_k] and
   [read_word_stack] now live in Common/MuslStrlen.v. *)

(** Argv string [k] ends at or below [State.TASK_SIZE]: it ends below the
    stack VMA's end [ed_top] (the arithmetic of [SeqExec.argv_ptr_bounds]),
    and under Sv48 [ed_top] is at most [sp_window_hi], which is
    [TASK_SIZE].  A [write] of the string passes [access_okb]. *)
Lemma argv_str_task : forall inp mbase (sp brk : word) draw,
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  forall k, (k < length (in_argv inp))%nat ->
  (bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
   + Z.of_nat (length (nth k (in_argv inp) [])) <= TASK_SIZE)%Z.
Proof.
  intros inp mbase sp brk draw Hlau k Hk.
  pose proof (launch_string_base_arith Sv48 inp mbase sp brk draw Hlau) as HA.
  pose proof (u_cat_string_base Sv48 inp mbase sp brk draw Hlau) as Hu.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  pose proof (total_arg_bytes_firstn_within (in_argv inp) k Hk) as Hw.
  assert (Htop : (bv_unsigned (ed_top draw) <= TASK_SIZE)%Z).
  { destruct Hlau as ((_ & Ht & _) & _ & _). cbn [va_stack_top] in Ht.
    unfold TASK_SIZE. unfold sp_window_hi in Ht. lia. }
  assert (Hstr : (Z.of_nat (total_arg_bytes_nat (firstn k (in_argv inp)))
                  + Z.of_nat (length (nth k (in_argv inp) [])) + 1
                  <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)))%Z).
  { unfold launch_string_bytes. rewrite (length_flatten_strings (in_argv inp)). lia. }
  rewrite (cat_argv_ptr_offset (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k Hk).
  rewrite word_add_nat, Hu.
  rewrite u_Z2bv by lia.
  lia.
Qed.
