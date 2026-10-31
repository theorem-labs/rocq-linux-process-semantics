(* Written by the OSS-Fuzz proof collaborators. *)
(** * AsanNodesStartXInit — XEnvScan / XPnScan / XLayout for ANY class invariant [SINV]
      implying AsanInit's concrete [SINV0] (e.g. SINV0
      itself, the argument-leaf SINV1, the main-phase SINVm), with AsanInit's [argH0],
      for ANY image (segs, A, ph) given the two loops' code facts. *)

(* The entry draw ([Run.en_draw]) gives the AT_RANDOM bytes (= at_random_bytes (ed_random draw)) and, in [ed_top], the stack VMA's end; the auxv is 29 pairs / 464 bytes ([StackLayout.auxv_size] under CONFIG_RSEQ) and AT_HWCAP is its eleventh pair; the mapped image is [Run.entry_stack_image], Linux's whole block from sp to [ed_top]. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape.
From LinuxProcessSemantics.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From LinuxProcessSemantics.Common Require Import AsanNodesAux AsanStartLoops AsanNodesStartX.
From LinuxProcessSemantics.Common Require Import AsanCeil.  (* the zero-draw hypothesis AsanInit's Section carries *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GenericInit.
  (** the image *)
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  (** the code of the two loops *)
  Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
  Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
  Hypothesis Fe1 : fetch_word segs (Z_to_bv 64 (x_envscan A)) = Some we1.
  Hypothesis Fe2 : fetch_word segs (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
  Hypothesis Fe3 : fetch_word segs (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
  Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
  Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
  Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
  Hypothesis Fp0 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
  Hypothesis Fp1 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
  Hypothesis Fp2 : fetch_word segs (Z_to_bv 64 (x_pnscan A)) = Some wp2.
  Hypothesis Fp3 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
  Hypothesis Fp4 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
  Hypothesis Ep : is_ecall wp0 = false /\ is_ecall wp1 = false /\ is_ecall wp2 = false /\ is_ecall wp3 = false /\ is_ecall wp4 = false.
  Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  (** the run.  [apc], [mbase], [gid], [groups] and [net] are here because the
      auxv — hence the stack image AsanInit's [SINV0] speaks about — reads
      AT_ENTRY, AT_SYSINFO_EHDR and AT_GID/AT_EGID. *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* the entry draw [Run.en_draw]; ed_random = the AT_RANDOM bytes, ed_top = the stack VMA's end *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Variable uid gid : word.
  Variable hw : word.   (* AT_HWCAP *)
  Variable groups : list word.
  Variable net : NetQueue.

  Let INP := inp argv envp fs stdin uid gid hw groups net.
  Let entryw := Z_to_bv 64 (Z.of_N apc).

  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (** AsanInit's Section carries these too, and Rocq generalises each of its
      lemmas over every hypothesis its proof term reads, so they must be here
      for [eassumption] to discharge them. *)
  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* from valid_entry *)
  Hypothesis Hlaunch : valid_launch INP.             (* from valid_input *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.  (* valid_entry's fifth conjunct *)

  (** the class invariant: anything implying SINV0 and stable like it *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M ->
    SINV0 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  Let rseq := kb_rseq (in_kernel INP).
  Let execfn := in_execfn INP.
  Let top := ed_top rdraw.
  (** argv[0]: the top of the AT_RANDOM bytes plus the [arch_align_stack] pad.
      It WAS [usp + 8*argc + 8*envc + 184]. *)
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.
  Lemma inp_argv' : in_argv INP = argv.   Proof. reflexivity. Qed.
  Lemma inp_envp' : in_envp INP = envp.   Proof. reflexivity. Qed.

  (** AsanInit's [STR0] ([usp + C + pad]) and AsanNodesStartX's
      ([usp + cat_string_off]) are the same number *)
  Lemma str0_split : STR0 = usp + Z.of_nat (block_head_size rseq argv envp)
                                 + Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  Proof. unfold STR0, cat_string_off. rewrite Nat2Z.inj_add. lia. Qed.

  (** what [SINV0] provides, in the form AsanNodesAux wants *)
  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E e_str0 = STR0.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (U1 : uE (E0 sp rdraw brk0 argv envp uid) e_envp = usp + 8 * argc + 16)
      by (unfold usp, argc; exact (u_e_envp ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net Hsp Hva Hve Hlau)).
    assert (U3 : uE (E0 sp rdraw brk0 argv envp uid) e_str0
                 = usp + Z.of_nat (block_head_size rseq argv envp)
                   + Z.of_nat (block_pad_len rseq sp top argv envp execfn))
      by (unfold usp, rseq, execfn, top; exact (u_e_str0 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net Hsp Hva Hve Hlau)).
    assert (U2 : uE (E0 sp rdraw brk0 argv envp uid) (EVar V_ENVC) = envc)
      by (unfold envc; exact (uE0_envc ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net Hsp Hva Hve Hlau)).
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev (E0 sp rdraw brk0 argv envp uid) n)
      by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *.
    rewrite (edenot_ev_agree NX0 E (E0 sp rdraw brk0 argv envp uid) e_envp eq_refl Hev7).
    rewrite (edenot_ev_agree NX0 E (E0 sp rdraw brk0 argv envp uid) e_str0 eq_refl Hev7).
    split; [exact U1|]. split; [|rewrite U3; symmetry; exact str0_split].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree NX0 E (E0 sp rdraw brk0 argv envp uid) (EVar V_ENVC) eq_refl Hev7).
    apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. left.
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (** the string area runs from argv[0] to the stack VMA's end, and argv[0]
      with its NUL is inside it ([AsanInit.s0_in_strings]), so the bytes the
      progname scan reads are hidden by [argH0] *)
  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. right.
    assert (HS0 : Z.of_nat (length (nth 0 argv [])) + 1
                  <= Z.of_nat (launch_string_bytes argv envp execfn))
      by (unfold execfn; apply (s0_in_strings apc sp rdraw argv envp Hva Hfit)).
    assert (HT : usp + Z.of_nat (block_head_size rseq argv envp)
                 + Z.of_nat (block_pad_len rseq sp top argv envp execfn)
                 + Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned top)
      (** [AsanInit.str0_hi] is QUALIFIED because [AsanNodesStartX] exports a
          lemma of the same name and is imported after [AsanInit], so the later
          import wins and the bare reference resolved to the wrong one: the two
          differ only in their first argument, so the mistake shows up as a type
          error far from its cause.  Same shape as the two copies of
          [AsanNodesMmLib.reserved_free_above] / [AsanNodesMmB.reserved_free_above]
          — two things that must agree with nothing to say so. *)
      by (unfold usp, rseq, execfn, top; apply (AsanInit.str0_hi apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net Hlau)).
    rewrite str0_split in Ha. unfold s0 in Ha.
    (** AsanInit's [argH0] carries the kernel build and the exec name INLINED
        ([State.default_kernel], [State.default_execfn]), because they are
        variable-free [Let]s of its Section; the hypotheses above carry them as
        projections of [INP].  The two are convertible, so [change] lines them
        up for [lia]. *)
    unfold rseq, execfn, top, usp in Ha, HT, HS0.
    change (in_kernel INP) with default_kernel in Ha, HT, HS0.
    change (in_execfn INP) with default_execfn in Ha, HT, HS0.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Theorem init_x_sound_envscan :
    x_stmt segs A NX0 LIMIT SINV (argH0 sp rdraw argv envp) FS0 XEnvScan.
  Proof.
    apply (x_sound_envscan segs A NX0 LIMIT SINV (argH0 sp rdraw argv envp) FS0
              SEGS_wx SEGS_in_hull HULL_ok SINV_frame
              we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
              ph INP mbase entryw sp brk0 rdraw);
      solve [ assumption | exact sp_lo | exact sp_hi
            | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 ].
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs A NX0 LIMIT SINV (argH0 sp rdraw argv envp) FS0 XPnScan.
  Proof.
    apply (x_sound_pnscan segs A NX0 LIMIT SINV (argH0 sp rdraw argv envp) FS0
              SEGS_wx SEGS_in_hull HULL_ok
              (argH0_high apc sp rdraw argv envp Hsp Hva) (argH0_agree sp rdraw argv envp)
              SINV_frame SINV_agree
              wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
              ph INP mbase entryw sp brk0 rdraw);
      solve [ assumption | exact sp_lo | exact sp_hi
            | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 ].
  Qed.

  Theorem init_x_sound_layout :
    x_stmt segs A NX0 LIMIT SINV (argH0 sp rdraw argv envp) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.
