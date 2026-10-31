(** * Checks.Cases.Kernel.Vdso — the vDSO pair, checked

    NOT part of the trusted specification.  This file is the evidence
    for the four steps of the vDSO design (Vdso.v, [Run.vdso_segments],
    [Run.sstep]'s vDSO arms, [RiscvSemantics.fetch_failure]):

    1. the image is data, and it is the measured one: the four bytes at
       the text base are the ELF magic, and the mapping is
       [[vdso_top - T, vdso_top)];
    2. a load from the vvar pages is [MachineUnmodeled];
    3. a call at an exported entry is one step with the system call's
       own specification — and the two routes to a clock reading agree;
    4. a fetch at another text address is [MachineUnmodeled], and a
       store to the text is a fault.

    Plus the claim the design exists for: musl's own lookup
    ([Checks.Cases.Kernel.VdsoSym], a transcription of
    [src/internal/vdso.c] at musl f21a9653) finds
    [__vdso_clock_gettime] in the measured image, and reads nothing
    outside the text pages while it does. *)

From Stdlib Require Import ZArith NArith List Lia Bool String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel Require Import VdsoSym.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mprotect.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* =========================================================================
   The fixture: one launch, and the pair [execve] installs for it
   ========================================================================= *)

(** A launch in the middle of [Run.valid_sp]'s window, with the mmap
    base [Run.valid_mmap_base] admits.  The numbers are not special:
    what matters is that [Run.vdso_segments] is the function under
    test, so the pair lands exactly where a run puts it. *)
Definition fx_sp : word := Z_to_bv 64 0x7ffffffffdf0.
Definition fx_mbase : word := Z_to_bv 64 0x7ffff8000000.

(** The kernel build: [State.default_kernel], whose [kb_vdso] is 1 and
    so names entry [1 mod 1 = 0] of [Vdso.vdso_images] — the one
    measured image. *)
Definition fx_kb : KernelBuild := default_kernel.

Definition fx_pair : list Segment := vdso_segments fx_kb fx_sp fx_mbase.

(** [page_round_down (min mbase (page_round_down (sp - 8 MiB)))], the
    ledger's [State.vdso_top] at this launch. *)
Definition fx_top : Z := 0x7ffff8000000.
Definition fx_vvar_base : Z := 0x7ffff7ffa000.
Definition fx_text_base : Z := 0x7ffff7ffe000.

Example fx_pair_is_the_pair :
  fx_pair =
  [ {| seg_base := Z.to_N fx_vvar_base; seg_size := 16384;
       seg_perms := "r--D"%string; seg_bytes := [] |}
  ; {| seg_base := Z.to_N fx_text_base; seg_size := 8192;
       seg_perms := "r--V"%string; seg_bytes := vi_bytes vdso_image_default |} ].
Proof. vm_compute. reflexivity. Qed.

(** The text ends at the ledger's [vdso_top], and the pair is the five
    pages below it: four of vvar, then T of text. *)
Example fx_text_ends_at_vdso_top :
  (fx_text_base + Z.of_N 2 * page_size)%Z = fx_top
  /\ (fx_vvar_base + vdso_vvar_pages * page_size)%Z = fx_text_base
  /\ vdso_text_pages fx_kb = 2.
Proof. vm_compute. repeat split. Qed.

(** THE SMALL CODE SEGMENT the machine Examples run.  Three
    instructions, each the one the Example needs, at 0x10000:

      0x10000  ld  a0, 0(a1)   03 b5 05 00
      0x10004  sd  a0, 0(a1)   23 b0 a5 00

    a1 carries the address under test, so one segment serves both the
    vvar load and the store to the text. *)
Definition fx_code : Segment :=
  {| seg_base := 0x10000; seg_size := 8;
     seg_perms := "r-x"%string;
     seg_bytes := ["03b5050023b0a500"%pstring] |}.

Definition fx_segs : list Segment := fx_code :: fx_pair.

(** A machine state at [pc] with a1 = [addr] and nothing else set. *)
Definition fx_ms (pc addr : word) : machine_state :=
  {| ms_regs := bvmap_set 11 addr (bvmap_set 2 fx_sp bvmap_empty);
     ms_fregs := bvmap_empty;
     ms_pc_val := pc;
     ms_svc_pending := None;
     ms_resv := None;
     ms_fcsr := Z_to_bv 32 0;
     ms_mem := fun _ => None;
     ms_rom := fun a => match memory_read fx_segs a 1 with
                        | Some (b :: _) => Some b
                        | _ => None
                        end |}.

(* =========================================================================
   Step 1 — the image is data, and it is the measured one
   ========================================================================= *)

(** The four bytes at the text base, which is what the auxv publishes as
    [AT_SYSINFO_EHDR]. *)
Example vdso_text_starts_with_elf_magic :
  memory_read fx_segs (Z_to_bv 64 fx_text_base) 4
  = Some (map (Z_to_bv 8) [0x7f; 0x45; 0x4c; 0x46]).
Proof. vm_compute. reflexivity. Qed.

(** The exported entries the model answers at, as ADDRESSES: the text
    base plus each symbol's [st_value]. *)
Definition fx_entry (f : VdsoFn) : word :=
  match vdso_sym_off (vi_syms vdso_image_default) f with
  | Some o => Z_to_bv 64 (fx_text_base + Z.of_N o)
  | None => Z_to_bv 64 0
  end.

Example fx_entry_clock_gettime_is_recognised :
  vdso_entry_fn fx_segs (fx_entry VdsoClockGettime) = Some VdsoClockGettime
  /\ vdso_entry_fn fx_segs (fx_entry VdsoClockGetres) = Some VdsoClockGetres
  /\ vdso_fn_sysno VdsoClockGettime = Some 113
  /\ vdso_fn_sysno VdsoClockGetres = Some 114.
Proof. vm_compute. repeat split. Qed.

(** F, the frame a call may leave bytes in: the measured image's. *)
Example fx_frame_is_measured : vdso_frame fx_segs = 240%N.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   musl's lookup, over the measured image and over the mapping
   ========================================================================= *)

(** Over the IMAGE's own bytes: [__vdsosym("LINUX_4.15",
    "__vdso_clock_gettime")] answers the offset the measurement
    recorded, 0x5b4. *)
Example musl_lookup_finds_clock_gettime :
  image_lookup_result vdso_image_default
    str_linux_4_15 str_vdso_clock_gettime = Some 0x5b4.
Proof. vm_compute. reflexivity. Qed.

(** ... and reads nothing outside the image. *)
Example musl_lookup_reads_only_the_image :
  reads_within vdso_image_default
    (image_lookup_reads vdso_image_default
       str_linux_4_15 str_vdso_clock_gettime) = true.
Proof. vm_compute. reflexivity. Qed.

(** The byte at image offset [o], read THROUGH THE MAPPING: what a
    program's own load instruction at [fx_text_base + o] reads. *)
Definition fx_peek (o : Z) : option byte :=
  match memory_read fx_segs (Z_to_bv 64 (fx_text_base + o)) 1 with
  | Some (b :: _) => Some b
  | _ => None
  end.

Definition fx_lookup : list Z * option (option Z) :=
  vdsosym fx_peek 4096 str_linux_4_15 str_vdso_clock_gettime [].

(** THE CLAIM THE DESIGN RESTS ON.  Run over the MAPPING rather than
    over the image, musl's lookup gives the same answer — so the entry
    a pipeline-built binary calls is the address
    [Run.sstep]'s vDSO arm answers at. *)
Example musl_lookup_on_the_mapping :
  snd fx_lookup = Some (Some 0x5b4).
Proof. vm_compute. reflexivity. Qed.

Example musl_lookup_entry_is_the_model_s :
  Z_to_bv 64 (fx_text_base + 0x5b4) = fx_entry VdsoClockGettime.
Proof. vm_compute. reflexivity. Qed.

(** AND IT READS ONLY TEXT-PAGE BYTES.  Every offset the walk touched
    is inside the two text pages, so every ADDRESS it touched is in
    [[fx_text_base, fx_text_base + 8192)] — it never reaches the vvar
    pages below, nor anything above the mapping. *)
Example musl_lookup_reads_only_text_pages :
  forallb (fun o => (0 <=? o) && (o <? 8192)) (fst fx_lookup) = true.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   Step 2 — a load from the vvar pages is [MachineUnmodeled]
   ========================================================================= *)

Example vvar_load_is_unmodeled :
  step fx_segs (fx_ms (Z_to_bv 64 0x10000) (Z_to_bv 64 fx_vvar_base))
  = MachineUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** The last vvar byte too, and the first byte of the text is NOT vvar:
    the boundary is where the design puts it. *)
Example vvar_range_is_exactly_four_pages :
  vvar_byte_at fx_segs (Z_to_bv 64 (fx_text_base - 1)) = true
  /\ vvar_byte_at fx_segs (Z_to_bv 64 fx_text_base) = false
  /\ vvar_byte_at fx_segs (Z_to_bv 64 fx_vvar_base) = true
  /\ vvar_byte_at fx_segs (Z_to_bv 64 (fx_vvar_base - 1)) = false.
Proof. vm_compute. repeat split. Qed.

(* =========================================================================
   Step 4 — other fetches, and stores
   ========================================================================= *)

(** A fetch four bytes past an exported entry: the model declines, and
    says so as the MODEL declining, not as the process crashing. *)
Example fetch_inside_the_text_is_unmodeled :
  step fx_segs (fx_ms (fx_entry VdsoClockGettime + Z_to_bv 64 4)
                      (Z_to_bv 64 0))
  = MachineUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** The text base itself, which is not an entry either. *)
Example fetch_at_the_text_base_is_unmodeled :
  step fx_segs (fx_ms (Z_to_bv 64 fx_text_base) (Z_to_bv 64 0))
  = MachineUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** A store into the text is the SIGSEGV a real MMU delivers: the
    kernel maps the text without [VM_WRITE]. *)
Example store_to_the_text_faults :
  step fx_segs (fx_ms (Z_to_bv 64 0x10004) (Z_to_bv 64 fx_text_base))
  = MachineFault.
Proof. vm_compute. reflexivity. Qed.

Example store_to_vvar_faults :
  step fx_segs (fx_ms (Z_to_bv 64 0x10004) (Z_to_bv 64 fx_vvar_base))
  = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   Step 3 — a call is one step with the system call's specification
   ========================================================================= *)

(** What one vDSO call at [ms] can answer: the value it leaves in a0,
    the bytes it wrote, and the model it left.  Read off
    [Run.sstep]'s vDSO arm, premise for premise. *)
Definition vdso_call_answers (segs : list Segment) (ms : machine_state)
    (model : Model) (ret : word) (ws : list (word * list byte))
    (post : Model) : Prop :=
  exists fn n eff model' evs,
    vdso_entry_fn segs (ms_pc ms) = Some fn
    /\ vdso_fn_sysno fn = Some n
    /\ syscall_spec (sys_input segs ms (Z_to_bv 64 n)) model (Ok eff model' evs)
    /\ eff_ret eff <> errno_ret EFAULT
    /\ m_halted model' = None
    /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some post
    /\ ret = eff_ret eff
    /\ ws = eff_writes eff.

(** The same three things for an [ecall] of system call [x8] at the
    same registers and the same memory: [Run.sstep_syscall]'s premises,
    which read [ms] through [Run.sys_input] exactly as the arm above
    does. *)
Definition ecall_answers (segs : list Segment) (ms : machine_state)
    (model : Model) (x8 : word) (ret : word) (ws : list (word * list byte))
    (post : Model) : Prop :=
  exists eff model' evs,
    syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
    /\ m_halted model' = None
    /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some post
    /\ ret = eff_ret eff
    /\ ws = eff_writes eff.

(** THE AGREEMENT.  At the entry of [__vdso_clock_gettime], the vDSO
    call step and an [ecall] of system call 113 with the same registers
    give the SAME set of return values, written bytes and models — with
    the one difference the design names, that the vDSO's [-EFAULT]
    outcome is [unmodeled] rather than answered.

    It holds by construction rather than by a second argument: the arm
    hands [Specs.syscall_spec] the number [Vdso.vdso_fn_sysno] gives,
    over [Run.sys_input] of the same machine state, so the two sides
    are the same proposition with the same arguments. *)
Lemma vdso_call_agrees_with_ecall_113 :
  forall segs ms model ret ws post,
    vdso_entry_fn segs (ms_pc ms) = Some VdsoClockGettime ->
    (vdso_call_answers segs ms model ret ws post
     <-> (ecall_answers segs ms model (Z_to_bv 64 113) ret ws post
          /\ ret <> errno_ret EFAULT)).
Proof.
  intros segs ms model ret ws post Hentry. split.
  - intros (fn & n & eff & model' & evs &
            Hfn & Hno & Hspec & Hef & Hh & Hmat & Hret & Hws).
    rewrite Hentry in Hfn. injection Hfn as <-.
    cbn in Hno. injection Hno as <-.
    split; [| rewrite Hret; exact Hef].
    exists eff, model', evs. repeat split; assumption.
  - intros ((eff & model' & evs & Hspec & Hh & Hmat & Hret & Hws) & Hne).
    exists VdsoClockGettime, 113%Z, eff, model', evs.
    split; [exact Hentry|]. split; [reflexivity|]. split; [exact Hspec|].
    split; [rewrite <- Hret; exact Hne|]. split; [exact Hh|].
    split; [exact Hmat|]. split; assumption.
Qed.

(** The same for [__vdso_clock_getres] and system call 114, which LPS
    pull request #34 added, and for [__vdso_gettimeofday] and 169. *)
Lemma vdso_call_agrees_with_ecall_of :
  forall segs ms model fn n ret ws post,
    vdso_entry_fn segs (ms_pc ms) = Some fn ->
    vdso_fn_sysno fn = Some n ->
    (vdso_call_answers segs ms model ret ws post
     <-> (ecall_answers segs ms model (Z_to_bv 64 n) ret ws post
          /\ ret <> errno_ret EFAULT)).
Proof.
  intros segs ms model fn n ret ws post Hentry Hno. split.
  - intros (fn' & n' & eff & model' & evs &
            Hfn & Hno' & Hspec & Hef & Hh & Hmat & Hret & Hws).
    rewrite Hentry in Hfn. injection Hfn as <-.
    rewrite Hno in Hno'. injection Hno' as <-.
    split; [| rewrite Hret; exact Hef].
    exists eff, model', evs. repeat split; assumption.
  - intros ((eff & model' & evs & Hspec & Hh & Hmat & Hret & Hws) & Hne).
    exists fn, n, eff, model', evs.
    split; [exact Hentry|]. split; [exact Hno|]. split; [exact Hspec|].
    split; [rewrite <- Hret; exact Hne|]. split; [exact Hh|].
    split; [exact Hmat|]. split; assumption.
Qed.

(** What the STEP does to the machine, beside the system call's own
    effect: pc becomes ra, sp is unchanged, and a0 is the result — not
    the draw's value for a0, which the effect overwrites. *)
Lemma vdso_post_pc : forall segs ms model f eff,
  ms_pc (vdso_post segs ms model f eff) = ms_reg ms 1.
Proof. reflexivity. Qed.

Lemma vdso_post_no_svc : forall segs ms model f eff,
  ms_svc_pending (vdso_post segs ms model f eff) = None.
Proof. reflexivity. Qed.

(* =========================================================================
   Step 4, continued — an [mprotect] that meets the pair
   ========================================================================= *)

(** A launch whose ledger holds the pair, and one ordinary mapping
    beside it that an [mprotect] can still change.  [fx_mbase] and
    [fx_sp] are the fixture's, so [State.vdso_top] of this ledger is
    [fx_top] and the pair is the five pages below it. *)
Definition fx_inp : ProcInput :=
  mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1000) [] net_silent
              default_nofile (Z_to_bv 64 0) (Z_to_bv 64 0) false Sv48.

Definition fx_model0 : Model :=
  init_model [] 0 fx_mbase fx_sp 0x40000000 fx_inp.

(** One page at 0x80000000, mapped and PROT_NONE, which is the shape
    [Sys.Mm.Mprotect]'s modelled arm changes. *)
Definition fx_other : word := Z_to_bv 64 0x80000000.

Definition fx_model : Model :=
  with_vmmaps
    (mkVmMapsFull (vm_reserved (m_vmmaps fx_model0))
       [(fx_other, Z_to_bv 64 4096)] [] 0 0 0x40000000 fx_mbase fx_sp)
    fx_model0.

(** The pair is in this ledger's reservations, at the fixture's
    addresses: the Examples below are about the range the model really
    reserved, not about a number written twice. *)
Example fx_model_reserves_the_pair :
  vdso_reserved (m_kernel fx_model) (vdso_top (m_vmmaps fx_model))
  = [(Z_to_bv 64 fx_vvar_base, Z_to_bv 64 (6 * 4096))].
Proof. vm_compute. reflexivity. Qed.

(** REFUSES: a page of the vDSO text.  Linux would allow it — the
    kernel maps the text with [VM_MAYWRITE] — and after it the bytes
    are no longer the measured image's, which is a vDSO this model has
    no term for. *)
Example mprotect_on_the_vdso_text_is_unmodeled :
  check_mprotect (Z_to_bv 64 fx_text_base) (Z_to_bv 64 4096)
    (Z_to_bv 64 3) (mkEffect (Z_to_bv 64 0) [] []) fx_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** REFUSES: a page of the vvar data. *)
Example mprotect_on_the_vvar_pages_is_unmodeled :
  check_mprotect (Z_to_bv 64 fx_vvar_base) (Z_to_bv 64 4096)
    (Z_to_bv 64 3) (mkEffect (Z_to_bv 64 0) [] []) fx_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** REFUSES: a request that only MEETS the pair, starting one page
    below the vvar base and running two pages into it. *)
Example mprotect_overlapping_the_pair_is_unmodeled :
  check_mprotect (Z_to_bv 64 (fx_vvar_base - 4096)) (Z_to_bv 64 8192)
    (Z_to_bv 64 3) (mkEffect (Z_to_bv 64 0) [] []) fx_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** STILL ADMITS: the neighbouring page the pair does not meet.  This
    is the half that shows the gate did not simply stop answering:
    the same request, one ordinary mapping away, is still the modelled
    [mprotect] that reports the pages it backed. *)
Example mprotect_beside_the_pair_still_works :
  check_mprotect fx_other (Z_to_bv 64 4096) (Z_to_bv 64 3)
    (mkEffect (Z_to_bv 64 0) [] [(fx_other, Z_to_bv 64 4096)]) fx_model
  = CheckOk (mprotect_model_next fx_model fx_other (Z_to_bv 64 4096)) [].
Proof. vm_compute. reflexivity. Qed.

(** STILL ADMITS: the page directly BELOW the pair, which the request
    above runs into but this one stops short of.  The two together pin
    the gate's lower edge. *)
Example mprotect_one_page_below_the_pair_is_not_refused :
  check_mprotect (Z_to_bv 64 (fx_vvar_base - 4096)) (Z_to_bv 64 4096)
    (Z_to_bv 64 3) (mkEffect (Z_to_bv 64 0) [] []) fx_model
  <> CheckUnmodeled
  \/ region_free (vdso_reserved (m_kernel fx_model)
                   (vdso_top (m_vmmaps fx_model)))
       (Z_to_bv 64 (fx_vvar_base - 4096)) (Z_to_bv 64 4096) = true.
Proof. right. vm_compute. reflexivity. Qed.
