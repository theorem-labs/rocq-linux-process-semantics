(** * Checks.Cases.Kernel.VdsoSym — musl's [__vdsosym], transcribed, over a measured image

    NOT part of the trusted specification.  This file is EVIDENCE: it
    says what the libc the pipeline links actually finds in the vDSO
    image the model maps, so that the model's claim — that a program
    which reads the clock through its libc reaches the vDSO call step —
    is checked rather than assumed.

    WHAT IS TRANSCRIBED.  musl 1.2.6 at commit f21a9653 (v1.2.6-20),
    [src/internal/vdso.c], the whole of [__vdsosym] with its two
    helpers [checkver] and [count_syms_gnu].  static-asan
    b05061352064 pins that musl (static-asan's README.md, named by
    docs/building.md in oss-verify-proofs-internal), and
    [arch/riscv64/syscall_arch.h] there defines [VDSO_CGT_SYM] as
    ["__vdso_clock_gettime"] and [VDSO_CGT_VER] as ["LINUX_4.15"], so
    those two strings are what the first [clock_gettime] of a
    pipeline-built binary looks up.

    HOW IT IS TRANSCRIBED.  [__vdsosym] walks C pointers; this walks
    OFFSETS from the ELF header, through a reader [peek] the caller
    supplies, and records every offset it reads.  Two things follow
    that a pointer walk would not give:

    - the lookup's READS are a value the statements below can quantify
      over, which is how "the lookup reads only bytes of the text
      pages" becomes a theorem rather than a sentence;
    - the walk is a pure function of the image's bytes, so the answer
      for a measured image is decided by computation.

    The one step of musl's function NOT here is its first loop, over
    [libc.auxv] for [AT_SYSINFO_EHDR].  That loop's answer is the base
    this file takes as a parameter, and what the auxv publishes is the
    entry block's business ([StackLayout.auxv_entries]).

    A NOTE ON [size_t].  musl's [base] starts at [(size_t)-1] as a
    sentinel and is set to [eh + p_offset - p_vaddr], which is a
    POINTER DIFFERENCE this file keeps in [Z] (it can be negative for
    an image whose [PT_LOAD] has [p_vaddr > p_offset]; the measured
    image has both zero).  [count_syms_gnu]'s [nsym] and the hash
    words are unsigned 32-bit or 64-bit and are kept in [N]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Vdso RiscvSemantics.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* =========================================================================
   The reader: an offset walk that records what it read
   ========================================================================= *)

(** A read of the image returns a value and grows the list of offsets
    the walk has touched.  [None] is "this walk cannot go on" — musl's
    [return 0], and also a byte the reader does not supply, which for
    the machine-level reader below is a byte outside the mapping. *)
Definition RD (A : Type) : Type := list Z -> (list Z * option A).

Definition rd_ret {A} (a : A) : RD A := fun t => (t, Some a).
Definition rd_fail {A} : RD A := fun t => (t, None).

Definition rd_bind {A B} (m : RD A) (f : A -> RD B) : RD B :=
  fun t =>
    let '(t', r) := m t in
    match r with
    | Some a => f a t'
    | None => (t', None)
    end.

Local Notation "x <-- m ;;; k" := (rd_bind m (fun x => k))
  (at level 76, right associativity, only parsing).

Section WithPeek.

(** The byte at image offset [o].  For the lemmas below it is either
    the measured image's own bytes or the machine's view of the text
    mapping; the walk cannot tell the two apart, which is the point. *)
Variable peek : Z -> option byte.

Definition rd_u8 (o : Z) : RD N :=
  fun t => (o :: t, match peek o with
                    | Some b => Some (Z.to_N (bv_unsigned b))
                    | None => None
                    end).

(** Little-endian multi-byte reads, each byte recorded. *)
Fixpoint rd_le (o : Z) (n : nat) : RD N :=
  match n with
  | O => rd_ret 0%N
  | S n' =>
      b <-- rd_u8 o ;;;
      hi <-- rd_le (o + 1) n' ;;;
      rd_ret (b + 256 * hi)%N
  end.

Definition rd_u16 (o : Z) : RD N := rd_le o 2.
Definition rd_u32 (o : Z) : RD N := rd_le o 4.
Definition rd_u64 (o : Z) : RD N := rd_le o 8.

(** [strcmp(s, image + o) == 0], with [s] the C string's bytes without
    its NUL.  Reads the image byte by byte and stops at the first
    difference or at the NUL, exactly as [strcmp] does, so the
    recorded offsets are the ones musl really touches. *)
Fixpoint rd_streq (o : Z) (s : list byte) : RD bool :=
  match s with
  | [] => c <-- rd_u8 o ;;; rd_ret (N.eqb c 0)
  | ch :: rest =>
      c <-- rd_u8 o ;;;
      if N.eqb c (Z.to_N (bv_unsigned ch))
      then rd_streq (o + 1) rest
      else rd_ret false
  end.

(* =========================================================================
   The ELF structures musl reads
   ========================================================================= *)

(** ELF64 field offsets, from elf.h.  Only the fields [__vdsosym]
    names are here; a field it does not read is not read here either. *)
Definition E_PHOFF : Z := 32.      (** [Elf64_Ehdr.e_phoff] *)
Definition E_PHENTSIZE : Z := 54.  (** [Elf64_Ehdr.e_phentsize] *)
Definition E_PHNUM : Z := 56.      (** [Elf64_Ehdr.e_phnum] *)

Definition P_TYPE : Z := 0.        (** [Elf64_Phdr.p_type] *)
Definition P_OFFSET : Z := 8.      (** [Elf64_Phdr.p_offset] *)
Definition P_VADDR : Z := 16.      (** [Elf64_Phdr.p_vaddr] *)

(** THE INDEX UNIT OF THE DYNAMIC WALK IS 8 BYTES, NOT 16.

    musl does not walk [Elf64_Dyn] records.  [src/internal/vdso.c] at
    musl f21a9653 declares [dynv] as a pointer to [size_t] and reads
    [dynv[i]] as the tag and [dynv[i+1]] as the value, stepping [i] by
    TWO: its loop is [for (i=0; dynv[i]; i+=2)], its value is
    [base + dynv[i+1]], and its switch is on [dynv[i]].

    So the step from one entry to the next is [i += 2] over 8-byte
    words, which is 16 bytes, while the step from the tag to its value
    is ONE word.  Writing the index unit as [sizeof(Elf64_Dyn)] reads
    as correct and is wrong: it skips every second entry.  That is the
    error this transcription first made, and it was found by running a
    byte-for-byte mirror of this function over the measured image and
    seeing it miss [DT_SYMTAB] -- not by reading the code again. *)
Definition DYN_WORD : Z := 8.
Definition D_TAG : Z := 0.
Definition D_VAL : Z := 8.

Definition SYM_SIZE : Z := 24.     (** sizeof(Elf64_Sym) *)
Definition ST_NAME : Z := 0.
Definition ST_INFO : Z := 4.
Definition ST_SHNDX : Z := 6.
Definition ST_VALUE : Z := 8.

Definition VD_FLAGS : Z := 2.      (** [Elf64_Verdef.vd_flags] *)
Definition VD_NDX : Z := 4.
Definition VD_AUX : Z := 12.
Definition VD_NEXT : Z := 16.
Definition VDA_NAME : Z := 0.      (** [Elf64_Verdaux.vda_name] *)

Definition PT_LOAD : N := 1.
Definition PT_DYNAMIC : N := 2.

Definition DT_HASH : N := 4.
Definition DT_STRTAB : N := 5.
Definition DT_SYMTAB : N := 6.
Definition DT_VERSYM : N := 0x6ffffff0.
Definition DT_VERDEF : N := 0x6ffffffc.
Definition DT_GNU_HASH : N := 0x6ffffef5.

Definition VER_FLG_BASE : N := 1.

(** [OK_TYPES] and [OK_BINDS] of vdso.c, as the bit masks the macros
    expand to: types [STT_NOTYPE] 0, [STT_OBJECT] 1, [STT_FUNC] 2 and
    [STT_COMMON] 5; binds [STB_GLOBAL] 1, [STB_WEAK] 2 and
    [STB_GNU_UNIQUE] 10. *)
Definition OK_TYPES : N := 0x27.
Definition OK_BINDS : N := 0x406.

Definition bit_set (mask k : N) : bool := N.testbit mask k.

(* =========================================================================
   [__vdsosym], step by step
   ========================================================================= *)

(** The program-header loop.  musl keeps the LAST [PT_LOAD]'s delta and
    the LAST [PT_DYNAMIC]'s offset, because each assignment overwrites
    the one before; this fold does the same. *)
Fixpoint rd_phdrs (phoff phent : Z) (n : nat) (i : Z)
    (base : option Z) (dynv : option Z) : RD (option Z * option Z) :=
  match n with
  | O => rd_ret (base, dynv)
  | S n' =>
      let ph := phoff + i * phent in
      ty <-- rd_u32 (ph + P_TYPE) ;;;
      if N.eqb ty PT_LOAD then
        off <-- rd_u64 (ph + P_OFFSET) ;;;
        va <-- rd_u64 (ph + P_VADDR) ;;;
        rd_phdrs phoff phent n' (i + 1) (Some (Z.of_N off - Z.of_N va)) dynv
      else if N.eqb ty PT_DYNAMIC then
        off <-- rd_u64 (ph + P_OFFSET) ;;;
        rd_phdrs phoff phent n' (i + 1) base (Some (Z.of_N off))
      else
        rd_phdrs phoff phent n' (i + 1) base dynv
  end.

(** What the dynamic-section walk collects, each already resolved
    against [base] into an image offset. *)
Record DynInfo := mkDynInfo {
  di_strings : option Z;
  di_syms    : option Z;
  di_hash    : option Z;
  di_ghash   : option Z;
  di_versym  : option Z;
  di_verdef  : option Z
}.

Definition di_empty : DynInfo := mkDynInfo None None None None None None.

(** The [for (i=0; dynv[i]; i+=2)] loop.  [fuel] bounds it; musl's own
    bound is the [DT_NULL] terminator, which every well-formed dynamic
    section has. *)
Fixpoint rd_dyn (base dynv : Z) (fuel : nat) (i : Z) (acc : DynInfo)
    : RD DynInfo :=
  match fuel with
  | O => rd_ret acc
  | S fuel' =>
      let e := dynv + i * DYN_WORD in
      tag <-- rd_u64 (e + D_TAG) ;;;
      if N.eqb tag 0 then rd_ret acc
      else
        val <-- rd_u64 (e + D_VAL) ;;;
        let p := base + Z.of_N val in
        let acc' :=
          if N.eqb tag DT_STRTAB then mkDynInfo (Some p) (di_syms acc)
                                      (di_hash acc) (di_ghash acc)
                                      (di_versym acc) (di_verdef acc)
          else if N.eqb tag DT_SYMTAB then mkDynInfo (di_strings acc) (Some p)
                                      (di_hash acc) (di_ghash acc)
                                      (di_versym acc) (di_verdef acc)
          else if N.eqb tag DT_HASH then mkDynInfo (di_strings acc) (di_syms acc)
                                      (Some p) (di_ghash acc)
                                      (di_versym acc) (di_verdef acc)
          else if N.eqb tag DT_GNU_HASH then mkDynInfo (di_strings acc) (di_syms acc)
                                      (di_hash acc) (Some p)
                                      (di_versym acc) (di_verdef acc)
          else if N.eqb tag DT_VERSYM then mkDynInfo (di_strings acc) (di_syms acc)
                                      (di_hash acc) (di_ghash acc)
                                      (Some p) (di_verdef acc)
          else if N.eqb tag DT_VERDEF then mkDynInfo (di_strings acc) (di_syms acc)
                                      (di_hash acc) (di_ghash acc)
                                      (di_versym acc) (Some p)
          else acc in
        rd_dyn base dynv fuel' (i + 2) acc'
  end.

(** [count_syms_gnu]'s first loop: the largest bucket value. *)
Fixpoint rd_gnu_max_bucket (buckets : Z) (n : nat) (i : Z) (best : N)
    : RD N :=
  match n with
  | O => rd_ret best
  | S n' =>
      b <-- rd_u32 (buckets + 4 * i) ;;;
      rd_gnu_max_bucket buckets n' (i + 1) (if N.ltb best b then b else best)
  end.

(** [count_syms_gnu]'s do-while loop over the hash chain.  In C it is
    [do nsym++; while (!( *hashval++ & 1));] -- a space stands between
    the two symbols that open a Rocq comment.  It stops at the first
    chain word with bit 0 set, which marks the end of a bucket's
    chain. *)
Fixpoint rd_gnu_chain (hashval : Z) (fuel : nat) (nsym : N) : RD N :=
  match fuel with
  | O => rd_fail
  | S fuel' =>
      h <-- rd_u32 hashval ;;;
      let nsym' := N.succ nsym in
      if N.eqb (N.land h 1) 0
      then rd_gnu_chain (hashval + 4) fuel' nsym'
      else rd_ret nsym'
  end.

(** [count_syms_gnu(gh)]: [buckets = gh + 4 + gh[2]*sizeof(size_t)/4]
    with [sizeof(size_t)] 8, so [gh[2]*2] words past [gh + 4]. *)
Definition rd_count_syms_gnu (gh : Z) (fuel : nat) : RD N :=
  nbuckets <-- rd_u32 gh ;;;
  symoffset <-- rd_u32 (gh + 4) ;;;
  bloom <-- rd_u32 (gh + 8) ;;;
  let buckets := gh + 4 * (4 + Z.of_N bloom * 2) in
  nsym <-- rd_gnu_max_bucket buckets (N.to_nat nbuckets) 0 0 ;;;
  if N.eqb nsym 0 then rd_ret 0%N
  else
    let hashval := buckets + 4 * (Z.of_N nbuckets + (Z.of_N nsym - Z.of_N symoffset)) in
    rd_gnu_chain hashval fuel nsym.

(** [checkver].  Walks the [Verdef] chain for the entry whose
    [vd_ndx & 0x7fff] is the symbol's version index and which is not
    the BASE entry, then compares the version name. *)
Fixpoint rd_checkver (verdef strings : Z) (fuel : nat) (def : Z)
    (vsym : N) (vername : list byte) : RD bool :=
  match fuel with
  | O => rd_ret false
  | S fuel' =>
      flags <-- rd_u16 (def + VD_FLAGS) ;;;
      ndx <-- rd_u16 (def + VD_NDX) ;;;
      if (negb (bit_set flags 0) && N.eqb (N.land ndx 0x7fff) vsym)%bool
      then
        aux <-- rd_u32 (def + VD_AUX) ;;;
        nm <-- rd_u32 (def + Z.of_N aux + VDA_NAME) ;;;
        rd_streq (strings + Z.of_N nm) vername
      else
        next <-- rd_u32 (def + VD_NEXT) ;;;
        if N.eqb next 0 then rd_ret false
        else rd_checkver verdef strings fuel' (def + Z.of_N next) vsym vername
  end.

(** The symbol loop.  Every [continue] of musl's body is a [false] arm
    here, in the order musl tests them, so a symbol is skipped for the
    first reason musl would skip it and the recorded reads stop
    there. *)
Fixpoint rd_syms (base syms strings : Z) (versym verdef : option Z)
    (n : nat) (i : Z) (name vername : list byte) (fuel : nat) : RD (option Z) :=
  match n with
  | O => rd_ret None
  | S n' =>
      let sy := syms + i * SYM_SIZE in
      info <-- rd_u8 (sy + ST_INFO) ;;;
      if negb (bit_set OK_TYPES (N.land info 0xf))
      then rd_syms base syms strings versym verdef n' (i + 1) name vername fuel
      else if negb (bit_set OK_BINDS (N.shiftr info 4))
      then rd_syms base syms strings versym verdef n' (i + 1) name vername fuel
      else
        shndx <-- rd_u16 (sy + ST_SHNDX) ;;;
        if N.eqb shndx 0
        then rd_syms base syms strings versym verdef n' (i + 1) name vername fuel
        else
          nm <-- rd_u32 (sy + ST_NAME) ;;;
          eq <-- rd_streq (strings + Z.of_N nm) name ;;;
          if negb eq
          then rd_syms base syms strings versym verdef n' (i + 1) name vername fuel
          else
            match versym, verdef with
            | Some vs, Some vd =>
                vi <-- rd_u16 (vs + 2 * i) ;;;
                ok <-- rd_checkver vd strings fuel vd (N.land vi 0x7fff) vername ;;;
                if ok
                then (v <-- rd_u64 (sy + ST_VALUE) ;;; rd_ret (Some (base + Z.of_N v)))
                else rd_syms base syms strings versym verdef n' (i + 1) name vername fuel
            | _, _ =>
                v <-- rd_u64 (sy + ST_VALUE) ;;; rd_ret (Some (base + Z.of_N v))
            end
  end.

(** [__vdsosym(vername, name)], from the ELF header on.  The answer is
    an OFFSET from the header: the caller adds the base the auxv
    published, which is what musl's pointer arithmetic does.

    [fuel] bounds the three loops musl bounds by terminators (the
    dynamic section's [DT_NULL], the [Verdef] chain's [vd_next], and
    [count_syms_gnu]'s hash chain). *)
Definition vdsosym (fuel : nat) (vername name : list byte) : RD (option Z) :=
  phoff <-- rd_u64 E_PHOFF ;;;
  phent <-- rd_u16 E_PHENTSIZE ;;;
  phnum <-- rd_u16 E_PHNUM ;;;
  bd <-- rd_phdrs (Z.of_N phoff) (Z.of_N phent) (N.to_nat phnum) 0 None None ;;;
  match bd with
  | (Some base, Some dynv) =>
      di <-- rd_dyn base dynv fuel 0 di_empty ;;;
      match di_strings di, di_syms di with
      | Some strings, Some syms =>
          (* [if (!verdef) versym = 0;] *)
          let versym := match di_verdef di with
                        | Some _ => di_versym di
                        | None => None
                        end in
          match di_hash di, di_ghash di with
          | Some h, _ =>
              n <-- rd_u32 (h + 4) ;;;
              rd_syms base syms strings versym (di_verdef di)
                      (N.to_nat n) 0 name vername fuel
          | None, Some gh =>
              n <-- rd_count_syms_gnu gh fuel ;;;
              rd_syms base syms strings versym (di_verdef di)
                      (N.to_nat n) 0 name vername fuel
          | None, None => rd_ret None
          end
      | _, _ => rd_ret None
      end
  | _ => rd_ret None
  end.

End WithPeek.

(* =========================================================================
   The two strings riscv64 musl looks up
   ========================================================================= *)

Definition ascii_bytes (s : list Z) : list byte := map (Z_to_bv 8) s.

(** ["__vdso_clock_gettime"], [VDSO_CGT_SYM] of
    musl's arch/riscv64/syscall_arch.h at f21a9653. *)
Definition str_vdso_clock_gettime : list byte :=
  ascii_bytes [95;95;118;100;115;111;95;99;108;111;99;107;95;103;101;116;116;105;109;101].

(** ["LINUX_4.15"], [VDSO_CGT_VER] of the same header. *)
Definition str_linux_4_15 : list byte :=
  ascii_bytes [76;73;78;85;88;95;52;46;49;53].

(** ["__vdso_clock_getres"], which musl's [clock_getres] looks up with
    the same version (src/time/clock_getres.c has no vDSO path at
    f21a9653; the name is here because the model exports the entry and
    a reader should be able to check it the same way). *)
Definition str_vdso_clock_getres : list byte :=
  ascii_bytes [95;95;118;100;115;111;95;99;108;111;99;107;95;103;101;116;114;101;115].

(* =========================================================================
   The reader over a measured image
   ========================================================================= *)

(** The image's own bytes, as a reader over offsets.  An offset outside
    the image reads [None], so a walk that stepped off the end would
    stop rather than read a neighbouring mapping — which is what makes
    the containment statement below about the WALK and not about the
    reader. *)
Definition image_peek (im : VdsoImage) (o : Z) : option byte :=
  if (0 <=? o) && (o <? Z.of_N (vi_size im))
  then segment_byte_at (vi_bytes im) (Z.to_N o)
  else None.

(** Run the lookup on a measured image and keep both halves: what it
    answered and which offsets it read. *)
Definition image_lookup (im : VdsoImage) (vername name : list byte)
    : list Z * option (option Z) :=
  vdsosym (image_peek im) 4096 vername name [].

Definition image_lookup_result (im : VdsoImage) (vername name : list byte)
    : option Z :=
  match snd (image_lookup im vername name) with
  | Some r => r
  | None => None
  end.

Definition image_lookup_reads (im : VdsoImage) (vername name : list byte)
    : list Z :=
  fst (image_lookup im vername name).

(** Every offset the walk read lies inside the image. *)
Definition reads_within (im : VdsoImage) (os : list Z) : bool :=
  forallb (fun o => (0 <=? o) && (o <? Z.of_N (vi_size im))) os.
