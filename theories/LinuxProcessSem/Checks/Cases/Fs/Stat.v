(** * LinuxProcessSem.Checks.Cases.Fs.Stat — worked examples over newfstatat (79) and fstat (80)

    Mirrors [Sys/Fs/Stat.v], which answers to Linux [fs/stat.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(** newfstatat(AT_FDCWD, "f", <buf>, 0) against an empty file system: the
    path bytes are 'f', NUL at 0x2000, the file is absent, and the answer
    is -ENOENT.  The pathname was still COPIED IN to reach that answer,
    so the effect carries the two bytes [getname_flags] read. *)
Definition statat_absent_input : SyscallInput :=
  mkInput 79 [AT_FDCWD; 0x2000; 0; 0; 0; 0]
    (fun a => if bv_eqb a 0x2000 then Some 102
              else if bv_eqb a 0x2001 then Some 0 else None)
    (fun _ => None).

Definition statat_absent_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(** Which reason from the top of [Checks/Examples.v]: the third and the
    fourth together.  A copy-in ledger is MODEL-INTERNAL STATE that no
    observation of a real execution reveals — Linux returns the same
    -ENOENT whether or not the model charged the pathname's page, and
    there is no [vm_limit] on a real kernel for the charge to be visible
    through — and the rejecting direction needs a kernel behaving
    inadmissibly, which is the fourth.

    A check that builds the expected ledger by calling the model's own
    [cstr_access_len_aux] compares the model against itself, and would
    keep passing if the spec and that check were made empty TOGETHER,
    which is exactly the defect this file exists to catch.  Only a
    literal range written down from outside separates the two.

    The first conjunct is the one that would have caught it: an effect
    with an EMPTY ledger is rejected.  That is the shape a spec with no
    [record_copyins] wrapper produces, and the shape
    [Prelude.check_ret_only] — which pattern-matches [mkEffectU ret [] []
    [] [] []] — would have DEMANDED.  The remaining conjuncts pin the
    range's two endpoints (an over-long ledger and a shifted one), and
    the last is the accepting control, without which every rejection
    above could be an artefact of some other field. *)
Example newfstatat_pathname_copyin_is_charged :
  let check eff := check_syscall statat_absent_input eff statat_absent_model in
  (* the ledger is not optional: this is the effect with no [record_copyins] *)
  check (mkEffect (errno_ret ENOENT) [] []) = CheckReject
  (* nor may it over-report: the fetch stops at the NUL, at two bytes *)
  /\ check (with_copyins [(0x2000, 3%nat)] (mkEffect (errno_ret ENOENT) [] []))
     = CheckReject
  (* nor start anywhere but the pathname pointer *)
  /\ check (with_copyins [(0x2001, 2%nat)] (mkEffect (errno_ret ENOENT) [] []))
     = CheckReject
  (* control: the truthful ledger IS accepted, so the three above are
     rejections of the ledger and not of the errno beside it *)
  /\ check (with_copyins [(0x2000, 2%nat)] (mkEffect (errno_ret ENOENT) [] []))
     = CheckOk statat_absent_model [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* -------------------------------------------------------------------------
   fstat (80) — the delivered struct stat

   WHICH REASON FROM THE TOP OF [Checks/Examples.v]: the fourth, for
   every rejecting example, and the first for the accepting controls.
   The rejecting direction needs a kernel behaving inadmissibly — one
   that reports a length its own S_IFREG contradicts, that scribbles
   [cp_new_stat]'s cleared padding, that names no file type at all, or
   that changes a file's inode between two stats of it.  No Linux does
   any of those, so no real run can construct them.  Everything below
   is a claim about particular bytes at particular offsets.

   The accepting controls are not decoration.  Without them each
   rejection could be an artefact of some other field — the address, the
   width, the return value — rather than of the member it names.
   ------------------------------------------------------------------------- *)

(** "f", nine bytes long: a length no neighbouring member of the struct
    below coincides with, so a rejection at [st_size] cannot be a
    rejection at [st_blocks] or [st_nlink] read through a wrong
    offset. *)
Definition fstat_path : Fs.path := [Z_to_bv 8 102].
Definition fstat_data : list byte := repeat (Z_to_bv 8 65) 9.
Definition fstat_data_grown : list byte := repeat (Z_to_bv 8 65) 12.

Definition fstat_model_of (d : list byte) : Model :=
  with_fds [(Z_to_bv 64 3, FdFile fstat_path (Z_to_bv 64 0))]
    (init_model [] 0 0 demo_sp demo_limit
       (demo_input [(fstat_path, d)] IEof)).

Definition fstat_model : Model := fstat_model_of fstat_data.
Definition fstat_model_grown : Model := fstat_model_of fstat_data_grown.

(** The same file and the same nine bytes, held through a READ-WRITE
    descriptor instead of a read-only one.  The pair of examples below is
    the whole difference the fourth file kind makes to [fstat]: none. *)
Definition fstat_model_rw : Model :=
  with_fds [(Z_to_bv 64 3, FdFileRW fstat_path (Z_to_bv 64 0))]
    (init_model [] 0 0 demo_sp demo_limit
       (demo_input [(fstat_path, fstat_data)] IEof)).

(** A descriptor on a path the map does not hold.  No run builds it:
    [unlinkat] never removes a key a descriptor still names -- the
    working-directory arm declines that removal, and the /tmp arm turns
    each such descriptor into a [State.FdAnon] first
    ([Fs.Namei.unlink_open_tmp_spec]). *)
Definition fstat_model_unlinked : Model :=
  with_fds [(Z_to_bv 64 3, FdFile fstat_path (Z_to_bv 64 0))]
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)).

(** A 128-byte writable landing zone at 4096, and the same zone one byte
    shy — the shape that separates [copy_to_user]'s -EFAULT from the
    decline a partial copy gets. *)
Definition stat_out : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4224 then Some 0 else None.
Definition stat_out_short : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4223 then Some 0 else None.

Definition fstat_input : SyscallInput :=
  mkInput 80 [Z_to_bv 64 3; Z_to_bv 64 4096; 0; 0; 0; 0]
    (fun _ => None) stat_out.

(** A [struct stat] in the asm-generic layout riscv64 inherits, written
    member by member at the offsets [Uapi] names.  The five arguments
    are the ones the examples vary; everything else is a plausible
    constant (an ext4-ish [st_dev], one link, the [demo_input] user, no
    [st_rdev], a 4096-byte block size) and none of it is claimed to be
    what any kernel would report. *)
Definition stat_of (ino mode size blocks tim : Z) : list byte :=
  Z_to_le_bytes 8 2049                                   (* st_dev *)
  ++ Z_to_le_bytes 8 ino                                 (* st_ino *)
  ++ Z_to_le_bytes 4 mode                                (* st_mode *)
  ++ Z_to_le_bytes 4 1                                   (* st_nlink *)
  ++ Z_to_le_bytes 4 1000                                (* st_uid *)
  ++ Z_to_le_bytes 4 1000                                (* st_gid *)
  ++ Z_to_le_bytes 8 0                                   (* st_rdev *)
  ++ Z_to_le_bytes 8 0                                   (* __pad1 *)
  ++ Z_to_le_bytes 8 size                                (* st_size *)
  ++ Z_to_le_bytes 4 4096                                (* st_blksize *)
  ++ Z_to_le_bytes 4 0                                   (* __pad2 *)
  ++ Z_to_le_bytes 8 blocks                              (* st_blocks *)
  ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0            (* st_atime *)
  ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0            (* st_mtime *)
  ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0            (* st_ctime *)
  ++ Z_to_le_bytes 8 0.                                  (* __unused4/5 *)

(** The truthful answer for the nine-byte file: a regular file of length
    nine.  Nothing but the width, the padding, the type's validity and
    the length is checked, so every other member here is free. *)
Definition stat_truthful : list byte := stat_of 4711 S_IFREG 9 8 1700000000.

(* ---- the accepting controls -------------------------------------------- *)

(** The first stat of a file is where its identity enters the model: the
    answer is admitted and BECOMES the pin. *)
Example fstat_first_answer_pins :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] []) fstat_model
  = CheckOk (with_statpin fstat_path stat_truthful fstat_model) [].
Proof. check_eq. Qed.

(** The model does NOT claim the file is regular, and this is the case
    that says so.  Offered S_IFCHR with [st_size] 0 — which is the true
    answer for a character device at a path this model resolves and
    holds nine bytes for — the checker ACCEPTS.  Rejecting
    it is the false rejection the conditional in [Uapi.stat_size_ok]
    exists to avoid, and this example is what would fail if the
    implication were ever strengthened to an assertion. *)
Example fstat_character_device_answer_admitted :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4711 S_IFCHR 0 0 1700000000)] []) fstat_model
  = CheckOk (with_statpin fstat_path (stat_of 4711 S_IFCHR 0 0 1700000000)
               fstat_model) [].
Proof. check_eq. Qed.

(* ---- the read-write descriptor answers as the other file kinds do ------- *)

(** [FdFileRW] gets the SAME answer as [FdFile] above, from the same
    [fstat_file_spec] under the same implication, and pins it the same
    way.  A stat reads the INODE: neither [f_mode] nor [f_flags] is a
    member of [struct stat] ([cp_new_stat]/[generic_fillattr], fs/stat.c,
    Linux v6.18.46, commit 1f99e9ab748f), so how the descriptor was
    opened is not something a stat can report.  This is the accepting
    half; the rejecting half is directly below, so the pair attributes
    the answer to the arm rather than to the checker being lax about a
    kind it does not recognise. *)
Example fstat_read_write_fd_answers_as_a_file :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] []) fstat_model_rw
  = CheckOk (with_statpin fstat_path stat_truthful fstat_model_rw) [].
Proof. check_eq. Qed.

(** …and the length obligation BITES through the read-write descriptor
    too.  Eight bytes under the kernel's own S_IFREG where the map holds
    nine: inadmissible, exactly as it is for [FdFile].  Without this the
    example above would pass just as happily if the arm answered
    [unmodeled], since a decline is not a rejection. *)
Example fstat_read_write_wrong_size_rejected :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4711 S_IFREG 8 8 1700000000)] []) fstat_model_rw
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(* ---- what the length obligation rejects -------------------------------- *)

(** …and the implication still BITES on the arm it is about.  Eight
    bytes where the map holds nine, under the kernel's own S_IFREG:
    inadmissible.  Paired with the control above, this attributes the
    rejection to the length rather than to the type. *)
Example fstat_wrong_size_under_ifreg_rejected :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4711 S_IFREG 8 8 1700000000)] []) fstat_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** A file that GREW must report the new length, not the old one.  The
    pin is not what settles this — the same rejection holds against an
    unpinned model — but it is where the two halves meet: the length
    tracks the map while the identity does not. *)
Example fstat_stale_size_after_growth_rejected :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] [])
    (with_statpin fstat_path stat_truthful fstat_model_grown)
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example fstat_grown_size_admitted :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4711 S_IFREG 12 8 1700000042)] [])
    (with_statpin fstat_path stat_truthful fstat_model_grown)
  = CheckOk (with_statpin fstat_path stat_truthful fstat_model_grown) [].
Proof. check_eq. Qed.

(* ---- what the padding and the type bits reject -------------------------- *)

(** [cp_new_stat] clears the whole struct through
    [INIT_STRUCT_STAT_PADDING] and then assigns the members, so no
    assignment covers [__pad1] and it is delivered as zero.  One
    nonzero byte there is a kernel this model refuses. *)
Example fstat_nonzero_pad1_rejected :
  let bs := firstn 40 stat_truthful ++ Z_to_le_bytes 8 1
            ++ skipn 48 stat_truthful in
  check_syscall fstat_input (mkEffect 0 [(4096, bs)] []) fstat_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example fstat_nonzero_unused45_rejected :
  let bs := firstn 120 stat_truthful ++ Z_to_le_bytes 8 1 in
  check_syscall fstat_input (mkEffect 0 [(4096, bs)] []) fstat_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** AN ALL-ZERO STRUCT IS THE SHAPE A KERNEL THAT WROTE NOTHING AND SAID
    IT DID WOULD PRODUCE, and it is refused by [st_mode] naming no file
    type.  Without that conjunct it would be admitted: the padding is
    zero, the width is right, and [st_mode] 0 is not S_IFREG so the
    length obligation would not apply — which is precisely how a check
    over free members turns into a check of nothing. *)
Example fstat_all_zero_struct_rejected :
  check_syscall fstat_input
    (mkEffect 0 [(4096, repeat (Z_to_bv 8 0) 128)] []) fstat_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** …and so is a type word that is none of the seven, here 0170000
    itself — every S_IFMT bit set, which no inode holds. *)
Example fstat_impossible_type_rejected :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4711 S_IFMT 9 8 1700000000)] []) fstat_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(* ---- the pin: two stats of one file cannot disagree -------------------- *)

(** Once pinned, a later stat must repeat the STABLE members.  The
    defector below differs in [st_ino] alone and is otherwise the same
    admissible answer — it would have been accepted as a FIRST answer,
    which the control after it shows — so it is refused for disagreeing
    with the record.  That is the whole content of "a file keeps its
    inode for the life of a run", and it is the conjunct a per-call
    [choose] would have dropped. *)
Example fstat_pinned_repeat_admitted :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] [])
    (with_statpin fstat_path stat_truthful fstat_model)
  = CheckOk (with_statpin fstat_path stat_truthful fstat_model) [].
Proof. check_eq. Qed.

Example fstat_pinned_inode_defector_rejected :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4712 S_IFREG 9 8 1700000000)] [])
    (with_statpin fstat_path stat_truthful fstat_model)
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example fstat_inode_defector_is_itself_admissible_first :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4712 S_IFREG 9 8 1700000000)] []) fstat_model
  = CheckOk (with_statpin fstat_path (stat_of 4712 S_IFREG 9 8 1700000000)
               fstat_model) [].
Proof. check_eq. Qed.

(** THE MEMBERS THE PIN DOES NOT HOLD, pinned as a NON-rejection.  A
    later stat may report new timestamps and a new block count against
    the same pin — every read and write moves them, and demanding they
    repeat would reject a conforming trace.  Without this example
    [Uapi.stat_stable_eqb] could be widened to the whole buffer and
    every other example here would still pass. *)
Example fstat_pinned_new_times_and_blocks_admitted :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4711 S_IFREG 9 16 1700000099)] [])
    (with_statpin fstat_path stat_truthful fstat_model)
  = CheckOk (with_statpin fstat_path stat_truthful fstat_model) [].
Proof. check_eq. Qed.

(* ---- the write itself: width, address and the empty copy-in ledger ------ *)

(** The copy is [cp_new_stat]'s single 128-byte [copy_to_user]: 127
    bytes is not a short answer this model has a name for. *)
Example fstat_short_struct_rejected :
  check_syscall fstat_input
    (mkEffect 0 [(4096, firstn 127 stat_truthful)] []) fstat_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** …and it lands at [statbuf], not one byte past it. *)
Example fstat_shifted_write_rejected :
  check_syscall fstat_input (mkEffect 0 [(4097, stat_truthful)] []) fstat_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** fstat takes its descriptor in a register and reads no user byte at
    all, so there is no [copy_from_user] anywhere on the path and the
    ledger must be empty.  A success that claimed to have read the
    statbuf is rejected, here on the arm that really does write. *)
Example fstat_forged_copyin_rejected :
  check_syscall fstat_input
    (with_copyins [(4096, 128%nat)] (mkEffect 0 [(4096, stat_truthful)] []))
    fstat_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(* ---- the destination, in the three bands -------------------------------- *)

(** [access_ok] refuses the 128-byte range: [copy_to_user]'s own gate,
    which fires before a byte moves, so -EFAULT is exact. *)
Example fstat_access_ok_fault :
  check_syscall
    (mkInput 80 [Z_to_bv 64 3; Z_to_bv 64 9223372036854775808; 0; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) fstat_model
  = CheckOk fstat_model [].
Proof. check_eq. Qed.

(** A range [access_ok] ADMITS but memory does not wholly back is
    declined rather than faulted: [copy_to_user] would commit a prefix
    and then answer -EFAULT, and the model cannot say how long that
    prefix is.  One byte short of 128 is the whole difference. *)
Example fstat_one_byte_short_is_unmodeled :
  check_syscall
    (mkInput 80 [Z_to_bv 64 3; Z_to_bv 64 4096; 0; 0; 0; 0]
      (fun _ => None) stat_out_short)
    (mkEffect 0 [(4096, stat_truthful)] []) fstat_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** A descriptor whose path the map no longer holds is declined, as
    [Stat.fstat_file_spec] says, for a [Model] no run builds (see
    [fstat_model_unlinked]).  What the /tmp arm's removal of an open name
    really leaves is an unnamed file, whose [fstat] is
    [Stat.fstat_anon_spec]'s, with [st_nlink] 0. *)
Example fstat_unlinked_path_is_unmodeled :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] [])
    fstat_model_unlinked
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(* ---- the pin dies with the file it identifies -------------------------- *)

(** [unlinkat] destroys the inode, and Linux gives the NEXT file created
    at that name a different one — so a pin that outlived the removal
    would reject the conforming trace `create f; fstat; unlink f;
    create f; fstat`.  [State.with_fs] drops it, and these two say that
    it drops the right ones: gone when the key goes, kept when the same
    key is merely rewritten.  Neither is reachable from a checker
    verdict, because the second create puts the key back before any
    [fstat] can look — the two states differ only in a field no
    syscall reports. *)

Example fstat_pin_dies_with_the_file :
  m_statpins (with_fs [] (with_statpin fstat_path stat_truthful fstat_model))
  = [].
Proof. vm_compute. reflexivity. Qed.

Example fstat_pin_survives_a_rewrite :
  m_statpins (with_fs [(fstat_path, fstat_data_grown)]
                (with_statpin fstat_path stat_truthful fstat_model))
  = [(fstat_path, stat_truthful)].
Proof. vm_compute. reflexivity. Qed.

(** …and the consequence at the checker: with the pin gone, the file
    created next at that name may report ANY inode, exactly as a first
    stat may.  Read beside [fstat_pinned_inode_defector_rejected], which
    is the same struct against a live pin, this is what says the
    rejection there is about the file's identity and not about the
    number. *)
Example fstat_recreated_file_takes_a_new_inode :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4712 S_IFREG 9 8 1700000000)] [])
    (with_fs [(fstat_path, fstat_data)]
       (with_fs [] (with_statpin fstat_path stat_truthful fstat_model)))
  = CheckOk (with_statpin fstat_path (stat_of 4712 S_IFREG 9 8 1700000000)
               (with_fs [(fstat_path, fstat_data)]
                  (with_fs [] (with_statpin fstat_path stat_truthful
                                 fstat_model)))) [].
Proof. check_eq. Qed.
