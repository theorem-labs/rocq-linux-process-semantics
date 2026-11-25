(** * LinuxProcessSem.Checks.Cases.Fs.Stat — worked examples over newfstatat (79) and fstat (80)

    Mirrors [Sys/Fs/Stat.v], which answers to Linux [fs/stat.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

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
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Fs.Namei.

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
  init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof).

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

(** A NAME THE WALK DOES NOT FIND IN THE /dev SUBTREE IS -ENOENT, as it
    is anywhere else.  The image describes /dev completely at launch and
    the kernel makes no device node during the run ([Fs.dev_dir] carries
    the argument; in Linux v6.18.46 a devtmpfs node is made by
    [devtmpfs_create_node], drivers/base/devtmpfs.c:129-154, when a
    driver-core device is registered), so a name the image does not hold
    under /dev is one the guest does not have.  A success is refused
    beside it, and the twin under /tmp gives the same answer. *)
Definition statat_ns_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof).

Definition statat_devpts_model : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input
       (Fs.fs_set (demo_fs [])
          (Fs.child_key Fs.dev_dir
             (map (fun z => Z_to_bv 8 z) [112; 116; 115]%Z)) EDir)
       IEof).

Definition statat_mem (bs : list Z) : word -> option byte :=
  fun a => if (0x2000 <=? bv_unsigned a)%Z
           then nth_error (map (fun z => Z_to_bv 8 z) (bs ++ [0%Z]))
                  (Z.to_nat (bv_unsigned a - 0x2000))
           else None.

Example newfstatat_under_dev_absent_is_enoent :
  check_syscall
    (mkInput 79 [AT_FDCWD; 0x2000; 0; 0; 0; 0]
       (statat_mem [47; 100; 101; 118; 47; 122; 101; 114; 111]%Z)
       (fun _ => None))
    (with_copyins [(0x2000, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
    statat_ns_model
  = CheckOk statat_ns_model []
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; 0; 0; 0; 0]
          (statat_mem [47; 100; 101; 118; 47; 122; 101; 114; 111]%Z)
          (fun _ => None))
       (with_copyins [(0x2000, 10%nat)] (mkEffect 0 [] []))
       statat_ns_model
     = CheckReject
  (* one level down, under a DECLARED /dev/pts, the same *)
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; 0; 0; 0; 0]
          (statat_mem [47; 100; 101; 118; 47; 112; 116; 115; 47; 48]%Z)
          (fun _ => None))
       (with_copyins [(0x2000, 11%nat)] (mkEffect (errno_ret ENOENT) [] []))
       statat_devpts_model
     = CheckOk statat_devpts_model []
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; 0; 0; 0; 0]
          (statat_mem [47; 116; 109; 112; 47; 122; 101; 114; 111]%Z)
          (fun _ => None))
       (with_copyins [(0x2000, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
       statat_ns_model
     = CheckOk statat_ns_model [].
Proof. split_conj; check_eq. Qed.

(** [getname_flags]' -ENOMEM beside its own answers and every answer
    past them: the name is allocated before a byte is copied
    (fs/namei.c:146-148, Linux v6.18.46), so on a fetch that reads
    nothing before [getname_flags] that -ENOMEM carries no copy-in
    ([Fs.Namei.getname_refusals]).  [newfstatat] without AT_EMPTY_PATH
    fetches with plain [getname] (include/linux/fs.h:2952-2953), so the
    empty name's -ENOENT, an unmapped pointer's -EFAULT, an absent
    name's -ENOENT and the -EFAULT of a name that faults on its second
    byte admit it.  [readlinkat] fetches with [getname_flags] under
    LOOKUP_EMPTY (fs/stat.c:569, :575), which lets the empty name
    through only after the allocation, so its -ENOENT (593) admits it.
    Under AT_EMPTY_PATH the fetch reads the lead byte first
    ([newfstatat_empty_path_getname_enomem_reads_the_lead_byte]). *)
Example newfstatat_getname_enomem_copies_nothing :
  let call (nr : word) a2 a3 mp := check_syscall
        (mkInput nr [AT_FDCWD; 0x2000; a2; a3; 0; 0] mp (fun _ => None))
        (mkEffect (errno_ret ENOMEM) [] []) statat_ns_model in
  call 79 0 0 (statat_mem []) = CheckOk statat_ns_model []
  /\ call 79 0 0 (fun _ => None) = CheckOk statat_ns_model []
  /\ call 79 0 0 (statat_mem [47; 116; 109; 112; 47; 122; 101; 114; 111]%Z)
     = CheckOk statat_ns_model []
  /\ call 79 0 0 (fun a => if bv_eqb a 0x2000 then Some 102 else None)
     = CheckOk statat_ns_model []
  /\ call 78 0 16 (statat_mem []) = CheckOk statat_ns_model [].
Proof. vm_compute; split_conj; check_eq. Qed.

(** ...and not with the copy-in on a name no answer reads and then
    fails for memory: the empty one, an unmapped one, and the one whose
    second byte faults, whose -ENOMEM under AT_EMPTY_PATH reads the
    lead byte alone
    ([newfstatat_empty_path_getname_enomem_reads_the_lead_byte]). *)
Example newfstatat_getname_enomem_with_the_copyin_rejected :
  check_syscall
    (mkInput 79 [AT_FDCWD; 0x2000; 0; 0; 0; 0] (statat_mem []) (fun _ => None))
    (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret ENOMEM) [] []))
    statat_ns_model
  = CheckReject
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret ENOMEM) [] []))
       statat_ns_model
     = CheckReject
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; 0; Z_to_bv 64 AT_EMPTY_PATH; 0; 0]
          (fun a => if bv_eqb a 0x2000 then Some 102 else None) (fun _ => None))
       (with_copyins [(0x2000, 2%nat)] (mkEffect (errno_ret ENOMEM) [] []))
       statat_ns_model
     = CheckReject
  /\ check_syscall
       (mkInput 78 [AT_FDCWD; 0x2000; 0; 16; 0; 0] (statat_mem []) (fun _ => None))
       (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret ENOMEM) [] []))
       statat_ns_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** UNDER AT_EMPTY_PATH THE FETCH READS THE LEAD BYTE BEFORE IT
    ALLOCATES.  [__getname_maybe_null] loads that byte with [get_user]
    (fs/namei.c:231, Linux v6.18.46) and calls [getname_flags] (236)
    only on a readable byte that is not NUL, so [__getname]'s -ENOMEM
    (146-148) carries the one-byte read [(pathp, 1)]
    ([Stat.statat_lead_reads]): on a name whose second byte faults, and
    on an ordinary absent name. *)
Example newfstatat_empty_path_getname_enomem_reads_the_lead_byte :
  let call mp := check_syscall
        (mkInput 79 [AT_FDCWD; 0x2000; 0; Z_to_bv 64 AT_EMPTY_PATH; 0; 0] mp
           (fun _ => None))
        (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret ENOMEM) [] []))
        statat_ns_model in
  call (fun a => if bv_eqb a 0x2000 then Some 102 else None)
    = CheckOk statat_ns_model []
  /\ call (statat_mem [47; 116; 109; 112; 47; 122; 101; 114; 111]%Z)
     = CheckOk statat_ns_model [].
Proof. vm_compute; split_conj; check_eq. Qed.

(** ...and never with nothing read: the lead byte's [get_user]
    (fs/namei.c:231) comes before the [getname_flags] (236) whose
    [__getname] fails, so under AT_EMPTY_PATH an -ENOMEM with no
    copy-in is a ledger no kernel writes, on either name.  The one-byte
    ledger is AT_EMPTY_PATH's: plain [getname] allocates before it
    reads, so without the flag the same name's -ENOMEM with that ledger
    is refused. *)
Example newfstatat_empty_path_getname_enomem_without_the_lead_byte_rejected :
  let call mp := check_syscall
        (mkInput 79 [AT_FDCWD; 0x2000; 0; Z_to_bv 64 AT_EMPTY_PATH; 0; 0] mp
           (fun _ => None))
        (mkEffect (errno_ret ENOMEM) [] []) statat_ns_model in
  call (fun a => if bv_eqb a 0x2000 then Some 102 else None) = CheckReject
  /\ call (statat_mem [47; 116; 109; 112; 47; 122; 101; 114; 111]%Z) = CheckReject
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; 0; 0; 0; 0]
          (fun a => if bv_eqb a 0x2000 then Some 102 else None) (fun _ => None))
       (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret ENOMEM) [] []))
       statat_ns_model
     = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** A name with no NUL in its first PATH_MAX bytes under AT_EMPTY_PATH
    ([Cases.Fs.Namei.mem_long_name], 'a' from 0x2000): its lead byte
    reads, so [getname_flags] runs, and its first copy fills
    EMBEDDED_NAME_MAX = 4064 bytes ([Fs.Namei.embedded_name_max]).  So
    -ENOMEM is admitted with the first copy's 4064 bytes read (the
    re-copy's [kzalloc], fs/namei.c:189-193), which hold the lead byte,
    and with the lead byte alone ([__getname], 146-148, after the
    [get_user] at 231); it is refused with nothing read and with all of
    PATH_MAX read, which only the second copy does, and the second
    copy's -ENAMETOOLONG (207-211) carries the whole. *)
Example newfstatat_empty_path_long_name_enomem_carries_the_first_copy :
  let call ci e := check_syscall
        (mkInput 79 [AT_FDCWD; 0x2000; 0; Z_to_bv 64 AT_EMPTY_PATH; 0; 0]
           Cases.Fs.Namei.mem_long_name (fun _ => None))
        (with_copyins ci (mkEffect (errno_ret e) [] [])) statat_ns_model in
  call [(0x2000, 4064%nat)] ENOMEM = CheckOk statat_ns_model []
  /\ call [(0x2000, 1%nat)] ENOMEM = CheckOk statat_ns_model []
  /\ call [] ENOMEM = CheckReject
  /\ call [(0x2000, 4096%nat)] ENOMEM = CheckReject
  /\ call [(0x2000, 4096%nat)] ENAMETOOLONG = CheckOk statat_ns_model [].
Proof. vm_compute; split_conj; check_eq. Qed.

(** ...and where [getname_flags] is not reached, no -ENOMEM.  Under
    AT_EMPTY_PATH a lead byte that faults is [__getname_maybe_null]'s
    own -EFAULT (fs/namei.c:231-232) and a NUL one is no name at all
    (233-234), both before anything is allocated: the first answers
    -EFAULT alone, and the second stats the working folder, here into a
    [statbuf] above the user range, so [cp_new_stat]'s -EFAULT stands
    alone (fs/stat.c:542-546).  A [bufsiz] of 0 is [do_readlinkat]'s
    -EINVAL ahead of [getname_flags] (fs/stat.c:571-572).  And on the
    empty name the walk's -EACCES is refused: no component is walked. *)
Example newfstatat_getname_enomem_needs_getname :
  check_syscall
    (mkInput 79 [AT_FDCWD; 0x2000; 0; Z_to_bv 64 AT_EMPTY_PATH; 0; 0]
       (fun _ => None) (fun _ => None))
    (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret EFAULT) [] []))
    statat_ns_model
  = CheckOk statat_ns_model []
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; 0; Z_to_bv 64 AT_EMPTY_PATH; 0; 0]
          (fun _ => None) (fun _ => None))
       (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret ENOMEM) [] []))
       statat_ns_model
     = CheckReject
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; 0; Z_to_bv 64 AT_EMPTY_PATH; 0; 0]
          (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] [])
       statat_ns_model
     = CheckReject
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; Z_to_bv 64 (2 ^ 63); Z_to_bv 64 AT_EMPTY_PATH; 0; 0]
          (statat_mem []) (fun _ => None))
       (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret EFAULT) [] []))
       statat_ns_model
     = CheckOk statat_ns_model []
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; Z_to_bv 64 (2 ^ 63); Z_to_bv 64 AT_EMPTY_PATH; 0; 0]
          (statat_mem []) (fun _ => None))
       (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret ENOMEM) [] []))
       statat_ns_model
     = CheckReject
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; Z_to_bv 64 (2 ^ 63); Z_to_bv 64 AT_EMPTY_PATH; 0; 0]
          (statat_mem []) (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] [])
       statat_ns_model
     = CheckReject
  /\ check_syscall
       (mkInput 78 [AT_FDCWD; 0x2000; 0; 0; 0; 0] (statat_mem []) (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] [])
       statat_ns_model
     = CheckReject
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0x2000; 0; 0; 0; 0] (statat_mem []) (fun _ => None))
       (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret EACCES) [] []))
       statat_ns_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A NULL PATHNAME UNDER AT_EMPTY_PATH IS DECLINED
    ([Stat.statat_null_name]).  [getname_maybe_null] returns NULL for it
    without loading a byte (include/linux/fs.h:2955-2956, Linux
    v6.18.46), so [vfs_fstatat] stats the working folder for AT_FDCWD
    (the NULL name is "" to the walk, [__set_nameidata], fs/namei.c:668,
    Linux v6.18.46) and the descriptor itself for a dfd of 0 or more
    (fs/stat.c:372-373, Linux v6.18.46), whatever address 0 holds.
    Declined with address 0 unmapped, where the body would answer
    -EFAULT; with a NUL there, where it would stat the folder; and beside
    AT_SYMLINK_NOFOLLOW with dirfd 3.  Without AT_EMPTY_PATH the same
    NULL is plain getname's -EFAULT, from [getname_flags]
    (fs/namei.c:161-165, Linux v6.18.46), still answered with its one
    attempted byte. *)
Example newfstatat_null_name_under_at_empty_path_declines :
  check_syscall
    (mkInput 79 [AT_FDCWD; 0; 0x3000; Z_to_bv 64 AT_EMPTY_PATH; 0; 0]
       (fun _ => None) (fun _ => None))
    (with_copyins [(0, 1%nat)] (mkEffect (errno_ret EFAULT) [] []))
    statat_ns_model
  = CheckUnmodeled
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0; 0x3000; Z_to_bv 64 AT_EMPTY_PATH; 0; 0]
          (fun a => if bv_eqb a 0 then Some 0 else None) (fun _ => None))
       (mkEffect 0 [] [])
       statat_ns_model
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 79 [3; 0; 0x3000; Z_to_bv 64 (AT_EMPTY_PATH + AT_SYMLINK_NOFOLLOW)%Z; 0; 0]
          (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] [])
       statat_ns_model
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 79 [AT_FDCWD; 0; 0x3000; 0; 0; 0] (fun _ => None) (fun _ => None))
       (with_copyins [(0, 1%nat)] (mkEffect (errno_ret EFAULT) [] []))
       statat_ns_model
     = CheckOk statat_ns_model [].
Proof. split_conj; check_eq. Qed.

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
    offset.  The file is inode 1 of an image holding nothing else, and
    descriptor 3 holds it. *)
Definition fstat_path : Fs.path := [Z_to_bv 8 102].
Definition fstat_data : list byte := repeat (Z_to_bv 8 65) 9.
Definition fstat_data_grown : list byte := repeat (Z_to_bv 8 65) 12.

Definition fstat_model_of (d : list byte) : Model :=
  with_fds [(Z_to_bv 64 3, FdFile 1 (Z_to_bv 64 0))]
    (init_model [] 0 0 demo_sp demo_limit
       (demo_input (Fs.fs_create_file Fs.fs_empty fstat_path d) IEof)).

Definition fstat_model : Model := fstat_model_of fstat_data.
Definition fstat_model_grown : Model := fstat_model_of fstat_data_grown.

(** The same file and the same nine bytes, held through a READ-WRITE
    descriptor instead of a read-only one.  The pair of examples below is
    the whole difference the fourth file kind makes to [fstat]: none. *)
Definition fstat_model_rw : Model :=
  with_fds [(Z_to_bv 64 3, FdFileRW 1 (Z_to_bv 64 0))]
    (init_model [] 0 0 demo_sp demo_limit
       (demo_input (Fs.fs_create_file Fs.fs_empty fstat_path fstat_data) IEof)).

(** The same file after [unlinkat] removed its only name while
    descriptor 3 holds it: the inode keeps its row ([Fs.fs_unlink_file])
    and no name. *)
Definition fstat_model_unlinked : Model :=
  with_fs (Fs.fs_unlink_file (m_fs fstat_model) fstat_path 1 true) fstat_model.

(** The pin a first [fstat] of inode 1 leaves. *)
Definition pin1 (bs : list byte) (m : Model) : Model :=
  with_statpin (IdIno 1) (mkStatPin bs None false) m.

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
    what any kernel would report except the one link, which is the
    count of a file with one name. *)
Definition stat_of_nl (ino mode nlink size blocks tim : Z) : list byte :=
  Z_to_le_bytes 8 2049                                   (* st_dev *)
  ++ Z_to_le_bytes 8 ino                                 (* st_ino *)
  ++ Z_to_le_bytes 4 mode                                (* st_mode *)
  ++ Z_to_le_bytes 4 nlink                               (* st_nlink *)
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

Definition stat_of (ino mode size blocks tim : Z) : list byte :=
  stat_of_nl ino mode 1 size blocks tim.

(** The truthful answer for the nine-byte file: a regular file of length
    nine with one link.  Nothing but the width, the padding, the type's
    validity, the length and the link count is checked, so every other
    member here is free. *)
Definition stat_truthful : list byte := stat_of 4711 S_IFREG 9 8 1700000000.

(* ---- the accepting controls -------------------------------------------- *)

(** The first stat of a file is where its identity enters the model: the
    answer is admitted and BECOMES the pin. *)
Example fstat_first_answer_pins :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] []) fstat_model
  = CheckOk (pin1 stat_truthful fstat_model) [].
Proof. check_eq. Qed.

(** A FILE IS REPORTED AS A FILE.  The entry is an [Fs.EFile], which is
    a regular file ([Fs.Stat.fstat_file_spec] says why), so S_IFCHR with
    [st_size] 0 for the nine-byte file is inadmissible: [generic_fillattr]
    copies [i_mode] (fs/stat.c:90, Linux v6.18.46).  The accepting
    control is [fstat_first_answer_pins] just above: the same call with
    S_IFREG and nine bytes. *)
Example fstat_character_device_answer_for_a_file_rejected :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4711 S_IFCHR 0 0 1700000000)] []) fstat_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

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
  = CheckOk (pin1 stat_truthful fstat_model_rw) [].
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

(** …and the length BITES on the arm it is about.  Eight bytes where
    the map holds nine, under S_IFREG: inadmissible.  Paired with the
    control above, this attributes the rejection to the length rather
    than to the type. *)
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
    (pin1 stat_truthful fstat_model_grown)
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example fstat_grown_size_admitted :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4711 S_IFREG 12 8 1700000042)] [])
    (pin1 stat_truthful fstat_model_grown)
  = CheckOk (pin1 stat_truthful fstat_model_grown) [].
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
    (pin1 stat_truthful fstat_model)
  = CheckOk (pin1 stat_truthful fstat_model) [].
Proof. check_eq. Qed.

Example fstat_pinned_inode_defector_rejected :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4712 S_IFREG 9 8 1700000000)] [])
    (pin1 stat_truthful fstat_model)
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example fstat_inode_defector_is_itself_admissible_first :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4712 S_IFREG 9 8 1700000000)] []) fstat_model
  = CheckOk (pin1 (stat_of 4712 S_IFREG 9 8 1700000000)
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
    (pin1 stat_truthful fstat_model)
  = CheckOk (pin1 stat_truthful fstat_model) [].
Proof. check_eq. Qed.

(* ---- the set-id bits: a write or truncate clears them, nothing sets them - *)

(** The nine-byte file with the permission bits [perm] beside S_IFREG.
    The modes below are written in decimal: 2541 is 04755, 493 is 0755,
    3565 is 06755, 1517 is 02755, 3492 is 06644, 1444 is 02644, 2468 is
    04644, 420 is 0644 and 384 is 0600. *)
Definition stat_perm (perm : Z) : list byte := stat_of 4711 (S_IFREG + perm)%Z 9 8 1700000000.

(** A WRITE OR A TRUNCATE CLEARS S_ISUID, so a later stat of a file
    pinned as 04755 may report 0755.  [file_remove_privs] (a write,
    [shmem_file_write_iter], mm/shmem.c:3500, Linux v6.18.46) and
    [do_truncate] (fs/open.c:55-60) take their mask from
    [setattr_should_drop_suidgid] (fs/attr.c:63-79), which names S_ISUID
    whenever it is set and the caller lacks CAP_FSETID, and
    [notify_change] clears it (fs/attr.c:489-494); [generic_fillattr]
    reports the new mode (fs/stat.c:90).  The stat that shows the drop
    becomes the pin ([Fs.Stat.file_pin_after]).  Before the drop was
    admitted the model rejected this answer, and with it the true trace
    stat, write, stat of a setuid file. *)
Example fstat_setuid_cleared_after_the_pin_admitted :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 493)] [])
    (pin1 (stat_perm 2541) fstat_model)
  = CheckOk (pin1 (stat_perm 493) (pin1 (stat_perm 2541) fstat_model)) [].
Proof. check_eq. Qed.

(** …and the spec itself admits it: [check_syscall_sound_ok] carries the
    checker's verdict to [Specs.syscall_spec]. *)
Example fstat_spec_admits_a_setuid_drop :
  syscall_spec fstat_input (pin1 (stat_perm 2541) fstat_model)
    (Ok (mkEffect 0 [(4096, stat_perm 493)] [])
        (pin1 (stat_perm 493) (pin1 (stat_perm 2541) fstat_model)) []).
Proof. apply check_syscall_sound_ok. exact fstat_setuid_cleared_after_the_pin_admitted. Qed.

(** S_ISGID GOES WITH THE GROUP BITS.  Under S_IXGRP
    [setattr_should_drop_sgid] names it whenever it is set (fs/attr.c:33-45),
    so 06755 and 02755 may report 0755.  Without S_IXGRP it names it
    only for a caller outside the file's group ([in_group_or_capable],
    fs/inode.c:2910-2918), and the model knows neither the caller's
    groups nor its capabilities: 06644 may report 02644 (a caller in the
    group) or 0644 (one outside it), and the mode unchanged (a caller
    with CAP_FSETID, or no write at all). *)
Example fstat_setgid_cleared_as_the_group_bits_say_admitted :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 493)] [])
    (pin1 (stat_perm 3565) fstat_model)
  = CheckOk (pin1 (stat_perm 493) (pin1 (stat_perm 3565) fstat_model)) []
  /\ check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 493)] [])
       (pin1 (stat_perm 1517) fstat_model)
     = CheckOk (pin1 (stat_perm 493) (pin1 (stat_perm 1517) fstat_model)) []
  /\ check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 1444)] [])
       (pin1 (stat_perm 3492) fstat_model)
     = CheckOk (pin1 (stat_perm 1444) (pin1 (stat_perm 3492) fstat_model)) []
  /\ check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 420)] [])
       (pin1 (stat_perm 3492) fstat_model)
     = CheckOk (pin1 (stat_perm 420) (pin1 (stat_perm 3492) fstat_model)) []
  /\ check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 3492)] [])
       (pin1 (stat_perm 3492) fstat_model)
     = CheckOk (pin1 (stat_perm 3492) fstat_model) [].
Proof. split_conj; check_eq. Qed.

(** …but ONE KILL TAKES S_ISUID WITH S_ISGID.  The mask that names
    S_ISGID names S_ISUID too when it is set ([setattr_should_drop_suidgid],
    fs/attr.c:63-79), and under S_IXGRP the two go together.  So a set-id
    file never reports S_ISGID dropped beside a kept S_ISUID, and under
    S_IXGRP never S_ISUID dropped beside a kept S_ISGID. *)
Example fstat_setgid_dropped_without_setuid_rejected :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 2468)] [])
    (pin1 (stat_perm 3492) fstat_model)
  = CheckReject
  /\ check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 2541)] [])
       (pin1 (stat_perm 3565) fstat_model)
     = CheckReject
  /\ check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 1517)] [])
       (pin1 (stat_perm 3565) fstat_model)
     = CheckReject.
Proof. split_conj; vm_compute; reflexivity. Qed.

(** NO MODELED SYSCALL SETS A SET-ID BIT: there is no [chmod] arm, so a
    later stat that reports S_ISUID or S_ISGID the pin does not have is
    refused. *)
Example fstat_setuid_set_against_the_pin_rejected :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 2541)] [])
    (pin1 (stat_perm 493) fstat_model)
  = CheckReject
  /\ check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 1444)] [])
       (pin1 (stat_perm 420) fstat_model)
     = CheckReject.
Proof. split_conj; vm_compute; reflexivity. Qed.

(** THE REST OF THE MODE IS HELD WHOLE: 0644 then 0600 is refused, and
    so is a drop of S_ISUID that also takes the group and other bits. *)
Example fstat_permission_bits_held_against_the_pin :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 384)] [])
    (pin1 (stat_perm 420) fstat_model)
  = CheckReject
  /\ check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 448)] [])
       (pin1 (stat_perm 2541) fstat_model)
     = CheckReject.
Proof. split_conj; vm_compute; reflexivity. Qed.

(** …and so is every other stable member: a drop of S_ISUID does not
    let [st_ino] move with it. *)
Example fstat_setuid_cleared_with_another_inode_rejected :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4712 (S_IFREG + 493)%Z 9 8 1700000000)] [])
    (pin1 (stat_perm 2541) fstat_model)
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** A BIT ONCE SHOWN CLEARED STAYS CLEARED.  The stat that showed the
    drop is the pin now, so a stat after it may not show S_ISUID again,
    and the mode it showed is admitted with the model left as it is. *)
Example fstat_setuid_once_cleared_stays_cleared :
  check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 2541)] [])
    (pin1 (stat_perm 493) (pin1 (stat_perm 2541) fstat_model))
  = CheckReject
  /\ check_syscall fstat_input (mkEffect 0 [(4096, stat_perm 493)] [])
       (pin1 (stat_perm 493) (pin1 (stat_perm 2541) fstat_model))
     = CheckOk (pin1 (stat_perm 493) (pin1 (stat_perm 2541) fstat_model)) [].
Proof. split_conj; check_eq. Qed.

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

(** A FILE UNLINKED WHILE OPEN IS STILL A REGULAR FILE OF ITS LENGTH,
    WITH NO LINK.  [generic_fillattr] copies [i_nlink] (fs/stat.c:91,
    Linux v6.18.46), and [vfs_unlink]'s [drop_nlink] has taken it to 0
    ([shmem_unlink], mm/shmem.c:4006-4019), while the inode lives on under the
    descriptor until the last [iput] ([iput_final], fs/inode.c:1874-1915).
    So the answer with [st_nlink] 0 and the nine bytes' length is
    admitted, and the one-link answer the file gave before is refused. *)
Example fstat_unlinked_open_file_has_no_link :
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of_nl 4711 S_IFREG 0 9 8 1700000000)] [])
    fstat_model_unlinked
  = CheckOk (pin1 (stat_of_nl 4711 S_IFREG 0 9 8 1700000000)
               fstat_model_unlinked) []
  /\ check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] [])
       fstat_model_unlinked
     = CheckReject.
Proof. split; check_eq. Qed.

(** ...and the link count FOLLOWS the names: a second name for the same
    inode makes it 2 ([vfs_link]'s [inc_nlink] through [shmem_link],
    mm/shmem.c:3965-3995), so the one-link answer is refused there too. *)
Example fstat_two_names_two_links :
  let m := with_fs (Fs.fs_set (m_fs fstat_model) [Z_to_bv 8 103] (EFile 1))
             fstat_model in
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of_nl 4711 S_IFREG 2 9 8 1700000000)] []) m
  = CheckOk (pin1 (stat_of_nl 4711 S_IFREG 2 9 8 1700000000) m) []
  /\ check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] []) m
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- the pin dies with the file it identifies -------------------------- *)

(** [unlinkat] destroys the inode once no descriptor holds it, and Linux
    gives the NEXT file created at that name a different one -- so a pin
    that outlived the removal would reject the conforming trace
    `create f; fstat; close; unlink f; create f; fstat`.  [State.with_fs]
    drops it, and these two say that it drops the right ones: gone when
    the inode has neither a name nor a row, kept when the same inode is
    merely rewritten.  Neither is reachable from a checker verdict,
    because the second create makes a file before any [fstat] can look
    -- the two states differ only in a field no syscall reports. *)

Example fstat_pin_dies_with_the_file :
  m_statpins (with_fs Fs.fs_empty (pin1 stat_truthful fstat_model))
  = [].
Proof. vm_compute. reflexivity. Qed.

Example fstat_pin_survives_a_rewrite :
  m_statpins (with_fs (Fs.fs_set_ino_data (m_fs fstat_model) 1 fstat_data_grown)
                (pin1 stat_truthful fstat_model))
  = [(IdIno 1, mkStatPin stat_truthful None false)].
Proof. vm_compute. reflexivity. Qed.

(** …and the consequence at the checker: with the pin gone, the file
    created next at that name may report ANY inode, exactly as a first
    stat may.  Read beside [fstat_pinned_inode_defector_rejected], which
    is the same struct against a live pin, this is what says the
    rejection there is about the file's identity and not about the
    number.  (The model hands the new file the number 1 again: its
    numbers are its own, and [st_ino] is the environment's.) *)
Example fstat_recreated_file_takes_a_new_inode :
  let m := with_fs (Fs.fs_create_file Fs.fs_empty fstat_path fstat_data)
             (with_fs Fs.fs_empty (pin1 stat_truthful fstat_model)) in
  check_syscall fstat_input
    (mkEffect 0 [(4096, stat_of 4712 S_IFREG 9 8 1700000000)] []) m
  = CheckOk (pin1 (stat_of 4712 S_IFREG 9 8 1700000000) m) [].
Proof. check_eq. Qed.

(* ------------------------------------------------------- readlinkat (78) *)

(** THIS ARM HAD NO WORKED EXAMPLE AT ALL, and that is how it kept
    answering -EINVAL for a trailing separator on a regular file where
    Linux answers -ENOTDIR.  It was rewritten from a blanket -EINVAL to
    a full match on the walk and arrived with no pin to hold any row of
    it down.  One example per row now, and the two that changed carry
    the rejecting half as well. *)

Definition rl_mem (bs : list Z) : word -> option byte :=
  fun a => if (8192 <=? bv_unsigned a)%Z
           then nth_error (map (fun z => Z_to_bv 8 z) (bs ++ [0%Z]))
                  (Z.to_nat (bv_unsigned a - 8192))
           else None.

Definition rl_file : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([102], SFile [104; 105])]) IEof).

Definition rl_dir : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([100], SDir)]) IEof).

Definition rl_empty : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof).

(** A RESOLVED ENTRY IS -EINVAL, because no entry kind here is a
    symlink.  That is the row the pre-namespace arm answered to
    everything. *)
Example readlinkat_found_file_is_einval :
  check_syscall
    (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0] (rl_mem [102]%Z)
       (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EINVAL) [] []))
    rl_file
  = CheckOk rl_file []
  (* a DIRECTORY is the same -EINVAL, and for the same reason *)
  /\ check_syscall
       (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0] (rl_mem [100]%Z)
          (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EINVAL) [] []))
       rl_dir
     = CheckOk rl_dir [].
Proof. split; check_eq. Qed.

(** THE TRAILING SEPARATOR IS THE CELL THE ARM WAS MISSING.
    [do_readlinkat] reaches [path_lookupat], whose closing
    LOOKUP_DIRECTORY test answers -ENOTDIR for a component that cannot
    be looked up in, and [lookup_last] is what sets that flag for a
    LAST_NORM component a separator follows.  So "f/" on a regular file
    is -ENOTDIR, and the -EINVAL the arm used to give is rejected.  A
    DIRECTORY with a separator keeps its -EINVAL, which is what says the
    cell reads the ENTRY and not the separator alone. *)
Example readlinkat_trailing_separator_needs_a_directory :
  check_syscall
    (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0] (rl_mem [102; 47]%Z)
       (fun _ => None))
    (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
    rl_file
  = CheckOk rl_file []
  /\ check_syscall
       (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0] (rl_mem [102; 47]%Z)
          (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret EINVAL) [] []))
       rl_file
     = CheckReject
  /\ check_syscall
       (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0] (rl_mem [100; 47]%Z)
          (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret EINVAL) [] []))
       rl_dir
     = CheckOk rl_dir [].
Proof. split; [|split]; check_eq. Qed.

(** A NAME THE WALK DOES NOT FIND IN THE /dev SUBTREE IS -ENOENT for
    [readlinkat] too, as anywhere else: the image describes /dev
    completely at launch ([Fs.dev_dir]).  A link body for it is
    refused, the same name under /tmp gives the same -ENOENT, and the
    declared device is an ordinary -EINVAL. *)
Example readlinkat_under_dev_absent_is_enoent :
  check_syscall
    (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0]
       (rl_mem [47; 100; 101; 118; 47; 122; 101; 114; 111]%Z) (fun _ => None))
    (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
    rl_empty
  = CheckOk rl_empty []
  /\ check_syscall
       (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0]
          (rl_mem [47; 100; 101; 118; 47; 122; 101; 114; 111]%Z) (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret EINVAL) [] []))
       rl_empty
     = CheckReject
  /\ check_syscall
       (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0]
          (rl_mem [47; 116; 109; 112; 47; 122; 101; 114; 111]%Z)
          (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
       rl_empty
     = CheckOk rl_empty []
  (* and the declared device is still an ordinary -EINVAL, because it is
     found and is not a symlink *)
  /\ check_syscall
       (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0]
          (rl_mem [47; 100; 101; 118; 47; 110; 117; 108; 108]%Z)
          (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret EINVAL) [] []))
       rl_empty
     = CheckOk rl_empty [].
Proof. split_conj; check_eq. Qed.

(** THE WALK'S OTHER OUTCOMES each get their own errno, where the
    pre-namespace arm gave -EINVAL to all of them: an absent last
    component is -ENOENT and a non-directory in the PREFIX is
    -ENOTDIR. *)
Example readlinkat_walk_outcomes :
  check_syscall
    (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0] (rl_mem [102]%Z)
       (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOENT) [] []))
    rl_empty
  = CheckOk rl_empty []
  /\ check_syscall
       (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0] (rl_mem [102; 47; 120]%Z)
          (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
       rl_file
     = CheckOk rl_file []
  (* and -EINVAL is rejected on both, which is what says the arm stopped
     answering it to everything *)
  /\ check_syscall
       (mkInput 78 [AT_FDCWD; 8192; 4096; 64; 0; 0] (rl_mem [102]%Z)
          (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EINVAL) [] []))
       rl_empty
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** A NONPOSITIVE bufsiz IS -EINVAL AHEAD OF THE PATHNAME, so that arm
    carries NO copy-in — [do_readlinkat]'s first statement runs before
    [getname_flags].  The ledger is what pins the ordering: with the
    range attached the same call is rejected. *)
Example readlinkat_nonpositive_bufsiz_records_no_copyin :
  check_syscall
    (mkInput 78 [AT_FDCWD; 8192; 4096; 0; 0; 0] (rl_mem [102]%Z)
       (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) rl_file
  = CheckOk rl_file []
  /\ check_syscall
       (mkInput 78 [AT_FDCWD; 8192; 4096; 0; 0; 0] (rl_mem [102]%Z)
          (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EINVAL) [] []))
       rl_file
     = CheckReject.
Proof. split; check_eq. Qed.

(* ----------------------------------------- links, names and identities *)

(** A run of calls, each accepted with no event, then the verdict of the
    last one. *)
Fixpoint st_seq (steps : list (SyscallInput * SyscallEffect)) (m : Model)
    : check_result :=
  match steps with
  | [] => CheckOk m []
  | [(i, e)] => check_syscall i e m
  | (i, e) :: r =>
      match check_syscall i e m with
      | CheckOk m' [] => st_seq r m'
      | c => c
      end
  end.

Definition st_ok (c : check_result) : Prop :=
  match c with CheckOk _ _ => True | _ => False end.

(** [newfstatat(AT_FDCWD, <bs>, 4096, flag)] answering [eff]. *)
Definition st_stat_eff (bs : list Z) (flag : Z) (eff : SyscallEffect)
    : SyscallInput * SyscallEffect :=
  (mkInput 79 [AT_FDCWD; 0x2000; 4096; Z_to_bv 64 flag; 0; 0] (statat_mem bs) stat_out,
   with_copyins [(0x2000, S (length bs))] eff).

Definition st_stat (bs : list Z) (flag : Z) (out : list byte)
    : SyscallInput * SyscallEffect :=
  st_stat_eff bs flag (mkEffect 0 [(4096, out)] []).

(** A pathname call [nr(AT_FDCWD, <bs>, a2)] answering [eff]. *)
Definition st_call (nr : word) (bs : list Z) (a2 : word) (eff : SyscallEffect)
    : SyscallInput * SyscallEffect :=
  (mkInput nr [AT_FDCWD; 0x2000; a2; 0; 0; 0] (statat_mem bs) (fun _ => None),
   with_copyins [(0x2000, S (length bs))] eff).

(** "tmp000000.flac", nine bytes (inode 1), a regular file of the
    working folder, and the record a kernel hands back for it: S_IFREG
    with the permission bits 0644, nine bytes, one link, [st_ino]
    4711. *)
Definition st_flac_name : list Z :=
  [116; 109; 112; 48; 48; 48; 48; 48; 48; 46; 102; 108; 97; 99]%Z.

Definition st_flac : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [(map (fun z => Z_to_bv 8 z) st_flac_name, SFile fstat_data)])
       IEof).

Definition st_flac_stat : list byte := stat_of 4711 (S_IFREG + 420)%Z 9 8 1700000000.

(** NEWFSTATAT OF A REGULAR FILE NAMED RELATIVE TO THE WORKING FOLDER
    DELIVERS THE FILE'S RECORD.  [vfs_fstatat] (fs/stat.c:365-379, Linux
    v6.18.46) fetches the name and calls [vfs_statx] (fs/stat.c:341-363),
    which takes the flag word 0 (348-350) and asks for the last link to
    be followed ([statx_lookup_flags], fs/stat.c:284-294).  The name is
    resolved by [filename_lookup] (fs/namei.c:2697-2716), and a relative
    name starts at the working directory ([path_init],
    fs/namei.c:2589-2604).  The record is the inode's
    ([generic_fillattr], fs/stat.c:82-113: the inode number at 89, the
    mode at 90, the size at 95), and [cp_new_stat] (fs/stat.c:470-507)
    copies it out, so the call returns 0 (536-547).  The first record is
    admitted and becomes the inode's pin, and a second stat must repeat
    its [st_ino].  A record with a size other than nine, or a type other
    than S_IFREG, is refused, and so is -ENOENT, the answer for a name
    the folder does not hold. *)
Example newfstatat_relative_regular_file_delivers_its_stat :
  st_seq [st_stat st_flac_name 0 st_flac_stat] st_flac
  = CheckOk (pin1 st_flac_stat st_flac) []
  /\ st_ok (st_seq [st_stat st_flac_name 0 st_flac_stat;
                    st_stat st_flac_name 0 st_flac_stat] st_flac)
  /\ st_seq [st_stat st_flac_name 0 st_flac_stat;
             st_stat st_flac_name 0 (stat_of 4712 (S_IFREG + 420)%Z 9 8 1700000000)] st_flac
     = CheckReject
  /\ st_seq [st_stat st_flac_name 0 (stat_of 4711 (S_IFREG + 420)%Z 8 8 1700000000)] st_flac
     = CheckReject
  /\ st_seq [st_stat st_flac_name 0 (stat_of 4711 (S_IFDIR + 493)%Z 9 8 1700000000)] st_flac
     = CheckReject
  /\ st_seq [st_stat_eff st_flac_name 0 (mkEffect (errno_ret ENOENT) [] [])] st_flac
     = CheckReject.
Proof. vm_compute. split_conj; try exact I; check_eq. Qed.

(** "f" nine bytes (inode 1), "l" -> "f". *)
Definition st_links : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([102], SFile fstat_data); ([108], SLink [102])]) IEof).

(** NEWFSTATAT WITH AT_SYMLINK_NOFOLLOW ON A LINK IS THE LINK: S_IFLNK|0777,
    with [st_size] the body's length ([generic_fillattr]'s mode and size,
    fs/stat.c:90 and :95, on the link's own inode, whose [i_size] tmpfs
    sets to the body's length, mm/shmem.c:4140, :4158).  Without the
    flag it is the file the link names; -ELOOP is refused beside that
    answer, since a walk of one link counts at most two of the 41
    [reserve_stack] needs (fs/namei.c:1878-1879;
    [Fs.Namei.walk_errnos]), and beside the unfollowed one too. *)
Example newfstatat_nofollow_on_a_link_is_the_link :
  st_ok (st_seq [st_stat [108]%Z AT_SYMLINK_NOFOLLOW
                   (stat_of_nl 4800 (S_IFLNK + 511)%Z 1 1 0 1700000000)] st_links)
  /\ st_seq [st_stat [108]%Z AT_SYMLINK_NOFOLLOW
               (stat_of_nl 4800 (S_IFLNK + 511)%Z 1 9 0 1700000000)] st_links = CheckReject
  /\ st_seq [st_stat [108]%Z AT_SYMLINK_NOFOLLOW stat_truthful] st_links = CheckReject
  /\ st_seq [st_stat_eff [108]%Z AT_SYMLINK_NOFOLLOW (mkEffect (errno_ret ELOOP) [] [])]
       st_links = CheckReject
  (* followed, it is the file *)
  /\ st_ok (st_seq [st_stat [108]%Z 0 stat_truthful] st_links)
  /\ st_seq [st_stat [108]%Z 0 (stat_of_nl 4800 (S_IFLNK + 511)%Z 1 1 0 1700000000)] st_links
     = CheckReject
  /\ st_seq [st_stat_eff [108]%Z 0 (mkEffect (errno_ret ELOOP) [] [])] st_links
     = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** "f" (inode 1) and "g", a second name of the same inode. *)
Definition st_two : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (Fs.fs_set (demo_fs [([102], SFile fstat_data)]) (wk [103]) (EFile 1))
       IEof).

(** TWO NAMES OF ONE FILE GIVE ONE [st_ino] AND [st_nlink] 2: the pin is
    the inode's ([State.IdIno]), so a stat of "g" after a stat of "f"
    must report the pair "f" reported, and the link count is the names'
    ([vfs_link]'s [inc_nlink] through [shmem_link], mm/shmem.c:3965-3995;
    [generic_fillattr]'s [nlink], fs/stat.c:91). *)
Example two_names_give_one_st_ino_and_two_links :
  st_ok (st_seq [st_stat [102]%Z 0 (stat_of_nl 4711 S_IFREG 2 9 8 1700000000);
                 st_stat [103]%Z 0 (stat_of_nl 4711 S_IFREG 2 9 8 1700000000)] st_two)
  /\ st_seq [st_stat [102]%Z 0 (stat_of_nl 4711 S_IFREG 2 9 8 1700000000);
             st_stat [103]%Z 0 (stat_of_nl 4712 S_IFREG 2 9 8 1700000000)] st_two
     = CheckReject
  /\ st_seq [st_stat [103]%Z 0 (stat_of_nl 4711 S_IFREG 1 9 8 1700000000)] st_two
     = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** UNLINKING ONE OF TWO NAMES KEEPS THE DATA UNDER THE OTHER, WITH ONE
    LINK: [vfs_unlink]'s [drop_nlink] ([shmem_unlink], mm/shmem.c:4006-4019)
    takes the count from 2 to 1 and the inode stays. *)
Example unlinking_one_of_two_names_keeps_the_other :
  match (let '(i, e) := st_call 35 [102]%Z 0 (mkEffect 0 [] []) in
         check_syscall i e st_two) with
  | CheckOk m [] =>
      file_at (m_fs m) (wk [103]) = Some fstat_data
      /\ Fs.fs_lookup (m_fs m) (wk [102]) = None
  | _ => False
  end
  /\ st_ok (st_seq [st_call 35 [102]%Z 0 (mkEffect 0 [] []);
                    st_stat [103]%Z 0 (stat_of_nl 4711 S_IFREG 1 9 8 1700000000)] st_two)
  /\ st_seq [st_call 35 [102]%Z 0 (mkEffect 0 [] []);
             st_stat [103]%Z 0 (stat_of_nl 4711 S_IFREG 2 9 8 1700000000)] st_two
     = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** A FILE UNLINKED WHILE OPEN STAYS READABLE through its descriptor, and
    "/proc/self/fd/3" opens it again, on the same inode ([proc_fd_link]
    hands back the open file's own path, fs/proc/fd.c, and following it
    reopens that dentry).  [fstat_unlinked_open_file_has_no_link] above
    is its [st_nlink] 0. *)
Example unlinked_open_file_reads_and_reopens :
  match check_syscall (mkInput 63 [3; 4096; 9; 0; 0; 0] (fun _ => None) stat_out)
          (mkEffect 9 [(4096, fstat_data)] []) fstat_model_unlinked with
  | CheckOk _ [] => True
  | _ => False
  end
  /\ match check_syscall
             (mkInput 56 [AT_FDCWD; 0x2000; 0; 0; 0; 0]
                (statat_mem [47; 112; 114; 111; 99; 47; 115; 101; 108; 102; 47; 102; 100; 47; 51]%Z)
                (fun _ => None))
             (with_copyins [(0x2000, 16%nat)] (mkEffect 0 [] [])) fstat_model_unlinked with
     | CheckOk m [] => fd_lookup (m_fds m) 0 = Some (FdFile 1 (Z_to_bv 64 0))
     | _ => False
     end.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** A FOLDER'S [st_nlink] UNDER BOTH RULES ACROSS [mkdirat].  "d" is an
    empty folder: 2 under the counting rule (tmpfs's [inc_nlink] at
    mm/shmem.c:3133-3134 over [inode_init_always]'s 1, fs/inode.c:242;
    ramfs's [ramfs_get_inode], fs/ramfs/inode.c:82) and 1 under the fixed one
    (btrfs, fs/btrfs/inode.c:7020-7031), which no supported kernel
    gives ([Fs.DirLinks]).  The first stat that
    tells them apart chooses the rule and the pin keeps it: after
    "d/e" is made, a counting folder reports 3 ([shmem_mkdir]'s
    [inc_nlink(dir)], mm/shmem.c:3952) and a fixed one still 1. *)
Definition st_dir : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs [([100], SDir)]) IEof).

Definition dir_stat (nl : Z) : list byte := stat_of_nl 4711 S_IFDIR nl 0 0 1700000000.

Definition mkdir_d_e : SyscallInput * SyscallEffect :=
  st_call 34 [100; 47; 101]%Z 493 (mkEffect 0 [] []).

Example folder_link_count_under_both_rules :
  st_ok (st_seq [st_stat [100]%Z 0 (dir_stat 2); mkdir_d_e;
                 st_stat [100]%Z 0 (dir_stat 3)] st_dir)
  /\ st_seq [st_stat [100]%Z 0 (dir_stat 2); mkdir_d_e;
             st_stat [100]%Z 0 (dir_stat 1)] st_dir = CheckReject
  /\ st_seq [st_stat [100]%Z 0 (dir_stat 2); mkdir_d_e;
             st_stat [100]%Z 0 (dir_stat 2)] st_dir = CheckReject
  /\ st_ok (st_seq [st_stat [100]%Z 0 (dir_stat 1); mkdir_d_e;
                    st_stat [100]%Z 0 (dir_stat 1)] st_dir)
  /\ st_seq [st_stat [100]%Z 0 (dir_stat 1); mkdir_d_e;
             st_stat [100]%Z 0 (dir_stat 3)] st_dir = CheckReject
  (* a count neither rule gives is refused at the first stat *)
  /\ st_seq [st_stat [100]%Z 0 (dir_stat 5)] st_dir = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** A FOLDER REMOVED AND MADE AGAIN AT ONE NAME IS A NEW FOLDER, and the
    stat pin of the old one dies with it.  [shmem_rmdir] drops the
    folder's last link (mm/shmem.c:4032-4040, Linux v6.18.46) and the
    inode is freed at its last [iput] ([iput_final], fs/inode.c:1874-1915);
    [mkdirat] then makes a fresh inode through [shmem_get_inode], whose
    number [shmem_reserve_inode] hands out anew (mm/shmem.c:3084, :3088,
    :3094).  So the second folder may report any [st_ino], and a pin kept
    on the key ([State.StatId]'s [IdDir]) would refuse the conforming
    trace `stat d; rmdir d; mkdir d; stat d`; [State.statpins_restrict]
    drops it when the key stops holding a folder.  The control: with the
    folder left in place, the second stat must repeat the pinned
    [st_ino]. *)
Definition dir_stat_ino (ino nl : Z) : list byte :=
  stat_of_nl ino S_IFDIR nl 0 0 1700000000.

Definition rmdir_d : SyscallInput * SyscallEffect :=
  st_call 35 [100]%Z (Z_to_bv 64 AT_REMOVEDIR) (mkEffect 0 [] []).

Definition mkdir_d : SyscallInput * SyscallEffect :=
  st_call 34 [100]%Z 493 (mkEffect 0 [] []).

Example folder_pin_dies_with_rmdir_then_mkdir :
  st_ok (st_seq [st_stat [100]%Z 0 (dir_stat_ino 4711 2); rmdir_d; mkdir_d;
                 st_stat [100]%Z 0 (dir_stat_ino 4712 2)] st_dir)
  (* the same number again is admitted too: nothing ties the new folder
     to the old *)
  /\ st_ok (st_seq [st_stat [100]%Z 0 (dir_stat_ino 4711 2); rmdir_d; mkdir_d;
                    st_stat [100]%Z 0 (dir_stat_ino 4711 2)] st_dir)
  (* the control: the folder left in place keeps its st_ino *)
  /\ st_seq [st_stat [100]%Z 0 (dir_stat_ino 4711 2);
             st_stat [100]%Z 0 (dir_stat_ino 4712 2)] st_dir = CheckReject
  (* and between the rmdir and the mkdir the name is gone *)
  /\ st_seq [st_stat [100]%Z 0 (dir_stat_ino 4711 2); rmdir_d;
             st_stat [100]%Z 0 (dir_stat_ino 4711 2)] st_dir = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** "f" and "g", nine bytes each (inodes 1 and 2), two links "l" and "m",
    both -> "f", and an empty folder "d". *)
Definition st_two_links : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([102], SFile fstat_data); ([103], SFile fstat_data);
                          ([108], SLink [102]); ([109], SLink [102]); ([100], SDir)]) IEof).

(** A [struct stat] with every member the pins below compare given
    apart: the link count, [st_rdev], the size, the block count and the
    three timestamps (their nanosecond halves 0). *)
Definition stat_full (ino mode nl rdev size blocks ta tm tc : Z) : list byte :=
  Z_to_le_bytes 8 2049 ++ Z_to_le_bytes 8 ino ++ Z_to_le_bytes 4 mode ++ Z_to_le_bytes 4 nl
  ++ Z_to_le_bytes 4 1000 ++ Z_to_le_bytes 4 1000 ++ Z_to_le_bytes 8 rdev ++ Z_to_le_bytes 8 0
  ++ Z_to_le_bytes 8 size ++ Z_to_le_bytes 4 4096 ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 8 blocks
  ++ Z_to_le_bytes 8 ta ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 tm ++ Z_to_le_bytes 8 0
  ++ Z_to_le_bytes 8 tc ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0.

(** lstat of "l" (one byte of body), stat of /dev/null (S_IFCHR 0666,
    [st_rdev] 259, 1:3, no size and no blocks) and stat of "d". *)
Definition lstat_l (nl blocks ta tm tc : Z) : SyscallInput * SyscallEffect :=
  st_stat [108]%Z AT_SYMLINK_NOFOLLOW
    (stat_full 4800 (S_IFLNK + 511)%Z nl 0 1 blocks ta tm tc).

Definition stat_devnull_nl (nl ta tm tc : Z) : SyscallInput * SyscallEffect :=
  st_stat [47; 100; 101; 118; 47; 110; 117; 108; 108]%Z 0
    (stat_full 17 (S_IFCHR + 438)%Z nl 259 0 0 ta tm tc).

Definition stat_d (nl size blocks ta tm tc : Z) : SyscallInput * SyscallEffect :=
  st_stat [100]%Z 0 (stat_full 4711 S_IFDIR nl 0 size blocks ta tm tc).

Definition unlink_m : SyscallInput * SyscallEffect :=
  st_call 35 [109]%Z 0 (mkEffect 0 [] []).

Definition unlink_g : SyscallInput * SyscallEffect :=
  st_call 35 [103]%Z 0 (mkEffect 0 [] []).

(** A LINK'S PIN HOLDS ITS LINK COUNT, [st_blocks], [st_mtime] AND
    [st_ctime] FROM ONE lstat TO THE NEXT ([Fs.Stat.stat_pin_held]).
    [generic_fillattr] reads them off the inode (fs/stat.c:91-106, Linux
    v6.18.46); nothing writes a link's body, and its count and ctime move
    only when one of its names is removed ([simple_unlink],
    fs/libfs.c:787-795; [shmem_unlink], mm/shmem.c:4016-4019, Linux
    v6.18.46).  Its [st_atime] stays free: [readlinkat] and a walk that
    follows the link touch it (fs/stat.c:589, fs/namei.c:1936).  The
    one-byte body of "l" is kept inline, so 8 blocks is refused at any
    stat ([Uapi.stat_lnk_blocks_ok]).  The unlink of the other link "m"
    releases the count and the ctime, since "m" may have been a second
    name of "l" ([State.statpins_release_links]): there the count falls
    and the ctime moves, and the next lstat holds them again; the unlink
    of the file "g" releases nothing. *)
Example link_pin_holds_its_count_blocks_mtime_and_ctime :
  let T := 1700000000%Z in
  st_ok (st_seq [lstat_l 1 0 T T T; lstat_l 1 0 T T T] st_two_links)
  /\ st_seq [lstat_l 1 0 T T T; lstat_l 2 0 T T T] st_two_links = CheckReject
  /\ st_seq [lstat_l 1 0 T T T; lstat_l 1 8 T T T] st_two_links = CheckReject
  /\ st_seq [lstat_l 1 0 T T T; lstat_l 1 0 T (T + 1) T] st_two_links = CheckReject
  /\ st_seq [lstat_l 1 0 T T T; lstat_l 1 0 T T (T + 1)] st_two_links = CheckReject
  (* the atime is free *)
  /\ st_ok (st_seq [lstat_l 1 0 T T T; lstat_l 1 0 (T + 1) T T] st_two_links)
  (* the unlink of another link releases the count and the ctime *)
  /\ st_ok (st_seq [lstat_l 2 0 T T T; unlink_m; lstat_l 1 0 T T (T + 5)] st_two_links)
  (* and the next lstat holds it again *)
  /\ st_seq [lstat_l 2 0 T T T; unlink_m; lstat_l 1 0 T T (T + 5);
             lstat_l 2 0 T T (T + 5)] st_two_links = CheckReject
  (* the unlink of a regular file's name releases nothing *)
  /\ st_seq [lstat_l 2 0 T T T; unlink_g; lstat_l 1 0 T T T] st_two_links = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** A DEVICE NODE'S PIN HOLDS ITS LINK COUNT AND ITS THREE TIMESTAMP
    PAIRS ([Fs.Stat.stat_pin_held]): no arm makes or removes a device
    name, and no call the model answers on /dev/null touches the inode
    ([read_null], drivers/char/mem.c:412-416; [write_null],
    drivers/char/mem.c:418-422; Linux v6.18.46), the unlink of a link
    included. *)
Example device_pin_holds_its_count_and_timestamps :
  let T := 1700000000%Z in
  st_ok (st_seq [stat_devnull_nl 1 T T T; stat_devnull_nl 1 T T T] st_two_links)
  /\ st_seq [stat_devnull_nl 1 T T T; stat_devnull_nl 2 T T T] st_two_links = CheckReject
  /\ st_seq [stat_devnull_nl 1 T T T; stat_devnull_nl 1 (T + 1) T T] st_two_links
     = CheckReject
  /\ st_seq [stat_devnull_nl 1 T T T; stat_devnull_nl 1 T (T + 1) T] st_two_links
     = CheckReject
  /\ st_seq [stat_devnull_nl 1 T T T; stat_devnull_nl 1 T T (T + 1)] st_two_links
     = CheckReject
  /\ st_seq [stat_devnull_nl 1 T T T; unlink_m; stat_devnull_nl 2 T T (T + 5)] st_two_links
     = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** A FOLDER'S PIN HOLDS ITS [st_blocks], 0 for a folder's whole life on
    tmpfs and ramfs ([__shmem_get_inode], mm/shmem.c:3096;
    [ramfs_dir_inode_operations], fs/ramfs/inode.c:191, Linux v6.18.46),
    and asserted 0 at every stat besides
    ([first_stat_carries_what_tmpfs_and_ramfs_fix] below), and holds
    neither its [st_size], which stays within the names' bound
    ([Uapi.stat_dir_size_ok]), nor its timestamps: a name made in it moves
    them ([shmem_mknod], mm/shmem.c:3899-3900), and [getdents64] the
    atime (fs/readdir.c:111).  So across [mkdirat] of "d/e" the count is
    3, the size and times may move, and the blocks may not. *)
Example folder_pin_holds_its_blocks :
  let T := 1700000000%Z in
  st_ok (st_seq [stat_d 2 40 0 T T T; stat_d 2 40 0 T T T] st_two_links)
  /\ st_seq [stat_d 2 40 0 T T T; stat_d 2 40 8 T T T] st_two_links = CheckReject
  (* the size and the times are free *)
  /\ st_ok (st_seq [stat_d 2 40 0 T T T; stat_d 2 60 0 (T + 1) (T + 2) (T + 2)]
              st_two_links)
  /\ st_ok (st_seq [stat_d 2 40 0 T T T; mkdir_d_e; stat_d 3 60 0 T (T + 2) (T + 2)]
              st_two_links)
  /\ st_seq [stat_d 2 40 0 T T T; mkdir_d_e; stat_d 3 60 8 T (T + 2) (T + 2)] st_two_links
     = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** A FOLDER'S [st_size] IS 0, OR A MULTIPLE OF 20 OF AT LEAST 40 AND 20
    PER NAME ([Uapi.stat_dir_size_ok]): ramfs keeps every folder at the 0
    [inode_init_always_gfp] gives it (fs/inode.c:251), and tmpfs makes a
    folder at [2 * BOGO_DIRENT_SIZE] ([__shmem_get_inode],
    mm/shmem.c:3136) and adds [BOGO_DIRENT_SIZE] for each name made in it
    ([shmem_mknod], mm/shmem.c:3899); [BOGO_DIRENT_SIZE] is 20
    (mm/shmem.c:92).  The names the image shows are a
    lower bound ([Fs.fs_dir_names]), so a size above the least one is
    admitted.  The empty "d" admits 0, 40 and 60 and refuses 1, 20 and
    50; once "d/e" is made it refuses 40 and admits 60 and 0.  The root
    holds "/dev" at least, so 40 is refused there and 0 admitted (its
    first stat may report the fixed rule's count, 1). *)
Definition stat_root (size : Z) : SyscallInput * SyscallEffect :=
  st_stat [47]%Z 0 (stat_full 4711 S_IFDIR 1 0 size 0 1700000000 1700000000 1700000000).

Example folder_size_is_bounded_by_its_names :
  let T := 1700000000%Z in
  st_ok (st_seq [stat_d 2 0 0 T T T] st_two_links)
  /\ st_ok (st_seq [stat_d 2 40 0 T T T] st_two_links)
  /\ st_ok (st_seq [stat_d 2 60 0 T T T] st_two_links)
  /\ st_seq [stat_d 2 1 0 T T T] st_two_links = CheckReject
  /\ st_seq [stat_d 2 20 0 T T T] st_two_links = CheckReject
  /\ st_seq [stat_d 2 50 0 T T T] st_two_links = CheckReject
  (* a name made in it *)
  /\ st_seq [mkdir_d_e; stat_d 3 40 0 T T T] st_two_links = CheckReject
  /\ st_ok (st_seq [mkdir_d_e; stat_d 3 60 0 T T T] st_two_links)
  /\ st_ok (st_seq [mkdir_d_e; stat_d 3 0 0 T T T] st_two_links)
  (* the root *)
  /\ st_seq [stat_root 40] st_two_links = CheckReject
  /\ st_ok (st_seq [stat_root 0] st_two_links).
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** A [struct stat] like [stat_full] with [st_blksize] given too. *)
Definition stat_bs (ino mode nl rdev size blksize blocks ta tm tc : Z) : list byte :=
  Z_to_le_bytes 8 2049 ++ Z_to_le_bytes 8 ino ++ Z_to_le_bytes 4 mode ++ Z_to_le_bytes 4 nl
  ++ Z_to_le_bytes 4 1000 ++ Z_to_le_bytes 4 1000 ++ Z_to_le_bytes 8 rdev ++ Z_to_le_bytes 8 0
  ++ Z_to_le_bytes 8 size ++ Z_to_le_bytes 4 blksize ++ Z_to_le_bytes 4 0
  ++ Z_to_le_bytes 8 blocks
  ++ Z_to_le_bytes 8 ta ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 tm ++ Z_to_le_bytes 8 0
  ++ Z_to_le_bytes 8 tc ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0.

(** lstat of "l" with its inode number given. *)
Definition lstat_li (ino nl blocks ta tm tc : Z) : SyscallInput * SyscallEffect :=
  st_stat [108]%Z AT_SYMLINK_NOFOLLOW
    (stat_full ino (S_IFLNK + 511)%Z nl 0 1 blocks ta tm tc).

(** "f" nine bytes (inode 1), "n" -> a body of 130 bytes, which tmpfs
    keeps in a page of its own (mm/shmem.c:4159-4170, Linux v6.18.46),
    and "m" -> "f". *)
Definition st_long_link : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([102], SFile fstat_data); ([110], SLink (repeat (Z_to_bv 8 97) 130));
                          ([109], SLink [102])]) IEof).

(** lstat of "n". *)
Definition lstat_n (nl blocks ta tm tc : Z) : SyscallInput * SyscallEffect :=
  st_stat [110]%Z AT_SYMLINK_NOFOLLOW
    (stat_full 4900 (S_IFLNK + 511)%Z nl 0 130 blocks ta tm tc).

(** THE UNLINK OF ANOTHER LINK RELEASES A LINK'S COUNT AND CTIME, AND
    NOTHING ELSE ([State.statpins_release_links]).  Had "m" been a
    second name of "l", [simple_unlink] (fs/libfs.c:787-795) and
    [shmem_unlink] (mm/shmem.c:4016-4019, Linux v6.18.46) would have
    lowered the count of "l"'s inode and set its ctime; neither replaces
    an inode, so "l" still reports the same device, number, mode,
    owners, block size, [st_blocks] and [st_mtime] ([generic_fillattr],
    fs/stat.c:88-106).  So after the unlink "l" may report a count of 1
    and a later ctime, or the same two, but not another [st_ino] and not
    another [st_mtime]; a long body's [st_blocks] is held across it too;
    and the stat after it is the pin again, whose count and ctime the
    next stat must repeat. *)
Example link_release_keeps_the_identity :
  let T := 1700000000%Z in
  (* lstat("l") st_ino 4800, unlinkat("m"), lstat("l") st_ino 4801 *)
  st_seq [lstat_li 4800 2 0 T T T; unlink_m; lstat_li 4801 1 0 T T (T + 5)] st_two_links
  = CheckReject
  /\ st_seq [lstat_li 4800 2 0 T T T; unlink_m; lstat_li 4801 2 0 T T T] st_two_links
     = CheckReject
  (* the mtime is held across it *)
  /\ st_seq [lstat_li 4800 2 0 T T T; unlink_m; lstat_li 4800 1 0 T (T + 5) (T + 5)]
       st_two_links = CheckReject
  (* and a long body's blocks *)
  /\ st_seq [lstat_n 2 8 T T T; unlink_m; lstat_n 1 0 T T (T + 5)] st_long_link
     = CheckReject
  /\ st_ok (st_seq [lstat_n 2 8 T T T; unlink_m; lstat_n 1 8 T T (T + 5)] st_long_link)
  (* the count and the ctime may move across it, or stay *)
  /\ st_ok (st_seq [lstat_li 4800 2 0 T T T; unlink_m; lstat_li 4800 1 0 T T (T + 5)]
              st_two_links)
  /\ st_ok (st_seq [lstat_li 4800 2 0 T T T; unlink_m; lstat_li 4800 2 0 T T T]
              st_two_links)
  (* and the stat after it is the pin: its count and ctime are held again *)
  /\ st_seq [lstat_li 4800 2 0 T T T; unlink_m; lstat_li 4800 1 0 T T (T + 5);
             lstat_li 4800 1 0 T T (T + 6)] st_two_links = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** A FIRST STAT ALREADY CARRIES WHAT tmpfs AND ramfs FIX, before any
    pin is there to hold it: a folder's [st_blocks] 0, [st_rdev] 0 and
    [st_blksize] 4096 ([Uapi.stat_dir_fixed]); a link's whole [st_mode]
    S_IFLNK|0777, its [st_rdev] 0, its [st_blksize] 4096, and its
    [st_blocks] 0 for a body kept inline and 0 or 8 for a body in a page
    ([Uapi.stat_lnk_fixed]); a device node's [st_blksize] 4096
    ([Uapi.stat_chrdev_ok]); a regular file's [st_rdev] 0 and its
    [st_blksize] 4096 too ([Uapi.stat_reg_fixed]): the configuration of
    record has no huge pages for [shmem_getattr] to raise it to
    ([Uapi.stat_page_blksize]).  Each is a member the pin holds, so a
    first stat that got one wrong would be held wrong for good. *)
Example first_stat_carries_what_tmpfs_and_ramfs_fix :
  let T := 1700000000%Z in
  (* a folder: blocks, device number, block size *)
  st_seq [stat_d 2 40 8 T T T] st_two_links = CheckReject
  /\ st_ok (st_seq [stat_d 2 40 0 T T T] st_two_links)
  /\ st_seq [st_stat [100]%Z 0 (stat_bs 4711 S_IFDIR 2 1 40 4096 0 T T T)] st_two_links
     = CheckReject
  /\ st_seq [st_stat [100]%Z 0 (stat_bs 4711 S_IFDIR 2 0 40 512 0 T T T)] st_two_links
     = CheckReject
  (* a link: mode, device number, block size, blocks *)
  /\ st_seq [st_stat [108]%Z AT_SYMLINK_NOFOLLOW (stat_bs 4800 S_IFLNK 1 0 1 4096 0 T T T)]
       st_two_links = CheckReject
  /\ st_seq [st_stat [108]%Z AT_SYMLINK_NOFOLLOW
               (stat_bs 4800 (S_IFLNK + 420)%Z 1 0 1 4096 0 T T T)] st_two_links
     = CheckReject
  /\ st_ok (st_seq [lstat_l 1 0 T T T] st_two_links)
  /\ st_seq [st_stat [108]%Z AT_SYMLINK_NOFOLLOW
               (stat_bs 4800 (S_IFLNK + 511)%Z 1 1 1 4096 0 T T T)] st_two_links
     = CheckReject
  /\ st_seq [st_stat [108]%Z AT_SYMLINK_NOFOLLOW
               (stat_bs 4800 (S_IFLNK + 511)%Z 1 0 1 512 0 T T T)] st_two_links
     = CheckReject
  /\ st_seq [lstat_l 1 8 T T T] st_two_links = CheckReject
  /\ st_ok (st_seq [lstat_n 1 8 T T T] st_long_link)
  /\ st_ok (st_seq [lstat_n 1 0 T T T] st_long_link)
  /\ st_seq [lstat_n 1 16 T T T] st_long_link = CheckReject
  (* a device node: block size *)
  /\ st_seq [st_stat [47; 100; 101; 118; 47; 110; 117; 108; 108]%Z 0
               (stat_bs 17 (S_IFCHR + 438)%Z 1 259 0 512 0 T T T)] st_two_links
     = CheckReject
  /\ st_ok (st_seq [stat_devnull_nl 1 T T T] st_two_links)
  (* a regular file: device number and block size *)
  /\ st_seq [st_stat [102]%Z 0 (stat_bs 4711 S_IFREG 1 1 9 4096 8 T T T)] st_two_links
     = CheckReject
  /\ st_seq [st_stat [102]%Z 0 (stat_bs 4711 S_IFREG 1 0 9 512 8 T T T)] st_two_links
     = CheckReject
  /\ st_ok (st_seq [st_stat [102]%Z 0 (stat_bs 4711 S_IFREG 1 0 9 4096 8 T T T)]
              st_two_links).
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** THE TRUE TRACE, stat, truncate, stat, of a setuid file through a
    read-write descriptor.  [ftruncate(3, 9)] keeps the length and still
    drops S_ISUID: [do_ftruncate] calls [do_truncate] whatever the
    length (fs/open.c:195), and [do_truncate] asks
    [dentry_needs_remove_privs] first (fs/open.c:55-60).  So the second
    stat may report 0755, or 04755 again for a caller with CAP_FSETID; a
    stat after the drop may not report 04755, and no truncate sets the
    bit on a file the first stat saw without it. *)
Definition st_fstat (out : list byte) : SyscallInput * SyscallEffect :=
  (fstat_input, mkEffect 0 [(4096, out)] []).

Definition st_ftruncate (len : word) : SyscallInput * SyscallEffect :=
  (mkInput 46 [3; len; 0; 0; 0; 0] (fun _ => None) (fun _ => None), mkEffect 0 [] []).

Example fstat_setuid_cleared_across_an_ftruncate :
  st_ok (st_seq [st_fstat (stat_perm 2541); st_ftruncate 9; st_fstat (stat_perm 493)]
           fstat_model_rw)
  /\ st_ok (st_seq [st_fstat (stat_perm 2541); st_ftruncate 9; st_fstat (stat_perm 2541)]
              fstat_model_rw)
  /\ st_seq [st_fstat (stat_perm 2541); st_ftruncate 9; st_fstat (stat_perm 493);
             st_fstat (stat_perm 2541)] fstat_model_rw = CheckReject
  /\ st_seq [st_fstat (stat_perm 493); st_ftruncate 9; st_fstat (stat_perm 2541)]
       fstat_model_rw = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** A FOLDER'S S_ISGID IS HELD: only a regular file's set-id bits are
    ever cleared ([setattr_should_drop_suidgid] tests S_ISREG,
    fs/attr.c:63-79, and so does [file_remove_privs_flags],
    fs/inode.c:2253), and a setgid folder is the common kind.  "d"
    pinned as 02755 may not report 0755, and repeats 02755. *)
Example folder_setgid_is_held :
  st_seq [st_stat [100]%Z 0 (stat_of_nl 4711 (S_IFDIR + 1517)%Z 2 40 0 1700000000);
          st_stat [100]%Z 0 (stat_of_nl 4711 (S_IFDIR + 493)%Z 2 40 0 1700000000)] st_dir
  = CheckReject
  /\ st_ok (st_seq [st_stat [100]%Z 0 (stat_of_nl 4711 (S_IFDIR + 1517)%Z 2 40 0 1700000000);
                    st_stat [100]%Z 0 (stat_of_nl 4711 (S_IFDIR + 1517)%Z 2 40 0 1700000000)]
              st_dir).
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** READLINKAT COPIES THE BODY UP TO [bufsiz] AND NO NUL ([readlink_copy],
    fs/namei.c:5419-5429), the body read to its first NUL (:5469).  The
    empty pathname names the working folder, which is not a link:
    -ENOENT ([do_readlinkat]). *)
Definition rl_link : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([108], SLink [97; 98; 99]); ([110], SLink [97; 98; 0; 99])])
       IEof).

Definition rl_call (bs : list Z) (bufsiz : word) (eff : SyscallEffect) : check_result :=
  check_syscall (mkInput 78 [AT_FDCWD; 8192; 4096; bufsiz; 0; 0] (rl_mem bs) stat_out)
    (with_copyins [(8192, S (length bs))] eff) rl_link.

Example readlinkat_copies_the_body_up_to_bufsiz :
  rl_call [108]%Z 64 (mkEffect 3 [(4096, [97; 98; 99])] []) = CheckOk rl_link []
  /\ rl_call [108]%Z 2 (mkEffect 2 [(4096, [97; 98])] []) = CheckOk rl_link []
  /\ rl_call [108]%Z 2 (mkEffect 3 [(4096, [97; 98; 99])] []) = CheckReject
  (* no NUL is written after the body *)
  /\ rl_call [108]%Z 64 (mkEffect 4 [(4096, [97; 98; 99; 0])] []) = CheckReject
  (* the body is read to its first NUL *)
  /\ rl_call [110]%Z 64 (mkEffect 2 [(4096, [97; 98])] []) = CheckOk rl_link []
  /\ rl_call []%Z 64 (mkEffect (errno_ret ENOENT) [] []) = CheckOk rl_link [].
Proof. split_conj; check_eq. Qed.

(** [bufsiz] IS AN [int]: [do_readlinkat] (fs/stat.c:563-572, Linux
    v6.18.46) takes [int bufsiz] and opens with [if (bufsiz <= 0) return
    -EINVAL;], before [getname_flags].  So a register whose low half is
    0xFFFFFFFF (-1) or 0x80000000 (INT_MIN) is -EINVAL with no copy-in and
    nothing written to [buf], and a copy of the body there is refused;
    0x7FFFFFFF, the largest [int], copies a short body whole. *)
Example readlinkat_negative_int_bufsiz_is_einval :
  check_syscall (mkInput 78 [AT_FDCWD; 8192; 4096; 4294967295; 0; 0] (rl_mem [108]%Z) stat_out)
    (mkEffect (errno_ret EINVAL) [] []) rl_link = CheckOk rl_link []
  /\ check_syscall (mkInput 78 [AT_FDCWD; 8192; 4096; 2147483648; 0; 0] (rl_mem [108]%Z) stat_out)
    (mkEffect (errno_ret EINVAL) [] []) rl_link = CheckOk rl_link []
  /\ rl_call [108]%Z 4294967295 (mkEffect 3 [(4096, [97; 98; 99])] []) = CheckReject
  /\ rl_call [108]%Z 2147483648 (mkEffect 3 [(4096, [97; 98; 99])] []) = CheckReject
  /\ rl_call [108]%Z 2147483647 (mkEffect 3 [(4096, [97; 98; 99])] []) = CheckOk rl_link [].
Proof. split_conj; check_eq. Qed.

(** THE LARGEST [int] [bufsiz], 0x7FFFFFFF, on a three-byte link body
    copies the body whole, three bytes and no NUL: [readlink_copy] copies
    [min(len, buflen)] (fs/namei.c:5419-5429, Linux v6.18.46).  The
    register's high half is not read ([do_readlinkat]'s [int bufsiz],
    fs/stat.c:563-564), so 0xFFFFFFFF7FFFFFFF answers the same; on the
    body with an inner NUL two bytes are copied ([strlen],
    fs/namei.c:5469); and a two-byte answer on the three-byte body is
    refused.  Each is decided by [vm_compute] through the checker, which
    is what [Stat.readlink_count] is written for: it never builds a
    [nat] as large as [bufsiz]. *)
Example readlinkat_largest_int_bufsiz_copies_a_short_body :
  rl_call [108]%Z 2147483647 (mkEffect 3 [(4096, [97; 98; 99])] []) = CheckOk rl_link []
  /\ rl_call [108]%Z 18446744071562067967 (mkEffect 3 [(4096, [97; 98; 99])] [])
     = CheckOk rl_link []
  /\ rl_call [110]%Z 2147483647 (mkEffect 2 [(4096, [97; 98])] []) = CheckOk rl_link []
  /\ rl_call [108]%Z 2147483647 (mkEffect 2 [(4096, [97; 98])] []) = CheckReject.
Proof. split_conj; check_eq. Qed.

(** AN EMPTY BODY IS A COPY OF NO BYTE, and that returns 0 wherever
    [buf] points: [readlink_copy] (fs/namei.c:5419-5429, Linux v6.18.46)
    calls [copy_to_user(buf, link, 0)], whose [_inline_copy_to_user]
    (include/linux/uaccess.h:190-200) returns the 0 bytes it did not
    copy when [access_ok] refuses [buf], so no -EFAULT is reached
    ([Stat.readlink_copy_faults]).  tmpfs holds such a link when an
    initramfs entry names one ([shmem_symlink] takes ""), and a body
    whose first byte is NUL is read as empty (:5469).  Above TASK_SIZE
    (0x900000000000), "e" (the empty body) and "z" (a NUL first) answer
    0 with no write and refuse -EFAULT; at a writable [buf] "e" answers
    0 too; and the three-byte body "l" at the same [buf] still faults,
    -EFAULT and not 0. *)
Definition rl_body_model : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([101], SLink []); ([108], SLink [97; 98; 99]);
                          ([122], SLink [0; 97])])
       IEof).

Definition rl_call_at (bs : list Z) (buf : word) (eff : SyscallEffect) : check_result :=
  check_syscall (mkInput 78 [AT_FDCWD; 8192; buf; 64; 0; 0] (rl_mem bs) stat_out)
    (with_copyins [(8192, S (length bs))] eff) rl_body_model.

Example readlinkat_empty_body_returns_zero_whatever_buf :
  rl_call_at [101]%Z 158329674399744 (mkEffect 0 [] []) = CheckOk rl_body_model []
  /\ rl_call_at [122]%Z 158329674399744 (mkEffect 0 [] []) = CheckOk rl_body_model []
  /\ rl_call_at [101]%Z 4096 (mkEffect 0 [] []) = CheckOk rl_body_model []
  /\ rl_call_at [101]%Z 158329674399744 (mkEffect (errno_ret EFAULT) [] []) = CheckReject
  /\ rl_call_at [122]%Z 158329674399744 (mkEffect (errno_ret EFAULT) [] []) = CheckReject
  /\ rl_call_at [108]%Z 158329674399744 (mkEffect (errno_ret EFAULT) [] [])
     = CheckOk rl_body_model []
  /\ rl_call_at [108]%Z 158329674399744 (mkEffect 0 [] []) = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A STAT OF A DEVICE DESCRIPTOR HOLDS ITS NODE, under the node's key
    when the node is the image's one of its kind and under the
    DESCRIPTOR otherwise ([Stat.fstat_devfd_spec]).  A null-device
    descriptor carries no key and may come from any null-device node,
    and two nodes are two inodes, each allocated by the file system
    ([__shmem_get_inode], mm/shmem.c:3084-3097; [ramfs_get_inode],
    fs/ramfs/inode.c:60-68, Linux v6.18.46), but the descriptor holds one
    of them for its whole life, and [vfs_fstat] reports that held
    file's inode at every call (fs/stat.c:276-281; [generic_fillattr],
    fs/stat.c:82-94).  With /dev/x beside /dev/null, two stats of
    descriptor 3 with nothing between them report one [st_ino]; the pin
    is the descriptor's ([State.IdDevFd]), not /dev/null's; the device's
    own members (S_IFCHR, [st_rdev] 1:3) are asserted; and with
    /dev/null the image's one null node, the first stat pins it and a
    second must repeat its [st_ino]. *)
Definition devx_key : Fs.path := Fs.child_key Fs.dev_dir [Z_to_bv 8 120].

Definition devfd_model (fs0 : Fs.Fs) : Model :=
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input fs0 IEof) in
  with_fds (fd_insert (m_fds m) 3 (FdDevNull true false)) m.

Definition devfd_stat (ino rdev : Z) : list byte :=
  stat_full ino (S_IFCHR + 438)%Z 1 rdev 0 0 1700000000 1700000000 1700000000.

Definition devfd_two : Model :=
  devfd_model (Fs.fs_set (demo_fs []) devx_key (EDev DevNull)).

Example device_descriptor_stat_holds_its_node :
  let one := devfd_model (demo_fs []) in
  st_seq [st_fstat (devfd_stat 17 259); st_fstat (devfd_stat 18 259)] devfd_two
  = CheckReject
  /\ st_ok (st_seq [st_fstat (devfd_stat 17 259); st_fstat (devfd_stat 17 259)] devfd_two)
  /\ (match st_seq [st_fstat (devfd_stat 17 259)] devfd_two with
      | CheckOk m _ =>
          statpin_lookup (m_statpins m) (IdDev Fs.devnull_key) = None
          /\ statpin_lookup (m_statpins m) (IdDevFd 3 DevNull)
             = Some (mkStatPin (devfd_stat 17 259) None false)
      | _ => False end)
  /\ st_seq [st_fstat (devfd_stat 17 265)] devfd_two = CheckReject
  /\ st_seq [st_fstat (devfd_stat 17 259); st_fstat (devfd_stat 18 259)] one = CheckReject
  /\ st_ok (st_seq [st_fstat (devfd_stat 17 259); st_fstat (devfd_stat 17 259)] one).
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** THE DESCRIPTOR'S PIN DIES WITH ITS FILE.  [close(3)] and an [openat]
    of "/dev/x" that answers 3 give number 3 another file, on the other
    node, so its stat may report another [st_ino]; so does a [dup3] of a
    descriptor on "/dev/x" onto 3, which leaves at 3 an entry equal to
    the old one ([do_dup2] stores the other file there,
    fs/file.c:1303-1304, Linux v6.18.46).  The opening arm and [dup3]
    drop number 3's pin as they install ([State.with_fd_unpinned],
    [State.with_fd_dup]).  The control: an [openat] of "/dev/x" that
    answers 4 leaves 3's file and its pin alone. *)
Definition devx_name : list Z := [47; 100; 101; 118; 47; 120]%Z.

Definition devx_open (ret : word) : SyscallInput * SyscallEffect :=
  st_call 56 devx_name 0 (mkEffect ret [] []).

Definition close3 : SyscallInput * SyscallEffect :=
  (mkInput 57 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None), mkEffect 0 [] []).

Definition dup3_4_3 : SyscallInput * SyscallEffect :=
  (mkInput 24 [4; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None), mkEffect 3 [] []).

Example device_descriptor_pin_dies_with_its_file :
  st_ok (st_seq [st_fstat (devfd_stat 17 259); close3; devx_open 3;
                 st_fstat (devfd_stat 18 259)] devfd_two)
  /\ st_ok (st_seq [st_fstat (devfd_stat 17 259); devx_open 4; dup3_4_3;
                    st_fstat (devfd_stat 18 259)] devfd_two)
  (* the new file's stat is held in its turn *)
  /\ st_seq [st_fstat (devfd_stat 17 259); devx_open 4; dup3_4_3;
             st_fstat (devfd_stat 18 259); st_fstat (devfd_stat 17 259)] devfd_two
     = CheckReject
  (* the control: an open at another number keeps 3's pin *)
  /\ st_seq [st_fstat (devfd_stat 17 259); devx_open 4;
             st_fstat (devfd_stat 18 259)] devfd_two = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(** TWO NUMBERS OF ONE FILE REPORT ONE INODE.  [dup] installs at 4 the
    [struct file] number 3 holds ([SYSCALL_DEFINE1(dup)],
    fs/file.c:1457-1467, Linux v6.18.46), and [vfs_fstat] stats that file
    (fs/stat.c:276-281).  With /dev/x beside /dev/null, a stat of 4 must
    repeat the [st_ino] a stat of 3 reported before the [dup] (4 takes
    3's pin), and a stat of 3 the one a stat of 4 reported first (4 is
    paired with 3 while 3 has none, and the first stat pins both:
    [State.with_fd_dup], [State.with_statpin]).  A [dup3] of a
    descriptor on "/dev/x" onto 4 cuts 4's link alone: 4 may then report
    another [st_ino], in either order, and 3 still holds its own. *)
Definition fstat_at (fd : word) (out : list byte) : SyscallInput * SyscallEffect :=
  (mkInput 80 [fd; 4096; 0; 0; 0; 0] (fun _ => None) stat_out, mkEffect 0 [(4096, out)] []).

Definition dup_3 : SyscallInput * SyscallEffect :=
  (mkInput 23 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None), mkEffect 4 [] []).

Definition dup3_5_4 : SyscallInput * SyscallEffect :=
  (mkInput 24 [5; 4; 0; 0; 0; 0] (fun _ => None) (fun _ => None), mkEffect 4 [] []).

Example device_descriptor_dup_shares_its_pin :
  (* stat 3, dup, stat 4 *)
  st_seq [st_fstat (devfd_stat 17 259); dup_3; fstat_at 4 (devfd_stat 18 259)] devfd_two
  = CheckReject
  /\ st_ok (st_seq [st_fstat (devfd_stat 17 259); dup_3; fstat_at 4 (devfd_stat 17 259)]
              devfd_two)
  (* dup, stat 4 first, then stat 3 *)
  /\ st_seq [dup_3; fstat_at 4 (devfd_stat 17 259); st_fstat (devfd_stat 18 259)] devfd_two
     = CheckReject
  /\ st_ok (st_seq [dup_3; fstat_at 4 (devfd_stat 17 259); st_fstat (devfd_stat 17 259)]
              devfd_two)
  (* a dup3 of a descriptor on the other node onto 4 *)
  /\ st_ok (st_seq [st_fstat (devfd_stat 17 259); dup_3; devx_open 5; dup3_5_4;
                    fstat_at 4 (devfd_stat 18 259)] devfd_two)
  /\ st_ok (st_seq [dup_3; devx_open 5; dup3_5_4; fstat_at 4 (devfd_stat 18 259);
                    st_fstat (devfd_stat 17 259)] devfd_two)
  /\ st_seq [st_fstat (devfd_stat 17 259); dup_3; devx_open 5; dup3_5_4;
             fstat_at 4 (devfd_stat 18 259); st_fstat (devfd_stat 18 259)] devfd_two
     = CheckReject.
Proof. vm_compute. split_conj; try exact I; reflexivity. Qed.

(* -------------------------------------------------------------------------
   newfstatat(fd, "", st, AT_EMPTY_PATH) on a descriptor is fstat(fd, st).
   [getname_maybe_null] gives no name for "" under the flag, so
   [vfs_fstatat] takes [vfs_fstat] for a dfd of 0 or more (fs/stat.c:372-373,
   Linux v6.18.46), the stat [newfstat] gives (:550-559).  The empty name's
   one byte is in the ledger.
   ------------------------------------------------------------------------- *)

Definition statat_fd_input (fd flag : Z) : SyscallInput :=
  mkInput 79 [Z_to_bv 64 fd; 0x2000; 4096; Z_to_bv 64 flag; 0; 0] (statat_mem []) stat_out.

(** On a regular file: [fstat_first_answer_pins]' answer, pinned the same
    way, with or without AT_SYMLINK_NOFOLLOW.  Refused: the -ENOENT of a
    walk, a character device's stat, and a success on a closed number,
    whose answer is [fstat]'s -EBADF. *)
Example newfstatat_empty_name_on_a_file_is_its_fstat :
  check_syscall (statat_fd_input 3 AT_EMPTY_PATH)
    (with_copyins [(0x2000, 1%nat)] (mkEffect 0 [(4096, stat_truthful)] [])) fstat_model
  = CheckOk (pin1 stat_truthful fstat_model) []
  /\ check_syscall (statat_fd_input 3 (AT_EMPTY_PATH + AT_SYMLINK_NOFOLLOW))
       (with_copyins [(0x2000, 1%nat)] (mkEffect 0 [(4096, stat_truthful)] [])) fstat_model
     = CheckOk (pin1 stat_truthful fstat_model) []
  /\ check_syscall (statat_fd_input 3 AT_EMPTY_PATH)
       (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret ENOENT) [] [])) fstat_model
     = CheckReject
  /\ check_syscall (statat_fd_input 3 AT_EMPTY_PATH)
       (with_copyins [(0x2000, 1%nat)]
          (mkEffect 0 [(4096, stat_of 4711 S_IFCHR 0 0 1700000000)] [])) fstat_model
     = CheckReject
  /\ check_syscall (statat_fd_input 5 AT_EMPTY_PATH)
       (with_copyins [(0x2000, 1%nat)] (mkEffect (errno_ret EBADF) [] [])) fstat_model
     = CheckOk fstat_model []
  /\ check_syscall (statat_fd_input 5 AT_EMPTY_PATH)
       (with_copyins [(0x2000, 1%nat)] (mkEffect 0 [(4096, stat_truthful)] [])) fstat_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** On /dev/null: the device's stat is admitted and a stat with
    /dev/urandom's [st_rdev] (1:9) is refused, as [fstat] judges them
    ([device_descriptor_stat_holds_its_node]).  On a folder: the verdict
    is [fstat]'s, which is a judgement and not a decline.  On a channel:
    declined, as [fstat] declines it (its [st_mode] is the far end's). *)
Example newfstatat_empty_name_on_a_device_folder_channel :
  let dirm := with_fds [(Z_to_bv 64 3, FdDir Fs.default_cwd)] statat_ns_model in
  let dir_bytes := dir_stat 2 in
  (match check_syscall (statat_fd_input 3 AT_EMPTY_PATH)
           (with_copyins [(0x2000, 1%nat)] (mkEffect 0 [(4096, devfd_stat 17 259)] []))
           (devfd_model (demo_fs [])) with
   | CheckOk _ _ => True
   | _ => False
   end)
  /\ check_syscall (statat_fd_input 3 AT_EMPTY_PATH)
       (with_copyins [(0x2000, 1%nat)] (mkEffect 0 [(4096, devfd_stat 17 265)] []))
       (devfd_model (demo_fs []))
     = CheckReject
  /\ check_syscall (statat_fd_input 3 AT_EMPTY_PATH)
       (with_copyins [(0x2000, 1%nat)] (mkEffect 0 [(4096, dir_bytes)] [])) dirm
     = check_syscall (mkInput 80 [3; 4096; 0; 0; 0; 0] (fun _ => None) stat_out)
         (mkEffect 0 [(4096, dir_bytes)] []) dirm
  /\ check_syscall (mkInput 80 [3; 4096; 0; 0; 0; 0] (fun _ => None) stat_out)
       (mkEffect 0 [(4096, dir_bytes)] []) dirm <> CheckUnmodeled
  /\ check_syscall (statat_fd_input 1 AT_EMPTY_PATH)
       (with_copyins [(0x2000, 1%nat)] (mkEffect 0 [(4096, stat_truthful)] []))
       statat_ns_model
     = CheckUnmodeled.
Proof. vm_compute. split_conj; first [exact I | reflexivity | discriminate]. Qed.
