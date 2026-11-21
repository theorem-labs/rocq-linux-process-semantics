(** * LinuxProcessSem.Checks.Cases.Fs.Namei — worked examples over unlinkat (35), mkdirat (34)

    Mirrors [Sys/Fs/Namei.v], which answers to Linux [fs/namei.c]: this
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

(** Path bytes at 8192 for the examples below: 'a', NUL. *)
Definition mem_name_a : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 97        (* 'a' *)
           else if bv_eqb a 8193 then Some 0    (* NUL *)
           else None.

(** 'a', '/', NUL. *)
Definition mem_name_a_slash : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 97        (* 'a' *)
           else if bv_eqb a 8193 then Some 47   (* '/' *)
           else if bv_eqb a 8194 then Some 0    (* NUL *)
           else None.

(** '/', NUL — a path with no component at all. *)
Definition mem_name_root : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 47        (* '/' *)
           else if bv_eqb a 8193 then Some 0    (* NUL *)
           else None.

(** '.', NUL and '.', '.', NUL. *)
Definition mem_name_dot : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 46
           else if bv_eqb a 8193 then Some 0
           else None.

Definition mem_name_dotdot : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 46
           else if bv_eqb a 8193 then Some 46
           else if bv_eqb a 8194 then Some 0
           else None.

(** 'a', '/', 'b', NUL — a two-component path, which the walk takes
    one folder at a time. *)
Definition mem_name_a_b : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 97
           else if bv_eqb a 8193 then Some 47
           else if bv_eqb a 8194 then Some 98
           else if bv_eqb a 8195 then Some 0
           else None.

(** A PATHNAME FROM ITS BYTES, for the crossing pins below, whose four
    paths would otherwise want four more one-off memories. *)
Definition name_mem (bs : list Z) : word -> option byte :=
  fun a => if (8192 <=? bv_unsigned a)%Z
           then nth_error (map (fun z => Z_to_bv 8 z) (bs ++ [0%Z]))
                  (Z.to_nat (bv_unsigned a - 8192))
           else None.

(** The four CROSSING paths: a prefix that fails, and a last component
    that is not LAST_NORM.  'a' is a regular file in [ns_file_a] and
    absent in [ns_empty], so these read the two ways the parent walk can
    fail.  There is deliberately no root-form crossing: LAST_ROOT is a
    path of nothing but separators, which has no prefix to fail. *)
Definition mem_a_dotdot : word -> option byte := name_mem [97; 47; 46; 46]%Z.
Definition mem_a_dot : word -> option byte := name_mem [97; 47; 46]%Z.
Definition mem_m_dotdot : word -> option byte := name_mem [109; 47; 46; 46]%Z.
Definition mem_m_dot : word -> option byte := name_mem [109; 47; 46]%Z.

(** THE IMAGES.  [demo_fs] puts each plain name at the key it resolves
    to and ships the standard root and the chain to the working
    directory with it, which is what makes these images NAMESPACES a
    walk can reach rather than bare maps. *)
Definition ns_file_a : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([97], SFile [104])]) IEof).

Definition ns_empty_dir_a : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([97], SDir)]) IEof).

(** "a" a DIRECTORY holding "b". *)
Definition ns_dir_a_with_b : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input
       (Fs.fs_create_file (demo_fs [([97], SDir)])
          (Fs.child_key (wk [97]) [98]) [104])
       IEof).

Definition ns_empty : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof).

(* ------------------------------------------- separators are walked

   A pathname with a "/" in it is walked component by component, and a
   folder is an entry of the image: the walk reaches "a/b", and "a" is
   a directory because the image says so. *)

(** "a/b" is REMOVED.  This is the pin that would catch a spec that
    declined a pathname for holding a separator. *)
Example unlinkat_two_components_removes_the_key :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a_b (fun _ => None))
    (with_copyins [(8192, 4%nat)] (mkEffect 0 [] []))
    ns_dir_a_with_b
  = CheckOk (with_fs (Fs.fs_unlink_file (m_fs ns_dir_a_with_b)
                        (Fs.child_key (wk [97]) [98]) 1 false) ns_dir_a_with_b) [].
Proof. check_eq. Qed.

(** ...and unlinking the DIRECTORY "a" itself is -EISDIR. *)
Example unlinkat_directory_is_eisdir :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EISDIR) [] []))
    ns_dir_a_with_b
  = CheckOk ns_dir_a_with_b []
  (* and a kernel that claimed to have removed it is refused *)
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
       ns_dir_a_with_b
     = CheckReject.
Proof. split; check_eq. Qed.

(** The contrast, so a folder is a COMPONENT prefix and not a byte
    prefix: "ab" does not live under "a", and the removal of the file
    "a" goes through, leaving "ab" where it was.  The effect carries the
    pathname copy-in the spec records — two bytes, 'a' and the NUL —
    without which the checker rejects it.  The image left is stated as
    it is OBSERVED ([Fs.fs_observe]): "ab" holds inode 2 in the run and
    inode 1 in the one-file image, and the observation renumbers by
    name. *)
Example unlinkat_byte_prefix_is_not_a_directory :
  match check_syscall
          (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
          (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input (demo_fs [([97], SFile []); ([97; 98], SFile [104])])
                IEof)) with
  | CheckOk m [] =>
      Fs.fs_observe (m_fs m) = Fs.fs_observe (demo_fs [([97; 98], SFile [104])])
  | _ => False
  end.
Proof. check_eq. Qed.

(** A name UNDER A FILE is -ENOTDIR, the walk's own answer, and a
    confident -ENOENT is refused. *)
Example unlinkat_under_a_file_is_enotdir :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a_b (fun _ => None))
    (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
    ns_file_a
  = CheckOk ns_file_a []
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a_b (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_file_a
     = CheckReject.
Proof. split; check_eq. Qed.

(** A missing PROPER PREFIX is -ENOENT, and the two are told apart by
    what the prefix holds rather than by the spelling. *)
Example unlinkat_missing_prefix_is_enoent :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a_b (fun _ => None))
    (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_empty
  = CheckOk ns_empty [].
Proof. check_eq. Qed.

(** A MISSING LAST NAME under a folder that resolved.  [do_unlinkat]
    (fs/namei.c:4724-4730, Linux v6.18.46) and [do_rmdir] (4595-4600)
    call [mnt_want_write] and then [lookup_one_qstr_excl], whose dentry
    allocation (1701-1703) comes before the negative dentry's -ENOENT
    (1713-1716).  So a read-only mount's -EROFS and the lookup's -ENOMEM
    stand beside the -ENOENT on both calls
    ([Fs.Namei.unlink_before_slashes_errnos]), and the -ENOENT still
    does. *)
Example unlinkat_missing_victim_admits_erofs_and_enomem :
  let call (a2 : word) e := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; a2; 0; 0; 0] mem_name_a (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret e) [] [])) ns_empty in
  call 0 ENOENT = CheckOk ns_empty []
  /\ call 0 EROFS = CheckOk ns_empty []
  /\ call 0 ENOMEM = CheckOk ns_empty []
  /\ call (Z_to_bv 64 AT_REMOVEDIR) ENOENT = CheckOk ns_empty []
  /\ call (Z_to_bv 64 AT_REMOVEDIR) EROFS = CheckOk ns_empty []
  /\ call (Z_to_bv 64 AT_REMOVEDIR) ENOMEM = CheckOk ns_empty [].
Proof. vm_compute; split_conj; check_eq. Qed.

(** ...and nothing the lookup's -ENOENT stops: [may_delete] and
    [vfs_unlink] / [vfs_rmdir] never run, so their -EPERM, -EOVERFLOW
    and -EBUSY are refused, as is rmdir's -ENOTEMPTY.  (-EACCES is
    [may_lookup]'s, earlier in the walk, and stands.)  A missing PROPER
    PREFIX fails in [filename_parentat], before [mnt_want_write], so
    -EROFS is refused there. *)
Example unlinkat_missing_victim_refuses_what_follows_the_lookup :
  let call (a2 : word) e := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; a2; 0; 0; 0] mem_name_a (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret e) [] [])) ns_empty in
  call 0 EBUSY = CheckReject
  /\ call 0 EPERM = CheckReject
  /\ call 0 EOVERFLOW = CheckReject
  /\ call (Z_to_bv 64 AT_REMOVEDIR) EBUSY = CheckReject
  /\ call (Z_to_bv 64 AT_REMOVEDIR) EPERM = CheckReject
  /\ call (Z_to_bv 64 AT_REMOVEDIR) ENOTEMPTY = CheckReject
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a_b (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret EROFS) [] []))
       ns_empty
     = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(* ---------------------------------------------- where the ledger starts

   The copy-in boundary is a CHOICE, and wrapping the whole spec in a
   ledger rather than only the arms past [read_cstr] would satisfy every
   case above just as well.  These four pin the boundary itself: two on
   either side of it, and two on the extent.

   They matter because [read_cstr]'s extent is the string length, not a
   constant like [prlimit64]'s 16 bytes, so [Fs.Namei.unlinkat_spec] has
   to compute it.  What pins that computation is a literal here. *)

(** The flag word is decided BEFORE [getname()], so that arm reads NO
    user memory and its ledger is empty.  A ledger claimed there is a
    read the kernel did not perform.  This is the case a whole-spec
    wrapper gets wrong: it would EXPECT this range and accept. *)
Example unlinkat_bad_flags_records_no_copyin :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 1; 0; 0; 0] mem_name_a (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EINVAL) [] []))
    ns_file_a
  = CheckReject.
Proof. check_eq. Qed.

(** ...and the same call with an EMPTY ledger is admitted, so the
    rejection above is about the ledger and not about the arm. *)
Example unlinkat_bad_flags_empty_ledger_ok :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 1; 0; 0; 0] mem_name_a (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] [])
    ns_file_a
  = CheckOk ns_file_a [].
Proof. check_eq. Qed.

(** Past the flag test the ledger is REQUIRED: the removal really did
    read the path, so denying it is a rejection.  Contrast with the case
    above — the two differ in the flag word alone, and the ledger
    obligation flips with it. *)
Example unlinkat_removal_needs_the_copyin :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
    (mkEffect 0 [] [])
    ns_file_a
  = CheckReject.
Proof. check_eq. Qed.

(** And the EXTENT is the NUL-terminated prefix — 'a' and the NUL, two
    bytes.  One byte short is the name without its terminator, which is
    not what [getname()] reads; the checker rejects it. *)
Example unlinkat_copyin_extent_is_the_nul_terminated_prefix :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
    (with_copyins [(8192, 1%nat)] (mkEffect 0 [] []))
    ns_file_a
  = CheckReject.
Proof. check_eq. Qed.

(* -------------------------------------- the refusals ahead of the copy

   [getname_flags] allocates the name with [__getname] before it copies
   a byte (fs/namei.c:146-148, Linux v6.18.46), so its -ENOMEM stands
   beside every answer the call gives, the three the copy gives itself
   included: the empty name's -ENOENT (167-171), a fault's -EFAULT
   (161-165) and a full PATH_MAX's -ENAMETOOLONG (207-211).  It has
   copied nothing, so it carries no copy-in
   ([Fs.Namei.getname_refusals]).  A name whose first EMBEDDED_NAME_MAX
   bytes hold no NUL takes a second allocation, the [kzalloc] of the
   re-copy path (180-193), after the first copy and before the second;
   its -ENOMEM carries exactly that first copy.  Both come after the
   flag word, which [SYSCALL_DEFINE3(unlinkat)] tests before it calls
   [getname], and before the walk, so the walk's -EACCES is not beside
   them on a name the walk is never handed. *)

(** [unlinkat(AT_FDCWD, "", 0)], [unlinkat(AT_FDCWD, "", AT_REMOVEDIR)]
    and [mkdirat(AT_FDCWD, "", 0755)] may be -ENOMEM with nothing
    copied in, as may all three on an unmapped pointer and on the
    ordinary name "a", each with the model unchanged. *)
Example unlinkat_getname_enomem_copies_nothing :
  let call (nr a2 : word) mp m := check_syscall
        (mkInput nr [AT_FDCWD; 8192; a2; 0; 0; 0] mp (fun _ => None))
        (mkEffect (errno_ret ENOMEM) [] []) m in
  call 35 0 (name_mem []) ns_file_a = CheckOk ns_file_a []
  /\ call 35 (Z_to_bv 64 AT_REMOVEDIR) (name_mem []) ns_file_a = CheckOk ns_file_a []
  /\ call 34 493 (name_mem []) ns_empty = CheckOk ns_empty []
  /\ call 35 0 (fun _ => None) ns_file_a = CheckOk ns_file_a []
  /\ call 35 (Z_to_bv 64 AT_REMOVEDIR) (fun _ => None) ns_file_a = CheckOk ns_file_a []
  /\ call 34 493 (fun _ => None) ns_empty = CheckOk ns_empty []
  /\ call 35 0 mem_name_a ns_file_a = CheckOk ns_file_a []
  /\ call 35 (Z_to_bv 64 AT_REMOVEDIR) mem_name_a ns_empty_dir_a
     = CheckOk ns_empty_dir_a []
  /\ call 34 493 mem_name_a ns_empty = CheckOk ns_empty [].
Proof. vm_compute; split_conj; check_eq. Qed.

(** ...and not with the copy-in.  On "" and on an unmapped pointer no
    answer of the call reads the name and then fails for memory, so an
    -ENOMEM that claims the NUL or the faulting byte read is a ledger no
    kernel writes.  (On "a" the walk's own -ENOMEM does carry it.) *)
Example unlinkat_getname_enomem_with_the_copyin_rejected :
  let call (nr a2 : word) mp m := check_syscall
        (mkInput nr [AT_FDCWD; 8192; a2; 0; 0; 0] mp (fun _ => None))
        (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret ENOMEM) [] [])) m in
  call 35 0 (name_mem []) ns_file_a = CheckReject
  /\ call 35 (Z_to_bv 64 AT_REMOVEDIR) (name_mem []) ns_file_a = CheckReject
  /\ call 34 493 (name_mem []) ns_empty = CheckReject
  /\ call 35 0 (fun _ => None) ns_file_a = CheckReject
  /\ call 35 (Z_to_bv 64 AT_REMOVEDIR) (fun _ => None) ns_file_a = CheckReject
  /\ call 34 493 (fun _ => None) ns_empty = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** A name with no NUL in its first PATH_MAX bytes: 'a' from 8192 up to
    12800. *)
Definition mem_long_name : word -> option byte :=
  fun a => if ((8192 <=? bv_unsigned a) && (bv_unsigned a <? 12800))%Z
           then Some 97 else None.

(** Its first copy fills EMBEDDED_NAME_MAX = 4064 bytes
    ([Fs.Namei.embedded_name_max]), so the [kzalloc] of the re-copy path
    may fail after that copy and before the second reads to PATH_MAX:
    -ENOMEM is admitted with the first 4064 bytes read and with nothing
    read, and refused with all of PATH_MAX read, which only the second
    copy does; the second copy's -ENAMETOOLONG carries the whole. *)
Example unlinkat_long_name_enomem_carries_the_first_copy :
  let call ci e := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_long_name (fun _ => None))
        (with_copyins ci (mkEffect (errno_ret e) [] [])) ns_file_a in
  call [(8192, 4064%nat)] ENOMEM = CheckOk ns_file_a []
  /\ call [] ENOMEM = CheckOk ns_file_a []
  /\ call [(8192, 4096%nat)] ENOMEM = CheckReject
  /\ call [(8192, 4096%nat)] ENAMETOOLONG = CheckOk ns_file_a []
  /\ call [(8192, 4064%nat)] ENAMETOOLONG = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** ...and a short name never takes the re-copy, so the 4064-byte
    ledger is refused on "a". *)
Example unlinkat_short_name_enomem_has_no_first_copy_ledger :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
    (with_copyins [(8192, 4064%nat)] (mkEffect (errno_ret ENOMEM) [] []))
    ns_file_a
  = CheckReject.
Proof. check_eq. Qed.

(** ...and nothing past it: the walk's -EACCES needs a component the
    walk never reaches on "" or on a fault, so it is refused on both;
    and under a flag word [SYSCALL_DEFINE3(unlinkat)] refuses,
    [getname] is never called, so -ENOMEM is refused beside the
    -EINVAL. *)
Example unlinkat_getname_enomem_needs_getname :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] (name_mem []) (fun _ => None))
    (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret EACCES) [] []))
    ns_file_a
  = CheckReject
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret EACCES) [] []))
       ns_file_a
     = CheckReject
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] (name_mem []) (fun _ => None))
       (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret EACCES) [] []))
       ns_empty
     = CheckReject
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 1; 0; 0; 0] (name_mem []) (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] [])
       ns_file_a
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(* --------------------------------------- the arms typed by the walk

   [Fs.resolve] returns the LAST COMPONENT'S KIND, and the two calls the
   flag word selects read it differently.  A conformance run can only
   show the checker what the kernel actually did, so it exercises the
   accepting half of an arm and never the rejecting half — no probe can
   make Linux remove a file through a name with a trailing separator. *)

(** "a/" names the same component "a" as "a" does, but [do_unlinkat]
    tests the byte just past the component and jumps to [slashes:]. *)
Example unlinkat_trailing_slash_on_a_file_is_enotdir :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a_slash (fun _ => None))
    (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
    ns_file_a
  = CheckOk ns_file_a [].
Proof. check_eq. Qed.

(** The rejecting half: a kernel that removed the file through "a/". *)
Example unlinkat_trailing_slash_success_rejected :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a_slash (fun _ => None))
    (with_copyins [(8192, 3%nat)] (mkEffect 0 [] []))
    ns_file_a
  = CheckReject.
Proof. check_eq. Qed.

(** [mnt_want_write] and dentry allocation precede [slashes:], but
    [may_delete] does not run there; [may_lookup]'s -EACCES comes
    earlier still, at the top of [link_path_walk]'s component loop
    (fs/namei.c:2466-2469, Linux v6.18.46), so it stands here as on
    every pathname with a component ([Fs.Namei.walk_refusals]).  Each
    admitted refusal preserves the whole model, not just its file
    map. *)
Example unlinkat_trailing_slash_admits_earlier_refusals :
  let call e := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a_slash (fun _ => None))
        (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret e) [] [])) ns_file_a in
  call ENOTDIR = CheckOk ns_file_a []
  /\ call EROFS = CheckOk ns_file_a []
  /\ call ENOMEM = CheckOk ns_file_a []
  /\ call EACCES = CheckOk ns_file_a []
  /\ call EOVERFLOW = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** THE LAST-COMPONENT TABLE, cell by cell.  [do_unlinkat] has ONE test
    and gives all three the same -EISDIR; [do_rmdir] switches on the
    type and gives three different answers. *)
Example unlinkat_last_component_table :
  (* "/" — no component at all *)
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_root (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EISDIR) [] []))
    ns_file_a
  = CheckOk ns_file_a []
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_root
          (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EBUSY) [] []))
       ns_file_a
     = CheckOk ns_file_a []
  (* "." *)
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_dot (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EISDIR) [] []))
       ns_file_a
     = CheckOk ns_file_a []
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_dot
          (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EINVAL) [] []))
       ns_file_a
     = CheckOk ns_file_a []
  (* ".." *)
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_dotdot (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret EISDIR) [] []))
       ns_file_a
     = CheckOk ns_file_a []
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_dotdot
          (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret ENOTEMPTY) [] []))
       ns_file_a
     = CheckOk ns_file_a [].
Proof. repeat split; check_eq. Qed.

(** The rejecting half of the root cell, and the one that matters most:
    -ENOENT is the answer a spec that looked the path up in a map would
    give, and the model must not admit it. *)
Example unlinkat_root_enoent_rejected :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_root
       (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_file_a
  = CheckReject.
Proof. check_eq. Qed.

(** "/" has no component, so [link_path_walk] leaves the type at its
    initial LAST_ROOT and [do_rmdir]'s [case LAST_ROOT] answers -EBUSY.
    The victim is not looked at, so an image holding nothing but the
    standard root gives the same answer as [ns_file_a] in the table
    above. *)
Example unlinkat_root_removedir_is_ebusy :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_root
       (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EBUSY) [] []))
    ns_empty
  = CheckOk ns_empty [].
Proof. check_eq. Qed.

(** A PATHNAME WITH NO COMPONENT IS NEVER REFUSED -EACCES.  The walk's
    -EACCES is [may_lookup]'s, which [link_path_walk] calls at the top of
    its component loop ([link_path_walk], fs/namei.c:2466-2469, Linux
    v6.18.46), and "/" returns before that loop (2455-2458).  What
    follows is the type test, each before [mnt_want_write]: -EISDIR in
    [do_unlinkat] (4720-4722), -EBUSY in [do_rmdir] (4589-4590) and
    -EEXIST in [filename_create] (4219-4220), so -EROFS is refused too.
    The walk's -ENOMEM, which carries the copy-in, stands beside each
    answer ([Fs.Namei.walk_errnos]).  The empty pathname never reaches
    the walk: [getname_flags] answers it -ENOENT (167-171), so -EACCES
    is refused there as well. *)
Example unlinkat_pathname_without_a_component_refuses_eacces :
  let root (nr a2 : word) (e : Z) := check_syscall
        (mkInput nr [AT_FDCWD; 8192; a2; 0; 0; 0] mem_name_root (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret e) [] [])) ns_empty in
  let empty (nr a2 : word) (e : Z) := check_syscall
        (mkInput nr [AT_FDCWD; 8192; a2; 0; 0; 0] (name_mem []) (fun _ => None))
        (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret e) [] [])) ns_empty in
  root 35 0 ENOMEM = CheckOk ns_empty []
  /\ root 35 0 EACCES = CheckReject
  /\ root 35 0 EROFS = CheckReject
  /\ root 35 (Z_to_bv 64 AT_REMOVEDIR) ENOMEM = CheckOk ns_empty []
  /\ root 35 (Z_to_bv 64 AT_REMOVEDIR) EACCES = CheckReject
  /\ root 34 493 ENOMEM = CheckOk ns_empty []
  /\ root 34 493 EACCES = CheckReject
  /\ empty 35 0 ENOENT = CheckOk ns_empty []
  /\ empty 35 0 EACCES = CheckReject
  /\ empty 34 493 ENOENT = CheckOk ns_empty []
  /\ empty 34 493 EACCES = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(* ------------------------------------ what comes before a type answer

   [may_delete] answers on the victim's TYPE only after its own
   refusals, and its callers only reach it after theirs.  The model
   tracks the conditions behind none of them, so they stand beside the
   type answer ([Fs.Namei.unlink_before_type_errnos]).  This case and
   [unlinkat_tmp_directory_admits_earlier_refusals] below pin that for
   the two type answers: the old answer is still admitted, the earlier
   refusals are admitted beside it, and what Linux reaches only later is
   refused. *)

(** AT_REMOVEDIR ON A MODEL FILE.  [do_rmdir] reaches [may_delete]'s
    -ENOTDIR only after [mnt_want_write]'s -EROFS, the lookup's -ENOMEM
    and [may_delete]'s own -EOVERFLOW, -EACCES and -EPERM, and the model
    tracks none of the conditions behind those: a file "a" in a working
    directory the caller may not write is -EACCES on Linux.  So the
    -ENOTDIR is still admitted, and an -EACCES and an -EOVERFLOW are
    admitted beside it, each leaving the file where it was.  A success
    is still refused, and so is the -EBUSY of a mount point, which
    [vfs_rmdir] raises only after [may_delete] has passed.  (fs/namei.c,
    Linux v6.18.46.) *)
Example unlinkat_removedir_file_admits_earlier_refusals :
  let call eff := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_a
           (fun _ => None))
        (with_copyins [(8192, 2%nat)] eff) ns_file_a in
  call (mkEffect (errno_ret ENOTDIR) [] []) = CheckOk ns_file_a []
  /\ call (mkEffect (errno_ret EACCES) [] []) = CheckOk ns_file_a []
  /\ call (mkEffect (errno_ret EOVERFLOW) [] []) = CheckOk ns_file_a []
  /\ call (mkEffect 0 [] []) = CheckReject
  /\ call (mkEffect (errno_ret EBUSY) [] []) = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** BOTH TYPE ANSWERS, AND THE REFUSALS LINUX REACHES BEFORE EACH.  A
    plain "a" naming a folder reaches [may_delete]'s -EISDIR
    ([may_delete], fs/namei.c:3289-3290, Linux v6.18.46) through
    [vfs_unlink], and AT_REMOVEDIR on a file "a" reaches its -ENOTDIR
    (3284-3286) through [vfs_rmdir].  Before either, Linux may answer
    -EROFS from [mnt_want_write] ([do_unlinkat] 4724-4726, [do_rmdir]
    4595-4597), -ENOMEM from the lookup's [d_alloc] (1701-1703), and
    [may_delete]'s own -EOVERFLOW (3267-3270), -EACCES (3274-3276) and
    -EPERM (3277-3283), none of whose conditions the model tracks.  Each
    stands beside the type answer and leaves the model as it was.
    -EINVAL is refused on both: with the flag word 0 or AT_REMOVEDIR it
    is only [do_rmdir]'s answer for a last component "." (4587-4589),
    and "a" is not one. *)
Example unlinkat_type_answers_admit_the_refusals_before_them :
  let dir_unl e := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret e) [] [])) ns_empty_dir_a in
  let file_rmd e := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_a
           (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret e) [] [])) ns_file_a in
  dir_unl EISDIR = CheckOk ns_empty_dir_a []
  /\ dir_unl EROFS = CheckOk ns_empty_dir_a []
  /\ dir_unl ENOMEM = CheckOk ns_empty_dir_a []
  /\ dir_unl EOVERFLOW = CheckOk ns_empty_dir_a []
  /\ dir_unl EACCES = CheckOk ns_empty_dir_a []
  /\ dir_unl EPERM = CheckOk ns_empty_dir_a []
  /\ dir_unl EINVAL = CheckReject
  /\ file_rmd ENOTDIR = CheckOk ns_file_a []
  /\ file_rmd EROFS = CheckOk ns_file_a []
  /\ file_rmd ENOMEM = CheckOk ns_file_a []
  /\ file_rmd EPERM = CheckOk ns_file_a []
  /\ file_rmd EINVAL = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(* ------------------------------------------ an absolute name under /tmp

   A program may write a temporary file and then unlink it by an
   ABSOLUTE name under /tmp.  /tmp is a folder of the image like any
   other, so the walk answers that shape: the removal of a key the image
   holds, and the -ENOENT of one it does not.  The cases below pin both
   from the sides a real run cannot reach. *)

(** The pathname bytes of "/tmp/out.gif" at 8192, NUL-terminated.  A
    [bytes_at] literal rather than [mem_name_a_slash]'s if-chain, which
    stops being readable well before thirteen bytes. *)
Definition abs_gif_name : list byte :=
  [47; 116; 109; 112; 47; 111; 117; 116; 46; 103; 105; 102].

Definition mem_abs_gif : word -> option byte :=
  bytes_at 8192 (abs_gif_name ++ [0]).

(** The name alone, without its directory: "out.gif". *)
Definition mem_gif_basename : word -> option byte :=
  bytes_at 8192 ([111; 117; 116; 46; 103; 105; 102] ++ [0]).

(** The standard root with the file "/tmp/out.gif" in it. *)
Definition tmp_gif_fs : Fs.Fs :=
  Fs.fs_create_file (demo_fs []) abs_gif_name [104].

Definition ns_tmp_gif : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input tmp_gif_fs IEof).

(** The same call on a name the image does not hold.  The walk reaches
    /tmp and finds no "out.gif" there, so the answer is the real -ENOENT
    Linux gives for a negative dentry.  Nothing moves — the model handed
    back is the one handed in — and the success a kernel holding the
    file would return is refused, which is what keeps the answer from
    being a licence to remove. *)
Example unlinkat_tmp_key_not_held_is_enoent :
  let call eff := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_abs_gif (fun _ => None))
        (with_copyins [(8192, 13%nat)] eff) ns_empty in
  call (mkEffect (errno_ret ENOENT) [] []) = CheckOk ns_empty []
  /\ call (mkEffect 0 [] []) = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** THE SECOND UNLINK: a key the image held and the run then removed
    ITSELF.  The first call takes the key out and returns 0; the second
    reads the image that call left and answers -ENOENT, and a second
    success is refused.

    THIS CASE IS DOCUMENTARY.  Its first two conjuncts are
    [unlinkat_tmp_declared_key_removed] below on the same fixture, and
    the model that removal leaves holds the same image as the one
    [unlinkat_tmp_key_not_held_is_enoent] above is stated over.  What it
    records is the COMPOSITION a program that cleans up after itself
    makes, written down in one place because its two halves are proved
    separately. *)
Example unlinkat_tmp_removed_key_second_unlink_is_enoent :
  let call eff m := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_abs_gif (fun _ => None))
        (with_copyins [(8192, 13%nat)] eff) m in
  match call (mkEffect 0 [] [])
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input_tmp (demo_fs [])
                [([111; 117; 116; 46; 103; 105; 102], SFile [104])] IEof)) with
  | CheckOk m1 [] =>
      m_fs m1 = demo_fs []
      /\ call (mkEffect (errno_ret ENOENT) [] []) m1 = CheckOk m1 []
      /\ call (mkEffect 0 [] []) m1 = CheckReject
  | _ => False
  end.
Proof. vm_compute; split_conj; check_eq. Qed.

(** THE REMOVAL ITSELF, over an image whose /tmp holds the one file
    "out.gif" ([demo_input_tmp] lays it in at "/tmp/out.gif").  The key
    is gone afterwards, and nothing else moved. *)
Example unlinkat_tmp_declared_key_removed :
  match check_syscall
          (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_abs_gif (fun _ => None))
          (with_copyins [(8192, 13%nat)] (mkEffect 0 [] []))
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input_tmp (demo_fs [])
                [([111; 117; 116; 46; 103; 105; 102], SFile [104])] IEof)) with
  | CheckOk m [] => m_fs m = demo_fs []
  | _ => False
  end.
Proof. check_eq. Qed.

(** The SAME image written with the absolute key rather than through
    [demo_input_tmp]: the two are one image, so the arm cannot tell
    them apart, and this case is what says so. *)
Example unlinkat_tmp_image_key_removed :
  match check_syscall
          (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_abs_gif (fun _ => None))
          (with_copyins [(8192, 13%nat)] (mkEffect 0 [] []))
          ns_tmp_gif with
  | CheckOk m [] => m_fs m = demo_fs []
  | _ => False
  end.
Proof. check_eq. Qed.

(** A FOLDER INSIDE /tmp, "/tmp/d" holding "f".  Linux refuses to unlink
    a directory in [may_delete], which [vfs_unlink] calls before it
    removes anything, so the type answer is -EISDIR and the model does
    not move.

    THE TRAILING-SEPARATOR SPELLING IS THE SAME ANSWER BY A DIFFERENT
    ROUTE: Linux jumps to [do_unlinkat]'s [slashes:] label, whose own
    [d_is_dir] test answers -EISDIR for a directory.

    WHAT COMES BEFORE THAT -EISDIR, spelling by spelling.  On the plain
    spelling [vfs_unlink] reaches [may_delete]'s -EISDIR only after
    [do_unlinkat]'s -EROFS, the lookup's -ENOMEM and [may_delete]'s own
    -EOVERFLOW, -EACCES and -EPERM: the -EISDIR is still admitted, an
    -EACCES and an -EOVERFLOW are admitted beside it, each leaving the
    model as it was, and the -EBUSY of a mount point, which
    [vfs_unlink] raises only after [may_delete] has passed, is refused.
    The trailing-separator spelling reaches its -EISDIR at
    [do_unlinkat]'s [slashes:] label, after -EROFS and -ENOMEM but
    without [may_delete]; its -EACCES is the walk's own, [may_lookup]'s
    on the search of each folder (fs/namei.c:2466-2469).
    (fs/namei.c, Linux v6.18.46, 4716-4772.) *)
Definition tmp_dir_d_fs : Fs.Fs :=
  Fs.fs_create_file (Fs.fs_set (demo_fs []) [47; 116; 109; 112; 47; 100] EDir)
    [47; 116; 109; 112; 47; 100; 47; 102] [104].

Example unlinkat_tmp_directory_admits_earlier_refusals :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input tmp_dir_d_fs IEof) in
  let call mem n eff := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem (fun _ => None))
        (with_copyins [(8192, n)] eff) m0 in
  let dir := bytes_at 8192 ([47; 116; 109; 112; 47; 100] ++ [0]) in
  let dir_slash := bytes_at 8192 ([47; 116; 109; 112; 47; 100; 47] ++ [0]) in
  call dir 7%nat (mkEffect (errno_ret EISDIR) [] []) = CheckOk m0 []
  /\ call dir 7%nat (mkEffect 0 [] []) = CheckReject
  /\ call dir 7%nat (mkEffect (errno_ret EACCES) [] []) = CheckOk m0 []
  /\ call dir 7%nat (mkEffect (errno_ret EOVERFLOW) [] []) = CheckOk m0 []
  /\ call dir 7%nat (mkEffect (errno_ret EBUSY) [] []) = CheckReject
  /\ call dir_slash 8%nat (mkEffect (errno_ret EISDIR) [] []) = CheckOk m0 []
  /\ call dir_slash 8%nat (mkEffect 0 [] []) = CheckReject
  /\ call dir_slash 8%nat (mkEffect (errno_ret EROFS) [] []) = CheckOk m0 []
  /\ call dir_slash 8%nat (mkEffect (errno_ret ENOMEM) [] []) = CheckOk m0 []
  /\ call dir_slash 8%nat (mkEffect (errno_ret EACCES) [] []) = CheckOk m0 [].
Proof. vm_compute; split_conj; check_eq. Qed.

(** THE [Uapi.NAME_MAX] BOUNDARY on this arm, from both sides: a
    component of 255 bytes is REMOVED and admits no -ENAMETOOLONG; one
    of 256 is removed too, as by a file system with a larger limit,
    which no supported kernel does (a priority-2 gap:
    [Fs.comp_too_long]), and -ENAMETOOLONG stands beside it.  The limit
    is the file system's own [->lookup] ([simple_lookup],
    fs/libfs.c:71-72, which tmpfs and ramfs use, mm/shmem.c:5285 and
    fs/ramfs/inode.c:193), reached from [lookup_one_qstr_excl]
    (fs/namei.c:1685-1722) once [do_unlinkat] has the parent. *)
Example unlinkat_tmp_name_max_boundary :
  let name n := List.repeat (Z_to_bv 8 97) n in
  let call n eff := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0]
           (bytes_at 8192 ([Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109;
                            Z_to_bv 8 112; Z_to_bv 8 47] ++ name n
                           ++ [Z_to_bv 8 0])) (fun _ => None))
        (with_copyins [(8192, (6 + n)%nat)] eff)
        (init_model [] 0 0 demo_sp demo_limit
           (demo_input_tmp (demo_fs []) [(name n, SFile [Z_to_bv 8 104])] IEof)) in
  (* 255: the key is removed, and the name's length is no refusal *)
  match call 255%nat (mkEffect 0 [] []) with
  | CheckOk m [] => m_fs m = demo_fs [] | _ => False end
  /\ call 255%nat (mkEffect (errno_ret ENAMETOOLONG) [] []) = CheckReject
  (* 256: removed just the same, and -ENAMETOOLONG admitted beside it *)
  /\ match call 256%nat (mkEffect 0 [] []) with
     | CheckOk m [] => m_fs m = demo_fs [] | _ => False end
  /\ match call 256%nat (mkEffect (errno_ret ENAMETOOLONG) [] []) with
     | CheckOk _ [] => True | _ => False end.
Proof. vm_compute; split_conj; check_eq. Qed.

(** The rejecting half, reached through the bare name.  "out.gif" is
    resolved from the working directory, which holds no such name, so
    it is answered -ENOENT: "/tmp/out.gif" is not reached through it.  A
    kernel that removed something through it is not admitted. *)
Example unlinkat_absolute_basename_success_rejected :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_gif_basename (fun _ => None))
    (with_copyins [(8192, 8%nat)] (mkEffect 0 [] []))
    ns_tmp_gif
  = CheckReject.
Proof. check_eq. Qed.

(** ...and the answer it does admit, so the rejection above is about the
    removal and not about the ledger. *)
Example unlinkat_absolute_basename_is_enoent :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_gif_basename (fun _ => None))
    (with_copyins [(8192, 8%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_tmp_gif
  = CheckOk ns_tmp_gif [].
Proof. check_eq. Qed.

(** The open-file route must make the same distinction at [slashes:],
    without changing the descriptor or the named file.  The walk's own
    -EACCES ([may_lookup], called at fs/namei.c:2466-2469 in
    [link_path_walk]) comes before it too. *)
Example unlinkat_open_tmp_trailing_slash_admits_earlier_refusals :
  let p : path := [47; 116; 109; 112; 47; 120] in
  let m0 := with_fds [(3, FdFileRW 1 0)]
              (init_model [] 0 0 demo_sp demo_limit
                 (demo_input_tmp (demo_fs []) [([120], SFile [104])] IEof)) in
  let call e := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0]
           (bytes_at 8192 (p ++ [47; 0])) (fun _ => None))
        (with_copyins [(8192, 8%nat)] (mkEffect (errno_ret e) [] [])) m0 in
  call ENOTDIR = CheckOk m0 []
  /\ call EROFS = CheckOk m0 []
  /\ call ENOMEM = CheckOk m0 []
  /\ call EACCES = CheckOk m0 []
  /\ call EOVERFLOW = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** [may_delete]'s unmapped-id refusal also precedes actual removal,
    including the route that would detach an open descriptor. *)
Example unlinkat_removal_admits_eoverflow :
  let p : path := [47; 116; 109; 112; 47; 120] in
  let mt := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp (demo_fs []) [([120], SFile [104])] IEof) in
  let mo := with_fds [(3, FdFileRW 1 0)] mt in
  let call mem n m := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem (fun _ => None))
        (with_copyins [(8192, n)] (mkEffect (errno_ret EOVERFLOW) [] [])) m in
  call mem_name_a 2%nat ns_file_a = CheckOk ns_file_a []
  /\ call (bytes_at 8192 (p ++ [0])) 7%nat mt = CheckOk mt []
  /\ call (bytes_at 8192 (p ++ [0])) 7%nat mo = CheckOk mo [].
Proof. vm_compute; split_conj; check_eq. Qed.

(** THE REMOVAL'S OWN UNTRACKED REFUSALS, each beside the removal it
    stops.  A file "a" removed by [do_unlinkat] and an empty folder "a"
    removed by [do_rmdir] meet environment conditions the model does not
    track: -EROFS from [mnt_want_write], which [do_unlinkat]
    (fs/namei.c:4724-4726, Linux v6.18.46) and [do_rmdir] (4595-4597)
    call before the lookup, -ENOMEM from the lookup's [d_alloc]
    (1701-1703), [may_delete]'s -EOVERFLOW (3267-3270), -EACCES
    (3274-3276) and -EPERM (3277-3283).  Each leaves the model as it
    was.  -EBUSY is refused on both: its sources are a mount point at the
    victim ([vfs_unlink] 4669-4670, [vfs_rmdir] 4543-4546), and under
    SCOPE.md's launch premises a file is never one (the tree holds no
    bind mount) and a folder below the top level is never one (every
    mount point is a child of "/"), so it is no answer of a launch the
    statements cover ([Fs.Namei.unlinkat_errnos]).  -EINVAL is
    [unlinkat]'s answer to a flag word it does not know (4777-4778),
    decided before [getname]; with the flag word 0 or AT_REMOVEDIR,
    [do_unlinkat] (4705-4773), [do_rmdir] (4570-4622), [may_delete]
    (3255-3296), [vfs_unlink] (4654-4696) and [vfs_rmdir] (4529-4568) do
    not give it for a name "a", so it is refused on both removals. *)
Example unlinkat_removal_admits_the_untracked_refusals :
  let unl e := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret e) [] [])) ns_file_a in
  let rmd e := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_a
           (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret e) [] [])) ns_empty_dir_a in
  unl ENOMEM = CheckOk ns_file_a []
  /\ unl EACCES = CheckOk ns_file_a []
  /\ unl EPERM = CheckOk ns_file_a []
  /\ unl EROFS = CheckOk ns_file_a []
  /\ unl EBUSY = CheckReject
  /\ unl EOVERFLOW = CheckOk ns_file_a []
  /\ unl EINVAL = CheckReject
  /\ rmd EROFS = CheckOk ns_empty_dir_a []
  /\ rmd EPERM = CheckOk ns_empty_dir_a []
  /\ rmd EBUSY = CheckReject
  /\ rmd EINVAL = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(* ------------------------------------- a relative name in the working folder

   A program may make a scratch file in the folder it runs in and then
   unlink it by a RELATIVE name: the bare name, or the name behind
   "./".  Under AT_FDCWD a relative pathname is walked from the working
   directory ([path_init], fs/namei.c:2589-2604, Linux v6.18.46, starts
   from the task's pwd), so both spellings reach the key the folder
   holds. *)

(** "tmp000000.flac" and "_1_1.config", two regular files of the
    working folder: inodes 1 and 2, one byte each. *)
Definition cwd_flac_name : list byte :=
  [116; 109; 112; 48; 48; 48; 48; 48; 48; 46; 102; 108; 97; 99].

Definition cwd_config_name : list byte :=
  [95; 49; 95; 49; 46; 99; 111; 110; 102; 105; 103].

Definition ns_cwd_files : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [(cwd_flac_name, SFile [104]); (cwd_config_name, SFile [105])])
       IEof).

(** THE BARE NAME AND THE "./" NAME ARE BOTH REMOVED.  [do_unlinkat]
    (fs/namei.c:4705-4773, Linux v6.18.46) walks to the parent with
    [filename_parentat] (4716), whose [link_path_walk] (2441-2537)
    stops in front of the last component and types it LAST_NORM
    (2484-2486).  A leading "." is LAST_DOT (2480-2482), and
    [walk_component] hands it to [handle_dots] (2142-2145), which does
    not move for LAST_DOT (2096-2131), so "./_1_1.config" has the
    working directory for its parent, as "_1_1.config" does.  The type
    test passes (4720-4722), [lookup_one_qstr_excl] finds the positive
    dentry (1685-1722), the byte past the name is the NUL (4734-4735),
    and [vfs_unlink] (4741, 4654-4696) removes it: 0, the name is gone
    and the other file stays.  -ENOENT is [lookup_one_qstr_excl]'s
    answer for a NEGATIVE dentry (1713-1716), so on either spelling of a
    name the folder holds it is refused.  The copy-in is the name and
    its NUL: fifteen bytes, and fourteen for "./_1_1.config". *)
Example unlinkat_working_folder_relative_names_removed :
  let call mem n eff := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem (fun _ => None))
        (with_copyins [(8192, n)] eff) ns_cwd_files in
  let flac := bytes_at 8192 (cwd_flac_name ++ [0]) in
  let dot_config := bytes_at 8192 ([46; 47] ++ cwd_config_name ++ [0]) in
  match call flac 15%nat (mkEffect 0 [] []) with
  | CheckOk m [] =>
      Fs.fs_lookup (m_fs m) (wk cwd_flac_name) = None
      /\ file_at (m_fs m) (wk cwd_config_name) = Some [105]
  | _ => False
  end
  /\ match call dot_config 14%nat (mkEffect 0 [] []) with
     | CheckOk m [] =>
         Fs.fs_lookup (m_fs m) (wk cwd_config_name) = None
         /\ file_at (m_fs m) (wk cwd_flac_name) = Some [104]
     | _ => False
     end
  /\ call flac 15%nat (mkEffect (errno_ret ENOENT) [] []) = CheckReject
  /\ call dot_config 14%nat (mkEffect (errno_ret ENOENT) [] []) = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(* ------------------------------------------------------------- rmdir *)

(** AN EMPTY DIRECTORY IS REMOVED: a folder is an entry of the image,
    so rmdir of one is answered, where a model file could only ever
    give -ENOTDIR; its parent's link count follows ([Fs.fs_rmdir]). *)
Example rmdir_empty_directory_is_removed :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_a
       (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
    ns_empty_dir_a
  = CheckOk (with_fs (Fs.fs_rmdir (m_fs ns_empty_dir_a) (wk [97]))
               ns_empty_dir_a) [].
Proof. check_eq. Qed.

(** A NON-EMPTY one is -ENOTEMPTY, and the emptiness test is "no key's
    parent is this one" rather than anything about the spelling. *)
Example rmdir_non_empty_directory_is_enotempty :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_a
       (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOTEMPTY) [] []))
    ns_dir_a_with_b
  = CheckOk ns_dir_a_with_b []
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_a
          (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
       ns_dir_a_with_b
     = CheckReject.
Proof. split; check_eq. Qed.

(** A REGULAR FILE under AT_REMOVEDIR is -ENOTDIR, from
    [may_delete(..., isdir = 1)]'s own test. *)
Example rmdir_of_a_file_is_enotdir :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_a
       (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
    ns_file_a
  = CheckOk ns_file_a [].
Proof. check_eq. Qed.

(** TRAILING SEPARATORS ARE IGNORED by rmdir, where it differs from
    unlinkat: "a/" and "a" are one call. *)
Example rmdir_ignores_a_trailing_separator :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_a_slash
       (fun _ => None))
    (with_copyins [(8192, 3%nat)] (mkEffect 0 [] []))
    ns_empty_dir_a
  = CheckOk (with_fs (Fs.fs_rmdir (m_fs ns_empty_dir_a) (wk [97]))
               ns_empty_dir_a) [].
Proof. check_eq. Qed.

(** A TOP-LEVEL FOLDER DECLINES.  SCOPE.md's launch premise lets every
    child of "/" be a mount point, as /tmp is in the agreement checks'
    launch (testing/vm/tracer.c:936), and on a mount point [vfs_rmdir]
    answers -EBUSY before it asks [->rmdir] ([is_local_mountpoint],
    fs/namei.c:4543-4546, then 4552, Linux v6.18.46), while the same
    folder unmounted is removed.  The image does not say which, so
    rmdir of the empty /tmp is [CheckUnmodeled] beside 0, -EBUSY and
    -ENOTEMPTY alike, "/tmp/" too.  One level lower no folder is a mount
    point: the empty /tmp/d is removed and its -EBUSY refused, and "/"
    keeps [do_rmdir]'s LAST_ROOT -EBUSY (4590-4592). *)
Definition tmp_sub_key : Fs.path := Fs.child_key Fs.tmp_dir [Z_to_bv 8 100].
Definition ns_tmp_sub : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (Fs.fs_set (demo_fs []) tmp_sub_key EDir) IEof).

Example rmdir_of_a_top_level_folder_declines :
  let rmd (p : list Z) (n : nat) (e : word) (m : Model) := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] (name_mem p)
           (fun _ => None))
        (with_copyins [(8192, n)] (mkEffect e [] [])) m in
  rmd [47; 116; 109; 112]%Z 5%nat 0 ns_empty = CheckUnmodeled
  /\ rmd [47; 116; 109; 112]%Z 5%nat (errno_ret EBUSY) ns_empty = CheckUnmodeled
  /\ rmd [47; 116; 109; 112]%Z 5%nat (errno_ret ENOTEMPTY) ns_empty = CheckUnmodeled
  /\ rmd [47; 116; 109; 112; 47]%Z 6%nat 0 ns_empty = CheckUnmodeled
  (* one level lower: removed, and no -EBUSY *)
  /\ rmd [47; 116; 109; 112; 47; 100]%Z 7%nat 0 ns_tmp_sub
     = CheckOk (with_fs (Fs.fs_rmdir (m_fs ns_tmp_sub) tmp_sub_key) ns_tmp_sub) []
  /\ rmd [47; 116; 109; 112; 47; 100]%Z 7%nat (errno_ret EBUSY) ns_tmp_sub = CheckReject
  /\ rmd [97]%Z 2%nat 0 ns_empty_dir_a
     = CheckOk (with_fs (Fs.fs_rmdir (m_fs ns_empty_dir_a) (wk [97])) ns_empty_dir_a) []
  (* "/" is the LAST_ROOT answer, unchanged *)
  /\ rmd [47]%Z 2%nat (errno_ret EBUSY) ns_empty = CheckOk ns_empty [].
Proof. vm_compute; split_conj; check_eq. Qed.

(** THE DECLINES, on the image that reaches each.  Linux SUCCEEDS at
    these and leaves an S_DEAD directory behind, which this model has no
    term for; no errno is invented.

    The working directory itself: the fixture's cwd is [Fs.default_cwd]
    and the path resolves to it, so the arm declines. *)
Definition mem_name_work : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 47        (* '/' *)
           else if bv_eqb a 8193 then Some 119  (* 'w' *)
           else if bv_eqb a 8194 then Some 111  (* 'o' *)
           else if bv_eqb a 8195 then Some 114  (* 'r' *)
           else if bv_eqb a 8196 then Some 107  (* 'k' *)
           else if bv_eqb a 8197 then Some 0
           else None.

Example rmdir_of_the_working_directory_is_declined :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_work
       (fun _ => None))
    (with_copyins [(8192, 6%nat)] (mkEffect 0 [] []))
    ns_empty
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** A directory an open [State.FdDir] names.  The descriptor is the only
    difference from [rmdir_empty_directory_is_removed] above, so this
    pins the guard rather than the arm. *)
Definition ns_empty_dir_a_open : Model :=
  with_fds [(3, FdDir (wk [97]))] ns_empty_dir_a.

Example rmdir_of_an_open_directory_is_declined :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_a
       (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
    ns_empty_dir_a_open
  = CheckUnmodeled.
Proof. check_eq. Qed.

(* ----------------------------------------------------------- mkdirat *)

(** THE CREATE, at the key the walk names: a folder is a value of the
    image, [EDir], and its parent's link count follows ([Fs.fs_mkdir]). *)
Example mkdirat_creates_at_the_resolved_key :
  check_syscall
    (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
    ns_empty
  = CheckOk (with_fs (Fs.fs_mkdir (m_fs ns_empty) (wk [97])) ns_empty) [].
Proof. check_eq. Qed.

(** THE MODE IS IGNORED, which the pin shows by giving the same answer
    for a second mode word. *)
Example mkdirat_ignores_the_mode :
  check_syscall
    (mkInput 34 [AT_FDCWD; 8192; 511; 0; 0; 0] mem_name_a (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
    ns_empty
  = CheckOk (with_fs (Fs.fs_mkdir (m_fs ns_empty) (wk [97])) ns_empty) [].
Proof. check_eq. Qed.

(** AN EXISTING NAME IS -EEXIST whatever kind it is. *)
Example mkdirat_existing_name_is_eexist :
  check_syscall
    (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EEXIST) [] []))
    ns_file_a
  = CheckOk ns_file_a []
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EEXIST) [] []))
       ns_empty_dir_a
     = CheckOk ns_empty_dir_a [].
Proof. split; check_eq. Qed.

(** THE NON-NORMAL LAST COMPONENTS ARE -EEXIST, all three, and this is
    the cell where mkdirat differs from rmdir: [filename_create]
    initialises its dentry to ERR_PTR(-EEXIST) and returns it for any
    type but LAST_NORM, where [do_rmdir] gives -EINVAL, -ENOTEMPTY and
    -EBUSY.  A spec that reused rmdir's table would answer three
    different errnos here. *)
Example mkdirat_non_normal_last_component_is_eexist :
  check_syscall
    (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_dot (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EEXIST) [] []))
    ns_empty
  = CheckOk ns_empty []
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_dotdot
          (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret EEXIST) [] []))
       ns_empty
     = CheckOk ns_empty []
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_root
          (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EEXIST) [] []))
       ns_empty
     = CheckOk ns_empty []
  (* and rmdir's -EINVAL for "." is refused here *)
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_dot (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EINVAL) [] []))
       ns_empty
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** TRAILING SEPARATORS ARE IGNORED by mkdirat too, and for a reason of
    its own: [do_mkdirat] passes LOOKUP_DIRECTORY, so the line that
    would strip the create flags does not fire. *)
Example mkdirat_ignores_a_trailing_separator :
  check_syscall
    (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a_slash
       (fun _ => None))
    (with_copyins [(8192, 3%nat)] (mkEffect 0 [] []))
    ns_empty
  = CheckOk (with_fs (Fs.fs_mkdir (m_fs ns_empty) (wk [97])) ns_empty) [].
Proof. check_eq. Qed.

(** THE PREFIX ERRORS ARE THE WALK'S, before the last component is
    typed: a missing parent is -ENOENT and a file where a directory was
    needed is -ENOTDIR. *)
Example mkdirat_prefix_errors :
  check_syscall
    (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a_b (fun _ => None))
    (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_empty
  = CheckOk ns_empty []
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a_b
          (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
       ns_file_a
     = CheckOk ns_file_a [].
Proof. split; check_eq. Qed.

(** A MKDIR IN THE /dev SUBTREE CREATES, as it does anywhere else.  The
    image describes /dev completely at launch and the kernel makes no
    device node during the run ([Fs.dev_dir] carries the argument; in
    Linux v6.18.46 a devtmpfs node is made by [devtmpfs_create_node],
    drivers/base/devtmpfs.c:129-154, when a driver-core device is
    registered), so /dev is an ordinary folder here and an absent name
    in it is a name the guest does not have.  The -ENOENT of a missing
    last component is not an answer to a create, so it is refused.  The
    same holds one level down, under a DECLARED /dev/pts.

    The twin is the same call under /tmp, which creates the same way. *)
Definition mem_dev_d : word -> option byte :=
  name_mem [47; 100; 101; 118; 47; 100]%Z.
Definition dev_d_key : Fs.path := Fs.child_key Fs.dev_dir [Z_to_bv 8 100].
Definition mem_tmp_d : word -> option byte :=
  name_mem [47; 116; 109; 112; 47; 100]%Z.
Definition tmp_d_key : Fs.path := Fs.child_key Fs.tmp_dir [Z_to_bv 8 100].

Definition devpts_key : Fs.path :=
  Fs.child_key Fs.dev_dir (map (fun z => Z_to_bv 8 z) [112; 116; 115]%Z).
Definition mem_devpts_d : word -> option byte :=
  name_mem [47; 100; 101; 118; 47; 112; 116; 115; 47; 100]%Z.
Definition ns_devpts : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (Fs.fs_set (demo_fs []) devpts_key EDir) IEof).

Example mkdirat_under_dev_creates :
  check_syscall
    (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_dev_d (fun _ => None))
    (with_copyins [(8192, 7%nat)] (mkEffect 0 [] []))
    ns_empty
  = CheckOk (with_fs (Fs.fs_mkdir (m_fs ns_empty) dev_d_key) ns_empty) []
  (* the -ENOENT of an absent name is not an answer to a create *)
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_dev_d (fun _ => None))
       (with_copyins [(8192, 7%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_empty
     = CheckReject
  (* one level down, under a DECLARED /dev/pts, it creates too *)
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_devpts_d
          (fun _ => None))
       (with_copyins [(8192, 11%nat)] (mkEffect 0 [] []))
       ns_devpts
     = CheckOk (with_fs (Fs.fs_mkdir (m_fs ns_devpts)
                           (Fs.child_key devpts_key [Z_to_bv 8 100]))
                  ns_devpts) []
  (* ... and the same call under /tmp creates the same way *)
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_tmp_d (fun _ => None))
       (with_copyins [(8192, 7%nat)] (mkEffect 0 [] []))
       ns_empty
     = CheckOk (with_fs (Fs.fs_mkdir (m_fs ns_empty) tmp_d_key) ns_empty) [].
Proof. split_conj; check_eq. Qed.

(** AN UNLINK IN THE /dev SUBTREE READS THE SAME WAY: an absent name
    there is -ENOENT, as under /tmp, and the declared device's own row
    is untouched -- a device entry is declined, for its own reason
    ([Fs.Namei.unlinkat_file_spec]'s [EDev] row).

    THE TWINS OUTSIDE THE SUBTREE take the two -ENOENT paths separately:
    an absent LAST COMPONENT under a present /tmp, and an absent PROPER
    PREFIX at /etc, which the fixture does not ship.  The /dev cell
    gives the same answer as the first. *)
Definition mem_dev_zero : word -> option byte :=
  name_mem [47; 100; 101; 118; 47; 122; 101; 114; 111]%Z.
Definition mem_dev_null : word -> option byte :=
  name_mem [47; 100; 101; 118; 47; 110; 117; 108; 108]%Z.
Definition mem_tmp_zero : word -> option byte :=
  name_mem [47; 116; 109; 112; 47; 122; 101; 114; 111]%Z.
Definition mem_etc_zero : word -> option byte :=
  name_mem [47; 101; 116; 99; 47; 122; 101; 114; 111]%Z.

Example unlinkat_under_dev_absent_is_enoent :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_dev_zero (fun _ => None))
    (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_empty
  = CheckOk ns_empty []
  (* and a removal of the absent name is refused *)
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_dev_zero (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect 0 [] []))
       ns_empty
     = CheckReject
  (* the declared device itself still declines *)
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_dev_null (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect 0 [] []))
       ns_empty
     = CheckUnmodeled
  (* the twin under /tmp: an absent last component is a real -ENOENT *)
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_tmp_zero (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_empty
     = CheckOk ns_empty []
  (* and the twin under an ABSENT /etc, the other -ENOENT path *)
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_etc_zero (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_empty
     = CheckOk ns_empty [].
Proof. split_conj; check_eq. Qed.

(** THE TWO AXES CROSS, AND THE PREFIX WINS.  Every other pin in this
    file sits on ONE axis: the last-component table uses bare ".", ".."
    and "/", whose prefixes are trivially fine, and the prefix pins use
    "a/b", whose last component is LAST_NORM.  Neither can see the
    ordering both of them name, and an arm that read the last kind FIRST
    passed all of them while answering -EISDIR where Linux answers
    -ENOTDIR.

    The kernel's order is [filename_parentat], then the kind switch
    ([do_unlinkat], fs/namei.c:4716-4722, Linux v6.18.46):

        error = filename_parentat(dfd, name, lookup_flags, &path, &last, &type);
        if (error)
                goto exit1;
        error = -EISDIR;
        if (type != LAST_NORM)
                goto exit2;

    ([do_rmdir] and [filename_create] have the same two steps in the
    same order).  So each pin below takes BOTH halves: the prefix's
    errno is accepted and the last kind's errno is REJECTED, which is
    what makes it a statement about the order rather than about either
    answer. *)
Example unlinkat_prefix_beats_the_last_kind :
  (* "a/.." with 'a' a regular file: the walk cannot descend *)
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_a_dotdot (fun _ => None))
    (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
    ns_file_a
  = CheckOk ns_file_a []
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_a_dotdot (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret EISDIR) [] []))
       ns_file_a
     = CheckReject
  (* "a/." is the same crossing through the other non-normal kind *)
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_a_dot (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
       ns_file_a
     = CheckOk ns_file_a []
  (* "m/.." with 'm' absent: the prefix is -ENOENT, not -EISDIR *)
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_m_dotdot (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_empty
     = CheckOk ns_empty []
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_m_dotdot (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret EISDIR) [] []))
       ns_empty
     = CheckReject
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_m_dot (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_empty
     = CheckOk ns_empty [].
Proof. split_conj; check_eq. Qed.

(** The same crossing under AT_REMOVEDIR, where the last-kind switch
    answers three DIFFERENT errnos and so had three ways to win. *)
Example rmdir_prefix_beats_the_last_kind :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0]
       mem_a_dotdot (fun _ => None))
    (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
    ns_file_a
  = CheckOk ns_file_a []
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0]
          mem_a_dotdot (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOTEMPTY) [] []))
       ns_file_a
     = CheckReject
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0]
          mem_a_dot (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
       ns_file_a
     = CheckOk ns_file_a []
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0]
          mem_a_dot (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret EINVAL) [] []))
       ns_file_a
     = CheckReject
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0]
          mem_m_dotdot (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_empty
     = CheckOk ns_empty []
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0]
          mem_m_dot (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_empty
     = CheckOk ns_empty [].
Proof. split_conj; check_eq. Qed.

(** And under mkdirat, where [filename_create]'s -EEXIST had to lose to
    the parent walk the same way. *)
Example mkdirat_prefix_beats_the_last_kind :
  check_syscall
    (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_a_dotdot (fun _ => None))
    (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
    ns_file_a
  = CheckOk ns_file_a []
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_a_dotdot (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret EEXIST) [] []))
       ns_file_a
     = CheckReject
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_a_dot (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
       ns_file_a
     = CheckOk ns_file_a []
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_m_dotdot (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_empty
     = CheckOk ns_empty []
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_m_dotdot (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret EEXIST) [] []))
       ns_empty
     = CheckReject
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_m_dot (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_empty
     = CheckOk ns_empty [].
Proof. split_conj; check_eq. Qed.

(** THE INJECTABLE FAILURES, offered beside the create. *)
Example mkdirat_injectable_errnos :
  check_syscall
    (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOMEM) [] []))
    ns_empty
  = CheckOk ns_empty []
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EROFS) [] []))
       ns_empty
     = CheckOk ns_empty []
  (* -EEXIST is NOT injectable: existence is resolution *)
  /\ check_syscall
       (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EEXIST) [] []))
       ns_empty
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** THE CREATE'S UNTRACKED REFUSALS, three of the five
    ([mkdirat_create_admits_eoverflow] and [mkdirat_create_admits_enospc]
    pin the other two; [mkdirat_create_refuses_eperm] pins the -EPERM
    that is not one).  Beside the -ENOMEM and
    -EROFS above: -EACCES from [may_create]'s [inode_permission] on the
    parent ([may_create], fs/namei.c:3318, Linux v6.18.46).  Each leaves
    the image as it was.
    -EINVAL is refused:
    [do_mkdirat] (4474-4503), [filename_create] (4200-4250), [may_create]
    (3307-3319) and [vfs_mkdir] (4433-4471) do not give it, and tmpfs
    gives it only for a name a strictly case-folding folder refuses
    ([shmem_mknod], mm/shmem.c:3880-3881, Linux v6.18.46), which the
    one-byte name "a" is not. *)
Example mkdirat_create_admits_the_untracked_refusals :
  let call e := check_syscall
        (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret e) [] [])) ns_empty in
  call ENOMEM = CheckOk ns_empty []
  /\ call EACCES = CheckOk ns_empty []
  /\ call EROFS = CheckOk ns_empty []
  /\ call EINVAL = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** [may_create]'s -EOVERFLOW, for a caller whose fsuid or fsgid has no
    mapping in the superblock's user namespace ([fsuidgid_has_mapping],
    fs/namei.c:3315-3316 and include/linux/fs.h:1762-1776, Linux
    v6.18.46), which [vfs_mkdir] reaches at 4440-4442 on the row that
    creates the folder: admitted there, leaving the image as it was.  An
    existing name refuses it, a file or a folder alike: [filename_create]'s
    lookup answers -EEXIST first, and [may_create] itself tests the child
    (3311-3312) before the mapping. *)
Example mkdirat_create_admits_eoverflow :
  let call m := check_syscall
        (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EOVERFLOW) [] [])) m in
  call ns_empty = CheckOk ns_empty []
  /\ call ns_file_a = CheckReject
  /\ call ns_empty_dir_a = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** The file system's -ENOSPC, for a create that finds no room for its
    inode, which [vfs_mkdir] reaches only past [may_create], calling
    [->mkdir] at fs/namei.c:4457 (Linux v6.18.46).  On tmpfs
    [__shmem_get_inode] answers it when [shmem_reserve_inode] finds the
    inode budget spent (mm/shmem.c:354-358, Linux v6.18.46) or
    [new_inode] fails (:3088-3091); on ramfs, [ramfs_mknod] answers it
    when its inode allocation fails (fs/ramfs/inode.c:101-104, Linux
    v6.18.46), and [ramfs_mkdir] returns it (:125-128).  Admitted on the
    row that creates the folder, leaving the image as it was; refused
    beside an existing name, a file or a folder alike, which
    [filename_create]'s lookup answers -EEXIST before the file system
    is asked anything. *)
Example mkdirat_create_admits_enospc :
  let call m := check_syscall
        (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOSPC) [] [])) m in
  call ns_empty = CheckOk ns_empty []
  /\ call ns_file_a = CheckReject
  /\ call ns_empty_dir_a = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** NO -EPERM BESIDE THE CREATE.  [vfs_mkdir] answers -EPERM for a
    parent whose file system has no [->mkdir] (fs/namei.c:4444-4446,
    Linux v6.18.46), such as an mqueue folder
    ([mqueue_dir_inode_operations], ipc/mqueue.c:1613-1617).  SCOPE.md's
    launch premise puts every folder the walk reaches on tmpfs or ramfs,
    and both install one ([shmem_dir_inode_operations],
    mm/shmem.c:5281-5289;
    [ramfs_dir_inode_operations], fs/ramfs/inode.c:191-197);
    [inode_permission]'s -EPERM
    (fs/namei.c:581-582) needs the immutable attribute, which SCOPE.md
    excludes too.  So -EPERM is refused on the row that creates the
    folder, and beside an existing name's -EEXIST, a file or a folder
    alike ([Sys.Fs.Namei.mkdirat_errnos]). *)
Example mkdirat_create_refuses_eperm :
  let call m := check_syscall
        (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EPERM) [] [])) m in
  call ns_empty = CheckReject
  /\ call ns_file_a = CheckReject
  /\ call ns_empty_dir_a = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** THE ROUND TRIP: rmdir then mkdirat at ONE key leaves the image
    where it started. *)
Example mkdirat_after_rmdir_restores_the_key :
  match check_syscall
          (mkInput 35 [AT_FDCWD; 8192; Z_to_bv 64 AT_REMOVEDIR; 0; 0; 0] mem_name_a
             (fun _ => None))
          (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
          ns_empty_dir_a with
  | CheckOk m1 [] =>
      match check_syscall
              (mkInput 34 [AT_FDCWD; 8192; 493; 0; 0; 0] mem_name_a
                 (fun _ => None))
              (with_copyins [(8192, 2%nat)] (mkEffect 0 [] [])) m1 with
      | CheckOk m2 [] => Fs.fs_lookup (m_fs m2) (wk [97]) = Some EDir
      | _ => False
      end
  | _ => False
  end.
Proof. check_eq. Qed.

(* ------------------------------------------- symbolic links at the parent end

   [unlinkat], [rmdir] and [mkdirat] walk to the PARENT of their last
   name ([path_parentat], fs/namei.c:2719-2733) and look the name up
   without following it ([lookup_one_qstr_excl], :1685-1722).  So
   [unlinkat] of a link removes the link and leaves what it names
   ([vfs_unlink] on the link's own dentry); "l/" is [do_unlinkat]'s
   -ENOTDIR for a dentry that is not a folder (:4767-4772); AT_REMOVEDIR
   on a link is [may_delete]'s -ENOTDIR (:3285-3286); and [mkdirat] of a
   link's name is -EEXIST ([filename_create]'s positive dentry,
   :4237-4239), whatever the link names. *)

(** "f" a file (inode 1), "l" -> "f", "dang" -> "new". *)
Definition ns_links : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([102], SFile [104; 105]); ([108], SLink [102]);
                          ([100; 97; 110; 103], SLink [110; 101; 119])]) IEof).

Definition ln_namei (nr : word) (bs : list Z) (a2 : word) (eff : SyscallEffect)
    : check_result :=
  check_syscall (mkInput nr [AT_FDCWD; 8192; a2; 0; 0; 0] (name_mem bs) (fun _ => None))
    (with_copyins [(8192, S (length bs))] eff) ns_links.

(** UNLINKAT OF A LINK REMOVES THE LINK ONLY: the name "l" goes, the
    file it names keeps its name and its bytes. *)
Example unlinkat_of_a_link_removes_the_link :
  match ln_namei 35 [108]%Z 0 (mkEffect 0 [] []) with
  | CheckOk m [] =>
      Fs.fs_lookup (m_fs m) (wk [108]) = None
      /\ file_at (m_fs m) (wk [102]) = Some [104; 105]
  | _ => False
  end
  (* a dangling link goes the same way *)
  /\ match ln_namei 35 [100; 97; 110; 103]%Z 0 (mkEffect 0 [] []) with
     | CheckOk m [] => Fs.fs_lookup (m_fs m) (wk [100; 97; 110; 103]) = None
     | _ => False
     end
  (* and the -ENOENT of a walk that followed it is refused *)
  /\ ln_namei 35 [100; 97; 110; 103]%Z 0 (mkEffect (errno_ret ENOENT) [] [])
     = CheckReject.
Proof. vm_compute. split_conj; reflexivity. Qed.

(** "l/" IS -ENOTDIR, and AT_REMOVEDIR ON A LINK IS -ENOTDIR: the last
    name is the link, never the file it names. *)
Example unlinkat_link_slash_and_removedir_are_enotdir :
  ln_namei 35 [108; 47]%Z 0 (mkEffect (errno_ret ENOTDIR) [] []) = CheckOk ns_links []
  /\ ln_namei 35 [108; 47]%Z 0 (mkEffect 0 [] []) = CheckReject
  /\ ln_namei 35 [108]%Z (Z_to_bv 64 AT_REMOVEDIR) (mkEffect (errno_ret ENOTDIR) [] [])
     = CheckOk ns_links []
  /\ ln_namei 35 [108]%Z (Z_to_bv 64 AT_REMOVEDIR) (mkEffect 0 [] []) = CheckReject.
Proof. split_conj; check_eq. Qed.

(** MKDIRAT ON A LINK'S NAME IS -EEXIST, for a link to a file and for a
    link to nothing alike: the name is taken, and nothing is made. *)
Example mkdirat_on_a_link_name_is_eexist :
  ln_namei 34 [108]%Z 493 (mkEffect (errno_ret EEXIST) [] []) = CheckOk ns_links []
  /\ ln_namei 34 [108]%Z 493 (mkEffect 0 [] []) = CheckReject
  /\ ln_namei 34 [100; 97; 110; 103]%Z 493 (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk ns_links []
  /\ ln_namei 34 [100; 97; 110; 103]%Z 493 (mkEffect 0 [] []) = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A WALK THAT FOLLOWED A LINK ADMITS -ELOOP, AND ONLY SUCH A WALK.
    "l/x" goes to its parent through "l", which is not the last
    component, so the walk follows it: [step_into]
    (fs/namei.c:1984-2022, Linux v6.18.46) hands a link to [pick_link];
    the body "f" is a file, and the walk stops on it with -ENOTDIR
    (2529-2535).  [pick_link] answers -ELOOP for every link on a
    [nosymfollow] mount (1927-1929), and the
    model does not know the mount's flags, so -ELOOP stands beside the
    -ENOTDIR, for [unlinkat] and for [mkdirat] alike, as do -ENOMEM and
    [may_lookup]'s -EACCES (2466-2469).  "f/x" stops on the same file
    with no link on the way: -ENOTDIR and -ENOMEM stand, and -ELOOP is
    refused, since [pick_link] and [reserve_stack] (1876-1900) are
    reached only through a link and the image holds no automount point
    ([follow_automount] 1456-1457). *)
Example unlinkat_walk_through_a_link_admits_eloop :
  ln_namei 35 [108; 47; 120]%Z 0 (mkEffect (errno_ret ENOTDIR) [] []) = CheckOk ns_links []
  /\ ln_namei 35 [108; 47; 120]%Z 0 (mkEffect (errno_ret ELOOP) [] []) = CheckOk ns_links []
  /\ ln_namei 35 [108; 47; 120]%Z 0 (mkEffect (errno_ret ENOMEM) [] []) = CheckOk ns_links []
  /\ ln_namei 35 [108; 47; 120]%Z 0 (mkEffect (errno_ret EACCES) [] []) = CheckOk ns_links []
  /\ ln_namei 34 [108; 47; 120]%Z 493 (mkEffect (errno_ret ELOOP) [] []) = CheckOk ns_links []
  /\ ln_namei 35 [102; 47; 120]%Z 0 (mkEffect (errno_ret ENOTDIR) [] []) = CheckOk ns_links []
  /\ ln_namei 35 [102; 47; 120]%Z 0 (mkEffect (errno_ret ENOMEM) [] []) = CheckOk ns_links []
  /\ ln_namei 35 [102; 47; 120]%Z 0 (mkEffect (errno_ret ELOOP) [] []) = CheckReject.
Proof. split_conj; check_eq. Qed.
