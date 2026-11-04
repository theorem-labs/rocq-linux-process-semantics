(** * LinuxProcessSem.Checks.Cases.Fs.Namei — worked examples over unlinkat (35)

    Mirrors [Sys/Fs/Namei.v], which answers to Linux [fs/namei.c]: this
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

(** Path bytes at 8192 for the unlinkat examples below: 'a', NUL. *)
Definition mem_name_a : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 97        (* 'a' *)
           else if bv_eqb a 8193 then Some 0    (* NUL *)
           else None.

(** A key living UNDER a name means reality has a DIRECTORY that the flat
    map only implies: unlinking that name is -EISDIR on Linux and would be
    -ENOENT here, so [Fs.Namei.fs_under] declines it.  No modeled
    syscall puts a separator in a key, so only the starting image can
    set this up.

    This image holds "a/b" and NOT "a", which is the REALIZABLE shape: a
    real directory "a" containing a file "b" contributes exactly the one
    key. *)
Example unlinkat_implied_directory_unmodeled :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EISDIR) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97; 47; 98], [104])] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** The same guard on the UNREALIZABLE image, where "a" and "a/b" are
    both keys — a tree that cannot exist, since "a" cannot be a regular
    file and a directory at once.  [Fs.valid_fs] admits it anyway, which
    is what [Fs.Namei.unlinkat_spec] means by the guard covering those
    images too, and this is the case that pins it: here the lookup of "a"
    would SUCCEED, so a guard placed after the lookup would remove the
    file and return 0 instead of declining.  On the realizable image
    above the lookup misses either way, so that one cannot tell the two
    orderings apart. *)
Example unlinkat_implied_directory_unrealizable_image_unmodeled :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EISDIR) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []); ([97; 47; 98], [104])] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** The contrast, so the guard is a COMPONENT prefix and not a byte
    prefix: "ab" does not live under "a", and the removal goes through,
    leaving the map in its canonical sorted form ([Fs.fs_remove_sorted]).
    The effect carries the pathname copy-in the spec records — two bytes,
    'a' and the NUL — without which the checker rejects it. *)
Example unlinkat_byte_prefix_is_not_a_directory :
  match check_syscall
          (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
          (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []); ([97; 98], [104])] IEof)) with
  | CheckOk m [] => m_fs m = [([97; 98], [104])]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

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
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof))
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** ...and the same call with an EMPTY ledger is admitted, so the
    rejection above is about the ledger and not about the arm. *)
Example unlinkat_bad_flags_empty_ledger_ok :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 1; 0; 0; 0] mem_name_a (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof)) [].
Proof. vm_compute. reflexivity. Qed.

(** Past the flag test the ledger is REQUIRED: the removal really did
    read the path, so denying it is a rejection.  Contrast with the case
    above — the two differ in the flag word alone, and the ledger
    obligation flips with it. *)
Example unlinkat_removal_needs_the_copyin :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
    (mkEffect 0 [] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []); ([97; 98], [104])] IEof))
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** And the EXTENT is the NUL-terminated prefix — 'a' and the NUL, two
    bytes.  One byte short is the name without its terminator, which is
    not what [getname()] reads; the checker rejects it. *)
Example unlinkat_copyin_extent_is_the_nul_terminated_prefix :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a (fun _ => None))
    (with_copyins [(8192, 1%nat)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []); ([97; 98], [104])] IEof))
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(* --------------------------------------- the two arms typed by the walk

   [Fs.Namei.unlinkat_spec] answers a TRAILING separator and an
   all-separator path without a directory structure, because the kernel
   settles both without one either.  The four cases below pin each from
   both sides.  A real run can only show the checker what the kernel
   actually did, so it exercises the accepting half of an arm and never
   the rejecting half — no program can make Linux remove a file through
   a name with a trailing separator. *)

(** Path bytes at 8192: 'a', '/', NUL. *)
Definition mem_name_a_slash : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 97        (* 'a' *)
           else if bv_eqb a 8193 then Some 47   (* '/' *)
           else if bv_eqb a 8194 then Some 0    (* NUL *)
           else None.

(** Path bytes at 8192: '/', NUL — a path with no component at all. *)
Definition mem_name_root : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 47        (* '/' *)
           else if bv_eqb a 8193 then Some 0    (* NUL *)
           else None.

(** "a/" names the same component "a" as "a" does, but [do_unlinkat]
    tests the byte just past it and jumps to its [slashes:] label, which
    for a regular file is -ENOTDIR.  The file survives: the answer is
    reached from ABOVE [vfs_unlink]. *)
Example unlinkat_trailing_slash_on_a_file_is_enotdir :
  match check_syscall
          (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a_slash (fun _ => None))
          (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [104])] IEof)) with
  | CheckOk m [] => m_fs m = [([97], [104])]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** The rejecting half: a kernel that removed the file through "a/" and
    returned 0 is a kernel this model must not admit.  Without the
    [path_trailing_slash] test this case is the ordinary removal and
    accepts, so this is what separates the two spellings of the arm. *)
Example unlinkat_trailing_slash_success_rejected :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a_slash (fun _ => None))
    (with_copyins [(8192, 3%nat)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [104])] IEof))
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** [mnt_want_write] and dentry allocation precede [slashes:], but
    [may_delete] does not run there.  Each admitted refusal preserves
    the whole model, not just its file map. *)
Example unlinkat_trailing_slash_admits_earlier_refusals :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [104])] IEof) in
  let call e := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_name_a_slash (fun _ => None))
        (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret e) [] [])) m0 in
  call ENOTDIR = CheckOk m0 []
  /\ call EROFS = CheckOk m0 []
  /\ call ENOMEM = CheckOk m0 []
  /\ call EACCES = CheckReject
  /\ call EOVERFLOW = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** "/" has no component, so [link_path_walk] leaves the type at its
    initial LAST_ROOT and [do_rmdir]'s [case LAST_ROOT] answers -EBUSY.
    The file system is not consulted, so an EMPTY map gives the same
    answer as any other. *)
Example unlinkat_root_removedir_is_ebusy :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 512; 0; 0; 0]   (* AT_REMOVEDIR *) mem_name_root (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EBUSY) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [].
Proof. vm_compute. reflexivity. Qed.

(** The rejecting half, and the one that matters most: -ENOENT is the
    answer the flat map WOULD give on its own — "no such key" — and it is
    the confident wrong one.  Linux never answers -ENOENT for "/". *)
Example unlinkat_root_enoent_rejected :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 512; 0; 0; 0]   (* AT_REMOVEDIR *) mem_name_root (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOENT) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

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
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [104])] IEof) in
  let call eff := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 512; 0; 0; 0]   (* AT_REMOVEDIR *) mem_name_a (fun _ => None))
        (with_copyins [(8192, 2%nat)] eff) m0 in
  call (mkEffect (errno_ret ENOTDIR) [] []) = CheckOk m0 []
  /\ call (mkEffect (errno_ret EACCES) [] []) = CheckOk m0 []
  /\ call (mkEffect (errno_ret EOVERFLOW) [] []) = CheckOk m0 []
  /\ call (mkEffect 0 [] []) = CheckReject
  /\ call (mkEffect (errno_ret EBUSY) [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ------------------------------------------ an absolute name under /tmp

   A program may write a temporary file and then unlink it by an
   ABSOLUTE name under /tmp.  The /tmp arm answers that shape: the
   removal of a key the run holds, and the -ENOENT of one it does not.
   The cases below pin both from the sides a real run cannot reach.  An
   absolute name under any OTHER directory is still the separator
   guard's decline.

   The shape is worth separating from that decline because the two prices
   [Sys.Fs.Namei.unlinkat_spec]'s WORLD note puts on an interior
   separator do not buy it between them.  A component walk over the
   existing keys answers a name INSIDE the working directory's subtree; a
   recorded working-directory path relates an absolute name to one.  This
   name is neither: its parent is a directory the working directory does
   not contain, so with both paid the map still holds no key for it.
   Closing it in general is the third price the note names — directories
   as state in their own right — and what this arm does INSTEAD is rest
   on the privacy premise, which buys /tmp and nothing else. *)

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

(** The same call on a name the run does not hold: the empty
    image the model starts a run with and an EMPTY declared /tmp.  The
    path is one the /tmp arm names — one component under "/tmp/" — so the
    separator gate is not what answers it.  The run declared nothing at
    that name and created nothing there, and the privacy premise makes
    the run's own table the whole truth about the directory, so the
    answer is the real -ENOENT Linux gives for a negative dentry.
    Nothing moves — the model handed back is the one
    handed in — and the success a kernel holding the file would return is
    refused, which is what keeps the answer from being a licence to
    remove. *)
Example unlinkat_tmp_key_not_held_is_enoent :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  let call eff := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_abs_gif (fun _ => None))
        (with_copyins [(8192, 13%nat)] eff) m0 in
  call (mkEffect (errno_ret ENOENT) [] []) = CheckOk m0 []
  /\ call (mkEffect 0 [] []) = CheckReject.
Proof. vm_compute. split; reflexivity. Qed.

(** THE SECOND UNLINK: a key the run DECLARED and then removed ITSELF.
    The first call takes the key out and returns 0; the second reads the
    table that call left and answers -ENOENT, and a second success is
    refused.

    THIS CASE IS DOCUMENTARY, and saying so is worth more than a
    stronger-sounding claim.  It distinguishes no kernel this file does
    not already distinguish: its first two conjuncts are
    [unlinkat_tmp_declared_key_removed] below on the same fixture, and
    since the arm reads only [m_fs], the model that removal leaves is
    indistinguishable to it from the empty one
    [unlinkat_tmp_key_not_held_is_enoent] above is stated over.  What it
    records is the COMPOSITION a program that cleans up after itself
    makes, written down in one place because its two halves are proved
    separately.  A case that bit on its own would have to leave a SECOND
    declared component behind the removal, so that the post-removal model
    is one no other case reaches. *)
Example unlinkat_tmp_removed_key_second_unlink_is_enoent :
  let call eff m := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_abs_gif (fun _ => None))
        (with_copyins [(8192, 13%nat)] eff) m in
  match call (mkEffect 0 [] [])
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input_tmp [] [([111; 117; 116; 46; 103; 105; 102], [104])]
                IEof)) with
  | CheckOk m1 [] =>
      m_fs m1 = []
      /\ call (mkEffect (errno_ret ENOENT) [] []) m1 = CheckOk m1 []
      /\ call (mkEffect 0 [] []) m1 = CheckReject
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE REMOVAL ITSELF, over a /tmp the run DECLARED ([State.in_tmp]
    carrying the one component "out.gif", which [State.fs_seed_tmp]
    seeds under "/tmp/").  The key is gone afterwards, and nothing else
    moved. *)
Example unlinkat_tmp_declared_key_removed :
  match check_syscall
          (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_abs_gif (fun _ => None))
          (with_copyins [(8192, 13%nat)] (mkEffect 0 [] []))
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input_tmp [] [([111; 117; 116; 46; 103; 105; 102], [104])] IEof)) with
  | CheckOk m [] => m_fs m = []
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** The SAME image written as a raw key rather than as a declaration.
    The two are one model — the seeding puts the declared component
    under "/tmp/" and nowhere else — so the arm cannot tell a declared
    entry from an image key that spells the same path, and this case is
    what says so.  It also records the reading the /tmp arm gives: a
    "/tmp/"-prefixed key IS the file in the run's private /tmp. *)
Example unlinkat_tmp_image_key_removed :
  match check_syscall
          (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_abs_gif (fun _ => None))
          (with_copyins [(8192, 13%nat)] (mkEffect 0 [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input [(abs_gif_name, [104])] IEof)) with
  | CheckOk m [] => m_fs m = []
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** What stays declined under /tmp, each on the image that HOLDS the
    key, so that none of them is declining for want of the file.

    AT_REMOVEDIR is declined: Linux answers -ENOTDIR here (a model file
    is never a directory), and the working-directory arm says so, but
    which answer it is turns on /tmp holding a directory, which the /tmp
    arm does not model.  A second component needs a walk.  "/tmp"
    itself, "/tmp/" and "/tmp/." name the directory rather than a file
    in it. *)
Example unlinkat_tmp_excluded_shapes_unmodeled :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input [(abs_gif_name, [104]); ([47; 116; 109; 112; 47; 100; 47; 102], [104])] IEof) in
  let call mem n flags eff := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; flags; 0; 0; 0] mem (fun _ => None))
        (with_copyins [(8192, n)] eff) m0 in
  (* AT_REMOVEDIR at the very name the plain flag removes *)
  call mem_abs_gif 13%nat 512 (* AT_REMOVEDIR *) (mkEffect (errno_ret ENOTDIR) [] []) = CheckUnmodeled
  (* a second component, "/tmp/d/f", whose key the image holds *)
  /\ call (bytes_at 8192 ([47; 116; 109; 112; 47; 100; 47; 102] ++ [0])) 9%nat 0
       (mkEffect 0 [] []) = CheckUnmodeled
  (* the directory itself, in its three spellings *)
  /\ call (bytes_at 8192 ([47; 116; 109; 112] ++ [0])) 5%nat 0
       (mkEffect (errno_ret EISDIR) [] []) = CheckUnmodeled
  /\ call (bytes_at 8192 ([47; 116; 109; 112; 47] ++ [0])) 6%nat 0
       (mkEffect (errno_ret EISDIR) [] []) = CheckUnmodeled
  /\ call (bytes_at 8192 ([47; 116; 109; 112; 47; 46] ++ [0])) 7%nat 0
       (mkEffect (errno_ret EISDIR) [] []) = CheckUnmodeled
  /\ call (bytes_at 8192 ([47; 116; 109; 112; 47; 46; 46] ++ [0])) 8%nat 0
       (mkEffect (errno_ret EISDIR) [] []) = CheckUnmodeled.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A DIRECTORY INSIDE /tmp, which the flat map only implies: the
    declaration names "d/f", so a key lives under "/tmp/d" and
    [Fs.Namei.fs_under] sees it there.  Linux refuses to unlink a
    directory in [may_delete], which [vfs_unlink] calls before it
    removes anything, so the type answer is -EISDIR and the model does
    not move.  The removal a flat map would have performed is refused
    beside it.  (What else that spelling admits is the next case.)

    THE TRAILING-SEPARATOR SPELLING IS THE SAME ANSWER BY A DIFFERENT
    ROUTE, which is why it is worth pinning next to the plain one: the
    model strips the separator and reaches the same arm, and Linux does
    not — it jumps to [do_unlinkat]'s [slashes:] label, whose own
    [d_is_dir] test answers -EISDIR for a directory.  (fs/namei.c, Linux
    v6.18.46.) *)
Example unlinkat_tmp_implied_directory_is_eisdir :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([100; 47; 102], [104])] IEof) in
  let call mem n eff := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem (fun _ => None))
        (with_copyins [(8192, n)] eff) m0 in
  let dir := bytes_at 8192 ([47; 116; 109; 112; 47; 100] ++ [0]) in
  let dir_slash := bytes_at 8192 ([47; 116; 109; 112; 47; 100; 47] ++ [0]) in
  call dir 7%nat (mkEffect (errno_ret EISDIR) [] []) = CheckOk m0 []
  /\ call dir 7%nat (mkEffect 0 [] []) = CheckReject
  /\ call dir_slash 8%nat (mkEffect (errno_ret EISDIR) [] []) = CheckOk m0 []
  /\ call dir_slash 8%nat (mkEffect 0 [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** WHAT COMES BEFORE THAT -EISDIR, spelling by spelling.  On the plain
    spelling [vfs_unlink] reaches [may_delete]'s -EISDIR only after
    [do_unlinkat]'s -EROFS, the lookup's -ENOMEM and [may_delete]'s own
    -EOVERFLOW, -EACCES and -EPERM: the -EISDIR is still admitted, an
    -EACCES and an -EOVERFLOW are admitted beside it, each leaving the
    model as it was, and the -EBUSY of a mount point, which
    [vfs_unlink] raises only after [may_delete] has passed, is refused.
    The trailing-separator spelling reaches its -EISDIR at
    [do_unlinkat]'s [slashes:] label, after -EROFS and -ENOMEM but
    without [may_delete], so -EACCES remains refused there.
    (fs/namei.c, Linux v6.18.46.) *)
Example unlinkat_tmp_directory_admits_earlier_refusals :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([100; 47; 102], [104])] IEof) in
  let call mem n eff := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem (fun _ => None))
        (with_copyins [(8192, n)] eff) m0 in
  let dir := bytes_at 8192 ([47; 116; 109; 112; 47; 100] ++ [0]) in
  let dir_slash := bytes_at 8192 ([47; 116; 109; 112; 47; 100; 47] ++ [0]) in
  call dir 7%nat (mkEffect (errno_ret EISDIR) [] []) = CheckOk m0 []
  /\ call dir 7%nat (mkEffect (errno_ret EACCES) [] []) = CheckOk m0 []
  /\ call dir 7%nat (mkEffect (errno_ret EOVERFLOW) [] []) = CheckOk m0 []
  /\ call dir 7%nat (mkEffect (errno_ret EBUSY) [] []) = CheckReject
  /\ call dir_slash 8%nat (mkEffect (errno_ret EISDIR) [] []) = CheckOk m0 []
  /\ call dir_slash 8%nat (mkEffect (errno_ret EROFS) [] []) = CheckOk m0 []
  /\ call dir_slash 8%nat (mkEffect (errno_ret ENOMEM) [] []) = CheckOk m0 []
  /\ call dir_slash 8%nat (mkEffect (errno_ret EACCES) [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE ORDER OF THE TWO /tmp RULES, which is the whole of what keeps
    the answer above right.  "/tmp/d" is not a key the run HOLDS — the
    declaration named "d/f" and nothing else — so the rule that answers
    a name the run does not hold would call it -ENOENT, and Linux calls
    it -EISDIR.  [Fs.Namei.unlinkat_tmp_spec] tests [fs_under] BEFORE
    the lookup, so the directory wins; this case is what says the two
    rules are in that order and not the other one, by refusing the
    -ENOENT.

    The honest twin is the second half: at a name with nothing under it,
    the not-held rule still fires and -ENOENT is still the answer.
    Without it a spec that answered -EISDIR for every absent name under
    /tmp would pass the first half. *)
Example unlinkat_tmp_implied_directory_precedes_not_held :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([100; 47; 102], [104])] IEof) in
  let call mem n eff := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem (fun _ => None))
        (with_copyins [(8192, n)] eff) m0 in
  let dir := bytes_at 8192 ([47; 116; 109; 112; 47; 100] ++ [0]) in
  (* the implied directory: -ENOENT is REFUSED, -EISDIR is the answer *)
  call dir 7%nat (mkEffect (errno_ret ENOENT) [] []) = CheckReject
  /\ call dir 7%nat (mkEffect (errno_ret EISDIR) [] []) = CheckOk m0 []
  (* a name with nothing under it: the not-held rule still answers *)
  /\ call mem_abs_gif 13%nat (mkEffect (errno_ret ENOENT) [] []) = CheckOk m0 []
  /\ call mem_abs_gif 13%nat (mkEffect (errno_ret EISDIR) [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE OTHER HONEST TWIN: the -EISDIR does not leak onto a sibling.
    On a /tmp declaring both the nested "d/f" and a plain "out.gif", the
    plain key is still REMOVED and the nested declaration is still
    seeded at its own key — [State.in_tmp] does not forbid a separator
    in a declared name. *)
Example unlinkat_tmp_implied_directory_sibling_still_unlinks :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp []
                 [([100; 47; 102], [104]);
                  ([111; 117; 116; 46; 103; 105; 102], [104])] IEof) in
  fs_lookup (m_fs m0) [47; 116; 109; 112; 47; 100; 47; 102] = Some [104]
  /\ match check_syscall
             (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_abs_gif (fun _ => None))
             (with_copyins [(8192, 13%nat)] (mkEffect 0 [] [])) m0 with
     | CheckOk m [] =>
         fs_lookup (m_fs m) abs_gif_name = None
         /\ fs_lookup (m_fs m) [47; 116; 109; 112; 47; 100; 47; 102] = Some [104]
     | _ => False
     end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE [Uapi.NAME_MAX] BOUNDARY on this arm, from both sides, as the
    openat twin has it ([Checks.Cases.Fs.Open.openat_tmp_name_max_boundary]).
    Both arms have to draw the line at the same place, since "held" is
    one predicate over one key space: a component the open can mint and
    the unlink cannot remove would be a file the run could not get rid
    of.  So a component of 255 bytes is REMOVED and one of 256 is
    DECLINED, over a declaration holding each. *)
Example unlinkat_tmp_name_max_boundary :
  let name n := List.repeat (Z_to_bv 8 97) n in
  let call n := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0]
           (bytes_at 8192 ([Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109;
                            Z_to_bv 8 112; Z_to_bv 8 47] ++ name n
                           ++ [Z_to_bv 8 0])) (fun _ => None))
        (with_copyins [(8192, (6 + n)%nat)] (mkEffect 0 [] []))
        (init_model [] 0 0 demo_sp demo_limit
           (demo_input_tmp [] [(name n, [Z_to_bv 8 104])] IEof)) in
  (* 255: the key the declaration seeded is removed *)
  match call 255%nat with CheckOk m [] => m_fs m = [] | _ => False end
  (* 256: declined, though the run holds the key just the same *)
  /\ call 256%nat = CheckUnmodeled.
Proof. vm_compute. split; reflexivity. Qed.

(** A NAME the declaration could not put anywhere: a component with a
    NUL byte in it.  [State.fs_seed_tmp] drops it, so the run holds
    nothing at that name, and no pathname could reach it in any case —
    [Uaccess.read_cstr] stops at the NUL, so the path this call passes is
    "/tmp/o", not "/tmp/o\0ut".  The declaration is not an image the
    model can be surprised by. *)
Example unlinkat_tmp_nul_name_is_not_seeded :
  m_fs (init_model [] 0 0 demo_sp demo_limit
          (demo_input_tmp [] [([111; 0; 117; 116], [104])] IEof)) = [].
Proof. vm_compute. reflexivity. Qed.

(** The rejecting half, reached through the name the walk WOULD end at.
    "out.gif" carries no separator, so it is answered rather than
    declined — and on the image above it is answered -ENOENT, because
    [Fs.Namei.fs_under] is a COMPONENT prefix and "/tmp/out.gif" does not
    live under "out.gif".  A kernel that removed something through it is
    not admitted.  Without this the two cases above are consistent with a
    model that reads the flat map as a directory tree. *)
Example unlinkat_absolute_basename_success_rejected :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_gif_basename (fun _ => None))
    (with_copyins [(8192, 8%nat)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [(abs_gif_name, [104])] IEof))
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** ...and the answer it does admit, so the rejection above is about the
    removal and not about the ledger. *)
Example unlinkat_absolute_basename_is_enoent :
  check_syscall
    (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem_gif_basename (fun _ => None))
    (with_copyins [(8192, 8%nat)] (mkEffect (errno_ret ENOENT) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [(abs_gif_name, [104])] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [(abs_gif_name, [104])] IEof)) [].
Proof. vm_compute. reflexivity. Qed.

(** The open-file /tmp route must make the same distinction at
    [slashes:], without changing the descriptor or the named file. *)
Example unlinkat_open_tmp_trailing_slash_admits_earlier_refusals :
  let p : path := [47; 116; 109; 112; 47; 120] in
  let m0 := with_fds [(3, FdFileRW p 0)]
              (init_model [] 0 0 demo_sp demo_limit
                 (demo_input_tmp [] [([120], [104])] IEof)) in
  let call e := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0]
           (bytes_at 8192 (p ++ [47; 0])) (fun _ => None))
        (with_copyins [(8192, 8%nat)] (mkEffect (errno_ret e) [] [])) m0 in
  call ENOTDIR = CheckOk m0 []
  /\ call EROFS = CheckOk m0 []
  /\ call ENOMEM = CheckOk m0 []
  /\ call EACCES = CheckReject
  /\ call EOVERFLOW = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** [may_delete]'s unmapped-id refusal also precedes actual removal,
    including the /tmp route that would detach an open descriptor. *)
Example unlinkat_removal_admits_eoverflow :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [104])] IEof) in
  let p : path := [47; 116; 109; 112; 47; 120] in
  let mt := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([120], [104])] IEof) in
  let mo := with_fds [(3, FdFileRW p 0)] mt in
  let call mem n m := check_syscall
        (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] mem (fun _ => None))
        (with_copyins [(8192, n)] (mkEffect (errno_ret EOVERFLOW) [] [])) m in
  call mem_name_a 2%nat m0 = CheckOk m0 []
  /\ call (bytes_at 8192 (p ++ [0])) 7%nat mt = CheckOk mt []
  /\ call (bytes_at 8192 (p ++ [0])) 7%nat mo = CheckOk mo [].
Proof. vm_compute. repeat split; reflexivity. Qed.
