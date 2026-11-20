(** * LinuxProcessSem.Checks.Cases.Fs.Resolve — worked examples over the path namespace

    Mirrors [Fs.v]'s namespace section, which answers to Linux
    fs/namei.c ([link_path_walk], [walk_component], [step_into],
    [follow_dotdot], [lookup_last], [may_open], [do_rmdir],
    [do_mkdirat]) and to fs/namei.c's [getname_flags] for the empty
    pathname: this file holds the worked examples for the key
    discipline, the resolution function, well-formedness, the default
    image and the migration, and no others.

    These are worked examples over the specs and checkers for the
    matching module, read off without running a binary.  Everything here
    is decided by [vm_compute]: the point of the namespace being
    EXECUTABLE is that a claim about it is a computation and not an
    argument, so a walk-order regression is a red check rather than a
    review miss.

    Ported from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export Prelude.

Open Scope Z_scope.

(** A path written as the bytes it is.  Every literal below is ASCII, so
    a reader can check the spelling against the comment beside it. *)
Definition rp (l : list Z) : Fs.path := map (Z_to_bv 8) l.

(** THE FIXTURE IMAGE: the default image at the default working
    directory, plus one regular file and one empty directory in it.

        /  /dev  /dev/null  /dev/urandom  /tmp  /work  /work/d  /work/f

    The empty directory is not decoration: it is the entry a flat map
    could not hold at all, and half the refutations below are about
    telling it from a file. *)
Definition ns_image : Fs.Fs :=
  Fs.fs_set (Fs.fs_create_file (Fs.standard_root Fs.default_cwd)
               (rp [47;119;111;114;107;47;102]) [Z_to_bv 8 65])
            (rp [47;119;111;114;107;47;100]) Fs.EDir.

Definition ns_cwd : Fs.path := Fs.default_cwd.               (* /work *)

(** The walk most arms take ([Fs.WalkFull]): the last link followed and
    no folder demanded, as [open] without O_CREAT, [stat] and
    [faccessat] walk.  The pins below that are about another end of the
    walk name their mode. *)
Definition ns_md : Fs.WalkMode := Fs.WalkFull true false.

(** The outcome of resolving [p] from the fixture's working directory. *)
Definition ns (p : list Z) : Fs.Resolved :=
  fst (fst (Fs.resolve ns_md ns_image ns_cwd (rp p))).

(** The same, against an image a pin builds for itself.  Several of the
    /dev pins below need an entry the fixture does not ship, and
    writing the projection out at each one buried the claim. *)
Definition ns_of (fs : Fs.Fs) (p : list Z) : Fs.Resolved :=
  fst (fst (Fs.resolve ns_md fs ns_cwd (rp p))).

Definition ns_last (p : list Z) : Fs.LastKind :=
  snd (fst (Fs.resolve ns_md ns_image ns_cwd (rp p))).

Definition ns_slash (p : list Z) : bool :=
  snd (Fs.resolve ns_md ns_image ns_cwd (rp p)).

(** Whether the walk handed a component over [Fs.name_max] to the file
    system's lookup, which admits -ENAMETOOLONG beside its answer. *)
Definition ns_long (p : list Z) : bool :=
  Fs.wr_long (Fs.resolve_res ns_md ns_image ns_cwd (rp p)).

(* =========================================================================
   PART 1 — the image is well formed, and so is every image shipped
   ========================================================================= *)

(** THE SATISFIABILITY PINS.  Every agent theorem has [Run.valid_input]
    as a hypothesis, so a validity predicate nothing satisfies would
    make every one of them vacuously true.  These decide, by
    computation, that the file-system clauses are satisfiable — first on
    the default image, then on a migrated non-trivial legacy literal,
    then on the fixture. *)
Example wf_standard_root : Fs.wf_fsb (Fs.standard_root Fs.default_cwd) = true.
Proof. vm_compute. reflexivity. Qed.

Example wf_ns_image : Fs.wf_fsb ns_image = true.
Proof. vm_compute. reflexivity. Qed.

Example wf_migrated_legacy :
  Fs.wf_fsb (fst (Fs.migrate_image Fs.default_cwd
                    [(rp [102], [Z_to_bv 8 65]);
                     (rp [100;47;103], [Z_to_bv 8 66]);
                     (rp [111;117;116;46;103;105;102], [])])) = true.
Proof. vm_compute. reflexivity. Qed.

(** THE STANDARD-ROOT PREMISE is satisfied by the default image, which
    is what makes [Run.standard_root_premise] a premise a launch can
    meet rather than one nothing can. *)
Example standard_root_present_holds :
  Fs.standard_root_presentb (Fs.standard_root Fs.default_cwd) = true.
Proof. vm_compute. reflexivity. Qed.

Example ns_image_has_the_standard_root :
  Fs.standard_root_presentb ns_image = true.
Proof. vm_compute. reflexivity. Qed.

(** THE MALFORMED-IMAGE REFUTATIONS, which close the ledger gap the
    inventory recorded: before this file nothing stated [~ Fs.wf_fs _]
    or [fs_sorted _ = false] on a literal.  Each one fails a DIFFERENT
    clause of [Fs.wf_fs]. *)
Example wf_rejects_a_relative_key :
  Fs.wf_fsb (Fs.fs_create_file (Fs.standard_root Fs.default_cwd)
               (rp [102]) []) = false.
Proof. vm_compute. reflexivity. Qed.

Example wf_rejects_a_trailing_slash_key :
  Fs.wf_fsb (Fs.fs_create_file (Fs.standard_root Fs.default_cwd)
               (rp [47;119;111;114;107;47]) []) = false.
Proof. vm_compute. reflexivity. Qed.

Example wf_rejects_a_dot_component :
  Fs.wf_fsb (Fs.fs_create_file (Fs.standard_root Fs.default_cwd)
               (rp [47;119;111;114;107;47;46;47;102]) []) = false.
Proof. vm_compute. reflexivity. Qed.

Example wf_rejects_a_doubled_separator :
  Fs.wf_fsb (Fs.fs_create_file (Fs.standard_root Fs.default_cwd)
               (rp [47;47;102]) []) = false.
Proof. vm_compute. reflexivity. Qed.

Example wf_rejects_an_absent_parent :
  Fs.wf_fsb (Fs.fs_create_file (Fs.standard_root Fs.default_cwd)
               (rp [47;97;47;98]) []) = false.
Proof. vm_compute. reflexivity. Qed.

Example wf_rejects_a_file_as_a_parent :
  Fs.wf_fsb (Fs.fs_create_file ns_image
               (rp [47;119;111;114;107;47;102;47;103]) []) = false.
Proof. vm_compute. reflexivity. Qed.

Example wf_rejects_a_missing_root :
  Fs.wf_fsb (Fs.fs_of_tree [(rp [47;97], Fs.EDir)]) = false.
Proof. vm_compute. reflexivity. Qed.

Example wf_rejects_an_unsorted_image :
  Fs.wf_fsb (Fs.fs_of_tree [(rp [47;98], Fs.EDir); (rp [47], Fs.EDir)]) = false.
Proof. vm_compute. reflexivity. Qed.

(** ... AND [wf_fsb] AGREES WITH [wf_fs], which is what lets a fixture
    be decided by computation and a theorem reason about the [Prop]. *)
Example wf_bridge_positive : Fs.wf_fs ns_image.
Proof. apply Fs.wf_fsb_iff. vm_compute. reflexivity. Qed.

Example wf_bridge_negative : ~ Fs.wf_fs (Fs.fs_of_tree [(rp [47;97], Fs.EDir)]).
Proof.
  intros H. apply Fs.wf_fsb_iff in H. vm_compute in H. discriminate.
Qed.

(* =========================================================================
   PART 2 — the walk is left-to-right, in the kernel's order
   ========================================================================= *)

(** THE REFUTATIONS OF THE NORMALISE-FIRST READING.  A model that
    textually normalised a pathname before walking it would answer every
    one of these differently, and each answer below is Linux's.  They
    are the reason [Fs.resolve] is a per-component fold and not a
    rewrite of the byte string. *)

(** "missing/../x": Linux walks "missing", does not find it, and returns
    -ENOENT.  A normalise-first model would cancel "missing/.." and
    answer for "x". *)
Example walk_missing_dotdot_is_absent :
  ns [109;47;46;46;47;120] = Fs.RAbsent (rp [47;119;111;114;107;47;109]).
Proof. vm_compute. reflexivity. Qed.

(** "f/../x" and "f/.": "f" is a FILE, so the walk cannot step through
    it — -ENOTDIR, not the answer for "x" and not the answer for "f". *)
Example walk_file_dotdot_is_notdir :
  ns [102;47;46;46;47;120] = Fs.RNotDir (rp [47;119;111;114;107;47;102]).
Proof. vm_compute. reflexivity. Qed.

Example walk_file_dot_is_notdir :
  ns [102;47;46] = Fs.RNotDir (rp [47;119;111;114;107;47;102]).
Proof. vm_compute. reflexivity. Qed.

(** A directory CAN be stepped through, which is the control for the
    two above. *)
Example walk_dir_dotdot_reaches_the_cwd :
  ns [100;47;46;46;47;102] = Fs.RFound (rp [47;119;111;114;107;47;102])
                                       (Fs.EFile 1).
Proof. vm_compute. reflexivity. Qed.

(** AN OVER-LONG COMPONENT IS HANDED TO THE FILE SYSTEM'S LOOKUP ONLY
    WHEN THE WALK REACHES IT.  The length limit is the file system's
    ([simple_lookup], fs/libfs.c:71-72, the lookup of tmpfs and ramfs),
    so the walk goes on as a file system with a larger limit would, an
    answer no supported kernel gives ([Fs.comp_too_long]), and records
    that the limit was crossed ([Fs.wr_long]): the arms admit
    -ENAMETOOLONG beside the answer.
    Reached, the 300-byte name is looked up and absent; behind an absent
    component or a file, it is never looked at. *)
Definition long300 : list Z := repeat 97 300.

Example walk_toolong_when_reached :
  ns (long300 ++ [47;46;46;47;120])
  = Fs.RAbsent (rp ([47;119;111;114;107;47] ++ long300))
  /\ ns_long (long300 ++ [47;46;46;47;120]) = true.
Proof. split; vm_compute; reflexivity. Qed.

(** ... AND BEHIND A NON-DIRECTORY IT IS NEVER LOOKED UP.  The order is
    the kernel's: [link_path_walk]'s loop ends with [d_can_lookup] on the
    dentry the previous component reached (fs/namei.c:2529-2535), so a
    file answers -ENOTDIR before the next component is hashed; the
    length limit lives in the file system's own [->lookup], which only a
    directory is ever asked.  The pair with the [RAbsent] pin below is
    what says the limit is met from a DIRECTORY and from nothing else. *)
Example walk_toolong_behind_a_file_is_notdir :
  ns ([102; 47] ++ long300) = Fs.RNotDir (rp [47;119;111;114;107;47;102])
  /\ ns_long ([102; 47] ++ long300) = false.
Proof. split; vm_compute; reflexivity. Qed.

Example walk_toolong_behind_a_missing_component_is_absent :
  ns ([109;47] ++ long300) = Fs.RAbsent (rp [47;119;111;114;107;47;109])
  /\ ns_long ([109;47] ++ long300) = false.
Proof. split; vm_compute; reflexivity. Qed.

Example walk_name_max_boundary_is_255 :
  ns (repeat 97 255) = Fs.RMissing Fs.default_cwd (rp (repeat 97 255))
  /\ ns_long (repeat 97 255) = false.
Proof. split; vm_compute; reflexivity. Qed.

Example walk_name_max_boundary_is_not_256 :
  ns (repeat 97 256) = Fs.RMissing Fs.default_cwd (rp (repeat 97 256))
  /\ ns_long (repeat 97 256) = true.
Proof. split; vm_compute; reflexivity. Qed.

(** [ROutside] IS A WALK-STATE TEST, NOT A SPELLING TEST: "proc" or
    "sys" looked up while the walk stands on the root is outside,
    whatever spelling led there.  All four spellings, pinned. *)
Example outside_absolute_proc :
  ns [47;112;114;111;99;47;46;46;47;101;116;99;47;120] = Fs.ROutside.
Proof. vm_compute. reflexivity. Qed.

Example outside_dotdot_from_the_cwd :
  ns [46;46;47;112;114;111;99;47;120] = Fs.ROutside.
Proof. vm_compute. reflexivity. Qed.

Example outside_through_a_dot :
  ns [47;46;47;112;114;111;99;47;120] = Fs.ROutside.
Proof. vm_compute. reflexivity. Qed.

Example outside_sys_through_a_dotdot :
  ns [47;119;111;114;107;47;46;46;47;115;121;115;47;120] = Fs.ROutside.
Proof. vm_compute. reflexivity. Qed.

(** ... and NOT outside where the walk is not standing on the root: a
    directory named "proc" under the working directory is an ordinary
    name. *)
Example not_outside_below_the_root :
  fst (fst (Fs.resolve ns_md
              (Fs.fs_set ns_image (rp [47;119;111;114;107;47;112;114;111;99])
                 Fs.EDir)
              ns_cwd (rp [112;114;111;99])))
  = Fs.RFound (rp [47;119;111;114;107;47;112;114;111;99]) Fs.EDir.
Proof. vm_compute. reflexivity. Qed.

(** REPEATED AND TRAILING SEPARATORS are skipped, as [link_path_walk]
    skips them: "//a" is "/a", and a trailing one changes the FLAG and
    not the outcome. *)
Example doubled_separator_resolves_as_one :
  ns [47;47;119;111;114;107] = ns [47;119;111;114;107].
Proof. vm_compute. reflexivity. Qed.

Example dotdot_at_the_root_stays_at_the_root :
  ns [47;46;46] = Fs.RFound Fs.root Fs.EDir.
Proof. vm_compute. reflexivity. Qed.

Example dotdot_at_the_root_twice_stays_at_the_root :
  ns [47;46;46;47;46;46] = Fs.RFound Fs.root Fs.EDir.
Proof. vm_compute. reflexivity. Qed.

(** AN ABSENT LAST COMPONENT IS [RMissing] AND CARRIES ITS PARENT, which
    is what an [O_CREAT] arm creates under; an absent PROPER PREFIX is
    [RAbsent], which no arm may create under. *)
Example missing_last_component_carries_its_parent :
  ns [122] = Fs.RMissing Fs.default_cwd (rp [122]).
Proof. vm_compute. reflexivity. Qed.

Example missing_proper_prefix_is_absent :
  ns [122;47;121] = Fs.RAbsent (rp [47;119;111;114;107;47;122]).
Proof. vm_compute. reflexivity. Qed.

(** THE DEVICES ARE ENTRIES, not magic names: resolution finds them, and
    an image that did not hold them would answer -ENOENT by resolution
    rather than by an arm that recognised a spelling. *)
Example devnull_resolves_to_the_device :
  ns [47;100;101;118;47;110;117;108;108]
  = Fs.RFound Fs.devnull_key (Fs.EDev Fs.DevNull).
Proof. vm_compute. reflexivity. Qed.

Example urandom_resolves_to_the_device :
  ns [47;100;101;118;47;117;114;97;110;100;111;109]
  = Fs.RFound Fs.urandom_key (Fs.EDev Fs.DevUrandom).
Proof. vm_compute. reflexivity. Qed.

Example localtime_is_absent_by_resolution :
  ns [47;101;116;99;47;108;111;99;97;108;116;105;109;101]
  = Fs.RAbsent (rp [47;101;116;99]).
Proof. vm_compute. reflexivity. Qed.

(** A NAME THE WALK DOES NOT FIND UNDER /dev IS MISSING, as it is in
    every other folder.  The image describes /dev completely at launch
    and the kernel makes no device node during the run ([Fs.dev_dir]
    carries the argument; in Linux v6.18.46 a devtmpfs node is made by
    [devtmpfs_create_node], drivers/base/devtmpfs.c:129-154, when a
    driver-core device is registered), so a name the image does not
    hold under /dev is a name the guest does not have, and its open is
    the walk's -ENOENT. *)
Example devzero_is_missing :
  ns [47;100;101;118;47;122;101;114;111]
  = Fs.RMissing Fs.dev_dir (rp [122;101;114;111]).
Proof. vm_compute. reflexivity. Qed.

(** ... AND AN ABSENCE THAT IS NOT THE LAST COMPONENT is [RAbsent], as
    it is anywhere else. *)
Example devzero_with_a_tail_is_absent :
  ns [47;100;101;118;47;122;101;114;111;47;120]
  = Fs.RAbsent (rp [47;100;101;118;47;122;101;114;111]).
Proof. vm_compute. reflexivity. Qed.

Example dev_absent_through_a_dotdot_is_absent :
  ns [47;100;101;118;47;102;111;111;47;46;46;47;120]
  = Fs.RAbsent (rp [47;100;101;118;47;102;111;111]).
Proof. vm_compute. reflexivity. Qed.

(** ... by any spelling that reaches /dev, and from a working directory
    of /dev. *)
Example dev_reached_through_a_dotdot_is_missing :
  ns [47;119;111;114;107;47;46;46;47;100;101;118;47;122;101;114;111]
  = Fs.RMissing Fs.dev_dir (rp [122;101;114;111]).
Proof. vm_compute. reflexivity. Qed.

Example relative_name_from_dev_is_missing :
  fst (fst (Fs.resolve ns_md ns_image Fs.dev_dir (rp [122;101;114;111])))
  = Fs.RMissing Fs.dev_dir (rp [122;101;114;111]).
Proof. vm_compute. reflexivity. Qed.

(** THE CONTROLS: a name the image DOES hold under /dev answers as a
    found entry, from the root and from a working directory of /dev
    alike; /dev itself is a directory; and a found entry under /dev
    reports [RNotDir] when a component follows it. *)
Example devnull_answers_beside_an_absent_name :
  ns [47;100;101;118;47;110;117;108;108]
  = Fs.RFound Fs.devnull_key (Fs.EDev Fs.DevNull).
Proof. vm_compute. reflexivity. Qed.

Example relative_null_from_dev_still_answers :
  fst (fst (Fs.resolve ns_md ns_image Fs.dev_dir (rp [110;117;108;108])))
  = Fs.RFound Fs.devnull_key (Fs.EDev Fs.DevNull).
Proof. vm_compute. reflexivity. Qed.

Example dev_itself_is_still_a_directory :
  ns [47;100;101;118] = Fs.RFound Fs.dev_dir Fs.EDir.
Proof. vm_compute. reflexivity. Qed.

Example a_tail_behind_devnull_is_still_notdir :
  ns [47;100;101;118;47;110;117;108;108;47;120] = Fs.RNotDir Fs.devnull_key.
Proof. vm_compute. reflexivity. Qed.

(** ONE LEVEL DOWN THE SAME HOLDS.  A numbered node under /dev/pts is
    made by [devpts_pty_new] (fs/devpts/inode.c:512-547), which
    [ptmx_open] (drivers/tty/pty.c:790-869) calls at
    drivers/tty/pty.c:842, and the image has no entry kind an open of
    /dev/ptmx could reach, so the run cannot make one either: an image
    that DECLARES /dev/pts and nothing in it answers [RMissing] there.
    The fixture pin beside it says /dev/pts really is in the image and
    really is a directory, so the declared pin is about the deeper key;
    with /dev/pts ABSENT the walk fails one level up, at /dev. *)
Definition ns_image_devpts : Fs.Fs :=
  Fs.fs_set ns_image (rp [47;100;101;118;47;112;116;115]) Fs.EDir.

Example devpts_fixture_really_declares_the_directory :
  ns_of ns_image_devpts [47;100;101;118;47;112;116;115]
  = Fs.RFound (rp [47;100;101;118;47;112;116;115]) Fs.EDir.
Proof. vm_compute. reflexivity. Qed.

Example devpts_declared_absence_is_missing :
  ns_of ns_image_devpts [47;100;101;118;47;112;116;115;47;48]
  = Fs.RMissing (rp [47;100;101;118;47;112;116;115]) (rp [48]).
Proof. vm_compute. reflexivity. Qed.

Example devpts_undeclared_absence_is_absent :
  ns [47;100;101;118;47;112;116;115;47;48]
  = Fs.RAbsent (rp [47;100;101;118;47;112;116;115]).
Proof. vm_compute. reflexivity. Qed.

(** ... and from a WORKING DIRECTORY inside the subtree.  The twin under
    it: with /dev/pts absent the walk cannot even START there, so
    [resolve] answers [RAbsent] for the working directory itself. *)
Example relative_name_from_devpts_is_missing :
  fst (fst (Fs.resolve ns_md ns_image_devpts
              (rp [47;100;101;118;47;112;116;115]) (rp [48])))
  = Fs.RMissing (rp [47;100;101;118;47;112;116;115]) (rp [48]).
Proof. vm_compute. reflexivity. Qed.

Example relative_name_from_an_undeclared_devpts_is_absent :
  fst (fst (Fs.resolve ns_md ns_image
              (rp [47;100;101;118;47;112;116;115]) (rp [48])))
  = Fs.RAbsent (rp [47;100;101;118;47;112;116;115]).
Proof. vm_compute. reflexivity. Qed.

(** A WALK THAT CLIMBS OUT OF THE SUBTREE answers by where it ends. *)
Example a_walk_that_leaves_the_subtree_answers_ordinarily :
  fst (fst (Fs.resolve ns_md ns_image_devpts
              (rp [47;100;101;118;47;112;116;115])
              (rp [46;46;47;46;46;47;116;109;112;47;122;101;114;111])))
  = Fs.RMissing (rp [47;116;109;112]) (rp [122;101;114;111]).
Proof. vm_compute. reflexivity. Qed.

(** A DECLARED ENTRY IN THE SUBTREE ANSWERS: an image that declares a
    regular file under /dev is read exactly as it is written. *)
Definition ns_image_devfoo : Fs.Fs :=
  Fs.fs_create_file ns_image (rp [47;100;101;118;47;102;111;111]) [Z_to_bv 8 66].

(** The file the image declares second is inode 2: [ns_image]'s
    /work/f is inode 1 ([Fs.fs_fresh_ino]). *)
Example a_declared_file_under_dev_is_found :
  ns_of ns_image_devfoo [47;100;101;118;47;102;111;111]
  = Fs.RFound (rp [47;100;101;118;47;102;111;111]) (Fs.EFile 2).
Proof. vm_compute. reflexivity. Qed.

(** THE SUBTREE TEST [Fs.in_dev_subtree], which the validity clause
    [Run.devices_in_dev_subtree] reads, COMPARES COMPONENTS, NOT BYTES:
    "/devices" starts with the same four bytes as "/dev" and is an
    ordinary directory. *)
Definition ns_image_devices : Fs.Fs :=
  Fs.fs_set ns_image (rp [47;100;101;118;105;99;101;115]) Fs.EDir.

Example a_key_that_merely_starts_with_dev_is_ordinary :
  ns_of ns_image_devices [47;100;101;118;105;99;101;115;47;120]
  = Fs.RMissing (rp [47;100;101;118;105;99;101;115]) (rp [120]).
Proof. vm_compute. reflexivity. Qed.

(** THE TWINS: an absent name under /tmp is [RMissing] and -ENOENT, the
    same under a DECLARED /etc, and an absent name under an ABSENT
    directory is [RAbsent] -- the same answers the /dev pins above
    give. *)
Definition ns_image_etc : Fs.Fs :=
  Fs.fs_set ns_image (rp [47;101;116;99]) Fs.EDir.

Example absent_under_a_declared_etc_is_still_missing :
  ns_of ns_image_etc [47;101;116;99;47;120]
  = Fs.RMissing (rp [47;101;116;99]) (rp [120]).
Proof. vm_compute. reflexivity. Qed.

Example absent_under_tmp_is_still_missing :
  ns [47;116;109;112;47;122;101;114;111]
  = Fs.RMissing (rp [47;116;109;112]) (rp [122;101;114;111]).
Proof. vm_compute. reflexivity. Qed.

Example absent_under_an_absent_etc_is_still_absent :
  ns [47;101;116;99;47;122;101;114;111] = Fs.RAbsent (rp [47;101;116;99]).
Proof. vm_compute. reflexivity. Qed.

(** AN EMPTY DIRECTORY EXISTS: "/work/d" has no key under it and
    resolves to a directory. *)
Example an_empty_directory_resolves :
  ns [100] = Fs.RFound (rp [47;119;111;114;107;47;100]) Fs.EDir.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   PART 3 — the last component's type, and what each walk does with a
   trailing separator
   ========================================================================= *)

(** [do_rmdir] SWITCHES ON THE LAST COMPONENT'S TYPE BEFORE ANY LOOKUP,
    so resolution returns it, computed textually.  One cell per
    constructor, and the shapes that decide them. *)
Example last_kind_normal : ns_last [102] = Fs.LastNorm.
Proof. vm_compute. reflexivity. Qed.

Example last_kind_dot : ns_last [100;47;46] = Fs.LastDot.
Proof. vm_compute. reflexivity. Qed.

Example last_kind_dotdot : ns_last [47;46;46] = Fs.LastDotDot.
Proof. vm_compute. reflexivity. Qed.

Example last_kind_root : ns_last [47] = Fs.LastRoot.
Proof. vm_compute. reflexivity. Qed.

Example last_kind_root_doubled : ns_last [47;47] = Fs.LastRoot.
Proof. vm_compute. reflexivity. Qed.

(** A TRAILING SEPARATOR DOES NOT CHANGE WHICH COMPONENT IS THE LAST
    ONE, and does not change the type. *)
Example last_kind_survives_a_trailing_slash :
  ns_last [102;47] = Fs.LastNorm.
Proof. vm_compute. reflexivity. Qed.

Example last_kind_dot_survives_a_trailing_slash :
  ns_last [100;47;46;47] = Fs.LastDot.
Proof. vm_compute. reflexivity. Qed.

(** ... WHAT IT CHANGES IS THE FLAG, which is the kernel's own
    [last.name[last.len]]. *)
Example trailing_slash_flag_set : ns_slash [102;47] = true.
Proof. vm_compute. reflexivity. Qed.

Example trailing_slash_flag_clear : ns_slash [102] = false.
Proof. vm_compute. reflexivity. Qed.

Example trailing_slash_flag_on_repeated_separators :
  ns_slash [102;47;47] = true.
Proof. vm_compute. reflexivity. Qed.

(** ... and under the FULL walk the separator asks for a folder:
    [lookup_last] sets LOOKUP_DIRECTORY for a LAST_NORM component a
    separator follows (fs/namei.c:2649-2650), and [path_lookupat] ends
    with -ENOTDIR when the walk did not stop on one (:2685-2687).  So
    "f/" on a file is [RNotDir] where "f" is found, and "d/" on a
    directory is found either way. *)
Example trailing_slash_on_a_file_asks_for_a_folder :
  ns [102;47] = Fs.RNotDir (rp [47;119;111;114;107;47;102])
  /\ ns [102] = Fs.RFound (rp [47;119;111;114;107;47;102]) (Fs.EFile 1)
  /\ ns [100;47] = ns [100].
Proof. split_conj; vm_compute; reflexivity. Qed.

(** UNDER O_CREAT THE WALK STOPS IN FRONT OF A SLASHED LAST NAME
    ([Fs.WalkCreate]): [lookup_fast_for_open] answers -EISDIR before any
    lookup (fs/namei.c:3821-3823), so a missing name and a present file
    both end at [RParent], and nothing is looked up.  "." is handed to
    [handle_dots] first (:3848-3868), so "./" is not stopped. *)
Example create_walk_stops_in_front_of_a_slashed_name :
  fst (fst (Fs.resolve (Fs.WalkCreate true) ns_image ns_cwd (rp [120;47])))
  = Fs.RParent Fs.default_cwd (rp [120])
  /\ fst (fst (Fs.resolve (Fs.WalkCreate true) ns_image ns_cwd (rp [102;47])))
     = Fs.RParent Fs.default_cwd (rp [102])
  /\ fst (fst (Fs.resolve (Fs.WalkCreate false) ns_image ns_cwd (rp [46;47])))
     = Fs.RFound Fs.default_cwd Fs.EDir.
Proof. split_conj; vm_compute; reflexivity. Qed.

(** THE PARENT END NEVER LOOKS UP ITS LAST NAME ([path_parentat],
    fs/namei.c:2719-2733): it stops in front of it with the separator
    recorded, and [unlinkat], [rmdir] and [mkdirat] read both. *)
Example parent_walk_stops_in_front_of_the_last_name :
  Fs.resolve Fs.WalkParent ns_image ns_cwd (rp [100;47])
  = (Fs.RParent Fs.default_cwd (rp [100]), Fs.LastNorm, true)
  /\ Fs.resolve Fs.WalkParent ns_image ns_cwd (rp [122])
     = (Fs.RParent Fs.default_cwd (rp [122]), Fs.LastNorm, false)
  /\ Fs.resolve Fs.WalkParent ns_image ns_cwd (rp [47])
     = (Fs.RParent Fs.root [], Fs.LastRoot, false).
Proof. split_conj; vm_compute; reflexivity. Qed.

(* =========================================================================
   PART 4 — the key discipline
   ========================================================================= *)

Example canonical_accepts_the_root : Fs.canonical_key Fs.root = true.
Proof. reflexivity. Qed.

Example canonical_accepts_a_deep_key :
  Fs.canonical_key (rp [47;119;111;114;107;47;100;47;102]) = true.
Proof. vm_compute. reflexivity. Qed.

Example canonical_rejects_the_empty_path : Fs.canonical_key (rp []) = false.
Proof. reflexivity. Qed.

Example canonical_rejects_a_relative_key :
  Fs.canonical_key (rp [102]) = false.
Proof. vm_compute. reflexivity. Qed.

Example canonical_rejects_a_trailing_slash :
  Fs.canonical_key (rp [47;102;47]) = false.
Proof. vm_compute. reflexivity. Qed.

Example canonical_rejects_a_doubled_slash :
  Fs.canonical_key (rp [47;47;102]) = false.
Proof. vm_compute. reflexivity. Qed.

Example canonical_rejects_a_dot_component :
  Fs.canonical_key (rp [47;46]) = false.
Proof. vm_compute. reflexivity. Qed.

Example canonical_rejects_a_dotdot_component :
  Fs.canonical_key (rp [47;46;46]) = false.
Proof. vm_compute. reflexivity. Qed.

Example canonical_rejects_a_nul_in_a_component :
  Fs.canonical_key (rp [47;102;0;103]) = false.
Proof. vm_compute. reflexivity. Qed.

(** A LONG COMPONENT IS STILL A KEY: over-length is the file system's
    refusal, admitted beside the walk's answer ([Fs.wr_long]), and not a
    malformed key, because the limit belongs to the file system's
    [->lookup] rather than to the namespace. *)
Example canonical_accepts_an_over_long_component :
  Fs.canonical_key (rp (47 :: repeat 97 300)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Parents and children round-trip, which is what [Fs.wf_fs]'s parent
    clause and the walk both rest on. *)
Example parent_of_a_deep_key :
  Fs.path_parent (rp [47;119;111;114;107;47;102]) = Fs.default_cwd.
Proof. vm_compute. reflexivity. Qed.

Example parent_of_a_top_level_key :
  Fs.path_parent Fs.default_cwd = Fs.root.
Proof. vm_compute. reflexivity. Qed.

Example parent_of_the_root_is_the_root :
  Fs.path_parent Fs.root = Fs.root.
Proof. reflexivity. Qed.

Example child_of_the_root :
  Fs.child_key Fs.root (rp [100;101;118]) = Fs.dev_dir.
Proof. vm_compute. reflexivity. Qed.

Example child_of_a_deep_key :
  Fs.child_key Fs.default_cwd (rp [102]) = rp [47;119;111;114;107;47;102].
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   PART 5 — the migration, class by class
   ========================================================================= *)

(** A PLAIN LEGACY KEY LANDS UNDER THE WORKING DIRECTORY with its bytes
    intact, in an inode of its own.  This is the class every harness
    recording and every Example is in, and the only one whose MEANING is
    preserved. *)
Example migration_accepts_a_plain_name :
  file_at (fst (Fs.migrate_image Fs.default_cwd
                  [(rp [102], [Z_to_bv 8 65])]))
          (rp [47;119;111;114;107;47;102])
  = Some [Z_to_bv 8 65].
Proof. vm_compute. reflexivity. Qed.

Example migration_accepts_a_nested_name :
  file_at (fst (Fs.migrate_image Fs.default_cwd
                  [(rp [100;47;103], [Z_to_bv 8 66])]))
          (rp [47;119;111;114;107;47;100;47;103])
  = Some [Z_to_bv 8 66].
Proof. vm_compute. reflexivity. Qed.

(** ... and every PROPER PREFIX of an accepted key becomes a directory,
    which is what makes the result well formed. *)
Example migration_mints_the_prefix_directories :
  Fs.fs_lookup (fst (Fs.migrate_image Fs.default_cwd
                       [(rp [100;47;103], [Z_to_bv 8 66])]))
               (rp [47;119;111;114;107;47;100])
  = Some Fs.EDir.
Proof. vm_compute. reflexivity. Qed.

(** THE DEFAULT IMAGE IS UNDERNEATH every migrated literal, so a fixture
    that opened /dev/null yesterday opens the same device today. *)
Example migration_keeps_the_devices :
  Fs.fs_lookup (fst (Fs.migrate_image Fs.default_cwd
                       [(rp [102], [])])) Fs.devnull_key
  = Some (Fs.EDev Fs.DevNull).
Proof. vm_compute. reflexivity. Qed.

Example migration_of_nothing_is_the_default_image :
  fst (Fs.migrate_image Fs.default_cwd []) = Fs.standard_root Fs.default_cwd.
Proof. vm_compute. reflexivity. Qed.

(** THE REJECTION CLASSES, one example each, WITH THE REASON REPORTED.
    The migration rejects rather than normalises: silently rewriting a
    key would move a fixture's file without saying so. *)
Example migration_rejects_an_absolute_key :
  snd (Fs.migrate_image Fs.default_cwd [(rp [47;97], [])])
  = [(rp [47;97], Fs.MrAbsoluteKey)].
Proof. vm_compute. reflexivity. Qed.

Example migration_rejects_the_empty_key :
  snd (Fs.migrate_image Fs.default_cwd [(rp [], [])])
  = [(rp [], Fs.MrEmptyKey)].
Proof. vm_compute. reflexivity. Qed.

Example migration_rejects_an_empty_component :
  snd (Fs.migrate_image Fs.default_cwd [(rp [97;47;47;98], [])])
  = [(rp [97;47;47;98], Fs.MrEmptyComponent)].
Proof. vm_compute. reflexivity. Qed.

Example migration_rejects_a_dot_component :
  snd (Fs.migrate_image Fs.default_cwd [(rp [46], [])])
  = [(rp [46], Fs.MrDirRefComponent)].
Proof. vm_compute. reflexivity. Qed.

Example migration_rejects_a_dotdot_component :
  snd (Fs.migrate_image Fs.default_cwd [(rp [46;46], [])])
  = [(rp [46;46], Fs.MrDirRefComponent)].
Proof. vm_compute. reflexivity. Qed.

Example migration_rejects_a_nul_bearing_key :
  snd (Fs.migrate_image Fs.default_cwd [(rp [97;0;98], [])])
  = [(rp [97;0;98], Fs.MrUnnameableComponent)].
Proof. vm_compute. reflexivity. Qed.

(** A REJECTED KEY IS NOT IN THE IMAGE.  The report is not decoration:
    without this half, "rejected" and "silently dropped" would be the
    same thing to a reader. *)
Example a_rejected_key_is_absent :
  Fs.fs_lookup (fst (Fs.migrate_image Fs.default_cwd [(rp [46;46], [])]))
               (rp [47;119;111;114;107;47;46;46]) = None.
Proof. vm_compute. reflexivity. Qed.

(** THE FILE/PREFIX COLLISION: "a" beside "a/b".  The DIRECTORY WINS and
    the file is REPORTED, which is the decision the design note records
    (issue #1011, section 15, question 5). *)
Example migration_directory_wins_a_collision :
  Fs.fs_lookup (fst (Fs.migrate_image Fs.default_cwd
                       [(rp [97], [Z_to_bv 8 88]); (rp [97;47;98], [])]))
               (rp [47;119;111;114;107;47;97])
  = Some Fs.EDir.
Proof. vm_compute. reflexivity. Qed.

Example migration_reports_the_shadowed_file :
  snd (Fs.migrate_image Fs.default_cwd
         [(rp [97], [Z_to_bv 8 88]); (rp [97;47;98], [])])
  = [(rp [97], Fs.MrShadowedByDirectory)].
Proof. vm_compute. reflexivity. Qed.

(** ... and the file UNDER the collision survives, so the collision
    costs exactly the one entry the report names. *)
Example migration_keeps_the_file_under_a_collision :
  file_at (fst (Fs.migrate_image Fs.default_cwd
                  [(rp [97], [Z_to_bv 8 88]); (rp [97;47;98], [])]))
          (rp [47;119;111;114;107;47;97;47;98])
  = Some [].
Proof. vm_compute. reflexivity. Qed.

(** AN UNSORTED, DUPLICATED LEGACY LITERAL still migrates to a canonical
    image, and the LATER entry wins — the reading a fold can give, and
    the one the pre-namespace seeding gave. *)
Example migration_canonicalises_an_unsorted_literal :
  Fs.wf_fsb (fst (Fs.migrate_image Fs.default_cwd
                    [(rp [122], [Z_to_bv 8 1]); (rp [97], [Z_to_bv 8 2]);
                     (rp [122], [Z_to_bv 8 3])])) = true.
Proof. vm_compute. reflexivity. Qed.

Example migration_later_entry_wins :
  file_at (fst (Fs.migrate_image Fs.default_cwd
                  [(rp [122], [Z_to_bv 8 1]); (rp [122], [Z_to_bv 8 3])]))
          (rp [47;119;111;114;107;47;122])
  = Some [Z_to_bv 8 3].
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   PART 6 — what the arms read resolution through
   ========================================================================= *)

(** A PLAIN NAME IS ONE LOOKUP.  Every collaborator target opens its
    input by one, so this is the rewrite a harness proof does once.  The
    one side condition a link adds is that the name does not hold a link
    the walk would follow. *)
Example plain_name_resolves_by_one_lookup :
  Fs.resolve ns_md ns_image ns_cwd (rp [102])
  = (Fs.RFound (Fs.child_key ns_cwd (rp [102])) (Fs.EFile 1),
     Fs.LastNorm, false).
Proof.
  rewrite (Fs.resolve_plain_name ns_md ns_image ns_cwd (rp [102])).
  all: try (vm_compute; reflexivity).
  intros b Hb. vm_compute in Hb. discriminate Hb.
Qed.

(** ... AND THE SAME REWRITE HOLDS FROM /dev.  The lemma characterises
    every working directory, so a caller standing in /dev reads the
    missing name off the same equation. *)
Example plain_name_from_dev_is_one_lookup :
  Fs.resolve ns_md ns_image Fs.dev_dir (rp [122;101;114;111])
  = (Fs.RMissing Fs.dev_dir (rp [122;101;114;111]), Fs.LastNorm, false).
Proof.
  rewrite (Fs.resolve_plain_name ns_md ns_image Fs.dev_dir (rp [122;101;114;111])).
  all: try (vm_compute; reflexivity).
  intros b Hb. vm_compute in Hb. discriminate Hb.
Qed.

(** THE DEVICE LEMMAS the arms lane and [Common] consume: under the
    standard-root premise the two devices resolve deterministically,
    from ANY working directory. *)
Example devnull_resolves_from_any_cwd : forall cwd,
  Fs.resolve ns_md ns_image cwd Fs.devnull_key
  = (Fs.RFound Fs.devnull_key (Fs.EDev Fs.DevNull), Fs.LastNorm, false).
Proof.
  intros cwd. apply Fs.resolve_devnull; vm_compute; reflexivity.
Qed.

Example urandom_resolves_from_any_cwd : forall cwd,
  Fs.resolve ns_md ns_image cwd Fs.urandom_key
  = (Fs.RFound Fs.urandom_key (Fs.EDev Fs.DevUrandom), Fs.LastNorm, false).
Proof.
  intros cwd. apply Fs.resolve_urandom; vm_compute; reflexivity.
Qed.

(** A SET AT A KEY THE WALK NEVER LOOKS UP CHANGES NOTHING ([Fs.walk_runs_ext]
    is the frame a write proof uses: the rules read the image through
    [Fs.fs_lookup] alone) ... *)
Example a_write_elsewhere_does_not_move_a_path :
  Fs.resolve ns_md (Fs.fs_set ns_image (rp [47;119;111;114;107;47;122])
                      (Fs.EFile 2)) ns_cwd (rp [102])
  = Fs.resolve ns_md ns_image ns_cwd (rp [102]).
Proof. vm_compute. reflexivity. Qed.

(** ... and a set AT the key a path already resolves to gives the new
    entry back, with the same walk. *)
Example a_write_at_the_key_is_seen :
  Fs.resolve ns_md (Fs.fs_set ns_image (rp [47;119;111;114;107;47;102])
                      (Fs.EFile 2)) ns_cwd (rp [102])
  = (Fs.RFound (rp [47;119;111;114;107;47;102]) (Fs.EFile 2),
     Fs.LastNorm, false).
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   PART 7 — the timing pin
   ========================================================================= *)

(** RESOLUTION STAYS EXECUTABLE ON A HARNESS-SIZED IMAGE.  The harness's
    recorded images are hundreds of entries; this builds one of about
    five hundred and resolves a deep path in it under [vm_compute].  A
    regression that made the walk quadratic in the image, or that left a
    [nat] numeral to be built unary, shows up here as a check that does
    not finish rather than as a slow review.

    It is a TIMING pin and not a correctness pin, so what it asserts is
    only that the answer is the right one; the cost is in whether this
    file still compiles. *)
Definition big_name (n : nat) : Fs.path :=
  rp [47;119;111;114;107;47] ++ map (Z_to_bv 8) (repeat 97 n).

Definition big_image : Fs.Fs :=
  fold_left (fun acc n => Fs.fs_create_file acc (big_name n) [])
            (seq 1 500) ns_image.

Example big_image_is_well_formed : Fs.wf_fsb big_image = true.
Proof. vm_compute. reflexivity. Qed.

Example big_image_resolves_a_deep_path :
  fst (fst (Fs.resolve ns_md big_image ns_cwd
              (rp [46;46;47;119;111;114;107;47;100;47;46;46;47;102])))
  = Fs.RFound (rp [47;119;111;114;107;47;102]) (Fs.EFile 1).
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   PART 8 — the input, and the shared statpin
   ========================================================================= *)

(** A [Run.valid_input] WITNESS.  Without one, every agent theorem is
    vacuously true; this is the pin that says the file-system clauses
    ([Run.localtime_absent] among them), the credential clauses and the
    rest are jointly satisfiable. *)
(** [Cases.Prelude.demo_input] fixes argv to the EMPTY list, which
    [Run.valid_argv] refuses (a run has at least argv[0]), so the
    witness names the record directly and gives it one. *)
Definition ns_input : ProcInput :=
  mkProcInput_full [[]] [] ns_image Fs.default_cwd IEof
                   demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom default_kernel default_execfn
                   true true false.

(** [Run.valid_launch] of a launch whose exec file name is
    [State.default_execfn], the one-byte relative name "a" that
    [getname_flags] (fs/namei.c, Linux v6.18.46) can return, and whose
    strings are far under the E2BIG limit [bprm_stack_limits]
    (fs/exec.c) computes. *)
Ltac launch_ok :=
  unfold valid_launch; split;
  [ unfold valid_execfn, valid_path_name, default_execfn; left; split;
    [ cbn; lia
    | cbn; intros [Hz | []]; apply (f_equal bv_unsigned) in Hz;
      vm_compute in Hz; discriminate ]
  | unfold e2big_limit; apply Z.leb_le; vm_compute; reflexivity ].

Ltac argv_no_nul :=
  let H := fresh in
  intro H; cbn in H;
  repeat (destruct H as [H|H];
          [ now apply (f_equal bv_unsigned) in H; vm_compute in H | ]);
  exact H.

(** Every clause past the argument and environment lists, in
    [Run.valid_input]'s order, the same way for each witness below. *)
Ltac ns_valid_tail :=
  split; [ unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm |];
  split; [ unfold valid_creds; cbn; split; unfold valid_id; vm_compute; reflexivity |];
  split; [ unfold valid_nofile; vm_compute; intro; discriminate |];
  split; [ unfold valid_sigmask; cbn; apply bv_eq; vm_compute; reflexivity |];
  split; [ unfold valid_hwcap; left; reflexivity |];
  split; [ reflexivity |];
  split; [ reflexivity |];
  split; [ unfold valid_urandom; cbn [in_urandom]; apply default_urandom_infinite |];
  split; [ launch_ok |];
  split; [ reflexivity |];
  split; reflexivity.

Ltac ns_valid_envp :=
  unfold valid_envp; cbn [in_envp];
  split; [cbn; lia|];
  split; [vm_compute; intro; discriminate|];
  split; apply Forall_nil.

Example ns_input_is_valid : valid_input ns_input.
Proof.
  unfold valid_input, ns_input.
  cbn [in_argv in_envp in_fs in_cwd in_uid in_gid in_nofile in_sigmask
       in_hwcap in_abort_terminal in_va_size in_urandom in_execfn
       in_channel_reader in_sigpipe_terminal in_kernel].
  split; [| split; [ns_valid_envp | ns_valid_tail]].
  unfold valid_argv. cbn [tl].
  split; [cbn; lia|].
  split; [vm_compute; intro; discriminate|].
  split; [repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  split; [repeat apply Forall_cons; try apply Forall_nil; argv_no_nul|].
  apply Forall_nil.
Qed.

(** AN OPERAND OF [Fs.name_max] BYTES IS VALID, and so is one a byte
    longer: [Run.valid_argv] bounds no component.  The 255-byte name
    RESOLVES, to an ordinary [Fs.RMissing]
    ([walk_name_max_boundary_is_255] above); the 256-byte one resolves
    too, and every path-taking arm admits -ENAMETOOLONG beside its answer
    ([walk_name_max_boundary_is_not_256]), so a statement that opens an
    argv entry and claims one answer carries the bound as a hypothesis of
    its own ([Common.FileSim.resolve_argv_operand]). *)
Definition name_max_argv : list Fs.path :=
  [[]; rp (repeat 97 255)].

Definition name_max_input : ProcInput :=
  mkProcInput_full name_max_argv [] ns_image Fs.default_cwd IEof
                   demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom default_kernel default_execfn
                   true true false.

Example name_max_input_is_valid : valid_input name_max_input.
Proof.
  unfold valid_input, name_max_input, name_max_argv.
  cbn [in_argv in_envp in_fs in_cwd in_uid in_gid in_nofile in_sigmask
       in_hwcap in_abort_terminal in_va_size in_urandom in_execfn
       in_channel_reader in_sigpipe_terminal in_kernel].
  split; [| split; [ns_valid_envp | ns_valid_tail]].
  unfold valid_argv. cbn [tl].
  split; [cbn; lia|].
  split; [vm_compute; intro; discriminate|].
  split; [repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  split; [repeat apply Forall_cons; try apply Forall_nil; argv_no_nul|].
  repeat apply Forall_cons; try apply Forall_nil.
  split; vm_compute; reflexivity.
Qed.

(** The operand is within [Fs.name_max], stated on the witness. *)
Example name_max_input_bounds_its_operand :
  (length (nth 1 (in_argv name_max_input) []) <= Fs.name_max)%nat.
Proof.
  unfold name_max_input, name_max_argv, rp.
  cbn [in_argv nth].
  unfold Fs.name_max; rewrite length_map, repeat_length; lia.
Qed.

(** ...and one byte more is still a valid argv. *)
Example valid_argv_admits_a_256_byte_operand :
  valid_argv [[]; rp (repeat 97 256)].
Proof.
  unfold valid_argv. cbn [tl].
  split; [cbn; lia|].
  split; [vm_compute; intro; discriminate|].
  split; [repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  split; [repeat apply Forall_cons; try apply Forall_nil; argv_no_nul|].
  repeat apply Forall_cons; try apply Forall_nil.
  split; vm_compute; reflexivity.
Qed.

(** THE DIRECTORY-AT-THE-SOURCE BRANCH IS REACHABLE.  Both halves are
    pinned, because either alone would pass for the wrong reason: the
    RESOLUTION alone would hold for a model no valid input reaches, and
    the VALIDITY alone would not say the operand lands on a directory.

    The fixture's working directory is /work and its empty directory is
    /work/d, so the argv ["", "d", "f"] is an operand pair whose source
    resolves to a directory and whose destination is an ordinary file. *)
Definition dir_operand_argv : list Fs.path :=
  [[]; rp [100]; rp [102]].                             (* "", "d", "f" *)

Definition dir_operand_input : ProcInput :=
  mkProcInput_full dir_operand_argv [] ns_image Fs.default_cwd IEof
                   demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom default_kernel default_execfn
                   true true false.

Example dir_operand_input_is_valid : valid_input dir_operand_input.
Proof.
  unfold valid_input, dir_operand_input, dir_operand_argv.
  cbn [in_argv in_envp in_fs in_cwd in_uid in_gid in_nofile in_sigmask
       in_hwcap in_abort_terminal in_va_size in_urandom in_execfn
       in_channel_reader in_sigpipe_terminal in_kernel].
  split; [| split; [ns_valid_envp | ns_valid_tail]].
  unfold valid_argv. cbn [tl].
  split; [cbn; lia|].
  split; [vm_compute; intro; discriminate|].
  split; [repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  split; [repeat apply Forall_cons; try apply Forall_nil; argv_no_nul|].
  repeat apply Forall_cons; try apply Forall_nil;
    (split; vm_compute; reflexivity).
Qed.

(** ...and the source operand of that very input resolves to a DIRECTORY
    at the key the walk settles it on, with [Fs.LastNorm] for the last
    component's kind. *)
Example dir_operand_resolves_to_a_directory :
  Fs.resolve ns_md (in_fs dir_operand_input) (in_cwd dir_operand_input)
             (nth 1 (in_argv dir_operand_input) [])
  = (Fs.RFound (Fs.child_key (in_cwd dir_operand_input)
                  (nth 1 (in_argv dir_operand_input) [])) Fs.EDir,
     Fs.LastNorm, false).
Proof. vm_compute. reflexivity. Qed.

(** ...and its DESTINATION operand is an ordinary regular file. *)
Example dir_operand_destination_is_a_file :
  file_at (in_fs dir_operand_input)
    (Fs.child_key (in_cwd dir_operand_input)
       (nth 2 (in_argv dir_operand_input) []))
  = Some [Z_to_bv 8 65].
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   PART 8b — /proc and /sys at the root, and the working directory
   ========================================================================= *)

(** The walk answers [Fs.ROutside] for a first component
    "proc" or "sys" LOOKED UP AT THE ROOT, before any lookup, and every
    path-taking arm declines it ([Cases.Fs.Open.openat_proc_is_outside]).
    [Run.valid_input] admits a working directory of "/", so a relative
    "proc" from there reaches the decline; the pins below are the walk's
    side of that, and the image of the input that reaches it is valid. *)

(** ONE. At the root the operand is outside the modeled surface. *)
Example root_cwd_operand_is_outside :
  Fs.resolve ns_md ns_image Fs.root (rp [112;114;111;99])
  = (Fs.ROutside, Fs.LastNorm, false).
Proof. vm_compute. reflexivity. Qed.

Example root_cwd_sys_operand_is_outside :
  Fs.resolve ns_md ns_image Fs.root (rp [115;121;115])
  = (Fs.ROutside, Fs.LastNorm, false).
Proof. vm_compute. reflexivity. Qed.

(** TWO. One step down it is an ordinary missing name, which is what
    says the guard is a WALK-STATE test.  [not_outside_below_the_root]
    above is the same point with the name PRESENT. *)
Example proc_below_the_root_is_an_ordinary_name :
  Fs.resolve ns_md ns_image Fs.default_cwd (rp [112;114;111;99])
  = (Fs.RMissing Fs.default_cwd (rp [112;114;111;99]), Fs.LastNorm, false).
Proof. vm_compute. reflexivity. Qed.

(** THREE. The image of an input standing at the root is a valid image:
    the clauses of [Run.valid_image] about the working directory ask for
    a canonical key the image holds as a directory, short enough for
    [getcwd], and outside /proc and /sys ([Run.outside_proc_sysb]), and
    the root is all of these. *)
Definition root_cwd_input : ProcInput :=
  mkProcInput_full [[]; rp [112;114;111;99]] [] ns_image Fs.root IEof
                   demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom default_kernel default_execfn
                   true true false.

Example valid_image_admits_a_root_working_directory :
  valid_image root_cwd_input.
Proof. unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm. Qed.

(** ...and the same of a working directory of /dev, which is an
    ordinary folder of the image. *)
Definition dev_cwd_input : ProcInput :=
  mkProcInput_full [[]; rp [110;117;108;108]; rp [117;114;97;110;100;111;109]]
                   [] (Fs.standard_root Fs.default_cwd) Fs.dev_dir IEof
                   demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom default_kernel default_execfn
                   true true false.

Example valid_image_admits_a_dev_working_directory :
  valid_image dev_cwd_input.
Proof. unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm. Qed.

(** From /dev the operand "urandom" names the random device, which is
    the case [Common.FileSim.operand_is_not_a_device] excludes by its
    working-directory hypotheses; from the fixture's own working
    directory it does not. *)
Example the_device_key_needs_the_dev_working_directory :
  Fs.child_key Fs.dev_dir (rp [117;114;97;110;100;111;109]) = Fs.urandom_key
  /\ Fs.child_key Fs.default_cwd (rp [117;114;97;110;100;111;109])
     <> Fs.urandom_key.
Proof. split; vm_compute; [reflexivity | discriminate]. Qed.

Example the_dev_operand_resolves_to_the_random_device :
  Fs.resolve ns_md (Fs.standard_root Fs.default_cwd) Fs.dev_dir
             (rp [117;114;97;110;100;111;109])
  = (Fs.RFound Fs.urandom_key (Fs.EDev Fs.DevUrandom), Fs.LastNorm, false).
Proof. vm_compute. reflexivity. Qed.

(** FOUR. ...but NOT a working directory inside /proc or /sys
    ([Run.outside_proc_sysb]).  [Fs.ROutside] is a WALK-STATE test (TWO
    above), so a walk that starts in a folder /proc never meets it: from
    there "self" is an ordinary missing name of the image, where Linux,
    with procfs mounted at /proc, asks procfs ([proc_root_lookup],
    fs/proc/root.c:409-415, Linux v6.18.46) and finds the process's own
    folder.  The image below is the standard root with the folders /proc,
    /sys and /sys/kernel added. *)
Definition proc_sys_image : Fs.Fs :=
  Fs.fs_set (Fs.fs_set (Fs.fs_set (Fs.standard_root Fs.default_cwd)
                          (rp [47;112;114;111;99]) Fs.EDir)
               (rp [47;115;121;115]) Fs.EDir)
    (rp [47;115;121;115;47;107;101;114;110;101;108]) Fs.EDir.

Definition proc_cwd : Fs.path := rp [47;112;114;111;99].                (* /proc *)
Definition sys_kernel_cwd : Fs.path :=
  rp [47;115;121;115;47;107;101;114;110;101;108].                       (* /sys/kernel *)

Definition proc_sys_input (cwd : Fs.path) : ProcInput :=
  mkProcInput_full [[]] [] proc_sys_image cwd IEof
                   demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom default_kernel default_execfn
                   true true false.

(** The walk's side, which is why the clause is needed: from /proc,
    "self" is the image's own absence. *)
Example proc_cwd_walk_answers_from_the_image :
  Fs.resolve ns_md proc_sys_image proc_cwd (rp [115;101;108;102])
  = (Fs.RMissing proc_cwd (rp [115;101;108;102]), Fs.LastNorm, false).
Proof. vm_compute. reflexivity. Qed.

(** The same image at the ordinary working directory /work, and at the
    root, is a valid image: folders named /proc and /sys in the image are
    not what the clause refuses. *)
Example valid_image_admits_an_ordinary_cwd_beside_proc_and_sys :
  valid_image (proc_sys_input Fs.default_cwd)
  /\ valid_image (proc_sys_input Fs.root).
Proof. split; unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm. Qed.

(** The working directory /proc is not valid, and neither is /sys/kernel,
    below /sys. *)
Example valid_image_refuses_a_proc_cwd :
  ~ valid_image (proc_sys_input proc_cwd).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hout & _).
  vm_compute in Hout. discriminate.
Qed.

Example valid_image_refuses_a_sys_kernel_cwd :
  ~ valid_image (proc_sys_input sys_kernel_cwd).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hout & _).
  vm_compute in Hout. discriminate.
Qed.

(** ...and the working-directory clause is the only one they fail
    (it was the last clause until the size clause followed it): each is a
    canonical key the image holds as a directory, short enough for
    [getcwd].  The clause is decided COMPONENT BY COMPONENT: /sys itself
    fails it, and "/procs", "/system" and "/work/proc" pass. *)
Example proc_and_sys_cwds_fail_only_the_last_clause :
  Fs.canonical_key proc_cwd = true
  /\ Fs.fs_lookup proc_sys_image proc_cwd = Some Fs.EDir
  /\ Nat.leb (length proc_cwd + 1)%nat path_max = true
  /\ outside_proc_sysb proc_cwd = false
  /\ Fs.canonical_key sys_kernel_cwd = true
  /\ Fs.fs_lookup proc_sys_image sys_kernel_cwd = Some Fs.EDir
  /\ Nat.leb (length sys_kernel_cwd + 1)%nat path_max = true
  /\ outside_proc_sysb sys_kernel_cwd = false
  /\ outside_proc_sysb (rp [47;115;121;115]) = false
  /\ outside_proc_sysb (rp [47;112;114;111;99;115]) = true
  /\ outside_proc_sysb (rp [47;115;121;115;116;101;109]) = true
  /\ outside_proc_sysb (rp [47;119;111;114;107;47;112;114;111;99]) = true.
Proof. split_conj; vm_compute; reflexivity. Qed.

(** EVERY DEVICE THE IMAGE DECLARES IS INSIDE THE /dev SUBTREE
    ([Run.devices_in_dev_subtree]).  Nothing in [Fs.wf_fs] decides any
    of the four cases below -- it asks for sorted, canonical keys, a
    directory at the root and at every key's parent, and says nothing
    about where a device may sit -- which is why the clause is needed:
    the standard root passes, a device at an ORDINARY key fails, a
    device DEEPER in the subtree passes, and a device under a LOOKALIKE
    directory fails. *)
Example devices_in_dev_subtree_standard_root :
  devices_in_dev_subtreeb (Fs.standard_root Fs.default_cwd) = true.
Proof. vm_compute. reflexivity. Qed.

Example devices_in_dev_subtree_refuses_a_device_at_an_ordinary_key :
  devices_in_dev_subtreeb
    (Fs.fs_set (Fs.standard_root Fs.default_cwd)
       (rp [47;119;111;114;107;47;111;117;116]) (Fs.EDev Fs.DevUrandom))
  = false.
Proof. vm_compute. reflexivity. Qed.

Example devices_in_dev_subtree_admits_a_deeper_device :
  devices_in_dev_subtreeb
    (Fs.fs_set (Fs.fs_set (Fs.standard_root Fs.default_cwd)
                  (rp [47;100;101;118;47;112;116;115]) Fs.EDir)
       (rp [47;100;101;118;47;112;116;115;47;48]) (Fs.EDev Fs.DevNull))
  = true.
Proof. vm_compute. reflexivity. Qed.

Example devices_in_dev_subtree_refuses_a_lookalike :
  devices_in_dev_subtreeb
    (Fs.fs_set (Fs.fs_set (Fs.standard_root Fs.default_cwd)
                  (rp [47;100;101;118;105;99;101]) Fs.EDir)
       (rp [47;100;101;118;105;99;101;47;110]) (Fs.EDev Fs.DevNull))
  = false.
Proof. vm_compute. reflexivity. Qed.

(** FIVE. EVERY FOLDER ROW HOLDS COUNTS A KERNEL GIVES ([Fs.dir_rows_okb],
    the last clause of [Run.valid_image]).  The image below is the
    standard root with an empty folder /work/d, and [dir_row_image r]
    gives it the folder rows [r].  On tmpfs and ramfs an empty folder
    has the count 2 ([inode_init_always_gfp], fs/inode.c:242, then
    [inc_nlink] in [__shmem_get_inode], mm/shmem.c:3133-3134, Linux
    v6.18.46), and [generic_fillattr] reports it (fs/stat.c:91, Linux
    v6.18.46). *)
Definition work_d : Fs.path := rp [47;119;111;114;107;47;100].          (* /work/d *)

Definition dir_row_image (r : list (Fs.path * Fs.DirLinks)) : Fs.Fs :=
  Fs.fs_with_dirs (Fs.fs_set (Fs.standard_root Fs.default_cwd) work_d Fs.EDir) r.

Definition dir_row_input (r : list (Fs.path * Fs.DirLinks)) : ProcInput :=
  mkProcInput_full [[]] [] (dir_row_image r) Fs.default_cwd IEof
                   demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom default_kernel default_execfn
                   true true false.

(** The row [(/work/d, 0, 0)] is refused, and it is all that is wrong:
    the same image with no row is valid.  Before the clause the input
    was valid, and [stat] of /work/d answered an [st_nlink] of 0, which
    no kernel gives a folder. *)
Example valid_image_refuses_a_folder_row_below_the_tree :
  ~ valid_image (dir_row_input [(work_d, Fs.mkDirLinks 0 0)]).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrows).
  vm_compute in Hrows. discriminate.
Qed.

Example valid_image_admits_the_folder_without_a_row :
  valid_image (dir_row_input []).
Proof. unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm. Qed.

(** A ROW ABOVE THE TREE'S COUNT BELOW THE ROOT IS REFUSED.  /work/d is
    empty in the tree, and the image holds every name of a folder below
    the root and outside /proc and /sys, so its count is 2.  With the
    row 3, [newfstatat] of /work/d answered an [st_nlink] of 3, a count
    with a subfolder in it, and [unlinkat(AT_FDCWD, "/work/d",
    AT_REMOVEDIR)] then removed the folder, since
    [Sys.Fs.Namei.rmdir_spec] asks the tree alone; Linux answers
    -ENOTEMPTY for a folder with a subfolder ([simple_empty],
    fs/libfs.c:766-784, from [simple_rmdir] at fs/libfs.c:799-807 and
    [shmem_rmdir] at mm/shmem.c:4032-4035, Linux v6.18.46).  The row at
    the tree's own count stays valid. *)
Example valid_image_refuses_a_folder_row_above_the_tree_below_the_root :
  ~ valid_image (dir_row_input [(work_d, Fs.mkDirLinks 3 1)]).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrows).
  vm_compute in Hrows. discriminate.
Qed.

Example valid_image_admits_a_folder_row_at_the_tree :
  valid_image (dir_row_input [(work_d, Fs.mkDirLinks 2 1)]).
Proof. unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm. Qed.

(** ...and so NO VALID IMAGE has a folder below the root and outside
    /proc and /sys whose count is above its tree's: a [stat] that counts
    a subfolder the tree does not show, followed by an [rmdir] that finds
    the folder empty, starts from no launch. *)
Example valid_image_no_folder_below_the_root_counts_above_its_tree : forall inp k,
  valid_image inp -> k <> Fs.root -> Fs.in_proc_sys_subtree k = false ->
  ~ (2 + Fs.fs_nsubdirs (in_fs inp) k < Fs.dl_counting (Fs.fs_dir_links (in_fs inp) k))%nat.
Proof.
  intros inp k Hv Hk Hp Hlt.
  destruct (valid_image_dir_links inp k Hv) as [_ [Heq _]].
  rewrite (Heq Hp), (Fs.fs_tree_count_below _ _ Hk) in Hlt. exact (Nat.lt_irrefl _ Hlt).
Qed.

(** THE ROOT'S COUNT IS THE TREE'S PLUS /proc AND /sys.  The tree implies
    5 for the root (two, and /dev, /tmp and /work), and the root's count
    also counts /proc and /sys: folders of the root file system, not
    symbolic links, by two launch premises ([Fs.root_unheld_dirs]; the
    kernel does not make them so, since [do_mount] follows a link at the
    mount point, fs/namespace.c:4048, Linux v6.18.46), which this image
    does not hold.  So its row must say 7, as a kernel gives ([ramfs_mkdir],
    fs/ramfs/inode.c:122-127, and [shmem_mkdir], mm/shmem.c:3952, raise
    the root's count once for each; [generic_fillattr] reports it,
    fs/stat.c:91, Linux v6.18.46). *)
Example valid_image_admits_a_root_row_above_the_tree :
  valid_image (dir_row_input [(Fs.root, Fs.mkDirLinks 7 1)]).
Proof. unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm. Qed.

(** ...and a root row above that is refused: with the row 8,
    [newfstatat(AT_FDCWD, "/")] answered an [st_nlink] of 8, where a root
    holding /dev, /tmp, /work, /proc and /sys counts 7.  The row passed
    before the root's count had an upper bound. *)
Example valid_image_refuses_a_root_row_above_proc_and_sys :
  ~ valid_image (dir_row_input [(Fs.root, Fs.mkDirLinks 8 1)]).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrows).
  vm_compute in Hrows. discriminate.
Qed.

(** ...and so is a root row of the tree's count alone: with the row 5,
    [newfstatat] of "/" answered 5, a root without the /proc folder that
    procfs is mounted on.  The row passed before the root's count counted
    /proc and /sys. *)
Example valid_image_refuses_a_root_row_without_proc_and_sys :
  ~ valid_image (dir_row_input [(Fs.root, Fs.mkDirLinks 5 1)]).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrows).
  vm_compute in Hrows. discriminate.
Qed.

(** WITH NO ROW THE ROOT HAS THE SAME COUNT: the standard root (/dev,
    /tmp, /work) gives 7, not the tree's 5.  A tree that holds /proc and
    /sys as folders counts them as subfolders and adds nothing more:
    [proc_sys_image] holds /dev, /proc, /sys, /tmp and /work, so its
    root counts 7 and a root row there may say 7 and not 8.  A file or a
    link at /proc is not a folder of the tree: an image that holds one
    contradicts the launch premise, and the root counts the folder /proc
    all the same. *)
Example the_root_counts_proc_and_sys_once :
  Fs.fs_dir_links (Fs.standard_root Fs.default_cwd) Fs.root = Fs.mkDirLinks 7 1
  /\ Fs.fs_nsubdirs (Fs.standard_root Fs.default_cwd) Fs.root = 3%nat
  /\ Fs.root_unheld_dirs (Fs.standard_root Fs.default_cwd) = 2%nat
  /\ Fs.fs_dir_links proc_sys_image Fs.root = Fs.mkDirLinks 7 1
  /\ Fs.fs_nsubdirs proc_sys_image Fs.root = 5%nat
  /\ Fs.root_unheld_dirs proc_sys_image = 0%nat
  /\ Fs.dir_rows_okb (Fs.fs_with_dirs proc_sys_image [(Fs.root, Fs.mkDirLinks 7 1)]) = true
  /\ Fs.dir_rows_okb (Fs.fs_with_dirs proc_sys_image [(Fs.root, Fs.mkDirLinks 8 1)]) = false
  /\ Fs.fs_dir_links (Fs.fs_set (Fs.standard_root Fs.default_cwd) Fs.proc_key
                        (Fs.ELink (rp [119;111;114;107])))
       Fs.root
     = Fs.mkDirLinks 7 1.
Proof. split_conj; vm_compute; reflexivity. Qed.

(** ...and so IN EVERY VALID IMAGE the root's count is two, plus one per
    subfolder the tree shows, plus one for each of /proc and /sys that
    the tree does not hold as a folder: a [stat] of "/" answers the count
    a kernel gives the launch, a row or none. *)
Example valid_image_root_counts_its_tree_and_proc_and_sys : forall inp,
  valid_image inp ->
  Fs.dl_counting (Fs.fs_dir_links (in_fs inp) Fs.root)
  = (2 + Fs.fs_nsubdirs (in_fs inp) Fs.root + Fs.root_unheld_dirs (in_fs inp))%nat.
Proof.
  intros inp Hv.
  destruct (valid_image_dir_links inp Fs.root Hv) as [_ [Heq _]].
  rewrite (Heq ltac:(vm_compute; reflexivity)). apply Fs.fs_tree_count_root.
Qed.

(** A ROW AT /proc, OR BELOW /sys, ABOVE THE TREE'S COUNT STAYS VALID:
    procfs and sysfs count folders of their own that an image need not
    hold, and no walk reaches such a row ([Fs.at_outside]).
    [proc_sys_image] holds /proc, /sys and /sys/kernel and no folder
    under /proc or /sys/kernel, so the tree implies 2 for both; the rows
    say 9 and 4, and the same rows at /work/d would be refused. *)
Definition proc_sys_row_input (r : list (Fs.path * Fs.DirLinks)) : ProcInput :=
  mkProcInput_full [[]] [] (Fs.fs_with_dirs proc_sys_image r) Fs.default_cwd IEof
                   demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom default_kernel default_execfn
                   true true false.

Example valid_image_admits_proc_and_sys_rows_above_the_tree :
  valid_image (proc_sys_row_input [(proc_cwd, Fs.mkDirLinks 9 1);
                                   (sys_kernel_cwd, Fs.mkDirLinks 4 1)]).
Proof. unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm. Qed.

(** The clause row by row: below the root and outside /proc and /sys the
    tree's own count passes with a fixed count of 1 and a count above it
    fails; a count one below the tree's, a fixed count other than 1, and
    a row at a key that is no folder fail.  With no row, /work/d has the
    counts 2 and 1 and the root 7 and 1 (/dev, /tmp and /work, and
    /proc and /sys). *)
Example dir_rows_okb_decides_each_row :
  Fs.dir_rows_okb (dir_row_image [(work_d, Fs.mkDirLinks 2 1)]) = true
  /\ Fs.dir_rows_okb (dir_row_image [(work_d, Fs.mkDirLinks 9 1)]) = false
  /\ Fs.dir_rows_okb (dir_row_image [(work_d, Fs.mkDirLinks 1 1)]) = false
  /\ Fs.dir_rows_okb (dir_row_image [(work_d, Fs.mkDirLinks 2 2)]) = false
  /\ Fs.dir_rows_okb (dir_row_image [(work_d, Fs.mkDirLinks 2 0)]) = false
  /\ Fs.dir_rows_okb (dir_row_image [(Fs.root, Fs.mkDirLinks 4 1)]) = false
  /\ Fs.dir_rows_okb (dir_row_image [(rp [47;119;111;114;107;47;101], Fs.mkDirLinks 2 1)])
     = false
  /\ Fs.fs_dir_links (dir_row_image []) work_d = Fs.mkDirLinks 2 1
  /\ Fs.fs_dir_links (dir_row_image []) Fs.root = Fs.mkDirLinks 7 1.
Proof. split_conj; vm_compute; reflexivity. Qed.

(* =========================================================================
   PART 8c — a device at an ordinary key
   ========================================================================= *)

(** THE INPUT THE DEVICE CLAUSE REFUSES.  The random device at an
    ORDINARY key, under an ordinary working directory: [Fs.wf_fs] admits
    the image and [Fs.standard_root_present] admits it too, and an
    operand naming that key would reach a device through a file's name.
    [Run.devices_in_dev_subtree] is what refuses it. *)
Definition dev_anywhere_fs : Fs.Fs :=
  Fs.fs_set (Fs.fs_create_file (Fs.standard_root Fs.default_cwd)
               (rp [47;119;111;114;107;47;105;110]) [Z_to_bv 8 65])
            (rp [47;119;111;114;107;47;111;117;116]) (Fs.EDev Fs.DevUrandom).

Definition dev_anywhere_input : ProcInput :=
  mkProcInput_full [[]; rp [105;110]; rp [111;117;116]] []
                   dev_anywhere_fs Fs.default_cwd IEof
                   demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom default_kernel default_execfn
                   true true false.

Example the_image_is_well_formed_and_standard :
  Fs.wf_fsb dev_anywhere_fs = true
  /\ Fs.standard_root_presentb dev_anywhere_fs = true.
Proof. split; vm_compute; reflexivity. Qed.

Example dev_anywhere_input_is_refused : ~ valid_input dev_anywhere_input.
Proof.
  intros (_ & _ & (_ & _ & _ & Hdev & _) & _).
  vm_compute in Hdev. discriminate.
Qed.

(** ...and what it would have reached: the destination operand resolves
    to the device. *)
Example the_ordinary_destination_would_resolve_to_the_device :
  Fs.resolve ns_md dev_anywhere_fs Fs.default_cwd (rp [111;117;116])
  = (Fs.RFound (rp [47;119;111;114;107;47;111;117;116])
               (Fs.EDev Fs.DevUrandom), Fs.LastNorm, false).
Proof. vm_compute. reflexivity. Qed.

(** THE WORKING DIRECTORY REACHES THE MODEL and is the key a relative
    pathname resolves against. *)
Example the_model_carries_the_declared_cwd :
  m_cwd (init_model [] 0 0 0 0 ns_input) = Fs.default_cwd.
Proof. reflexivity. Qed.

(** THE STATPIN IS KEYED BY THE INODE THE NAME HOLDS, so three spellings
    of one file share one pinned identity rather than three.  The pin is
    the equality of the entries the three spellings resolve to. *)
Example three_spellings_share_one_statpin_key :
  ns [102] = ns [46;47;102]
  /\ ns [102] = ns [47;119;111;114;107;47;102]
  /\ ns [102] = ns [100;47;46;46;47;102].
Proof. repeat split; vm_compute; reflexivity. Qed.

(* =========================================================================
   PART 9 — what a writer has to show, and what RMissing delivers
   ========================================================================= *)

(** THE CONTENT WRITERS keep the image well formed: rewriting a file's
    bytes changes its inode's row and nothing in the name tree.  The
    writers that use it ([write], [pwrite], the three [writev] arms,
    both truncates) only ever write the inode a descriptor holds
    ([Fs.fs_set_ino_data]). *)
Example replace_keeps_wf :
  Fs.wf_fsb (Fs.fs_set_ino_data ns_image 1 [Z_to_bv 8 66; Z_to_bv 8 67]) = true.
Proof. vm_compute. reflexivity. Qed.

(** UNLINK of a file keeps it well formed; of a DIRECTORY with a child
    it would not, which is why [Fs.wf_fs_remove_file] asks for a
    non-directory and why [rmdir]'s emptiness test is not decoration. *)
Example remove_file_keeps_wf :
  Fs.wf_fsb (Fs.fs_remove ns_image (rp [47;119;111;114;107;47;102])) = true.
Proof. vm_compute. reflexivity. Qed.

Example remove_a_directory_with_a_child_breaks_wf :
  Fs.wf_fsb (Fs.fs_remove ns_image Fs.default_cwd) = false.
Proof. vm_compute. reflexivity. Qed.

(** CREATING AT A MISSING KEY keeps it well formed, and the same
    pathname then resolves to what was created.  Both halves by
    computation, on the pathname the [RMissing] pin above names. *)
Example create_at_a_missing_key_keeps_wf :
  Fs.wf_fsb (Fs.fs_create_file ns_image (Fs.child_key Fs.default_cwd (rp [122]))
               [Z_to_bv 8 88]) = true.
Proof. vm_compute. reflexivity. Qed.

Example create_at_a_missing_key_is_then_found :
  fst (fst (Fs.resolve ns_md
              (Fs.fs_create_file ns_image (Fs.child_key Fs.default_cwd (rp [122]))
                 [Z_to_bv 8 88])
              ns_cwd (rp [122])))
  = Fs.RFound (rp [47;119;111;114;107;47;122]) (Fs.EFile 2).
Proof. vm_compute. reflexivity. Qed.

(** ... and the two together are what [Fs.resolve_missing_create]
    states over an arbitrary image and entry, off nothing but the
    [RMissing] the create walk returned; the entry here is the one the
    create writes, the name of the fresh inode 2. *)
Example missing_create_lemma_applies :
  Fs.wf_fs (Fs.fs_set ns_image
              (Fs.child_key Fs.default_cwd (rp [122])) (Fs.EFile 2))
  /\ Fs.resolve (Fs.WalkCreate true)
       (Fs.fs_set ns_image (Fs.child_key Fs.default_cwd (rp [122])) (Fs.EFile 2))
       ns_cwd (rp [122])
     = (Fs.RFound (Fs.child_key Fs.default_cwd (rp [122]))
                  (Fs.EFile 2), Fs.LastNorm, false).
Proof.
  apply (Fs.resolve_missing_create true ns_image ns_cwd (rp [122])
           Fs.default_cwd (rp [122]) Fs.LastNorm false).
  - apply Fs.wf_fsb_iff. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(** WHAT THE CREATE ARM READS OFF AN [RMissing], on the same pathname,
    named rather than counted: the parent is a CANONICAL KEY, the name
    is NAMEABLE, the child key is CANONICAL too, its PARENT is the
    parent the walk returned, the parent is a DIRECTORY in the image,
    and the child key is ABSENT from it.  The last two are what make
    the create keep the image well formed; the first four are what make
    the key it creates at a key at all. *)
Example missing_parent_facts :
  Fs.canonical_key Fs.default_cwd = true
  /\ Fs.comp_ok (rp [122]) = true
  /\ Fs.canonical_key (Fs.child_key Fs.default_cwd (rp [122])) = true
  /\ Fs.path_parent (Fs.child_key Fs.default_cwd (rp [122])) = Fs.default_cwd
  /\ Fs.fs_lookup ns_image Fs.default_cwd = Some Fs.EDir
  /\ Fs.fs_lookup ns_image (Fs.child_key Fs.default_cwd (rp [122])) = None.
Proof.
  apply (Fs.resolve_missing_parent ns_md ns_image ns_cwd (rp [122])
           Fs.default_cwd (rp [122]) Fs.LastNorm false);
    vm_compute; reflexivity.
Qed.

(* =========================================================================
   PART 10 — /tmp, /proc/self/fd/N and /etc/localtime on the image
   ========================================================================= *)

Close Scope Z_scope.

(** A path's bytes and its NUL at 8192, for the [check_syscall] pins
    below. *)
Definition at_8192 (p : list Z) : word -> option byte :=
  bytes_at (Z_to_bv 64 8192) (rp p ++ [Z_to_bv 8 0]).

(** /tmp IS KEYS OF THE IMAGE.  An input whose image holds "/tmp/a"
    reads it by [openat("/tmp/a")]: the walk reaches the folder /tmp and
    finds the file there, and the descriptor names that key. *)
Definition tmp_a_key : Fs.path := rp [47;116;109;112;47;97]%Z.

Definition tmp_a_model : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (Fs.fs_create_file (demo_fs []) tmp_a_key [Z_to_bv 8 104]) IEof).

Example tmp_is_image_keys :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0] (at_8192 [47;116;109;112;47;97]%Z)
       (fun _ => None))
    (with_copyins [(8192, 7%nat)] (mkEffect 3 [] []))
    tmp_a_model
  = CheckOk (with_fds (fd_insert (m_fds tmp_a_model) 3
                         (FdFile 1 (Z_to_bv 64 0))) tmp_a_model) []
  (* and an -ENOENT for the key the image holds is refused *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0] (at_8192 [47;116;109;112;47;97]%Z)
          (fun _ => None))
       (with_copyins [(8192, 7%nat)] (mkEffect (errno_ret ENOENT) [] []))
       tmp_a_model
     = CheckReject.
Proof. split; check_eq. Qed.

(** "/proc/self/fd/N" IS READ AHEAD OF THE WALK.  "proc" looked up at
    the root is [Fs.ROutside], which every arm declines; the
    [Sys.Fs.Open.proc_self_fd] test runs on the raw pathname first, so
    "/proc/self/fd/3" on a file unlinked while open reopens it, while
    "/proc/self/x", which is not that shape, reaches the walk and
    declines. *)
Definition procfd_m0 : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof).

Definition procfd_model : Model :=
  with_fds (fd_insert (m_fds procfd_m0) 3 (FdFile 1 (Z_to_bv 64 0)))
    (with_fs (Fs.fs_unlink_file
                (Fs.fs_create_file (m_fs procfd_m0) tmp_a_key [Z_to_bv 8 104])
                tmp_a_key 1 true)
       procfd_m0).

Example proc_self_fd_beats_routside :
  match check_syscall
          (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
             (at_8192 [47;112;114;111;99;47;115;101;108;102;47;102;100;47;51]%Z)
             (fun _ => None))
          (with_copyins [(8192, 16%nat)] (mkEffect 4 [] []))
          procfd_model with
  | CheckOk _ _ => True
  | _ => False
  end
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (at_8192 [47;112;114;111;99;47;115;101;108;102;47;120]%Z)
          (fun _ => None))
       (with_copyins [(8192, 13%nat)] (mkEffect (errno_ret ENOENT) [] []))
       procfd_model
     = CheckUnmodeled.
Proof. split; [vm_compute; exact I | check_eq]. Qed.

(** /proc AND /sys AT THE ROOT ARE DECLINED BY THE ARM, whatever the
    answer offered: the walk's [Fs.ROutside], read through [openat]. *)
Example proc_and_sys_at_the_root_are_unmodeled :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0] (at_8192 [47;112;114;111;99]%Z)
       (fun _ => None))
    (with_copyins [(8192, 6%nat)] (mkEffect (errno_ret ENOENT) [] []))
    procfd_m0
  = CheckUnmodeled
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0] (at_8192 [47;115;121;115]%Z)
          (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect 3 [] []))
       procfd_m0
     = CheckUnmodeled
  (* the same name below the root is an ordinary missing name *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0] (at_8192 [112;114;111;99]%Z)
          (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOENT) [] []))
       procfd_m0
     = CheckOk procfd_m0 [].
Proof. split_conj; check_eq. Qed.

(** THE /etc/localtime CLAUSE, [Run.localtime_absent].  The standard
    root holds no /etc, so the walk of /etc/localtime ends in
    [Fs.RAbsent] and the clause holds; an image with a folder /etc and
    no localtime in it holds it too ([Fs.RMissing]).  An image with a
    FILE at /etc/localtime fails it, and so does one with a FILE at
    /etc, where the walk answers [Fs.RNotDir]: both are well formed, so
    the clause is what refuses them. *)
Definition etc_key : Fs.path := rp [47;101;116;99]%Z.

Definition localtime_file_image : Fs.Fs :=
  Fs.fs_create_file (Fs.fs_set (demo_fs []) etc_key Fs.EDir)
    localtime_path [Z_to_bv 8 84].

Definition etc_file_image : Fs.Fs :=
  Fs.fs_create_file (demo_fs []) etc_key [Z_to_bv 8 84].

Example localtime_absent_holds_on_the_standard_root :
  localtime_absentb (demo_fs []) = true
  /\ localtime_absentb (Fs.fs_set (demo_fs []) etc_key Fs.EDir) = true.
Proof. split; vm_compute; reflexivity. Qed.

Example localtime_file_image_not_valid :
  Fs.wf_fsb localtime_file_image = true
  /\ localtime_absentb localtime_file_image = false
  /\ Fs.wf_fsb etc_file_image = true
  /\ localtime_absentb etc_file_image = false.
Proof. split_conj; vm_compute; reflexivity. Qed.

(** ...and the inputs built on them are not valid: a FILE at
    /etc/localtime, and a FILE at /etc. *)
Example localtime_file_input_not_valid :
  ~ valid_image (demo_input localtime_file_image IEof).
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hlt & _).
  unfold localtime_absent in Hlt. vm_compute in Hlt. discriminate.
Qed.

Example etc_file_input_not_valid :
  ~ valid_image (demo_input etc_file_image IEof).
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hlt & _).
  unfold localtime_absent in Hlt. vm_compute in Hlt. discriminate.
Qed.

(** A DANGLING LINK AT /etc/localtime IS INSIDE THE CLAUSE: the walk
    follows it ([lookup_last]'s LOOKUP_FOLLOW, fs/namei.c:2647-2652) and
    ends where its body names nothing, so the clause holds and the input
    is valid; an open of it is -ENOENT, with -ELOOP beside it because a
    link was followed ([pick_link], :1927-1929).  A link to a FILE there
    is outside the clause, as the file itself is. *)
Definition localtime_link_image (body : list Z) : Fs.Fs :=
  Fs.fs_set (Fs.fs_set (demo_fs []) etc_key Fs.EDir) localtime_path
    (Fs.ELink (rp body)).

(* "/usr/share/zoneinfo/UTC", which the image does not hold *)
Definition zoneinfo_utc : list Z :=
  [47;117;115;114;47;115;104;97;114;101;47;122;111;110;101;105;110;102;111;
   47;85;84;67]%Z.

Example a_dangling_localtime_link_is_inside_the_clause :
  localtime_absentb (localtime_link_image zoneinfo_utc) = true
  /\ valid_image (demo_input (localtime_link_image zoneinfo_utc) IEof)
  (* a link at /etc/localtime to a file is outside it *)
  /\ localtime_absentb
       (Fs.fs_create_file (localtime_link_image [47;101;116;99;47;122]%Z)
          (rp [47;101;116;99;47;122]%Z) [Z_to_bv 8 84]) = false.
Proof.
  split; [vm_compute; reflexivity|].
  split; [unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm|].
  vm_compute. reflexivity.
Qed.

Example a_dangling_localtime_link_opens_to_enoent :
  let m := init_model [] 0 0 demo_sp demo_limit
             (demo_input (localtime_link_image zoneinfo_utc) IEof) in
  let open eff := check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (at_8192 [47;101;116;99;47;108;111;99;97;108;116;105;109;101]%Z)
       (fun _ => None))
    (with_copyins [(8192, 15%nat)] eff) m in
  open (mkEffect (errno_ret ENOENT) [] []) = CheckOk m []
  /\ open (mkEffect (errno_ret ELOOP) [] []) = CheckOk m []
  /\ open (mkEffect 3 [] []) = CheckReject.
Proof. split_conj; check_eq. Qed.

(* =========================================================================
   PART 11 — symbolic links in the walk

   Linux v6.18.46, fs/namei.c.  A link that is not the last component is
   always followed and the last one is followed under LOOKUP_FOLLOW
   ([step_into], :1994-2021); [pick_link] (:1904-1975) counts the follow
   ([reserve_stack] :1878-1879, with MAXSYMLINKS 40 at
   include/linux/namei.h:13), walks an absolute body from the root
   ([nd_jump_root], :1962-1967) and a relative one from the folder
   holding the link, and an empty body leaves the walk on that folder
   (:1957-1958, :1969-1973).  ".." is the parent of the dentry the walk
   stands on ([follow_dotdot] :2064-2094, [dget_parent] :2083), so after
   a link it is the TARGET's parent; at the root it stays (:2068-2069).
   ========================================================================= *)

Open Scope Z_scope.

(** THE LINK FIXTURE, over [ns_image]:

        /work/d/g    a second file, inode 2
        /work/l   -> "f"          a relative link to a file
        /work/ld  -> "d"          a link to a folder
        /work/le  -> ""           an empty body
        /work/lt  -> "/tmp"       an absolute link to a folder
        /work/ln  -> "f\0g"       a body with a NUL in it
        /work/lp  -> "/proc"      a link that leads outside the image
        /work/dang -> "new"       a link to nothing
        /work/o   -> "o"          a link to itself *)
Definition ln_image : Fs.Fs :=
  fold_left (fun fs kb => Fs.fs_set fs (Fs.child_key ns_cwd (rp (fst kb)))
                              (Fs.ELink (rp (snd kb))))
    [([108], [102]); ([108;100], [100]); ([108;101], []);
     ([108;116], [47;116;109;112]); ([108;110], [102;0;103]);
     ([108;112], [47;112;114;111;99]); ([100;97;110;103], [110;101;119]);
     ([111], [111])]
    (Fs.fs_create_file ns_image (rp [47;119;111;114;107;47;100;47;103])
       [Z_to_bv 8 66]).

Example wf_ln_image : Fs.wf_fsb ln_image = true.
Proof. vm_compute. reflexivity. Qed.

(** The outcome and the follow flag of a walk over the fixture. *)
Definition ln (md : Fs.WalkMode) (p : list Z) : Fs.Resolved :=
  fst (fst (Fs.resolve md ln_image ns_cwd (rp p))).
Definition ln_followed (p : list Z) : bool :=
  Fs.wr_followed (Fs.resolve_res ns_md ln_image ns_cwd (rp p)).

(** A LINK ON THE PATH RESOLVES TO WHAT IT NAMES: "l" to the file, and
    the walk records that it followed one; unfollowed, "l" is the link
    itself.  A body is read to its first NUL ([vfs_readlink]'s
    [strlen], fs/namei.c:5469), so "ln" names "f" too.  A plain file
    follows nothing. *)
Example link_on_the_path_resolves_to_a_file :
  ln ns_md [108] = Fs.RFound (rp [47;119;111;114;107;47;102]) (Fs.EFile 1)
  /\ ln_followed [108] = true
  /\ ln (Fs.WalkFull false false) [108]
     = Fs.RFound (rp [47;119;111;114;107;47;108]) (Fs.ELink (rp [102]))
  /\ ln ns_md [108;110] = Fs.RFound (rp [47;119;111;114;107;47;102]) (Fs.EFile 1)
  /\ ln_followed [102] = false.
Proof. split_conj; vm_compute; reflexivity. Qed.

(** A LINK TO A FOLDER IN THE MIDDLE is walked through, followed even
    when the last component is not ([WALK_MORE], :2516). *)
Example link_to_a_folder_in_the_middle :
  ln ns_md [108;100;47;103] = Fs.RFound (rp [47;119;111;114;107;47;100;47;103]) (Fs.EFile 2)
  /\ ln (Fs.WalkFull false false) [108;100;47;103]
     = Fs.RFound (rp [47;119;111;114;107;47;100;47;103]) (Fs.EFile 2).
Proof. split; vm_compute; reflexivity. Qed.

(** AN EMPTY BODY LEAVES THE WALK ON THE FOLDER HOLDING THE LINK. *)
Example empty_body_link_is_the_folder_holding_it :
  ln ns_md [108;101] = Fs.RFound Fs.default_cwd Fs.EDir
  /\ ln ns_md [108;101;47;102] = Fs.RFound (rp [47;119;111;114;107;47;102]) (Fs.EFile 1).
Proof. split; vm_compute; reflexivity. Qed.

(** ".." AFTER A LINK IS TAKEN FROM THE TARGET'S PARENT, not from the
    text: "lt/.." is the parent of /tmp, the root, where a reading of
    the text would cancel "lt/.." to the working folder.  And ".." at
    the root stays at the root. *)
Example dotdot_after_a_link_is_the_targets_parent :
  ln ns_md [108;116;47;46;46] = Fs.RFound Fs.root Fs.EDir
  /\ ln ns_md [108;116;47;46;46;47;46;46] = Fs.RFound Fs.root Fs.EDir
  /\ ln ns_md [108;116;47;46;46;47;119;111;114;107;47;102]
     = Fs.RFound (rp [47;119;111;114;107;47;102]) (Fs.EFile 1).
Proof. split_conj; vm_compute; reflexivity. Qed.

(** A TRAILING SEPARATOR FORCES THE FOLLOW AND ASKS FOR A FOLDER
    ([lookup_last], :2647-2652): "l/" is -ENOTDIR at the file, even on a
    walk that does not follow its last link; "ld/" is the folder. *)
Example trailing_slash_on_a_link :
  ln ns_md [108;47] = Fs.RNotDir (rp [47;119;111;114;107;47;102])
  /\ ln (Fs.WalkFull false false) [108;47] = Fs.RNotDir (rp [47;119;111;114;107;47;102])
  /\ ln (Fs.WalkFull false false) [108;100;47] = Fs.RFound (rp [47;119;111;114;107;47;100]) Fs.EDir.
Proof. split_conj; vm_compute; reflexivity. Qed.

(** A LINK TO NOTHING ends where its body's last name is missing, in the
    folder the body is walked from: that is where [O_CREAT] creates
    ([lookup_open], :3788-3800).  O_CREAT|O_EXCL does not follow it. *)
Example dangling_link_is_missing_at_its_target :
  ln ns_md [100;97;110;103] = Fs.RMissing Fs.default_cwd (rp [110;101;119])
  /\ ln (Fs.WalkCreate true) [100;97;110;103] = Fs.RMissing Fs.default_cwd (rp [110;101;119])
  /\ ln (Fs.WalkCreate false) [100;97;110;103]
     = Fs.RFound (rp [47;119;111;114;107;47;100;97;110;103]) (Fs.ELink (rp [110;101;119])).
Proof. split_conj; vm_compute; reflexivity. Qed.

(** A LINK THAT LEADS TO /proc is outside the image, like the name. *)
Example link_to_proc_is_outside :
  ln ns_md [108;112] = Fs.ROutside /\ ln ns_md [108;112;47;120] = Fs.ROutside.
Proof. split; vm_compute; reflexivity. Qed.

(** THE FOLLOW BUDGET.  A link to itself is -ELOOP on the 41st follow.
    A chain of 41 links ends -ELOOP and a chain of exactly 40 resolves:
    [total_link_count++ >= MAXSYMLINKS] refuses the 41st follow and no
    earlier one.  The 40-chain's success is ADMITTED and not forced: it
    followed links, so -ELOOP stands beside it (the count is not reset
    when the kernel retries a walk, :2705-2709), which the arms read off
    [Fs.wr_followed]. *)
Definition chain_name (n : nat) : list Z := [99; Z.of_nat n].

(** "cA" (65) -> "cB" -> ... -> "ci" (105) -> "f": 41 links. *)
Definition chain_image : Fs.Fs :=
  fold_left (fun fs n => Fs.fs_set fs (Fs.child_key ns_cwd (rp (chain_name n)))
                              (Fs.ELink (rp (chain_name (S n)))))
    (seq 65 40)
    (Fs.fs_set ns_image (Fs.child_key ns_cwd (rp (chain_name 105))) (Fs.ELink (rp [102]))).

Example the_41st_follow_is_eloop :
  ln ns_md [111] = Fs.RLoop
  (* 41 follows from "cA" *)
  /\ fst (fst (Fs.resolve ns_md chain_image ns_cwd (rp (chain_name 65)))) = Fs.RLoop
  (* 40 from "cB": the file, with the follow recorded *)
  /\ Fs.resolve_res ns_md chain_image ns_cwd (rp (chain_name 66))
     = Fs.mkWalkRes (Fs.RFound (rp [47;119;111;114;107;47;102]) (Fs.EFile 1))
         Fs.LastNorm false true false.
Proof. split_conj; vm_compute; reflexivity. Qed.
