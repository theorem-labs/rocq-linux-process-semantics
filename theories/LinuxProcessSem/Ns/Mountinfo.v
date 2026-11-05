(** * LinuxProcessSem.Ns.Mountinfo — the text of /proc/<pid>/mountinfo

    [mountinfo_text] is what [show_mountinfo] (Linux v6.18.46
    fs/proc_namespace.c:135-191) prints for a mount namespace seen from a root:
    one line per mount of the namespace, in the order the mounts were
    made (the order the tables keep), skipping a mount whose mount point
    is not reachable from the root ([seq_path_root]'s SEQ_SKIP):

      <id> <parent id> <major>:<minor> <root> <mount point> <ro|rw>
      [,nosuid][,nodev][,noexec],relatime [shared:<g>]
      [master:<g>[ propagate_from:<g>]][ unbindable] - <type> <source>
      <ro|rw><super options>

    The root is the mount's root within its file system ([show_path]),
    the mount point is its path from the reader's root, both escaped as
    [seq_path_root] and [seq_dentry] escape space, tab, newline and
    backslash ("\ooo").  Every mount of the model is relatime (see
    [Ns.NewMount]).

    What the tables do not hold is the environment's, in [Tables.MiEnv],
    one value per kernel object for the whole run, kept in the namespace
    state ([env_mountinfo]): the kernel's mount ids and peer-group ids,
    each superblock's device number, the type name of a host superblock,
    each mount's source name, the superblock options a file system prints,
    and [propagate_from] where the master chain leaves the tables.
    [propagate_from] is computed from the state and the reader's root
    ([Propagation.dominating_id]; [get_dominating_id], fs/pnode.c:56-67,
    printed when not 0 and not the master's number,
    fs/proc_namespace.c:161-167) while the chain stays in the tables;
    [mi_dom] gives it where the chain reaches a group with no member in
    the tables.  [show_type], [mangle] and [seq_show_option] escape space,
    tab, newline and backslash in the type, the source and the options,
    so no value breaks a line or a field.  A reader of the text can rely
    on the root, the mount point, the mount options, the type of a tmpfs,
    procfs or devpts superblock, the superblock's ro/rw, which mounts are
    shared, slaves or unbindable, which lines name the same parent, and,
    where the values are well formed ([mi_env_ok], [mi_groups_ok]),
    distinct ids for distinct mounts, distinct devices for distinct
    superblocks and distinct numbers for distinct live peer groups.  The
    text of a namespace that holds a mount which can receive a mount event
    from an open group has no answer: the host can change it at any time
    ([Propagation.ns_open]). *)

From Stdlib Require Import ZArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount Walk Files Propagation.
Import ListNotations.
Local Open Scope Z_scope.

(** A byte that separates fields or lines in the text: space, tab or
    newline. *)
Definition separator_byte (c : byte) : bool :=
  let v := bv_unsigned c in (v =? 32) || (v =? 9) || (v =? 10).

(** Well-formed values: distinct mounts have distinct ids ([mnt_id] comes
    from an IDA, fs/namespace.c [mnt_alloc_id]) and distinct superblocks
    distinct device numbers ([s_dev] is the block device, or an anonymous
    device from [get_anon_bdev]); the numbers are not negative, as the
    text prints them unsigned; and a host type name and the options text
    hold no space, tab or newline, which [show_type] and
    [seq_show_option] (fs/proc_namespace.c, fs/seq_file.c) print escaped
    ("\ooo").  The values are the text after that escaping. *)
Definition mi_env_ok (E : MiEnv) : Prop :=
  (forall a b, mi_id E a = mi_id E b -> a = b)
  /\ (forall a b, mi_dev E a = mi_dev E b -> a = b)
  /\ (forall a, 0 <= mi_id E a)
  /\ (forall s, 0 <= fst (mi_dev E s) /\ 0 <= snd (mi_dev E s))
  /\ (forall s, existsb separator_byte (mi_type E s) = false)
  /\ (forall s, existsb separator_byte (mi_sbopts E s) = false).

Lemma default_mi_env_ok : mi_env_ok default_mi_env.
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a b H. cbn in H. injection H as H. exact H.
  - intros a b H. cbn in H. injection H as H. exact H.
  - intros a. cbn. lia.
  - intros s. cbn. lia.
  - intros s. reflexivity.
  - intros s. reflexivity.
Qed.

(** Well-formed group numbers in state [st]: live peer groups have
    distinct numbers, each at least 1.  Group numbers come from one IDA
    for the whole system, [mnt_group_ida], which gives the lowest free
    number of at least 1 (fs/namespace.c:239-247; [ida_alloc_min],
    include/linux/idr.h:309-312) and reuses a number once its group dies,
    so the rule holds per state, not over the run: a group key that is
    no longer live may share its number with a later group.  A group is
    live while a mount of the tables is in it or a slave of it
    ([Propagation.live_group]). *)
Definition mi_groups_ok (E : MiEnv) (st : NsState) : Prop :=
  (forall g h, live_group st g -> live_group st h -> mi_group E g = mi_group E h -> g = h)
  /\ (forall g, live_group st g -> 1 <= mi_group E g).

Lemma default_mi_env_groups_ok : forall st, mi_groups_ok default_mi_env st.
Proof.
  intros st. split.
  - intros g h _ _ H. cbn in H. injection H as H. exact H.
  - intros g _. cbn. lia.
Qed.

Fixpoint dec_rev (fuel : nat) (n : Z) : list byte :=
  match fuel with
  | O => []
  | S f => if n <? 10 then [Z_to_bv 8 (48 + n)] else Z_to_bv 8 (48 + n mod 10) :: dec_rev f (n / 10)
  end.

(** "%i" / "%u" of a non-negative number. *)
Definition dec (n : Z) : list byte := rev (dec_rev 20 (Z.max 0 n)).

(** [mangle] / the escapes of [seq_path_root]: space, tab, newline and
    backslash as a backslash and three octal digits. *)
Definition escape_byte (c : byte) : list byte :=
  let v := bv_unsigned c in
  if (v =? 32) || (v =? 9) || (v =? 10) || (v =? 92)
  then ascii [92; 48 + v / 64; 48 + (v / 8) mod 8; 48 + v mod 8]
  else [c].

Definition escape (l : list byte) : list byte := flat_map escape_byte l.

(** The path of dentry [d] from its superblock's root ([dentry_path_raw]):
    "/" for the root. *)
Fixpoint sb_path_fuel (fuel : nat) (st : NsState) (d : positive) (acc : list byte) : option (list byte) :=
  match fuel with
  | O => None
  | S f => match find_dentry st d with
           | None => None
           | Some x => match d_parent x with
                       | None => Some (match acc with [] => ascii [47] | _ => acc end)
                       | Some p => sb_path_fuel f st p (ascii [47] ++ d_name x ++ acc)
                       end
           end
  end.

(** [dentry_path] (fs/d_path.c), which [show_mountinfo] prints the root
    with: [dentry_path_raw]'s path, then "//deleted" for an unlinked dentry. *)
Definition sb_path (st : NsState) (d : positive) : option (list byte) :=
  let deleted := match find_dentry st d with
                 | Some x => if d_unlinked x then ascii [47; 47; 100; 101; 108; 101; 116; 101; 100] else []
                 | None => []
                 end in
  option_map (fun p => p ++ deleted) (sb_path_fuel (S (length (ns_dentries st))) st d []).

Definition flag_text (m : Mount) : list byte :=
  (if mf_ro (mnt_flags m) then ascii [32; 114; 111] else ascii [32; 114; 119])
  ++ (if mf_nosuid (mnt_flags m) then ascii [44; 110; 111; 115; 117; 105; 100] else [])
  ++ (if mf_nodev (mnt_flags m) then ascii [44; 110; 111; 100; 101; 118] else [])
  ++ (if mf_noexec (mnt_flags m) then ascii [44; 110; 111; 101; 120; 101; 99] else [])
  ++ ascii [44; 114; 101; 108; 97; 116; 105; 109; 101].                      (* ",relatime" *)

Definition type_name (E : MiEnv) (s : SuperBlock) : list byte :=
  match sb_kind s with
  | SbTmpfs => ascii [116; 109; 112; 102; 115]
  | SbProc _ => ascii [112; 114; 111; 99]
  | SbDevpts => ascii [100; 101; 118; 112; 116; 115]
  | SbHost => mi_type E (sb_id s)
  end.

(** [is_path_reachable] of mount [d]'s root from the reader's root
    (fs/namespace.c:4514-4522): [prepend_path] reaches the root (code 0),
    the test [mount_line] makes for [d]'s own line.  [None] when the
    tables do not decide it. *)
Definition reach_root (st : NsState) (root : Loc) (d : Mount) : option bool :=
  match prepend_path st root (mnt_id d) (mnt_root d) with
  | Some (code, _) => Some (code =? 0)
  | None => None
  end.

(** " propagate_from:" and the number. *)
Definition propagate_from_text (x : Z) : list byte :=
  ascii [32; 112; 114; 111; 112; 97; 103; 97; 116; 101; 95; 102; 114; 111; 109; 58] ++ dec x.

(** " propagate_from:D" after " master:N" ([show_mountinfo],
    fs/proc_namespace.c:161-167): printed when D is not 0 and not N.  A
    chain that leaves the tables gives the environment's [mi_dom]. *)
Definition dom_text (E : MiEnv) (m : Mount) (master : Z) (d : DomId) : list byte :=
  match d with
  | DomGroup h =>
      let x := mi_group E h in
      if (x =? 0) || (x =? master) then [] else propagate_from_text x
  | DomZero => []
  | DomOut => match mi_dom E (mnt_id m) with
              | Some x => propagate_from_text x
              | None => []
              end
  end.

(** The optional fields of mount [m] seen from [root]: shared, master
    with propagate_from, unbindable (fs/proc_namespace.c:158-169).  [None]
    when the tables do not decide propagate_from. *)
Definition tagged (E : MiEnv) (st : NsState) (root : Loc) (m : Mount) : option (list byte) :=
  let shared := match mnt_peer m with
                | Some g => ascii [32; 115; 104; 97; 114; 101; 100; 58] ++ dec (mi_group E g)  (* " shared:" *)
                | None => []
                end in
  let unbindable := if mnt_unbindable m then ascii [32; 117; 110; 98; 105; 110; 100; 97; 98; 108; 101]
                    else [] in
  match mnt_master m with
  | None => Some (shared ++ unbindable)
  | Some g =>
      match dominating_id (ns_mounts st) (reach_root st root) m with
      | Some d =>
          let master := mi_group E g in
          Some (shared ++ ascii [32; 109; 97; 115; 116; 101; 114; 58] ++ dec master  (* " master:" *)
                ++ dom_text E m master d ++ unbindable)
      | None => None
      end
  end.

(** One line, or [Some []] for a mount whose mount point the root does not
    reach; [None] when the tables do not decide. *)
Definition mount_line (E : MiEnv) (st : NsState) (root : Loc) (m : Mount) : option (list byte) :=
  match find_sb st (mnt_sb m), sb_path st (mnt_root m), prepend_path st root (mnt_id m) (mnt_root m) with
  | Some s, Some rpath, Some (code, mpath) =>
      if negb (code =? 0) then Some []
      else
        match tagged E st root m with
        | Some tags =>
            let pid := match mnt_parent m with Some p => p | None => mnt_id m end in
            let (maj, mn) := mi_dev E (sb_id s) in
            Some (dec (mi_id E (mnt_id m)) ++ ascii [32] ++ dec (mi_id E pid) ++ ascii [32]
                  ++ dec maj ++ ascii [58] ++ dec mn ++ ascii [32]
                  ++ escape rpath ++ ascii [32] ++ escape mpath
                  ++ flag_text m ++ tags
                  ++ ascii [32; 45; 32] ++ type_name E s ++ ascii [32] ++ escape (mi_source E (mnt_id m))
                  ++ (if sb_rdonly s then ascii [32; 114; 111] else ascii [32; 114; 119])
                  ++ mi_sbopts E (sb_id s) ++ ascii [10])
        | None => None
        end
  | _, _, _ => None
  end.

(** The whole text for mount namespace [ns] seen from [root]; no answer
    when [ns] holds a mount that can receive a mount event from an open
    group ([Propagation.ns_open]), or a mount whose superblock's read-only
    state an outside task may change ([Propagation.flags_open]): each line
    prints [sb_rdonly] as its super options' " ro" or " rw"
    ([show_mountinfo], fs/proc_namespace.c:182, Linux v6.18.46), and a
    remount through a mount of a listed namespace, or a reconfiguration
    through [fspick] (see [Propagation.flags_open]), changes it for every
    mount of the superblock.  The per-mount " ro" or " rw" is the mount's
    own MNT_READONLY (155), which only a task in the mount's own namespace
    can change. *)
Definition mountinfo_text (E : MiEnv) (st : NsState) (ns : positive) (root : Loc) : option (list byte) :=
  if ns_open st ns
     || existsb (fun m => Pos.eqb (mnt_ns m) ns && flags_open st m) (ns_mounts st)
  then None
  else fold_right (fun m acc => match acc, mount_line E st root m with
                                | Some rest, Some l => Some (l ++ rest)
                                | _, _ => None
                                end)
                  (Some [])
                  (List.filter (fun m => Pos.eqb (mnt_ns m) ns) (ns_mounts st)).
