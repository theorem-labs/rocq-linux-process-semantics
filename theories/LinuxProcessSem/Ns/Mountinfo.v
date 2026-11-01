(** * LinuxProcessSem.Ns.Mountinfo — the text of /proc/<pid>/mountinfo

    [mountinfo_text] is what [show_mountinfo] (Linux 6.18.44
    fs/proc_namespace.c) prints for a mount namespace seen from a root:
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

    What the tables do not hold is the environment's, in [MiEnv]: the
    kernel's mount ids and peer-group ids (any values, the ids of
    distinct mounts distinct), each superblock's device number, the type
    name of a host superblock, each mount's source name, the superblock
    options a file system prints, and [propagate_from], which turns on
    peer groups outside the namespace.  A reader of the text can rely on
    the root, the mount point, the mount options, the type of a tmpfs,
    procfs or devpts superblock, the superblock's ro/rw, which mounts are
    shared, slaves or unbindable, and which lines name the same parent. *)

From Stdlib Require Import ZArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount Walk Files.
Import ListNotations.
Local Open Scope Z_scope.

Record MiEnv := mkMiEnv {
  mi_id      : positive -> Z;              (** [mnt_id] of a mount *)
  mi_group   : positive -> Z;              (** [mnt_group_id] of a peer group *)
  mi_dev     : positive -> Z * Z;          (** [MAJOR], [MINOR] of a superblock's [s_dev] *)
  mi_type    : positive -> list byte;      (** the type name of a host superblock *)
  mi_source  : positive -> list byte;      (** a mount's [mnt_devname] *)
  mi_sbopts  : positive -> list byte;      (** a superblock's [show_options] text *)
  mi_dom     : positive -> option Z        (** [get_dominating_id] when it differs from the master *)
}.

(** The ids of distinct mounts of the namespace are distinct. *)
Definition mi_env_ok (E : MiEnv) (st : NsState) : Prop :=
  forall a b, In a (map mnt_id (ns_mounts st)) -> In b (map mnt_id (ns_mounts st)) ->
              mi_id E a = mi_id E b -> a = b.

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

Definition sb_path (st : NsState) (d : positive) : option (list byte) :=
  sb_path_fuel (S (length (ns_dentries st))) st d [].

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

(** The optional fields: shared, master (with propagate_from), unbindable. *)
Definition tagged (E : MiEnv) (m : Mount) : list byte :=
  (match mnt_peer m with
   | Some g => ascii [32; 115; 104; 97; 114; 101; 100; 58] ++ dec (mi_group E g)          (* " shared:" *)
   | None => []
   end)
  ++ (match mnt_master m with
      | Some g => ascii [32; 109; 97; 115; 116; 101; 114; 58] ++ dec (mi_group E g)        (* " master:" *)
                  ++ match mi_dom E (mnt_id m) with
                     | Some x => ascii [32; 112; 114; 111; 112; 97; 103; 97; 116; 101; 95; 102; 114;
                                        111; 109; 58] ++ dec x                            (* " propagate_from:" *)
                     | None => []
                     end
      | None => []
      end)
  ++ (if mnt_unbindable m then ascii [32; 117; 110; 98; 105; 110; 100; 97; 98; 108; 101] else []).

(** One line, or [Some []] for a mount whose mount point the root does not
    reach; [None] when the tables do not decide. *)
Definition mount_line (E : MiEnv) (st : NsState) (root : Loc) (m : Mount) : option (list byte) :=
  match find_sb st (mnt_sb m), sb_path st (mnt_root m), prepend_path st root (mnt_id m) (mnt_root m) with
  | Some s, Some rpath, Some (code, mpath) =>
      if negb (code =? 0) then Some []
      else
        let pid := match mnt_parent m with Some p => p | None => mnt_id m end in
        let (maj, mn) := mi_dev E (sb_id s) in
        Some (dec (mi_id E (mnt_id m)) ++ ascii [32] ++ dec (mi_id E pid) ++ ascii [32]
              ++ dec maj ++ ascii [58] ++ dec mn ++ ascii [32]
              ++ escape rpath ++ ascii [32] ++ escape mpath
              ++ flag_text m ++ tagged E m
              ++ ascii [32; 45; 32] ++ type_name E s ++ ascii [32] ++ escape (mi_source E (mnt_id m))
              ++ (if sb_rdonly s then ascii [32; 114; 111] else ascii [32; 114; 119])
              ++ mi_sbopts E (sb_id s) ++ ascii [10])
  | _, _, _ => None
  end.

(** The whole text for mount namespace [ns] seen from [root]. *)
Definition mountinfo_text (E : MiEnv) (st : NsState) (ns : positive) (root : Loc) : option (list byte) :=
  fold_right (fun m acc => match acc, mount_line E st root m with
                           | Some rest, Some l => Some (l ++ rest)
                           | _, _ => None
                           end)
             (Some [])
             (List.filter (fun m => Pos.eqb (mnt_ns m) ns) (ns_mounts st)).
