(** * LinuxProcessSem.Checks.Cases.Ns.MountinfoCases — the text of mountinfo

    A small mount namespace (a tmpfs root, a read-only procfs bind below
    it, a slave devpts mount, a mount the reader's root does not reach)
    and the exact text [mountinfo_text] gives with a chosen environment;
    then [propagate_from] computed from the tables (Linux v6.18.46,
    [get_dominating_id], fs/pnode.c:33-67; [show_mountinfo],
    fs/proc_namespace.c:158-169) and the rule on group numbers. *)

From Stdlib Require Import ZArith List Bool PArith String Ascii Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount Walk Files Propagation Mountinfo.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Ns Require MountArmsCases.
Import ListNotations.
Open Scope Z_scope.

Definition s (x : string) : list byte := map (fun c => Z_to_bv 8 (Z.of_nat (nat_of_ascii c))) (list_ascii_of_string x).

(** The environment: a mount's id is 20 plus its model id, a group's 5
    plus its, every device 0:<superblock id>, host type "ext4", every
    source "none", no superblock options, no propagate_from. *)
Definition E : MiEnv :=
  mkMiEnv (fun i => 20 + Zpos i) (fun g => 5 + Zpos g) (fun s => (0, Zpos s))
          (fun _ => s "ext4") (fun _ => s "none") (fun _ => []) (fun _ => None).

Definition nf : MountFlags := mkMountFlags false false false false.
Definition ro3 : MountFlags := mkMountFlags true true true false.
Definition nsx : MountFlags := mkMountFlags false true false true.

(** Mount 1: tmpfs root (dentry 1); mount 2: procfs (superblock 3) on
    dentry 2 "proc", read-only, nosuid, nodev, showing its subdirectory
    dentry 31 "sys"; mount 3: devpts on dentry 3 "dev pts" (a space),
    slave of group 4, nosuid, noexec; mount 4: in another namespace;
    mount 5: on dentry 9 of mount 4, which the root does not reach. *)
Definition st : NsState :=
  let w := with_mounts empty_nsstate
    [mkMount 1 1 None 1 1 1 nf nf false false None None;
     mkMount 2 1 (Some 1%positive) 2 31 3 ro3 nf false false None None;
     mkMount 3 1 (Some 1%positive) 3 40 4 nsx nf false false None (Some 4%positive);
     mkMount 4 2 None 1 1 1 nf nf false false None None;
     mkMount 5 1 (Some 4%positive) 9 1 1 nf nf false false None None] in
  let w := with_sbs w
    [mkSb 1 SbTmpfs 1 1 false 16914836 false false false;
     mkSb 3 (SbProc 1) 1 30 false 40864 true true true;
     mkSb 4 SbDevpts 1 40 false 7377 false false false] in
  with_dentries w
    [mkDentry 1 1 None [] 1; mkDentry 2 1 (Some 1%positive) (s "proc") 2;
     mkDentry 3 1 (Some 1%positive) (s "dev pts") 3; mkDentry 9 1 (Some 1%positive) (s "x") 9;
     mkDentry 30 3 None [] 30; mkDentry 31 3 (Some 30%positive) (s "sys") 31;
     mkDentry 40 4 None [] 40].

(** Mount 3 is a slave of group 4, which has no member in the tables, so
    [propagate_from] is the environment's ([mi_dom], here none): the text
    is the one the model gave before it computed [propagate_from]. *)
Example mountinfo_lines :
  mountinfo_text E st 1 (LDentry 1 1)
  = Some (s "21 21 0:1 / / rw,relatime - tmpfs none rw
22 21 0:3 /sys /proc ro,nosuid,nodev,relatime - proc none rw
23 21 0:4 / /dev\040pts rw,nosuid,noexec,relatime master:9 - devpts none rw
").
Proof. vm_compute. reflexivity. Qed.

(** Seen from the root of mount 2 (dentry 31 of procfs), only that mount
    is reachable, at "/". *)
Example mountinfo_from_proc :
  mountinfo_text E st 1 (LDentry 2 31) = Some (s "22 21 0:3 /sys / ro,nosuid,nodev,relatime - proc none rw
").
Proof. vm_compute. reflexivity. Qed.

(** The case's values are well formed; a host type name or an options
    text with a newline is not (Linux prints it escaped), nor are two
    superblocks with one device number. *)
Example E_ok : mi_env_ok E.
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a b H. cbn in H. apply Pos2Z.inj. lia.
  - intros a b H. cbn in H. injection H as H. exact H.
  - intros a. cbn. lia.
  - intros x. cbn. lia.
  - intros x. reflexivity.
  - intros x. reflexivity.
Qed.

Example newline_type_not_ok :
  ~ mi_env_ok (mkMiEnv (fun i => Zpos i) (fun g => Zpos g) (fun x => (0, Zpos x))
                       (fun _ => s "ext4
") (fun _ => []) (fun _ => []) (fun _ => None)).
Proof. intros (_ & _ & _ & _ & H & _). specialize (H 1%positive). vm_compute in H. discriminate H. Qed.

Example shared_device_not_ok :
  ~ mi_env_ok (mkMiEnv (fun i => Zpos i) (fun g => Zpos g) (fun _ => (0, 7))
                       (fun _ => []) (fun _ => []) (fun _ => []) (fun _ => None)).
Proof. intros (_ & H & _). specialize (H 1%positive 2%positive eq_refl). discriminate H. Qed.

(** Mount namespace 1: the root mount 1, shared in group 10, and mount 3
    (devpts on "dev pts"), a slave of group 11.  Mount namespace 2: its
    root mount 4, and mount 6, the only member of group 11, a slave of
    group 10.  The mounts are built with the setters. *)
Definition b1 : Mount := mnt_with_peer (MountArmsCases.mnt 1 None 1 1 1 false false) (Some 10%positive).
Definition b3 (g : positive) : Mount :=
  mnt_with_master (MountArmsCases.mnt 3 (Some 1%positive) 3 40 4 false false) (Some g).
Definition b4 : Mount := mnt_with_ns (MountArmsCases.mnt 4 None 1 1 1 false false) 2.
Definition b6 : Mount :=
  mnt_with_master (mnt_with_peer (mnt_with_ns (MountArmsCases.mnt 6 (Some 4%positive) 9 1 1 false false) 2)
                                 (Some 11%positive))
                  (Some 10%positive).
Definition st2 : NsState := with_mounts st [b1; b3 11; b4; b6].

(** Group 11, mount 3's master group, has no member in namespace 1; its
    master group 10 has mount 1 there, whose root the reader's root
    reaches: [get_dominating_id] gives group 10 (fs/pnode.c:56-67), and
    its number 15 is not 0 and not the master's 16, so the line prints
    "propagate_from:15" (fs/proc_namespace.c:165-166).  Before the model
    computed it, the line printed [mi_dom E] of the mount, here nothing:
    "master:16" alone.  [st2] is a launch the model took before (peer and
    master groups are launch values), so this is a corrected answer. *)
Example propagate_from_computed :
  mountinfo_text E st2 1 (LDentry 1 1)
  = Some (s "21 21 0:1 / / rw,relatime shared:15 - tmpfs none rw
23 21 0:4 / /dev\040pts rw,relatime master:16 propagate_from:15 - devpts none rw
")
  /\ mi_dom E 3 = None.
Proof. split; vm_compute; reflexivity. Qed.

(** Seen from the root of mount 3, mount 1's root is not reachable
    ([get_peer_under_root], fs/pnode.c:41), and group 10 has no master:
    [get_dominating_id] gives 0, and nothing is printed. *)
Example propagate_from_unreachable :
  mountinfo_text E st2 1 (LDentry 3 40)
  = Some (s "23 21 0:4 / / rw,relatime master:16 - devpts none rw
").
Proof. vm_compute. reflexivity. Qed.

(** Mount 3 a slave of group 10 itself: the dominating group is the
    master, and nothing is printed. *)
Example propagate_from_is_master :
  mountinfo_text E (with_mounts st [b1; b3 10; b4; b6]) 1 (LDentry 1 1)
  = Some (s "21 21 0:1 / / rw,relatime shared:15 - tmpfs none rw
23 21 0:4 / /dev\040pts rw,relatime master:15 - devpts none rw
").
Proof. vm_compute. reflexivity. Qed.

(** With group 10 open, the host can mount on mount 1 at any time: the
    text of namespace 1 has no answer. *)
Example mountinfo_open_group :
  mountinfo_text E (with_open_groups st2 [10%positive]) 1 (LDentry 1 1) = None.
Proof. vm_compute. reflexivity. Qed.

(** [st] without mount 5.  Mount 5 is a mount of namespace 1 on mount 4 of
    namespace 2, so with namespace 2 entered the path of mount 5's line,
    and so the text of namespace 1, has no answer for that reason alone. *)
Definition st_sb : NsState :=
  with_mounts st (filter (fun m => negb (Pos.eqb (mnt_id m) 5)) (ns_mounts st)).

(** Mount 4 of namespace 2 is on superblock 1, mount 1's.  Without outside
    entry the text of namespace 1 is the one of [mountinfo_lines] (the
    root does not reach mount 5).  With only namespace 2 entered from
    outside, namespace 1 holds no open mount, but an outside remount
    through mount 4 can make superblock 1 read-only, which mount 1's line
    prints as its super options' " ro" (fs/proc_namespace.c:182, Linux
    v6.18.46): the text of namespace 1 has no answer.  Namespace 2's own
    text has none either. *)
Example mountinfo_shared_sb_entered :
  mountinfo_text E st_sb 1 (LDentry 1 1) = mountinfo_text E st 1 (LDentry 1 1)
  /\ mountinfo_text E (with_entered_mntns st_sb [2%positive]) 1 (LDentry 1 1) = None
  /\ mountinfo_text E (with_entered_mntns st_sb [2%positive]) 2 (LDentry 4 1) = None.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(** [st_sb] with mount 4 of namespace 2 on a superblock of its own
    (superblock 5, root dentry 50).  With namespace 2 entered, no mount of
    namespace 1 shares a superblock with it, so namespace 1's text keeps
    its answer, the text of [mountinfo_lines]; namespace 2's text has
    none.  The decline reaches only namespaces that share a superblock
    with an entered one. *)
Definition st_own : NsState :=
  let w := with_mounts st_sb
    (map (fun m => if Pos.eqb (mnt_id m) 4 then mnt_with_root (mnt_with_sb m 5) 50 else m)
         (ns_mounts st_sb)) in
  let w := with_sbs w (ns_sbs st_sb ++ [mkSb 5 SbTmpfs 1 50 false 16914836 false false false]) in
  with_dentries w (ns_dentries st_sb ++ [mkDentry 50 5 None [] 50]).

Example mountinfo_own_sb_entered :
  mountinfo_text E (with_entered_mntns st_own [2%positive]) 1 (LDentry 1 1)
    = mountinfo_text E st 1 (LDentry 1 1)
  /\ mountinfo_text E (with_entered_mntns st_own [2%positive]) 2 (LDentry 4 50) = None.
Proof. split; vm_compute; reflexivity. Qed.

(** Groups 10 and 11 are live in [st2]; [E] gives them distinct numbers of
    at least 1, and one number for every group breaks the rule. *)
Example E_groups_ok : mi_groups_ok E st2.
Proof.
  split.
  - intros g h _ _ H. cbn in H. apply Pos2Z.inj. lia.
  - intros g _. cbn. lia.
Qed.

Example one_group_number_not_ok :
  ~ mi_groups_ok (mkMiEnv (fun i => 20 + Zpos i) (fun _ => 7) (fun x => (0, Zpos x))
                          (fun _ => []) (fun _ => []) (fun _ => []) (fun _ => None)) st2.
Proof.
  intros [H _].
  assert (Hg : 10%positive = 11%positive).
  { apply H; [apply live_groupb_live; vm_compute; reflexivity
             |apply live_groupb_live; vm_compute; reflexivity
             |reflexivity]. }
  discriminate Hg.
Qed.
