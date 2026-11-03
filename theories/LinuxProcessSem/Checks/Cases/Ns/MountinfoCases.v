(** * LinuxProcessSem.Checks.Cases.Ns.MountinfoCases — the text of mountinfo

    A small mount namespace (a tmpfs root, a read-only procfs bind below
    it, a slave devpts mount, a mount the reader's root does not reach)
    and the exact text [mountinfo_text] gives with a chosen environment. *)

From Stdlib Require Import ZArith List Bool PArith String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount Walk Files Mountinfo.
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
  mkNsState
    [mkMount 1 1 None 1 1 1 nf nf false false None None;
     mkMount 2 1 (Some 1%positive) 2 31 3 ro3 nf false false None None;
     mkMount 3 1 (Some 1%positive) 3 40 4 nsx nf false false None (Some 4%positive);
     mkMount 4 2 None 1 1 1 nf nf false false None None;
     mkMount 5 1 (Some 4%positive) 9 1 1 nf nf false false None None]
    [] [] [] []
    [mkSb 1 SbTmpfs 1 1 false 16914836 false false false;
     mkSb 3 (SbProc 1) 1 30 false 40864 true true true;
     mkSb 4 SbDevpts 1 40 false 7377 false false false]
    [mkDentry 1 1 None [] 1; mkDentry 2 1 (Some 1%positive) (s "proc") 2;
     mkDentry 3 1 (Some 1%positive) (s "dev pts") 3; mkDentry 9 1 (Some 1%positive) (s "x") 9;
     mkDentry 30 3 None [] 30; mkDentry 31 3 (Some 30%positive) (s "sys") 31;
     mkDentry 40 4 None [] 40]
    [] [] (ns_env empty_nsstate).

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
