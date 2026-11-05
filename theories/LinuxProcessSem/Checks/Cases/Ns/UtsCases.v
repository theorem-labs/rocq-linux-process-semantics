(** * LinuxProcessSem.Checks.Cases.Ns.UtsCases — the UTS namespace: sethostname, setdomainname, uname, clone

    The examples follow bubblewrap 0.13.1's setup child when it sets a host name:
    a task of the host clones with a new user, mount, UTS, IPC, pid and
    network namespace ([clone_ns_exact]), and the child calls
    [sethostname("h", 1)] in its new UTS namespace, which its new user
    namespace owns.  Around it: the kernel's refusals in the order of
    [SYSCALL_DEFINE2(sethostname)] (Linux v6.18.46, kernel/sys.c:1419-1443),
    the host's UTS namespace, [uname] after the write, a clone with and
    without CLONE_NEWUTS after the write, and [setdomainname]. *)

From Stdlib Require Import ZArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Mount Userns Walk Arm UserArms Net Clone Task Spec.
Import ListNotations.
Open Scope Z_scope.

(* =========================================================================
   The host and bubblewrap's setup child
   ========================================================================= *)

Definition creds (id : Z) : Creds :=
  mkCreds (Z_to_bv 64 id) (Z_to_bv 64 id) (Z_to_bv 64 id) (Z_to_bv 64 id) (Z_to_bv 64 id)
          (Z_to_bv 64 id) [].

Definition nf : MountFlags := mkMountFlags false false false false.
Definition full : list IdExtent := [mkExtent 0 0 4294967295].
Definition nocaps : CapSets := mkCaps 0 0 0 (2 ^ 41 - 1) 0.
Definition fullcaps : CapSets := mkCaps (2 ^ 41 - 1) (2 ^ 41 - 1) 0 (2 ^ 41 - 1) 0.

(** The host: user namespace 1 (initial, every id mapped), mount namespace
    1, pid namespace 1, network namespace 1 and UTS namespace 1
    ([host_utsns]), all the host's. *)
Definition host : NsState :=
  let st := with_mounts empty_nsstate [mkMount 1 1 None 1 1 1 nf nf false false None None] in
  let st := with_userns st [mkUserNs 1 None 0 0 (Some full) (Some full) true true 100 false] in
  let st := with_mntns st [mk_mntns 1 1 1 true] in
  let st := with_pidns st [mkPidNs 1 None 1 0 0] in
  with_netns st [mkNetNs 1 1 [] false].

(** bubblewrap's parent: pid 136 of the host, uid 65534, no capability. *)
Definition parent : NsCtx := with_caps (with_pids init_nsctx [(1%positive, 136)]) nocaps.
Definition m0 : Model :=
  with_creds (creds 65534) (init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) demo_sp demo_limit (demo_input [] IEof)).

Definition SIGCHLD : Z := 17.

(** The clone of the setup child: a new mount, UTS, IPC, user, pid and
    network namespace, exit signal SIGCHLD. *)
Definition BWRAP_FLAGS : Z :=
  fold_left Z.lor [CLONE_NEWNS; CLONE_NEWUTS; CLONE_NEWIPC; CLONE_NEWUSER; CLONE_NEWPID; CLONE_NEWNET;
                   SIGCHLD] 0.

(** The setup child [C] (host pid 138) and the state after the clone. *)
Definition c_ctx : NsCtx :=
  match clone_ns_exact BWRAP_FLAGS m0 parent host 138 with CnOk c _ _ => c | _ => parent end.
Definition c_st : NsState :=
  match clone_ns_exact BWRAP_FLAGS m0 parent host 138 with CnOk _ _ s => s | _ => host end.

(** [C] is in UTS namespace 2, which its new user namespace 2 owns and
    whose names are still the host's; the host's UTS namespace is
    unchanged; and [C] is outside the released world. *)
Example bwrap_child_uts :
  cx_uts c_ctx = 2%positive /\ cx_user c_ctx = 2%positive
  /\ find_utsns c_st 2 = Some (mkUtsNs 2 2 None None)
  /\ find_utsns c_st 1 = Some host_utsns
  /\ flat_view c_ctx c_st = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* =========================================================================
   sethostname (161) and setdomainname (162)
   ========================================================================= *)

(** Bytes [bs] at address [base], nothing else mapped. *)
Definition at_ (base : Z) (bs : list Z) : word -> option byte :=
  fun a => let k := bv_unsigned a - base in
           if (0 <=? k) && (k <? Z.of_nat (length bs)) then Some (Z_to_bv 8 (nth (Z.to_nat k) bs 0))
           else None.

Definition NAME : Z := 8192.
Definition BUF : Z := 12288.

Definition call (n : Z) (args : list Z) (mm : word -> option byte) : SyscallInput :=
  mkInput (Z_to_bv 64 n) (map (Z_to_bv 64) args) mm mm.

(** [sethostname(NAME, len)] with [bs] at [NAME]. *)
Definition sethost (len : Z) (bs : list Z) : SyscallInput := call 161 [NAME; len] (at_ NAME bs).

Definition ret_of (o : ext_outcome) : option Z :=
  match o with EOk eff _ _ _ _ => Some (bv_signed (eff_ret eff)) | EUnmodeled => None end.
Definition copyins_of (o : ext_outcome) : option (list (Z * nat)) :=
  match o with
  | EOk eff _ _ _ _ => Some (map (fun p => (bv_unsigned (fst p), snd p)) (eff_copyins eff))
  | EUnmodeled => None
  end.
(** The names of UTS namespace [n] after the answer [o]. *)
Definition names_of (o : ext_outcome) (n : positive) : option (option (list Z) * option (list Z)) :=
  match o with
  | EOk _ _ _ s _ =>
      option_map (fun u => (option_map (map bv_unsigned) (utsns_nodename u),
                            option_map (map bv_unsigned) (utsns_domainname u)))
                 (find_utsns s n)
  | EUnmodeled => None
  end.

(** The namespace model answers [C]'s call 161 with [sethostname_arm]. *)
Lemma ns_spec_c : forall i o, ns_sysno i = 161 ->
  ns_spec i m0 c_ctx c_st o <-> o = set_uts_fn UtsNodename i m0 c_ctx c_st.
Proof.
  intros i o Hn. unfold ns_spec. replace (flat_view c_ctx c_st) with false by (vm_compute; reflexivity).
  rewrite Hn. reflexivity.
Qed.

(** bubblewrap's [sethostname("h", 1)] in [C]: [C] holds CAP_SYS_ADMIN in
    its user namespace, which owns its UTS namespace, so the call returns
    0, reads the one byte, and nodename becomes "h" and 64 NULs; the
    host's names do not change. *)
Definition c_sethost : ext_outcome := set_uts_fn UtsNodename (sethost 1 [104]) m0 c_ctx c_st.

Example bwrap_sethostname :
  ns_spec (sethost 1 [104]) m0 c_ctx c_st c_sethost
  /\ ret_of c_sethost = Some 0
  /\ copyins_of c_sethost = Some [(NAME, 1%nat)]
  /\ names_of c_sethost 2 = Some (Some (104 :: repeat 0 64), None)
  /\ names_of c_sethost 1 = Some (None, None).
Proof.
  split; [apply (proj2 (ns_spec_c (sethost 1 [104]) c_sethost eq_refl)); reflexivity|].
  vm_compute. repeat split; reflexivity.
Qed.

(** While bubblewrap's parent lives, the namespace model admits [C]'s
    sethostname ([Spec.ns_multiproc]). *)
Example bwrap_sethostname_multiproc : ext_multiproc ns_ext (sethost 1 [104]) m0 c_ctx c_st = true.
Proof. vm_compute. reflexivity. Qed.

(** The longest name, 64 bytes, and the empty one: the field is the bytes
    and NULs to 65; the empty name reads nothing, whatever the pointer
    (here above [TASK_SIZE]). *)
Example sethostname_64_and_0 :
  names_of (set_uts_fn UtsNodename (sethost 64 (repeat 97 64)) m0 c_ctx c_st) 2
    = Some (Some (repeat 97 64 ++ [0]), None)
  /\ ret_of (set_uts_fn UtsNodename (call 161 [2 ^ 47; 0] (fun _ => None)) m0 c_ctx c_st) = Some 0
  /\ copyins_of (set_uts_fn UtsNodename (call 161 [2 ^ 47; 0] (fun _ => None)) m0 c_ctx c_st) = Some []
  /\ names_of (set_uts_fn UtsNodename (call 161 [2 ^ 47; 0] (fun _ => None)) m0 c_ctx c_st) 2
     = Some (Some (repeat 0 65), None).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** EINVAL for a length above 64, and for a1 = 0xffffffff, whose low 32
    bits are -1 as an [int]; nothing is read. *)
Example sethostname_einval :
  ret_of (set_uts_fn UtsNodename (sethost 65 (repeat 97 65)) m0 c_ctx c_st) = Some (-22)
  /\ ret_of (set_uts_fn UtsNodename (sethost 4294967295 [104]) m0 c_ctx c_st) = Some (-22)
  /\ copyins_of (set_uts_fn UtsNodename (sethost 4294967295 [104]) m0 c_ctx c_st) = Some [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** EFAULT, exact: a name [access_ok] admits that memory does not back
    (nothing at [BUF]), and one above [TASK_SIZE]; the copy failed, so no
    copy-in is recorded, and the name does not change. *)
Example sethostname_efault :
  ret_of (set_uts_fn UtsNodename (call 161 [BUF; 1] (at_ NAME [104])) m0 c_ctx c_st) = Some (-14)
  /\ copyins_of (set_uts_fn UtsNodename (call 161 [BUF; 1] (at_ NAME [104])) m0 c_ctx c_st) = Some []
  /\ names_of (set_uts_fn UtsNodename (call 161 [BUF; 1] (at_ NAME [104])) m0 c_ctx c_st) 2
     = Some (None, None)
  /\ ret_of (set_uts_fn UtsNodename (call 161 [2 ^ 47; 1] (at_ NAME [104])) m0 c_ctx c_st) = Some (-14).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** EPERM before EINVAL: a task of user namespace 2 (a child of the
    initial one) in the host's UTS namespace holds no capability over the
    initial user namespace, which owns it; so even a bad length is EPERM. *)
Definition inside : NsState :=
  with_userns host [mkUserNs 2 (Some 1%positive) 1 65534 None None true false 2147483647 true;
                    mkUserNs 1 None 0 0 (Some full) (Some full) true true 100 false].
Definition in_userns2 : NsCtx := with_caps (with_user_ns init_nsctx 2) fullcaps.

Example sethostname_eperm_host_ns :
  flat_view in_userns2 inside = false
  /\ ret_of (set_uts_fn UtsNodename (sethost 1 [104]) m0 in_userns2 inside) = Some (-1)
  /\ ret_of (set_uts_fn UtsNodename (sethost 65 [104]) m0 in_userns2 inside) = Some (-1).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** In the host's UTS namespace with CAP_SYS_ADMIN over its owner (a task
    of the initial user namespace outside the released world through its
    mount namespace) the call declines: a write would change the host's
    name, the environment's pin. *)
Definition two_mntns : NsState := with_mntns host [mk_mntns 1 1 1 true; mk_mntns 2 1 1 false].
Definition host_admin : NsCtx := with_caps (with_mount_ns init_nsctx 2) fullcaps.

Example sethostname_host_ns_declines :
  flat_view host_admin two_mntns = false
  /\ set_uts_fn UtsNodename (sethost 1 [104]) m0 host_admin two_mntns = EUnmodeled
  /\ set_uts_fn UtsDomainname (call 162 [NAME; 1] (at_ NAME [100])) m0 host_admin two_mntns = EUnmodeled.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** setdomainname is the same template on domainname. *)
Example bwrap_setdomainname :
  names_of (set_uts_fn UtsDomainname (call 162 [NAME; 1] (at_ NAME [100])) m0 c_ctx c_st) 2
  = Some (None, Some (100 :: repeat 0 64)).
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   uname (160) after the write
   ========================================================================= *)

(** The state after [C]'s sethostname. *)
Definition st1 : NsState := match c_sethost with EOk _ _ _ s _ => s | EUnmodeled => c_st end.

Lemma ns_spec_uname_c : forall i o, ns_sysno i = 160 ->
  ns_spec i m0 c_ctx st1 o <-> uname_arm i m0 c_ctx st1 o.
Proof.
  intros i o Hn. unfold ns_spec. replace (flat_view c_ctx st1) with false by (vm_compute; reflexivity).
  rewrite Hn. reflexivity.
Qed.

Definition uname_in : SyscallInput := call 160 [BUF] (at_ BUF (repeat 0 390)).

(** For every answer the released [uname] gives, [C] gets it with "h" as
    nodename; on the released answer's bytes (here 390 'x's), bytes
    65..129 become "h" and 64 NULs and the others stay. *)
Example uname_after_sethostname :
  (forall eff m' evs,
     released uname_in m0 c_ctx st1 (EOk eff m' c_ctx st1 evs) ->
     ns_spec uname_in m0 c_ctx st1 (EOk (uts_view_eff (find_utsns st1 (cx_uts c_ctx)) eff) m' c_ctx st1 evs))
  /\ option_map (fun u => map bv_unsigned (uts_overlay u (repeat (Z_to_bv 8 120) 390)))
                (find_utsns st1 (cx_uts c_ctx))
     = Some (repeat 120 65 ++ (104 :: repeat 0 64) ++ repeat 120 260).
Proof.
  split.
  - intros eff m' evs Hr.
    apply (proj2 (ns_spec_uname_c uname_in _ eq_refl)). unfold uname_arm.
    exists (EOk eff m' c_ctx st1 evs). split; [exact Hr | reflexivity].
  - vm_compute. reflexivity.
Qed.

(** Before the write, and in the host's UTS namespace, [uname] has exactly
    the released answers ([Task.uname_arm_released]). *)
Example uname_unnamed_is_released : forall o,
  (uname_arm uname_in m0 c_ctx c_st o <-> released uname_in m0 c_ctx c_st o)
  /\ (uname_arm uname_in m0 in_userns2 inside o <-> released uname_in m0 in_userns2 inside o).
Proof.
  intros o. split; apply uname_arm_released; vm_compute; split; reflexivity.
Qed.

(* =========================================================================
   clone after the write
   ========================================================================= *)

(** A clone by [C] with CLONE_NEWUTS (host pid 140): the new UTS namespace
    3, owned by [C]'s user namespace, starts with the name [C] set; a
    plain fork shares [C]'s UTS namespace. *)
Definition cl (f : Z) : CloneNs := clone_ns_exact f m0 c_ctx st1 140.
Definition child_uts (o : CloneNs) : option positive := match o with CnOk c _ _ => Some (cx_uts c) | _ => None end.
Definition clone_names (o : CloneNs) (n : positive) : option (option UtsNs) :=
  match o with CnOk _ _ s => Some (find_utsns s n) | _ => None end.

Example clone_newuts_copies_name :
  child_uts (cl (Z.lor CLONE_NEWUTS SIGCHLD)) = Some 3%positive
  /\ option_map (option_map (fun u => (utsns_owner u, option_map (map bv_unsigned) (utsns_nodename u),
                                       utsns_domainname u)))
                (clone_names (cl (Z.lor CLONE_NEWUTS SIGCHLD)) 3)
     = Some (Some (2%positive, Some (104 :: repeat 0 64), None))
  /\ child_uts (cl SIGCHLD) = Some 2%positive.
Proof. vm_compute. repeat split; reflexivity. Qed.
