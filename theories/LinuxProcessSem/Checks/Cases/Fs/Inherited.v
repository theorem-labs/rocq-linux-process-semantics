(** * LinuxProcessSem.Checks.Cases.Fs.Inherited — worked examples over the inherited descriptors

    A launch may hand the process descriptors above 2 that its parent
    opened ([State.ProcInput]'s [in_inherited_fds]): each a descriptor
    number and the bytes of the regular file its open file description
    reads, open read-only at offset 0.  [State.init_model] puts each
    after fds 0, 1 and 2 as a live [State.OInherited], which holds the
    bytes and the offset.

    Each case below is paired with the control a broken change fails:

    - ONE KEY: [read] answers the bytes from offset 0 and moves the
      offset, and the next [read] answers 0.  The control is the same
      read on the launch without the key, which is -EBADF: an
      [init_model] that ignored the field passes the control and fails
      the case.
    - TWO KEYS: each descriptor has its own offset.  Reading 3 to its end
      leaves 5 at 0; the answer one shared offset would give is
      rejected.
    - LOWEST FREE: with a key at 3, [openat] answers 4 and not 3; without
      it, 3 and not 4 ([alloc_fd], fs/file.c, v6.18.46, starts at the
      lowest free number).
    - THE DEFAULT: [State.mkProcInput] fills the list with [[]]; the
      setter [State.with_inherited_fds] is what makes a keyed launch.
    - VALIDITY: [Run.inherited_fds_ok] admits numbers from 3, strictly
      increasing, below [Run.nr_open_max].
    - THE PIN: [Run.valid_input] holds of the plain launch and NOT of the
      keyed one; [Run.valid_input_inherited] holds of the keyed one.
    - THE KIND: [write], [lseek] and [fstat] decline on a key; [close]
      answers 0 and frees the slot; [fcntl]'s [F_GETFD] answers the
      table's close-on-exec bit as on every kind.
    - THE CLONE GATE: a [clone] by a caller that holds a key with its
      offset declines, with either word; the same clone without the key
      answers a pid. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Examples.
Import ListNotations.
Open Scope bv_scope.

(* -------------------------------------------------------------------------
   The launches
   ------------------------------------------------------------------------- *)

(** The bytes "key\n". *)
Definition inh_key : list byte := [107; 101; 121; 10].

(** [Checks.Examples.demo_input_valid]'s input: the plain launch. *)
Definition inh_plain_launch : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

(** The same launch with one key at descriptor 3. *)
Definition inh_key_launch : ProcInput :=
  with_inherited_fds [(3, inh_key)] inh_plain_launch.

Definition inh_model (inp : ProcInput) : Model :=
  init_model [] 0 0 demo_sp demo_limit inp.

(** [read(fd, 4096, 8192)] with [4096, 4096 + 8192) writable. *)
Definition inh_wmem : word -> option byte :=
  fun a => if Z.leb 4096%Z (bv_unsigned a) && Z.ltb (bv_unsigned a) 12288%Z
           then Some 0 else None.

Definition inh_read (fd : word) : SyscallInput :=
  mkInput 63 [fd; 4096; 8192; 0; 0; 0] (fun _ => None) inh_wmem.

(* -------------------------------------------------------------------------
   One key: the bytes, then 0
   ------------------------------------------------------------------------- *)

(** The first [read] answers the four bytes at the buffer and moves the
    offset to 4; the second answers 0 and leaves it there, as
    [ksys_read] (fs/read_write.c, v6.18.46) does at the end of a regular
    file. *)
Example inherited_read_answers_the_bytes_then_eof :
  match check_syscall (inh_read 3) (mkEffect 4 [(4096, inh_key)] [])
          (inh_model inh_key_launch) with
  | CheckOk m1 [] =>
      fd_lookup (m_fds m1) 3 = Some (FdOpaque (OInherited (Some (inh_key, 4))))
      /\ match check_syscall (inh_read 3) (mkEffect 0 [] []) m1 with
         | CheckOk m2 [] =>
             fd_lookup (m_fds m2) 3 = Some (FdOpaque (OInherited (Some (inh_key, 4))))
         | _ => False
         end
  | _ => False
  end.
Proof. vm_compute. split; check_eq. Qed.

(** Fewer bytes than the file holds from the offset, or other bytes, are
    rejected: the answer is the file's. *)
Example inherited_read_rejects_other_bytes :
  check_syscall (inh_read 3) (mkEffect 3 [(4096, [107; 101; 121])] [])
    (inh_model inh_key_launch) = CheckReject
  /\ check_syscall (inh_read 3) (mkEffect 4 [(4096, [107; 101; 121; 11])] [])
       (inh_model inh_key_launch) = CheckReject
  /\ check_syscall (inh_read 3) (mkEffect 0 [] []) (inh_model inh_key_launch)
     = CheckReject.
Proof. repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity. Qed.

(** THE CONTROL: the launch without the key has no descriptor 3, so the
    same read is -EBADF and the four bytes are rejected. *)
Example inherited_read_without_the_key_is_ebadf :
  check_syscall (inh_read 3) (mkEffect (errno_ret EBADF) [] [])
    (inh_model inh_plain_launch) = CheckOk (inh_model inh_plain_launch) []
  /\ check_syscall (inh_read 3) (mkEffect 4 [(4096, inh_key)] [])
       (inh_model inh_plain_launch) = CheckReject.
Proof. split; check_eq. Qed.

(* -------------------------------------------------------------------------
   Two keys: one offset each
   ------------------------------------------------------------------------- *)

Definition inh_two_launch : ProcInput :=
  with_inherited_fds [(3, [97]); (5, [98; 99])] inh_plain_launch.

(** Reading 3 to its end leaves 5 at 0: 5 then answers both of its
    bytes. *)
Example inherited_two_keys_keep_two_offsets :
  match check_syscall (inh_read 3) (mkEffect 1 [(4096, [97])] [])
          (inh_model inh_two_launch) with
  | CheckOk m1 [] =>
      match check_syscall (inh_read 5) (mkEffect 2 [(4096, [98; 99])] []) m1 with
      | CheckOk m2 [] =>
          fd_lookup (m_fds m2) 3 = Some (FdOpaque (OInherited (Some ([97], 1))))
          /\ fd_lookup (m_fds m2) 5
             = Some (FdOpaque (OInherited (Some ([98; 99], 2))))
      | _ => False
      end
  | _ => False
  end.
Proof. vm_compute. split; check_eq. Qed.

(** THE CONTROL: after the read of 3, the answer ONE shared offset would
    give for 5 -- its second byte alone -- is rejected. *)
Example inherited_two_keys_reject_a_shared_offset :
  match check_syscall (inh_read 3) (mkEffect 1 [(4096, [97])] [])
          (inh_model inh_two_launch) with
  | CheckOk m1 [] =>
      check_syscall (inh_read 5) (mkEffect 1 [(4096, [99])] []) m1 = CheckReject
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------
   Lowest free: an open after a key at 3 answers 4
   ------------------------------------------------------------------------- *)

(** [openat(AT_FDCWD, "f", O_RDONLY)] over the image file "f" = "hi"
    ([Checks.Cases.Fs.ReadWrite.mem_open_write] holds the name). *)
Definition inh_open_in : SyscallInput :=
  mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 0; 420; 0; 0] mem_open_write (fun _ => None).

Definition inh_open_plain : ProcInput :=
  mkProcInput [[]] [] [([102], [104; 105])] IEof demo_uid demo_gid demo_groups
              net_silent default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

Example inherited_key_moves_the_lowest_free_descriptor :
  (* with the key at 3: the open answers 4 *)
  match check_syscall inh_open_in (with_copyins [(8192, 2%nat)] (mkEffect 4 [] []))
          (inh_model (with_inherited_fds [(3, inh_key)] inh_open_plain)) with
  | CheckOk m [] => fd_lookup (m_fds m) 4 = Some (FdFile [102] 0)
  | _ => False
  end
  /\ check_syscall inh_open_in (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
       (inh_model (with_inherited_fds [(3, inh_key)] inh_open_plain)) = CheckReject
  (* THE CONTROL, without the key: 3, and not 4 *)
  /\ match check_syscall inh_open_in (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
             (inh_model inh_open_plain) with
     | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdFile [102] 0)
     | _ => False
     end
  /\ check_syscall inh_open_in (with_copyins [(8192, 2%nat)] (mkEffect 4 [] []))
       (inh_model inh_open_plain) = CheckReject.
Proof. vm_compute. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(* -------------------------------------------------------------------------
   The default and the setter
   ------------------------------------------------------------------------- *)

(** [State.mkProcInput] fills the list with the literal [[]]
    ([State.mkProcInput_inherited_fds]); THE CONTROL is the setter, whose
    list is the one it is given. *)
Example inherited_default_is_empty :
  in_inherited_fds inh_plain_launch = []
  /\ in_inherited_fds inh_key_launch <> [].
Proof.
  split; [reflexivity|].
  unfold inh_key_launch. rewrite in_inherited_fds_with_inherited_fds.
  discriminate.
Qed.

(* -------------------------------------------------------------------------
   Validity: numbers from 3, strictly increasing, below the ceiling
   ------------------------------------------------------------------------- *)

Example inherited_fds_ok_cases :
  inherited_fds_ok [(3, []); (2147483583, [])] = true
  (* the launch's own channel 2 *)
  /\ inherited_fds_ok [(2, [])] = false
  (* a repeated number *)
  /\ inherited_fds_ok [(4, []); (4, [])] = false
  (* a decreasing pair *)
  /\ inherited_fds_ok [(5, []); (4, [])] = false
  (* [Run.nr_open_max] itself *)
  /\ inherited_fds_ok [(2147483584, [])] = false.
Proof. repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity. Qed.

(* -------------------------------------------------------------------------
   The pin: [Run.valid_input] is the plain launch, [Run.valid_input_inherited]
   the keyed one
   ------------------------------------------------------------------------- *)

Example inherited_plain_launch_valid : valid_input inh_plain_launch.
Proof. exact demo_input_valid. Qed.

Example inherited_key_launch_not_valid_input : ~ valid_input inh_key_launch.
Proof.
  intro H. apply valid_input_no_inherited in H.
  unfold inh_key_launch in H. rewrite in_inherited_fds_with_inherited_fds in H.
  discriminate H.
Qed.

Example inherited_key_launch_valid_inherited : valid_input_inherited inh_key_launch.
Proof.
  unfold inh_key_launch.
  apply valid_input_inherited_with_inherited_fds;
    [exact demo_input_valid | vm_compute; reflexivity].
Qed.

(* -------------------------------------------------------------------------
   The kind: every other call on a key declines, close and F_GETFD answer
   ------------------------------------------------------------------------- *)

Example inherited_key_other_calls_decline :
  (* write(3, 4096, 1) *)
  check_syscall
    (mkInput 64 [3; 4096; 1; 0; 0; 0]
       (fun a => if bv_eqb a 4096 then Some 122 else None) (fun _ => None))
    (with_copyins [(4096, 1%nat)] (mkEffect 1 [] [])) (inh_model inh_key_launch)
  = CheckUnmodeled
  (* lseek(3, 0, SEEK_SET) *)
  /\ check_syscall (mkInput 62 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) (inh_model inh_key_launch) = CheckUnmodeled
  (* fstat(3, 4096) *)
  /\ check_syscall (mkInput 80 [3; 4096; 0; 0; 0; 0] (fun _ => None) inh_wmem)
       (mkEffect 0 [] []) (inh_model inh_key_launch) = CheckUnmodeled.
Proof. repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity. Qed.

Example inherited_key_close_frees_the_slot :
  match check_syscall (mkInput 57 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
          (mkEffect 0 [] []) (inh_model inh_key_launch) with
  | CheckOk m [] => fd_lookup (m_fds m) 3 = None
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** THE CONTROL: [F_GETFD] (1) reads the table's close-on-exec bit, which
    the launch leaves clear, as it does for every kind. *)
Example inherited_key_getfd_answers :
  check_syscall (mkInput 25 [3; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) (inh_model inh_key_launch)
  = CheckOk (inh_model inh_key_launch) []
  /\ check_syscall (mkInput 25 [3; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 1 [] []) (inh_model inh_key_launch) = CheckReject.
Proof. split; check_eq. Qed.

(* -------------------------------------------------------------------------
   The clone gate
   ------------------------------------------------------------------------- *)

(** The namespace flag word: SIGCHLD | CLONE_NEWNS | CLONE_NEWUSER |
    CLONE_NEWPID | CLONE_NEWNET | CLONE_NEWIPC | CLONE_NEWUTS. *)
Definition inh_ns_clone_flags : word :=
  Z_to_bv 64 (SIGCHLD + CLONE_NEWNS + CLONE_NEWUSER + CLONE_NEWPID
              + CLONE_NEWNET + CLONE_NEWIPC + CLONE_NEWUTS).

Definition inh_clone_plain : Model :=
  with_fds [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2)] clone_case_model.

Definition inh_clone_key : Model :=
  with_fds (fd_insert (m_fds inh_clone_plain) 3
              (FdOpaque (OInherited (Some (inh_key, 0))))) inh_clone_plain.

(** A caller that holds a key with its offset: the child would share the
    description's offset ([dup_fd], fs/file.c, v6.18.46), which the
    model holds in the caller's entry alone, so both words decline. *)
Example inherited_key_clone_declines :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] []) inh_clone_key
  = CheckUnmodeled
  /\ check_syscall (clone_in inh_ns_clone_flags) (mkEffect 4242 [] []) inh_clone_key
     = CheckUnmodeled.
Proof. split; vm_compute; reflexivity. Qed.

(** THE CONTROL: the same clones without the key answer the pid. *)
Example inherited_no_key_clone_answers :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] []) inh_clone_plain
  = CheckOk (with_child (Z_to_bv 64 4242) inh_clone_plain) []
  /\ check_syscall (clone_in inh_ns_clone_flags) (mkEffect 4242 [] []) inh_clone_plain
     = CheckOk (with_child (Z_to_bv 64 4242) inh_clone_plain) [].
Proof. split; check_eq. Qed.
