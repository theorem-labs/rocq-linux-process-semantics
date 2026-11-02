(** * LinuxProcessSem.Checks.ProcsPrivateFrame — a class-(A) call changes nothing a peer sees

    Not part of the trusted specification: QA on [Procs.multiproc_private_sysnos],
    in the sense of [Checks.Examples]'s header, under its first reason: the
    statements are universally quantified over configurations and steps.

    ** What this pins

    [Procs.multiproc_allowed] admits the class-(A) numbers while another
    entry lives.  The class rule ([Procs], above [multiproc_core_sysnos]) is
    a claim about each released spec; this file proves it.

    - [syscall_spec_private_shared]: every [Ok] outcome of the released spec
      at a class-(A) number leaves [m_fsys] and [m_io], the two slots
      [Procs.pe_cfg] splices from [shared], as it found them.  It is a
      [Forall] over [checked_table], as [VmMapsDisjoint]'s ledger invariant
      is, so an arm added to the class-(A) list without a lemma here fails
      the build by name.
    - [pstep_at_private_frame]: a [pstep_at] step of entry [p] with a
      class-(A) call pending leaves [pcfg_shared] and [pcfg_root] equal, and
      every other entry equal, except that a child of [p] loses its parent
      when the step halted [p] (the orphaning [Procs.absorb] does at exit;
      tkill, tgkill and rt_sigprocmask can kill the caller).
      [pstep_at_private_views]: so every other entry's VIEW ([pe_cfg]) is
      unchanged.  [pstep_at_private_wf]: the step keeps [pconfig_wf]
      ([Checks.ProcsWellFormed.pstep_at_preserves_wf]).
    - [pstep_x_at_private_frame]: the same for [Procs.pstep_x_at] wherever
      [Procs.ext_agrees] holds, through [Procs.pstep_x_at_agree_iff].
    - [peer_call_outside]: the pin.  A class-(C) call of an entry whose
      table has another entry takes [pstep_outside], and no step of that
      entry has a successor.
    - [multiproc_partition]: the core, class-(A), class-(B) and class-(C)
      lists together are exactly [Specs.modeled_sysnos].

    Class (B) is [Checks.ProcsSharedFrame]'s. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Signal.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint ProcsWellFormed.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel Require Import Signal.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(* =========================================================================
   The two slots the core splices
   ========================================================================= *)

(** The part of a model [Procs.pe_cfg] takes from [shared]. *)
Definition sh_of (m : Model) : FsState * IoState := (m_fsys m, m_io m).

(** The checker cascade of [VmMapsDisjoint]'s frame proofs ([vm_step]),
    finished for this goal.  Every setter rebuilds its own subsystem record
    and carries the rest across, so [sh_of] of any stack of them is [sh_of]
    of the base by conversion. *)

Lemma check_efault_or_sh : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof. intros fb eff m m' evs H. unfold check_efault_or in H. repeat vm_step H; reflexivity. Qed.

Lemma check_sigpipe_write_sh : forall eff m m' evs,
  check_sigpipe_write eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros eff m m' evs H. unfold check_sigpipe_write in H.
  apply check_ret_only_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); reflexivity.
Qed.

Lemma check_sigpipe_writev_sh : forall reads eff m m' evs,
  check_sigpipe_writev reads eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros reads eff m m' evs H. unfold check_sigpipe_writev in H.
  apply check_ret_only_copyins_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); reflexivity.
Qed.

Lemma check_readv_gap_sh : forall m' evs,
  check_readv_gap = CheckOk m' evs -> False.
Proof. intros m' evs H. unfold check_readv_gap in H. discriminate. Qed.

Lemma check_open_result_sh : forall eff m mk m' evs,
  (forall fd, sh_of (mk fd) = sh_of m) ->
  check_open_result eff m mk = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_open_result, check_new_fd_result in H.
  repeat vm_step H; try apply Hmk; reflexivity.
Qed.

Ltac sh_done H :=
  first
  [ apply check_efault_or_sh in H; exact H
  | apply check_sigpipe_write_sh in H; exact H
  | apply check_sigpipe_writev_sh in H; exact H
  | elim (check_readv_gap_sh _ _ H)
  | (eapply check_open_result_sh in H;
     [exact H | intros; reflexivity]) ].

Ltac sh_frame2 H :=
  repeat (vm_step H || sh_done H); try reflexivity.

Lemma check_getcwd_sh : forall size eff m m' evs,
  check_getcwd size eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros size eff m m' evs H. unfold check_getcwd in H. sh_frame2 H.
Qed.

Lemma check_eventfd2_sh : forall flags eff m m' evs,
  check_eventfd2 flags eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros flags eff m m' evs H.
  unfold check_eventfd2, check_new_fd_result in H. sh_frame2 H.
Qed.

Lemma check_epoll_create1_sh : forall flags32 eff m m' evs,
  check_epoll_create1 flags32 eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros flags32 eff m m' evs H. unfold check_epoll_create1 in H. sh_frame2 H.
Qed.

Lemma check_epoll_ctl_sh : forall i epfd op32 tfd event eff m m' evs,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i epfd op32 tfd event eff m m' evs H.
  unfold check_epoll_ctl in H. sh_frame2 H.
Qed.

Lemma check_epoll_pwait_sh :
  forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
    = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H.
  unfold check_epoll_pwait in H. sh_frame2 H.
Qed.

Lemma check_dup_sh : forall oldfd eff m m' evs,
  check_dup oldfd eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros oldfd eff m m' evs H.
  unfold check_dup, check_dup_result in H. sh_frame2 H.
Qed.

Lemma check_dup3_sh : forall oldfd newfd flags eff m m' evs,
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros oldfd newfd flags eff m m' evs H. unfold check_dup3 in H. sh_frame2 H.
Qed.

Lemma check_fcntl_sh : forall fd cmd arg eff m m' evs,
  check_fcntl fd cmd arg eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros fd cmd arg eff m m' evs H. unfold check_fcntl in H. sh_frame2 H.
Qed.

Lemma check_ioctl_sh : forall fd req eff m m' evs,
  check_ioctl fd req eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof. intros fd req eff m m' evs H. unfold check_ioctl in H. sh_frame2 H. Qed.

Lemma check_close_sh : forall fd eff m m' evs,
  check_close fd eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof. intros fd eff m m' evs H. unfold check_close in H. sh_frame2 H. Qed.

Lemma check_pipe2_sh : forall i fildes flags eff m m' evs,
  check_pipe2 i fildes flags eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i fildes flags eff m m' evs H.
  unfold check_pipe2, pipe2_model in H. sh_frame2 H.
Qed.

Lemma check_getdents64_sh : forall fd count eff m m' evs,
  check_getdents64 fd count eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros fd count eff m m' evs H. unfold check_getdents64 in H. sh_frame2 H.
Qed.

Lemma check_pselect6_sh : forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold check_pselect6 in H. sh_frame2 H.
Qed.

Lemma check_ppoll_sh : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll in H. sh_frame2 H.
Qed.

Lemma check_fsync_sh : forall fd eff m m' evs,
  check_fsync fd eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof. intros fd eff m m' evs H. unfold check_fsync in H. sh_frame2 H. Qed.

Lemma check_timerfd_create_sh : forall clkid flags eff m m' evs,
  check_timerfd_create clkid flags eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros clkid flags eff m m' evs H.
  unfold check_timerfd_create in H. sh_frame2 H.
Qed.

Lemma check_capget_sh : forall i header dataptr eff m m' evs,
  check_capget i header dataptr eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i header dataptr eff m m' evs H.
  unfold check_capget, check_capget_copy in H. sh_frame2 H.
Qed.

Lemma check_capset_sh : forall i header data eff m m' evs,
  check_capset i header data eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i header data eff m m' evs H.
  unfold check_capset in H. sh_frame2 H.
Qed.

Lemma check_futex_sh : forall i uaddr op val utime eff m m' evs,
  check_futex i uaddr op val utime eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i uaddr op val utime eff m m' evs H.
  unfold check_futex, check_futex_wake_private, check_futex_wait_private in H.
  sh_frame2 H.
Qed.

Lemma check_set_robust_list_sh : forall len eff m m' evs,
  check_set_robust_list len eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros len eff m m' evs H.
  unfold check_set_robust_list in H. sh_frame2 H.
Qed.

Lemma check_clock_getres_sh : forall i clkid tp eff m m' evs,
  check_clock_getres i clkid tp eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold check_clock_getres, check_clock_getres_result in H. sh_frame2 H.
Qed.

Lemma check_sched_setscheduler_sh : forall i pid policy param eff m m' evs,
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i pid policy param eff m m' evs H.
  unfold check_sched_setscheduler in H. sh_frame2 H.
Qed.

Lemma check_sched_getaffinity_sh : forall len eff m m' evs,
  check_sched_getaffinity len eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros len eff m m' evs H. unfold check_sched_getaffinity in H. sh_frame2 H.
Qed.

Lemma check_sched_yield_sh : forall eff m m' evs,
  check_sched_yield eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros eff m m' evs H. unfold check_sched_yield in H. sh_frame2 H.
Qed.

Lemma check_sigaltstack_sh : forall i uss uoss eff m m' evs,
  check_sigaltstack i uss uoss eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i uss uoss eff m m' evs H.
  unfold check_sigaltstack in H. sh_frame2 H.
Qed.

Lemma check_rt_sigaction_sh : forall i sig act oact ss eff m m' evs,
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i sig act oact ss eff m m' evs H.
  unfold check_rt_sigaction in H. sh_frame2 H.
Qed.

Lemma check_setid_sh : forall get put user v eff m m' evs,
  check_setid get put user v eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros get put user v eff m m' evs H.
  unfold check_setid, check_setid_result in H. sh_frame2 H.
Qed.

Lemma check_setresid_sh : forall get put user r e sv eff m m' evs,
  check_setresid get put user r e sv eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros get put user r e sv eff m m' evs H.
  unfold check_setresid, check_setid_result in H. sh_frame2 H.
Qed.

Lemma check_getresid_sh : forall i get rp ep sp eff m m' evs,
  check_getresid i get rp ep sp eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i get rp ep sp eff m m' evs H.
  unfold check_getresid, check_ret_writes in H. sh_frame2 H.
Qed.

Lemma check_getgroups_sh : forall gidsetsize eff m m' evs,
  check_getgroups gidsetsize eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros gidsetsize eff m m' evs H. unfold check_getgroups in H. sh_frame2 H.
Qed.

Lemma check_setgroups_sh : forall i eff m m' evs,
  check_setgroups i eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros i eff m m' evs H. unfold check_setgroups in H. sh_frame2 H.
Qed.

Lemma check_gettimeofday_sh : forall i tv tz eff m m' evs,
  check_gettimeofday i tv tz eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i tv tz eff m m' evs H.
  unfold check_gettimeofday in H. sh_frame2 H.
Qed.

Lemma check_getid_sh : forall sel eff m m' evs,
  check_getid sel eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof. intros sel eff m m' evs H. unfold check_getid in H. sh_frame2 H. Qed.

Lemma check_socket_sh : forall domain type protocol eff m m' evs,
  check_socket domain type protocol eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros domain type protocol eff m m' evs H.
  unfold check_socket, check_new_fd_result, check_errno_or_list in H. sh_frame2 H.
Qed.

Lemma check_socketpair_sh : forall i family type protocol sv eff m m' evs,
  check_socketpair i family type protocol sv eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i family type protocol sv eff m m' evs H.
  unfold check_socketpair, check_socketpair_written, check_socketpair_faulted
    in H. sh_frame2 H.
Qed.

Lemma check_bind_sh : forall i fd addrp addrlen eff m m' evs,
  check_bind i fd addrp addrlen eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_bind, check_errno_or_success in H. sh_frame2 H.
Qed.

Lemma check_listen_sh : forall fd backlog eff m m' evs,
  check_listen fd backlog eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros fd backlog eff m m' evs H.
  unfold check_listen, check_errno_or_success, check_errno_only in H.
  sh_frame2 H.
Qed.

Lemma check_connect_sh : forall i fd addrp addrlen eff m m' evs,
  check_connect i fd addrp addrlen eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_connect in H. sh_frame2 H.
Qed.

Lemma check_getsockname_sh : forall fd eff m m' evs,
  check_getsockname fd eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros fd eff m m' evs H.
  unfold check_getsockname, check_getsockname_core in H. sh_frame2 H.
Qed.

Lemma check_getpeername_sh : forall fd eff m m' evs,
  check_getpeername fd eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros fd eff m m' evs H.
  unfold check_getpeername, check_getpeername_core in H. sh_frame2 H.
Qed.

Lemma check_send_on_socket_sh :
  forall pre acc fd sk total bs eff m m' evs,
  check_send_on_socket pre acc fd sk total bs eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros pre acc fd sk total bs eff m m' evs H.
  unfold check_send_on_socket in H. sh_frame2 H.
Qed.

Lemma check_recv_fd_answer_sh : forall fds fd eff m m' evs,
  check_recv_fd_answer fds fd eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros fds fd eff m m' evs H.
  unfold check_recv_fd_answer in H. sh_frame2 H.
Qed.

Lemma check_sendto_sh : forall i fd buf count flags addrp eff m m' evs,
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i fd buf count flags addrp eff m m' evs H.
  unfold check_sendto, check_access_ok_zero, check_send_on_socket in H.
  sh_frame2 H.
Qed.

Lemma check_recvfrom_sh : forall i fd buf size eff m m' evs,
  check_recvfrom i fd buf size eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i fd buf size eff m m' evs H.
  unfold check_recvfrom, check_access_ok_zero, check_recv_fd_answer in H.
  sh_frame2 H.
Qed.

Lemma check_setsockopt_sh : forall fd level optlen eff m m' evs,
  check_setsockopt fd level optlen eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros fd level optlen eff m m' evs H.
  unfold check_setsockopt, check_setsockopt_core in H. sh_frame2 H.
Qed.

Lemma check_getsockopt_sh : forall i fd level optlenp eff m m' evs,
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i fd level optlenp eff m m' evs H.
  unfold check_getsockopt, check_getsockopt_core in H. sh_frame2 H.
Qed.

Lemma check_shutdown_sh : forall fd how eff m m' evs,
  check_shutdown fd how eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros fd how eff m m' evs H.
  unfold check_shutdown, check_shutdown_core in H. sh_frame2 H.
Qed.

Lemma check_sendmsg_sh : forall i fd msgp flags eff m m' evs,
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i fd msgp flags eff m m' evs H.
  unfold check_sendmsg, check_send_on_socket in H. sh_frame2 H.
Qed.

Lemma check_recvmsg_sh : forall fd flags eff m m' evs,
  check_recvmsg fd flags eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros fd flags eff m m' evs H.
  unfold check_recvmsg, check_recv_fd_answer in H. sh_frame2 H.
Qed.

Lemma check_getrandom_sh : forall i buf cap flags eff m m' evs,
  check_getrandom i buf cap flags eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i buf cap flags eff m m' evs H.
  unfold check_getrandom, check_getrandom_zero in H. sh_frame2 H.
Qed.

Lemma check_close_range_sh : forall fd max_fd flags eff m m' evs,
  check_close_range fd max_fd flags eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros fd max_fd flags eff m m' evs H. unfold check_close_range in H.
  sh_frame2 H.
Qed.

Lemma check_madvise_sh : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros addr len advice [ret ws zs us cs ci] m m' evs H.
  unfold check_madvise in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [discriminate|].
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [|discriminate].
  destruct ws, us, cs, ci; try discriminate.
  dif H; [|discriminate]. injection H as <- <-. reflexivity.
Qed.

(** The memory-management arms build their post-models through the
    wrappers of [Sys.Mm]; two of them branch or recurse, so they get a
    lemma, and every other wrapper keeps [sh_of] by conversion. *)
Lemma sh_of_forget_vm_ranges : forall rs m, sh_of (forget_vm_ranges rs m) = sh_of m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma sh_of_with_brk_next : forall m req r, sh_of (with_brk_next m req r) = sh_of m.
Proof.
  intros m req r. unfold with_brk_next. cbv zeta.
  rewrite sh_of_forget_vm_ranges. reflexivity.
Qed.

Lemma sh_of_with_mmap_backing : forall flags a n m,
  sh_of (with_mmap_backing flags a n m) = sh_of m.
Proof.
  intros flags a n m. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma sh_of_with_mmap_replacement : forall flags a n m,
  sh_of (with_mmap_replacement flags a n m) = sh_of m.
Proof.
  intros flags a n m. unfold with_mmap_replacement.
  rewrite sh_of_with_mmap_backing. reflexivity.
Qed.

(** Split [H] on every [if] and [match] to a leaf, as [MmStepFrame] does. *)
Local Ltac mm_walk H :=
  repeat (cbv beta iota zeta in H;
          lazymatch type of H with
          | CheckOk _ _ = CheckOk _ _ => fail
          | _ => match type of H with
                 | context [match ?x with _ => _ end] => destruct x
                 end
          end);
  try discriminate H.

Local Ltac mm_leaf H :=
  injection H as <- <-;
  rewrite ?sh_of_with_mmap_backing, ?sh_of_with_mmap_replacement, ?sh_of_with_brk_next;
  reflexivity.

Lemma check_brk_sh : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros req [ret ws zs us cs ci] m m' evs H.
  unfold check_brk in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mmap_sh : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H.
  unfold check_mmap, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mremap_sh : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H.
  unfold check_mremap, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_munmap_sh : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H.
  unfold check_munmap, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mprotect_sh : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H.
  unfold check_mprotect, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.


Lemma sh_of_sigmask_deliver_model : forall new m,
  sh_of (sigmask_deliver_model new m) = sh_of m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    reflexivity.
Qed.

Lemma check_rt_sigprocmask_sh : forall i how nset oset ss eff m m' evs,
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs ->
  sh_of m' = sh_of m.
Proof.
  intros i how nset oset ss eff m m' evs H.
  unfold check_rt_sigprocmask in H.
  destruct (negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))) eqn:Hss;
    cbv beta iota zeta in H.
  { apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (w_is0 nset) eqn:Hn; cbv beta iota in H.
  { destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
    - apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _).
    - apply check_write_oset_ok_iff in H. now destruct H as (-> & _ & _ & _). }
  destruct (sigset_at (in_mem i) nset) as [raw|] eqn:Hr; cbv beta iota in H.
  2:{ apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (negb (how_valid how)) eqn:Hh; cbv beta iota zeta in H.
  { apply check_ret_only_copyins_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (_ & -> & _).
    now rewrite sh_of_sigmask_deliver_model. }
  unfold check_write_oset_copyins in H.
  destruct (check_write_oset i oset (m_sigmask m) (clear_copyins eff)
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m)
                               (sigmask_strip raw)) m))
    as [m2 evs2| |] eqn:Hcw; [|discriminate|discriminate].
  destruct (access_ranges_eqb (eff_copyins eff)
              [(nset, Z.to_nat NSIG_BYTES)]); [|discriminate].
  apply check_write_oset_ok_iff in Hcw. destruct Hcw as (-> & _ & _ & _).
  inversion H; subst. now rewrite sh_of_sigmask_deliver_model.
Qed.

Lemma check_tkill_sh : forall pid sig eff m m' evs,
  check_tkill pid sig eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros pid sig eff m m' evs H.
  unfold check_tkill, check_tkill_self, check_send_sigabrt in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _);
         reflexivity);
    inversion H; subst; autorewrite with model; reflexivity.
Qed.

Lemma check_tgkill_sh : forall tgid pid sig eff m m' evs,
  check_tgkill tgid pid sig eff m = CheckOk m' evs -> sh_of m' = sh_of m.
Proof.
  intros tgid pid sig eff m m' evs H.
  unfold check_tgkill, check_tkill_self, check_send_sigabrt in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _);
         reflexivity);
    inversion H; subst; autorewrite with model; reflexivity.
Qed.

(* =========================================================================
   Every class-(A) arm leaves the spliced slots alone
   ========================================================================= *)

(** What one dispatcher arm owes the core, as a property of the table entry:
    if its number is class (A), every answer it accepts keeps [sh_of]. *)
Definition arm_private_sh (c : CheckedArm) : Prop :=
  List.existsb (Z.eqb (ca_no c)) multiproc_private_sysnos = true ->
  forall i eff m m' evs, ca_check c i eff m = CheckOk m' evs -> sh_of m' = sh_of m.

(** Every arm discharges it: an arm whose number is not class (A) by
    computing its number, a class-(A) arm by its lemma above.  An arm added
    to the class-(A) list with no lemma reaches the last alternative, which
    names what to write. *)
Lemma checked_table_private_sh : Forall arm_private_sh checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_private_sh).
  all: unfold arm_private_sh; intros Hp i eff m m' evs H.
  all: first
    [ exfalso; clear H; vm_compute in Hp; discriminate Hp
    | autorewrite with arm_unfold in H;
      first
      [
        eapply check_getcwd_sh; eassumption
      | eapply check_eventfd2_sh; eassumption
      | eapply check_epoll_create1_sh; eassumption
      | eapply check_epoll_ctl_sh; eassumption
      | eapply check_epoll_pwait_sh; eassumption
      | eapply check_dup_sh; eassumption
      | eapply check_dup3_sh; eassumption
      | eapply check_fcntl_sh; eassumption
      | eapply check_ioctl_sh; eassumption
      | eapply check_close_sh; eassumption
      | eapply check_pipe2_sh; eassumption
      | eapply check_getdents64_sh; eassumption
      | eapply check_pselect6_sh; eassumption
      | eapply check_ppoll_sh; eassumption
      | eapply check_fsync_sh; eassumption
      | eapply check_timerfd_create_sh; eassumption
      | eapply check_capget_sh; eassumption
      | eapply check_capset_sh; eassumption
      | eapply check_futex_sh; eassumption
      | eapply check_set_robust_list_sh; eassumption
      | eapply check_clock_getres_sh; eassumption
      | eapply check_sched_setscheduler_sh; eassumption
      | eapply check_sched_getaffinity_sh; eassumption
      | eapply check_sched_yield_sh; eassumption
      | eapply check_tkill_sh; eassumption
      | eapply check_tgkill_sh; eassumption
      | eapply check_sigaltstack_sh; eassumption
      | eapply check_rt_sigaction_sh; eassumption
      | eapply check_rt_sigprocmask_sh; eassumption
      | eapply check_setid_sh; eassumption
      | eapply check_setresid_sh; eassumption
      | eapply check_getresid_sh; eassumption
      | eapply check_getgroups_sh; eassumption
      | eapply check_setgroups_sh; eassumption
      | eapply check_gettimeofday_sh; eassumption
      | eapply check_getid_sh; eassumption
      | eapply check_socket_sh; eassumption
      | eapply check_socketpair_sh; eassumption
      | eapply check_bind_sh; eassumption
      | eapply check_listen_sh; eassumption
      | eapply check_connect_sh; eassumption
      | eapply check_getsockname_sh; eassumption
      | eapply check_getpeername_sh; eassumption
      | eapply check_sendto_sh; eassumption
      | eapply check_recvfrom_sh; eassumption
      | eapply check_setsockopt_sh; eassumption
      | eapply check_getsockopt_sh; eassumption
      | eapply check_shutdown_sh; eassumption
      | eapply check_sendmsg_sh; eassumption
      | eapply check_recvmsg_sh; eassumption
      | eapply check_brk_sh; eassumption
      | eapply check_munmap_sh; eassumption
      | eapply check_mremap_sh; eassumption
      | eapply check_mmap_sh; eassumption
      | eapply check_mprotect_sh; eassumption
      | eapply check_madvise_sh; eassumption
      | eapply check_getrandom_sh; eassumption
      | eapply check_close_range_sh; eassumption
      | fail 2 "checked_table_private_sh has no case for this class-(A) arm: give its checker a *_sh lemma above and add it to the list" ] ].
Qed.

Lemma lookup_ca_no : forall t n c, lookup_ca t n = Some c -> ca_no c = n.
Proof.
  induction t as [|a t IH]; intros n c H; cbn [lookup_ca] in H; [discriminate H|].
  destruct (Z.eqb (ca_no a) n) eqn:E.
  - injection H as <-. apply Z.eqb_eq. exact E.
  - exact (IH n c H).
Qed.

(** THE SPEC FRAME: at a class-(A) number, every [Ok] outcome of the
    released spec keeps [m_fsys] and [m_io]. *)
Theorem syscall_spec_private_shared : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  List.existsb (Z.eqb (bv_unsigned (in_sysno i))) multiproc_private_sysnos = true ->
  sh_of m' = sh_of m.
Proof.
  intros i m eff m' evs H Hp. apply check_syscall_ok_iff in H.
  unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_private_sh as Hall. rewrite Forall_forall in Hall.
  refine (Hall c (lookup_ca_In _ _ _ Elk) _ i eff m m' evs H).
  rewrite (lookup_ca_no _ _ _ Elk). exact Hp.
Qed.

Lemma sh_of_materialize : forall m acc m'',
  materialize_model_accesses m acc = Some m'' -> sh_of m'' = sh_of m.
Proof.
  intros m acc m'' H. unfold materialize_model_accesses in H.
  destruct (materialize_accesses _ _ _ _ _); [injection H as <-; reflexivity | discriminate H].
Qed.

(** The released step at a class-(A) call keeps the two slots. *)
Lemma sstep_private_shared : forall segs cfg c evs c',
  multiproc_private c = true ->
  sstep_cfg segs cfg c evs (SNext c') -> sh_of (cfg_model c') = sh_of (cfg_model c).
Proof.
  intros segs cfg c evs c' Hp H.
  inversion H; subst; unfold multiproc_private in Hp; cbn [cfg_ms cfg_model] in Hp |- *.
  all: match goal with
       | Hs : ms_svc_pending ?s = None |- _ => rewrite Hs in Hp; discriminate Hp
       | Hs : ms_svc_pending ?s = Some _ |- _ => rewrite Hs in Hp
       end.
  all: match goal with
       | Hsp : syscall_spec (sys_input _ _ _) _ (Ok _ _ _) |- _ =>
           pose proof (syscall_spec_private_shared _ _ _ _ _ Hsp) as Hsh;
           cbn [in_sysno sys_input] in Hsh; specialize (Hsh Hp)
       end.
  all: first
    [ exact Hsh
    | match goal with
      | Hm : materialize_model_accesses _ _ = Some _ |- _ =>
          rewrite (sh_of_materialize _ _ _ Hm); exact Hsh
      end ].
Qed.

(* =========================================================================
   The step frame
   ========================================================================= *)

(** Another entry after the step: the same, or, when the step halted [p],
    a child of [p] with its parent cleared. *)
Definition orphaned_or_same (p : Pid) (f f' : ProcessEntry) : Prop :=
  f' = f \/ (pe_parent f = Some p /\ f' = with_parent f None).

Lemma look_in_replace_other : forall ps p e' q,
  q <> p -> look_in (replace_in ps p e') q = look_in ps q.
Proof.
  induction ps as [|[k x] r IH]; intros p e' q Hne; [reflexivity|].
  cbn [replace_in look_in fst snd].
  destruct (bv_eqb k p) eqn:Ekp.
  - apply bv_eqb_true_eq in Ekp. subst k. cbn [look_in fst snd].
    rewrite (pid_neq_eqb p q) by (intros Heq; apply Hne; symmetry; exact Heq).
    reflexivity.
  - cbn [look_in fst snd]. destruct (bv_eqb k q); [reflexivity|].
    apply IH. exact Hne.
Qed.

Lemma look_in_orphan : forall m p ps q,
  look_in (List.map (orphan_slot m p) ps) q
  = option_map (fun f => snd (orphan_slot m p (q, f))) (look_in ps q).
Proof.
  intros m p. induction ps as [|[k x] r IH]; intros q; [reflexivity|].
  cbn [List.map look_in]. rewrite orphan_slot_fst. cbn [fst snd].
  destruct (bv_eqb k q) eqn:E; [|apply IH].
  apply bv_eqb_true_eq in E. subst k. reflexivity.
Qed.

Lemma orphan_slot_orphaned : forall m p q f,
  orphaned_or_same p f (snd (orphan_slot m p (q, f))).
Proof.
  intros m p q f. unfold orphan_slot.
  destruct (m_halted m); [|left; reflexivity].
  unfold orphan_one. cbn [fst snd].
  match goal with |- context [if ?b then _ else _] => destruct b eqn:E end;
    [|left; reflexivity].
  right. apply andb_true_iff in E as [_ E].
  destruct (pe_parent f) as [r|] eqn:Ep; [|discriminate E].
  apply bv_eqb_true_eq in E. subst r. split; reflexivity.
Qed.

Lemma private_not_clone : forall c,
  clone_pending_b c = true -> multiproc_private c = false.
Proof.
  intros c H. unfold clone_pending_b, clone_sysno in H. unfold multiproc_private.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; [|discriminate H].
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; rewrite H; reflexivity.
Qed.

Lemma private_not_intercept : forall c,
  wait4_intercept_b c = true -> multiproc_private c = false.
Proof.
  intros c H. unfold wait4_intercept_b in H. unfold multiproc_private.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; [|discriminate H].
  apply andb_true_iff in H as [H _]. apply Z.eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma private_not_owned : forall P e,
  wait4_owned_b P e = true -> multiproc_private (pe_cfg (pcfg_shared P) e) = false.
Proof.
  intros P e H. destruct (wait4_owned_260 P e H) as (x8 & Hs & H260).
  unfold multiproc_private. cbn [cfg_ms pe_cfg]. rewrite Hs, H260. reflexivity.
Qed.

Lemma private_not_sync : forall P e,
  sync_pending_b P e = true -> multiproc_private (pe_cfg (pcfg_shared P) e) = false.
Proof.
  intros P e H. unfold sync_pending_b in H. unfold multiproc_private.
  cbn [cfg_ms pe_cfg]. destruct (ms_svc_pending (pe_ms e)) as [x8|]; [|discriminate H].
  apply andb_true_iff in H as [H _]. cbn [multiproc_synced_sysnos List.existsb] in H.
  apply orb_true_iff in H as [H|H];
    [|apply orb_true_iff in H as [H|H]; [|discriminate H]];
    apply Z.eqb_eq in H; rewrite H; reflexivity.
Qed.

(** THE FRAME.  A step of [p] at a class-(A) call keeps the shared state
    and the root, and every other entry, but for the orphaning of [p]'s
    children when the step halted [p]. *)
Theorem pstep_at_private_frame : forall segs cfg p P evs P' e,
  look P p = Some e ->
  multiproc_private (pe_cfg (pcfg_shared P) e) = true ->
  pstep_at segs cfg p P evs (PNext P') ->
  pcfg_shared P' = pcfg_shared P
  /\ pcfg_root P' = pcfg_root P
  /\ (forall q, q <> p ->
        match look P q, look P' q with
        | None, None => True
        | Some f, Some f' => orphaned_or_same p f f'
        | _, _ => False
        end).
Proof.
  intros segs cfg p P evs P' e Hl Hp H.
  destruct (pstep_next_cases _ _ _ _ _ _ H) as (e1 & Hl1 & Hpid & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-. subst p.
  destruct Hcases as
    [ (c' & Hs & _ & _ & ->)
    | [ (c' & q & _ & Hsucc & _)
      | [ (Hwt & _) | [ (Hwo & _) | (Hsy & _ & _) ] ] ] ].
  - pose proof (sstep_private_shared _ _ _ _ _ Hp Hs) as Hsh.
    unfold sh_of in Hsh. injection Hsh as Hf Hi.
    split; [|split; [reflexivity|]].
    + unfold absorb, shared_absorb. cbn [pcfg_shared].
      rewrite Hf, Hi. destruct (pcfg_shared P); reflexivity.
    + intros q Hne. unfold look, absorb. cbn [pcfg_procs].
      rewrite orphan_at_exit_map, look_in_orphan, look_in_replace_other by exact Hne.
      destruct (look_in (pcfg_procs P) q) as [f|]; cbn [option_map];
        [apply orphan_slot_orphaned | exact I].
  - rewrite (private_not_clone _ (clone_success_pending _ _ Hsucc)) in Hp. discriminate Hp.
  - rewrite (private_not_intercept _ Hwt) in Hp. discriminate Hp.
  - rewrite (private_not_owned _ _ Hwo) in Hp. discriminate Hp.
  - rewrite (private_not_sync _ _ Hsy) in Hp. discriminate Hp.
Qed.

(** So every other entry's VIEW is unchanged: [pe_cfg] reads [pe_ms] and
    [pe_model] and the shared state, and the orphaning writes [pe_parent]
    alone. *)
Corollary pstep_at_private_views : forall segs cfg p P evs P' e q f,
  look P p = Some e ->
  multiproc_private (pe_cfg (pcfg_shared P) e) = true ->
  pstep_at segs cfg p P evs (PNext P') ->
  q <> p -> look P q = Some f ->
  exists f', look P' q = Some f' /\ pe_cfg (pcfg_shared P') f' = pe_cfg (pcfg_shared P) f.
Proof.
  intros segs cfg p P evs P' e q f Hl Hp H Hne Hf.
  destruct (pstep_at_private_frame segs cfg p P evs P' e Hl Hp H) as (Hsh & _ & Hq).
  specialize (Hq q Hne). rewrite Hf in Hq.
  destruct (look P' q) as [f'|]; [|contradiction].
  exists f'. split; [reflexivity|]. rewrite Hsh.
  destruct Hq as [-> | (_ & ->)]; reflexivity.
Qed.

(** And the step keeps the table well formed. *)
Corollary pstep_at_private_wf : forall segs cfg p P evs P' e,
  pconfig_wf P ->
  look P p = Some e ->
  multiproc_private (pe_cfg (pcfg_shared P) e) = true ->
  pstep_at segs cfg p P evs (PNext P') ->
  pconfig_wf P' /\ pcfg_shared P' = pcfg_shared P.
Proof.
  intros segs cfg p P evs P' e Hwf Hl Hp H. split.
  - exact (pstep_at_preserves_wf segs cfg p P evs P' Hwf H).
  - exact (proj1 (pstep_at_private_frame segs cfg p P evs P' e Hl Hp H)).
Qed.

(** The extended relation, wherever it agrees with the core's. *)
Corollary pstep_x_at_private_frame : forall ext cenv segs cfg p P evs P' e,
  ext_agrees ext cenv segs P ->
  look P p = Some e ->
  multiproc_private (pe_cfg (pcfg_shared P) e) = true ->
  pstep_x_at ext cenv segs cfg p P evs (PNext P') ->
  pcfg_shared P' = pcfg_shared P
  /\ pcfg_root P' = pcfg_root P
  /\ (forall q, q <> p ->
        match look P q, look P' q with
        | None, None => True
        | Some f, Some f' => orphaned_or_same p f f'
        | _, _ => False
        end).
Proof.
  intros ext cenv segs cfg p P evs P' e Hag Hl Hp H.
  apply (pstep_at_private_frame segs cfg p P evs P' e Hl Hp).
  exact (proj1 (pstep_x_at_agree_iff ext cenv segs cfg p P evs (PNext P') Hag) H).
Qed.

(* =========================================================================
   The pin: what is not admitted still fails closed
   ========================================================================= *)

(** Class (C): the answer needs the peer, and the core does not give it. *)
Definition multiproc_peer_sysnos : list Z :=
  [32; 35; 80; 96; 156; 157; 160; 167; 172; 173; 178; 261]%Z.

Lemma not_admitted_sysno : forall n,
  List.existsb (Z.eqb n) multiproc_peer_sysnos = true ->
  List.existsb (Z.eqb n) multiproc_sysnos = false.
Proof.
  intros n H. apply List.existsb_exists in H as (k & Hin & Hk).
  apply Z.eqb_eq in Hk. subst k. cbn in Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity|]). destruct Hin.
Qed.

Lemma not_admitted_not_260 : forall n,
  List.existsb (Z.eqb n) multiproc_sysnos = false -> n <> 260%Z.
Proof. intros n H ->. discriminate H. Qed.

Lemma intercept_260 : forall c,
  wait4_intercept_b c = true ->
  exists x8, ms_svc_pending (cfg_ms c) = Some x8 /\ bv_unsigned x8 = 260%Z.
Proof.
  intros c H. unfold wait4_intercept_b in H.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; [|discriminate H].
  apply andb_true_iff in H as [H _]. apply Z.eqb_eq in H.
  exists x8. split; [reflexivity | exact H].
Qed.

(** A step to a successor passes the surface guard, or is one of the
    [wait4] arms, which need a pending 260. *)
Lemma pstep_next_allowed : forall segs cfg p P evs P',
  pstep_at segs cfg p P evs (PNext P') ->
  exists e, look P p = Some e /\
    ( multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true
      \/ wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true
      \/ wait4_owned_b P e = true
      \/ sync_pending_b P e = true ).
Proof.
  intros segs cfg p P evs P' H. inversion H; subst;
    (eexists; split; [eassumption|]); auto.
Qed.

(** THE PIN.  An entry whose table holds another entry, with a class-(C)
    call pending, takes [pstep_outside], and no step of it has a
    successor: the released spec never answers it.  getpid (172), whose
    released answer would pin a tid that can be the peer's pid, is one. *)
Theorem peer_call_outside : forall segs cfg P e x8,
  look P (pe_pid e) = Some e ->
  m_halted (pe_model e) = None ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  List.existsb (Z.eqb (bv_unsigned x8)) multiproc_peer_sysnos = true ->
  (1 < List.length (pcfg_procs P))%nat ->
  pstep_at segs cfg (pe_pid e) P [] PError
  /\ (forall evs P', ~ pstep_at segs cfg (pe_pid e) P evs (PNext P')).
Proof.
  intros segs cfg P e x8 Hl Hh Hs Hn Hlen.
  pose proof (not_admitted_sysno _ Hn) as Hna.
  assert (Hma : multiproc_allowed P (pe_cfg (pcfg_shared P) e) = false).
  { unfold multiproc_allowed. cbn [cfg_ms pe_cfg]. rewrite Hs, Hna.
    rewrite (proj2 (Nat.leb_gt _ _) Hlen). reflexivity. }
  split; [apply pstep_outside; assumption|].
  intros evs P' Hp.
  destruct (pstep_next_allowed _ _ _ _ _ _ Hp) as (e1 & Hl1 & Hor).
  rewrite Hl in Hl1. injection Hl1 as <-.
  destruct Hor as [Hma' | [Hwt | [Hwo | Hsy]]].
  - congruence.
  - destruct (intercept_260 _ Hwt) as (y & Hy & Hy260).
    cbn [cfg_ms pe_cfg] in Hy. rewrite Hs in Hy. injection Hy as <-.
    exact (not_admitted_not_260 _ Hna Hy260).
  - destruct (wait4_owned_260 _ _ Hwo) as (y & Hy & Hy260).
    rewrite Hs in Hy. injection Hy as <-.
    exact (not_admitted_not_260 _ Hna Hy260).
  - unfold sync_pending_b in Hsy. rewrite Hs in Hsy.
    apply andb_true_iff in Hsy as [Hsy _].
    unfold multiproc_sysnos in Hna. rewrite !List.existsb_app, Hsy in Hna.
    rewrite orb_true_r in Hna. discriminate Hna.
Qed.

(** The admitted lists and the class-(C) list are the modeled surface, each
    number once in all. *)
Lemma multiproc_partition :
  List.forallb (fun n => List.existsb (Z.eqb n)
                  (multiproc_sysnos ++ multiproc_peer_sysnos))
    modeled_sysnos = true
  /\ List.forallb (fun n => List.existsb (Z.eqb n) modeled_sysnos)
       (multiproc_sysnos ++ multiproc_peer_sysnos) = true
  /\ List.length (multiproc_sysnos ++ multiproc_peer_sysnos)
     = List.length modeled_sysnos.
Proof. split; [|split]; vm_compute; reflexivity. Qed.
