/* forkwait -- the multi-process pathfinder for LinuxProcessSem.Procs.
 *
 * Static riscv64, no libc, no startup files.  It calls
 *   clone(SIGCHLD, 0, 0, 0, 0)
 * the child calls exit_group(7), and the parent calls
 *   wait4(-1, &status, 0, NULL)
 * then exit_group(status >> 8).  Every path exits 7, so the statement's
 * allowed-exit set is [7].
 *
 * The register shape of the clone is the one SYSCALL_DEFINE5(clone) reads on
 * riscv64, which selects CONFIG_CLONE_BACKWARDS (arch/riscv/Kconfig):
 *   a0 = flags, a1 = newsp, a2 = parent_tidptr, a3 = tls, a4 = child_tidptr.
 * The flag word is the bare SIGCHLD (17) that
 * LinuxProcessSem.Sys.Kernel.Fork.clone_fork_flags_b admits -- a child that
 * shares nothing.  newsp = 0 means the child keeps the parent's stack
 * pointer, which it never uses: it exits at once.
 *
 * The `bltz` arm handles the injected errnos of Fork.clone_errnos
 * (EAGAIN, ENOMEM, EMFILE, EACCES).  They are suppressed at
 * Run.forced_only_cfg, which is the environment the released
 * `halts_within_budget` shape fixes, so that arm is unreachable there; it is
 * kept so the program is also correct at Run.may_fail_cfg.
 *
 * status is 7 << 8 = 1792 (kernel/exit.c:1131, Linux v6.18.46: exit_group
 * passes (error_code & 0xff) << 8 to do_group_exit).  It is positive, so the
 * sign extension of `lw` changes nothing and `srli` recovers 7.
 */

	.section .text
	.globl _start
	.type _start, @function

_start:
	li	a0, 17			/* SIGCHLD */
	li	a1, 0			/* newsp */
	li	a2, 0			/* parent_tidptr */
	li	a3, 0			/* tls */
	li	a4, 0			/* child_tidptr */
	li	a7, 220			/* __NR_clone */
	ecall
	bltz	a0, .Lfail		/* an errno: exit 7 too */
	beqz	a0, .Lchild		/* a0 == 0 only in the child */

.Lparent:
	addi	sp, sp, -16
	li	a0, -1			/* upid = -1: any child */
	mv	a1, sp			/* &status */
	li	a2, 0			/* options = 0: BLOCKING */
	li	a3, 0			/* rusage = NULL */
	li	a7, 260			/* __NR_wait4 */
	ecall
	lw	a0, 0(sp)		/* the status word */
	srli	a0, a0, 8		/* WEXITSTATUS */
	li	a7, 94			/* __NR_exit_group */
	ecall

.Lchild:
	li	a0, 7
	li	a7, 94
	ecall

.Lfail:
	li	a0, 7
	li	a7, 94
	ecall

	.size _start, . - _start
