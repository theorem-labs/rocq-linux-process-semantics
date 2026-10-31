/* A test program for the vDSO clock path of the Rocq model.
 *
 * It calls clock_gettime(CLOCK_MONOTONIC, &ts) once.  In musl 1.2.6
 * (commit f21a9653, v1.2.6-20) the first call of clock_gettime runs
 * cgt_init (src/time/clock_gettime.c), which calls __vdsosym
 * (src/internal/vdso.c).  __vdsosym reads AT_SYSINFO_EHDR from the auxv
 * that __init_libc saved, walks the vDSO image there, and returns the
 * address of "__vdso_clock_gettime" with version "LINUX_4.15"
 * (arch/riscv64/syscall_arch.h, VDSO_CGT_SYM and VDSO_CGT_VER).  The
 * program then writes the eight bytes of ts.tv_sec to file descriptor 1
 * and exits with code 0.
 *
 * The program stays this small on purpose: each instruction of its trace
 * costs proof time.  It uses write and _exit, not printf, so that no
 * locale code and no stdio buffer is in the trace.
 */

#include <time.h>
#include <unistd.h>

int main(void)
{
	struct timespec ts;

	clock_gettime(CLOCK_MONOTONIC, &ts);
	write(1, &ts.tv_sec, 8);
	_exit(0);
}
