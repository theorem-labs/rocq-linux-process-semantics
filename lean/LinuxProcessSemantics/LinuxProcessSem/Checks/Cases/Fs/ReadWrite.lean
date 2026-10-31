import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.StreamLaws
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! rocq-cases: a71fd38a08571d519b9cfc5f66308db5c26da570
covers: file_write_emits_nothing -- file_write_emits_nothing
covers: read_after_eof_deterministic -- stdin_at_eof_is_zero
covers: read_eof_is_sticky -- stdin_at_eof_delivery_rejected, stdin_zero_with_input_rejected
covers: read_delivers_stream_prefix -- stdin_delivers_a_prefix_iff
covers: file_read_clamped_len -- file_read_clamped_len
unpinned: read_delivery_clamped -- symbolic over every fd kind, every model and every count: a proof over the relation, not a pin, which in Rocq walks `check_read_complete_ok` and the checker's arms; the arithmetic it rests on is ported (`rw_count_clamp_range`/`rw_count_clamp_word` in State/Readers.lean since PR #804, `file_read_clamped_len` here) but the Lean checker has no completeness lemma to walk; no fixture here holds more than MAX_RW_COUNT bytes, so the ceiling is not observable in this file
unpinned: read_ret_over_clamp_rejected -- symbolic over the file's data, and no fixture here holds more than MAX_RW_COUNT bytes, so the clamp's own value is not observable in this file; the refused full count is a lie because `vfs_read` (fs/read_write.c:566-567, v6.18.46) clamps the count to `MAX_RW_COUNT` (include/linux/fs.h:2838) before the read, so no kernel acknowledges a byte past it; `file_over_clamp_raw_count_rejected` is its instance at a count of MAX_RW_COUNT + 1 over the two-byte file, refusing the raw count as the return
covers: write_channel_outcome -- channel_write_delivers_a_prefix_iff, stderr_write_delivers_a_prefix_iff
covers: write_ab_events -- write_ab_events
covers: write_ab_short_delivery -- write_ab_short_delivery
covers: write_a_then_b_events -- write_a_then_b_events, write_a_delivers_iff, write_b_delivers_iff
covers: read_bad_fd_ebadf -- closed_fd_is_ebadf
covers: read_bad_fd_success_rejected -- closed_fd_success_rejected
covers: write_fd_truncates_to_32_bits -- write_fd_truncates_to_32_bits
covers: write_fd_high_bits_ebadf_rejected -- write_fd_high_bits_ebadf_rejected
covers: read_fd_truncates_to_32_bits -- fd_truncates_to_32_bits, fd_2_32_ebadf_rejected
covers: write_count_bound_declines_on_every_file_kind -- write_count_bound_declines_on_the_write_only_kind, write_count_at_the_bound_is_judged_on_the_write_only_kind, write_count_over_the_bound_at_a_mapped_buffer_is_judged, write_count_bound_decline_is_not_a_short_write
covers: write_range_boundary_pins_the_three_file_kinds -- write_range_boundary_pins_the_write_only_kind
covers: writev_aggregate_past_the_retired_bound_is_judged_by_every_file_kind -- writev_aggregate_past_the_retired_bound_is_judged_on_a_file, writev_aggregate_past_the_retired_bound_pipe_is_the_control, writev_arm_aggregate_past_the_retired_bound_is_imported
unpinned: rdwr_fd_refuses_ebadf_in_either_direction -- `read_spec` and `write_spec` decline `FdFileRW` (`Sys/Fs/ReadWrite.lean`'s header; `a17_rdwr_read_declines`, `a17_rdwr_write_declines`), where Rocq answers the transfer; both refused -EBADFs are lies because `vfs_read` (fs/read_write.c:556-557, v6.18.46) and `vfs_write` (fs/read_write.c:670-671) test `FMODE_READ` and `FMODE_WRITE`, both of which `OPEN_FMODE(O_RDWR)` (include/linux/fs.h:3981) sets; lands with the port of those arms
unpinned: rdwr_read_then_write_shares_one_offset -- `read_spec` and `write_spec` decline `FdFileRW` (`Sys/Fs/ReadWrite.lean`'s header), so there is no read for the write to follow; lands with the port of those arms
covers: create_write_updates_fs -- file_write_lands_at_the_offset_iff
covers: write_zero_len_past_eof_leaves_file_alone -- write_zero_len_past_eof_leaves_file_alone
covers: write_zero_len_rejects_zero_length_copyin -- write_zero_len_rejects_zero_length_copyin
covers: write_one_byte_past_eof_zero_fills -- write_one_byte_past_eof_zero_fills
covers: write_zero_len_within_file_is_a_noop -- write_zero_len_within_file_is_a_noop
unpinned: append_write_ignores_the_offset -- `write_spec` declines `FdFileA` (`Sys/Fs/ReadWrite.lean`'s header; `a17_append_write_declines`), where Rocq's arm writes at the end of the file; lands with the port of that arm
unpinned: append_zero_write_leaves_the_offset_alone -- `write_spec` declines `FdFileA` (`Sys/Fs/ReadWrite.lean`'s header), and `a17_append_write_declines` pins that decline on this very zero-length write; lands with the port of that arm
unpinned: append_write_at_llong_max_is_einval -- `write_spec` declines `FdFileA` (`Sys/Fs/ReadWrite.lean`'s header; `a17_append_write_declines`), where Rocq's arm writes at the end of the file; the refused answer 1 is a lie because `rw_verify_area` (fs/read_write.c:467-469, v6.18.46) answers -EINVAL when `(loff_t)(pos + count) < 0` on the fd's real position, before any byte moves; lands with the port of that arm
unpinned: append_write_access_ok_precedes_the_position_test -- `write_spec` declines `FdFileA` (`Sys/Fs/ReadWrite.lean`'s header; `a17_append_write_declines`), where Rocq's arm writes at the end of the file; the refused -EINVAL is a lie because `vfs_write` (fs/read_write.c:674-677, v6.18.46) runs `access_ok` and answers -EFAULT before it calls `rw_verify_area`; lands with the port of that arm
unpinned: non_append_write_at_the_same_offset_differs -- `write_spec` declines `FdFileA` (`Sys/Fs/ReadWrite.lean`'s header; `a17_append_write_declines`), where Rocq's arm writes at the end of the file, so there is no append-mode write to contrast with the write-only one; lands with the port of that arm
covers: writev_channel_outcome -- writev_stdout_delivers_a_prefix_iff, writev_ab_short_delivery, writev_ab_zero_delivery_rejected, t139_writev_stdout_empty_is_zero, t139_writev_stdout_empty_efault_refuted
covers: writev_outcome_is_write_outcome -- writev_outcome_is_write_outcome
covers: write_outcome_is_writev_outcome -- write_outcome_is_writev_outcome
covers: writev_two_iovecs_equals_one_write -- writev_two_iovecs_equals_one_write, writev_ab_events, writev_ab_over_total_rejected, writev_arm_gathers_and_records, writev_file_lands_at_the_offset_iff
covers: writev_wide_iovcnt_is_unmodeled -- writev_iovcnt_wide_count_declines, writev_raw_count_2_32_declines, writev_raw_count_2_32_einval_rejected, writev_count_1025_is_einval, writev_count_minus_one_is_einval, writev_arm_raw_count_truncates, writev_arm_raw_count_einval_rejected, writev_arm_raw_count_2_32_is_zero, writev_arm_count_over_max_is_einval
covers: writev_over_max_with_small_low32_is_unmodeled -- writev_raw_count_delivery_refuted, writev_raw_count_einval_rejected, writev_in_range_count_einval_rejected, t139_writev_wide_iov_max_any_memory_declines, t139_writev_wide_iov_max_declines, t139_writev_wide_iov_max_zero_refuted
covers: writev_import_range_fault_beats_the_gather -- writev_import_range_fault_beats_the_gather, writev_import_range_fault_short_write_rejected, writev_zero_length_past_top_is_efault, writev_zero_length_past_top_zero_rejected, writev_arm_import_range_fault_beats_the_gather, writev_arm_import_range_fault_short_write_rejected, writev_arm_zero_length_past_top_is_efault, writev_arm_zero_length_past_top_zero_rejected
covers: writev_at_llong_max_is_einval -- writev_at_llong_max_is_einval, writev_at_llong_max_write_rejected, writev_arm_at_llong_max_is_einval, writev_arm_at_llong_max_write_rejected
covers: writev_wide_count_over_rw_bytes_max_is_unmodeled -- writev_wide_count_over_rw_bytes_max_is_unmodeled, writev_wide_count_over_rw_bytes_max_old_answer_refuted
covers: writev_over_rw_bytes_max_total_is_judged -- writev_over_rw_bytes_max_total_is_judged, writev_over_rw_bytes_max_delivers_one_byte, writev_over_rw_bytes_max_einval_rejected, writev_arm_aggregate_past_the_retired_bound_is_imported, writev_arm_aggregate_past_the_retired_bound_einval_rejected
covers: readv_single_iovec_caps_before_access_ok -- readv_single_descriptor_caps_before_access_ok, readv_single_descriptor_efault_rejected, readv_array_path_checks_the_raw_length, readv_array_path_zero_rejected
covers: readv_huge_len_delivers_one_byte_without_unary_expansion -- readv_huge_descriptor_delivers_the_input, readv_huge_descriptor_efault_rejected, readv_huge_descriptor_on_a_file, readv_huge_descriptor_on_a_file_efault_rejected
covers: readv_huge_file_offset_is_bounded_by_file_length -- readv_huge_offset_is_eof
covers: readv_heap_iovec_boundary_fails_closed -- readv_eight_descriptors_are_judged, readv_eight_descriptors_enomem_rejected, readv_nine_descriptors_decline, readv_nine_descriptors_zero_rejected, readv_nine_descriptors_enomem_rejected, readv_iov_max_descriptors_decline, readv_raw_heap_count_declines, readv_raw_heap_count_einval_rejected
covers: readv_closed_fd_empty_first_entry_is_ebadf -- readv_closed_fd_empty_first_entry_is_ebadf, readv_closed_fd_empty_first_entry_zero_refuted, t139_readv_closed_iov_max_is_ebadf, t139_readv_closed_iov_max_unmodeled_refuted, t139_readv_closed_iov_max_zero_refuted, t139_readv_closed_nine_empty_is_ebadf, t139_readv_closed_nine_empty_unmodeled_refuted, t139_readv_closed_nine_empty_zero_refuted, t139_readv_closed_over_iov_max_declines, t139_readv_closed_over_iov_max_ebadf_refuted
covers: writev_closed_fd_empty_first_entry_is_ebadf -- writev_closed_fd_empty_first_entry_is_ebadf, writev_closed_fd_empty_first_entry_zero_refuted, t139_writev_closed_iov_max_is_ebadf, t139_writev_closed_iov_max_unmodeled_refuted, t139_writev_closed_iov_max_zero_refuted, t139_writev_closed_nine_empty_is_ebadf, t139_writev_closed_nine_empty_unmodeled_refuted, t139_writev_closed_nine_empty_zero_refuted, t139_writev_closed_over_iov_max_declines, t139_writev_closed_over_iov_max_ebadf_refuted
covers: readv_wide_iovcnt_is_unmodeled -- readv_iovcnt_wide_count_declines, readv_count_one_at_eof_is_zero, readv_second_descriptor_unreadable_is_efault, readv_second_descriptor_unreadable_zero_rejected
covers: readv_over_max_with_small_low32_is_unmodeled -- readv_iovcnt_wide_count_declines, readv_raw_count_over_max_einval_rejected
covers: readv_write_only_fd_unreadable_array_is_unmodeled -- readv_stdout_declines_before_import, readv_stdout_efault_rejected, readv_write_only_file_declines_before_the_band, readv_pipe_write_end_declines, readv_devnull_write_only_declines
covers: readv_zero_prefix_then_bad_base_is_efault_on_a_file -- readv_file_zero_prefix_then_bad_base_is_efault, readv_file_zero_prefix_zero_rejected, readv_file_eisdir_rejected
covers: readv_directory_never_consults_the_destination -- readv_dir_never_consults_the_destination, readv_dir_zero_rejected, readv_dir_later_null_efault_rejected, readv_dir_writable_first_then_null_is_eisdir
covers: readv_directory_import_range_fault_beats_eisdir -- readv_dir_import_range_fault_beats_eisdir, readv_dir_import_range_fault_eisdir_rejected
covers: readv_unreadable_base_faults_before_the_sign_test -- readv_unreadable_base_faults_before_the_sign_test, readv_unreadable_base_einval_rejected
covers: readv_at_llong_max_is_einval_not_eof -- readv_at_llong_max_is_einval, readv_at_llong_max_zero_rejected, readv_below_llong_max_is_eof, read_at_llong_max_answers_zero_divergence, readv_file_zero_aggregate_at_llong_max_is_zero, readv_file_zero_aggregate_at_llong_max_einval_rejected
covers: partial_destination_on_a_pipe_declines -- readv_stdin_partial_destination_declines, readv_stdin_partial_destination_short_read_rejected, readv_stdin_full_delivery
covers: lseek_channel_espipe -- lseek_channel_espipe
covers: lseek_channel_bad_whence_is_einval_not_espipe -- lseek_channel_bad_whence_is_einval, lseek_channel_bad_whence_espipe_rejected
covers: lseek_channel_seek_hole_is_espipe -- lseek_channel_seek_hole_is_espipe
covers: lseek_seek_data_on_a_file_is_unmodeled -- lseek_seek_data_on_a_file_is_unmodeled, lseek_seek_hole_on_a_file_is_unmodeled, lseek_channel_seek_hole_is_espipe, lseek_file_seek_end_reports_the_size
covers: lseek_whence_high_bits_einval_rejected -- lseek_whence_high_bits_is_seek_end, lseek_whence_high_bits_einval_rejected
covers: lseek_bad_fd_beats_a_bad_whence -- lseek_bad_fd_beats_a_bad_whence, lseek_bad_fd_einval_rejected
covers: bit31_is_part_of_the_32_bit_arguments -- lseek_bit31_whence_is_einval, lseek_bit31_whence_seek_end_rejected, write_bit31_fd_is_ebadf, ioctl_bit31_fd_is_closed, ioctl_bit31_fd_enotty_rejected, ioctl_bit31_request_declines
covers: read_channel_eintr_rejected -- stdin_eintr_rejected, stdin_one_byte_delivered
covers: write_channel_eintr_rejected -- write_channel_eintr_rejected
covers: write_channel_epipe_rejected -- write_channel_epipe_rejected
covers: file_write_short_rejected -- file_write_short_rejected
covers: pread64_leaves_the_model_alone -- pread64_leaves_the_model_alone
covers: pread64_urandom_advances_the_stream -- pread64_urandom_advances_the_stream
covers: pread64_pipe_end_is_espipe -- pread64_pipe_end_is_espipe, pread64_pipe_write_end_is_espipe, pread64_pipe_write_end_rejects_ebadf
covers: pwrite64_negative_pos_precedes_the_descriptor -- pwrite64_negative_pos_precedes_the_descriptor
covers: pwrite64_negative_pos_rejects_ebadf -- pwrite64_negative_pos_on_a_closed_fd_is_einval, pwrite64_negative_pos_rejects_ebadf
covers: pwrite64_writes_at_the_named_position -- pwrite64_writes_at_the_named_position, pwrite64_short_return_rejected
covers: pwrite64_over_rw_bytes_max_is_judged -- pwrite64_over_rw_bytes_max_is_judged, pwrite64_over_rw_bytes_max_short_rejected
covers: pwrite64_copyin_clamped -- pwrite64_copyin_clamped
covers: pipe_read_over_rw_bytes_max_is_judged -- pipe_read_over_rw_bytes_max_is_judged, pipe_read_over_rw_bytes_max_short_rejected
covers: pipe_write_empty_enomem_unchanged -- pipe_write_empty_enomem_unchanged
covers: pipe_write_nonempty_enomem_rejected -- pipe_write_nonempty_enomem_rejected
covers: pipe_write_empty_enomem_copyin_rejected -- pipe_write_empty_enomem_copyin_rejected
covers: pipe_write_empty_delivery -- pipe_write_empty_delivery
covers: pipe_write_nonempty_delivery -- pipe_write_nonempty_delivery
covers: pipe_write_drained_enomem_unchanged -- pipe_write_into_a_drained_pipe
covers: pipe_write_drained_delivery -- pipe_write_into_a_drained_pipe
covers: writev_stdin_alias_is_ebadf -- writev_stdin_alias_is_ebadf
covers: writev_urandom_is_ebadf -- writev_urandom_is_ebadf
covers: writev_devnull_read_only_is_ebadf -- writev_devnull_read_only_is_ebadf
covers: writev_read_only_file_is_ebadf -- writev_read_only_file_is_ebadf
covers: writev_directory_is_ebadf -- writev_directory_is_ebadf
covers: writev_pipe_read_end_is_ebadf -- writev_pipe_read_end_is_ebadf
covers: writev_stdin_channel_is_ebadf -- writev_stdin_channel_is_ebadf
covers: readv_stdout_is_ebadf_before_import -- readv_stdout_is_ebadf_before_import
covers: readv_stderr_is_ebadf -- readv_stderr_is_ebadf
covers: readv_devnull_write_only_is_ebadf -- readv_devnull_write_only_is_ebadf
covers: readv_pipe_write_end_is_ebadf -- readv_pipe_write_end_is_ebadf
covers: t139_writev_open_high_empty_is_unmodeled -- t139_writev_open_high_empty_is_unmodeled
covers: t139_writev_open_high_empty_ebadf_is_not_ok -- t139_writev_open_high_empty_ebadf_is_not_ok
covers: t139_readv_open_high_empty_is_unmodeled -- t139_readv_open_high_empty_is_unmodeled
covers: t139_readv_open_high_empty_ebadf_is_not_ok -- t139_readv_open_high_empty_ebadf_is_not_ok
covers: t139_writev_open_eight_empty_is_ebadf -- t139_writev_open_eight_empty_is_ebadf
covers: t139_readv_open_eight_empty_is_ebadf -- t139_readv_open_eight_empty_is_ebadf
covers: t139_writev_open_nine_empty_is_unmodeled -- t139_writev_open_nine_empty_is_unmodeled
covers: t139_writev_open_nine_empty_ebadf_is_not_ok -- t139_writev_open_nine_empty_ebadf_is_not_ok
covers: t139_writev_open_uncapped_later_is_unmodeled -- t139_writev_open_uncapped_later_is_unmodeled
covers: t139_writev_open_uncapped_later_ebadf_is_not_ok -- t139_writev_open_uncapped_later_ebadf_is_not_ok
covers: t139_writev_open_file_high_empty_is_unmodeled -- t139_writev_open_file_high_empty_is_unmodeled
covers: t139_writev_open_file_high_empty_ebadf_is_not_ok -- t139_writev_open_file_high_empty_ebadf_is_not_ok
covers: t139_writev_open_file_nine_empty_is_unmodeled -- t139_writev_open_file_nine_empty_is_unmodeled
covers: t139_writev_open_file_nine_empty_ebadf_is_not_ok -- t139_writev_open_file_nine_empty_ebadf_is_not_ok
covers: t139_writev_open_file_uncapped_later_is_unmodeled -- t139_writev_open_file_uncapped_later_is_unmodeled
covers: t139_writev_open_file_uncapped_later_ebadf_is_not_ok -- t139_writev_open_file_uncapped_later_ebadf_is_not_ok
covers: t139_writev_open_dir_high_empty_is_unmodeled -- t139_writev_open_dir_high_empty_is_unmodeled
covers: t139_writev_open_dir_high_empty_ebadf_is_not_ok -- t139_writev_open_dir_high_empty_ebadf_is_not_ok
covers: t139_writev_open_dir_nine_empty_is_unmodeled -- t139_writev_open_dir_nine_empty_is_unmodeled
covers: t139_writev_open_dir_nine_empty_ebadf_is_not_ok -- t139_writev_open_dir_nine_empty_ebadf_is_not_ok
covers: t139_writev_open_dir_uncapped_later_is_unmodeled -- t139_writev_open_dir_uncapped_later_is_unmodeled
covers: t139_writev_open_dir_uncapped_later_ebadf_is_not_ok -- t139_writev_open_dir_uncapped_later_ebadf_is_not_ok
covers: t139_writev_open_urandom_high_empty_is_unmodeled -- t139_writev_open_urandom_high_empty_is_unmodeled
covers: t139_writev_open_urandom_high_empty_ebadf_is_not_ok -- t139_writev_open_urandom_high_empty_ebadf_is_not_ok
covers: t139_writev_open_urandom_nine_empty_is_unmodeled -- t139_writev_open_urandom_nine_empty_is_unmodeled
covers: t139_writev_open_urandom_nine_empty_ebadf_is_not_ok -- t139_writev_open_urandom_nine_empty_ebadf_is_not_ok
covers: t139_writev_open_urandom_uncapped_later_is_unmodeled -- t139_writev_open_urandom_uncapped_later_is_unmodeled
covers: t139_writev_open_urandom_uncapped_later_ebadf_is_not_ok -- t139_writev_open_urandom_uncapped_later_ebadf_is_not_ok
covers: t139_writev_open_devnull_ro_high_empty_is_unmodeled -- t139_writev_open_devnull_ro_high_empty_is_unmodeled
covers: t139_writev_open_devnull_ro_high_empty_ebadf_is_not_ok -- t139_writev_open_devnull_ro_high_empty_ebadf_is_not_ok
covers: t139_writev_open_devnull_ro_nine_empty_is_unmodeled -- t139_writev_open_devnull_ro_nine_empty_is_unmodeled
covers: t139_writev_open_devnull_ro_nine_empty_ebadf_is_not_ok -- t139_writev_open_devnull_ro_nine_empty_ebadf_is_not_ok
covers: t139_writev_open_devnull_ro_uncapped_later_is_unmodeled -- t139_writev_open_devnull_ro_uncapped_later_is_unmodeled
covers: t139_writev_open_devnull_ro_uncapped_later_ebadf_is_not_ok -- t139_writev_open_devnull_ro_uncapped_later_ebadf_is_not_ok
covers: t139_writev_open_pipe_read_high_empty_is_unmodeled -- t139_writev_open_pipe_read_high_empty_is_unmodeled
covers: t139_writev_open_pipe_read_high_empty_ebadf_is_not_ok -- t139_writev_open_pipe_read_high_empty_ebadf_is_not_ok
covers: t139_writev_open_pipe_read_nine_empty_is_unmodeled -- t139_writev_open_pipe_read_nine_empty_is_unmodeled
covers: t139_writev_open_pipe_read_nine_empty_ebadf_is_not_ok -- t139_writev_open_pipe_read_nine_empty_ebadf_is_not_ok
covers: t139_writev_open_pipe_read_uncapped_later_is_unmodeled -- t139_writev_open_pipe_read_uncapped_later_is_unmodeled
covers: t139_writev_open_pipe_read_uncapped_later_ebadf_is_not_ok -- t139_writev_open_pipe_read_uncapped_later_ebadf_is_not_ok
covers: t139_readv_open_nine_empty_is_unmodeled -- t139_readv_open_nine_empty_is_unmodeled
covers: t139_readv_open_nine_empty_ebadf_is_not_ok -- t139_readv_open_nine_empty_ebadf_is_not_ok
covers: t139_readv_open_uncapped_later_is_unmodeled -- t139_readv_open_uncapped_later_is_unmodeled
covers: t139_readv_open_uncapped_later_ebadf_is_not_ok -- t139_readv_open_uncapped_later_ebadf_is_not_ok
covers: t139_readv_closed_high_empty_is_ebadf -- t139_readv_closed_high_empty_is_ebadf
covers: t139_writev_closed_high_empty_is_ebadf -- t139_writev_closed_high_empty_is_ebadf
-/

/-! # Checks.Cases.Fs.ReadWrite — what each of `read`, `write`, `readv`, `writev`, `lseek`, `pread64` and `pwrite64` admits, read off against Linux

Worked examples over `Sys.Fs.ReadWrite.read_spec`,
`Sys.Fs.ReadWrite.write_spec`, `readv_spec`, `writev_spec`, `lseek_spec`,
`pread64_spec` and `pwrite64_spec` — the `read` (63), `write` (64),
`readv` (65), `writev` (66), `lseek` (62), `pread64` (67) and `pwrite64`
(68) parts of the twin of
`theories/LinuxProcessSem/Checks/Cases/Fs/ReadWrite.v`, in the order of
that file's register above.  Not part of the trusted
specification: this file is QA on the definitions, written to be READ, and
every claim in it is a claim about what the kernel does, with the citation
beside it.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f), each
opened there.

HOW THESE ARE STATED.  A pin of one call goes through the dispatcher —
`syscall_spec` on a `SyscallInput` numbered 29 or 62 to 68 — so that the
table's `fd32` narrowing, and `lseek`'s `whence32`, are under test with
the arm, as Rocq's `check_syscall (mkInput 63 …)` cases have it.  (Pins
on a helper or fixture — `lseek_base`, `lseek_dest`, `ppos_einvalb`,
`rw_pos_einvalb`, `append_new_pos`, `modeled_file_gap`, `writev_file_arm`
and `readv_imported` among them — and the symbolic statements over every
fd, model and input, stated on `pread64_spec` / `pwrite64_spec`
directly, are the exception.)  A decision is pinned twice: an `iff` over
EVERY outcome `o`, which fixes the admitted answer and refuses every
other one, `Unmodeled`
included; and a refutation of the concrete answer a wrong model or a lying
kernel would give — the errno of the neighbouring check, the 0 of a
short-circuit that is not there, the byte a stream never held, the count
of a byte that was never read, the delivery a dead reader never saw.
Where a supported implementation gives an answer the arm does not yet
accept — qemu-user's -EFAULT ahead of Linux's order, or a filesystem's
smaller `s_maxbytes` — the pin is one-way instead, admitting Linux's answer
and saying why, since an `iff` would pin that refusal; its refutation, if
any, names an answer no implementation gives.  Most
close by `sys_norm` / `sys_refute`; the symbolic ones open the spec's gates
by hand (the whole-surface section says how).

THE INPUT'S BYTES ARE SYMBOLIC.  Where a pin states a post-state holding a
stream — the input after a delivery, a connection's script after one — the
stream's bytes are universally quantified (`hello b c d e f`,
`NCons b (NCons c NFin)`).  A closed stream is a function-and-proof
structure that `sys_norm`'s ground pass evaluates to a lambda no
`decide` can compare with `IEof`'s; a stream over variables is rewritten
by the `stream_take` / `net_take` equations of `StreamLaws` instead and
meets the claimed remainder syntactically.  It is also the stronger
statement: the read delivers the INPUT's bytes, whatever they are.  A
refutation of WRONG bytes needs two bytes that differ, so those few pins
use concrete ones; nothing about their post-state is claimed.

THE SOURCE BYTES ARE CONCRETE.  A write reads user memory and the
model's answer is a function of what is readable there, so each pin
names a readable view (`mem_ab`, `mem_hole`, `mem_first n`) and the
bytes the view holds; where the channel arm CHOOSES how much of the
readable prefix to deliver, the `iff` quantifies over that choice and
the refutations refuse a delivery that is not a prefix.

WHAT IS A GAP AND WHAT IS A CHOICE.  Every `Unmodeled` below is one of the
following, and each pin's docstring says which.  On the `read` half: a
partially writable destination, where Linux's count is the copy routine's
rounded progress (a coverage gap); a socket or pipe read whose range
leaves the address space at a count past `Uaccess.rw_bytes_max`, where
Linux answers -EFAULT and the model carries no -EFAULT arm
(bugs/write-out-of-range-short-write.md); and an empty pipe with a live
writer, where Linux BLOCKS and the model has no blocking (an empty
intersection with a model that never waits).  The fourth, a pipe id or a
path the tables do not hold, is unreachable through any modeled open.

On the `write` half: a count past `Uaccess.rw_bytes_max` whose range
leaves the address space, where Linux answers -EFAULT and the model
declines to judge the call (`Uaccess.modeled_rw_range`); a write past
end-of-file that would open a hole too large to zero-fill as a byte list
(`modeled_file_gap`); a pipe write that needs a second ring slot
(`State.pipe_write_room`) or whose source is not readable throughout,
where Linux's answer holds only under a bound the model means to relax; a
pipe whose reader is gone and a write to any socket, where Linux raises
SIGPIPE and the outcome type cannot say the process died; and a pipe id or
a path the tables do not hold, unreachable through any modeled open.

On the vectored half, each decline pin's docstring names the decline it
lands on and why: `readv_buf_gap` (`readv_heap_gap` shares its body),
`writev_buf_gap`, or one of the two the twin's module header declares
on the file write — the write past end-of-file from a source
with no readable byte, and the source readable at its first byte but not
throughout.

One more thing is NOT a decline but an ADMITTED answer this file inherits
and cannot refute: a socket or pipe read at a count within
`Uaccess.rw_bytes_max` whose destination straddles TASK_SIZE with writable
memory below it is answered as a delivery, where `vfs_read`'s access_ok
(fs/read_write.c:560-561, v6.18.46) answers -EFAULT before the arm is
reached -- bugs/write-out-of-range-short-write.md, "The read direction, on
two arms".  No pin below states that outcome: pinning it would pin the
divergence, and the two `*_big_out_of_range_count_declines` pins mark
where the gate takes over instead.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.ReadWrite

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## What the spec owes `sys_simp`

`Checks/Cases/Tactic.lean`'s header asks each spec for its unfolding
equation, and for each helper its post-states are spelled with; they are
registered here, beside the pins that read them, because this port edits
only its own two files.  `access_ok_zero` is `Sys/Uaccess.lean`'s; its
unfolding is registered here for the same reason, and moves to that
file's Cases twin the day one registers it. -/

attribute [sys_simp low] read_spec.eq_1 read_urandom.eq_1 socket_pending_error.eq_1
  access_ok_zero.eq_1

/-! The stream and script equations the delivering arms are read through:
`StreamLaws`' twins of the Rocq `stream_take` / `net_take` laws, and the
head-cell views the two matches of `read_spec` take.  `fd_lookup`'s own
equations are here for the one fixture whose table is not closed (the
connected socket over a symbolic script, below). -/

attribute [sys_simp] uncons_cons uncons_eof stream_take_cons stream_take_eof stream_take_zero
  stream_take_z_eq net_take_cons net_take_fin net_take_rst net_take_timedout net_take_zero
  net_take_z_eq ICons_ne_IEof IEof_ne_ICons network_fin_stays_fin network_reset_stays_reset
  network_timeout_stays_timeout List.length_cons List.length_nil
  FdEntry.FdSocket.injEq FdEntry.FdFile.injEq SockState.SkConnected.injEq
attribute [sys_simp low] fd_lookup.eq_1 fd_lookup.eq_2

/-! A refutation through a top-level `record_copyins`.  Since ticket D4,
`Sys/Syscall.lean`'s `record_copyins_iff` reads the wrapper at a full
application as `∃ o', spec i m o' ∧ o = outcome_copyins reads o'`
(`Checks/Cases/Tactic.lean` registers it at the default priority).  A
positive pin meets that as `∃ o', o' = Ok … ∧ …`, which `exists_eq_left`
substitutes.  A refutation meets it under `¬`, and the first pass pushes
the negation through (`not_exists`, `not_and`) before the inner
`writev_file_arm` outcome is decided — its gather needs the `+ground`
pass — so what the second pass reaches is
`∀ o', o' = Ok … → ¬ o = outcome_copyins reads o'`, and the pass carries
the `exists_eq_*` family but no `forall_eq`.  Core's `forall_eq` and
`forall_eq'` are the missing halves: without them the `sys_refute`
pins over `writev_file_arm` below stop at that residue (measured on the
09-14 day tip, where D4 is).  The general home is the pass in
`Checks/Cases/Tactic.lean`, which is not this ticket's file. -/
attribute [sys_simp] forall_eq forall_eq'

/-! ## The dispatcher, crossed before the normalizer runs

Every pin here but the readv and writev order declines, which state
`readv_spec` and `writev_spec` themselves and so give the step below
nothing to unfold, states its call through `syscall_spec`, and `sys_norm`
reads that by unfolding `spec_table` and walking `lookup_arm` down it.  The
unfolded table puts every arm's body in front of `simp`, which normalizes
each one under its binder before the walk reaches the arm the number
selects: about a third of a pin's elaboration on the pins measured for
issue #1461.  `rw_norm` below is `sys_norm` with one step in front of
it: unfold `syscall_spec` and `dispatch`, and reduce the `lookup_arm`
discriminant by `whnf`, so `simp` meets one arm.  The step is
definitional: it states no lemma and adds nothing to `sys_simp`.  When it
fails, `try` drops it, and what follows is `sys_norm` itself; `rw_refute`
is `sys_refute` over it.  They are local tactics rather than a
`macro_rules` on `sys_norm` because `tools/check_lean_pins.py` (PIN-7)
refuses a Cases file's `macro_rules` on a token no exempt header outside
`Checks/Cases/Tactic.lean` declares, and `sys_norm` is declared there.  A
pin that states `sys_refute at h` keeps `sys_refute`: the step reads the
goal.  With the arm reached first, `rst_left_pending_rejected` and
`timedout_left_pending_rejected` are the two pins whose build stopped at
`False → ¬evs = []`, which `false_implies` closes. -/

open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch in
/-- `sys_norm` with the dispatcher crossed first, the step the section
header describes.  `local`, so no other file sees it. -/
local macro "rw_norm" : tactic =>
  `(tactic| ((try (unfold syscall_spec dispatch; conv in lookup_arm _ _ => whnf));
             sys_norm))

/-- `sys_refute` over `rw_norm`: the goal must be closed by it. -/
local macro "rw_refute" : tactic =>
  `(tactic| (rw_norm; done))

attribute [local sys_simp] false_implies

/-- The head cell of a script with a byte at its front, the view the
socket arm's four-way match takes.
model: `NetStream.cell_at` on `NCons`, a rewrite for `sys_norm` -/
theorem cell_at_zero_cons (b : byte) (s : NetStream) : (NCons b s).cell_at 0 = .NByte b := rfl

/-- One event per delivered byte, on the channel the arm names: the
`List.map` the arm emits, unfolded over a cons.
model: `List.map (ReadEv ch)` over `::` and `[]`, rewrites for `sys_norm` -/
theorem map_ReadEv_cons (ch : word) (b : byte) (l : List byte) :
    List.map (ReadEv ch) (b :: l) = ReadEv ch b :: List.map (ReadEv ch) l := rfl

/-- …and over the empty list.
model: `List.map (ReadEv ch)` over `[]`, a rewrite for `sys_norm` -/
theorem map_ReadEv_nil (ch : word) : List.map (ReadEv ch) ([] : List byte) = [] := rfl

/-- The length word of a delivered list, for the list shapes the pins
deliver: one, two, three and five symbolic bytes.  `len_word` reads the
LENGTH only, so the bytes may stay variables.
model: `len_word` on a one-element list, a rewrite for `sys_norm` -/
theorem len_word_one (a : byte) : len_word [a] = 1 := rfl
/-- model: `len_word` on a two-element list, a rewrite for `sys_norm` -/
theorem len_word_two (a b : byte) : len_word [a, b] = 2 := rfl
/-- model: `len_word` on a three-element list, a rewrite for `sys_norm` -/
theorem len_word_three (a b c : byte) : len_word [a, b, c] = 3 := rfl
/-- model: `len_word` on a five-element list, a rewrite for `sys_norm` -/
theorem len_word_five (a b c d e : byte) : len_word [a, b, c, d, e] = 5 := rfl

attribute [sys_simp] cell_at_zero_cons map_ReadEv_cons map_ReadEv_nil len_word_one len_word_two
  len_word_three len_word_five

/-! ## read (63): the fixtures and the call

`read_model` is one process with every fd kind `read_spec` has an arm for,
over a file system holding "hi" at path `f` = 102 and "j" at `g` = 103:

| fd | kind | why it is here |
|---|---|---|
| 0, 1, 2 | the three channels | stdin, and the two write-only ones |
| 3 | `FdFile f 0` | a regular file at its start |
| 4 | `FdFileW g 0` | a file open write-only |
| 5 | `FdDir` | a directory |
| 6 | `FdFile f 2` | the same file at end of file |
| 7 | `FdFile [104] 0` | a path the file system does not hold |
| 8 | `FdDevNull true false` | /dev/null open read-only |
| 9 | `FdDevNull false true` | /dev/null open write-only |
| 10, 11, 12 | fresh, bound, listening sockets | never connected |
| 13 | `SkReset` | a socket whose peer's error was already reported |
| 14, 15 | pipe 0's read and write ends | pipe 0 holds "ab" |
| 16, 17 | pipe 1's read and write ends | pipe 1 is empty, its writer alive |
| 18 | pipe 2's read end | pipe 2 is empty and has no writer |
| 19 | `FdPipe 3 false` | a pipe id the table does not hold |
| 20, 21, 22 | connected sockets at `NFin`, `NRst`, `NTimedOut` | the three terminals |
| 23 | `FdFile f 1` | the file one byte in |
| 24 | `FdUrandom` | the random device |
| 26 | `FdChannel 0` | a second descriptor onto channel 0, as `dup(0)` mints |

fd 30 is deliberately absent: it is the closed fd the -EBADF pins name.
The connection's channel is 7 and its peer `peer_a`; nothing below reads
either beyond carrying them. -/

def peer_a : PeerAddr := PeerAddr.mkPeer (Z_to_bv 32 0x0100007f) (Z_to_bv 16 0x5000)

def read_fds : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
    (3, .FdFile [102] 0), (4, .FdFileW [103] 0), (5, .FdDir),
    (6, .FdFile [102] 2), (7, .FdFile [104] 0),
    (8, .FdDevNull true false), (9, .FdDevNull false true),
    (10, .FdSocket .SkFresh), (11, .FdSocket .SkBound), (12, .FdSocket .SkListening),
    (13, .FdSocket (.SkReset peer_a 7)),
    (14, .FdPipe 0 false), (15, .FdPipe 0 true), (16, .FdPipe 1 false), (17, .FdPipe 1 true),
    (18, .FdPipe 2 false), (19, .FdPipe 3 false),
    (20, .FdSocket (.SkConnected peer_a 7 NFin)), (21, .FdSocket (.SkConnected peer_a 7 NRst)),
    (22, .FdSocket (.SkConnected peer_a 7 NTimedOut)),
    (23, .FdFile [102] 1), (24, .FdUrandom), (26, .FdChannel 0) ]

/-- Pipe 0 holds "ab" with its page mark at 2; pipe 1 is empty with the
mark at 0; pipe 2 is empty with a mark left by a drained page. -/
def read_pipes : List (word × PipeBuf) := [(0, ([97, 98], 2)), (1, ([], 0)), (2, ([], 3))]

def read_fs : Fs.Fs := [([102], [104, 105]), ([103], [106])]

def read_model : Model := fixture_of (fds := read_fds) (pipes := read_pipes) (fs := read_fs)

/-- `read_model`'s fd table, in the form the normalizer leaves once `m_fds`
has unfolded on the bound model (`Fs/Stat.lean`'s fixture readings are the
precedent): with it, and the three fixture lists' unfoldings below, the
first pass of `sys_norm` resolves the descriptor itself instead of leaving
the closed model to the second pass's evaluation.
model: a fixture projection, a rewrite for `sys_norm`. -/
theorem read_model_fd_table : read_model.m_fd.fdst_table = read_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem read_model_fd_pipes : read_model.m_fd.fdst_pipes = read_pipes := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem read_model_fs : read_model.m_fsys.fsst_image = read_fs := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem read_model_stdin : read_model.m_io.iost_stdin = IEof := rfl

attribute [local sys_simp] read_model_fd_table read_model_fd_pipes read_model_fs read_model_stdin
attribute [local sys_simp low] read_fds.eq_1 read_pipes.eq_1 read_fs.eq_1

/-- Rocq's `hello_stdin` over symbolic bytes (the file header says why). -/
def hello (b c d e f : byte) : InputStream :=
  ICons b (ICons c (ICons d (ICons e (ICons f IEof))))

/-- `read_model` with standard input holding `s`. -/
def stdin_model (s : InputStream) : Model := with_stdin s read_model

/-- `read_model` with the random device's declared stream holding `s`. -/
def urandom_model (s : InputStream) : Model := with_urandom s read_model

/-- `read_model` plus a connected socket at fd 25 whose peer's script is
`rx`, the one fixture whose fd table is not a closed term. -/
def socket_fds (rx : NetStream) : List (word × FdEntry) :=
  (25, .FdSocket (.SkConnected peer_a 7 rx)) :: read_fds

def socket_model (rx : NetStream) : Model := with_fds (socket_fds rx) read_model

/-- `read(fd, buf, count)` as the dispatcher sees it: syscall 63, the three
arguments in a0..a2, nothing readable, `wmem` the writable view. -/
def read_in (fd buf count : word) (wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 63 [fd, buf, count, 0, 0, 0] (fun _ => none) wmem

/-- Rocq's `wmem_first n`: exactly `[4096, 4096 + n)` is writable.  The
range is arithmetic on the address, as `Checks/Cases/Net/Socket.lean`'s
maps spell theirs, not `bv_leu`/`bv_ltu`: the delivery iffs name this map
on their kernel side, and `check_lean_pins.py`'s PIN-6 reads a Cases `def`
applying a model predicate as that predicate under another name. -/
def wmem_first (n : Int) : word → Option byte :=
  fun a => if 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 4096 + n then some 0 else none

/-- Nothing is writable. -/
def wmem_none : word → Option byte := fun _ => none

/-- EVERYTHING is writable, the top of the address space included: the
view that separates `access_ok`'s range verdict from the copy's fault. -/
def wmem_all : word → Option byte := fun _ => some 0

/-! ## The destination window, as arithmetic

The two delivery pins (`stdin_delivers_a_prefix_iff`,
`socket_delivers_a_prefix_iff`) state the destination's bound as a numeral
on the delivered length rather than as the spec's own walk over
`wmem_first 5`: a kernel side that re-ran `read_bytes_map` over the fixture
would restate the arm's decision instead of stating what Linux does
(`check_lean_pins.py`'s PIN-6).  The bridge is proved once here, from the
walk's equation and closed walks of at most six bytes. -/

/-- A walk that fails at fuel `k` fails at every larger fuel: the unmapped
address it stopped at is on the longer walk's path too.
model: `State.read_bytes_aux`, by induction on the fuel -/
theorem read_bytes_aux_none_mono (mp : word → Option byte) (a : word) (k j : Nat)
    (h : read_bytes_aux mp a k = none) : read_bytes_aux mp a (k + j) = none := by
  induction k generalizing a with
  | zero => simp only [read_bytes_aux, reduceCtorEq] at h
  | succ k ih =>
    rw [Nat.add_right_comm]
    cases hb : mp a with
    | none => simp only [read_bytes_aux, hb]
    | some b =>
      simp only [read_bytes_aux, hb] at h ⊢
      cases hr : read_bytes_aux mp (a + 1) k with
      | none => rw [ih (a + 1) hr]
      | some r => rw [hr] at h; simp only [reduceCtorEq] at h

/-- The five-byte window of `wmem_first 5` at 4096 as a bound on the
delivered length: a walk of `bs.length` bytes from 4096 succeeds exactly
when `bs.length ≤ 5`, for any length a count of 100 can select.  Six bytes
fail — 4101 is unmapped — and so does every longer walk; each walk of at
most five is closed and evaluated.
model: `State.read_bytes_map` over `wmem_first 5`, through `read_bytes_map_eq` -/
theorem wmem_first_five_window (bs : List byte) (hl : (bs.length : Int) ≤ 100) :
    read_bytes_map (wmem_first 5) 4096 (len_word bs) ≠ none ↔ (bs.length : Int) ≤ 5 := by
  have hk : word_to_nat (len_word bs) = bs.length := by
    unfold word_to_nat len_word Z_to_bv
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    omega
  rw [read_bytes_map_eq, hk]
  constructor
  · intro hne
    refine Int.not_lt.mp fun hgt => hne ?_
    have h6 : read_bytes_aux (wmem_first 5) 4096 6 = none := by decide
    have h := read_bytes_aux_none_mono (wmem_first 5) 4096 6 (bs.length - 6) h6
    rwa [show 6 + (bs.length - 6) = bs.length by omega] at h
  · intro hle
    rcases (by omega : bs.length = 0 ∨ bs.length = 1 ∨ bs.length = 2 ∨ bs.length = 3
        ∨ bs.length = 4 ∨ bs.length = 5) with h | h | h | h | h | h <;> rw [h] <;> decide

/-! ## The clamp, as a law of the file reader

Rocq's `file_read_clamped_len`, the first direction of its bound: whatever
the count and however long the file, a file read under `rw_count_clamp`
delivers at most `MAX_RW_COUNT` bytes.  The second direction
(`read_delivery_clamped`, over the whole relation) stays unpinned; the
header says why. -/

/-- No file read under the clamp is longer than `MAX_RW_COUNT`: `vfs_read`
caps `count` at `MAX_RW_COUNT` (fs/read_write.c:566-567, v6.18.46) before
the file is consulted, and `file_read` takes at most that many bytes.
rocq-twin: file_read_clamped_len
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem file_read_clamped_len (data : List byte) (off count : word) :
    ((file_read data off (Z_to_bv 64 (rw_count_clamp count))).length : Int) ≤ MAX_RW_COUNT := by
  rw [file_read_unguarded, List.length_take]
  have h := rw_count_clamp_range count
  have hw := rw_count_clamp_word count
  unfold word_to_nat
  unfold bv_unsigned at hw
  omega

attribute [sys_simp low] read_in.eq_1 hello.eq_1 stdin_model.eq_1 urandom_model.eq_1
  socket_fds.eq_1 socket_model.eq_1

/-! ## `ksys_read`: the descriptor is resolved first

`ksys_read` (fs/read_write.c:704-720, Linux v6.18.46) resolves the fd with
`CLASS(fd_pos, f)(fd)` (:706) and answers -EBADF (:707) on an empty one
(:709) before `vfs_read` (:715) is reached, and `vfs_read` (:552-581)
tests `FMODE_READ` (:556-557) before `access_ok` (:560-561).  So a closed
fd, and an fd open without `FMODE_READ`, is -EBADF whatever `buf` and
`count` say — even a range `access_ok` would refuse. -/

/-- A closed fd is -EBADF and nothing else.
rocq-twin: read_bad_fd_ebadf
kernel: fs/read_write.c:ksys_read@v6.18.46 -/
theorem closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (read_in 30 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …and a kernel delivering four bytes on it is lying.
rocq-twin: read_bad_fd_success_rejected
probe: testing/syscall-check/tests/read_spec.c#reject --mutate read:ret=0 -- badfd -/
theorem closed_fd_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 30 4096 16 wmem_none) read_model
        (Ok (mkEffect 4 [(4096, [1, 2, 3, 4])] []) m' evs) := by
  rw_refute

/-- A zero count does not rescue a closed fd: `ksys_read` resolves the
descriptor (fs/read_write.c:706-709) before `vfs_read` ever sees `count`,
so it is -EBADF, not the 0 the open kinds answer.
kernel: fs/read_write.c:ksys_read@v6.18.46 -/
theorem closed_fd_zero_count_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (read_in 30 4096 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …so a 0 there is refused.
probe: testing/syscall-check/tests/socket_rw.c#reject --mutate read#7:ret=0 -- rw -/
theorem closed_fd_zero_count_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 30 4096 0 wmem_none) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- The order: a closed fd at a buffer past `State.TASK_SIZE` is -EBADF,
not the -EFAULT `vfs_read` would answer one test later.
kernel: fs/read_write.c:ksys_read,vfs_read@v6.18.46 -/
theorem closed_fd_beats_bad_range (o : outcome SyscallEffect) :
    syscall_spec (read_in 30 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- A file opened O_WRONLY lacks `FMODE_READ` (`init_file`'s
`f->f_mode = OPEN_FMODE(flags)`, fs/file_table.c:199): -EBADF.
kernel: fs/read_write.c:vfs_read; fs/file_table.c:init_file@v6.18.46 -/
theorem write_only_file_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (read_in 4 4096 16 (wmem_first 16)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …never a byte of the file it names: `vfs_read` returns -EBADF at
fs/read_write.c:556-557 before any `->read_iter` runs.
kernel: fs/read_write.c:vfs_read; fs/file_table.c:init_file@v6.18.46 -/
theorem write_only_file_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 4 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect 1 [(4096, [106])] []) m' evs) := by
  rw_refute

/-- …and -EBADF ahead of -EFAULT: `FMODE_READ` (:556-557) is tested before
`access_ok` (:560-561).
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem write_only_file_ebadf_beats_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 4 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- Channels 1 and 2 are write-only BY ASSUMPTION about the stdio the
process was handed (bugs/channel-fds-assume-unidirectional-stdio.md), so
a read on stdout is the -EBADF `vfs_read`'s `FMODE_READ` test gives a
write end (`create_pipe_files` opens it O_WRONLY, fs/pipe.c:944-946).
kernel: fs/read_write.c:vfs_read; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem stdout_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (read_in 1 4096 16 (wmem_first 16)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …and so is stderr.
probe: testing/syscall-check/tests/fd_modes.c#conform -- chandir -/
theorem stderr_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (read_in 2 4096 16 (wmem_first 16)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- A 0 on stdout would need `FMODE_READ` on a write end.
kernel: fs/read_write.c:vfs_read; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem stdout_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 1 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- The channel arm's order: the write-only channel is refused before the
range is looked at.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem stdout_ebadf_beats_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 1 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- A pipe's WRITE end is O_WRONLY (`create_pipe_files`, fs/pipe.c:944-946):
-EBADF, and the queue's two bytes are never consulted.
kernel: fs/read_write.c:vfs_read; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem pipe_write_end_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (read_in 15 4096 16 (wmem_first 16)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …not the queue's bytes, which the READ end delivers.
kernel: fs/read_write.c:vfs_read; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem pipe_write_end_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 15 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect 2 [(4096, [97, 98])] []) m' evs) := by
  rw_refute

/-- …and -EBADF ahead of the pipe arm's count gate: a huge count at an
address past `State.TASK_SIZE` on the write end is `FMODE_READ`'s -EBADF,
where the read end declines (`pipe_big_out_of_range_count_declines`).
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pipe_write_end_ebadf_beats_the_gate (o : outcome SyscallEffect) :
    syscall_spec (read_in 15 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- /dev/null opened O_WRONLY lacks `FMODE_READ` (`OPEN_FMODE`,
fs/file_table.c:199): -EBADF before the device is reached.
kernel: fs/read_write.c:vfs_read; fs/file_table.c:init_file@v6.18.46 -/
theorem devnull_write_only_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (read_in 9 4096 16 (wmem_first 16)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …not `read_null`'s 0, which a read-only description gets.
kernel: fs/read_write.c:vfs_read; drivers/char/mem.c:read_null@v6.18.46 -/
theorem devnull_write_only_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 9 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …and ahead of the range test.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem devnull_write_only_ebadf_beats_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 9 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- `read(2^32, buf, 16)` is a read on STDIN: `fd` arrives through the
`unsigned int` of `SYSCALL_DEFINE3(read, …)` (fs/read_write.c:722, v6.18.46), so
the table's `fd32` keeps the low half, and at end of input the answer is
0, not -EBADF — `anon_pipe_read`'s `if (!pipe->writers) break;`
(fs/pipe.c:370-371) with `ret` still 0.  The probe of the truncation,
`fd_truncation.c`, reads with input waiting and is
`fd_2_32_delivers_stdin`'s.
rocq-twin: read_fd_truncates_to_32_bits
kernel: fs/read_write.c:ksys_read; fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (read_in (Z_to_bv 64 (2 ^ 32)) 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- A kernel refusing fd 2^32 compared the whole register.
kernel: fs/read_write.c:ksys_read@v6.18.46 -/
theorem fd_2_32_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in (Z_to_bv 64 (2 ^ 32)) 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- …and with input waiting the truncated fd DELIVERS: the probe's
`read(0 | 2^32, buf, 2)` under `--stdin hi` answers "hi".
probe: testing/syscall-check/tests/fd_truncation.c#conform --stdin hi -/
theorem fd_2_32_delivers_stdin (b c d e f : byte) :
    syscall_spec (read_in (Z_to_bv 64 (2 ^ 32)) 4096 2 (wmem_first 2)) (stdin_model (hello b c d e f))
      (Ok (mkEffect 2 [(4096, [b, c])] []) (stdin_model (ICons d (ICons e (ICons f IEof))))
          [ReadEv 0 b, ReadEv 0 c]) := by
  rw_norm

/-- `fd32` is a MASK, not "high bits mean stdin": `read(2^32 + 3, buf, 100)`
is fd 3's file, its two bytes delivered and its offset moved — the probe's
`rfd | HI` read of a regular file.
probe: testing/syscall-check/tests/fd_truncation.c#conform --stdin hi -/
theorem fd_2_32_plus_3_reads_the_file (o : outcome SyscallEffect) :
    syscall_spec (read_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 100 (wmem_first 2)) read_model o ↔
      o = Ok (mkEffect 2 [(4096, [104, 105])] [])
             (with_fds (fd_insert read_fds 3 (.FdFile [102] 2)) read_model) [] := by
  rw_norm

/-- THE DIRECTION IS THE DESCRIPTION'S, NOT THE NUMBER'S.  fd 26 is a second
descriptor onto channel 0 (what `dup(0)` mints); `vfs_read` reads
`FMODE_READ` off the `struct file` (fs/read_write.c:556-557, v6.18.46), so
it reads as stdin — 0 at end of input — and a model keyed on the fd
number, which would answer -EBADF for any fd above 0, is refused.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem channel_zero_on_fd_26_reads_stdin (o : outcome SyscallEffect) :
    syscall_spec (read_in 26 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …and the number-keyed -EBADF is refused.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem channel_zero_on_fd_26_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 26 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-! ## `vfs_read`: `access_ok` on the count the call NAMED

`if (unlikely(!access_ok(buf, count))) return -EFAULT;`
(fs/read_write.c:560-561, v6.18.46) runs on the count as named — before
`rw_verify_area` (:563-565), before the `MAX_RW_COUNT` clamp (:566-567),
before any byte is consulted — and `__access_ok`
(include/asm-generic/access_ok.h:31-40, v6.18.46) is
`size <= TASK_SIZE && addr <= TASK_SIZE - size`.  Two consequences these
pins fix: a count negative as `ssize_t` is -EFAULT here and never reaches
`rw_verify_area`'s -EINVAL (:456-457); and a ZERO count still faces the
range test, so `read(fd, 2^47 + 1, 0)` is -EFAULT where
`read(fd, 2^47, 0)` is 0. -/

/-- A zero-length stdin read one byte past the limit is -EFAULT: the range
verdict, not a copy fault, and decided before the `count = 0` shortcut.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0-past -/
theorem stdin_zero_count_past_top_is_efault (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) (stdin_model (hello b c d e f)) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (stdin_model (hello b c d e f)) [] := by
  rw_norm

/-- …and never the 0 a count-first model would answer.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=0 -- chan0-past -/
theorem stdin_zero_count_past_top_zero_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) (stdin_model (hello b c d e f))
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- The limit itself passes: `addr <= TASK_SIZE - 0` at `addr = 2^47`, so a
zero count AT the top is 0.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0-top -/
theorem stdin_zero_count_at_top_is_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 0 (Z_to_bv 64 (2 ^ 47)) 0 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- A harness whose reservation ended below the limit would say -EFAULT
there; the kernel's predicate does not.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=-EFAULT -- chan0-top -/
theorem stdin_zero_count_at_top_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 (Z_to_bv 64 (2 ^ 47)) 0 wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- A range ending one past the limit is -EFAULT with input waiting: the
stream is not consulted and not consumed.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan-top-2 -/
theorem stdin_range_over_top_is_efault (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 0 (Z_to_bv 64 (2 ^ 47 - 1)) 2 wmem_none) (stdin_model (hello b c d e f)) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (stdin_model (hello b c d e f)) [] := by
  rw_norm

/-- …not the 0 of end of file, the probe's lie at this range: input is
waiting, and the verdict is the range's before the stream is looked at.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=0 -- chan-top-2 -/
theorem stdin_range_over_top_zero_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 (Z_to_bv 64 (2 ^ 47 - 1)) 2 wmem_none) (stdin_model (hello b c d e f))
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …and not a delivery of the byte that is there, refused on the same
range verdict.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem stdin_range_over_top_delivery_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 (Z_to_bv 64 (2 ^ 47 - 1)) 2 wmem_none) (stdin_model (hello b c d e f))
        (Ok (mkEffect 1 [(Z_to_bv 64 (2 ^ 47 - 1), [b])] []) m' evs) := by
  rw_refute

/-- THE RANGE VERDICT IS NOT THE COPY'S FAULT: the same call with every
byte of memory writable, the top of the address space included, is still
-EFAULT, because `vfs_read`'s range test (fs/read_write.c:560-561,
v6.18.46; `__access_ok`, include/asm-generic/access_ok.h:31-40) refuses
the RANGE before any byte is looked at.  A model that
let the destination speak for the range would deliver here.
kernel: fs/read_write.c:vfs_read; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem stdin_range_over_top_is_efault_even_if_writable (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 0 (Z_to_bv 64 (2 ^ 47 - 1)) 2 wmem_all) (stdin_model (hello b c d e f)) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (stdin_model (hello b c d e f)) [] := by
  rw_norm

/-- …so the two-byte delivery a copy-first model would make is refused.
kernel: fs/read_write.c:vfs_read; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem stdin_range_over_top_writable_delivery_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 (Z_to_bv 64 (2 ^ 47 - 1)) 2 wmem_all) (stdin_model (hello b c d e f))
        (Ok (mkEffect 2 [(Z_to_bv 64 (2 ^ 47 - 1), [b, c])] []) m' evs) := by
  rw_refute

/-- `count = -1` is -EFAULT: `size <= TASK_SIZE` fails in `__access_ok`
before `rw_verify_area`'s `(ssize_t) count < 0` (:456-457) could answer
-EINVAL.  The probe of this count, `read_window.c`'s `negc`, reads a
regular file and is `file_negative_count_is_efault`'s; the verdict is
`vfs_read`'s, ahead of the dispatch on the kind.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem stdin_negative_count_is_efault (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 0 4096 (Z_to_bv 64 (2 ^ 64 - 1)) (wmem_first 5)) (stdin_model (hello b c d e f)) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (stdin_model (hello b c d e f)) [] := by
  rw_norm

/-- …and the -EINVAL of `rw_verify_area` is refused: the range test is
ahead of it.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem stdin_negative_count_einval_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 (Z_to_bv 64 (2 ^ 64 - 1)) (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- A file fd at a buffer past the limit: -EFAULT with the offset
unchanged, before the file is opened.
probe: testing/syscall-check/tests/read_window.c#conform -- hi-efault -/
theorem file_range_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 (Z_to_bv 64 (2 ^ 63)) 8 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …never end of file.
probe: testing/syscall-check/tests/read_window.c#reject --mutate read:ret=0,drop-writes -- hi-efault -/
theorem file_range_past_top_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 (Z_to_bv 64 (2 ^ 63)) 8 wmem_none) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- The file arm's range verdict, with every byte writable: still -EFAULT
(`vfs_read`'s range test, fs/read_write.c:560-561, v6.18.46, before the
file is opened), the offset unmoved.
kernel: fs/read_write.c:vfs_read; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem file_range_past_top_is_efault_even_if_writable (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 (Z_to_bv 64 (2 ^ 63)) 8 wmem_all) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …so the file's two bytes are not delivered there.
kernel: fs/read_write.c:vfs_read; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem file_range_past_top_writable_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 (Z_to_bv 64 (2 ^ 63)) 8 wmem_all) read_model
        (Ok (mkEffect 2 [(Z_to_bv 64 (2 ^ 63), [104, 105])] []) m' evs) := by
  rw_refute

/-- A file AT end of file still faces the range test on a zero count:
`read(fd, 2^47 + 1, 0)` is -EFAULT there…
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- file0-past -/
theorem file_at_eof_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 6 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …and `read(fd, 2^47, 0)` is 0, the destination never inspected.  The
descriptor is written back with its offset unmoved — `ksys_read` stores
`f_pos` after every non-negative return (fs/read_write.c:716-717, v6.18.46) — which
the model spells as the entry re-inserted, unchanged.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- file0-top -/
theorem file_at_eof_at_top_is_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 6 (Z_to_bv 64 (2 ^ 47)) 0 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) (with_fds (fd_insert read_fds 6 (.FdFile [102] 2)) read_model) [] := by
  rw_norm

/-- The passing edge at a NONZERO count: two bytes ending exactly at the
top (`buf = 2^47 - 2`), `addr <= TASK_SIZE - size` holding with equality
in `__access_ok` (include/asm-generic/access_ok.h:31-40, v6.18.46), and the
file's two bytes are delivered — the destination writable up to the limit
(`wmem_all`), the copy not being what is at issue.  The probe's `win-at`
is this range on a file, its count running to TASK_SIZE exactly.
probe: testing/syscall-check/tests/read_window.c#conform -- win-at -/
theorem file_range_at_top_delivers (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 (Z_to_bv 64 (2 ^ 47 - 2)) 2 wmem_all) read_model o ↔
      o = Ok (mkEffect 2 [(Z_to_bv 64 (2 ^ 47 - 2), [104, 105])] [])
             (with_fds (fd_insert read_fds 3 (.FdFile [102] 2)) read_model) [] := by
  rw_norm

/-- …and is not -EFAULT: a predicate written `<` where the kernel's is
`<=` would refuse it.
probe: testing/syscall-check/tests/read_window.c#reject --mutate read:ret=-EFAULT,drop-writes -- win-at -/
theorem file_range_at_top_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 (Z_to_bv 64 (2 ^ 47 - 2)) 2 wmem_all) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- `count = -1` on a file is -EFAULT, `size <= TASK_SIZE` failing in
`__access_ok` before `rw_verify_area`'s `(ssize_t) count < 0`
(fs/read_write.c:456-457, v6.18.46) could answer -EINVAL; the descriptor
is not rewritten, so the offset does not move.
probe: testing/syscall-check/tests/read_window.c#conform -- negc -/
theorem file_negative_count_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 4096 (Z_to_bv 64 (2 ^ 64 - 1)) (wmem_first 2)) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …never 0: the verdict is the range's, before the file is read.
probe: testing/syscall-check/tests/read_window.c#reject --mutate read#1:ret=0,drop-writes -- negc -/
theorem file_negative_count_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 4096 (Z_to_bv 64 (2 ^ 64 - 1)) (wmem_first 2)) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- A directory fd at a buffer past the limit is -EFAULT AHEAD of -EISDIR:
`vfs_read`'s `access_ok` (:560-561) runs before it dispatches to
`generic_read_dir` (fs/libfs.c:224-227).
kernel: fs/read_write.c:vfs_read; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem dir_range_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 5 (Z_to_bv 64 (2 ^ 63)) 8 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …so the -EISDIR a dispatch-first model would answer is refused there.
kernel: fs/read_write.c:vfs_read; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem dir_range_past_top_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 5 (Z_to_bv 64 (2 ^ 63)) 8 wmem_none) read_model
        (Ok (mkEffect (errno_ret EISDIR) [] []) m' evs) := by
  rw_refute

/-- /dev/null too: the range test precedes `read_null`.
kernel: fs/read_write.c:vfs_read; drivers/char/mem.c:read_null@v6.18.46 -/
theorem devnull_range_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 8 (Z_to_bv 64 (2 ^ 63)) 8 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …so `read_null`'s 0 is refused past the limit.
kernel: fs/read_write.c:vfs_read; drivers/char/mem.c:read_null@v6.18.46 -/
theorem devnull_range_past_top_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 8 (Z_to_bv 64 (2 ^ 63)) 8 wmem_none) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- /dev/urandom too: the range test precedes the device, and the declared
stream is not consumed.
kernel: fs/read_write.c:vfs_read; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem urandom_range_past_top_is_efault (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 24 (Z_to_bv 64 (2 ^ 63)) 2 wmem_none) (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons b (ICons c IEof))) [] := by
  rw_norm

/-- /dev/urandom's range verdict with every byte writable: -EFAULT from
`vfs_read` (fs/read_write.c:560-561, v6.18.46) before `urandom_read_iter`
is reached, the declared stream not consumed.  A model that dispatched
to the device first would deliver two bytes here.
kernel: fs/read_write.c:vfs_read; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem urandom_range_past_top_is_efault_even_if_writable (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 24 (Z_to_bv 64 (2 ^ 63)) 2 wmem_all) (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons b (ICons c IEof))) [] := by
  rw_norm

/-- …so the device's two bytes are not delivered past the limit.
kernel: fs/read_write.c:vfs_read; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem urandom_range_past_top_writable_delivery_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 24 (Z_to_bv 64 (2 ^ 63)) 2 wmem_all) (urandom_model (ICons b (ICons c IEof)))
        (Ok (mkEffect 2 [(Z_to_bv 64 (2 ^ 63), [b, c])] []) m' evs) := by
  rw_refute

/-! ## `count = 0`: the range verdict is all Linux checks

Past `access_ok`, a zero count moves nothing on any kind: the channel arm
answers 0 without implying end of file, `sock_read_iter`'s
`if (!iov_iter_count(to)) return 0;` (net/socket.c:1168-1169, v6.18.46) fires
before the protocol on ANY socket, `anon_pipe_read`'s "Null read
succeeds" (fs/pipe.c:277-279, v6.18.46) fires before the pipe's mutex (:282), and
a file's `shmem_file_read_iter` copies nothing.  None of them inspects the
destination, so an unmapped buffer under the limit is still 0. -/

/-- `read(0, buf, 0)` with input waiting is 0: nothing consumed, no end
of file implied, and the unmapped destination not inspected.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0-unmapped -/
theorem stdin_zero_count_is_zero (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 0 4096 0 wmem_none) (stdin_model (hello b c d e f)) o ↔
      o = Ok (mkEffect 0 [] []) (stdin_model (hello b c d e f)) [] := by
  rw_norm

/-- …never -EFAULT: the range verdict is not a copy.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=-EFAULT -- chan0 -/
theorem stdin_zero_count_efault_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 0 wmem_none) (stdin_model (hello b c d e f))
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- …and never a byte: the count bounds the delivery.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem stdin_zero_count_delivery_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 0 (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (mkEffect 1 [(4096, [b])] []) m' evs) := by
  rw_refute

/-- A zero count on a FRESH socket is 0, short-circuited by `sock_read_iter`
(net/socket.c:1168-1169, v6.18.46) before `tcp_recvmsg_locked` could say -ENOTCONN.
probe: testing/syscall-check/tests/socket_rw.c#conform -- rw -/
theorem socket_zero_count_on_fresh_is_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 10 4096 0 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …so the -ENOTCONN a nonzero count gets is refused at zero.
probe: testing/syscall-check/tests/socket_rw.c#reject --mutate read#1:ret=-ENOTCONN -- rw -/
theorem socket_zero_count_on_fresh_enotconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 10 4096 0 wmem_none) read_model
        (Ok (mkEffect (errno_ret ENOTCONN) [] []) m' evs) := by
  rw_refute

/-- The same on a LISTENING socket…
probe: testing/syscall-check/tests/socket_rw.c#conform -- rw -/
theorem socket_zero_count_on_listening_is_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 12 4096 0 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …and on one whose peer has reset: `sock_read_iter` answers before
any state is read.
kernel: net/socket.c:sock_read_iter@v6.18.46 -/
theorem socket_zero_count_on_reset_is_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 13 4096 0 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …and on one whose peer RESET with the error still PENDING: 0, the
error left where it was — `sock_read_iter` returns at the empty iterator
(net/socket.c:1168-1169, v6.18.46) before `sock_recvmsg`, so `sk_err` is
neither read nor cleared, and the descriptor is not rewritten.
kernel: net/socket.c:sock_read_iter@v6.18.46 -/
theorem rst_zero_count_is_zero_and_stays_pending (o : outcome SyscallEffect) :
    syscall_spec (read_in 21 4096 0 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …so the -ECONNRESET a nonzero count gets is refused at zero.
kernel: net/socket.c:sock_read_iter@v6.18.46 -/
theorem rst_zero_count_connreset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 21 4096 0 wmem_none) read_model
        (Ok (mkEffect (errno_ret ECONNRESET) [] []) m' evs) := by
  rw_refute

/-- A zero count with BYTES QUEUED is 0 and consumes nothing: the same
early return, ahead of the queue walk.
kernel: net/socket.c:sock_read_iter@v6.18.46 -/
theorem socket_zero_count_with_bytes_is_zero (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 25 4096 0 wmem_none) (socket_model (NCons b (NCons c NFin))) o ↔
      o = Ok (mkEffect 0 [] []) (socket_model (NCons b (NCons c NFin))) [] := by
  rw_norm

/-- A zero count on a socket still faces `vfs_read`'s range test.
kernel: fs/read_write.c:vfs_read; net/socket.c:sock_read_iter@v6.18.46 -/
theorem socket_zero_count_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 10 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- "Null read succeeds": a zero-length read of an EMPTY pipe whose writer
is alive is 0 at fs/pipe.c:277-279, before the `mutex_lock` at :282, so
it never reaches the wait the nonzero read blocks in.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_zero_count_with_live_writer_is_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 16 4096 0 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- A zero count on a pipe still faces `vfs_read`'s range test.
kernel: fs/read_write.c:vfs_read; fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_zero_count_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 14 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- A zero count on a file is 0 with the offset unchanged (the descriptor
written back as it was, `ksys_read`'s `f_pos` store at fs/read_write.c:716-717, v6.18.46)
and the unmapped destination never inspected.
probe: testing/syscall-check/tests/read_spec.c#conform --mutate read:wmem-none -- file0 -/
theorem file_zero_count_is_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 4096 0 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) (with_fds (fd_insert read_fds 3 (.FdFile [102] 0)) read_model) [] := by
  rw_norm

/-- …never -EFAULT.
probe: testing/syscall-check/tests/read_spec.c#reject --mutate read:wmem-none,ret=-EFAULT -- file0 -/
theorem file_zero_count_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 4096 0 wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- A zero count on /dev/urandom is `get_random_bytes_user`'s
`if (unlikely(!iov_iter_count(iter))) return 0;` (drivers/char/random.c:440-441):
0, the declared stream untouched.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem urandom_zero_count_is_zero (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 24 4096 0 wmem_none) (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect 0 [] []) (urandom_model (ICons b (ICons c IEof))) [] := by
  rw_norm

/-- …but only in range: `vfs_read`'s access_ok (fs/read_write.c:560-561)
runs before `get_random_bytes_user`'s zero-count shortcut, so a zero count at
a buffer past the limit is -EFAULT, the declared stream still untouched.
kernel: fs/read_write.c:vfs_read; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem urandom_zero_count_past_top_is_efault (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 24 (Z_to_bv 64 (2 ^ 63)) 0 wmem_none) (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons b (ICons c IEof))) [] := by
  rw_norm

/-! ## Standard input

`read(0, buf, count)` with `count > 0`.  The channel arm answers for the
input stream: end of input is 0 and sticky; otherwise a nonempty prefix
of at most the clamped count is delivered, one `ReadEv` per byte on
channel 0, the stream advanced past exactly them.  The destination rule
is `copy_to_user`'s (`_inline_copy_to_user`, include/linux/uaccess.h:189-199, v6.18.46):
only the delivered bytes are touched. -/

/-- At end of input the answer is 0 — nothing moves, nothing is emitted —
here at count 16 into an unmapped buffer: one instance of Rocq's
symbolic `read_after_eof_deterministic`, which says it for every count
and every buffer.
rocq-twin: read_after_eof_deterministic
probe: testing/syscall-check/tests/rw_bytes_bound.c#conform -- chan-over -/
theorem stdin_at_eof_is_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 0 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- End of input is STICKY: `IEof` has no successor, so no later read
delivers a byte.
rocq-twin: read_eof_is_sticky
probe: testing/syscall-check/tests/rw_bytes_bound.c#reject --mutate read:ret=1,smuggle-write:a1:1 -- chan-over -/
theorem stdin_at_eof_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect 1 [(4096, [120])] []) m' evs) := by
  rw_refute

/-- An in-range end-of-input read is never -EFAULT, unmapped buffer or not:
no byte is copied.
probe: testing/syscall-check/tests/read_spec.c#reject --mutate read:wmem-none,ret=-EFAULT -- chan 100 0 -/
theorem stdin_at_eof_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- Input waiting and not one byte of the destination writable: -EFAULT,
`copy_to_user` having copied nothing, with the stream NOT consumed.
probe: testing/syscall-check/tests/read_spec.c#conform --stdin hello --mutate read:wmem-none,ret=-EFAULT,drop-writes -- chan 100 5 -/
theorem stdin_unwritable_is_efault (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 0 4096 100 wmem_none) (stdin_model (hello b c d e f)) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (stdin_model (hello b c d e f)) [] := by
  rw_norm

/-- …never 0: input remains, so this is not end of file.
probe: testing/syscall-check/tests/read_spec.c#reject --stdin hello --mutate read:wmem-none,ret=0,drop-writes -- chan 100 5 -/
theorem stdin_unwritable_zero_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 100 wmem_none) (stdin_model (hello b c d e f))
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …and never a delivery into memory nothing backs.
probe: testing/syscall-check/tests/read_spec.c#reject --stdin hello --mutate read:wmem-none -- chan 100 5 -/
theorem stdin_unwritable_delivery_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 100 wmem_none) (stdin_model (hello b c d e f))
        (Ok (mkEffect 5 [(4096, [b, c, d, e, f])] []) m' evs) := by
  rw_refute

/-- THE PARTIAL DESTINATION DECLINES.  Five bytes queued, a count of 100,
and only four bytes of the buffer writable: Linux answers -EFAULT with
four bytes stored if the five arrived in one pipe buffer
(`anon_pipe_read`'s `copy_page_to_iter` fails the whole buffer,
fs/pipe.c:343-348, v6.18.46) and a count of whole buffers otherwise, so the
five-byte delivery, the four-byte short read and the -EFAULT are all
outside what the model will say — a coverage gap, declined rather than
guessed (Rocq's note above `readv_imported`; Rocq's
`partial_destination_on_a_pipe_declines` states this `read` conjunct
beside its `readv` ones).
probe: testing/syscall-check/tests/read_spec.c#fail-closed --stdin hello --mutate read:wmem-hide:a1+4:4096 -- chan 100 5 -/
theorem stdin_partial_destination_declines (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 0 4096 100 (wmem_first 4)) (stdin_model (hello b c d e f)) o ↔
      o = Unmodeled := by
  rw_norm

/-- …so the four-byte short read Linux may really give is refused too:
a decline, not an answer.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_partial_destination_short_read_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 100 (wmem_first 4)) (stdin_model (hello b c d e f))
        (Ok (mkEffect 4 [(4096, [b, c, d, e])] []) m' evs) := by
  rw_refute

/-- THE DELIVERY, whole: with the destination able to hold everything the
stream could supply to this count, the admitted outcomes are exactly the
nonempty prefixes of the input of at most the count, each landing at
`buf`, one `ReadEv` per byte on channel 0, the stream advanced past
exactly them.  WHICH bytes is the input's; only HOW MANY is the
environment's (`anon_pipe_read` copies `buf->len` bytes of the buffer at
the head of the ring, fs/pipe.c:323, so a terminal or a pipe delivers
what it holds, not what was asked).  The last conjunct is the
destination: five writable bytes, stated as a bound on the length through
`wmem_first_five_window` rather than as the arm's own walk.  On this
fixture it excludes nothing the prefix conjunct does not already exclude —
the input is five bytes — and the arm's own pre-check (`read_bytes_map`
over the clamped take) declines before `choose` whenever that take
outruns the window, so the conjunct is carried for the statement's shape,
not for a case it decides.
rocq-twin: read_delivers_stream_prefix
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_delivers_a_prefix_iff (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 0 4096 100 (wmem_first 5)) (stdin_model (hello b c d e f)) o ↔
      ∃ bs : List byte,
        o = Ok (mkEffect (len_word bs) [(4096, bs)] [])
               (stdin_model (stream_take (hello b c d e f) bs.length).2)
               (List.map (ReadEv 0) bs)
        ∧ 1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ 100
        ∧ (stream_take (hello b c d e f) bs.length).1 = bs
        ∧ (bs.length : Int) ≤ 5 := by
  have h : syscall_spec (read_in 0 4096 100 (wmem_first 5)) (stdin_model (hello b c d e f)) o ↔
      ∃ bs : List byte,
        o = Ok (mkEffect (len_word bs) [(4096, bs)] [])
               (stdin_model (stream_take (hello b c d e f) bs.length).2)
               (List.map (ReadEv 0) bs)
        ∧ 1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ 100
        ∧ (stream_take (hello b c d e f) bs.length).1 = bs
        ∧ read_bytes_map (wmem_first 5) 4096 (len_word bs) ≠ none := by
    rw_norm
  rw [h]
  exact exists_congr fun bs => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun hc => and_congr_right fun _ => wmem_first_five_window bs hc

/-- The whole input in one read, leaving end of input behind.
probe: testing/syscall-check/tests/read_spec.c#conform --stdin hello -- chan 100 5 -/
theorem stdin_full_delivery (b c d e f : byte) :
    syscall_spec (read_in 0 4096 100 (wmem_first 5)) (stdin_model (hello b c d e f))
      (Ok (mkEffect 5 [(4096, [b, c, d, e, f])] []) (stdin_model IEof)
          [ReadEv 0 b, ReadEv 0 c, ReadEv 0 d, ReadEv 0 e, ReadEv 0 f]) := by
  rw_norm

/-- A SHORT read is real: one byte delivered, four left for the next call.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_short_delivery (b c d e f : byte) :
    syscall_spec (read_in 0 4096 100 (wmem_first 5)) (stdin_model (hello b c d e f))
      (Ok (mkEffect 1 [(4096, [b])] []) (stdin_model (ICons c (ICons d (ICons e (ICons f IEof)))))
          [ReadEv 0 b]) := by
  rw_norm

/-- Exactly the count: `read(0, buf, 5)` may deliver all five.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_exact_count_delivery (b c d e f : byte) :
    syscall_spec (read_in 0 4096 5 (wmem_first 5)) (stdin_model (hello b c d e f))
      (Ok (mkEffect 5 [(4096, [b, c, d, e, f])] []) (stdin_model IEof)
          [ReadEv 0 b, ReadEv 0 c, ReadEv 0 d, ReadEv 0 e, ReadEv 0 f]) := by
  rw_norm

/-- A 0 with input waiting is refused: only `IEof` answers 0 on a positive
count.
rocq-twin: read_eof_is_sticky
probe: testing/syscall-check/tests/read_spec.c#reject --stdin hello --mutate read:ret=0,drop-writes -- chan 100 5 -/
theorem stdin_zero_with_input_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 100 (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- The bytes are the INPUT's: "he" queued, "hh" delivered is refused.
probe: testing/syscall-check/tests/read_spec.c#reject --stdin hello --mutate read:poison-writes:57 -- chan 100 5 -/
theorem stdin_wrong_bytes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 100 (wmem_first 5)) (stdin_model (ICons 104 (ICons 101 IEof)))
        (Ok (mkEffect 2 [(4096, [104, 104])] []) m' evs) := by
  rw_refute

/-- Never more than the COUNT: `read(0, buf, 3)` with five bytes queued
cannot deliver five (`chars = total_len` caps the copy, fs/pipe.c:327-334, v6.18.46).
probe: testing/syscall-check/tests/read_spec.c#reject --stdin hello --mutate read:ret=5,grow-writes:1 -- chan 4 4 -/
theorem stdin_over_count_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 3 (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (mkEffect 5 [(4096, [b, c, d, e, f])] []) m' evs) := by
  rw_refute

/-- Never more than the INPUT holds: two bytes queued, three delivered is
refused — nothing is invented past the last byte written.
probe: testing/syscall-check/tests/read_spec.c#reject --stdin hello --mutate read:ret=6,grow-writes:1 -- chan 100 5 -/
theorem stdin_beyond_input_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 100 (wmem_first 5)) (stdin_model (ICons b (ICons c IEof)))
        (Ok (mkEffect 3 [(4096, [b, c, c])] []) m' evs) := by
  rw_refute

/-- The stream advances past EXACTLY the delivered bytes: a one-byte
delivery that claims to leave end of input behind dropped the tail.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_dropped_tail_rejected (b c : byte) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 100 (wmem_first 5)) (stdin_model (ICons b (ICons c IEof)))
        (Ok (mkEffect 1 [(4096, [b])] []) (stdin_model IEof) evs) := by
  -- `sys_norm` leaves `IEof = ICons c IEof → …`: the ground pass has
  -- unfolded the closed `IEof` on the left, so `IEof_ne_ICons` no longer
  -- matches it syntactically and is applied by name (they are defeq).
  rw_norm
  intro h
  exact absurd h (IEof_ne_ICons c IEof)

/-- The events are one `ReadEv` per byte on channel 0: a delivery that
emits nothing is refused…
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_no_events_rejected (b c d e f : byte) (m' : Model) :
    ¬ syscall_spec (read_in 0 4096 100 (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (mkEffect 1 [(4096, [b])] []) m' []) := by
  rw_refute

/-- …and so is one whose event names another channel.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_event_on_other_channel_rejected (b c d e f : byte) (m' : Model) :
    ¬ syscall_spec (read_in 0 4096 100 (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (mkEffect 1 [(4096, [b])] []) m' [ReadEv 7 b]) := by
  rw_refute

/-- -EINTR on a read: `read(0, buf, 1)` with one byte of input delivers it;
no model state admits the -EINTR a caught signal produces on a blocking
read (`anon_pipe_read` returns -ERESTARTSYS only from the wait at
fs/pipe.c:388, reached with nothing copied).
rocq-twin: read_channel_eintr_rejected
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_eintr_rejected (b : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 0 4096 1 (wmem_first 1)) (stdin_model (ICons b IEof))
        (Ok (mkEffect (errno_ret EINTR) [] []) m' evs) := by
  rw_refute

/-- …while the byte itself is delivered: the pairing that keeps the
refutation above from being vacuous.
rocq-twin: read_channel_eintr_rejected
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_one_byte_delivered (b : byte) :
    syscall_spec (read_in 0 4096 1 (wmem_first 1)) (stdin_model (ICons b IEof))
      (Ok (mkEffect 1 [(4096, [b])] []) (stdin_model IEof) [ReadEv 0 b]) := by
  rw_norm

/-! ## /dev/null

`null_fops` (drivers/char/mem.c:644-652, v6.18.46) installs `read_null` (:412-416)
as `.read` (:646), so `vfs_read` takes its `.read` branch
(fs/read_write.c:569-570, v6.18.46) and gets `return 0`: no byte lands, `f_pos` does
not move, the destination is never inspected. -/

/-- A read of /dev/null is 0 whatever the count and whether or not the
buffer is mapped.
probe: testing/syscall-check/tests/fs_path_not_regular.c#conform --no-fs-check -- readback -/
theorem devnull_read_is_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 8 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …never -EFAULT on the unmapped buffer: `read_null` copies nothing.
kernel: drivers/char/mem.c:read_null@v6.18.46 -/
theorem devnull_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 8 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- …and never a byte.
kernel: drivers/char/mem.c:read_null@v6.18.46 -/
theorem devnull_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 8 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect 1 [(4096, [0])] []) m' evs) := by
  rw_refute

/-! ## A directory

`generic_read_dir` (fs/libfs.c:224-227, v6.18.46) is `return -EISDIR`, and it is
the `.read` of every directory table in the tree (fs/libfs.c:234, :571,
:1770; fs/ext4/dir.c:685; all v6.18.46). -/

/-- A read on a directory fd is -EISDIR, resolved without touching the
(unmapped) destination.
kernel: fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem dir_is_eisdir (o : outcome SyscallEffect) :
    syscall_spec (read_in 5 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EISDIR) [] []) read_model [] := by
  rw_norm

/-- …never -EFAULT on the unmapped buffer, which `generic_read_dir` never
reads.
kernel: fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem dir_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 5 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- …and never 0.
kernel: fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem dir_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 5 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- THE ONE KIND WITHOUT A ZERO-COUNT SHORTCUT: `vfs_read` dispatches a
zero count to `generic_read_dir` like any other (fs/read_write.c:569-570,
v6.18.46), and `generic_read_dir` is `return -EISDIR` whatever the count
(fs/libfs.c:224-227).  So `read(dirfd, buf, 0)` is -EISDIR where every
other kind answers 0.
kernel: fs/read_write.c:vfs_read; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem dir_zero_count_is_eisdir (o : outcome SyscallEffect) :
    syscall_spec (read_in 5 4096 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EISDIR) [] []) read_model [] := by
  rw_norm

/-- …so the 0 the other kinds' shortcut would give is refused on a
directory.
kernel: fs/read_write.c:vfs_read; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem dir_zero_count_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 5 4096 0 wmem_none) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- A zero count at a buffer past the limit is still -EFAULT on a directory:
`vfs_read`'s access_ok (fs/read_write.c:560-561) asks about the ADDRESS
as well as the length, and it runs before `generic_read_dir`
(fs/libfs.c:224-227).
kernel: fs/read_write.c:vfs_read; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem dir_zero_count_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 5 (Z_to_bv 64 (2 ^ 63)) 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …so the -EISDIR of a model that tested the kind first is refused there.
kernel: fs/read_write.c:vfs_read; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem dir_zero_count_past_top_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 5 (Z_to_bv 64 (2 ^ 63)) 0 wmem_none) read_model
        (Ok (mkEffect (errno_ret EISDIR) [] []) m' evs) := by
  rw_refute

/-! ## Sockets: the count gate, then `tcp_recvmsg_locked`

The socket arm does not ask `access_ok` itself; it carries
`Uaccess.modeled_rw_range`, which admits every count at or below
`Uaccess.rw_bytes_max` and, above it, a range inside the address space.
A count past the bound whose range leaves the address space is DECLINED
where Linux answers -EFAULT (issue #666,
bugs/write-out-of-range-short-write.md) — a coverage gap the first pair
below records.  Past the gate, `sock_read_iter` (net/socket.c:1154-1174,
v6.18.46) hands a nonzero count to `tcp_recvmsg_locked` (net/ipv4/tcp.c:2634,
v6.18.46),
whose tests these pins fix in order: `TCP_LISTEN` → -ENOTCONN
(:2651-2653); then, with nothing copied, `SOCK_DONE` → 0 (:2741-2742),
`sk_err` → the pending error (:2744-2747), `RCV_SHUTDOWN` → 0
(:2749-2750), `TCP_CLOSE` → -ENOTCONN (:2752-2757). -/

/-- A count past `rw_bytes_max` at an address past the limit declines on a
socket: the arm has no -EFAULT of its own to give, where `vfs_read`'s
access_ok (fs/read_write.c:560-561) answers one.
kernel: fs/read_write.c:vfs_read; net/socket.c:sock_read_iter@v6.18.46 -/
theorem socket_big_out_of_range_count_declines (o : outcome SyscallEffect) :
    syscall_spec (read_in 10 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …and Linux's own answer there, -EFAULT from `vfs_read`'s `access_ok`,
is refused too: the gap is a decline, not a guess.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem socket_big_out_of_range_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 10 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- The same count inside the address space is JUDGED: a fresh socket
answers -ENOTCONN however large the request.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_big_in_range_count_is_judged (o : outcome SyscallEffect) :
    syscall_spec (read_in 10 4096 (Z_to_bv 64 (2 ^ 40)) wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret ENOTCONN) [] []) read_model [] := by
  rw_norm

/-- A FRESH socket never left `TCP_CLOSE`: -ENOTCONN at
net/ipv4/tcp.c:2752-2757 at v6.18.46, decided without touching the destination.
probe: testing/syscall-check/tests/socket_rw.c#conform -- rw -/
theorem fresh_socket_is_enotconn (o : outcome SyscallEffect) :
    syscall_spec (read_in 10 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret ENOTCONN) [] []) read_model [] := by
  rw_norm

/-- …not 0: a fresh socket does not report end of stream.
probe: testing/syscall-check/tests/socket_rw.c#reject --mutate read#2:ret=0 -- rw -/
theorem fresh_socket_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 10 4096 16 wmem_none) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …and not -EFAULT for the unmapped buffer, which is never reached.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem fresh_socket_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 10 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- A BOUND socket is still `TCP_CLOSE`: the same -ENOTCONN.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem bound_socket_is_enotconn (o : outcome SyscallEffect) :
    syscall_spec (read_in 11 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret ENOTCONN) [] []) read_model [] := by
  rw_norm

/-- A LISTENING socket is -ENOTCONN at the top of `tcp_recvmsg_locked`
(net/ipv4/tcp.c:2651-2653), before any queue is looked at.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem listening_socket_is_enotconn (o : outcome SyscallEffect) :
    syscall_spec (read_in 12 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret ENOTCONN) [] []) read_model [] := by
  rw_norm

/-- …and never delivers a byte.
probe: testing/syscall-check/tests/socket_rw.c#reject --mutate read#6:ret=1,smuggle-write:a1:1 -- rw -/
theorem listening_socket_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 12 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect 1 [(4096, [0])] []) m' evs) := by
  rw_refute

/-- The range verdict on a nonzero count under the bound: a fresh socket at
a buffer past the limit is -EFAULT, `vfs_read`'s, ahead of -ENOTCONN.
kernel: fs/read_write.c:vfs_read; net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem fresh_socket_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 10 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …so -ENOTCONN is refused there.
kernel: fs/read_write.c:vfs_read; net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem fresh_socket_past_top_enotconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 10 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret ENOTCONN) [] []) m' evs) := by
  rw_refute

/-! ## Sockets: end of stream, the pending error, and the read after it

`tcp_fin` (net/ipv4/tcp_input.c:4720, v6.18.46) sets `RCV_SHUTDOWN` (:4726)
and `SOCK_DONE` (:4727); `tcp_recvmsg_locked` tests `SOCK_DONE`
(net/ipv4/tcp.c:2741-2742, v6.18.46) BEFORE `sk_err` (:2744-2747), so end of stream
dominates a later error and is sticky.  `sock_error`
(include/net/sock.h:2486-2498, v6.18.46) reads the pending error with an
`xchg(&sk->sk_err, 0)` (:2496): reported once.  `tcp_done`
(net/ipv4/tcp.c:5020-5044, v6.18.46) sets `sk_shutdown = SHUTDOWN_MASK` (:5038) on
the reset path, and `RCV_SHUTDOWN` is tested (:2749-2750) IMMEDIATELY
ABOVE the `TCP_CLOSE` arm that answers -ENOTCONN (:2752-2757): the read
after the error is 0. -/

/-- The peer's FIN consumed in sequence: 0, sticky, the socket unchanged.
kernel: net/ipv4/tcp_input.c:tcp_fin; net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem fin_is_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 20 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- A FIN is not a reset.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate read#2:ret=-ECONNRESET --peer 68656c6c6f -- bytes -/
theorem fin_connreset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 20 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret ECONNRESET) [] []) m' evs) := by
  rw_refute

/-- Nothing follows a FIN.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate read#2:ret=1,smuggle-write:a1:1 --peer 68656c6c6f -- bytes -/
theorem fin_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 20 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect 1 [(4096, [0])] []) m' evs) := by
  rw_refute

/-- The range verdict ahead of the FIN: -EFAULT from `vfs_read`'s
access_ok (fs/read_write.c:560-561), the protocol never reached.
kernel: fs/read_write.c:vfs_read; net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem fin_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 20 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- A reset at the head of the script: -ECONNRESET, reported ONCE — the
socket moves to `SkReset` and no byte moves.
probe: testing/syscall-check/tests/socket_read_peer.c#conform --peer 6869:rst -- rst -/
theorem rst_is_connreset_once (o : outcome SyscallEffect) :
    syscall_spec (read_in 21 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret ECONNRESET) [] [])
             (with_fds (fd_insert read_fds 21 (.FdSocket (.SkReset peer_a 7))) read_model) [] := by
  rw_norm

/-- The reset is reported, not swallowed.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate read#2:ret=0 --peer 6869:rst -- rst -/
theorem rst_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 21 4096 16 wmem_none) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- A RST is -ECONNRESET, not -ETIMEDOUT.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate read#2:ret=-ETIMEDOUT --peer 6869:rst -- rst -/
theorem rst_etimedout_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 21 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret ETIMEDOUT) [] []) m' evs) := by
  rw_refute

/-- …and the error is CONSUMED by the read that reports it: an
-ECONNRESET that leaves the socket as it was is refused (`sock_error`'s
`xchg`, include/net/sock.h:2496).
kernel: include/net/sock.h:sock_error@v6.18.46 -/
theorem rst_left_pending_rejected (evs : List event) :
    ¬ syscall_spec (read_in 21 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret ECONNRESET) [] []) read_model evs) := by
  rw_refute

/-- The read AFTER the error is 0: `RCV_SHUTDOWN` (`tcp_done`'s
`SHUTDOWN_MASK`) is tested above the `TCP_CLOSE` arm.
probe: testing/syscall-check/tests/socket_read_peer.c#conform --peer 6869:rst -- rst -/
theorem reset_socket_reads_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 13 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …NOT -ENOTCONN, which a model testing `TCP_CLOSE` first would say.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate read#3:ret=-ENOTCONN --peer 6869:rst -- rst -/
theorem reset_socket_enotconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 13 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret ENOTCONN) [] []) m' evs) := by
  rw_refute

/-- …and not -ECONNRESET again: reported once.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate read#3:ret=-ECONNRESET --peer 6869:rst -- rst -/
theorem reset_socket_connreset_again_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 13 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret ECONNRESET) [] []) m' evs) := by
  rw_refute

/-- The range verdict on the reset socket too: `vfs_read`'s access_ok
(fs/read_write.c:560-561) answers -EFAULT before `tcp_recvmsg_locked`
reaches the `RCV_SHUTDOWN` test that would give 0.
kernel: fs/read_write.c:vfs_read; net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem reset_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 13 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- A timeout at the head of the script: -ETIMEDOUT once, the socket moved
to `SkReset` exactly as after a reset.  The errno is the one `tcp_write_err`
(net/ipv4/tcp_timer.c:76-80) hands to `tcp_done_with_error` when the
retransmit timer gives up — `sk->sk_err_soft ? : ETIMEDOUT` (:78) — and
`sock_error` reports it once.
kernel: net/ipv4/tcp_timer.c:tcp_write_err; include/net/sock.h:sock_error@v6.18.46 -/
theorem timedout_is_etimedout_once (o : outcome SyscallEffect) :
    syscall_spec (read_in 22 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret ETIMEDOUT) [] [])
             (with_fds (fd_insert read_fds 22 (.FdSocket (.SkReset peer_a 7))) read_model) [] := by
  rw_norm

/-- A timeout is not a reset.
kernel: include/net/sock.h:sock_error@v6.18.46 -/
theorem timedout_connreset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 22 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret ECONNRESET) [] []) m' evs) := by
  rw_refute

/-- …and, like the reset, consumed by the read that reports it: an
-ETIMEDOUT that leaves the socket as it was is refused.
kernel: include/net/sock.h:sock_error@v6.18.46 -/
theorem timedout_left_pending_rejected (evs : List event) :
    ¬ syscall_spec (read_in 22 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret ETIMEDOUT) [] []) read_model evs) := by
  rw_refute

/-- The range verdict on a pending error: -EFAULT from `vfs_read`, and the
protocol NEVER REACHED, so the error stays pending — the socket is
unchanged, not `SkReset`.
kernel: fs/read_write.c:vfs_read; include/net/sock.h:sock_error@v6.18.46 -/
theorem rst_past_top_is_efault_and_stays_pending (o : outcome SyscallEffect) :
    syscall_spec (read_in 21 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …so -ECONNRESET is refused there.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem rst_past_top_connreset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 21 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret ECONNRESET) [] []) m' evs) := by
  rw_refute

/-- The same on a pending timeout: -EFAULT from `vfs_read`, `sock_error`
never consulted, so -ETIMEDOUT stays pending and the socket is unchanged.
kernel: fs/read_write.c:vfs_read; include/net/sock.h:sock_error@v6.18.46 -/
theorem timedout_past_top_is_efault_and_stays_pending (o : outcome SyscallEffect) :
    syscall_spec (read_in 22 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …so -ETIMEDOUT is refused there.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem timedout_past_top_etimedout_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 22 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret ETIMEDOUT) [] []) m' evs) := by
  rw_refute

/-! ## Sockets: the delivery

`tcp_recvmsg_locked` walks `sk_receive_queue` (net/ipv4/tcp.c:2703, v6.18.46)
copying `used = skb->len - offset` (:2794) capped at `len`, and `target`
(:2685, 1 by default) governs only whether to BLOCK for more, never when
to stop copying: any length in `[1, count]` of what is queued in sequence
is possible, and the events land on the CONNECTION's channel.  Queued
bytes preempt a pending error by representation: the error is only ever
the head of the script. -/

/-- THE DELIVERY on a connected socket: exactly the nonempty prefixes of
the peer's script of at most the count, each landing at `buf`, one
`ReadEv` per byte on the connection's channel, the script advanced past
exactly them.  The last conjunct is the destination's five writable
bytes as a bound on the length (`wmem_first_five_window`), not the arm's
own walk; on a two-byte script it decides nothing the prefix conjunct
does not (the note on `stdin_delivers_a_prefix_iff`).  The count's bound
is tested where it bites by `socket_count_caps_the_delivery` and
`socket_over_count_rejected`.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_delivers_a_prefix_iff (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 25 4096 100 (wmem_first 5)) (socket_model (NCons b (NCons c NFin))) o ↔
      ∃ bs : List byte,
        o = Ok (mkEffect (len_word bs) [(4096, bs)] [])
               (with_fds (fd_insert (socket_fds (NCons b (NCons c NFin))) 25
                   (.FdSocket (.SkConnected peer_a 7 (net_take (NCons b (NCons c NFin)) bs.length).2)))
                 (socket_model (NCons b (NCons c NFin))))
               (List.map (ReadEv 7) bs)
        ∧ 1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ 100
        ∧ (net_take (NCons b (NCons c NFin)) bs.length).1 = bs
        ∧ (bs.length : Int) ≤ 5 := by
  have h : syscall_spec (read_in 25 4096 100 (wmem_first 5)) (socket_model (NCons b (NCons c NFin))) o ↔
      ∃ bs : List byte,
        o = Ok (mkEffect (len_word bs) [(4096, bs)] [])
               (with_fds (fd_insert (socket_fds (NCons b (NCons c NFin))) 25
                   (.FdSocket (.SkConnected peer_a 7 (net_take (NCons b (NCons c NFin)) bs.length).2)))
                 (socket_model (NCons b (NCons c NFin))))
               (List.map (ReadEv 7) bs)
        ∧ 1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ 100
        ∧ (net_take (NCons b (NCons c NFin)) bs.length).1 = bs
        ∧ read_bytes_map (wmem_first 5) 4096 (len_word bs) ≠ none := by
    rw_norm
  rw [h]
  exact exists_congr fun bs => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun hc => and_congr_right fun _ => wmem_first_five_window bs hc

/-- Everything queued in one call, the FIN left at the head for the next.
probe: testing/syscall-check/tests/socket_read_peer.c#conform --peer 68656c6c6f -- bytes -/
theorem socket_full_delivery (b c : byte) :
    syscall_spec (read_in 25 4096 100 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
      (Ok (mkEffect 2 [(4096, [b, c])] [])
          (with_fds (fd_insert (socket_fds (NCons b (NCons c NFin))) 25
              (.FdSocket (.SkConnected peer_a 7 NFin)))
            (socket_model (NCons b (NCons c NFin))))
          [ReadEv 7 b, ReadEv 7 c]) := by
  rw_norm

/-- A SHORT read: one byte, the other still queued — what
`tcp_recvmsg_locked` answers when one byte had arrived by the time
`target` (net/ipv4/tcp.c:2685) was met and the second had not.  The probe's
`short` case is the COUNT's cap, `socket_count_caps_the_delivery`: its
peer's five bytes arrive as one segment and the probe asserts exactly two
at a count of two, so a run cannot witness the environment's short read.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_short_delivery (b c : byte) :
    syscall_spec (read_in 25 4096 100 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
      (Ok (mkEffect 1 [(4096, [b])] [])
          (with_fds (fd_insert (socket_fds (NCons b (NCons c NFin))) 25
              (.FdSocket (.SkConnected peer_a 7 (NCons c NFin))))
            (socket_model (NCons b (NCons c NFin))))
          [ReadEv 7 b]) := by
  rw_norm

/-- THE COUNT CAPS THE DELIVERY: one byte asked of two queued is that byte,
the other left on the script — `tcp_recvmsg_locked` copies
`used = min(skb->len - offset, len)` (net/ipv4/tcp.c:2792-2796, v6.18.46).
At a count of one the arm's `choose` admits exactly the one-byte prefix,
so the `iff` holds too; it is stated as membership, the shape of
`stdin_one_byte_delivered`, because `sys_norm` closes the membership and
not the existential the `iff` leaves, and the refutation below is the
other half.
probe: testing/syscall-check/tests/socket_read_peer.c#conform --peer 68656c6c6f -- short -/
theorem socket_count_caps_the_delivery (b c : byte) :
    syscall_spec (read_in 25 4096 1 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
      (Ok (mkEffect 1 [(4096, [b])] [])
          (with_fds (fd_insert (socket_fds (NCons b (NCons c NFin))) 25
              (.FdSocket (.SkConnected peer_a 7 (NCons c NFin))))
            (socket_model (NCons b (NCons c NFin))))
          [ReadEv 7 b]) := by
  rw_norm

/-- …so both bytes at a count of one is refused: the `bs.length ≤ count`
conjunct, which no pin at a count above the queue can test.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate read#1:ret=5 --peer 68656c6c6f -- short -/
theorem socket_over_count_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 25 4096 1 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
        (Ok (mkEffect 2 [(4096, [b, c])] []) m' evs) := by
  rw_refute

/-- Exactly the count: `read(fd, buf, 2)` may deliver both.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_exact_count_delivery (b c : byte) :
    syscall_spec (read_in 25 4096 2 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
      (Ok (mkEffect 2 [(4096, [b, c])] [])
          (with_fds (fd_insert (socket_fds (NCons b (NCons c NFin))) 25
              (.FdSocket (.SkConnected peer_a 7 NFin)))
            (socket_model (NCons b (NCons c NFin))))
          [ReadEv 7 b, ReadEv 7 c]) := by
  rw_norm

/-- Queued bytes are not end of stream.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate read#1:ret=0 --peer 68656c6c6f -- bytes -/
theorem socket_zero_with_bytes_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 25 4096 100 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- Never more than the peer sent.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate read#1:ret=6,grow-writes:1 --peer 68656c6c6f -- bytes -/
theorem socket_over_queue_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 25 4096 100 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
        (Ok (mkEffect 3 [(4096, [b, c, c])] []) m' evs) := by
  rw_refute

/-- The bytes are the PEER's: "hi" queued, "hh" delivered is refused.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate read#1:poison-writes:41 --peer 68656c6c6f -- bytes -/
theorem socket_wrong_bytes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 25 4096 100 (wmem_first 5)) (socket_model (NCons 104 (NCons 105 NFin)))
        (Ok (mkEffect 2 [(4096, [104, 104])] []) m' evs) := by
  rw_refute

/-- The events name the CONNECTION's channel, not stdin's.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_event_on_stdin_channel_rejected (b c : byte) (m' : Model) :
    ¬ syscall_spec (read_in 25 4096 100 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
        (Ok (mkEffect 1 [(4096, [b])] []) m' [ReadEv 0 b]) := by
  rw_refute

/-- Not one byte writable: -EFAULT, nothing delivered, the script not
consumed — the socket unchanged.
kernel: include/linux/uaccess.h:_inline_copy_to_user; net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_unwritable_is_efault (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 25 4096 100 wmem_none) (socket_model (NCons b (NCons c NFin))) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (socket_model (NCons b (NCons c NFin))) [] := by
  rw_norm

/-- Only the first byte writable with two queued: the skb boundaries
decide Linux's answer, so the model declines (a coverage gap).
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_partial_destination_declines (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 25 4096 100 (wmem_first 1)) (socket_model (NCons b (NCons c NFin))) o ↔
      o = Unmodeled := by
  rw_norm

/-- Queued bytes PREEMPT a pending error: with a byte ahead of the reset,
the read delivers the byte and the reset waits.
probe: testing/syscall-check/tests/socket_read_peer.c#conform --peer 6869:rst -- rst -/
theorem socket_byte_before_rst_delivered (b : byte) :
    syscall_spec (read_in 25 4096 4 (wmem_first 5)) (socket_model (NCons b NRst))
      (Ok (mkEffect 1 [(4096, [b])] [])
          (with_fds (fd_insert (socket_fds (NCons b NRst)) 25
              (.FdSocket (.SkConnected peer_a 7 NRst)))
            (socket_model (NCons b NRst)))
          [ReadEv 7 b]) := by
  rw_norm

/-- …so -ECONNRESET with a byte still queued is refused.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate read#1:ret=-ECONNRESET --peer 6869:rst -- rst -/
theorem socket_rst_before_bytes_rejected (b : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 25 4096 4 (wmem_first 5)) (socket_model (NCons b NRst))
        (Ok (mkEffect (errno_ret ECONNRESET) [] []) m' evs) := by
  rw_refute

/-- …and the terminal is never read as a byte: two bytes out of `b, RST`
is refused.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_terminal_as_byte_rejected (b : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 25 4096 4 (wmem_first 5)) (socket_model (NCons b NRst))
        (Ok (mkEffect 2 [(4096, [b, b])] []) m' evs) := by
  rw_refute

/-! ## A regular file

Deterministic: the file's bytes at the fd's offset, truncated at end of
file (`shmem_file_read_iter`, mm/shmem.c:3370 at v6.18.46, breaks at
`iocb->ki_pos >= i_size`, :3388-3389) and at the `MAX_RW_COUNT` clamp
(fs/read_write.c:566-567, v6.18.46); the offset advances by the delivered length
(`ksys_read` writes `f_pos` back, :716-717); no trace events.  The
destination rule is `copy_to_user`'s. -/

/-- `read(3, buf, 100)` on "hi" at offset 0 delivers both bytes and moves
the offset to 2: the ONE admitted outcome.
probe: testing/syscall-check/tests/read_spec.c#conform --mutate read:wmem-hide:a1+3:4096 -- file -/
theorem file_read_is_deterministic (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 4096 100 (wmem_first 2)) read_model o ↔
      o = Ok (mkEffect 2 [(4096, [104, 105])] [])
             (with_fds (fd_insert read_fds 3 (.FdFile [102] 2)) read_model) [] := by
  rw_norm

/-- A file read is never SHORT of what the file holds: `shmem_file_read_iter`
copies up to `end_offset = min_t(loff_t, i_size, iocb->ki_pos + to->count)`
(mm/shmem.c:3423, v6.18.46), `nr = min_t(loff_t, end_offset - iocb->ki_pos,
fsize - offset)` bytes per folio (:3429), and loops until the request or
the file is exhausted.
probe: testing/syscall-check/tests/read_spec.c#reject --mutate read:ret=2,trunc-writes:2 -- file -/
theorem file_short_read_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 4096 100 (wmem_first 2)) read_model
        (Ok (mkEffect 1 [(4096, [104])] []) m' evs) := by
  rw_refute

/-- The bytes are the file's.
probe: testing/syscall-check/tests/read_spec.c#reject --mutate read:poison-writes:57 -- file -/
theorem file_wrong_bytes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 4096 100 (wmem_first 2)) read_model
        (Ok (mkEffect 2 [(4096, [57, 57])] []) m' evs) := by
  rw_refute

/-- The delivered bytes must be recorded: a count with no write is refused.
probe: testing/syscall-check/tests/read_spec.c#reject --mutate read:drop-writes -- file -/
theorem file_dropped_writes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 4096 100 (wmem_first 2)) read_model
        (Ok (mkEffect 2 [] []) m' evs) := by
  rw_refute

/-- The offset ADVANCES: a delivery that leaves the descriptor where it was
is refused.
kernel: fs/read_write.c:ksys_read@v6.18.46 -/
theorem file_offset_not_advanced_rejected (evs : List event) :
    ¬ syscall_spec (read_in 3 4096 100 (wmem_first 2)) read_model
        (Ok (mkEffect 2 [(4096, [104, 105])] []) read_model evs) := by
  rw_refute

/-- No trace events for a file: its contents are observed at exit.
kernel: fs/read_write.c:ksys_read@v6.18.46 -/
theorem file_events_rejected (m' : Model) :
    ¬ syscall_spec (read_in 3 4096 100 (wmem_first 2)) read_model
        (Ok (mkEffect 2 [(4096, [104, 105])] []) m' [ReadEv 0 104, ReadEv 0 105]) := by
  rw_refute

/-- The offset decides the bytes: one byte in, the tail "i" is delivered
and the offset moves to 2.
probe: testing/syscall-check/tests/read_spec.c#conform --mutate read#2:wmem-hide:a1+2:4096 -- filemid -/
theorem file_mid_offset_reads_the_tail (o : outcome SyscallEffect) :
    syscall_spec (read_in 23 4096 100 (wmem_first 1)) read_model o ↔
      o = Ok (mkEffect 1 [(4096, [105])] [])
             (with_fds (fd_insert read_fds 23 (.FdFile [102] 2)) read_model) [] := by
  rw_norm

/-- THE COUNT CAPS THE DELIVERY on a file: one byte asked of "hi" at
offset 0 is `[104]`, the offset moved to 1 and "i" left for the next read
— `shmem_file_read_iter` stops at `iocb->ki_pos + to->count`
(mm/shmem.c:3423, v6.18.46).  The probe's first read is this call.
probe: testing/syscall-check/tests/read_spec.c#conform --mutate read#2:wmem-hide:a1+2:4096 -- filemid -/
theorem file_count_caps_the_delivery (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 4096 1 (wmem_first 2)) read_model o ↔
      o = Ok (mkEffect 1 [(4096, [104])] [])
             (with_fds (fd_insert read_fds 3 (.FdFile [102] 1)) read_model) [] := by
  rw_norm

/-- …so the whole file at a count of one is refused, the destination
able to hold it: a port taking the file's bytes regardless of the count
passes every pin whose count exceeds what remains.
kernel: mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem file_over_count_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 4096 1 (wmem_first 2)) read_model
        (Ok (mkEffect 2 [(4096, [104, 105])] []) m' evs) := by
  rw_refute

/-- At end of file the answer is 0, the descriptor written back with its
offset unmoved (`ksys_read`, fs/read_write.c:716-717, v6.18.46), and the unmapped
destination never inspected.
probe: testing/syscall-check/tests/read_spec.c#conform --mutate read#2:wmem-none -- file2 -/
theorem file_at_eof_is_zero (o : outcome SyscallEffect) :
    syscall_spec (read_in 6 4096 100 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) (with_fds (fd_insert read_fds 6 (.FdFile [102] 2)) read_model) [] := by
  rw_norm

/-- …never -EFAULT.
probe: testing/syscall-check/tests/read_spec.c#reject --mutate read#2:wmem-none,ret=-EFAULT -- file2 -/
theorem file_at_eof_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 6 4096 100 wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- …and no byte from past the end.
probe: testing/syscall-check/tests/rw_bytes_bound.c#reject --mutate read:ret=11,smuggle-write:a1:11 -- seek-eof -/
theorem file_at_eof_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 6 4096 100 (wmem_first 16)) read_model
        (Ok (mkEffect 1 [(4096, [0])] []) m' evs) := by
  rw_refute

/-- Not one delivered byte writable: -EFAULT with the offset unchanged.
probe: testing/syscall-check/tests/read_spec.c#conform --mutate read:wmem-none,ret=-EFAULT,drop-writes -- file -/
theorem file_unwritable_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 4096 100 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …never 0.
probe: testing/syscall-check/tests/read_spec.c#reject --mutate read:wmem-none,ret=0,drop-writes -- file -/
theorem file_unwritable_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 4096 100 wmem_none) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …never a delivery.
probe: testing/syscall-check/tests/read_spec.c#reject --mutate read:wmem-none -- file -/
theorem file_unwritable_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 4096 100 wmem_none) read_model
        (Ok (mkEffect 2 [(4096, [104, 105])] []) m' evs) := by
  rw_refute

/-- A hole inside the delivered prefix declines: the count Linux answers is
the copy routine's rounded progress (a coverage gap).
probe: testing/syscall-check/tests/read_spec.c#fail-closed --mutate read:wmem-hide:a1+2:1 -- file -/
theorem file_partial_destination_declines (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 4096 100 (wmem_first 1)) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-- A count one past `MAX_RW_COUNT` on the two-byte file is JUDGED and
delivers the two bytes: the clamp (fs/read_write.c:566-567, v6.18.46)
truncates nothing a shorter file cannot supply, and the return is the
delivered length.  The clamp's own value is not observable on a two-byte
file; its pins are PR #804's, in `Checks/Cases/State.lean`.  No probe in
the tree names a count past `MAX_RW_COUNT` that passes access_ok:
`rw_bytes_bound.c`'s `r-over` sits at 131073, under the clamp, and
`read_window.c`'s `win-at` runs to TASK_SIZE from a mapping a gibibyte or
two below it, so the count the kernel saw there is under the clamp too.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem file_over_clamp_count_delivers_the_file :
    syscall_spec (read_in 3 4096 (Z_to_bv 64 0x7ffff001) (wmem_first 2)) read_model
      (Ok (mkEffect 2 [(4096, [104, 105])] [])
          (with_fds (fd_insert read_fds 3 (.FdFile [102] 2)) read_model) []) := by
  rw_norm

/-- …and the RAW count as the return is refused: a read returns what it
delivered.  This is the two-byte instance of Rocq's symbolic
`read_ret_over_clamp_rejected`, and only its return-is-the-delivery half:
with a two-byte file the clamp itself is not what refuses the count, and
no probe returns a raw count past it to be refused.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem file_over_clamp_raw_count_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 3 4096 (Z_to_bv 64 0x7ffff001) (wmem_first 2)) read_model
        (Ok (mkEffect (Z_to_bv 64 0x7ffff001) [(4096, [104, 105])] []) m' evs) := by
  rw_refute

/-- A path the file system does not hold declines: `openat` never mints
such a descriptor, so this is a state no run reaches.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem file_path_absent_declines (o : outcome SyscallEffect) :
    syscall_spec (read_in 7 4096 100 (wmem_first 2)) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-! ## /dev/urandom

`urandom_read_iter` (drivers/char/random.c:1453-1475, v6.18.46) is
`get_random_bytes_user` (:434-482) over the imported iterator: a
nonempty request is filled whole (:455-478), never waited for, so the
device delivers exactly the clamped count from the run's declared
stream and nothing reaches the trace. -/

/-- `read(24, buf, 2)` against a two-byte declared stream delivers both
bytes, advances the stream to its end and emits nothing: the ONE
admitted outcome.
kernel: drivers/char/random.c:urandom_read_iter,get_random_bytes_user@v6.18.46 -/
theorem urandom_read_is_deterministic (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 24 4096 2 (wmem_first 2)) (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect 2 [(4096, [b, c])] []) (urandom_model IEof) [] := by
  rw_norm

/-- The device is never short of a request it can fill.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem urandom_short_read_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 24 4096 2 (wmem_first 2)) (urandom_model (ICons b (ICons c IEof)))
        (Ok (mkEffect 1 [(4096, [b])] []) m' evs) := by
  rw_refute

/-- The bytes are the DECLARED stream's, in order.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem urandom_wrong_bytes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 24 4096 2 (wmem_first 2)) (urandom_model (ICons 104 (ICons 105 IEof)))
        (Ok (mkEffect 2 [(4096, [105, 104])] []) m' evs) := by
  rw_refute

/-- Nothing reaches the trace from the device.
kernel: drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem urandom_events_rejected (b c : byte) (m' : Model) :
    ¬ syscall_spec (read_in 24 4096 2 (wmem_first 2)) (urandom_model (ICons b (ICons c IEof)))
        (Ok (mkEffect 2 [(4096, [b, c])] []) m' [ReadEv 0 b, ReadEv 0 c]) := by
  rw_refute

/-- THE COUNT CAPS THE DELIVERY on the device too: one byte asked of a
two-byte declaration is one byte, the second left declared —
`get_random_bytes_user` fills the request's length and no more
(drivers/char/random.c:455-478, v6.18.46).
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem urandom_count_caps_the_delivery (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 24 4096 1 (wmem_first 2)) (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect 1 [(4096, [b])] []) (urandom_model (ICons c IEof)) [] := by
  rw_norm

/-- …so both declared bytes at a count of one is refused.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem urandom_over_count_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 24 4096 1 (wmem_first 2)) (urandom_model (ICons b (ICons c IEof)))
        (Ok (mkEffect 2 [(4096, [b, c])] []) m' evs) := by
  rw_refute

/-- The stream RUNNING OUT is a decline: three bytes asked of a two-byte
declaration is an environment that stopped answering where the device
never does.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem urandom_stream_short_declines (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 24 4096 3 (wmem_first 3)) (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Unmodeled := by
  rw_norm

/-- …so the two-byte short read is refused too, as a decline.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem urandom_stream_short_read_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 24 4096 3 (wmem_first 3)) (urandom_model (ICons b (ICons c IEof)))
        (Ok (mkEffect 2 [(4096, [b, c])] []) m' evs) := by
  rw_refute

/-- Not one byte writable: `copy_to_iter` copies nothing and
`return ret ? ret : -EFAULT` (drivers/char/random.c:481) fires; the
stream is not consumed.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem urandom_unwritable_is_efault (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 24 4096 2 wmem_none) (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons b (ICons c IEof))) [] := by
  rw_norm

/-- Only the first byte writable: the copy's rounded progress decides
Linux's count, so the model declines (a coverage gap).
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem urandom_partial_destination_declines (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (read_in 24 4096 2 (wmem_first 1)) (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Unmodeled := by
  rw_norm

/-! ## A pipe's read end

Everything here is `anon_pipe_read` (fs/pipe.c:269, v6.18.46), the `.read_iter`
`pipeanon_fops` installs on both ends (:1257-1266, :1259).  A nonempty
queue delivers EXACTLY `min count (length q)`: `chars = buf->len` (:323)
capped at `total_len` (:327-334), the loop continuing while bytes remain
and the ring is not empty (:363-367), and `if (ret) break;` (:372-373)
ahead of the only wait (:388).  An empty queue is end of file when no
writer is left (:370-371) and a BLOCK otherwise. -/

/-- `read(14, buf, 100)` on a pipe holding "ab" delivers both bytes and
leaves the queue empty with its page mark in place: the ONE admitted
outcome.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- rt -/
theorem pipe_read_delivers_the_queue (o : outcome SyscallEffect) :
    syscall_spec (read_in 14 4096 100 (wmem_first 2)) read_model o ↔
      o = Ok (mkEffect 2 [(4096, [97, 98])] [])
             (with_pipes (pipe_insert read_pipes 0 ([], 2)) read_model) [] := by
  rw_norm

/-- A pipe read is never short of `min count (length q)`.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate read:ret=4 -- rt -/
theorem pipe_short_read_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 14 4096 100 (wmem_first 2)) read_model
        (Ok (mkEffect 1 [(4096, [97])] []) m' evs) := by
  rw_refute

/-- The bytes are the ones written in.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate read:poison-writes:57 -- rt -/
theorem pipe_wrong_bytes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 14 4096 100 (wmem_first 2)) read_model
        (Ok (mkEffect 2 [(4096, [57, 57])] []) m' evs) := by
  rw_refute

/-- The queue is CONSUMED: a delivery that leaves the two bytes queued is
refused (`buf->offset += chars; buf->len -= chars`, fs/pipe.c:350-351).
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_queue_not_consumed_rejected (evs : List event) :
    ¬ syscall_spec (read_in 14 4096 100 (wmem_first 2)) read_model
        (Ok (mkEffect 2 [(4096, [97, 98])] []) read_model evs) := by
  rw_refute

/-- The COUNT caps the delivery: `read(14, buf, 1)` takes "a" and leaves
"b" queued under the same page mark.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_count_caps_the_delivery (o : outcome SyscallEffect) :
    syscall_spec (read_in 14 4096 1 (wmem_first 2)) read_model o ↔
      o = Ok (mkEffect 1 [(4096, [97])] [])
             (with_pipes (pipe_insert read_pipes 0 ([98], 2)) read_model) [] := by
  rw_norm

/-- A pipe read one byte over the OLD 128 KiB ceiling is JUDGED and delivers
the whole queue: the count never reaches a unary numeral.
rocq-twin: pipe_read_over_rw_bytes_max_is_judged
probe: testing/syscall-check/tests/read_window.c#conform -- pipe-over -/
theorem pipe_read_over_rw_bytes_max_is_judged :
    syscall_spec (read_in 14 4096 (Z_to_bv 64 (rw_bytes_max + 1)) (wmem_first 2)) read_model
      (Ok (mkEffect 2 [(4096, [97, 98])] [])
          (with_pipes (pipe_insert read_pipes 0 ([], 2)) read_model) []) := by
  rw_norm

/-- …and is not short there either: `anon_pipe_read` takes the whole
buffer at the head of the ring, `chars = buf->len` capped at `total_len`
(fs/pipe.c:323-334).  The probe's lies at this count are the 0 of end of
file with bytes queued, a byte too many and the retired cap — none a
short delivery; the one-of-two here is refused on the same walk.
rocq-twin: pipe_read_over_rw_bytes_max_is_judged
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_read_over_rw_bytes_max_short_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 14 4096 (Z_to_bv 64 (rw_bytes_max + 1)) (wmem_first 2)) read_model
        (Ok (mkEffect 1 [(4096, [97])] []) m' evs) := by
  rw_refute

/-- Not one byte writable: -EFAULT and the queue untouched.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_unwritable_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 14 4096 100 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- One byte writable, two queued: the pipe's buffer boundaries decide
Linux's answer, so the model declines (a coverage gap).
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_partial_destination_declines (o : outcome SyscallEffect) :
    syscall_spec (read_in 14 4096 100 (wmem_first 1)) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-- AN EMPTY PIPE WITH A LIVE WRITER HAS NO ANSWER: `anon_pipe_read` falls
past `if (!pipe->writers) break;` (fs/pipe.c:370-371) to the
`wait_event_interruptible_exclusive` at :388 and sleeps; the model has no
blocking and no O_NONBLOCK (-EAGAIN, :374-378), so the intersection with
a model that never waits is empty and it declines.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_empty_with_writer_declines (o : outcome SyscallEffect) :
    syscall_spec (read_in 16 4096 16 (wmem_first 16)) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …not end of file: a writer is alive, so the 0 of the `!pipe->writers`
break (fs/pipe.c:370-371) is never reached; Linux sleeps at :388 instead.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_empty_with_writer_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 16 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …and not -EAGAIN: no modeled pipe is O_NONBLOCK.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_empty_with_writer_eagain_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 16 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  rw_refute

/-- With no writer left an empty pipe is END OF FILE: the break at
fs/pipe.c:370-371 at v6.18.46 with `ret` still 0 — what makes closing the write end
observable.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- eof -/
theorem pipe_empty_without_writer_is_eof (o : outcome SyscallEffect) :
    syscall_spec (read_in 18 4096 16 (wmem_first 16)) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- End of file on a pipe is sticky: no later delivery.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate read#3:ret=1,smuggle-write:a1:1 -- eof -/
theorem pipe_eof_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 18 4096 16 (wmem_first 16)) read_model
        (Ok (mkEffect 1 [(4096, [0])] []) m' evs) := by
  rw_refute

/-- End of file on a pipe never inspects the destination: the break at
fs/pipe.c:370-371 (v6.18.46) comes before any `copy_page_to_iter` (:343-348),
so an in-range unwritable buffer still reads 0.
probe: testing/syscall-check/tests/pipe2_spec.c#conform --mutate read:wmem-none -- eofwmem -/
theorem pipe_eof_never_inspects_the_destination (o : outcome SyscallEffect) :
    syscall_spec (read_in 18 4096 16 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …so it is never -EFAULT.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate read:wmem-none,ret=-EFAULT -- eofwmem -/
theorem pipe_eof_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 18 4096 16 wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- The range verdict AHEAD of end of file: `vfs_read`'s access_ok
(fs/read_write.c:560-561, v6.18.46) answers -EFAULT before `anon_pipe_read`
is dispatched, so a writer-less empty pipe at a buffer past the top is
-EFAULT, not 0 — the FIN's `fin_past_top_is_efault`, on a pipe.  This is
the `access_ok_zero` on the arm's end-of-file path, which no in-range pin
above can tell from a plain 0.
kernel: fs/read_write.c:vfs_read; fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_eof_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 18 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …so the 0 of end of file is refused there: a twin answering it on
this path without the range test passes every in-range pin above.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pipe_eof_past_top_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 18 (Z_to_bv 64 (2 ^ 63)) 16 wmem_none) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- A pipe id the table does not hold declines: `pipe2` never mints one.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_id_absent_declines (o : outcome SyscallEffect) :
    syscall_spec (read_in 19 4096 16 (wmem_first 16)) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-- A count past `rw_bytes_max` at an address past the limit declines on a
pipe, as on a socket: no -EFAULT of the arm's own.
probe: testing/syscall-check/tests/read_window.c#fail-closed --expect-unmodeled read -- pipe-hi -/
theorem pipe_big_out_of_range_count_declines (o : outcome SyscallEffect) :
    syscall_spec (read_in 14 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …with Linux's -EFAULT refused there as well.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pipe_big_out_of_range_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 14 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- The same count inside the address space is JUDGED and delivers the
queue: access_ok passes at `buf = 4096`, the clamp (fs/read_write.c:566-567)
runs, and `anon_pipe_read` hands over what is queued.  The probe at this
shape, `read_window.c`'s `pipe-over`, sits at `rw_bytes_max + 1` and is
`pipe_read_over_rw_bytes_max_is_judged`'s; no probe reads a pipe at 2^40
in range.
kernel: fs/read_write.c:vfs_read; fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_big_in_range_count_delivers :
    syscall_spec (read_in 14 4096 (Z_to_bv 64 (2 ^ 40)) (wmem_first 2)) read_model
      (Ok (mkEffect 2 [(4096, [97, 98])] [])
          (with_pipes (pipe_insert read_pipes 0 ([], 2)) read_model) []) := by
  rw_norm

/-- THE GATE'S EDGE, on the count alone.  At an out-of-range buffer the
first disjunct of `Uaccess.modeled_rw_range` is all that decides:
`rw_bytes_max` is the last count it admits, and there the arm
reaches the copy, whose first byte is unwritable — Linux's -EFAULT, from
`vfs_read`'s access_ok (fs/read_write.c:560-561, v6.18.46) before the pipe
is read.  `read_window.c`'s `pipe-edge` mode is this call, but the file
carries no `CASE:` line for it, so the evidence is the source.
kernel: fs/read_write.c:vfs_read; fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_edge_count_at_bound_is_efault (o : outcome SyscallEffect) :
    syscall_spec (read_in 14 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 rw_bytes_max) wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …and the queue is not drained by it.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_edge_count_at_bound_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 14 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 rw_bytes_max) wmem_none) read_model
        (Ok (mkEffect 2 [(Z_to_bv 64 (2 ^ 63), [97, 98])] []) m' evs) := by
  rw_refute

/-- One more byte and the gate declines: the count is over `rw_bytes_max`
and the range is out, so neither disjunct holds — where Linux still answers
-EFAULT, the whole of what the gate costs
(bugs/write-out-of-range-short-write.md).
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pipe_edge_count_over_bound_declines (o : outcome SyscallEffect) :
    syscall_spec (read_in 14 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (rw_bytes_max + 1)) wmem_none) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …with Linux's -EFAULT refused there, as at 2^40.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pipe_edge_count_over_bound_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (read_in 14 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (rw_bytes_max + 1)) wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-! ## write (64): the fixtures and the call

The write pins follow the path `write_spec`'s docstring walks: `ksys_write`
(fs/read_write.c:727-744, Linux v6.18.46) resolves the fd with `fdget_pos`
(:729) and answers -EBADF (:730, the `fd_empty` test at :732) on an empty one; `vfs_write`
(:666-696) tests `FMODE_WRITE` (:670-671) and `FMODE_CAN_WRITE` (:672-673)
before `access_ok` (:674-675), `rw_verify_area` (:677-679) and the
`MAX_RW_COUNT` clamp (:680-681); then the file's `write_iter`.  The
fixture is `write_model`, one process with every fd kind `write_spec` has
an arm for, over a file system holding "hi" at path `f` = 102 and "j" at
`g` = 103.  Its first 26 rows are the read half's table (PR #1122), row for row, so
that a pin numbered the same way in either half names the same
descriptor; the rows from fd 27 on are the write-side shapes that table
has no room for:

| fd | kind | why it is here |
|---|---|---|
| 0, 1, 2 | the three channels | stdin, and the two write-only ones |
| 3 | `FdFile f 0` | a regular file at its start |
| 4 | `FdFileW g 0` | a file open write-only |
| 5 | `FdDir` | a directory |
| 6 | `FdFile f 2` | the same file at end of file |
| 7 | `FdFile [104] 0` | a path the file system does not hold |
| 8 | `FdDevNull true false` | /dev/null open read-only |
| 9 | `FdDevNull false true` | /dev/null open write-only |
| 10, 11, 12 | fresh, bound, listening sockets | never connected |
| 13 | `SkReset` | a socket whose peer's error was already reported |
| 14, 15 | pipe 0's read and write ends | pipe 0 holds "ab" |
| 16, 17 | pipe 1's read and write ends | pipe 1 is empty, its writer alive |
| 18 | pipe 2's read end | pipe 2 is empty and has no writer |
| 19 | `FdPipe 3 false` | a pipe id the table does not hold |
| 20, 21, 22 | connected sockets at `NFin`, `NRst`, `NTimedOut` | the three terminals |
| 23 | `FdFile f 1` | the file one byte in |
| 24 | `FdUrandom` | the random device |
| 26 | `FdChannel 0` | a second descriptor onto channel 0, as `dup(0)` mints |
| 27 | `FdFileW [104] 0` | a write-only fd on a path the file system does not hold |
| 28 | `FdPipe 4 true` | the write end of pipe 4, whose read end is closed |
| 31 | `FdFileW f 1` | the file "hi" one byte in, write-only |
| 32 | `FdPipe 3 true` | the write end of a pipe id the table does not hold |
| 33 | `FdFileW f 131075` | a write-only fd whose offset opens a hole one byte over `rw_bytes_max` |
| 34, 35 | pipe 5's read and write ends | pipe 5 holds one byte with its mark at 4095 |

fd 30 is deliberately absent: it is the closed fd the -EBADF pins name.
Pipe 4 is empty; pipe 5 is a page written to 4095 and drained to its last
byte, the shape whose next byte fills the page and whose next two do not.
The Rocq examples on `wpast_model` (the file "hi" at offset 4) stay on the
`Checks/Cases/Prelude.lean` fixture of that name; `wend_model` below is
the same file through fd 3 at offset 2, exactly its end, and through
fd 4 at offset 3, one byte past it. -/

/-! ### The write half proper -/

attribute [sys_simp low] write_spec.eq_1 write_range_gate.eq_1 write_ledger.eq_1
  write_file_tail.eq_1 modeled_file_gap.eq_1 modeled_file_gap.eq_2 modeled_zero_fill.eq_1
  unreadable_source_past_eof.eq_1 unreadable_source_past_eof.eq_2

/- `access_ok_zero` is `Sys/Uaccess.lean`'s, shared by every arm that
answers a zero count from `access_ok` alone; its unfolding is registered
here, `local` so that it reaches this file's pins and nothing else,
because this port edits only its own files, and it moves to that file's
Cases twin the day one registers it.  (The read half registers it too;
when the two halves are one file, one of the two lines goes.)
`record_copyins.eq_1`, the ledger wrapper's, is already in the global
`sys_simp` set — `Checks/Cases/Tactic.lean` registers it beside
`outcome_copyins` — so this file does not register it again. -/
attribute [local sys_simp low] access_ok_zero.eq_1

/-- One event per delivered byte on the channel the arm names, unfolded
over a cons.
model: `List.map (WriteEv ch)` over `::` and `[]`, rewrites for `sys_norm` -/
theorem map_WriteEv_cons (ch : word) (b : byte) (l : List byte) :
    List.map (WriteEv ch) (b :: l) = WriteEv ch b :: List.map (WriteEv ch) l := rfl

/-- …and over the empty list.
model: `List.map (WriteEv ch)` over `[]`, a rewrite for `sys_norm` -/
theorem map_WriteEv_nil (ch : word) : List.map (WriteEv ch) ([] : List byte) = [] := rfl

attribute [sys_simp] map_WriteEv_cons map_WriteEv_nil

/-- `pipe_append` read off a literal queue, one lemma per shape of its
`match`, so a pin over a pipe table normalizes to the queue it names.
model: `pipe_append` on the empty queue -/
theorem pipe_append_nil (used : Int) (bs : List byte) :
    pipe_append ([], used) bs = (bs, (bs.length : Int)) := rfl

/-- …and on a nonempty one: appended, the mark carried up.
model: `pipe_append` on a nonempty queue -/
theorem pipe_append_cons (b : byte) (q : List byte) (used : Int) (bs : List byte) :
    pipe_append (b :: q, used) bs = ((b :: q) ++ bs, used + (bs.length : Int)) := rfl

attribute [local sys_simp low] pipe_append_nil pipe_append_cons

/- `List.take` on a literal count and a literal list: the refutations
below leave `List.map (WriteEv c) (List.take n bs)` in an event
hypothesis, and the ground pass does not unfold `List.take` (it is
compiled by structural recursion, not a closed constant), so the two
step lemmas are handed to the normalizer here.  The offset pattern
`i + 1` matches a numeral in simp's index, which is what lets
`List.take 2 [97, 98]` step. -/
attribute [local sys_simp low] List.take_succ_cons List.take_zero List.take_nil

/-- A prefix of `bs` is no longer than `bs`: what bounds the `choose`
witness of a channel write when a forged outcome names a longer one.
model: a list fact the channel refutations close with -/
theorem prefix_length_le {ds bs : List byte} (h : ds = List.take ds.length bs) :
    ds.length ≤ bs.length := by
  have := congrArg List.length h
  rw [List.length_take] at this
  omega

/-- The witness of a channel write is determined by its length.
model: a list fact the channel refutations close with -/
theorem prefix_of_length {ds bs : List byte} {n : Nat} (hn : ds.length = n)
    (h : ds = List.take ds.length bs) : ds = List.take n bs := by
  rw [hn] at h
  exact h

/-- `write(fd, buf, count)` as the dispatcher sees it: syscall 64, the three
arguments in a0..a2, `mem` the readable view, nothing writable. -/
def write_in (fd buf count : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 64 [fd, buf, count, 0, 0, 0] mem (fun _ => none)

/-- Exactly `[4096, 4096 + n)` is readable, and reads as zeros. -/
def mem_first (n : Int) : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (Z_to_bv 64 (4096 + n)) then some 0 else none

/-- Nothing is readable. -/
def mem_none : word → Option byte := fun _ => none

/-- Everything below `TASK_SIZE` is readable and nothing above it: the view
a process really has, for the pins at the top of the address space. -/
def mem_below_top : word → Option byte :=
  fun a => if bv_ltu a (Z_to_bv 64 TASK_SIZE) then some 0 else none

/-- One byte, "z", readable at `b` and nothing else. -/
def mem_z_at (b : word) : word → Option byte := fun a => if bv_eqb a b then some 122 else none

/-- "a" at 4096 and nothing else readable: the first of two bytes. -/
def mem_a : word → Option byte := fun a => if bv_eqb a 4096 then some 97 else none

/-- "cd" at 4096, and nothing else readable. -/
def mem_cd : word → Option byte :=
  fun a => if bv_eqb a 4096 then some 99 else if bv_eqb a 4097 then some 100 else none

/-- "ab" at 4096, a hole at 4098, "c" at 4099: the buffer whose readable
prefix stops short of a readable byte. -/
def mem_hole : word → Option byte :=
  fun a => if bv_eqb a 4096 then some 97 else if bv_eqb a 4097 then some 98
           else if bv_eqb a 4099 then some 99 else none

/-- Four bytes below the address-space top: a range of 4 ends at the limit
and passes `access_ok`, a range of 8 does not. -/
def near_top : word := Z_to_bv 64 (TASK_SIZE - 4)

/-- The address-space top itself: a zero-byte range there passes
`access_ok`.  The limit `__access_ok` compares against is `TASK_SIZE_MAX`,
which its own header defines as `TASK_SIZE` where the architecture defines
none (include/asm-generic/access_ok.h:15-16, v6.18.46), as riscv does not;
the pins name this fixture so that the value they claim is the one that
header spells. -/
def at_top : word := Z_to_bv 64 TASK_SIZE

/-- One past the top: the first address a zero-byte range fails
`access_ok` at (include/asm-generic/access_ok.h:31-40, v6.18.46). -/
def past_top : word := Z_to_bv 64 (TASK_SIZE + 1)

/-- The connection's peer; nothing below reads it beyond carrying it. -/
def peer_w : PeerAddr := PeerAddr.mkPeer (Z_to_bv 32 0x0100007f) (Z_to_bv 16 0x5000)

def write_fds : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
    (3, .FdFile [102] 0), (4, .FdFileW [103] 0), (5, .FdDir),
    (6, .FdFile [102] 2), (7, .FdFile [104] 0),
    (8, .FdDevNull true false), (9, .FdDevNull false true),
    (10, .FdSocket .SkFresh), (11, .FdSocket .SkBound), (12, .FdSocket .SkListening),
    (13, .FdSocket (.SkReset peer_w 7)),
    (14, .FdPipe 0 false), (15, .FdPipe 0 true), (16, .FdPipe 1 false), (17, .FdPipe 1 true),
    (18, .FdPipe 2 false), (19, .FdPipe 3 false),
    (20, .FdSocket (.SkConnected peer_w 7 NFin)), (21, .FdSocket (.SkConnected peer_w 7 NRst)),
    (22, .FdSocket (.SkConnected peer_w 7 NTimedOut)),
    (23, .FdFile [102] 1), (24, .FdUrandom), (26, .FdChannel 0),
    (27, .FdFileW [104] 0), (28, .FdPipe 4 true), (31, .FdFileW [102] 1),
    (32, .FdPipe 3 true), (33, .FdFileW [102] (Z_to_bv 64 131075)),
    (34, .FdPipe 5 false), (35, .FdPipe 5 true) ]

/-- Pipe 0 holds "ab" with its page mark at 2; pipe 1 is empty with the
mark at 0; pipe 2 is empty with a mark left by a drained page; pipe 4 is
empty; pipe 5 holds one byte with its mark at 4095. -/
def write_pipes : List (word × PipeBuf) :=
  [(0, ([97, 98], 2)), (1, ([], 0)), (2, ([], 3)), (4, ([], 0)), (5, ([120], 4095))]

/-- "hi" at path `f` = 102 and "j" at `g` = 103. -/
def write_fs : Fs.Fs := [([102], [104, 105]), ([103], [106])]

def write_model : Model := fixture_of (fds := write_fds) (pipes := write_pipes) (fs := write_fs)

/-- model: a fixture projection, a rewrite for `sys_norm`, as `read_model`'s above. -/
theorem write_model_fd_table : write_model.m_fd.fdst_table = write_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem write_model_fd_pipes : write_model.m_fd.fdst_pipes = write_pipes := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem write_model_fs : write_model.m_fsys.fsst_image = write_fs := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem write_model_stdin : write_model.m_io.iost_stdin = IEof := rfl

attribute [local sys_simp] write_model_fd_table write_model_fd_pipes write_model_fs write_model_stdin
attribute [local sys_simp low] write_fds.eq_1 write_pipes.eq_1 write_fs.eq_1

/-- The file "hi" held for writing through fd 3 at offset 2, EXACTLY its
end, and through fd 4 at offset 3, ONE byte past it, and nothing else in
the table: the two edges `unreadable_source_past_eof`'s `<` is judged on.
`Checks/Cases/Prelude.lean`'s `wpast_model` is the same file at offset 4,
two bytes past the end. -/
def wend_model : Model :=
  fixture_of (fds := [(3, .FdFileW [102] 2), (4, .FdFileW [102] 3)])
    (fs := [([102], [104, 105])])

attribute [sys_simp low] write_in.eq_1

/-! ## `ksys_write`: the descriptor is resolved first

`ksys_write` (fs/read_write.c:727-744, Linux v6.18.46) answers -EBADF
(:730, the `fd_empty` test at :732) on an empty fd before `vfs_write` (:738) is reached, and
`vfs_write` (:666-696) tests `FMODE_WRITE` (:670-671) before `access_ok`
(:674-675).  So a closed fd, and an fd open without `FMODE_WRITE`, is
-EBADF whatever `buf` and `count` say — even a range `access_ok` would
refuse. -/

/-- A closed fd is -EBADF and nothing else.
probe: testing/syscall-check/tests/write_spec.c#conform --mutate write:mem-none -- w-badfd
The kernel side is `ksys_write` (fs/read_write.c, v6.18.46). -/
theorem write_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (write_in 30 4096 2 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- -EBADF beats the range: a closed fd with a source range the gate
would decline on any open kind — a 1 MiB count from 2^63, over
`rw_bytes_max` and outside user space, so `modeled_rw_range` is false —
is still -EBADF, the fd being resolved before `access_ok` is consulted.
(A count within `rw_bytes_max` passes the gate whatever the address, and
would not show the order.)
kernel: fs/read_write.c:ksys_write@v6.18.46 -/
theorem write_closed_fd_beats_the_range (o : outcome SyscallEffect) :
    syscall_spec (write_in 30 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 20)) mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- …so -EFAULT is refused there…
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:mem-none,ret=-EFAULT -- w-badfd -/
theorem write_closed_fd_is_not_efault (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 30 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- …and so is the range decline.
kernel: fs/read_write.c:ksys_write@v6.18.46 -/
theorem write_closed_fd_is_not_a_range_decline :
    ¬ syscall_spec (write_in 30 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
        Unmodeled := by
  rw_refute

/-- A file open read-only has no `FMODE_WRITE`: -EBADF.
probe: testing/syscall-check/tests/fd_modes.c#conform
The kernel side is `vfs_write` (fs/read_write.c, v6.18.46). -/
theorem write_read_only_file_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (write_in 3 4096 2 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- …and no byte goes through it.
probe: testing/syscall-check/tests/fd_modes.c#reject --mutate write#2:ret=1 -/
theorem write_read_only_file_delivers_nothing (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 3 4096 2 mem_ab) write_model (Ok (mkEffect 1 [] []) m' evs) := by
  rw_refute

/-- A directory fd is -EBADF: `may_open` (fs/namei.c:3540-3542, v6.18.46)
refuses to open a directory for writing with -EISDIR, so the fd a program
holds on one has no `FMODE_WRITE`, and `vfs_write` answers -EBADF.
probe: testing/syscall-check/tests/write_short.c#conform -- w-dir
The kernel side is `may_open` (fs/namei.c, v6.18.46). -/
theorem write_directory_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (write_in 5 4096 2 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- -EISDIR is `open`'s answer, never `write`'s.
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem write_directory_is_not_eisdir (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 5 4096 2 mem_ab) write_model
        (Ok (mkEffect (errno_ret EISDIR) [] []) m' evs) := by
  rw_refute

/-- …and a directory takes no byte.
probe: testing/syscall-check/tests/write_short.c#reject --mutate write:ret=1 -- w-dir -/
theorem write_directory_delivers_nothing (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 5 4096 2 mem_ab) write_model (Ok (mkEffect 1 [] []) m' evs) := by
  rw_refute

/-- The random device the model mints is open read-only: -EBADF.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_urandom_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (write_in 24 4096 2 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- /dev/null open read-only: -EBADF before `write_null` is reached.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_devnull_read_only_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (write_in 8 4096 2 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- Standard input is the read end of the harness's pipe: -EBADF.
probe: testing/syscall-check/tests/fd_modes.c#conform -- chandir
The kernel side is `vfs_write` (fs/read_write.c, v6.18.46). -/
theorem write_stdin_channel_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (write_in 0 4096 2 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- -EBADF beats the range on standard input too: `vfs_write`'s FMODE_WRITE
test (fs/read_write.c:670-671, v6.18.46) runs before its `access_ok`
(:674-675), so a source past the limit changes nothing.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_stdin_channel_beats_the_range (o : outcome SyscallEffect) :
    syscall_spec (write_in 0 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- …so the range decline is refused there.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_stdin_channel_past_the_limit_is_not_a_decline :
    ¬ syscall_spec (write_in 0 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
        Unmodeled := by
  rw_refute

/-- …and takes no byte.
probe: testing/syscall-check/tests/fd_modes.c#reject --mutate write:ret=1 -- chandir -/
theorem write_stdin_channel_delivers_nothing (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 0 4096 2 mem_ab) write_model (Ok (mkEffect 1 [] []) m' evs) := by
  rw_refute

/-- A `dup` of standard input is the same read end: -EBADF.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_dup_of_stdin_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (write_in 26 4096 2 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- A pipe's read end is opened `O_RDONLY` by `create_pipe_files`
(fs/pipe.c:956, v6.18.46): -EBADF.
kernel: fs/read_write.c:vfs_write;fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem write_pipe_read_end_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (write_in 14 4096 2 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- …not -EPIPE: the reader test is `anon_pipe_write`'s, which the read
end never reaches.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_pipe_read_end_is_not_epipe (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 14 4096 2 mem_ab) write_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  rw_refute

/-- -EBADF beats the range on a pipe's read end too: FMODE_WRITE
(fs/read_write.c:670-671, v6.18.46) before `access_ok` (:674-675).
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pipe_write_read_end_beats_the_range (o : outcome SyscallEffect) :
    syscall_spec (write_in 14 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- …so the range decline is refused there.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pipe_write_read_end_past_the_limit_is_not_a_decline :
    ¬ syscall_spec (write_in 14 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
        Unmodeled := by
  rw_refute

/-! ## The fd argument is 32 bits wide

`SYSCALL_DEFINE3(write, unsigned int, fd, …)` (fs/read_write.c:746-750,
v6.18.46): the register's upper half is gone before `ksys_write` sees the
fd, so 2^32 + 1 IS fd 1, and 2^31 + 1 is the (closed) fd 2147483649. -/

/-- Rocq's `write_fd_truncates_to_32_bits`: fd 2^32 + 1 is stdout.
rocq-twin: write_fd_truncates_to_32_bits
probe: testing/syscall-check/tests/fd_truncation.c#conform --stdin hi
The kernel side is `ksys_write` (fs/read_write.c, v6.18.46). -/
theorem write_fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (write_in (Z_to_bv 64 (2 ^ 32 + 1)) 4096 2 mem_ab) write_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) write_model
               (List.map (WriteEv 1) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 2
        ∧ ds = List.take ds.length [97, 98] := by
  rw_norm

/-- A kernel refusing fd 2^32 + 1 compared the whole register.
rocq-twin: write_fd_high_bits_ebadf_rejected
probe: testing/syscall-check/tests/fd_truncation.c#reject --stdin hi --mutate write#1:ret=-EBADF -/
theorem write_fd_high_bits_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in (Z_to_bv 64 (2 ^ 32 + 1)) 4096 2 mem_ab) write_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- Bit 31 is part of the fd: 2^31 + 1 is not fd 1 but a closed fd.  This
is the `write` conjunct of Rocq's four-conjunct
`bit31_is_part_of_the_32_bit_arguments`; the `lseek` conjunct is
`lseek_bit31_whence_is_einval` below, and the two `ioctl` conjuncts — bit
31 of the fd, -EBADF; bit 31 of the request, `Unmodeled` — are
`ioctl_bit31_fd_is_closed` and `ioctl_bit31_request_declines`, next.
rocq-twin: bit31_is_part_of_the_32_bit_arguments
kernel: fs/read_write.c:ksys_write@v6.18.46 -/
theorem write_bit31_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (write_in (Z_to_bv 64 (2 ^ 31 + 1)) 4096 2 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- …so it delivers nothing to stdout.
kernel: fs/read_write.c:ksys_write@v6.18.46 -/
theorem write_bit31_fd_delivers_nothing (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in (Z_to_bv 64 (2 ^ 31 + 1)) 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-! ### The `ioctl` conjuncts of the bit-31 argument

Two of the four conjuncts of Rocq's `bit31_is_part_of_the_32_bit_arguments`
are `ioctl` (29) calls on `init_model [] …`, which is `demo_model` here:
fds 0, 1 and 2 are the three channels and nothing else is open.  They go
through the dispatcher, as every pin of one call here does, so the registry's
`fd32` and `cmd32` narrowings are under test — `SYSCALL_DEFINE3(ioctl,
unsigned int, fd, unsigned int, cmd, unsigned long, arg)` (fs/ioctl.c:583,
v6.18.46) takes both as `unsigned int` — and bit 31 of each is shown to
survive.  `ioctl_spec`'s equation is registered for this section alone. -/
section ioctl_bit31

attribute [local sys_simp low] LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Ioctl.ioctl_spec.eq_1

/-- The fd conjunct: a0 = 2^31 + 1 is fd 2147483649, which no table here
holds, so `fd_empty` answers -EBADF (fs/ioctl.c:585-589, v6.18.46).  The
model matters: fd 1 is an OPEN channel in `demo_model`, so a narrowing
that dropped bit 31 would reach it and answer the channel's -ENOTTY
instead.  The request is the Rocq case's, TIOCGWINSZ, a terminal's
window-size query (`tty_ioctl`, drivers/tty/tty_io.c, v6.18.46); the fd is
looked up before any request is read.
rocq-twin: bit31_is_part_of_the_32_bit_arguments
kernel: fs/ioctl.c:ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem ioctl_bit31_fd_is_closed (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [Z_to_bv 64 (2 ^ 31 + 1), Sys.Uapi.TIOCGWINSZ, 4096, 0, 0, 0]
        (fun _ => none) (fun _ => none)) demo_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) demo_model [] := by
  rw_norm

/-- …so -ENOTTY, fd 1's answer to TIOCGWINSZ, is refused there: no kernel
looks fd 2147483649 up as fd 1.
kernel: fs/ioctl.c:ioctl@v6.18.46 -/
theorem ioctl_bit31_fd_enotty_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 29 [Z_to_bv 64 (2 ^ 31 + 1), Sys.Uapi.TIOCGWINSZ, 4096, 0, 0, 0]
        (fun _ => none) (fun _ => none)) demo_model
        (Ok (mkEffect (errno_ret ENOTTY) [] []) m' evs) := by
  rw_refute

/-- The request conjunct: a1 = 2^31 + TIOCGWINSZ keeps bit 31 through
`cmd32`, so the arm sees 0x80005413, which is none of the eight requests
`tty_only_request` answers, and declines.  A narrowing that dropped bit
31 would have left TIOCGWINSZ, which the channel arm answers -ENOTTY, so
the decline is what shows the width.  It is a decline and not a refusal
of that errno: 0x80005413 is in no case of `do_vfs_ioctl`, and the
handlers `Sys/Fs/Ioctl.lean`'s header walks answer an unknown request
-ENOTTY exactly as they answer TIOCGWINSZ (`pipe_ioctl`'s default arm,
fs/pipe.c:653-654, v6.18.46, returns -ENOIOCTLCMD, which `vfs_ioctl`
maps to -ENOTTY, fs/ioctl.c:52-53).  So the intersection here is not
empty.
rocq-twin: bit31_is_part_of_the_32_bit_arguments
kernel: fs/ioctl.c:ioctl,vfs_ioctl@v6.18.46 -/
theorem ioctl_bit31_request_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [1, Z_to_bv 64 (2 ^ 31 + 21523), 4096, 0, 0, 0]
        (fun _ => none) (fun _ => none)) demo_model o ↔ o = Unmodeled := by
  rw_norm

end ioctl_bit31

/-! ## A channel: any nonempty prefix of the readable source

Standard output and error are the write ends of the harness's pipes, so
their answer is `anon_pipe_write`'s (fs/pipe.c:431-601, v6.18.46): the
bytes copied before the pipe filled, a count between 1 and the request,
one `WriteEv` per byte.  What the arm delivers is a prefix of the READABLE
source: a copy stopping at an unreadable byte is -EFAULT at the merge
site whatever it copied (:489-491) and, on a fresh page, the bytes
counted on earlier pages or -EFAULT when there were none (:523-527) — the
channel arm keeps the short-write answer at every hole, which
`bugs/write-channel-partial-source-efault-refused.md` records. -/

/-- Rocq's `write_channel_outcome`: stdout takes a nonempty prefix.  The
Rocq lemma is universal — every fd, count, memory and model — and a proof
over the relation, not a pin; this is its fd-1, "ab", count-2 instance,
and `stderr_write_delivers_a_prefix_iff` below its fd-2 one.  The
universal is not restated here: the Lean checker has no completeness
lemma to walk, which is the same reason the header registers
`read_delivery_clamped` unpinned.
rocq-twin: write_channel_outcome
probe: testing/syscall-check/tests/write_spec.c#conform -- w-full
The kernel side is `anon_pipe_write` (fs/pipe.c, v6.18.46). -/
theorem channel_write_delivers_a_prefix_iff (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 4096 2 mem_ab) write_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) write_model
               (List.map (WriteEv 1) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 2
        ∧ ds = List.take ds.length [97, 98] := by
  rw_norm

/-- Rocq's `write_ab_events`: the full delivery, one event per byte.
rocq-twin: write_ab_events
probe: testing/syscall-check/tests/write_spec.c#conform -- w-full -/
theorem write_ab_events :
    syscall_spec (write_in 1 4096 2 mem_ab) write_model
      (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) write_model
          [WriteEv 1 97, WriteEv 1 98]) := by
  rw [channel_write_delivers_a_prefix_iff]
  exact ⟨[97, 98], by rw_norm, by decide, by decide, rfl⟩

/-- Rocq's `write_ab_short_delivery`: one byte, and the ledger records
only the byte delivered.
rocq-twin: write_ab_short_delivery
probe: testing/syscall-check/tests/write_spec.c#conform --mutate write:ret=1,drop-copyins,smuggle-copyin:a1:1 -- w-full -/
theorem write_ab_short_delivery :
    syscall_spec (write_in 1 4096 2 mem_ab) write_model
      (Ok (with_copyins [(4096, 1)] (mkEffect 1 [] [])) write_model [WriteEv 1 97]) := by
  rw [channel_write_delivers_a_prefix_iff]
  exact ⟨[97], by rw_norm, by decide, by decide, rfl⟩

/-- Rocq's `write_a_then_b_events`, first half: one byte at 4096 is "a".
rocq-twin: write_a_then_b_events
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_a_delivers_iff (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 4096 1 mem_ab) write_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) write_model
               (List.map (WriteEv 1) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 1
        ∧ ds = List.take ds.length [97] := by
  rw_norm

/-- …second half: one byte at 4097 is "b", and the ledger names 4097.
rocq-twin: write_a_then_b_events
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_b_delivers_iff (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 4097 1 mem_ab) write_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4097, ds.length)] (mkEffect (len_word ds) [] [])) write_model
               (List.map (WriteEv 1) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 1
        ∧ ds = List.take ds.length [98] := by
  rw_norm

/-- The two one-byte writes, as the Rocq example states them.
rocq-twin: write_a_then_b_events
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_a_then_b_events :
    syscall_spec (write_in 1 4096 1 mem_ab) write_model
      (Ok (with_copyins [(4096, 1)] (mkEffect 1 [] [])) write_model [WriteEv 1 97])
    ∧ syscall_spec (write_in 1 4097 1 mem_ab) write_model
      (Ok (with_copyins [(4097, 1)] (mkEffect 1 [] [])) write_model [WriteEv 1 98]) := by
  constructor
  · rw [write_a_delivers_iff]
    exact ⟨[97], by rw_norm, by decide, by decide, rfl⟩
  · rw [write_b_delivers_iff]
    exact ⟨[98], by rw_norm, by decide, by decide, rfl⟩

/-- The second byte is "b", not "a" again: the source is read at `buf`.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_b_is_not_a (m' : Model) :
    ¬ syscall_spec (write_in 1 4097 1 mem_ab) write_model
        (Ok (with_copyins [(4097, 1)] (mkEffect 1 [] [])) m' [WriteEv 1 97]) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- Over-delivery: three bytes of a two-byte request.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:ret=3 -- w-full -/
theorem write_over_count_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 3)] (mkEffect 3 [] [])) m' evs) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- A zero delivery of a nonzero request: a pipe with no room blocks, it
does not answer 0 (`anon_pipe_write` sleeps at fs/pipe.c:573, v6.18.46).
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:ret=0 -- w-full -/
theorem write_zero_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …nor 0 with an empty ledger entry.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:ret=0 -- w-full -/
theorem write_zero_delivery_with_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 0)] (mkEffect 0 [] [])) m' evs) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- Rocq's `write_channel_eintr_rejected`: `anon_pipe_write` answers
-ERESTARTSYS only when a signal is pending and nothing was written
(fs/pipe.c:557-559, v6.18.46).
rocq-twin: write_channel_eintr_rejected
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_channel_eintr_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (mkEffect (errno_ret EINTR) [] []) m' evs) := by
  rw_refute

/-- Rocq's `write_channel_epipe_rejected`: -EPIPE is the answer to a pipe
with no readers (fs/pipe.c:460-465, v6.18.46), and the channel arm
assumes its reader alive (`bugs/write-channel-assumes-its-reader-is-alive.md`).
rocq-twin: write_channel_epipe_rejected
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_channel_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  rw_refute

/-- -EFAULT on a fully readable source.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:ret=-EFAULT -- w-full -/
theorem write_efault_on_a_readable_source_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- -EBADF on an open write end.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:ret=-EBADF -- w-full -/
theorem write_channel_is_not_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- A full delivery records the source it read.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:drop-copyins -- w-full -/
theorem write_dropped_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model (Ok (mkEffect 2 [] []) m' evs) := by
  rw_refute

/-- A one-byte delivery cannot claim the two-byte range.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:ret=1,drop-copyins,smuggle-copyin:a1:2 -- w-full -/
theorem write_short_delivery_claims_only_its_prefix (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 1 [] [])) m' evs) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- A write moves no byte into user memory.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:ret=1,smuggle-write:a1:1 -- w-full -/
theorem write_smuggled_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 1)] (mkEffect 1 [(4096, [97])] [])) m' evs) := by
  rw_refute

/-- The bytes go to the pipe fd 1 names, not to stderr's.
kernel: fs/read_write.c:ksys_write@v6.18.46 -/
theorem write_wrong_channel_rejected (m' : Model) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' [WriteEv 2 97, WriteEv 2 98]) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- …and they are the source's bytes.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_wrong_bytes_rejected (m' : Model) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' [WriteEv 1 97, WriteEv 1 99]) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- Standard error is channel 2, and the events name IT: the arm emits
`WriteEv ch` for the descriptor's own channel, so the same two bytes on
fd 2 are the same prefix delivery with every event on channel 2.  Without
this pin a model that reported every write on channel 1 would pass the
stdout pins above unchanged.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem stderr_write_delivers_a_prefix_iff (o : outcome SyscallEffect) :
    syscall_spec (write_in 2 4096 2 mem_ab) write_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) write_model
               (List.map (WriteEv 2) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 2
        ∧ ds = List.take ds.length [97, 98] := by
  rw_norm

/-- …and the two bytes reported on channel 1 are not a delivery on fd 2.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem stderr_write_on_channel_one_rejected (m' : Model) :
    ¬ syscall_spec (write_in 2 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' [WriteEv 1 97, WriteEv 1 98]) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- A channel write changes no descriptor: the fd table is left alone.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_channel_leaves_the_table_alone (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) (with_fds [] write_model) evs) := by
  intro h
  sys_refute at h

/-! ### A zero count

`anon_pipe_write` returns 0 on a null write before anything else
(fs/pipe.c:454-456, v6.18.46), and `access_ok`
(include/asm-generic/access_ok.h, v6.18.46) in `vfs_write`
(fs/read_write.c:674-675, v6.18.46) is the only test the source meets: a range of
zero bytes at an address up to `TASK_SIZE` passes, one past it does not
(`__access_ok`, include/asm-generic/access_ok.h:31-40). -/

/-- Zero bytes: 0, and the source is never read.
probe: testing/syscall-check/tests/write_spec.c#conform --mutate write:mem-none -- w-zero
The kernel side is `anon_pipe_write` (fs/pipe.c, v6.18.46). -/
theorem write_zero_count_is_zero (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 4096 0 mem_none) write_model o ↔
      o = Ok (mkEffect 0 [] []) write_model [] := by
  rw_norm

/-- …not -EFAULT for an unreadable source.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:mem-none,ret=-EFAULT -- w-zero -/
theorem write_zero_count_is_not_efault (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 0 mem_none) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- …and no byte is delivered (`anon_pipe_write`, fs/pipe.c, v6.18.46).
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:ret=1 -- w-zero -/
theorem write_zero_count_delivers_nothing (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 0 mem_none) write_model (Ok (mkEffect 1 [] []) m' evs) := by
  rw_refute

/-- A zero-byte range AT the limit passes `access_ok`: 0.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- write0-top
The kernel side is `__access_ok` (include/asm-generic/access_ok.h, v6.18.46). -/
theorem write_zero_count_at_the_limit_is_zero (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 (Z_to_bv 64 TASK_SIZE) 0 mem_none) write_model o ↔
      o = Ok (mkEffect 0 [] []) write_model [] := by
  rw_norm

/-- …and is not -EFAULT.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate write:ret=-EFAULT -- write0-top -/
theorem write_zero_count_at_the_limit_is_not_efault (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 (Z_to_bv 64 TASK_SIZE) 0 mem_none) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- One past the limit, a zero-byte range fails `access_ok`: -EFAULT.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- write0-past
The kernel side is `__access_ok` (include/asm-generic/access_ok.h, v6.18.46). -/
theorem write_zero_count_past_the_limit_is_efault (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 (Z_to_bv 64 (TASK_SIZE + 1)) 0 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- …never 0.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate write:ret=0 -- write0-past -/
theorem write_zero_count_past_the_limit_is_not_zero (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 (Z_to_bv 64 (TASK_SIZE + 1)) 0 mem_none) write_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-! ### The source

Nothing readable at `buf` is -EFAULT: the copy into the pipe faults before
a byte is counted (fs/pipe.c:489-492 on a merge, :523-528 on a fresh page,
v6.18.46).  A readable prefix is delivered short — the channel arm's
stance at every hole, see the section header. -/

/-- An unreadable source is -EFAULT, with no ledger.
probe: testing/syscall-check/tests/write_spec.c#conform --mutate write:mem-none,ret=-EFAULT,drop-copyins -- w-full
The kernel side is `anon_pipe_write` (fs/pipe.c, v6.18.46). -/
theorem write_unreadable_source_is_efault (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 4096 2 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- A full write from unreadable memory.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:mem-none -- w-full -/
theorem write_unreadable_source_rejects_delivery (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_none) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- 0 from unreadable memory.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:mem-none,ret=0 -- w-full -/
theorem write_unreadable_source_is_not_zero (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_none) write_model (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- The wrong errno from unreadable memory: -EIO, which is 5 and which the
errno register does not spell.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:mem-none,ret=-EIO -- w-full -/
theorem write_unreadable_source_is_not_eio (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_none) write_model
        (Ok (mkEffect (errno_ret 5) [] []) m' evs) := by
  rw_refute

/-- -EFAULT moves no byte into user memory.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:mem-none,ret=-EFAULT,smuggle-write:a1:1 -- w-full -/
theorem write_unreadable_source_efault_carries_no_write (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_none) write_model
        (Ok (mkEffect (errno_ret EFAULT) [(4096, [0])] []) m' evs) := by
  rw_refute

/-- The first of two bytes readable: the delivery is a prefix of that one
byte, and the ledger records what was delivered.
probe: testing/syscall-check/tests/write_spec.c#conform --mutate write:mem-hide:a1+1:1,ret=1,drop-copyins,smuggle-copyin:a1:1 -- w-full
The kernel side is `anon_pipe_write` (fs/pipe.c, v6.18.46). -/
theorem write_partial_source_delivers_the_prefix_iff (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 4096 2 mem_a) write_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) write_model
               (List.map (WriteEv 1) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 2
        ∧ ds = List.take ds.length [97] := by
  rw_norm

/-- …so the one byte is delivered.
probe: testing/syscall-check/tests/write_spec.c#conform --mutate write:mem-hide:a1+1:1,ret=1,drop-copyins,smuggle-copyin:a1:1 -- w-full -/
theorem write_partial_source_delivers_one_byte :
    syscall_spec (write_in 1 4096 2 mem_a) write_model
      (Ok (with_copyins [(4096, 1)] (mkEffect 1 [] [])) write_model [WriteEv 1 97]) := by
  rw [write_partial_source_delivers_the_prefix_iff]
  exact ⟨[97], by rw_norm, by decide, by decide, rfl⟩

/-- …and the full count is beyond the readable prefix.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:mem-hide:a1+1:1 -- w-full -/
theorem write_partial_source_rejects_the_full_count (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_a) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' evs) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- -EFAULT when the first byte IS readable: the channel arm's stance,
recorded in `bugs/write-channel-partial-source-efault-refused.md` — a
pipe whose merge faults after copying nothing answers -EFAULT, and the
arm refuses it for the short write.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:mem-hide:a1+1:1,ret=-EFAULT -- w-full -/
theorem write_partial_source_is_not_efault (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_a) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- A hole in the middle stops the prefix: "ab", a hole, "c" delivers a
prefix of "ab".
probe: testing/syscall-check/tests/write_spec.c#conform --mutate write:mem-hide:a1+2:1,ret=2,drop-copyins,smuggle-copyin:a1:2 -- w-hole
The kernel side is `anon_pipe_write` (fs/pipe.c, v6.18.46). -/
theorem write_hole_stops_the_prefix_iff (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 4096 3 mem_hole) write_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) write_model
               (List.map (WriteEv 1) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 3
        ∧ ds = List.take ds.length [97, 98] := by
  rw_norm

/-- …and the hole at 4098 is not read through: a three-byte transfer is
refused.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:mem-hide:a1+2:1,ret=3 -- w-hole -/
theorem write_hole_is_not_skipped (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 3 mem_hole) write_model
        (Ok (with_copyins [(4096, 3)] (mkEffect 3 [] [])) m' evs) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-! ### The range gate

Above `rw_bytes_max` the arm's gate is Linux's own range test: a count
that runs past `TASK_SIZE` fails `access_ok`
(include/asm-generic/access_ok.h, v6.18.46) in `vfs_write`
(fs/read_write.c:674-675, v6.18.46), and the model declines rather than answer the -EFAULT itself
(`Sys/Uaccess.lean`'s `modeled_rw_range` says why).  A count above the
bound that stays in range is judged, at the `MAX_RW_COUNT` clamp
(:680-681). -/

/-- A count past the limit declines.
probe: testing/syscall-check/tests/write_window.c#fail-closed -- hi-count
The kernel side is `vfs_write` (fs/read_write.c, v6.18.46). -/
theorem write_channel_count_past_the_limit_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 near_top (Z_to_bv 64 (2 ^ 20)) mem_below_top) write_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …and answers no -EFAULT of its own.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_channel_count_past_the_limit_is_not_efault (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 near_top (Z_to_bv 64 (2 ^ 20)) mem_below_top) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- A count of 2^20 in range is judged: the readable prefix ("two zero
bytes, then a hole") is what may be delivered.
probe: testing/syscall-check/tests/rw_bytes_bound.c#conform -- w-huge
The kernel side is `vfs_write` (fs/read_write.c, v6.18.46). -/
theorem write_channel_over_the_old_bound_is_judged (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 4096 (Z_to_bv 64 (2 ^ 20)) (mem_first 2)) write_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) write_model
               (List.map (WriteEv 1) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 2 ^ 20
        ∧ ds = List.take ds.length [0, 0] := by
  rw_norm

/-- …and a zero delivery of a request with a readable first byte is refused.
probe: testing/syscall-check/tests/rw_bytes_bound.c#reject --mutate write:ret=0 -- w-huge -/
theorem write_channel_over_the_old_bound_is_not_zero (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 (Z_to_bv 64 (2 ^ 20)) (mem_first 2)) write_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- A count over `MAX_RW_COUNT` in range is clamped, and judged at the clamp.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_channel_count_over_the_clamp_is_judged (o : outcome SyscallEffect) :
    syscall_spec (write_in 1 4096 (Z_to_bv 64 (2 ^ 40)) (mem_first 2)) write_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) write_model
               (List.map (WriteEv 1) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 0x7ffff000
        ∧ ds = List.take ds.length [0, 0] := by
  rw_norm

/-! ## /dev/null: the count, unread

`write_null` (drivers/char/mem.c:418-422, v6.18.46) returns `count`
without touching the source; `vfs_write` (fs/read_write.c:674-675, v6.18.46) has
already applied `access_ok` (include/asm-generic/access_ok.h, v6.18.46)
and the `MAX_RW_COUNT` clamp (:680-681), so
the count returned is the clamped one and a range past the limit is
-EFAULT. -/

/-- The count comes back and the source is never read.
kernel: drivers/char/mem.c:write_null@v6.18.46 -/
theorem write_devnull_swallows_the_count (o : outcome SyscallEffect) :
    syscall_spec (write_in 9 4096 5 mem_none) write_model o ↔
      o = Ok (mkEffect 5 [] []) write_model [] := by
  rw_norm

/-- …with no ledger: `write_null` reads nothing.
kernel: drivers/char/mem.c:write_null@v6.18.46 -/
theorem write_devnull_reads_no_source (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 9 4096 5 mem_none) write_model
        (Ok (with_copyins [(4096, 5)] (mkEffect 5 [] [])) m' evs) := by
  rw_refute

/-- …and no -EFAULT for an unreadable source.
kernel: drivers/char/mem.c:write_null@v6.18.46 -/
theorem write_devnull_is_not_efault (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 9 4096 5 mem_none) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- A count over `MAX_RW_COUNT` comes back clamped.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_devnull_clamps_to_max_rw_count (o : outcome SyscallEffect) :
    syscall_spec (write_in 9 4096 (Z_to_bv 64 (2 ^ 40)) mem_none) write_model o ↔
      o = Ok (mkEffect (Z_to_bv 64 0x7ffff000) [] []) write_model [] := by
  rw_norm

/-- …not as requested.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_devnull_over_the_clamp_is_not_the_count (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 9 4096 (Z_to_bv 64 (2 ^ 40)) mem_none) write_model
        (Ok (mkEffect (Z_to_bv 64 (2 ^ 40)) [] []) m' evs) := by
  rw_refute

/-- A range past the limit is -EFAULT before `write_null` is reached.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_devnull_past_the_limit_is_efault (o : outcome SyscallEffect) :
    syscall_spec (write_in 9 near_top 8 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- A zero count is 0.
kernel: drivers/char/mem.c:write_null@v6.18.46 -/
theorem write_devnull_zero_count_is_zero (o : outcome SyscallEffect) :
    syscall_spec (write_in 9 4096 0 mem_none) write_model o ↔
      o = Ok (mkEffect 0 [] []) write_model [] := by
  rw_norm

/-- A count past the limit above `rw_bytes_max` declines, as on every kind.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_devnull_count_past_the_limit_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 9 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model o ↔
      o = Unmodeled := by
  rw_norm

/-! ## A socket: declined

`sock_write_iter` (net/socket.c:1176-1199, v6.18.46) hands the bytes to
the protocol's `sendmsg`, whose answer depends on the peer's window and
the connection's state; the model declines every socket write, the zero
count included, since `sock_write_iter` has no early return for it. -/

/-- A connected socket declines.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- write
The kernel side is `sock_write_iter` (net/socket.c, v6.18.46). -/
theorem write_socket_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 20 4096 2 mem_ab) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- …even for a zero count.
kernel: net/socket.c:sock_write_iter@v6.18.46 -/
theorem write_socket_zero_count_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 20 4096 0 mem_none) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- A reset peer is not answered -EPIPE by the arm: `sk_stream_error`
(net/core/stream.c:190-197, v6.18.46) raises SIGPIPE beside it, and the
signal's disposition is outside the model.
kernel: net/core/stream.c:sk_stream_error@v6.18.46 -/
theorem write_socket_is_not_epipe (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 21 4096 2 mem_ab) write_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  rw_refute

/-- …and nothing is delivered.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- write -/
theorem write_socket_delivers_nothing (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 20 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-! ## A write-only file: the readable prefix lands at the offset

`generic_perform_write` (mm/filemap.c:4244-4335, v6.18.46) copies the
source page by page, stops at the first unreadable byte, and answers
-EFAULT only when nothing was copied (the `status = -EFAULT` at
:4321-4323 is returned only under `if (!written)`, :4331-4332): the
readable prefix, exactly.  `ksys_write` writes the position back (fs/read_write.c:739-740, v6.18.46)
and the arm advances the descriptor's offset by the bytes written. -/

/-- Rocq's `create_write_updates_fs`, the write half: "ab" into the
one-byte file "j" at offset 0 leaves "ab", and the offset at 2.
rocq-twin: create_write_updates_fs
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem file_write_lands_at_the_offset_iff (o : outcome SyscallEffect) :
    syscall_spec (write_in 4 4096 2 mem_ab) write_model o ↔
      o = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
             (with_fds (fd_insert write_fds 4 (.FdFileW [103] 2))
               (with_fs (fs_set write_fs [103] [97, 98]) write_model)) [] := by
  rw_norm

/-- Rocq's `file_write_emits_nothing`: a file write is a page-cache copy,
no channel event.  Rocq states it for every write-only descriptor, source
and count; this is the fd-4, "ab" instance refuting the two events a
channel write of the same bytes would emit.
rocq-twin: file_write_emits_nothing
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem file_write_emits_nothing (m' : Model) :
    ¬ syscall_spec (write_in 4 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' [WriteEv 1 97, WriteEv 1 98]) := by
  rw_refute

/-- Rocq's `file_write_short_rejected`: a file write of a readable source
is never short.
rocq-twin: file_write_short_rejected
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:ret=1 -- w-file -/
theorem file_write_short_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 4 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 1)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-- -EINTR: `generic_perform_write` tests only a FATAL signal
(mm/filemap.c:4267-4269, v6.18.46), and a task with one pending never
returns to its program.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem file_write_eintr_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 4 4096 2 mem_ab) write_model
        (Ok (mkEffect (errno_ret EINTR) [] []) m' evs) := by
  rw_refute

/-- The position is written back: a stale offset is refused.
kernel: fs/read_write.c:ksys_write@v6.18.46 -/
theorem file_write_stale_offset_rejected (evs : List event) :
    ¬ syscall_spec (write_in 4 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
            (with_fs (fs_set write_fs [103] [97, 98]) write_model) evs) := by
  intro h
  sys_refute at h

/-- …and the file changes: an unchanged file is refused.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem file_write_unchanged_file_rejected (evs : List event) :
    ¬ syscall_spec (write_in 4 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
            (with_fds (fd_insert write_fds 4 (.FdFileW [103] 2)) write_model) evs) := by
  intro h
  sys_refute at h

/-- An unreadable source is -EFAULT, with no ledger and the file untouched.
probe: testing/syscall-check/tests/write_spec.c#conform --no-fs-check --mutate write:mem-none,ret=-EFAULT,drop-copyins -- w-file
The kernel side is `generic_perform_write` (mm/filemap.c, v6.18.46). -/
theorem file_write_unreadable_source_is_efault (o : outcome SyscallEffect) :
    syscall_spec (write_in 4 4096 2 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- Half readable: the one byte lands, the ledger names one byte, the
offset moves by one.
probe: testing/syscall-check/tests/write_spec.c#conform --no-fs-check --mutate write:mem-hide:a1+1:1,ret=1,drop-copyins,smuggle-copyin:a1:1 -- w-file
The kernel side is `generic_perform_write` (mm/filemap.c, v6.18.46). -/
theorem file_write_partial_source_is_short (o : outcome SyscallEffect) :
    syscall_spec (write_in 4 4096 2 mem_a) write_model o ↔
      o = Ok (with_copyins [(4096, 1)] (mkEffect 1 [] []))
             (with_fds (fd_insert write_fds 4 (.FdFileW [103] 1))
               (with_fs (fs_set write_fs [103] [97]) write_model)) [] := by
  rw_norm

/-- …and the full count is refused.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:mem-hide:a1+1:1 -- w-file -/
theorem file_write_partial_source_rejects_the_full_count (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 4 4096 2 mem_a) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- Rocq's `write_zero_len_within_file_is_a_noop`: zero bytes one byte
into "hi" leaves the file and the offset where they were.
rocq-twin: write_zero_len_within_file_is_a_noop
probe: testing/syscall-check/tests/write_spec.c#conform -- w-file-zero
The kernel side is `generic_write_checks_count` (fs/read_write.c, v6.18.46). -/
theorem write_zero_len_within_file_is_a_noop (o : outcome SyscallEffect) :
    syscall_spec (write_in 31 4096 0 mem_none) write_model o ↔
      o = Ok (mkEffect 0 [] [])
             (with_fds (fd_insert write_fds 31 (.FdFileW [102] 1))
               (with_fs (fs_set write_fs [102] [104, 105]) write_model)) [] := by
  rw_norm

/-- Rocq's `write_zero_len_past_eof_leaves_file_alone`: zero bytes past
the end of "hi" open no hole.
rocq-twin: write_zero_len_past_eof_leaves_file_alone
probe: testing/syscall-check/tests/rw_bytes_bound.c#conform -- gap-zero
The kernel side is `generic_write_checks_count` (fs/read_write.c, v6.18.46). -/
theorem write_zero_len_past_eof_leaves_file_alone (o : outcome SyscallEffect) :
    syscall_spec (write_in 3 4096 0 mem_none) wpast_model o ↔
      o = Ok (mkEffect 0 [] [])
             (with_fds (fd_insert (m_fds wpast_model) 3 (.FdFileW [102] 4))
               (with_fs (fs_set (m_fs wpast_model) [102] [104, 105]) wpast_model)) [] := by
  rw_norm

/-- Rocq's `write_zero_len_rejects_zero_length_copyin`: even a zero-length
source range claims a read that never happened.
rocq-twin: write_zero_len_rejects_zero_length_copyin
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:smuggle-copyin:a1:0 -- w-file-zero -/
theorem write_zero_len_rejects_zero_length_copyin (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 3 4096 0 mem_none) wpast_model
        (Ok (with_copyins [(4096, 0)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- …and no byte is claimed from a zero-length write.
probe: testing/syscall-check/tests/rw_bytes_bound.c#reject --mutate write#2:ret=1 -- gap-zero -/
theorem write_zero_len_past_eof_claims_no_byte (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 3 4096 0 mem_none) wpast_model (Ok (mkEffect 1 [] []) m' evs) := by
  rw_refute

/-- Rocq's `write_one_byte_past_eof_zero_fills`: "z" at offset 4 of "hi"
leaves "hi", two zero bytes, "z", and the offset at 5.
rocq-twin: write_one_byte_past_eof_zero_fills
probe: testing/syscall-check/tests/rw_bytes_bound.c#conform -- gap-at
The kernel side is `generic_perform_write` (mm/filemap.c, v6.18.46). -/
theorem write_one_byte_past_eof_zero_fills (o : outcome SyscallEffect) :
    syscall_spec (write_in 3 4096 1 (mem_z_at 4096)) wpast_model o ↔
      o = Ok (with_copyins [(4096, 1)] (mkEffect 1 [] []))
             (with_fds (fd_insert (m_fds wpast_model) 3 (.FdFileW [102] 5))
               (with_fs (fs_set (m_fs wpast_model) [102] [104, 105, 0, 0, 122]) wpast_model)) [] := by
  rw_norm

/-- …the hole is zeros, not closed up.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_one_byte_past_eof_no_fill_rejected (evs : List event) :
    ¬ syscall_spec (write_in 3 4096 1 (mem_z_at 4096)) wpast_model
        (Ok (with_copyins [(4096, 1)] (mkEffect 1 [] []))
            (with_fds (fd_insert (m_fds wpast_model) 3 (.FdFileW [102] 3))
              (with_fs (fs_set (m_fs wpast_model) [102] [104, 105, 122]) wpast_model)) evs) := by
  intro h
  sys_refute at h

/-- A zero-byte range past the limit is -EFAULT on a file too: `access_ok`
(include/asm-generic/access_ok.h, v6.18.46) in `vfs_write`
(fs/read_write.c:674-675, v6.18.46) precedes the file's own checks.
kernel: fs/read_write.c:vfs_write;include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem file_write_zero_count_past_the_limit_is_efault (o : outcome SyscallEffect) :
    syscall_spec (write_in 4 past_top 0 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- A path the file system does not hold declines: the descriptor was
minted by an `openat` this file system never saw.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_file_path_absent_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 27 4096 2 mem_ab) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- The source is read before the path is looked up: an unreadable source
on that descriptor is -EFAULT, not the absent-path decline.  Linux copies
the user bytes in `generic_perform_write` (mm/filemap.c:4290, v6.18.46),
through `copy_folio_from_iter_atomic` (lib/iov_iter.c:460-487, v6.18.46),
and answers -EFAULT once nothing was copied (mm/filemap.c:4331-4332)
whatever the file behind the descriptor holds.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_file_path_absent_unreadable_source_is_efault (o : outcome SyscallEffect) :
    syscall_spec (write_in 27 4096 1 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- …so the decline is refused there.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_file_path_absent_unreadable_source_is_not_a_decline :
    ¬ syscall_spec (write_in 27 4096 1 mem_none) write_model Unmodeled := by
  rw_refute

/-! ### The hole a write past the end opens

Linux zero-fills the gap between the file's end and the offset, with no
bound of its own; the model walks that gap byte for byte and stops at
`rw_bytes_max` (`modeled_zero_fill`), the inherited bound `Sys/Uaccess.lean`
carries.  A hole of exactly the bound is judged; one byte more declines.
A source with no readable byte at an offset past the end is declined
ahead of both, on either side of the bound — the one decline this twin
makes beyond Rocq's (`unreadable_source_past_eof`, and the pins after the
bound's). -/

/-- A hole one byte over the bound declines.
probe: testing/syscall-check/tests/write_window.c#fail-closed -- gap-over
(`rw_bytes_bound.c`'s `gap-over` case records the same decline.) -/
theorem write_gap_over_the_bound_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 33 4096 1 (mem_z_at 4096)) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- …and is not delivered.
probe: testing/syscall-check/tests/write_window.c#fail-closed -- gap-over -/
theorem write_gap_over_the_bound_is_not_delivered (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 33 4096 1 (mem_z_at 4096)) write_model
        (Ok (with_copyins [(4096, 1)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-- An unreadable source at the gap-declining offset declines too, and
not for the hole's size: it is the one shape `write_spec` declines where
Rocq answers.  Rocq's `write_file_tail` says -EFAULT with the file
untouched.  Linux v6.18.46 does not leave it untouched: `generic_perform_write`
(mm/filemap.c:4244-4335) has no pre-fault, calls `write_begin` (:4272)
before the copy (:4290) and `write_end` (:4293) after it, and tmpfs's
`shmem_write_end` (mm/shmem.c:3346-3368) moves `i_size` to `pos + copied`
whenever that passes the old size (:3352-3353) — `copied` being 0 — before
the loop answers -EFAULT for the byte that would not fault in
(:4321-4323, :4331-4332).  The file grows to the offset and the call
still returns -EFAULT.  Linux v4.17 through v6.13 fault the source in
ahead of `write_begin` and leave the file alone, as qemu-user does
(`lock_user` before the host write, linux-user/syscall.c:9848-9849,
QEMU 11.1.1).  No post-state is in the intersection, so the arm declines
(`unreadable_source_past_eof`);
bugs/write-file-past-eof-unreadable-source-answers-an-unchanged-file.md
records the Rocq answer.  The same decline within the bound is
`write_past_eof_unreadable_source_declines`.
kernel: mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem write_gap_unreadable_source_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 33 4096 1 mem_none) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- …and Rocq's -EFAULT with the file untouched is refused.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_gap_unreadable_source_is_not_efault :
    ¬ syscall_spec (write_in 33 4096 1 mem_none) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) write_model []) := by
  rw_refute

/-- Within the bound the same shape declines: one byte from an unreadable
source two bytes past the end of "hi" (`wpast_model`), where a readable
byte lands (`write_one_byte_past_eof_zero_fills`) and a zero count is a
no-op (`write_zero_len_past_eof_leaves_file_alone`).  The kernel argument
is `write_gap_unreadable_source_declines`'s.
kernel: mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem write_past_eof_unreadable_source_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 3 4096 1 mem_none) wpast_model o ↔ o = Unmodeled := by
  rw_norm

/-- …and the untouched-file -EFAULT is refused there too.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_past_eof_unreadable_source_is_not_efault :
    ¬ syscall_spec (write_in 3 4096 1 mem_none) wpast_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) wpast_model []) := by
  rw_refute

/-- AT the end of file the decline does not fire.  With `pos` equal to
`i_size`, `pos + copied` at `copied` 0 does not pass it (`shmem_write_end`,
mm/shmem.c:3352, v6.18.46; `ext4_da_do_write_end`, fs/ext4/inode.c:3246,
compares the same sum), so v6.18.46 leaves the file alone like every
other implementation, and -EFAULT with the file untouched is in the
intersection: the edge of `unreadable_source_past_eof`'s `<`.  The
-EFAULT itself is `generic_perform_write`'s (mm/filemap.c:4321-4323,
:4331-4332, v6.18.46).
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_at_eof_unreadable_source_is_efault (o : outcome SyscallEffect) :
    syscall_spec (write_in 3 4096 1 mem_none) wend_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) wend_model [] := by
  rw_norm

/-- …and is not the decline.
kernel: mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem write_at_eof_unreadable_source_is_not_a_decline :
    ¬ syscall_spec (write_in 3 4096 1 mem_none) wend_model Unmodeled := by
  rw_refute

/-- ONE byte past the end the decline fires: `pos + 0` is 3 against an
`i_size` of 2, so `shmem_write_end` (mm/shmem.c:3352-3353, v6.18.46) moves
the size by one byte before the -EFAULT, and the smallest hole is a hole.
The other side of the edge the pin above sits on.
kernel: mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem write_one_past_eof_unreadable_source_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 4 4096 1 mem_none) wend_model o ↔ o = Unmodeled := by
  rw_norm

/-- …and the untouched-file -EFAULT is refused one byte past the end.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_one_past_eof_unreadable_source_is_not_efault :
    ¬ syscall_spec (write_in 4 4096 1 mem_none) wend_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) wend_model []) := by
  rw_refute

/-- A hole of exactly `rw_bytes_max` past "hi" is within the model.
probe: testing/syscall-check/tests/rw_bytes_bound.c#conform -- gap-at -/
theorem write_gap_at_the_bound_is_modeled :
    modeled_file_gap [104, 105] (Z_to_bv 64 131074) [122] = true := by
  decide

/-- …and one byte more is not.
probe: testing/syscall-check/tests/rw_bytes_bound.c#fail-closed -- gap-over -/
theorem write_gap_over_the_bound_is_not_modeled :
    ¬ (modeled_file_gap [104, 105] (Z_to_bv 64 131075) [122] = true) := by
  decide

/-- A zero-byte write opens no hole at any offset.
probe: testing/syscall-check/tests/rw_bytes_bound.c#conform -- gap-zero -/
theorem write_zero_bytes_open_no_gap :
    modeled_file_gap [104, 105] (Z_to_bv 64 (2 ^ 62)) [] = true := by
  decide

/-! ### The count bound on the write-only kind

Rocq's `write_count_bound_declines_on_every_file_kind` and
`write_range_boundary_pins_the_three_file_kinds` walk `FdFileW`, `FdFileA`
and `FdFileRW`; the write-only third of each is pinned here, because
`write_spec` declines the other two kinds (the header of
`Sys/Fs/ReadWrite.lean` says so).  The boundary pin states the recorded
divergence `bugs/write-out-of-range-short-write.md`: a range that fails
`access_ok` by four bytes is judged by its readable prefix. -/

/-- Rocq's `write_count_bound_declines_on_every_file_kind`, the `FdFileW`
third: one byte over `rw_bytes_max` at four bytes below the limit declines.
rocq-twin: write_count_bound_declines_on_every_file_kind
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_count_bound_declines_on_the_write_only_kind (o : outcome SyscallEffect) :
    syscall_spec (write_in 4 near_top (Z_to_bv 64 131073) (mem_z_at near_top)) write_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …and AT the bound the arm judges, as Rocq's `at_bound` half says
(`vfs_write`, fs/read_write.c, v6.18.46).  The probe moves all 131072
bytes; the fixture keeps one readable so the normalizer can walk it.
What the fixture's range is, four bytes under `TASK_SIZE` and 131072
long, `access_ok` (:674-675) refuses: Linux answers -EFAULT and the model
judges the readable prefix, the divergence
`bugs/write-out-of-range-short-write.md` records and
`write_range_boundary_pins_the_write_only_kind` states in full.  What
this pin fixes is only that the bound itself is not a decline.
rocq-twin: write_count_bound_declines_on_every_file_kind
probe: testing/syscall-check/tests/rw_bytes_bound.c#conform -- w-at -/
theorem write_count_at_the_bound_is_judged_on_the_write_only_kind :
    ¬ syscall_spec (write_in 4 near_top (Z_to_bv 64 131072) (mem_z_at near_top)) write_model
        Unmodeled := by
  rw_refute

/-- Rocq's `write_range_boundary_pins_the_three_file_kinds`, the `FdFileW`
third: eight bytes at four below the limit, one of them readable, land as
one byte — the divergence `bugs/write-out-of-range-short-write.md` records:
`vfs_write` (fs/read_write.c:674-675, v6.18.46) would answer -EFAULT to
the whole range through `access_ok` — on riscv64 the `untagged_addr`
form, arch/riscv/include/asm/uaccess.h:42, over `__access_ok`'s
`addr <= TASK_SIZE_MAX - size` (include/asm-generic/access_ok.h:31-41),
all v6.18.46 — and the model judges the readable prefix.
rocq-twin: write_range_boundary_pins_the_three_file_kinds
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_range_boundary_pins_the_write_only_kind (o : outcome SyscallEffect) :
    syscall_spec (write_in 4 near_top 8 (mem_z_at near_top)) write_model o ↔
      o = Ok (with_copyins [(near_top, 1)] (mkEffect 1 [] []))
             (with_fds (fd_insert write_fds 4 (.FdFileW [103] 1))
               (with_fs (fs_set write_fs [103] [122]) write_model)) [] := by
  rw_norm

/-! ## A pipe: the whole count, a fresh page's -ENOMEM, or a decline

`anon_pipe_write` (fs/pipe.c:431-601, v6.18.46) copies the whole request
while slots remain — merged into the last buffer when it fits there
(:478-497) or onto a fresh page (:510-547), one of `PIPE_DEF_BUFFERS` =
16 (include/linux/pipe_fs_i.h:5) — and sleeps for a reader only once
every slot is taken (`pipe_full`, :510; the wait at :573).  The model's
ring is ONE page (`PipeBuf`, `pipe_write_room`), so the arm answers the
whole count when the source is readable and that page has room — and,
into an empty ring, also the -ENOMEM of a fresh page that fails to
allocate before the copy (`anon_pipe_get_page`, :515-519), which the
merge into a nonempty ring never calls — and declines everything else:
the second page Linux would take, the sleep the model cannot schedule, a
closed read end whose SIGPIPE (:460-465) has a disposition the model does
not carry, a short source whose two copy sites answer differently. -/

/-- "cd" after "ab" in pipe 0: appended, the count returned, the mark
carried up.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- rt
The kernel side is `anon_pipe_write` (fs/pipe.c, v6.18.46). -/
theorem pipe_write_appends_iff (o : outcome SyscallEffect) :
    syscall_spec (write_in 15 4096 2 mem_cd) write_model o ↔
      o = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
             (with_pipes (pipe_insert write_pipes 0 ([97, 98, 99, 100], 4)) write_model) [] := by
  rw_norm

/-- A pipe write with room is the full count, never short.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate write#1:ret=4 -- rt -/
theorem pipe_write_short_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 15 4096 2 mem_cd) write_model
        (Ok (with_copyins [(4096, 1)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-- -EAGAIN is `O_NONBLOCK`'s answer (fs/pipe.c:551-556, v6.18.46), a
flag no modeled pipe carries.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_is_not_eagain (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 15 4096 2 mem_cd) write_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  rw_refute

/-- -EPIPE needs a pipe with no readers; fd 14 holds pipe 0's.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_is_not_epipe (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 15 4096 2 mem_cd) write_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  rw_refute

/-- A pipe write emits no channel event: the bytes are in the queue.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_emits_no_channel_event (m' : Model) :
    ¬ syscall_spec (write_in 15 4096 2 mem_cd) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' [WriteEv 0 99, WriteEv 0 100]) := by
  rw_refute

/-- …and the queue changes: an unchanged pipe table is refused.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_unchanged_queue_rejected (evs : List event) :
    ¬ syscall_spec (write_in 15 4096 2 mem_cd) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) write_model evs) := by
  intro h
  sys_refute at h

/-- Into an empty pipe: a fresh page, the mark at the bytes written.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_into_an_empty_pipe (o : outcome SyscallEffect) :
    write_spec 17 4096 2 (write_in 17 4096 2 mem_cd) write_model o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) write_model [] ∨
      o = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
             (with_pipes (pipe_insert write_pipes 1 ([99, 100], 2)) write_model) [] := by
  rw_norm

/-! ### T169 / #1349: allocation failure before the first copy

No probe can force a page allocation to fail on demand.  The empty queue
uses `anon_pipe_get_page` before copying; a nonempty queue merges without
allocating (fs/pipe.c, `anon_pipe_write`, Linux v6.18.46). -/

/-- A drained pipe either returns -ENOMEM unchanged or delivers both bytes
with the new page's mark at two, independent of the old mark.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_into_a_drained_pipe (o : outcome SyscallEffect) :
    write_spec 17 4096 2 (write_in 17 4096 2 mem_cd)
      (with_pipes (pipe_insert write_pipes 1 ([], 3)) write_model) o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] [])
        (with_pipes (pipe_insert write_pipes 1 ([], 3)) write_model) [] ∨
      o = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        (with_pipes
          (pipe_insert (pipe_insert write_pipes 1 ([], 3)) 1 ([99, 100], 2))
          (with_pipes (pipe_insert write_pipes 1 ([], 3)) write_model)) [] := by
  rw_norm

/-- The fresh-page failure leaves every component of the model unchanged.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_empty_enomem_unchanged :
    write_spec 17 4096 2 (write_in 17 4096 2 mem_cd) write_model
      (Ok (mkEffect (errno_ret ENOMEM) [] []) write_model []) := by
  rw [pipe_write_into_an_empty_pipe]
  exact Or.inl rfl

/-- The allocation can also succeed and deliver the complete request.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_empty_delivery :
    write_spec 17 4096 2 (write_in 17 4096 2 mem_cd) write_model
      (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        (with_pipes (pipe_insert write_pipes 1 ([99, 100], 2)) write_model) []) := by
  rw [pipe_write_into_an_empty_pipe]
  exact Or.inr rfl

/-- The nonempty queue still delivers the complete request by merging.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_nonempty_delivery :
    write_spec 15 4096 2 (write_in 15 4096 2 mem_cd) write_model
      (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        (with_pipes (pipe_insert write_pipes 0 ([97, 98, 99, 100], 4)) write_model) []) := by
  rw_norm

/-- The merge path allocates no page, so cannot return this failure.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_nonempty_enomem_rejected (m' : Model) (evs : List event) :
    ¬ write_spec 15 4096 2 (write_in 15 4096 2 mem_cd) write_model
      (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  rw_refute

/-- A failed allocation has not read the source, so has no copy-in ledger.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_empty_enomem_copyin_rejected (m' : Model) (evs : List event) :
    ¬ write_spec 17 4096 2 (write_in 17 4096 2 mem_cd) write_model
      (Ok (with_copyins [(4096, 2)] (mkEffect (errno_ret ENOMEM) [] [])) m' evs) := by
  rw_refute

/-- One byte into the page pipe 5 has one byte of room in: it fits, and the
mark reaches the page's end.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- merge
The kernel side is `anon_pipe_write` (fs/pipe.c, v6.18.46). -/
theorem pipe_write_merges_into_the_page (o : outcome SyscallEffect) :
    syscall_spec (write_in 35 4096 1 (mem_z_at 4096)) write_model o ↔
      o = Ok (with_copyins [(4096, 1)] (mkEffect 1 [] []))
             (with_pipes (pipe_insert write_pipes 5 ([120, 122], 4096)) write_model) [] := by
  rw_norm

/-- …and is not 0.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate write#2:ret=0 -- merge -/
theorem pipe_write_merge_is_not_zero (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 35 4096 1 (mem_z_at 4096)) write_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- Two bytes into one byte of room declines.  Linux does not sleep here:
the merge needs the whole two bytes to fit the last page (`offset + chars
<= PAGE_SIZE`, fs/pipe.c:482-483, v6.18.46), so it takes a fresh page
instead (:510-530), fifteen slots being free, and returns 2.  The model's
ring is one page (`pipe_write_room`), so it has no second page to take,
and declines rather than answer.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_past_the_mark_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 35 4096 2 mem_cd) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- One byte over a page into an empty pipe declines.  Linux fills one
page and puts the byte on a second (fs/pipe.c:510-547, v6.18.46; sixteen
slots), returning 4097; the model's ring is one page and has nowhere to
put it.  The arm tests the room before it reads the source
(`pipe_write_room` ahead of `write_source`), so the source is left
unreadable here (`mem_none`): no byte of it is consulted, and a
4097-byte readable source is beyond the normalizer's reach.  A symbolic
memory would say the same, but the fd lookup is evaluated by the ground
pass and a symbolic `in_mem` keeps the input open.  (The page-filling
write itself, `pipe2_spec.c`'s `page` case, is a 4096-byte source the
normalizer cannot evaluate; the page boundary is pinned on pipe 5
above.)
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_over_the_page_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 17 4096 (Z_to_bv 64 4097) mem_none) write_model o ↔
      o = Unmodeled := by
  rw_norm

/-- A pipe whose read end is closed declines: SIGPIPE is sent beside the
-EPIPE (fs/pipe.c:460-465, v6.18.46) and its disposition is not modeled.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_without_a_reader_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 28 4096 1 (mem_z_at 4096)) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- …so -EPIPE is not the arm's answer: with SIGPIPE at its default the
task dies in `get_signal` (kernel/signal.c:3043, v6.18.46) before the
errno is seen.
kernel: kernel/signal.c:get_signal@v6.18.46 -/
theorem pipe_write_without_a_reader_is_not_epipe (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 28 4096 1 (mem_z_at 4096)) write_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  rw_refute

/-- A null write returns 0 before the reader test (`anon_pipe_write`,
fs/pipe.c:454-456, v6.18.46): no SIGPIPE, no -EPIPE.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- write0dead -/
theorem pipe_write_without_a_reader_zero_count_is_zero (o : outcome SyscallEffect) :
    syscall_spec (write_in 28 4096 0 mem_none) write_model o ↔
      o = Ok (mkEffect 0 [] []) write_model [] := by
  rw_norm

/-- …and is not -EPIPE (`anon_pipe_write`, fs/pipe.c:460-465, v6.18.46).
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate write#1:ret=-32 -- write0dead -/
theorem pipe_write_without_a_reader_zero_count_is_not_epipe (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 28 4096 0 mem_none) write_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  rw_refute

/-- A pipe id the table does not hold declines: `pipe2` never mints one.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_pipe_id_absent_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 32 4096 1 (mem_z_at 4096)) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- A source readable only in part declines: a merge that copies fewer
bytes than asked is -EFAULT whatever it copied (fs/pipe.c:489-491,
v6.18.46); a fresh page that faults is dropped and the call returns the
bytes counted on the pages before it, -EFAULT when there were none
(:523-527); and the arm spells neither.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_partial_source_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 15 4096 2 mem_a) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- …neither the short write…
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_partial_source_is_not_short (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 15 4096 2 mem_a) write_model
        (Ok (with_copyins [(4096, 1)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-- …nor the -EFAULT.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_partial_source_is_not_efault (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 15 4096 2 mem_a) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- Nothing readable declines too: the arm's short-source rule has no
exception for the empty prefix.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_unreadable_source_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 15 4096 2 mem_none) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- A count past the limit declines on a pipe, as on every kind.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pipe_write_count_past_the_limit_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 15 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model o ↔
      o = Unmodeled := by
  rw_norm

/-- A zero count on a pipe is 0, the null write's early return.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_zero_count_is_zero (o : outcome SyscallEffect) :
    syscall_spec (write_in 15 4096 0 mem_none) write_model o ↔
      o = Ok (mkEffect 0 [] []) write_model [] := by
  rw_norm

/-! ## write (64): the adversarial round

Lies a kernel could tell about a write, one pin each, sorted by the arm
they attack, with the honest answers the round found unpinned beside
them.  Where a harness case already refuses the same lie it is named; the
two-byte fixtures pin the same rule at a size the normalizer evaluates. -/

/-- Rocq's third group: an oversized count at a MAPPED buffer declines on
no kind — the write-only kind judges 131073 bytes at 4096 byte for byte,
the one readable byte landing as a one-byte write.  The probe moves all
131073 bytes; the fixture keeps one readable so the normalizer can walk it.
rocq-twin: write_count_bound_declines_on_every_file_kind
probe: testing/syscall-check/tests/rw_bytes_bound.c#conform -- w-over -/
theorem write_count_over_the_bound_at_a_mapped_buffer_is_judged :
    ¬ syscall_spec (write_in 4 4096 (Z_to_bv 64 131073) (mem_z_at 4096)) write_model
        Unmodeled := by
  rw_refute

/-! ### The channel: `write_spec.c`'s remaining reject cases, and the events -/

/-- The ledger starts at `buf`, not one past it.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:shift-copyins:1 -- w-full -/
theorem write_shifted_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4097, 2)] (mkEffect 2 [] [])) m' evs) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- A two-byte delivery records two bytes, not three.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:grow-copyins:1 -- w-full -/
theorem write_grown_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 3)] (mkEffect 2 [] [])) m' evs) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- 2^64 - 1, the encoding of -1, is no delivery of a two-byte write.
probe: testing/syscall-check/tests/write_spec.c#reject --mutate write:ret=max64 -- w-full -/
theorem write_max64_return_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect (Z_to_bv 64 (2 ^ 64 - 1)) [] [])) m' evs) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- The delivered bytes are the trace, in order: none dropped…
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_dropped_events_rejected (m' : Model) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' []) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- …none reordered…
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_reordered_events_rejected (m' : Model) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' [WriteEv 1 98, WriteEv 1 97]) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-- …and the ledger holds the one range the copy read, no second.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_second_ledger_entry_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 1 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2), (8192, 1)] (mkEffect 2 [] [])) m' evs) := by
  first
    | rw_refute
    | rw_norm
      intro x hl hn _ hev hlo hhi hx
      rw [← hn] at hx
      subst hx
      first
        | exact absurd hn (by decide)
        | exact absurd hlo (by decide)
        | exact absurd hhi (by decide)
        | exact absurd hl (by decide)
        | (sys_simp_pass +ground +decide at hl; done)
        | (sys_simp_pass +ground +decide at hev; done)

/-! ### -EBADF before the range, on more than the closed descriptor -/

/-- A pipe's read end one past the limit at count 0: -EBADF, the mode test
`vfs_write` runs before `access_ok`.
kernel: fs/read_write.c:vfs_write;include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem write_pipe_read_end_beats_the_range (o : outcome SyscallEffect) :
    syscall_spec (write_in 14 past_top 0 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- …and delivers nothing: a write to the READ end cannot succeed.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate write:ret=1 -- wrongend -/
theorem write_pipe_read_end_delivers_nothing (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 14 4096 1 mem_cd) write_model (Ok (mkEffect 1 [] []) m' evs) := by
  rw_refute

/-- A read-only file with a 2^63-byte count: -EBADF, not a range decline.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_read_only_file_beats_the_range (o : outcome SyscallEffect) :
    syscall_spec (write_in 3 4096 (Z_to_bv 64 (2 ^ 63)) mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-! ### The zero count at the address-space limit, kind by kind

`access_ok` is `vfs_write`'s (fs/read_write.c:674-675, v6.18.46), ahead of
every file operation, so a zero-byte range AT `TASK_SIZE` is 0 and one
past it -EFAULT on every kind with `FMODE_WRITE` — including the kinds
whose own answer would otherwise be a decline.  The pins name `at_top`
and `past_top`, whose docstrings carry the `TASK_SIZE_MAX` chain. -/

/-- /dev/null at the limit: 0.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem write_devnull_zero_count_at_the_limit_is_zero (o : outcome SyscallEffect) :
    syscall_spec (write_in 9 at_top 0 mem_none) write_model o ↔
      o = Ok (mkEffect 0 [] []) write_model [] := by
  rw_norm

/-- …one past it: -EFAULT.
kernel: fs/read_write.c:vfs_write;include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem write_devnull_zero_count_past_the_limit_is_efault (o : outcome SyscallEffect) :
    syscall_spec (write_in 9 past_top 0 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- A pipe one past the limit: -EFAULT before the pipe is looked at.
kernel: fs/read_write.c:vfs_write;include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pipe_write_zero_count_past_the_limit_is_efault (o : outcome SyscallEffect) :
    syscall_spec (write_in 15 past_top 0 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- A pipe whose reader is gone, one past the limit: `access_ok` fires
before `anon_pipe_write`'s reader test, so the answer is -EFAULT and not
the decline a reader-less pipe otherwise earns.
kernel: fs/read_write.c:vfs_write;include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pipe_write_without_a_reader_past_the_limit_is_efault (o : outcome SyscallEffect) :
    syscall_spec (write_in 28 past_top 0 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- The write-only file at the limit: 0, the file and the offset untouched
(fd 4 sits at offset 0 of the one-byte file "j").
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem file_write_zero_count_at_the_limit_is_zero (o : outcome SyscallEffect) :
    syscall_spec (write_in 4 at_top 0 mem_none) write_model o ↔
      o = Ok (mkEffect 0 [] [])
             (with_fds (fd_insert write_fds 4 (.FdFileW [103] 0))
               (with_fs (fs_set write_fs [103] [106]) write_model)) [] := by
  rw_norm

/-- An absent path one past the limit: -EFAULT beats the decline the
absent path earns…
kernel: fs/read_write.c:vfs_write;include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem write_file_path_absent_past_the_limit_is_efault (o : outcome SyscallEffect) :
    syscall_spec (write_in 27 past_top 0 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- …which an in-range zero count still earns: the path is looked up for
a zero-byte write too, and a path this file system never saw is the
model's own gap, not a kernel answer.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_file_path_absent_zero_count_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 27 4096 0 mem_none) write_model o ↔ o = Unmodeled := by
  rw_norm

/-! ### A range decline is a decline, on every kind -/

/-- /dev/null, 2^20 bytes from four below the limit: the decline is not
-EFAULT…
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_devnull_count_past_the_limit_is_not_efault (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 9 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- …nor on a pipe…
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pipe_write_count_past_the_limit_is_not_efault (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 15 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- …nor on the write-only file.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem file_write_count_past_the_limit_is_not_efault (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 4 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- The count-bound decline is not the one-byte short write the in-bound
call answers: a decline is a decline (`vfs_write`, fs/read_write.c, v6.18.46).
rocq-twin: write_count_bound_declines_on_every_file_kind
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_count_bound_decline_is_not_a_short_write (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 4 near_top (Z_to_bv 64 131073) (mem_z_at near_top)) write_model
        (Ok (with_copyins [(near_top, 1)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-! ### The position test at LLONG_MAX

`rw_verify_area` (fs/read_write.c:460-470, v6.18.46) answers -EINVAL when
`(loff_t) (pos + count) < 0` (:467-469): the sum wrapping past LLONG_MAX.
`rw_pos_einvalb` is that test on the model's unsigned offset, and its edge
is 2^63 - 1 exactly.  No `write` arm here calls it yet (the `FdFileA` and
`FdFileRW` arms are another ticket's, module header; `pread64_spec` and
`pwrite64_spec` do, pinned below), so the helper is pinned on its own — and so is `append_new_pos`, which Rocq's `FdFileA`
arms of `write` and `writev` call and nothing here calls yet, whose
zero-length arm is the whole of its argument. -/

/-- A sum of exactly LLONG_MAX is not negative: no -EINVAL.
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem rw_pos_at_llong_max_is_not_einval :
    rw_pos_einvalb (Z_to_bv 64 (2 ^ 63 - 2)) 1 = false := by
  decide

/-- …and one byte more wraps negative: -EINVAL.
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem rw_pos_past_llong_max_is_einval :
    rw_pos_einvalb (Z_to_bv 64 (2 ^ 63 - 1)) 1 = true := by
  decide

/-- A zero-length append leaves the offset where the `lseek` put it, seven
bytes into a two-byte file: `generic_write_checks_count` returns 0
(fs/read_write.c:1744-1745, v6.18.46) before the `IOCB_APPEND` assignment
of `ki_pos` (:1747-1748), and `new_sync_write` copies the position back
only for a positive return (:595-596).
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem append_zero_length_keeps_the_offset :
    append_new_pos [104, 105] [] (Z_to_bv 64 7) = Z_to_bv 64 7 := by
  decide

/-- …and not the file's end, which an unconditional assignment would say.
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem append_zero_length_is_not_the_end_of_file :
    ¬ (append_new_pos [104, 105] [] (Z_to_bv 64 7) = Z_to_bv 64 2) := by
  decide

/-- A delivering append ends at the NEW end of file, the old size plus the
bytes landed, wherever the offset stood: `ki_pos` is `i_size` under
`IOCB_APPEND` (fs/read_write.c:1747-1748, v6.18.46) and
`generic_perform_write` moves it by what landed (mm/filemap.c:4333).
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem append_delivery_ends_at_the_new_end :
    append_new_pos [104, 105] [122] (Z_to_bv 64 7) = Z_to_bv 64 3 := by
  decide

/-- …and not at the offset advanced by the count, the `FdFileW` answer.
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem append_delivery_is_not_the_offset_advanced :
    ¬ (append_new_pos [104, 105] [122] (Z_to_bv 64 7) = Z_to_bv 64 8) := by
  decide

/-! ### /dev/null, the write-only file and the pipe: return, ledger, state -/

/-- /dev/null returns the count named, not one less…
kernel: drivers/char/mem.c:write_null@v6.18.46 -/
theorem write_devnull_under_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 9 4096 5 mem_none) write_model (Ok (mkEffect 4 [] []) m' evs) := by
  rw_refute

/-- …and touches no descriptor.
kernel: drivers/char/mem.c:write_null@v6.18.46 -/
theorem write_devnull_leaves_the_table_alone :
    ¬ syscall_spec (write_in 9 4096 5 mem_none) write_model
        (Ok (mkEffect 5 [] []) (with_fds [] write_model) []) := by
  rw_refute

/-- A two-byte file write that read no user byte: the ledger is not
optional.  `write_window.c`'s case moves 262144 bytes; the two-byte
fixture pins the same rule at a size the normalizer walks.
probe: testing/syscall-check/tests/write_window.c#reject --mutate write#2:drop-copyins -- big -/
theorem file_write_dropped_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 4 4096 2 mem_ab) write_model
        (Ok (mkEffect 2 [] []) m' evs) := by
  rw_refute

/-- …nor may it name a third byte the copy never read.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem file_write_grown_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 4 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 3)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- Three bytes returned for a two-byte request: `vfs_write` returns what
the write operation moved, never more than `count`.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem file_write_over_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 4 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 3)] (mkEffect 3 [] [])) m' evs) := by
  rw_refute

/-- A file write copies FROM user memory: no user byte is written.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem file_write_smuggled_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 4 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [(4096, [97])] [])) m' evs) := by
  rw_refute

/-- The bytes land in the descriptor's own file, not in another path.
kernel: fs/read_write.c:ksys_write@v6.18.46 -/
theorem file_write_wrong_file_rejected :
    ¬ syscall_spec (write_in 4 4096 2 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
            (with_fds (fd_insert write_fds 4 (.FdFileW [103] 2))
              (with_fs (fs_set write_fs [102] [97, 98]) write_model)) []) := by
  rw_refute

/-- The clamp on a file: 2^40 named at 4096 with two readable zero bytes
lands those two at offset 0 — judged, clamped, short by the source.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem file_write_over_the_clamp_is_judged (o : outcome SyscallEffect) :
    syscall_spec (write_in 4 4096 (Z_to_bv 64 (2 ^ 40)) (mem_first 2)) write_model o ↔
      o = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
             (with_fds (fd_insert write_fds 4 (.FdFileW [103] 2))
               (with_fs (fs_set write_fs [103] [0, 0]) write_model)) [] := by
  rw_norm

/-- The pipe copy read two user bytes: the ledger says so.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_dropped_ledger_rejected :
    ¬ syscall_spec (write_in 15 4096 2 mem_cd) write_model
        (Ok (mkEffect 2 [] [])
            (with_pipes (pipe_insert write_pipes 0 ([97, 98, 99, 100], 4)) write_model) []) := by
  rw_refute

/-- The merge mark moves up by the bytes appended: 2 + 2 is 4, not 2.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_stale_mark_rejected :
    ¬ syscall_spec (write_in 15 4096 2 mem_cd) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
            (with_pipes (pipe_insert write_pipes 0 ([97, 98, 99, 100], 2)) write_model) []) := by
  rw_refute

/-- The bytes go into the descriptor's pipe, not another.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_wrong_pipe_rejected :
    ¬ syscall_spec (write_in 15 4096 2 mem_cd) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
            (with_pipes (pipe_insert write_pipes 1 ([99, 100], 2)) write_model) []) := by
  rw_refute

/-- Three for two: a pipe write returns the count it was asked, never more.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_over_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 15 4096 2 mem_cd) write_model
        (Ok (with_copyins [(4096, 3)] (mkEffect 3 [] [])) m' evs) := by
  rw_refute

/-- A pipe write copies FROM user memory: no user byte is written.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_smuggled_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (write_in 15 4096 2 mem_cd) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [(4096, [99])] [])) m' evs) := by
  rw_refute

/-- fd 2^32 + 15 is the pipe's write end: the same append as fd 15, the
truncation `ksys_write`'s `unsigned int fd` performs on every kind.
kernel: fs/read_write.c:ksys_write@v6.18.46 -/
theorem write_fd_truncates_on_a_pipe (o : outcome SyscallEffect) :
    syscall_spec (write_in (Z_to_bv 64 (2 ^ 32 + 15)) 4096 2 mem_cd) write_model o ↔
      o = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
             (with_pipes (pipe_insert write_pipes 0 ([97, 98, 99, 100], 4)) write_model) [] := by
  rw_norm

/-! ## readv (65) and writev (66): the vectored pair, read off against Linux

Worked examples over `Sys.Fs.ReadWrite.readv_spec` (this section and its
subsections); over `writev_file_arm`, the helper every file writev arm
shares (its own section below); and over `Sys.Fs.ReadWrite.writev_spec`
through the table (the sections after it), whose `FdFileW` arm applies
ticket S-Fs-ReadWrite-write's `modeled_file_gap` (PR #1127).  Everything
is stated as the read pins above are: through the dispatcher on a
`SyscallInput` numbered 65 or 66, an `iff` over every outcome and a
refutation of the lie a kernel could tell, line numbers Linux v6.18.46
(commit 1f99e9ab748f).

THE VECTOR IS IN `in_mem`, THE DESTINATION IN `in_wmem`.  `readv` reads
its descriptor array through the readable view and writes the delivered
bytes through the writable one, so a fixture names both: `iov_array`
lays `struct iovec`s out at 8192 as user memory holds them (eight
little-endian bytes of `iov_base`, then eight of `iov_len`), and the
`wmem_*` views above say where a delivered byte may land.

THE COPY-IN LEDGER IS PART OF THE ANSWER.  Every outcome below carries
`with_copyins` with the descriptor ranges the import read — one
sixteen-byte range per descriptor `copy_iovec_from_user` fetched, in
index order, stopping after the first it could not (lib/iov_iter.c
:1260-1290) — because `Run.apply_effect` materialises those pages, so
two outcomes differing only in the ledger are different post-states.

WHERE THE DELIVERY IS THE ENVIRONMENT'S.  On a channel or a connected
socket the delivered length is chosen, as for `read`; the pins state
the instances (whole, short) and the refutations first, and the `iff`
over the choice closes the readv pins (`readv_stdin_delivers_a_prefix_iff`,
`readv_socket_delivers_a_prefix_iff`), for the reason
`readv_stdin_full_delivery` gives. -/

attribute [sys_simp low] readv_spec.eq_1 readv_heap_gap.eq_1 readv_buf_gap.eq_1
  writev_file_arm.eq_1 writev_file_arm.eq_2 writev_ledger.eq_1 writev_buf_gap.eq_1
-- `writev_file_arm` has two equations, not one: its match on `data`, the file
-- the kind found, is on a parameter, so Lean splits the unfolding into the
-- `some` case (`eq_1`) and the `none` case (`eq_2`); the pins on a kind that
-- found no file read the second.
attribute [sys_simp low] readable_fd.eq_1 readable_fd.eq_2 readable_fd.eq_3 readable_fd.eq_4
  readable_fd.eq_5 readable_fd.eq_6 readable_fd.eq_7 readable_fd.eq_8

/-! `record_copyins` is the calling-convention wrapper both vectored calls
answer through (Sys/Syscall.lean); `Checks/Cases/Fs/Namei.lean` unfolds it
the same way.  `scatter_iovecs`' three equations, with `List.take` and
`List.drop` over a cons, are what lets a delivery of SYMBOLIC bytes
scatter: the ground pass cannot evaluate `scatter_iovecs (wmem_first 5)
[(4096, 2), (4098, 3)] [b, c, d, e, f]` while `b` is a variable, but the
equations reduce it segment by segment, since only the LENGTHS decide
the shape and `read_bytes_map (wmem_first 5) 4096 2` is closed. -/
attribute [sys_simp low] record_copyins.eq_1
attribute [sys_simp low] scatter_iovecs.eq_1 scatter_iovecs.eq_2 scatter_iovecs.eq_3
attribute [sys_simp] List.take_succ_cons List.take_zero List.drop_succ_cons List.drop_zero

/-- `readv(fd, iov, iovcnt)` as the dispatcher sees it: syscall 65, `mem`
the readable view the descriptor array is fetched through, `wmem` the
writable view the bytes land in. -/
def readv_in (fd iov iovcnt : word) (mem wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 65 [fd, iov, iovcnt, 0, 0, 0] mem wmem

/-- An iovec array at 8192, each entry eight little-endian bytes of
`iov_base` then eight of `iov_len` (include/uapi/linux/uio.h `struct
iovec`, riscv little-endian; v6.18.46), nothing else readable. -/
def iov_array (iovs : List (word × word)) : word → Option byte :=
  bytes_at 8192 (iovs.flatMap fun bl => word_le8 bl.1 ++ word_le8 bl.2)

/-- One descriptor: `{4096, 1}`, and NOTHING from 8208 on.  Rocq's
`mem_readv_iov`.  The guard is not a modeling choice — `iov_array` already
answers `none` past its bytes — but what keeps a lookup PAST the array,
the second descriptor of a two-descriptor call, a closed `none` the ground
pass reads in one step: without it the same lookup is a `bytes_at` index
past the list's end, which the pass evaluates by `whnf` beyond any
heartbeat budget (measured at 4M). -/
def mem_readv_iov : word → Option byte :=
  fun a => if bv_ltu a 8208 then iov_array [(4096, 1)] a else none

/-- Two descriptors given as words, plus one readable source byte at 4096
(for the writev shapes).  Rocq's `mem_iov_pair`. -/
def mem_iov_pair (b0 l0 b1 l1 : word) : word → Option byte :=
  fun a => if bv_eqb a 4096 then some 97 else iov_array [(b0, l0), (b1, l1)] a

/-- The single-versus-multi import order probe: a first entry exactly
`MAX_RW_COUNT` below the top of the address space and one byte longer
than `MAX_RW_COUNT`, then `{NULL, 0}`.  Rocq's `mem_readv_cap_order`. -/
def mem_readv_cap_order : word → Option byte :=
  iov_array [(Z_to_bv 64 (TASK_SIZE - MAX_RW_COUNT), Z_to_bv 64 (MAX_RW_COUNT + 1)), (0, 0)]

/-- One descriptor of 2^62 bytes at 4096.  Rocq's `mem_readv_huge`. -/
def mem_readv_huge : word → Option byte := iov_array [(4096, Z_to_bv 64 (2 ^ 62))]

/-- Eight all-zero descriptors: 128 zero bytes at 8192.  Rocq's
`mem_readv_eight_zero`. -/
def mem_readv_eight_zero : word → Option byte := bytes_at 8192 (List.replicate 128 0)

/-- The first entry's base bytes absent and its length 2^63, then a
readable `{4096, 1}`: the array starts at 8200.  Rocq's `mem_readv_len_only`. -/
def mem_readv_len_only : word → Option byte :=
  bytes_at 8200 (word_le8 (Z_to_bv 64 (2 ^ 63)) ++ word_le8 4096 ++ word_le8 1)

/-- Exactly the byte at 4096 writable.  Rocq's `wmem_readv_one`. -/
def wmem_readv_one : word → Option byte := fun a => if bv_eqb a 4096 then some 0 else none

/-- "ab" at 4096 beside the two-descriptor array `{4096,1},{4097,1}`, the
writev gather fixture.  Rocq's `mem_writev_ab`. -/
def mem_writev_ab : word → Option byte :=
  fun a => if bv_eqb a 4096 then some 97 else if bv_eqb a 4097 then some 98
           else iov_array [(4096, 1), (4097, 1)] a

/-- A file "abcde" on fd 3 at offset `off`.  Rocq's `readv_abcde_model`. -/
def readv_abcde_model (off : word) : Model :=
  fixture_of (fds := [(3, .FdFile [102] off)]) (fs := [([102], [97, 98, 99, 100, 101])])

/-- A one-byte file "x" on fd 3 at offset `off`.  Rocq's
`readv_huge_file_model`, with the offset a parameter. -/
def readv_x_model (off : word) : Model :=
  fixture_of (fds := [(3, .FdFile [102] off)]) (fs := [([102], [120])])

/-- The two-descriptor destination `{4096,2},{4098,3}` of the channel and
file deliveries below, and what the delivered bytes scatter to. -/
def iov_2_3 : word → Option byte := iov_array [(4096, 2), (4098, 3)]

/-! The call and the models are unfolded by `sys_norm`; the byte maps are
NOT.  A map left folded is a closed term the ground pass evaluates in one
step wherever the spec applies it, where a map unfolded to `bytes_at 8192
(List.flatMap …)` is re-evaluated at every lookup, and an out-of-range
lookup — the second descriptor of a one-descriptor array — then runs
`whnf` past its heartbeat budget.  The read pins above leave `wmem_first`
folded for the same reason. -/
attribute [sys_simp low] readv_in.eq_1 readv_abcde_model.eq_1 readv_x_model.eq_1

/-! ## The two delivering arms, read on the scatter

`readv_imported`'s channel and connected-socket arms choose the DELIVERED
BYTES `bs` and then the writes their scatter returns; the scatter of a
symbolic `bs` is a `match` nothing can reduce, so a pin on a forged
outcome, whose ledger names the scattered WRITES, has no equation to
substitute the first choice with.  `State.scatter_iovecs_concat` says the
writes determine the bytes — their concatenation IS `bs` — so the two
choices are one choice of the writes, the bytes taken as their
concatenation.  `choose_scatter_eq` below states that for ANY predicate on
the bytes and ANY continuation, and `sys_norm` reads the two arms through
it once their own equations have unfolded them: the outcome's ledger then
meets the chosen writes as an equation the existential eliminates.

It is parametric on purpose.  An equation restating an arm is false under
a mutant of the arm, so the mutant dies by that equation's failed proof
while every pin still reads the arm through the equation's UNMUTATED
right-hand side, and the sweep measures no pin.  The two per-arm equations
this replaced did exactly that to 22 mutants.  This one holds of every
arm, mutated or not, so what a pin reads is the arm as it is. -/

/-- The bytes a scatter delivered, in order: what the writes concatenate
to.  `State.scatter_iovecs_concat` is the equation that makes it the
chosen `bs`.
model: `readv_bytes`, the flatten of a ledger's byte lists; a definition, not a claim about Linux -/
def readv_bytes (writes : List (word × List byte)) : List byte := (writes.map Prod.snd).flatten

/-- The two choices of a delivering arm — the bytes under `P`, then the
ledger their scatter returns — are one choice of the ledger, under `P` of
its concatenation (`State.scatter_iovecs_concat`).  The deliveries it
serves are `anon_pipe_read` (fs/pipe.c:268-404, v6.18.46) and
`tcp_recvmsg_locked` (net/ipv4/tcp.c:2634-2910, v6.18.46); nothing here
decides either.
model: `choose_scatter_eq`, a rewrite between two `Sys` terms over `State.scatter_iovecs`; not a claim about Linux -/
theorem choose_scatter_eq {B : Type} (mp : word → Option byte) (iovs : List (word × word))
    (P : List byte → Prop) (k : List byte → List (word × List byte) → Sys B) :
    (bs <- choose P ;;
     writes <- choose (fun writes : List (word × List byte) =>
                 scatter_iovecs mp iovs bs = some writes) ;;
     k bs writes) =
    (writes <- choose (fun writes : List (word × List byte) =>
                 P (readv_bytes writes) ∧ scatter_iovecs mp iovs (readv_bytes writes) = some writes) ;;
     k (readv_bytes writes) writes) := by
  funext i m o
  apply propext
  simp only [bind_choose_iff]
  constructor
  · rintro ⟨bs, hP, w, hs, hk⟩
    have hc := scatter_iovecs_concat _ _ bs w hs
    subst hc
    exact ⟨w, ⟨hP, hs⟩, hk⟩
  · rintro ⟨w, ⟨hP, hs⟩, hk⟩
    exact ⟨readv_bytes w, hP, w, hs, hk⟩

/-! Every arm of `readv_imported` is read through its own equation, the
channel's `readv_imported.eq_1` among them, and a connected socket's head
cell through `cell_at_zero_cons`; `choose_scatter_eq` then meets the two
delivering arms' choices wherever the unfolding leaves them.  `readv_bytes`
unfolds under it; `List.map` and `List.flatten` over a closed ledger shape
reduce to the byte list. -/
attribute [sys_simp] choose_scatter_eq
attribute [sys_simp low] readv_bytes.eq_1 iov_prefix_accesses
attribute [sys_simp] List.map_cons List.map_nil List.flatten_cons List.flatten_nil
  List.cons_append List.nil_append List.append_nil
attribute [sys_simp low] readv_imported.eq_1 readv_imported.eq_2 readv_imported.eq_3 readv_imported.eq_4
  readv_imported.eq_5 readv_imported.eq_6 readv_imported.eq_7 readv_imported.eq_8
  readv_imported.eq_9 readv_imported.eq_10 readv_imported.eq_11

/-! A refutation of a delivery that leaves the input where it was compares
two streams, and a stream is a function: `StreamLaws`' injectivity of
`ICons` and `NCons` reduces the comparison to the bytes.  The laws see a
stream only while it is spelled as a chain — the ground pass evaluates a
closed one to its function first — so the two refutations that need them
give the stream a symbolic tail. -/
attribute [sys_simp] ICons_eq_ICons NCons_eq_NCons

/-! ## `do_readv`: the descriptor, then `FMODE_READ`, then the count

`do_readv` (fs/read_write.c:1068-1089, v6.18.46) resolves the fd with
`CLASS(fd_pos, f)(fd)` (:1071) and answers -EBADF on an empty slot (:1072-1074)
before `vfs_readv` (:1080), whose first test is `FMODE_READ` (:999-1000),
ahead of `import_iovec` (:1004-1005), since b8e1425bae85 in v6.8.
Linux v4.17 through v6.7 imports first (fs/read_write.c, vfs_readv,
v6.6:913), then checks the mode in do_iter_read. In v6.8+ a closed fd and an fd open
without `FMODE_READ` are -EBADF whatever the array holds — even when no
byte of it is readable, which is the shape qemu-user answers -EFAULT for
(its `lock_iovec` locks the array before it dispatches on the fd).
The spec declines these disagreements and answers -EBADF only on the
shared readable-array, empty-first-entry shape; an open wrong-mode fd
also needs count ≤ 8 and every uncapped range to pass access_ok. -/

/-- For readv on closed fd 30, count 2 names an unreadable array at 8192. Linux returns -EBADF
and qemu-user returns -EFAULT; the pin declines this call as `Unmodeled`.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdiov -/
theorem readv_closed_fd_declines (o : outcome SyscallEffect) :
    readv_spec 30 8192 2 (readv_in 30 8192 2 wmem_none wmem_none) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For readv on closed fd 30, count 2 names an unreadable array at 8192. Linux returns -EBADF
and qemu-user returns -EFAULT; the pin refuses the former concrete `-EBADF` outcome.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdiov -/
theorem readv_closed_fd_declines_old_answer_refuted :
    ¬ readv_spec 30 8192 2 (readv_in 30 8192 2 wmem_none wmem_none) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- Readv on closed fd 30 with count 2 and an unreadable array at 8192 returns -EBADF in Linux
and -EFAULT in qemu-user. The dispatcher pin refuses a zero-return outcome for this declined
shape.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdiov -/
theorem readv_closed_fd_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 30 8192 2 wmem_none wmem_none) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- For readv on closed fd 30, count 5000 exceeds IOV_MAX and the array at 8192 is unreadable.
Linux returns -EBADF and qemu-user rejects the count with -EINVAL; the pin declines this call as
`Unmodeled`.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdover -/
theorem readv_closed_fd_bad_count_declines (o : outcome SyscallEffect) :
    readv_spec 30 8192 5000 (readv_in 30 8192 5000 wmem_none wmem_none) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For readv on closed fd 30, count 5000 exceeds IOV_MAX and the array at 8192 is unreadable.
Linux returns -EBADF and qemu-user rejects the count with -EINVAL; the pin refuses the former
concrete `-EBADF` outcome.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdover -/
theorem readv_closed_fd_bad_count_declines_old_answer_refuted :
    ¬ readv_spec 30 8192 5000 (readv_in 30 8192 5000 wmem_none wmem_none) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- For readv on write-only stdout fd 1, count 2 names an unreadable array at 8192. Linux v6.8+
returns -EBADF and qemu-user returns -EFAULT; the pin declines this call as `Unmodeled`.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_stdout_declines_before_import (o : outcome SyscallEffect) :
    readv_spec 1 8192 2 (readv_in 1 8192 2 wmem_none wmem_none) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For readv on write-only stdout fd 1, count 2 names an unreadable array at 8192. Linux v6.8+
returns -EBADF and qemu-user returns -EFAULT; the pin refuses the former concrete `-EBADF`
outcome.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_stdout_declines_before_import_old_answer_refuted :
    ¬ readv_spec 1 8192 2 (readv_in 1 8192 2 wmem_none wmem_none) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- …so the -EFAULT the array would have earned is refused.
rocq-twin: readv_write_only_fd_unreadable_array_is_unmodeled
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem readv_stdout_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 1 8192 2 wmem_none wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- For readv on write-only file fd 4, count 9 requests eight readable {0,0} entries and an
absent ninth at 8320. Linux v6.8+ returns -EBADF and qemu-user fails the array lock with -EFAULT; the
pin declines this call as `Unmodeled`.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_write_only_file_declines_before_the_band (o : outcome SyscallEffect) :
    readv_spec 4 8192 9 (readv_in 4 8192 9 mem_readv_eight_zero wmem_none) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For readv on write-only file fd 4, count 9 requests eight readable {0,0} entries and an
absent ninth at 8320. Linux v6.8+ returns -EBADF and qemu-user fails the array lock with -EFAULT; the
pin refuses the former concrete `-EBADF` outcome.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_write_only_file_declines_before_the_band_old_answer_refuted :
    ¬ readv_spec 4 8192 9 (readv_in 4 8192 9 mem_readv_eight_zero wmem_none) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- For readv on closed fd 30, count 9 requests eight readable {0,0} entries and an absent ninth
at 8320. Linux returns -EBADF and qemu-user returns -EFAULT; the pin declines this call as
`Unmodeled`.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_closed_fd_inside_the_band_declines (o : outcome SyscallEffect) :
    readv_spec 30 8192 9 (readv_in 30 8192 9 mem_readv_eight_zero wmem_none) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For readv on closed fd 30, count 9 requests eight readable {0,0} entries and an absent ninth
at 8320. Linux returns -EBADF and qemu-user returns -EFAULT; the pin refuses the former concrete
`-EBADF` outcome.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_closed_fd_inside_the_band_declines_old_answer_refuted :
    ¬ readv_spec 30 8192 9 (readv_in 30 8192 9 mem_readv_eight_zero wmem_none) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- Readv on closed fd 30 requests count 9 from eight readable {0,0} entries at 8192 and an
absent ninth. Linux returns -EBADF and qemu-user returns -EFAULT, so the dispatcher pin refuses
the concrete -EBADF outcome.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_closed_fd_inside_the_band_old_ebadf_refuted :
    ¬ syscall_spec (readv_in 30 8192 9 mem_readv_eight_zero wmem_none) read_model (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- For readv on pipe write end fd 15, count 2 selects {4096,2},{4098,3}, with five writable
destination bytes. The pin declines this call as `Unmodeled`.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed --expect-unmodeled readv -- wrongend-readv -/
theorem readv_pipe_write_end_declines (o : outcome SyscallEffect) :
    readv_spec 15 8192 2 (readv_in 15 8192 2 iov_2_3 (wmem_first 5)) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For readv on pipe write end fd 15, count 2 selects {4096,2},{4098,3}, with five writable
destination bytes. The pin refuses the former concrete `-EBADF` outcome.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed --expect-unmodeled readv -- wrongend-readv -/
theorem readv_pipe_write_end_declines_old_answer_refuted :
    ¬ readv_spec 15 8192 2 (readv_in 15 8192 2 iov_2_3 (wmem_first 5)) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- Readv on pipe write end fd 15 uses count 2 and {4096,2},{4098,3}, with five writable
destination bytes. The dispatcher pin refuses a concrete -EINVAL outcome because the nonempty
first entry makes this shape decline.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed --expect-unmodeled readv -- wrongend-readv -/
theorem readv_pipe_write_end_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 15 8192 2 iov_2_3 (wmem_first 5)) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- For readv on pipe write end fd 15, count 0 leaves the unreadable array at 8192 unused. Linux
returns -EBADF and qemu-user returns 0; the pin declines this call as `Unmodeled`.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed --expect-unmodeled readv -- wrongend0-readv -/
theorem readv_pipe_write_end_count_zero_declines (o : outcome SyscallEffect) :
    readv_spec 15 8192 0 (readv_in 15 8192 0 wmem_none wmem_none) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For readv on pipe write end fd 15, count 0 leaves the unreadable array at 8192 unused. Linux
returns -EBADF and qemu-user returns 0; the pin refuses the former concrete `-EBADF` outcome.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed --expect-unmodeled readv -- wrongend0-readv -/
theorem readv_pipe_write_end_count_zero_declines_old_answer_refuted :
    ¬ readv_spec 15 8192 0 (readv_in 15 8192 0 wmem_none wmem_none) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- Readv on pipe write end fd 15 with count 0 and an unused unreadable array returns -EBADF in
Linux and 0 in qemu-user. The dispatcher pin refuses the concrete zero return because the shape
declines.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed --expect-unmodeled readv -- wrongend0-readv -/
theorem readv_pipe_write_end_count_zero_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 15 8192 0 wmem_none wmem_none) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- For readv on write-only /dev/null fd 9, count 1 selects {4096,1}, with that destination byte
writable. The pin declines this call as `Unmodeled`.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_devnull_write_only_declines (o : outcome SyscallEffect) :
    readv_spec 9 8192 1 (readv_in 9 8192 1 mem_readv_iov wmem_readv_one) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For readv on write-only /dev/null fd 9, count 1 selects {4096,1}, with that destination byte
writable. The pin refuses the former concrete `-EBADF` outcome.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_devnull_write_only_declines_old_answer_refuted :
    ¬ readv_spec 9 8192 1 (readv_in 9 8192 1 mem_readv_iov wmem_readv_one) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- The fd is narrowed to 32 bits by the table: fd 2^32 + 26 is fd 26, a
second descriptor onto channel 0, and reads standard input (here at end
of input: 0, with the one descriptor's ledger).
kernel: fs/read_write.c:do_readv@v6.18.46 -/
theorem readv_fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (readv_in (Z_to_bv 64 (2 ^ 32 + 26)) 8192 1 mem_readv_iov wmem_readv_one) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- Readv on closed fd 30 uses count 1 and a readable {0,0} entry at 8192. The empty first entry
lets qemu-user reach the host fd lookup, so both implementations return -EBADF and the pin
accepts exactly that outcome.
probe: testing/syscall-check/tests/readv_spec.c#conform -- badfd -/
theorem readv_closed_fd_empty_first_entry_is_ebadf (o : outcome SyscallEffect) :
    readv_spec 30 8192 1 (SyscallInput.mkInput 65 [30, 8192, 1, 0, 0, 0] mem_readv_eight_zero wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- Readv on closed fd 30 uses count 1 and a readable {0,0} entry at 8192, letting both
implementations reach -EBADF. The pin refuses a zero-return outcome for this shared-error
control.
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin abc --mutate readv:ret=0 -- badfd -/
theorem readv_closed_fd_empty_first_entry_zero_refuted (m' : Model) (evs : List event) :
    ¬ readv_spec 30 8192 1 (SyscallInput.mkInput 65 [30, 8192, 1, 0, 0, 0] mem_readv_eight_zero wmem_none) read_model
      (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- Writev on closed fd 30 uses count 1 and a readable {0,0} entry at 8192. The empty first
entry lets qemu-user reach the host fd lookup, so both implementations return -EBADF and the pin
accepts exactly that outcome.
probe: testing/syscall-check/tests/writev_adversarial.c#conform -- badfdempty -/
theorem writev_closed_fd_empty_first_entry_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 30 8192 1 (SyscallInput.mkInput 66 [30, 8192, 1, 0, 0, 0] mem_readv_eight_zero wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  unfold writev_spec
  rw_norm

/-- Writev on closed fd 30 uses count 1 and a readable {0,0} entry at 8192, letting both
implementations reach -EBADF. The pin refuses a zero-return outcome for this shared-error
control.
probe: testing/syscall-check/tests/writev_adversarial.c#reject --mutate writev:ret=0 -- badfdempty -/
theorem writev_closed_fd_empty_first_entry_zero_refuted (m' : Model) (evs : List event) :
    ¬ writev_spec 30 8192 1 (SyscallInput.mkInput 66 [30, 8192, 1, 0, 0, 0] mem_readv_eight_zero wmem_none) read_model
      (Ok (mkEffect 0 [] []) m' evs) := by
  unfold writev_spec
  rw_refute

/-! ## The count: raw disagreement gate, then narrowed import and allocation band

`import_iovec` takes the count through `unsigned nr_segs`
(lib/iov_iter.c:1424-1425, v6.18.46), so Linux imports its low 32 bits.
The spec first declines raw counts above `IOV_MAX` whose low word fits,
because QEMU 11.1.1 checks the raw count in linux-user/syscall.c
`lock_iovec`. On the remaining shapes, a narrowed count of one takes `__import_iovec_ubuf` (:1360-1361)
and never meets the `UIO_MAXIOV` test; zero copies nothing
(`iovec_from_user`, :1304-1305); above `IOV_MAX` is -EINVAL before a
descriptor is read (:1306-1307); and 9 through `IOV_MAX` allocate the
array with `kmalloc_array` (:1308-1312), whose -ENOMEM the model does not
represent — that band is declined. -/

/-- Readv on stdin fd 0 at EOF uses count 2^32+1 and one readable {4096,1} entry at 8192, with
no writable destination. Linux narrows the count and returns 0, while qemu-user returns -EINVAL,
so the pin declines the call.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv --stdin hello -- rawhigh -/
theorem readv_iovcnt_wide_count_declines (o : outcome SyscallEffect) :
    readv_spec 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Readv on stdin fd 0 at EOF uses count 2^32+1 and {4096,1} at 8192, with no writable
destination. Linux returns 0 after narrowing the count and qemu-user returns -EINVAL; the pin
refuses the former zero outcome with its descriptor-read ledger.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv --stdin hello -- rawhigh -/
theorem readv_iovcnt_wide_count_declines_old_answer_refuted :
    ¬ readv_spec 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none) read_model
      (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) read_model []) := by
  rw_refute

/-- An ordinary count of one remains the modeled EOF return of zero.
rocq-twin: readv_wide_iovcnt_is_unmodeled
kernel: lib/iov_iter.c:import_iovec@v6.18.46 -/
theorem readv_count_one_at_eof_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 1 mem_readv_iov wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- Readv on stdin fd 0 at EOF with count 2^32+1 and {4096,1} at 8192 gives Linux's narrowed-
count 0 and qemu-user's raw-count -EINVAL. The dispatcher pin refuses the concrete -EINVAL
outcome because the call declines.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv --stdin hello -- rawhigh -/
theorem readv_raw_count_over_max_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- A count of two on the one-descriptor array reaches the unreadable
second descriptor: -EFAULT, both descriptor reads in the ledger.
rocq-twin: readv_wide_iovcnt_is_unmodeled
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem readv_second_descriptor_unreadable_is_efault (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 2 mem_readv_iov wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- A zero there is refused, testing the ordinary descriptor-count
boundary.  (`readv_spec.c`'s `mem-hide:a1:16` reject hides the FIRST
descriptor; no probe hides the second alone.)
rocq-twin: readv_wide_iovcnt_is_unmodeled
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem readv_second_descriptor_unreadable_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 mem_readv_iov wmem_none) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- On this readable fd a count of zero accesses neither the array nor
the destination: zero, no ledger, even on an unreadable array pointer.
probe: testing/syscall-check/tests/readv_spec.c#conform --stdin abc -- cnt0 -/
theorem readv_count_zero_is_zero (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 0 wmem_none wmem_none) (stdin_model (hello b c d e f)) o ↔
      o = Ok (mkEffect 0 [] []) (stdin_model (hello b c d e f)) [] := by
  rw_norm

/-- …not -EINVAL.
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin abc --mutate readv:ret=-EINVAL -- cnt0 -/
theorem readv_count_zero_einval_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 0 wmem_none wmem_none) (stdin_model (hello b c d e f))
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- `IOV_MAX` + 1 is -EINVAL before a descriptor is read: no ledger.
probe: testing/syscall-check/tests/readv_spec.c#conform -- over -/
theorem readv_count_over_max_is_einval (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 1025 mem_readv_eight_zero wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …not -EFAULT, though the array is mostly unreadable.
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=-EFAULT -- over -/
theorem readv_count_over_max_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 1025 mem_readv_eight_zero wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- A count of -1 is 2^32 - 1 after the narrowing: over `IOV_MAX`,
-EINVAL.
probe: testing/syscall-check/tests/readv_spec.c#conform -- negcnt -/
theorem readv_count_minus_one_is_einval (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 (Z_to_bv 64 (2 ^ 64 - 1)) mem_readv_eight_zero wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- Eight zero-length descriptors stay on the stack: judged, 0, all eight
in the ledger.
rocq-twin: readv_heap_iovec_boundary_fails_closed
probe: testing/syscall-check/tests/readv_spec.c#conform -- heap8 -/
theorem readv_eight_descriptors_are_judged (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 8 mem_readv_eight_zero wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
                            (8288, 16), (8304, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- …and -ENOMEM is not among the answers on the stack path.
rocq-twin: readv_heap_iovec_boundary_fails_closed
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem readv_eight_descriptors_enomem_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 8 mem_readv_eight_zero wmem_none) read_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  rw_refute

/-- Nine need the allocation: the model DECLINES, whatever the kernel
answers.
rocq-twin: readv_heap_iovec_boundary_fails_closed
probe: testing/syscall-check/tests/readv_spec.c#fail-closed -- heap9 -/
theorem readv_nine_descriptors_decline (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 9 mem_readv_eight_zero wmem_none) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …so neither the 0 the stack path would give…
rocq-twin: readv_heap_iovec_boundary_fails_closed
probe: testing/syscall-check/tests/readv_spec.c#fail-closed -- heap9 -/
theorem readv_nine_descriptors_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 9 mem_readv_eight_zero wmem_none) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …nor the -ENOMEM that is the decline's reason is certified.
rocq-twin: readv_heap_iovec_boundary_fails_closed
probe: testing/syscall-check/tests/readv_spec.c#fail-closed -- heap9 -/
theorem readv_nine_descriptors_enomem_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 9 mem_readv_eight_zero wmem_none) read_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  rw_refute

/-- The band reaches `IOV_MAX` itself.
rocq-twin: readv_heap_iovec_boundary_fails_closed
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem readv_iov_max_descriptors_decline (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 1024 mem_readv_eight_zero wmem_none) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-- A raw 2^32 + 9 declines at the leading wide-count gate. An ordinary
count of nine separately declines at the allocation band.
rocq-twin: readv_heap_iovec_boundary_fails_closed
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- rawheap -/
theorem readv_raw_heap_count_declines (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 9)) mem_readv_eight_zero wmem_none) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …with qemu-user's raw-count -EINVAL undescribed rather than admitted.
rocq-twin: readv_heap_iovec_boundary_fails_closed
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --mutate readv:ret=-EINVAL -- rawheap -/
theorem readv_raw_heap_count_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 9)) mem_readv_eight_zero wmem_none) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-! ## The import: what `__import_iovec` says before a byte moves

`copy_iovec_from_user` (lib/iov_iter.c:1260-1290, v6.18.46) loads
`iov_len` (:1272) and `iov_base` (:1273) of each descriptor under one
`user_access_begin` over the array (:1265) and tests `len < 0` only after
both loads (:1276-1279); `__import_iovec` then applies `access_ok` to
every entry's UNCAPPED length (:1377-1392, -EFAULT at :1384).  The
single-descriptor path is different: `import_ubuf` (:1433-1441) caps to
`MAX_RW_COUNT` FIRST (:1435-1436) and range-checks the CAPPED length
(:1437-1438). -/

/-- An unreadable descriptor array is -EFAULT with an empty ledger: the
first sixteen-byte fetch is attempted and recorded, nothing else.
probe: testing/syscall-check/tests/readv_spec.c#conform --stdin hello --mutate readv:mem-hide:a1:16,ret=-EFAULT,drop-writes -- chan -/
theorem readv_unreadable_array_is_efault (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 2 wmem_none (wmem_first 5)) (stdin_model (hello b c d e f)) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) (stdin_model (hello b c d e f)) [] := by
  rw_norm

/-- A readable negative length beside an UNREADABLE base is -EFAULT, not
-EINVAL: the base load faults before the sign is tested, and the ledger
is the one attempted descriptor.
rocq-twin: readv_unreadable_base_faults_before_the_sign_test
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem readv_unreadable_base_faults_before_the_sign_test (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 2 mem_readv_len_only wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- …-EINVAL refused there.
rocq-twin: readv_unreadable_base_faults_before_the_sign_test
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:mem-hide:a1:8 -- neglen -/
theorem readv_unreadable_base_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 mem_readv_len_only wmem_none) read_model
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) m' evs) := by
  rw_refute

/-- A length negative as `ssize_t` beside a readable base is -EINVAL, the
ledger naming the one descriptor read: `copy_iovec_from_user` stops at
the offending entry (lib/iov_iter.c:1276-1279, v6.18.46).
probe: testing/syscall-check/tests/readv_spec.c#conform -- neglen -/
theorem readv_negative_length_is_einval (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) read_model [] := by
  rw_norm

/-- …not -EFAULT.
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=-EFAULT -- neglen -/
theorem readv_negative_length_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none) read_model
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw_refute

/-- THE SINGLE-DESCRIPTOR PATH CAPS BEFORE `access_ok`: the first entry,
`MAX_RW_COUNT` below the top of the address space and one byte longer,
imports at count 1 (the capped range ends AT the limit) and, with
standard input at end of input, answers 0.
rocq-twin: readv_single_iovec_caps_before_access_ok
probe: testing/syscall-check/tests/readv_spec.c#conform -- cap-order 1 -/
theorem readv_single_descriptor_caps_before_access_ok (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 1 mem_readv_cap_order wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- …so a harness that range-checked the raw length is refused.
rocq-twin: readv_single_iovec_caps_before_access_ok
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=-EFAULT -- cap-order 1 -/
theorem readv_single_descriptor_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 1 mem_readv_cap_order wmem_none) read_model
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw_refute

/-- THE ARRAY PATH CHECKS THE RAW LENGTH: the same first entry at count 2
runs one byte past the limit and is -EFAULT at import, both descriptors
read.
rocq-twin: readv_single_iovec_caps_before_access_ok
probe: testing/syscall-check/tests/readv_spec.c#conform -- cap-order 2 -/
theorem readv_array_path_checks_the_raw_length (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 2 mem_readv_cap_order wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- …never 0, however empty standard input is.
rocq-twin: readv_single_iovec_caps_before_access_ok
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=0 -- cap-order 2 -/
theorem readv_array_path_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 mem_readv_cap_order wmem_none) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-! ## Standard input through a vector

The channel rule is `read`'s (`stdin_delivers_a_prefix_iff` above): any
nonempty prefix of the input of at most the aggregate, one `ReadEv` per
byte on channel 0, the stream advanced past exactly them — scattered
across the capped vector in order, `iterate_iovec` skipping a segment
with nothing left (include/linux/iov_iter.h:51, v6.18.46).  The vector
here is `{4096,2},{4098,3}`, the input five symbolic bytes.

THE `iff` OVER THE CHOICE is `readv_stdin_delivers_a_prefix_iff`, in the
subsection closing the readv pins, stated on the ledger: `read`'s delivery `iff` names
the one write `(buf, bs)`, while readv's writes are `scatter_iovecs … bs`,
a match on the chosen `bs` that no rewrite reduces while `bs` is a
variable — so the choice is moved onto the ledger first
(`choose_scatter_eq`, above), and the `iff` quantifies over the
writes with the scatter equation as its last conjunct.  The instances
(whole, short, exact) and the refutations (0, over the input, over the
vector, wrong bytes, wrong scatter, input not consumed) pin the same set
from both sides in shapes a reader can check by eye.  The arm states no
length bound of its own: the aggregate bounds a delivery only through
the scatter, which has no writes for bytes past the last segment, and
the two over-the-vector refutations are the pins of that. -/

/-- THE DELIVERY, whole: five bytes, 2 then 3, standard input left at end
of input, five events on channel 0, both descriptors in the ledger.
rocq-twin: partial_destination_on_a_pipe_declines
probe: testing/syscall-check/tests/readv_spec.c#conform --stdin hello -- chan -/
theorem readv_stdin_full_delivery (b c d e f : byte) :
    syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (hello b c d e f))
      (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 5 [(4096, [b, c]), (4098, [d, e, f])] []))
          (stdin_model IEof) [ReadEv 0 b, ReadEv 0 c, ReadEv 0 d, ReadEv 0 e, ReadEv 0 f]) := by
  rw_norm

/-- A SHORT delivery is real: one byte into the first segment, four left.
`anon_pipe_read` returns what the pipe held when it ran empty (`if (ret)
break`, fs/pipe.c:372, v6.18.46), so a writer one byte ahead of the reader
is a one-byte readv; the probe's `ret=4,trunc-writes:4 -- chan` case is
the same admission at four bytes.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem readv_stdin_short_delivery (b c d e f : byte) :
    syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (hello b c d e f))
      (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 1 [(4096, [b])] []))
          (stdin_model (ICons c (ICons d (ICons e (ICons f IEof))))) [ReadEv 0 b]) := by
  rw_norm

/-- Three bytes: the first segment filled, one into the second — the
segment boundary crossed by one buffer's copy (`copy_page_to_iter` over
the iterator, fs/pipe.c:343, v6.18.46).
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem readv_stdin_three_byte_delivery (b c d e f : byte) :
    syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (hello b c d e f))
      (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 3 [(4096, [b, c]), (4098, [d])] []))
          (stdin_model (ICons e (ICons f IEof))) [ReadEv 0 b, ReadEv 0 c, ReadEv 0 d]) := by
  rw_norm

/-- A 0 with input waiting is refused.
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin hello --mutate readv:ret=0,drop-writes -- chan -/
theorem readv_stdin_zero_with_input_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- The return is the delivered count: four claimed for five stored is
refused.
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin hello --mutate readv:ret=4 -- chan -/
theorem readv_stdin_wrong_count_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 4 [(4096, [b, c]), (4098, [d, e, f])] [])) m' evs) := by
  rw_refute

/-- The scatter is canonical: five bytes in one segment of two is refused.
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin hello --mutate readv:split-writes -- chan -/
theorem readv_stdin_wrong_scatter_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 5 [(4096, [b, c, d, e, f])] [])) m' evs) := by
  rw_refute

/-- The bytes are the input's: "he" queued, "hh" delivered is refused.
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin hello --mutate readv:poison-writes:57 -- chan -/
theorem readv_stdin_wrong_bytes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (hello 104 101 108 108 111))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [104, 104])] [])) m' evs) := by
  rw_refute

/-- OVER THE VECTOR is refused: two bytes delivered through the one-byte
vector `{4096,1}`, with five bytes waiting and the byte past the vector
writable, so the room is the only bound that can refuse them.
`anon_pipe_read` copies at most `total_len = iov_iter_count(to)`
(fs/pipe.c:271, v6.18.46), cutting a larger buffer to it (`chars =
total_len`, :327-334).  The arm chooses the bytes with no length bound of
its own; what refuses these is the scatter's `none` for bytes past the
last segment (`pin_scatter_iovecs_over_capacity_is_none`).
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem readv_stdin_over_vector_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 1 mem_readv_iov (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (with_copyins [(8192, 16)] (mkEffect 2 [(4096, [b, c])] [])) m' evs) := by
  rw_refute

/-- …and so is a count of two with only the byte that fits written: the
answer of a scatter that dropped what it could not place instead of
refusing it.  The count is what the copy moved (`ret += chars`,
fs/pipe.c:349, v6.18.46), and with one byte of room it moved one.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem readv_stdin_over_vector_count_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 1 mem_readv_iov (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (with_copyins [(8192, 16)] (mkEffect 2 [(4096, [b])] [])) m' evs) := by
  rw_refute

/-- OVER THE INPUT is refused: three bytes delivered of the two waiting,
with room for five.  `anon_pipe_read` returns what the pipe held once it
runs empty (`if (ret) break`, fs/pipe.c:372, v6.18.46), and there is no
third byte for it to copy.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem readv_stdin_over_input_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (ICons b (ICons c IEof)))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 3 [(4096, [b, c]), (4098, [b])] [])) m' evs) := by
  rw_refute

/-- The ledger is the import's: a delivery that forgot the descriptor
reads is refused.
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin hello --mutate readv:drop-copyins -- chan -/
theorem readv_stdin_dropped_ledger_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (mkEffect 5 [(4096, [b, c]), (4098, [d, e, f])] []) m' evs) := by
  rw_refute

/-- …and one that reads a third descriptor is refused: the import stops
after the count's worth.
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin hello --mutate readv:drop-copyins,smuggle-copyin:a1:16,smuggle-copyin:a1+16:16,smuggle-copyin:a1+32:16 -- chan -/
theorem readv_stdin_third_descriptor_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (with_copyins [(8192, 16), (8208, 16), (8224, 16)] (mkEffect 5 [(4096, [b, c]), (4098, [d, e, f])] [])) m' evs) := by
  rw_refute

/-- No events, or events on another channel, are refused.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem readv_stdin_no_events_rejected (b c d e f : byte) (m' : Model) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (hello b c d e f))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 5 [(4096, [b, c]), (4098, [d, e, f])] [])) m' []) := by
  rw_refute

/-- Not one destination byte writable: -EFAULT, nothing consumed.
probe: testing/syscall-check/tests/readv_spec.c#conform --stdin hello --mutate readv:wmem-none,ret=-EFAULT,drop-writes -- chan -/
theorem readv_stdin_unwritable_is_efault (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 2 iov_2_3 wmem_none) (stdin_model (hello b c d e f)) o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] []))
             (stdin_model (hello b c d e f)) [] := by
  rw_norm

/-- …so the five-byte delivery is refused there.
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin hello --mutate readv:wmem-none -- chan -/
theorem readv_stdin_unwritable_delivery_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 wmem_none) (stdin_model (hello b c d e f))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 5 [(4096, [b, c]), (4098, [d, e, f])] [])) m' evs) := by
  rw_refute

/-- THE PARTIAL DESTINATION DECLINES: four of the five destination bytes
writable, five queued.  Linux answers -EFAULT with four stored if the
five arrived in one pipe buffer (`anon_pipe_read`'s page copy fails the
whole buffer, fs/pipe.c:343-348, v6.18.46) and a count of whole buffers
otherwise, so the delivery, the -EFAULT and the short read are all
outside what the model will say — a coverage gap, declined.  (The
probe's `fail-closed … wmem-hide:a1+35:1 -- file` case is the file's
instance of the same decline; readv_spec.c has no channel one.)
rocq-twin: partial_destination_on_a_pipe_declines
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem readv_stdin_partial_destination_declines (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 4)) (stdin_model (hello b c d e f)) o ↔
      o = Unmodeled := by
  rw_norm

/-- …the four-byte short read among the refused.
rocq-twin: partial_destination_on_a_pipe_declines
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem readv_stdin_partial_destination_short_read_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 4)) (stdin_model (hello b c d e f))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 4 [(4096, [b, c]), (4098, [d, e])] [])) m' evs) := by
  rw_refute

/-- End of input is 0, sticky, the destination never inspected.
probe: testing/syscall-check/tests/readv_spec.c#conform --stdin hello -- chaneof -/
theorem readv_stdin_at_eof_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 2 iov_2_3 wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- …a later delivery refused.
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin hello --mutate readv#2:ret=1,smuggle-write:a1+32:1 -- chaneof -/
theorem readv_stdin_at_eof_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 wmem_none) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 1 [(4096, [1])] [])) m' evs) := by
  rw_refute

/-- A zero aggregate — two zero-length entries — is 0 before the stream
is consulted, with input waiting and nothing writable.
probe: testing/syscall-check/tests/readv_spec.c#conform --stdin abc -- allzero -/
theorem readv_stdin_zero_aggregate_is_zero (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none) (stdin_model (hello b c d e f)) o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) (stdin_model (hello b c d e f)) [] := by
  rw_norm

/-- …not -EFAULT for the NULL base: a zero-length entry's base is never
touched.
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin abc --mutate readv:ret=-EFAULT -- allzero -/
theorem readv_stdin_zero_aggregate_efault_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none) (stdin_model (hello b c d e f))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw_refute

/-- A zero-length NULL entry ahead of a real one is skipped: the byte
lands in the second segment.
probe: testing/syscall-check/tests/readv_spec.c#conform --stdin abc -- zero -/
theorem readv_stdin_zero_length_entry_skipped (b c d e f : byte) :
    syscall_spec (readv_in 0 8192 2 (mem_iov_pair 0 0 4096 1) (wmem_first 1)) (stdin_model (hello b c d e f))
      (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 1 [(4096, [b])] []))
          (stdin_model (ICons c (ICons d (ICons e (ICons f IEof))))) [ReadEv 0 b]) := by
  rw_norm

/-- A single 2^62-byte descriptor delivers the one queued byte: the cap
happens before `access_ok`, and the delivery is bounded by the input.
rocq-twin: readv_huge_len_delivers_one_byte_without_unary_expansion
probe: testing/syscall-check/tests/readv_spec.c#conform --stdin x -- hugechan -/
theorem readv_huge_descriptor_delivers_the_input (b : byte) :
    syscall_spec (readv_in 0 8192 1 mem_readv_huge wmem_readv_one) (stdin_model (ICons b IEof))
      (Ok (with_copyins [(8192, 16)] (mkEffect 1 [(4096, [b])] [])) (stdin_model IEof) [ReadEv 0 b]) := by
  rw_norm

/-- …and a harness that range-checked the raw length is refused.
rocq-twin: readv_huge_len_delivers_one_byte_without_unary_expansion
probe: testing/syscall-check/tests/readv_spec.c#reject --stdin x --mutate readv:ret=-EFAULT,drop-writes -- hugechan -/
theorem readv_huge_descriptor_efault_rejected (b : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 1 mem_readv_huge wmem_readv_one) (stdin_model (ICons b IEof))
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw_refute

/-! ## Sockets through a vector

Nothing about the vector reaches the protocol: `tcp_recvmsg_locked`
(net/ipv4/tcp.c:2634, v6.18.46) sees an `iov_iter` and its total, so a
socket readv answers as a socket read of the same aggregate does
(`fresh_socket_is_enotconn` … `socket_delivers_a_prefix_iff` above), the
bytes scattered as standard input's are. -/

/-- A fresh socket is -ENOTCONN, both descriptors in the ledger.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_fresh_socket_is_enotconn (o : outcome SyscallEffect) :
    syscall_spec (readv_in 10 8192 2 iov_2_3 (wmem_first 5)) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOTCONN) [] [])) read_model [] := by
  rw_norm

/-- …never 0: a fresh socket does not report end of stream.
probe: testing/syscall-check/tests/socket_rw.c#reject --mutate readv#1:ret=0 -- rv -/
theorem readv_fresh_socket_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 10 8192 2 iov_2_3 (wmem_first 5)) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- A zero aggregate on a fresh socket is 0 before the protocol is asked
(`vfs_readv`'s `if (!tot_len) goto out`, fs/read_write.c:1009-1011).
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem readv_fresh_socket_zero_aggregate_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 10 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- …-ENOTCONN refused there.
probe: testing/syscall-check/tests/socket_rw.c#reject --mutate readv#2:ret=-ENOTCONN -- rv -/
theorem readv_fresh_socket_zero_aggregate_enotconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 10 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOTCONN) [] [])) m' evs) := by
  rw_refute

/-- …and a count of zero likewise.
probe: testing/syscall-check/tests/socket_rw.c#reject --mutate readv#3:ret=-ENOTCONN -- rv -/
theorem readv_fresh_socket_count_zero_enotconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 10 8192 0 wmem_none wmem_none) read_model
        (Ok (mkEffect (errno_ret ENOTCONN) [] []) m' evs) := by
  rw_refute

/-- Bound and listening sockets are -ENOTCONN too.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_bound_socket_is_enotconn (o : outcome SyscallEffect) :
    syscall_spec (readv_in 11 8192 2 iov_2_3 (wmem_first 5)) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOTCONN) [] [])) read_model [] := by
  rw_norm

/-- kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_listening_socket_is_enotconn (o : outcome SyscallEffect) :
    syscall_spec (readv_in 12 8192 2 iov_2_3 (wmem_first 5)) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOTCONN) [] [])) read_model [] := by
  rw_norm

/-- End of stream is 0, the destination untouched.
probe: testing/syscall-check/tests/socket_read_peer.c#conform --peer 68656c6c6f -- readv -/
theorem readv_fin_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 20 8192 2 iov_2_3 wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- …never a byte.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate readv#2:ret=1 --peer 68656c6c6f -- readv -/
theorem readv_fin_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 20 8192 2 iov_2_3 (wmem_first 5)) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 1 [(4096, [104])] [])) m' evs) := by
  rw_refute

/-- A pending reset is -ECONNRESET once, the socket moved to `SkReset`.
probe: testing/syscall-check/tests/socket_read_peer.c#conform --peer 6869:rst -- readv-rst -/
theorem readv_rst_is_connreset_once (o : outcome SyscallEffect) :
    syscall_spec (readv_in 21 8192 2 iov_2_3 (wmem_first 5)) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ECONNRESET) [] []))
             (with_fds (fd_insert read_fds 21 (.FdSocket (.SkReset peer_a 7))) read_model) [] := by
  rw_norm

/-- …not 0…
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate readv#2:ret=0 --peer 6869:rst -- readv-rst -/
theorem readv_rst_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 21 8192 2 iov_2_3 (wmem_first 5)) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- …and not left pending.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate readv#3:ret=-ECONNRESET --peer 6869:rst -- readv-rst -/
theorem readv_rst_left_pending_rejected (evs : List event) :
    ¬ syscall_spec (readv_in 21 8192 2 iov_2_3 (wmem_first 5)) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ECONNRESET) [] [])) read_model evs) := by
  rw_refute

/-- A reported error reads as 0 afterwards.
probe: testing/syscall-check/tests/socket_read_peer.c#conform --peer 6869:rst -- readv-rst -/
theorem readv_reset_socket_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 13 8192 2 iov_2_3 (wmem_first 5)) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- A pending timeout is -ETIMEDOUT once, the socket moved to `SkReset`:
`tcp_write_err` stores `sk_err_soft ? : ETIMEDOUT` when the retransmit
timer gives up (net/ipv4/tcp_timer.c:76-80, v6.18.46) and `sock_error`
hands it out once, clearing it (include/net/sock.h, v6.18.46), through
`tcp_recvmsg_locked`'s `sk->sk_err` arm.
kernel: net/ipv4/tcp_timer.c:tcp_write_err; include/net/sock.h:sock_error@v6.18.46 -/
theorem readv_timedout_is_etimedout_once (o : outcome SyscallEffect) :
    syscall_spec (readv_in 22 8192 2 iov_2_3 (wmem_first 5)) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ETIMEDOUT) [] []))
             (with_fds (fd_insert read_fds 22 (.FdSocket (.SkReset peer_a 7))) read_model) [] := by
  rw_norm

/-- …-ECONNRESET refused for it.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_timedout_connreset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 22 8192 2 iov_2_3 (wmem_first 5)) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ECONNRESET) [] [])) m' evs) := by
  rw_refute

/-- THE DELIVERY on a connected socket: both queued bytes, into the first
segment, the FIN left at the head, two events on the connection's
channel.
probe: testing/syscall-check/tests/socket_read_peer.c#conform --peer 68656c6c6f -- readv -/
theorem readv_socket_full_delivery (b c : byte) :
    syscall_spec (readv_in 25 8192 2 iov_2_3 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
      (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [b, c])] []))
          (with_fds (fd_insert (socket_fds (NCons b (NCons c NFin))) 25
              (.FdSocket (.SkConnected peer_a 7 NFin)))
            (socket_model (NCons b (NCons c NFin))))
          [ReadEv 7 b, ReadEv 7 c]) := by
  rw_norm

/-- A short delivery: one byte, one left.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_socket_short_delivery (b c : byte) :
    syscall_spec (readv_in 25 8192 2 iov_2_3 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
      (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 1 [(4096, [b])] []))
          (with_fds (fd_insert (socket_fds (NCons b (NCons c NFin))) 25
              (.FdSocket (.SkConnected peer_a 7 (NCons c NFin))))
            (socket_model (NCons b (NCons c NFin))))
          [ReadEv 7 b]) := by
  rw_norm

/-- The delivery that fills its vector: one byte of room and two queued,
and exactly the byte that fits is delivered, the second staying queued.
`tcp_recvmsg_locked` copies `used = min(skb->len - offset, len)`
(net/ipv4/tcp.c:2794-2796, v6.18.46) and leaves its loop once `len`
reaches 0 (`len -= used`, :2857; `while (len > 0)`, :2890), so a delivery
of exactly the room is real.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_socket_fills_the_vector (b c : byte) :
    syscall_spec (readv_in 25 8192 1 mem_readv_iov wmem_readv_one) (socket_model (NCons b (NCons c NFin)))
      (Ok (with_copyins [(8192, 16)] (mkEffect 1 [(4096, [b])] []))
          (with_fds (fd_insert (socket_fds (NCons b (NCons c NFin))) 25
              (.FdSocket (.SkConnected peer_a 7 (NCons c NFin))))
            (socket_model (NCons b (NCons c NFin))))
          [ReadEv 7 b]) := by
  rw_norm

/-- …and not more than the room: both queued bytes through the same
one-byte vector are refused, the byte past it writable.  `used` is cut to
`len` (net/ipv4/tcp.c:2795-2796, v6.18.46), and `len` is what the vector
holds, `msg_data_left(msg)` as `sock_recvmsg_nosec` passes it
(net/socket.c:1082, v6.18.46).  As on standard input, the scatter's
`none` for bytes past the last segment is what refuses them.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_socket_over_vector_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 25 8192 1 mem_readv_iov (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
        (Ok (with_copyins [(8192, 16)] (mkEffect 2 [(4096, [b, c])] [])) m' evs) := by
  rw_refute

/-- …and no delivery of nothing: with a byte queued and room for it,
`tcp_recvmsg_locked` copies at least that byte before its `len` test
(`found_ok_skb`, net/ipv4/tcp.c:2792-2857, v6.18.46); a 0 answer is
`copied == 0`, which the queued byte forbids.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_socket_zero_with_queue_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 25 8192 2 iov_2_3 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- The bytes are the peer's.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate readv#1:poison-writes:41 --peer 68656c6c6f -- readv -/
theorem readv_socket_wrong_bytes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 25 8192 2 iov_2_3 (wmem_first 5)) (socket_model (NCons 104 (NCons 105 NFin)))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [65, 65])] [])) m' evs) := by
  rw_refute

/-- The scatter is canonical here too: the peer's two bytes, one in each
segment, are refused, the bytes right and their placement wrong.
`tcp_recvmsg_locked` (net/ipv4/tcp.c:2822, v6.18.46) copies through
`skb_copy_datagram_msg` (include/linux/skbuff.h:4214, v6.18.46) into the
message's iterator, and `iterate_iovec` (include/linux/iov_iter.h:41-69,
v6.18.46) leaves a segment only once
`skip` reaches its `iov_len`, so two bytes fill the first segment of two.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem readv_socket_wrong_scatter_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 25 8192 2 iov_2_3 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [b]), (4098, [c])] [])) m' evs) := by
  rw_refute

/-- Over the queue is refused: three delivered of two queued.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_socket_over_queue_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 25 8192 2 iov_2_3 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 3 [(4096, [b, c]), (4098, [b])] [])) m' evs) := by
  rw_refute

/-- Events on standard input's channel for a socket delivery are refused.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_socket_event_on_stdin_channel_rejected (b c : byte) (m' : Model) :
    ¬ syscall_spec (readv_in 25 8192 2 iov_2_3 (wmem_first 5)) (socket_model (NCons b (NCons c NFin)))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [b, c])] [])) m' [ReadEv 0 b, ReadEv 0 c]) := by
  rw_refute

/-- Not one destination byte writable: -EFAULT, the script untouched.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_socket_unwritable_is_efault (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (readv_in 25 8192 2 iov_2_3 wmem_none) (socket_model (NCons b (NCons c NFin))) o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] []))
             (socket_model (NCons b (NCons c NFin))) [] := by
  rw_norm

/-- Only the first destination byte writable, two queued: declined.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_socket_partial_destination_declines (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (readv_in 25 8192 2 iov_2_3 (wmem_first 1)) (socket_model (NCons b (NCons c NFin))) o ↔
      o = Unmodeled := by
  rw_norm

/-! ## /dev/null, /dev/urandom, a pipe's read end

`read_iter_null` (drivers/char/mem.c:424-427, v6.18.46) returns 0 through
`do_iter_readv_writev`, `null_fops` carrying `.read_iter` (:648): no
destination byte touched.  /dev/urandom through a vector is FAIL-CLOSED
(the Sys twin says why: derivable, not written, the census reads the
device with `read`), and so is a pipe's read end (the mirror of `writev`'s
pipe arm; the scalar arm's atomicity argument is per transfer). -/

/-- /dev/null answers 0 whatever the vector names, both descriptors in
the ledger and nothing written.
kernel: drivers/char/mem.c:read_iter_null@v6.18.46 -/
theorem readv_devnull_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 8 8192 2 iov_2_3 wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- …not -EFAULT for an unwritable destination.
kernel: drivers/char/mem.c:read_iter_null@v6.18.46 -/
theorem readv_devnull_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 8 8192 2 iov_2_3 wmem_none) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw_refute

/-- /dev/urandom through a vector declines.
kernel: drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem readv_urandom_declines (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (readv_in 24 8192 2 iov_2_3 (wmem_first 5)) (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Unmodeled := by
  rw_norm

/-- …so the two-byte delivery a real kernel gives is refused, as a
decline.
kernel: drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem readv_urandom_delivery_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 24 8192 2 iov_2_3 (wmem_first 5)) (urandom_model (ICons b (ICons c IEof)))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [b, c])] [])) m' evs) := by
  rw_refute

/-- …but a zero aggregate on it is 0, judged before the arm.
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem readv_urandom_zero_aggregate_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 24 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- A pipe's read end through a vector declines, whatever it holds.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed -- rdv -/
theorem readv_pipe_read_end_declines (o : outcome SyscallEffect) :
    syscall_spec (readv_in 14 8192 2 iov_2_3 (wmem_first 5)) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …the queue's two bytes refused, as a decline.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed --expect-unmodeled readv -- rdv3 -/
theorem readv_pipe_read_end_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 14 8192 2 iov_2_3 (wmem_first 5)) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [97, 98])] [])) m' evs) := by
  rw_refute

/-- …and a raw-count -EINVAL undescribed rather than refused there.  The
probe's count is 2^32 + 3 over three descriptors; this fixture holds two,
so the count is 2^32 + 2 — each narrows to its own array's length
(`iovcnt32`) and reaches the pipe arm's decline.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed --mutate readv:ret=-EINVAL -- rdv3 -/
theorem readv_pipe_read_end_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 14 8192 (Z_to_bv 64 (2 ^ 32 + 2)) iov_2_3 (wmem_first 5)) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-! ## A directory

`generic_read_dir` (fs/libfs.c:224-227, v6.18.46) is `return -EISDIR`,
reached through `do_loop_readv_writev` (fs/read_write.c:835) because a
directory's operations carry `.read` and no `.read_iter`: -EISDIR on the
first entry, the destination never consulted.  Everything the destination
could say was said at import. -/

/-- A directory with a nonzero aggregate is -EISDIR, nothing writable.
probe: testing/syscall-check/tests/readv_spec.c#conform --mutate readv:wmem-none -- dir -/
theorem readv_dir_is_eisdir (o : outcome SyscallEffect) :
    syscall_spec (readv_in 5 8192 2 iov_2_3 wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) read_model [] := by
  rw_norm

/-- …-EFAULT refused: an import that passed never faults on a directory.
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=-EFAULT -- dir -/
theorem readv_dir_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 5 8192 2 iov_2_3 wmem_none) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw_refute

/-- A zero-length entry then an in-range NULL base: aggregate 1, the
entries import, -EISDIR without touching NULL.
rocq-twin: readv_directory_never_consults_the_destination
probe: testing/syscall-check/tests/readv_spec.c#conform -- dirzerofirstbad -/
theorem readv_dir_never_consults_the_destination (o : outcome SyscallEffect) :
    syscall_spec (readv_in 5 8192 2 (mem_iov_pair 0 0 0 1) wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) read_model [] := by
  rw_norm

/-- …qemu-user's 0 for the zeroed later range refused…
rocq-twin: readv_directory_never_consults_the_destination
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=0 -- dirzerofirstbad -/
theorem readv_dir_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 5 8192 2 (mem_iov_pair 0 0 0 1) wmem_none) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- …and its -EFAULT too.
rocq-twin: readv_directory_never_consults_the_destination
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=-EFAULT -- dirzerofirstbad -/
theorem readv_dir_later_null_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 5 8192 2 (mem_iov_pair 0 0 0 1) wmem_none) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw_refute

/-- A writable first entry ahead of the NULL one: still -EISDIR, the
first byte never written.
rocq-twin: readv_directory_never_consults_the_destination
probe: testing/syscall-check/tests/readv_spec.c#conform -- dirlater -/
theorem readv_dir_writable_first_then_null_is_eisdir (o : outcome SyscallEffect) :
    syscall_spec (readv_in 5 8192 2 (mem_iov_pair 4096 1 0 1) wmem_readv_one) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) read_model [] := by
  rw_norm

/-- An entry whose range leaves the address space — base 1, length
`TASK_SIZE` — is -EFAULT at import, ahead of the directory.  Rocq's shape;
the probe's is a NULL base with a length of `LLONG_MAX - 1024`, failing the
same `size <= limit` test of `__access_ok` (include/asm-generic/access_ok.h:33,
v6.18.46).
rocq-twin: readv_directory_import_range_fault_beats_eisdir
probe: testing/syscall-check/tests/readv_spec.c#conform -- dirbad -/
theorem readv_dir_import_range_fault_beats_eisdir (o : outcome SyscallEffect) :
    syscall_spec (readv_in 5 8192 2 (mem_iov_pair 1 (Z_to_bv 64 TASK_SIZE) 4096 3) wmem_readv_one) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- …-EISDIR refused there.
rocq-twin: readv_directory_import_range_fault_beats_eisdir
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=-EISDIR -- dirbad -/
theorem readv_dir_import_range_fault_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 5 8192 2 (mem_iov_pair 1 (Z_to_bv 64 TASK_SIZE) 4096 3) wmem_readv_one) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) m' evs) := by
  rw_refute

/-- A zero aggregate on a directory is 0, before `generic_read_dir`.
probe: testing/syscall-check/tests/readv_spec.c#conform -- dirzero -/
theorem readv_dir_zero_aggregate_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 5 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- …-EISDIR refused for it.
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=-EISDIR -- dirzero -/
theorem readv_dir_zero_aggregate_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 5 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) m' evs) := by
  rw_refute

/-! ## A regular file

Deterministic: the file's bytes at the offset (`shmem_file_read_iter`,
mm/shmem.c:3370, v6.18.46), scattered in order, the offset advanced by
the delivery (`do_readv` writes `f_pos` back, fs/read_write.c:1082);
`rw_verify_area`'s position test (:451-478) ahead of the read. -/

/-- "abcde" at offset 0 through `{4096,2},{4098,3}`: 2 then 3, offset 5,
the ONE admitted outcome.
probe: testing/syscall-check/tests/readv_spec.c#conform -- file -/
theorem readv_file_is_deterministic (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 2 iov_2_3 (wmem_first 5)) (readv_abcde_model 0) o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 5 [(4096, [97, 98]), (4098, [99, 100, 101])] []))
             (readv_abcde_model 5) [] := by
  rw_norm

/-- The bytes are the file's.
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:poison-writes:57 -- file -/
theorem readv_file_wrong_bytes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 3 8192 2 iov_2_3 (wmem_first 5)) (readv_abcde_model 0)
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 5 [(4096, [57, 57]), (4098, [57, 57, 57])] [])) m' evs) := by
  rw_refute

/-- A file readv is never short of what the file and the vector hold.
kernel: mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem readv_file_short_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 3 8192 2 iov_2_3 (wmem_first 5)) (readv_abcde_model 0)
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [97, 98])] [])) m' evs) := by
  rw_refute

/-- The offset advances: the same delivery leaving fd 3 at 0 is refused.
kernel: fs/read_write.c:do_readv@v6.18.46 -/
theorem readv_file_offset_not_advanced_rejected (evs : List event) :
    ¬ syscall_spec (readv_in 3 8192 2 iov_2_3 (wmem_first 5)) (readv_abcde_model 0)
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 5 [(4096, [97, 98]), (4098, [99, 100, 101])] []))
            (readv_abcde_model 0) evs) := by
  rw_refute

/-- At end of file the answer is 0, the descriptor written back unmoved.
probe: testing/syscall-check/tests/readv_spec.c#conform -- file -/
theorem readv_file_at_eof_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 2 iov_2_3 wmem_none) (readv_abcde_model 5) o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) (readv_abcde_model 5) [] := by
  rw_norm

/-- Not one destination byte writable: -EFAULT, the offset unmoved.
`shmem_file_read_iter` (mm/shmem.c:3370-3488, v6.18.46) copies folio by
folio; a short copy is `error = -EFAULT` and the loop ends (:3479-3482),
and with nothing copied `retval` is 0, so the error is what returns
(:3487) and `ki_pos` has moved by the 0 bytes copied (:3475).  The
probe's `reject … readv#1:wmem-none … -- file` case reads the same
answer from the second call's offset.
kernel: mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem readv_file_unwritable_is_efault (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 2 iov_2_3 wmem_none) (readv_abcde_model 0) o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) (readv_abcde_model 0) [] := by
  rw_norm

/-- A partial destination inside a later segment declines: Linux's count
is the copy loop's rounded progress.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --mutate readv:wmem-hide:a1+35:1 -- file -/
theorem readv_file_partial_destination_declines (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 2 iov_2_3 (wmem_first 4)) (readv_abcde_model 0) o ↔
      o = Unmodeled := by
  rw_norm

/-- A ZERO-LENGTH ENTRY, THEN A BAD BASE: the entry is skipped and the
first delivered byte lands at NULL, which is not writable — -EFAULT,
nothing delivered, the offset unchanged (`shmem_file_read_iter`: `copied
= 0` on the first folio).
rocq-twin: readv_zero_prefix_then_bad_base_is_efault_on_a_file
probe: testing/syscall-check/tests/readv_spec.c#conform -- filezerofirstbad -/
theorem readv_file_zero_prefix_then_bad_base_is_efault (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 2 (mem_iov_pair 0 0 0 1) wmem_none) (readv_abcde_model 0) o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) (readv_abcde_model 0) [] := by
  rw_norm

/-- …qemu-user's 0 refused…
rocq-twin: readv_zero_prefix_then_bad_base_is_efault_on_a_file
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=0 -- filezerofirstbad -/
theorem readv_file_zero_prefix_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 3 8192 2 (mem_iov_pair 0 0 0 1) wmem_none) (readv_abcde_model 0)
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- …and -EISDIR refused on a regular file.
rocq-twin: readv_zero_prefix_then_bad_base_is_efault_on_a_file
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=-EISDIR -- filezerofirstbad -/
theorem readv_file_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 3 8192 2 (mem_iov_pair 0 0 0 1) wmem_none) (readv_abcde_model 0)
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) m' evs) := by
  rw_refute

/-- A single 2^62-byte descriptor on a one-byte file delivers the byte
and moves the offset to 1: the cap, then the file's length, bound the
delivery.
rocq-twin: readv_huge_len_delivers_one_byte_without_unary_expansion
probe: testing/syscall-check/tests/readv_spec.c#conform -- hugefile -/
theorem readv_huge_descriptor_on_a_file (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 1 mem_readv_huge wmem_readv_one) (readv_x_model 0) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 1 [(4096, [120])] [])) (readv_x_model 1) [] := by
  rw_norm

/-- …-EFAULT refused for the capped single descriptor.
rocq-twin: readv_huge_len_delivers_one_byte_without_unary_expansion
probe: testing/syscall-check/tests/readv_spec.c#reject --mutate readv:ret=-EFAULT,drop-writes -- hugefile -/
theorem readv_huge_descriptor_on_a_file_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 3 8192 1 mem_readv_huge wmem_readv_one) (readv_x_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw_refute

/-- An offset of 2^62 on the one-byte file is end of file: 0, the offset
unmoved.
rocq-twin: readv_huge_file_offset_is_bounded_by_file_length
kernel: mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem readv_huge_offset_is_eof (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 1 mem_readv_huge wmem_readv_one) (readv_x_model (Z_to_bv 64 (2 ^ 62))) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (readv_x_model (Z_to_bv 64 (2 ^ 62))) [] := by
  rw_norm

/-- `rw_verify_area`'s position test: a nonempty readv at offset
`LLONG_MAX` is -EINVAL (`(loff_t)(pos + count) < 0`, fs/read_write.c:467-469),
where an offset merely past end of file is 0.
rocq-twin: readv_at_llong_max_is_einval_not_eof
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem readv_at_llong_max_is_einval (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 1 mem_readv_iov wmem_readv_one) (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1))) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] []))
             (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1))) [] := by
  rw_norm

/-- …not the 0 of end of file.
rocq-twin: readv_at_llong_max_is_einval_not_eof
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem readv_at_llong_max_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 3 8192 1 mem_readv_iov wmem_readv_one) (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1)))
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- One below: `LLONG_MAX - 1` plus a count of one does not reach 2^63,
so the test does not fire and the answer is end of file's 0.
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem readv_below_llong_max_is_eof (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 1 mem_readv_iov wmem_readv_one) (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 2))) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 2))) [] := by
  rw_norm

/-- THE RECORDED DIVERGENCE: the scalar `read` at the same offset reaches
the same kernel test and still answers 0 in the model, the descriptor
written back (bugs/read-write-position-past-llong-max-answers-zero.md).
Pinned so that closing it is a visible flip here, not a silent one.
rocq-twin: readv_at_llong_max_is_einval_not_eof -/
theorem read_at_llong_max_answers_zero_divergence (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 4096 1 wmem_readv_one) (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1))) o ↔
      o = Ok (mkEffect 0 [] []) (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1))) [] := by
  rw_norm

/-- A path the file system does not hold declines rather than invent a
file — a state the kernel cannot be in, an open description always
holding its inode — `vfs_readv` (fs/read_write.c:990-1026, v6.18.46)
never asks whether the file exists; the gap is a guard, not a behaviour.
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem readv_file_path_absent_declines (o : outcome SyscallEffect) :
    syscall_spec (readv_in 7 8192 1 mem_readv_iov wmem_readv_one) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-! ### Closing the readv pins: the delivery as one statement, and the zero aggregates -/

/-- THE CHANNEL DELIVERY AS ONE STATEMENT: every outcome of a two-descriptor
readv on stdin holding five bytes is a delivery — a nonempty prefix of the
input scattered across the capped vector, which bounds it by the
aggregate — and
every such delivery is an outcome, the stream advanced past exactly those
bytes and one event per byte.  `anon_pipe_read` copies pipe buffers until
the request is met or the pipe runs empty and returns what it has
(`if (!total_len)`, fs/pipe.c:364; `if (ret) break`, :372; v6.18.46); how
the writer's bytes were buffered is what the prefix ranges over.  Stated
on the ledger through `readv_bytes` (`choose_scatter_eq` above),
which is why the last conjunct is the scatter equation rather than a
single write.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem readv_stdin_delivers_a_prefix_iff (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (stdin_model (hello b c d e f)) o ↔
      ∃ writes : List (word × List byte),
        o = Ok (with_copyins [(8192, 16), (8208, 16)]
                 (mkEffect (len_word (readv_bytes writes)) writes []))
               (stdin_model (stream_take (hello b c d e f) (readv_bytes writes).length).2)
               (List.map (ReadEv 0) (readv_bytes writes))
        ∧ 1 ≤ ((readv_bytes writes).length : Int)
        ∧ (stream_take (hello b c d e f) (readv_bytes writes).length).1 = readv_bytes writes
        ∧ scatter_iovecs (wmem_first 5) (cap_iovecs [(4096, 2), (4098, 3)]) (readv_bytes writes)
            = some writes := by
  rw_norm

/-- …and no delivery leaves the input where it was: two bytes delivered
with the stream unmoved is not an outcome — `anon_pipe_read` retires what
it copied (`buf->offset += chars; buf->len -= chars`, fs/pipe.c:350-351,
v6.18.46).  The input is `hello` and then anything: a symbolic tail keeps
the two streams as `ICons` chains, which `ICons_eq_ICons` compares byte by
byte, where a closed stream is evaluated to its function before any law
can see it, and five concrete bytes are what the arm's own five-byte
fault probe of the destination needs to compute; the first byte is not
the third, so the two are provably different whatever the tail.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem readv_stdin_not_consumed_rejected (s : InputStream) (evs : List event) :
    ¬ syscall_spec (readv_in 0 8192 2 iov_2_3 (wmem_first 5))
        (stdin_model (ICons 104 (ICons 101 (ICons 108 (ICons 108 (ICons 111 s))))))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [104, 101])] []))
            (stdin_model (ICons 104 (ICons 101 (ICons 108 (ICons 108 (ICons 111 s)))))) evs) := by
  rw_refute

/-- THE SOCKET DELIVERY AS ONE STATEMENT, the `readv` twin of
`socket_delivers_a_prefix_iff`: a byte at the head of the script and every
outcome is a nonempty prefix of the queue scattered across the vector,
which bounds it by the aggregate, the script advanced past it and one event per byte on
the connection's channel.  `tcp_recvmsg_locked` copies `min(skb->len -
offset, len)` per skb (net/ipv4/tcp.c:2794-2796, v6.18.46) and returns
what it has when the queue runs dry with something copied.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_socket_delivers_a_prefix_iff (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (readv_in 25 8192 2 iov_2_3 (wmem_first 5)) (socket_model (NCons b (NCons c NFin))) o ↔
      ∃ writes : List (word × List byte),
        o = Ok (with_copyins [(8192, 16), (8208, 16)]
                 (mkEffect (len_word (readv_bytes writes)) writes []))
               (with_fds (fd_insert (socket_fds (NCons b (NCons c NFin))) 25
                   (.FdSocket (.SkConnected peer_a 7
                     (net_take (NCons b (NCons c NFin)) (readv_bytes writes).length).2)))
                 (socket_model (NCons b (NCons c NFin))))
               (List.map (ReadEv 7) (readv_bytes writes))
        ∧ 1 ≤ ((readv_bytes writes).length : Int)
        ∧ (net_take (NCons b (NCons c NFin)) (readv_bytes writes).length).1 = readv_bytes writes
        ∧ scatter_iovecs (wmem_first 5) (cap_iovecs [(4096, 2), (4098, 3)]) (readv_bytes writes)
            = some writes := by
  rw_norm

attribute [local sys_simp low] fd_insert.eq_1 in
/-- …and the queue is CONSUMED: both bytes delivered with the script left
as it was is refused — `tcp_recvmsg_locked` advances `copied_seq`
(`WRITE_ONCE(*seq, *seq + used)`, net/ipv4/tcp.c:2855, v6.18.46) and eats
the skb (:2881).  The script is `hello` and then anything, for the reason
`readv_stdin_not_consumed_rejected` gives; the unchanged table is compared
with the advanced one entry by entry, so `fd_insert` is unfolded for this
pin alone.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_socket_script_not_consumed_rejected (s : NetStream) (evs : List event) :
    ¬ syscall_spec (readv_in 25 8192 2 iov_2_3 (wmem_first 5))
        (socket_model (NCons 104 (NCons 101 (NCons 108 (NCons 108 (NCons 111 s))))))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [104, 101])] []))
            (socket_model (NCons 104 (NCons 101 (NCons 108 (NCons 108 (NCons 111 s)))))) evs) := by
  rw_refute

/-- A ZERO AGGREGATE IS 0 BEFORE THE POSITION TEST on readv too: `vfs_readv`
returns on `!tot_len` (fs/read_write.c:1009-1011, v6.18.46) before
`rw_verify_area` (:1013), so two empty descriptors at offset `LLONG_MAX`
are 0, not the -EINVAL a nonempty aggregate there is
(`readv_at_llong_max_is_einval`).
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem readv_file_zero_aggregate_at_llong_max_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none)
        (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1))) o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] []))
             (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1))) [] := by
  rw_norm

/-- …and not -EINVAL.
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem readv_file_zero_aggregate_at_llong_max_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 3 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none)
        (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1)))
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] [])) m' evs) := by
  rw_refute

/-- …and before the socket is asked: a pending RST under a zero aggregate
is 0 with the RST still pending, `vfs_readv`'s `!tot_len` return
(fs/read_write.c:1009-1011, v6.18.46) coming before the file's
`read_iter` — `sock_read_iter` here — is called (:1017-1018).
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem readv_rst_zero_aggregate_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 21 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- …and not -ECONNRESET.
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem readv_rst_zero_aggregate_econnreset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 21 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ECONNRESET) [] [])) m' evs) := by
  rw_refute

/-- …and before the pipe read end's decline: a zero aggregate on fd 14 is
0, answered by `vfs_readv` (fs/read_write.c:1009-1011, v6.18.46) where a
nonempty one declines (`readv_pipe_read_end_declines`).
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem readv_pipe_zero_aggregate_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 14 8192 2 (mem_iov_pair 4096 0 0 0) wmem_none) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-! ## `writev_file_arm`: what every file writev arm shares

The helper is pinned as a helper first — applied to an input and a
model directly, with `place` the kind's middle — so that what every file
kind shares is fixed independently of the one kind `writev_spec` lands
it on (its `FdFileW` arm, pinned through the table further down).  Two middles are used — `writev_place_none`,
a kind that declines, and `writev_place_fdw`, a stand-in for the
`FdFileW` update writing the offset back — so that the gates ahead of
`place` are pinned independently of any kind.  All fs/read_write.c
`vfs_writev` (:1028-1066) and lib/iov_iter.c, v6.18.46. -/

/-- The declining middle. -/
def writev_place_none : List byte → Option (Sys SyscallEffect → Sys SyscallEffect) := fun _ => none

/-- A stand-in for the `FdFileW` middle: write the offset back and hand
the ledger on. -/
def writev_place_fdw (off : word) : List byte → Option (Sys SyscallEffect → Sys SyscallEffect) :=
  fun bs => some (fun k => set_fds (fd_insert [(3, .FdFileW [102] 0)] 3 (.FdFileW [102] (off + len_word bs))) ;; k)

/-- The model the writev helper pins run in: an `FdFileW` on fd 3 over an
empty file. -/
def writev_model : Model := fixture_of (fds := [(3, .FdFileW [102] 0)]) (fs := [([102], [])])

attribute [sys_simp low] writev_place_none.eq_1 writev_place_fdw.eq_1 writev_model.eq_1

/-- An unreadable array is -EFAULT: the import's, before `place`.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem writev_arm_unreadable_array_is_efault (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm wmem_none 8192 2 0 (some []) writev_place_none i writev_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) writev_model [] := by
  rw_norm

/-- A negative length is -EINVAL, both descriptors read.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem writev_arm_negative_length_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (mem_iov_pair 4096 1 4096 (Z_to_bv 64 (2 ^ 63))) 8192 2 0 (some []) writev_place_none i writev_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] [])) writev_model [] := by
  rw_norm

/-- THE PER-SEGMENT `access_ok` REACHES writev: a readable first entry and
a second whose range leaves the address space — a base of 1 with
`TASK_SIZE` bytes fails `addr <= limit - size` — is -EFAULT at import
(`__import_iovec`, lib/iov_iter.c:1352-1400, v6.18.46), not the one-byte
short write a gather without the check would give.
rocq-twin: writev_import_range_fault_beats_the_gather
kernel: lib/iov_iter.c:__import_iovec; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem writev_arm_import_range_fault_beats_the_gather (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (mem_iov_pair 4096 1 1 at_top) 8192 2 0 (some []) (writev_place_fdw 0) i writev_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) writev_model [] := by
  rw_norm

/-- …the short write refused.
rocq-twin: writev_import_range_fault_beats_the_gather
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem writev_arm_import_range_fault_short_write_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ writev_file_arm (mem_iov_pair 4096 1 1 at_top) 8192 2 0 (some []) (writev_place_fdw 0) i writev_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-- A lone zero-length entry with a base past the ceiling is -EFAULT: the
single path range-checks the capped length, zero included.
rocq-twin: writev_import_range_fault_beats_the_gather
kernel: lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem writev_arm_zero_length_past_top_is_efault (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0) 8192 1 0 (some []) (writev_place_fdw 0) i writev_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) writev_model [] := by
  rw_norm

/-- …not the 0 qemu-user answers when it skips the entry.
rocq-twin: writev_import_range_fault_beats_the_gather
kernel: lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem writev_arm_zero_length_past_top_zero_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ writev_file_arm (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0) 8192 1 0 (some []) (writev_place_fdw 0) i writev_model
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- A zero aggregate is 0 above every kind — `place` is not consulted, so
the declining middle does not decline — and without a source byte read.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_arm_zero_aggregate_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (mem_iov_pair 4096 0 0 0) 8192 2 0 (some []) writev_place_none i writev_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) writev_model [] := by
  rw_norm

/-- A count narrowed to zero — raw 2^32 — is the same 0, no ledger.
rocq-twin: writev_wide_iovcnt_is_unmodeled
kernel: lib/iov_iter.c:import_iovec@v6.18.46 -/
theorem writev_arm_raw_count_2_32_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm mem_writev_ab 8192 (Z_to_bv 64 (2 ^ 32)) 0 (some []) writev_place_none i writev_model o ↔
      o = Ok (mkEffect 0 [] []) writev_model [] := by
  rw_norm

/-- A count whose low 32 bits are 1025 is -EINVAL; so is -1's.
rocq-twin: writev_wide_iovcnt_is_unmodeled
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem writev_arm_count_over_max_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm mem_writev_ab 8192 (Z_to_bv 64 (2 ^ 64 - 1)) 0 (some []) writev_place_none i writev_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) writev_model [] := by
  rw_norm

/-- `rw_verify_area`'s position test on the vectored write: two bytes at
offset `LLONG_MAX` are -EINVAL, the file and offset untouched, before
`place`.
rocq-twin: writev_at_llong_max_is_einval
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem writev_arm_at_llong_max_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm mem_writev_ab 8192 2 (Z_to_bv 64 (2 ^ 63 - 1)) (some []) (writev_place_fdw (Z_to_bv 64 (2 ^ 63 - 1))) i writev_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] [])) writev_model [] := by
  rw_norm

/-- …the two-byte write refused there.
rocq-twin: writev_at_llong_max_is_einval
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem writev_arm_at_llong_max_write_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ writev_file_arm mem_writev_ab 8192 2 (Z_to_bv 64 (2 ^ 63 - 1)) (some []) (writev_place_fdw (Z_to_bv 64 (2 ^ 63 - 1))) i writev_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- `rw_verify_area`'s FIRST test, a position negative as `loff_t`
(`if (unlikely(pos < 0))`, fs/read_write.c:462-464, v6.18.46), ahead of the
overflow test the pin above reaches (:467-469): one byte at 2^63 is
-EINVAL, the file and offset untouched, before `place`.
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem writev_arm_negative_position_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (iov_array [(4096, 1)]) 8192 1 (Z_to_bv 64 (2 ^ 63)) (some []) (writev_place_fdw (Z_to_bv 64 (2 ^ 63))) i writev_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) writev_model [] := by
  rw_norm

/-- …the one-byte write refused there.
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem writev_arm_negative_position_write_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ writev_file_arm (iov_array [(4096, 1)]) 8192 1 (Z_to_bv 64 (2 ^ 63)) (some []) (writev_place_fdw (Z_to_bv 64 (2 ^ 63))) i writev_model
        (Ok (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-- A zero aggregate is 0 BEFORE the position test: `vfs_writev` returns
on `!tot_len` (fs/read_write.c:1047-1049, v6.18.46) and calls
`rw_verify_area` only after (:1051), so an aggregate of 0 at an offset the
position test would refuse is still 0.  No `lseek` reaches the offset;
what the pin fixes is the ORDER of the two tests.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_arm_zero_aggregate_beats_the_position_test (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (mem_iov_pair 4096 0 0 0) 8192 2 (Z_to_bv 64 (2 ^ 63)) (some []) (writev_place_fdw (Z_to_bv 64 (2 ^ 63))) i writev_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) writev_model [] := by
  rw_norm

/-- …and not the -EINVAL the position test would give.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_arm_zero_aggregate_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ writev_file_arm (mem_iov_pair 4096 0 0 0) 8192 2 (Z_to_bv 64 (2 ^ 63)) (some []) (writev_place_fdw (Z_to_bv 64 (2 ^ 63))) i writev_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] [])) m' evs) := by
  rw_refute

/-- The position test beats the gather: two descriptors whose source is
unreadable, at offset `LLONG_MAX`, are -EINVAL: `vfs_writev`
(fs/read_write.c:1051, v6.18.46) asks `rw_verify_area`
(fs/read_write.c:451-478, the `(loff_t) (pos + count) < 0` arm at
:467-469) before the write, so the -EFAULT the write would raise finding
nothing to copy is never reached — the source is not consulted before the
position is judged.
kernel: fs/read_write.c:vfs_writev,rw_verify_area@v6.18.46 -/
theorem writev_arm_position_test_beats_the_gather (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (iov_array [(4096, 1), (4097, 1)]) 8192 2 (Z_to_bv 64 (2 ^ 63 - 1)) (some []) (writev_place_fdw (Z_to_bv 64 (2 ^ 63 - 1))) i writev_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] [])) writev_model [] := by
  rw_norm

/-- …and not -EFAULT.
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem writev_arm_position_test_efault_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ writev_file_arm (iov_array [(4096, 1), (4097, 1)]) 8192 2 (Z_to_bv 64 (2 ^ 63 - 1)) (some []) (writev_place_fdw (Z_to_bv 64 (2 ^ 63 - 1))) i writev_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw_refute

/-- Nothing gatherable of a nonzero request is -EFAULT
(`generic_perform_write`'s `if (unlikely(status == 0))` … `-EFAULT`),
before `place` — at offset 0 of the empty file the kind found, its end,
where the past-end decline does not fire.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_arm_nothing_gatherable_is_efault (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (iov_array [(4096, 1), (4097, 1)]) 8192 2 0 (some []) writev_place_none i writev_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) writev_model [] := by
  rw_norm

/-- The shared helper's first decline beyond Rocq's: handed the file the
kind found (an empty one) and an offset two bytes past its end, a one-byte
gather with no readable byte is `Unmodeled`, where Rocq's `writev_file_arm`
answers -EFAULT with the file untouched.  The kernel walk — `vfs_writev`
(fs/read_write.c:1056-1057, v6.18.46) to `generic_perform_write`
(mm/filemap.c:4244-4335), whose `shmem_write_end` (mm/shmem.c:3352-3353)
moves `i_size` before the -EFAULT, against the pre-fault of v4.17 through
v6.13 and qemu-user's `lock_iovec` — is the twin's, on `writev_file_arm`
and the module header; it is not repeated here.
kernel: mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem writev_arm_past_eof_unreadable_source_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (iov_array [(4096, 1)]) 8192 1 2 (some []) (writev_place_fdw 2) i writev_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …and refuses the untouched-file -EFAULT.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_arm_past_eof_unreadable_source_efault_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ writev_file_arm (iov_array [(4096, 1)]) 8192 1 2 (some []) (writev_place_fdw 2) i writev_model
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw_refute

/-- A kind that found no file keeps Rocq's -EFAULT: the `none` arm of the
match on the lookup answers it, and `openat` minted every `FdFileW` into
the fs, so the state is unreachable and the test does not widen the
decline to it; the -EFAULT is `generic_perform_write`'s
(mm/filemap.c:4321-4323, :4331-4332, v6.18.46).
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_arm_missing_file_keeps_efault (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (iov_array [(4096, 1)]) 8192 1 2 none writev_place_none i writev_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) writev_model [] := by
  rw_norm

/-- A kind that declines, declines only once the gates have passed: two
gatherable bytes on the declining middle.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_arm_declining_kind_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm mem_writev_ab 8192 2 0 (some []) writev_place_none i writev_model o ↔ o = Unmodeled := by
  rw_norm

/-- THE GATHER AND THE LEDGER: two one-byte descriptors gather "ab"; the
answer is 2, the source ranges follow the descriptor reads in the ledger,
and the middle's update is applied.
rocq-twin: writev_two_iovecs_equals_one_write
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_arm_gathers_and_records (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm mem_writev_ab 8192 2 0 (some []) (writev_place_fdw 0) i writev_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
             (with_fds [(3, .FdFileW [102] 2)] writev_model) [] := by
  rw_norm

/-- The total is exact: 3 for a two-byte gather is refused.
probe: testing/syscall-check/tests/writev_adversarial.c#reject --mutate writev#1:ret+1 -/
theorem writev_arm_over_total_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ writev_file_arm mem_writev_ab 8192 2 0 (some []) (writev_place_fdw 0) i writev_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 3 [] [])) m' evs) := by
  rw_refute

/-- A raw count of 2^32 + 2 is two descriptors: the same gather.
rocq-twin: writev_wide_iovcnt_is_unmodeled
kernel: lib/iov_iter.c:import_iovec@v6.18.46 -/
theorem writev_arm_raw_count_truncates (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm mem_writev_ab 8192 (Z_to_bv 64 (2 ^ 32 + 2)) 0 (some []) (writev_place_fdw 0) i writev_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
             (with_fds [(3, .FdFileW [102] 2)] writev_model) [] := by
  rw_norm

/-- The imported file helper follows Linux's low-32-bit import; the outer
spec now declines this wide-count call before the helper is reached.
kernel: lib/iov_iter.c:import_iovec@v6.18.46 -/
theorem writev_arm_raw_count_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ writev_file_arm mem_writev_ab 8192 (Z_to_bv 64 (2 ^ 32 + 2)) 0 (some []) (writev_place_fdw 0) i writev_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- A LATER-SEGMENT FAULT DECLINES — the second of the twin's two file-write
declines (module header of `Sys/Fs/ReadWrite.lean`): the first byte
readable, the second not, the gatherable prefix one byte of an aggregate
of two.  Linux v5.18 on delivers the byte and answers 1 (`generic_perform_write` bails only when `fault_in_iov_iter_readable`
faults nothing of the chunk in, mm/filemap.c:4321-4324 at v6.18.46), Linux
v4.17 through v5.17 fault the chunk in ahead of `write_begin` — at offset
0 one chunk holds both bytes — and answer -EFAULT with the file untouched
(mm/filemap.c:3129-3131 at v4.17,
:3760-3763 at v5.15, :3755 at v5.17), and qemu-user delivers the bytes of
the descriptors before the faulting one and none of that one's
(`lock_iovec`, linux-user/syscall.c:3120-3134, QEMU 11.1.1) — 1 here by
the shape's coincidence, 2 where Linux writes 3 on `{good,2},{half,2}`.
No answer is in the intersection at this offset.  The helper's docstring
has the walk;
Rocq's `writev_file_arm` declines the shape too.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_arm_later_fault_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (mem_iov_pair 4096 1 4097 1) 8192 2 0 (some []) (writev_place_fdw 0) i writev_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …so the certain short write — 1, the byte landed, the descriptor at
1 — is not proved here.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_arm_later_fault_short_write_not_certain (i : SyscallInput) (evs : List event) :
    ¬ writev_file_arm (mem_iov_pair 4096 1 4097 1) 8192 2 0 (some []) (writev_place_fdw 0) i writev_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] []))
            (with_fds [(3, .FdFileW [102] 1)] writev_model) evs) := by
  rw_refute

/-- THE DECLINE COVERS THE COINCIDENCE (module header): the same two
descriptors at offset 4095, where the unreadable byte opens the second
descriptor AND falls on the page boundary at 4096.  There every
implementation answers 1: Linux v5.18 on writes the readable byte; Linux
v4.17 through v5.17 take `bytes = min(PAGE_SIZE - offset, count)`, one
byte at 4095 (mm/filemap.c:3114-3116 at v4.17), write that chunk, fail
the next chunk's fault-in and return `written` (:3178 at v4.17); qemu-user
zeroes the second descriptor (`lock_iovec`, linux-user/syscall.c:3120-3134,
QEMU 11.1.1) and writes the first.  The helper's test reads the gather
and not the offset, so it declines here too — sound, and costing only
completeness, a refinement left undone.  A refinement that answers 1 here
has to move this pin, and the offset-0 pins above have to stay.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_arm_later_fault_at_the_page_boundary_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (mem_iov_pair 4096 1 4097 1) 8192 2 4095 (some []) (writev_place_fdw 4095) i writev_model o ↔
      o = Unmodeled := by
  rw_norm

/-- THE RETIRED BOUND IS NOT IN FRONT OF THE VECTORED WRITE: a single
descriptor of `rw_bytes_max + 1` bytes — `Uaccess.rw_bytes_max` is the
harness bound issue #460 retired from the model — is imported, not
declined at the import.  With one descriptor `__import_iovec_ubuf` hands
the pair to `import_ubuf`, whose only bound is the `MAX_RW_COUNT` cap
(lib/iov_iter.c:1330-1350, :1433-1442, v6.18.46) ahead of the range test
(`__access_ok`, include/asm-generic/access_ok.h); the count is `2^32 + 1`,
so the narrowing to one descriptor is exercised as well.  The outcome is
then the gather's: one readable byte of 131073 is the partial source this
twin declines (`writev_arm_later_fault_declines`), where Rocq's
`writev_over_rw_bytes_max_total_is_judged` delivers the byte.  A source
readable throughout at this length is past what `sys_norm` normalises, so
the bound's absence is pinned by the refutation below and the decline's
reason by the two-byte shape above.
rocq-twin: writev_over_rw_bytes_max_total_is_judged
kernel: lib/iov_iter.c:__import_iovec_ubuf,import_ubuf@v6.18.46 -/
theorem writev_arm_aggregate_past_the_retired_bound_is_imported (i : SyscallInput) (o : outcome SyscallEffect) :
    writev_file_arm (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0) 8192 (Z_to_bv 64 (2 ^ 32 + 1)) 0
        (some []) (writev_place_fdw 0) i writev_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …and not the -EINVAL a bound in front of the import would give.
rocq-twin: writev_over_rw_bytes_max_total_is_judged
kernel: lib/iov_iter.c:__import_iovec_ubuf,import_ubuf@v6.18.46 -/
theorem writev_arm_aggregate_past_the_retired_bound_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ writev_file_arm (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0) 8192 (Z_to_bv 64 (2 ^ 32 + 1)) 0
        (some []) (writev_place_fdw 0) i writev_model
        (Ok (with_copyins [(8192, 16), (4096, 1)] (mkEffect (errno_ret EINVAL) [] [])) m' evs) := by
  rw_refute

/-! ## `writev_spec` through the table: the Rocq worked cases

The helper pins above fixed the gates every file writev arm shares; these
run the whole arm through the dispatcher, on the fds `read_model` already
holds — stdout (1) for the channel delivery, the `FdFileW` on 4 and the
pipe write end on 15 for the aggregate pin — and on one fixture of their
own, a file at offset `LLONG_MAX`.  Two runs are compared where Rocq
compares them: the events of a two-descriptor writev are the events of
the one write of the same bytes, one per byte, which is what lets stdio
flush through writev at no cost to the equivalence (Checks/Examples.v).
fs/read_write.c `do_writev` (:1091-1112), `vfs_writev` (:1028-1066),
lib/iov_iter.c `__import_iovec` (:1352-1400), fs/pipe.c
`anon_pipe_write`; v6.18.46 throughout. -/

/-- `writev(fd, iov, iovcnt)` as the dispatcher sees it: syscall 66, the
three arguments in a0..a2, `mem` the readable view the descriptor array
and the sources are fetched through, nothing writable. -/
def writev_in (fd iov iovcnt : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 66 [fd, iov, iovcnt, 0, 0, 0] mem (fun _ => none)

/-- An `FdFileW` on fd 3 at offset `LLONG_MAX` over an empty file.  Rocq's
`writev_llong_max_model`. -/
def writev_llong_max_model : Model :=
  fixture_of (fds := [(3, .FdFileW [102] (Z_to_bv 64 (2 ^ 63 - 1)))]) (fs := [([102], [])])

attribute [sys_simp low] writev_spec.eq_1 writev_in.eq_1 writev_llong_max_model.eq_1

/-- The events of a delivery name its bytes: `WriteEv ch` is injective on
lists, so two deliveries with the same events delivered the same bytes.
model: `WriteEv` is a constructor of `event`, and the map of an injective
function over lists is injective -/
theorem map_WriteEv_inj (ch : word) : ∀ {l₁ l₂ : List byte},
    List.map (WriteEv ch) l₁ = List.map (WriteEv ch) l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: t₁, _ :: t₂, h => by
      have h' := List.cons.inj h
      rw [(event.WriteEv.inj h'.1).2, map_WriteEv_inj ch h'.2]

/-- The flat write of the same two bytes on the same fixture, in the shape
the two corollaries below compare against: stdout takes a nonempty prefix
of "ab", one event per byte, the ledger the flat range of the bytes
delivered.  Ticket S-Fs-ReadWrite-write pins `write_channel_outcome` on
its own fixture; this is the instance on `read_model`.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_ab_on_read_model_delivers_a_prefix_iff (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none)) read_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) read_model
               (List.map (WriteEv 1) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 2
        ∧ ds = List.take ds.length [97, 98] := by
  rw_norm

/-- THE CHANNEL DELIVERY AS ONE STATEMENT, Rocq's `writev_channel_outcome`
on its fixture: every outcome of writev(1, [{4096,1},{4097,1}], 2) over
"ab" is a nonempty prefix of the gathered bytes, one `WriteEv` per byte,
the ledger the descriptor reads and then the source ranges of exactly the
bytes delivered; and every such prefix is an outcome.  `anon_pipe_write`
(fs/pipe.c:431-601, v6.18.46) copies until the ring fills and returns
what it copied.  No bound on the length is stated beside the prefix:
`IS_ERR_VALUE`'s 2^64 - 4096 (include/linux/err.h, v6.18.46) and 2^64,
which Rocq's arm also names, are far above the `MAX_RW_COUNT` bytes a
gather over the capped vector holds, so no prefix reaches either.
rocq-twin: writev_channel_outcome
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem writev_stdout_delivers_a_prefix_iff (o : outcome SyscallEffect) :
    syscall_spec (writev_in 1 8192 2 mem_writev_ab) read_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins ([(8192, 16), (8208, 16)] ++ iov_prefix_accesses [(4096, 1), (4097, 1)] ds.length)
                 (mkEffect (len_word ds) [] [])) read_model (List.map (WriteEv 1) ds)
        ∧ 1 ≤ (ds.length : Int)
        ∧ ds = List.take ds.length [97, 98] := by
  rw_norm

/-- The full delivery: both bytes, the answer 2, the two source ranges in
the ledger after the two descriptor reads.
rocq-twin: writev_two_iovecs_equals_one_write
probe: testing/syscall-check/tests/writev_adversarial.c#conform -/
theorem writev_ab_events :
    syscall_spec (writev_in 1 8192 2 mem_writev_ab) read_model
      (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
          read_model [WriteEv 1 97, WriteEv 1 98]) := by
  rw [writev_stdout_delivers_a_prefix_iff]
  exact ⟨[97, 98], by rw_norm, by decide, rfl⟩

/-- The short delivery: one byte, and the ledger names only the byte
delivered — the second source range is not read.
rocq-twin: writev_channel_outcome
probe: testing/syscall-check/tests/write_spec.c#conform --mutate writev:ret=1,drop-copyins,smuggle-copyin:a1:16,smuggle-copyin:a1+16:16,smuggle-copyin:a1+32:1 -- v-two -/
theorem writev_ab_short_delivery :
    syscall_spec (writev_in 1 8192 2 mem_writev_ab) read_model
      (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] []))
          read_model [WriteEv 1 97]) := by
  rw [writev_stdout_delivers_a_prefix_iff]
  exact ⟨[97], by rw_norm, by decide, rfl⟩

/-- …and the total is exact: 3 for a two-byte gather is refused.
rocq-twin: writev_two_iovecs_equals_one_write
probe: testing/syscall-check/tests/writev_adversarial.c#reject --mutate writev#1:ret+1 -/
theorem writev_ab_over_total_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 1 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 3 [] [])) m' evs) := by
  rw [writev_stdout_delivers_a_prefix_iff]
  rintro ⟨ds, hok, h1, hds⟩
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact absurd h1 (by decide)
  · sys_refute at hok
  · sys_refute at hok
  · exact absurd (congrArg List.length hds)
      (by simp only [List.length_take, List.length_cons, List.length_nil]; omega)

/-- …nor is a zero delivery of a nonzero gather an outcome.
rocq-twin: writev_channel_outcome
probe: testing/syscall-check/tests/write_spec.c#reject --mutate writev:ret=0 -- v-two -/
theorem writev_ab_zero_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 1 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw [writev_stdout_delivers_a_prefix_iff]
  rintro ⟨ds, hok, h1, hds⟩
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact absurd h1 (by decide)
  · sys_refute at hok
  · sys_refute at hok
  · exact absurd (congrArg List.length hds)
      (by simp only [List.length_take, List.length_cons, List.length_nil]; omega)

/-- BYTE-LEVEL EVENTS ERASE CHUNKING, Rocq's
`writev_two_iovecs_equals_one_write`: writev(1, [{4096,1},{4097,1}], 2)
and write(1, "ab", 2) are both accepted with the same two events, one per
byte, in the same model — the flat buffer and the gathered descriptors
living in different memories.  The concrete witness that the two
`*_outcome_is_*` corollaries below have jointly satisfiable premises.
no-row: a write that delivers bytes emits events and a copy-in, which ROW-PURE never renders as a row, and no recorded run writes from 4096.
rocq-twin: writev_two_iovecs_equals_one_write
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem writev_two_iovecs_equals_one_write :
    syscall_spec (writev_in 1 8192 2 mem_writev_ab) read_model
      (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
          read_model [WriteEv 1 97, WriteEv 1 98])
    ∧ syscall_spec (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none)) read_model
      (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) read_model [WriteEv 1 97, WriteEv 1 98]) := by
  refine ⟨writev_ab_events, ?_⟩
  rw [write_ab_on_read_model_delivers_a_prefix_iff]
  exact ⟨[97, 98], by rw_norm, by decide, by decide, rfl⟩

/-- Rocq's `writev_outcome_is_write_outcome`, on the fixture: a delivery
of `ds` by the vectored write is a delivery of the same `ds` by the flat
write of the same bytes — same return, same events, the ledger naming the
flat range of the same length.
rocq-twin: writev_outcome_is_write_outcome
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem writev_outcome_is_write_outcome (ds : List byte) :
    syscall_spec (writev_in 1 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins ([(8192, 16), (8208, 16)] ++ iov_prefix_accesses [(4096, 1), (4097, 1)] ds.length)
              (mkEffect (len_word ds) [] [])) read_model (List.map (WriteEv 1) ds)) →
      syscall_spec (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none)) read_model
        (Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) read_model
            (List.map (WriteEv 1) ds)) := by
  intro h
  rw [writev_stdout_delivers_a_prefix_iff] at h
  obtain ⟨ds', hok, h1, hds'⟩ := h
  have hds : ds = ds' := map_WriteEv_inj 1 (outcome.Ok.inj hok).2.2
  subst ds'
  have hlen : (ds.length : Int) ≤ 2 := by
    have := congrArg List.length hds'
    simp only [List.length_take, List.length_cons, List.length_nil] at this
    omega
  rw [write_ab_on_read_model_delivers_a_prefix_iff]
  exact ⟨ds, rfl, h1, hlen, hds'⟩

/-- …and Rocq's `write_outcome_is_writev_outcome`, the converse: a
delivery of `ds` by the flat write is a delivery of the same `ds` by the
vectored one, its ledger the descriptor reads and then the source ranges
of the bytes delivered.
rocq-twin: write_outcome_is_writev_outcome
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_outcome_is_writev_outcome (ds : List byte) :
    syscall_spec (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none)) read_model
        (Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) read_model
            (List.map (WriteEv 1) ds)) →
      syscall_spec (writev_in 1 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins ([(8192, 16), (8208, 16)] ++ iov_prefix_accesses [(4096, 1), (4097, 1)] ds.length)
              (mkEffect (len_word ds) [] [])) read_model (List.map (WriteEv 1) ds)) := by
  intro h
  rw [write_ab_on_read_model_delivers_a_prefix_iff] at h
  obtain ⟨ds', hok, h1, -, hds'⟩ := h
  have hds : ds = ds' := map_WriteEv_inj 1 (outcome.Ok.inj hok).2.2
  subst ds'
  rw [writev_stdout_delivers_a_prefix_iff]
  exact ⟨ds, rfl, h1, hds'⟩

/-- Writev on stdout fd 1 uses count 2^32+2 and {4096,1},{4097,1} over readable "ab". Linux
imports two entries and can write both bytes, while qemu-user returns -EINVAL; the pin declines
the call.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- raw2 -/
theorem writev_iovcnt_wide_count_declines (o : outcome SyscallEffect) :
    writev_spec 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Writev on stdout fd 1 uses count 2^32 beside {4096,1},{4097,1} over readable "ab". Linux
narrows the count to zero and returns 0 without importing entries, while qemu-user returns
-EINVAL; the pin declines the call.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- raw0 -/
theorem writev_raw_count_2_32_declines (o : outcome SyscallEffect) :
    writev_spec 1 8192 (Z_to_bv 64 (2 ^ 32)) (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32)) mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Writev on stdout fd 1 uses count 2^32 beside the readable "ab" vector {4096,1},{4097,1}.
Linux returns 0 after narrowing and qemu-user returns -EINVAL, so the pin refuses the former
zero-return outcome.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- raw0 -/
theorem writev_raw_count_2_32_declines_old_answer_refuted :
    ¬ writev_spec 1 8192 (Z_to_bv 64 (2 ^ 32)) (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32)) mem_writev_ab) read_model
      (Ok (mkEffect 0 [] []) read_model []) := by
  rw_refute

/-- Writev on stdout fd 1 with count 2^32 leaves its readable "ab" vector {4096,1},{4097,1}
unused in Linux, which returns 0; qemu-user returns -EINVAL. The dispatcher pin refuses that
concrete -EINVAL because the shape declines.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- raw0 -/
theorem writev_raw_count_2_32_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32)) mem_writev_ab) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- On this open writable fd, count 1025 is -EINVAL at import
(`iovec_from_user`, lib/iov_iter.c:1306-1307, v6.18.46), before any
descriptor is read.
rocq-twin: writev_wide_iovcnt_is_unmodeled
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem writev_count_1025_is_einval (o : outcome SyscallEffect) :
    syscall_spec (writev_in 1 8192 1025 mem_writev_ab) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …and so are -1's low 32 bits.
rocq-twin: writev_wide_iovcnt_is_unmodeled
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem writev_count_minus_one_is_einval (o : outcome SyscallEffect) :
    syscall_spec (writev_in 1 8192 (Z_to_bv 64 (2 ^ 64 - 1)) mem_writev_ab) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- Writev on stdout fd 1 with count 2^32+2 selects {4096,1},{4097,1} over readable "ab" after
Linux narrows the count, but qemu-user returns -EINVAL. The dispatcher pin refuses the two-byte
delivery and its source-read ledger for this declined call.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- raw2 -/
theorem writev_raw_count_delivery_refuted :
    ¬ syscall_spec (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab) read_model
      (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
          read_model [WriteEv 1 97, WriteEv 1 98]) := by
  rw_refute

/-- Writev on stdout fd 1 with count 2^32+2 and readable "ab" in {4096,1},{4097,1} can deliver
two bytes in Linux but returns -EINVAL in qemu-user. The dispatcher pin refuses that concrete
-EINVAL as an outcome of the declined shape.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- raw2 -/
theorem writev_raw_count_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- …and an IN-RANGE count accepts the delivery and not -EINVAL either,
even with the descriptor reads in the ledger.
rocq-twin: writev_over_max_with_small_low32_is_unmodeled
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem writev_in_range_count_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 1 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] [])) m' evs) := by
  rw [writev_stdout_delivers_a_prefix_iff]
  rintro ⟨ds, hok, h1, hds⟩
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact absurd h1 (by decide)
  · sys_refute at hok
  · sys_refute at hok
  · exact absurd (congrArg List.length hds)
      (by simp only [List.length_take, List.length_cons, List.length_nil]; omega)

/-- THE PER-SEGMENT `access_ok` REACHES writev through the table: a
readable first entry and a second whose range leaves the address space is
-EFAULT at import, both descriptors read, no source byte.
rocq-twin: writev_import_range_fault_beats_the_gather
kernel: lib/iov_iter.c:__import_iovec; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem writev_import_range_fault_beats_the_gather (o : outcome SyscallEffect) :
    syscall_spec (writev_in 1 8192 2 (mem_iov_pair 4096 1 1 at_top)) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- …the one-byte short write a gather without the check would give is
refused.
rocq-twin: writev_import_range_fault_beats_the_gather
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem writev_import_range_fault_short_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 1 8192 2 (mem_iov_pair 4096 1 1 at_top)) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-- A lone zero-length entry with a base past the ceiling is -EFAULT
(`import_ubuf` range-checks the capped length, zero included).
rocq-twin: writev_import_range_fault_beats_the_gather
kernel: lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem writev_zero_length_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (writev_in 1 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0)) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- …not the 0 qemu-user answers when its `lock_iovec` skips the entry.
rocq-twin: writev_import_range_fault_beats_the_gather
kernel: lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem writev_zero_length_past_top_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 1 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0)) read_model
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- `rw_verify_area`'s position test on the vectored write: a nonempty
writev to a regular file at offset `LLONG_MAX` is -EINVAL, the file and
the offset untouched, the descriptors read and no source byte.
rocq-twin: writev_at_llong_max_is_einval
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem writev_at_llong_max_is_einval (o : outcome SyscallEffect) :
    syscall_spec (writev_in 3 8192 2 mem_writev_ab) writev_llong_max_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] []))
             writev_llong_max_model [] := by
  rw_norm

/-- …the two-byte write refused there.
rocq-twin: writev_at_llong_max_is_einval
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem writev_at_llong_max_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 3 8192 2 mem_writev_ab) writev_llong_max_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- THE AGGREGATE IS THE KERNEL'S, NOT THE MODEL'S (issue #460): a normal
count of one imports one descriptor, and with that descriptor one byte
over the retired `Uaccess.rw_bytes_max` the call is JUDGED — a one-byte
short write to stdout, only 4096 being mapped — where the aggregate bound
used to decline it.  The delivery is the channel's, so this is the iff
on that fixture; the one byte gatherable makes every outcome the same
one.
rocq-twin: writev_over_rw_bytes_max_total_is_judged
kernel: lib/iov_iter.c:__import_iovec_ubuf,import_ubuf@v6.18.46 -/
theorem writev_over_rw_bytes_max_total_is_judged (o : outcome SyscallEffect) :
    syscall_spec (writev_in 1 8192 1 (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0)) read_model o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins ([(8192, 16)] ++ iov_prefix_accesses [(4096, Z_to_bv 64 (rw_bytes_max + 1))] ds.length)
                 (mkEffect (len_word ds) [] [])) read_model (List.map (WriteEv 1) ds)
        ∧ 1 ≤ (ds.length : Int)
        ∧ ds = List.take ds.length [97] := by
  rw_norm

/-- …the one byte delivered, the ledger the descriptor read and the byte.
rocq-twin: writev_over_rw_bytes_max_total_is_judged
kernel: lib/iov_iter.c:__import_iovec_ubuf,import_ubuf@v6.18.46 -/
theorem writev_over_rw_bytes_max_delivers_one_byte :
    syscall_spec (writev_in 1 8192 1 (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0)) read_model
      (Ok (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) read_model [WriteEv 1 97]) := by
  rw [writev_over_rw_bytes_max_total_is_judged]
  exact ⟨[97], by rw_norm, by decide, rfl⟩

/-- A normal count of one cannot produce an import-count -EINVAL here.
rocq-twin: writev_over_rw_bytes_max_total_is_judged
kernel: lib/iov_iter.c:__import_iovec_ubuf,import_ubuf@v6.18.46 -/
theorem writev_over_rw_bytes_max_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 1 8192 1 (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0)) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- Writev on stdout fd 1 uses count 2^32+1 and {4096,rw_bytes_max+1},{0,0}, with only source
byte 97 at 4096 readable. The pin declines this wide-count call, including the low-word import
of one oversized buffer.
rocq-twin: writev_wide_count_over_rw_bytes_max_is_unmodeled
probe: testing/syscall-check/tests/rw_bytes_bound.c#fail-closed --expect-unmodeled writev -- wv-over-max -/
theorem writev_wide_count_over_rw_bytes_max_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 1 8192 (Z_to_bv 64 (2 ^ 32 + 1)) (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1)) (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0)) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Writev on stdout fd 1 uses count 2^32+1 and {4096,rw_bytes_max+1},{0,0}, with only source
byte 97 at 4096 readable. The pin refuses the former one-byte write and its descriptor/source
ledger for this declined shape.
probe: testing/syscall-check/tests/rw_bytes_bound.c#fail-closed --expect-unmodeled writev -- wv-over-max -/
theorem writev_wide_count_over_rw_bytes_max_old_answer_refuted :
    ¬ writev_spec 1 8192 (Z_to_bv 64 (2 ^ 32 + 1)) (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1)) (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0)) read_model
      (Ok (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) read_model [WriteEv 1 97]) := by
  rw_refute

/-- THE RETIRED BOUND IS IN FRONT OF NO FILE KIND, Rocq's
`writev_aggregate_past_the_retired_bound_is_judged_by_every_file_kind` on
the one file kind the Lean `FdEntry` has: a single descriptor of
`rw_bytes_max + 1` bytes at an unmapped source, on the `FdFileW`, is
imported and judged -EFAULT against a claimed length of 1 — not declined,
which is what the retired gate made the read-write arm do.
rocq-twin: writev_aggregate_past_the_retired_bound_is_judged_by_every_file_kind
kernel: lib/iov_iter.c:__import_iovec_ubuf,import_ubuf@v6.18.46 -/
theorem writev_aggregate_past_the_retired_bound_is_judged_on_a_file (o : outcome SyscallEffect) :
    syscall_spec (writev_in 4 8192 1 (iov_array [(4096, Z_to_bv 64 (rw_bytes_max + 1))])) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- THE PIPE IS THE CONTROL: the same call on the pipe write end declines
for a reason of its own (`writev_buf_gap`, the atomicity argument being
per transfer rather than per vector), so `Unmodeled` is reachable in this
fixture and the file pin above is a fact about the file arm rather than
about the shape of the call.
rocq-twin: writev_aggregate_past_the_retired_bound_is_judged_by_every_file_kind
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_aggregate_past_the_retired_bound_pipe_is_the_control (o : outcome SyscallEffect) :
    syscall_spec (writev_in 15 8192 1 (iov_array [(4096, Z_to_bv 64 (rw_bytes_max + 1))])) read_model o ↔
      o = Unmodeled := by
  rw_norm

/-! ## writev through the table: every fd kind's first decision

`writev_spec` dispatches on the fd's kind before it reads a descriptor,
as `do_writev` resolves the fd (fs/read_write.c:1095-1097, v6.18.46) and
`vfs_writev` tests `FMODE_WRITE` (fs/read_write.c:1037-1038, v6.18.46)
ahead of `import_iovec` (:1042-1043).  The pins above reach the
standard-output channel and the file arm's position test; these reach the
other kinds — one iff per decision and a refutation of the answer a
harness, or a description of another mode, would give.  Where a kind's
mode is the FIXTURE's premise rather than the kernel's (standard input,
the random device, the read ends, /dev/null opened one way or the other),
the docstring says so: the kernel fact is only that a description without
`FMODE_WRITE` is -EBADF before the array is touched.  The import's two
errnos and the zero aggregate are pinned once per arm because the arm
repeats the import per kind — a mutation of one copy is invisible to the
others' pins. -/

/-- For writev on closed fd 30, count 2 selects {4096,1},{4097,1} over readable "ab". The pin
declines this call as `Unmodeled`.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdnonempty -/
theorem writev_closed_fd_declines (o : outcome SyscallEffect) :
    writev_spec 30 8192 2 (writev_in 30 8192 2 mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For writev on closed fd 30, count 2 selects {4096,1},{4097,1} over readable "ab". The pin
refuses the former concrete `-EBADF` outcome.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdnonempty -/
theorem writev_closed_fd_declines_old_answer_refuted :
    ¬ writev_spec 30 8192 2 (writev_in 30 8192 2 mem_writev_ab) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- For writev on closed fd 30, count 2 names an unreadable array at 8192. Linux returns -EBADF
and qemu-user returns -EFAULT; the pin declines this call as `Unmodeled`.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdiov -/
theorem writev_closed_fd_unreadable_array_declines (o : outcome SyscallEffect) :
    writev_spec 30 8192 2 (writev_in 30 8192 2 wmem_none) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For writev on closed fd 30, count 2 names an unreadable array at 8192. Linux returns -EBADF
and qemu-user returns -EFAULT; the pin refuses the former concrete `-EBADF` outcome.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdiov -/
theorem writev_closed_fd_unreadable_array_declines_old_answer_refuted :
    ¬ writev_spec 30 8192 2 (writev_in 30 8192 2 wmem_none) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- Writev on closed fd 30 uses count 5000 beside {4096,1},{4097,1} over readable "ab". Linux
returns -EBADF and qemu-user rejects the full count with -EINVAL, so the dispatcher pin refuses
the concrete -EINVAL outcome.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- rawbadfd -/
theorem writev_closed_fd_count_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 30 8192 5000 mem_writev_ab) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- For writev on read-only file fd 3, count 2 selects {4096,1},{4097,1} over readable "ab". The
pin declines this call as `Unmodeled`.
probe: testing/syscall-check/tests/fd_modes.c#fail-closed --expect-unmodeled writev -- nonempty -/
theorem writev_read_only_file_declines (o : outcome SyscallEffect) :
    writev_spec 3 8192 2 (writev_in 3 8192 2 mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For writev on read-only file fd 3, count 2 selects {4096,1},{4097,1} over readable "ab". The
pin refuses the former concrete `-EBADF` outcome.
probe: testing/syscall-check/tests/fd_modes.c#fail-closed --expect-unmodeled writev -- nonempty -/
theorem writev_read_only_file_declines_old_answer_refuted :
    ¬ writev_spec 3 8192 2 (writev_in 3 8192 2 mem_writev_ab) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- …so the gather a writable description performs is refused.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_read_only_file_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 3 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- For writev on read-only directory fd 5, count 2 selects {4096,1},{4097,1} over readable
"ab". The pin declines this call as `Unmodeled`.
probe: testing/syscall-check/tests/dirfd_spec.c#fail-closed --expect-unmodeled writev -- writev-nonempty -/
theorem writev_directory_declines (o : outcome SyscallEffect) :
    writev_spec 5 8192 2 (writev_in 5 8192 2 mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For writev on read-only directory fd 5, count 2 selects {4096,1},{4097,1} over readable
"ab". The pin refuses the former concrete `-EBADF` outcome.
probe: testing/syscall-check/tests/dirfd_spec.c#fail-closed --expect-unmodeled writev -- writev-nonempty -/
theorem writev_directory_declines_old_answer_refuted :
    ¬ writev_spec 5 8192 2 (writev_in 5 8192 2 mem_writev_ab) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- …not the -EISDIR of the open that could not have produced this fd,
and not readv's answer for the same descriptor.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_directory_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 5 8192 2 mem_writev_ab) read_model
        (Ok (mkEffect (errno_ret EISDIR) [] []) m' evs) := by
  rw_refute

/-- A connected socket declines, the array unread: `sock_write_iter`
(net/socket.c:1176-1199, v6.18.46) is the send path the model does not
carry.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- writev -/
theorem writev_socket_declines (o : outcome SyscallEffect) :
    syscall_spec (writev_in 20 8192 2 mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- …every socket state alike: a fresh one too.
kernel: net/socket.c:sock_write_iter@v6.18.46 -/
theorem writev_fresh_socket_declines (o : outcome SyscallEffect) :
    syscall_spec (writev_in 10 8192 2 mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- …so the delivery a real kernel gives on the connected one is refused.
kernel: net/socket.c:sock_write_iter@v6.18.46 -/
theorem writev_socket_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 20 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- For writev on read-only stdin fd 0, count 2 selects {4096,1},{4097,1} over readable "ab".
The pin declines this call as `Unmodeled`.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_stdin_channel_declines (o : outcome SyscallEffect) :
    writev_spec 0 8192 2 (writev_in 0 8192 2 mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For writev on read-only stdin fd 0, count 2 selects {4096,1},{4097,1} over readable "ab".
The pin refuses the former concrete `-EBADF` outcome.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_stdin_channel_declines_old_answer_refuted :
    ¬ writev_spec 0 8192 2 (writev_in 0 8192 2 mem_writev_ab) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- For writev on fd 26, an alias of read-only stdin, count 2 selects {4096,1},{4097,1} over
readable "ab". The pin declines this call as `Unmodeled`.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_stdin_alias_declines (o : outcome SyscallEffect) :
    writev_spec 26 8192 2 (writev_in 26 8192 2 mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For writev on fd 26, an alias of read-only stdin, count 2 selects {4096,1},{4097,1} over
readable "ab". The pin refuses the former concrete `-EBADF` outcome.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_stdin_alias_declines_old_answer_refuted :
    ¬ writev_spec 26 8192 2 (writev_in 26 8192 2 mem_writev_ab) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- …never the delivery standard output gives the same call.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_stdin_channel_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 0 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- A readable array over an unreadable source on standard output:
-EFAULT, the descriptor in the ledger, nothing delivered.  The pipe behind
the harness's standard output copies the source page by page and answers
-EFAULT only when no byte was copied (`anon_pipe_write`,
fs/pipe.c:522-526, v6.18.46: `ret = -EFAULT` under `if (!ret)` at the
short copy).
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem writev_stdout_unreadable_source_is_efault (o : outcome SyscallEffect) :
    syscall_spec (writev_in 1 8192 1 (iov_array [(4096, 2)])) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- …and not 0: nothing gathered is a fault, not a short write of nothing.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem writev_stdout_unreadable_source_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 1 8192 1 (iov_array [(4096, 2)])) read_model
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-! ### The file arm through the table -/

/-- THE FILE ARM THROUGH THE TABLE: "ab" gathered from two descriptors
into the one-byte file "j" at offset 0 leaves "ab" and the descriptor at
2, both descriptor reads and both source bytes in the ledger, no event.
`do_writev` writes the position back (fs/read_write.c:1104-1105,
v6.18.46); `generic_perform_write` copies the source (mm/filemap.c:4244-4335, v6.18.46).
rocq-twin: writev_two_iovecs_equals_one_write
kernel: fs/read_write.c:do_writev;mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_lands_at_the_offset_iff (o : outcome SyscallEffect) :
    syscall_spec (writev_in 4 8192 2 mem_writev_ab) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
             (with_fds (fd_insert read_fds 4 (.FdFileW [103] 2))
               (with_fs (fs_set read_fs [103] [97, 98]) read_model)) [] := by
  rw_norm

/-- …the short write of "a" alone is refused: the whole source is readable.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_short_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 4 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-- …a stale descriptor beside the written file is refused.
kernel: fs/read_write.c:do_writev@v6.18.46 -/
theorem writev_file_stale_offset_rejected (evs : List event) :
    ¬ syscall_spec (writev_in 4 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
            (with_fs (fs_set read_fs [103] [97, 98]) read_model) evs) := by
  rw_refute

/-- …as is the advanced descriptor beside an unchanged file.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_unchanged_file_rejected (evs : List event) :
    ¬ syscall_spec (writev_in 4 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
            (with_fds (fd_insert read_fds 4 (.FdFileW [103] 2)) read_model) evs) := by
  rw_refute

/-- …and a file write emits no event: the page cache is not a channel.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_emits_nothing (m' : Model) :
    ¬ syscall_spec (writev_in 4 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
            m' [WriteEv 1 97, WriteEv 1 98]) := by
  rw_refute

/-- A readable array over an unreadable source on a file: -EFAULT, the
descriptor read, the file and descriptor untouched (`generic_perform_write`
answers -EFAULT only when nothing was copied: the `status = -EFAULT` at
mm/filemap.c:4322-4323 is returned under `if (!written)`, :4331-4332, v6.18.46).
The offset is 0 on a one-byte file, WITHIN it, where every implementation
leaves the file alone; past its end the arm declines instead
(`writev_arm_past_eof_unreadable_source_declines`).
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_unreadable_source_is_efault (o : outcome SyscallEffect) :
    syscall_spec (writev_in 4 8192 1 (iov_array [(4096, 2)])) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- …not 0.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_unreadable_source_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 4 8192 1 (iov_array [(4096, 2)])) read_model
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- A ZERO-LENGTH ENTRY AHEAD OF AN UNREADABLE ONE is the same -EFAULT:
`iterate_iovec` skips the empty entry without touching its base
(include/linux/iov_iter.h:51, v6.18.46), the one byte requested is not
readable, nothing is copied, and `generic_perform_write` answers -EFAULT
(mm/filemap.c:4321-4324, :4331-4334, v6.18.46) — as every Linux since
v4.17 does, the pre-fault of the older loop failing on the same byte.
Within the file, so the past-end decline does not fire, and a prefix of
nothing, so the partial-source decline does not either.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_zero_prefix_then_bad_source_is_efault (o : outcome SyscallEffect) :
    syscall_spec (writev_in 4 8192 2 (mem_iov_pair 4096 0 0 1)) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- …and not the 0 qemu-user answers: `lock_iovec` zeroes the length of a
later base it cannot lock (linux-user/syscall.c:3125-3134, QEMU 11.1.1)
and hands the host `writev` an empty vector — an answer decided by
locking the vector, which the readv side refuses (`readv_spec`'s
docstring; tests/readv_spec.c `filezerofirstbad`), refused here the same
way.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_zero_prefix_then_bad_source_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 4 8192 2 (mem_iov_pair 4096 0 0 1)) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- Zero descriptors on a file: 0, nothing imported, nothing touched —
`vfs_writev`'s `!tot_len` exit (fs/read_write.c:1047-1049, v6.18.46),
reached with `import_iovec` having imported nothing.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_file_zero_count_is_zero (o : outcome SyscallEffect) :
    syscall_spec (writev_in 4 8192 0 mem_writev_ab) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …not -EINVAL.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_file_zero_count_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 4 8192 0 mem_writev_ab) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- The import's -EINVAL reaches the file arm: 1025 descriptors is
`iovec_from_user`'s `nr_segs > UIO_MAXIOV` (lib/iov_iter.c:1306-1307,
v6.18.46), no ledger.
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem writev_file_count_1025_is_einval (o : outcome SyscallEffect) :
    syscall_spec (writev_in 4 8192 1025 mem_writev_ab) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …and its -EFAULT: a second descriptor whose range leaves the address
space faults at import on the file arm too, both descriptors read, no byte.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem writev_file_import_range_fault_is_efault (o : outcome SyscallEffect) :
    syscall_spec (writev_in 4 8192 2 (mem_iov_pair 4096 1 1 at_top)) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- …never the one-byte write the readable first descriptor would allow.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem writev_file_import_range_fault_short_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 4 8192 2 (mem_iov_pair 4096 1 1 at_top)) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-- An `FdFileW` on fd 3 at offset 2 over an empty file: the gather lands
after a two-byte hole. -/
def writev_hole_model : Model :=
  fixture_of (fds := [(3, .FdFileW [102] 2)]) (fs := [([102], [])])

/-- A small hole IS built: at offset 2 over an empty file the gather lands
after two zero bytes and the descriptor moves to 4 — `file_write`'s
padding, the bytes Linux's page cache reads back as zero from the hole
`generic_perform_write` leaves (mm/filemap.c:4244-4335, v6.18.46).
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_small_hole_is_zero_filled (o : outcome SyscallEffect) :
    syscall_spec (writev_in 3 8192 2 mem_writev_ab) writev_hole_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
             (with_fds (fd_insert (m_fds writev_hole_model) 3 (.FdFileW [102] 4))
               (with_fs (fs_set (m_fs writev_hole_model) [102] [0, 0, 97, 98]) writev_hole_model)) [] := by
  rw_norm

/-- …the hole is not skipped: "ab" landing at 0 is refused.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_small_hole_at_zero_rejected (evs : List event) :
    ¬ syscall_spec (writev_in 3 8192 2 mem_writev_ab) writev_hole_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
            (with_fds (fd_insert (m_fds writev_hole_model) 3 (.FdFileW [102] 2))
              (with_fs (fs_set (m_fs writev_hole_model) [102] [97, 98]) writev_hole_model)) evs) := by
  rw_refute

/-- An `FdFileW` on fd 3 at offset `rw_bytes_max + 1` over an empty file:
the zero-fill a write here would build is one byte past what the model
represents. -/
def writev_far_offset_model : Model :=
  fixture_of (fds := [(3, .FdFileW [102] (Z_to_bv 64 (rw_bytes_max + 1)))]) (fs := [([102], [])])

/-- A gather landing past a hole the model cannot build declines.  Linux
extends the file with a sparse hole at no cost (`generic_perform_write`,
mm/filemap.c:4244-4335, v6.18.46); the model holds a file as a flat list,
and `modeled_file_gap` refuses to build one longer than `rw_bytes_max` —
the retired bound whose cost is stated on `Uaccess.rw_bytes_max`.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_far_offset_declines (o : outcome SyscallEffect) :
    syscall_spec (writev_in 3 8192 2 mem_writev_ab) writev_far_offset_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …so the write Linux performs there is refused rather than admitted
with a fabricated file.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_far_offset_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 3 8192 2 mem_writev_ab) writev_far_offset_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- An unreadable source at an offset past the file's end declines through
the table: the one shape `writev_file_arm` declines where Rocq's answers
-EFAULT with the file untouched.  The kernel argument is
`writev_arm_past_eof_unreadable_source_declines`'s, the helper-level pin;
bugs/write-file-past-eof-unreadable-source-answers-an-unchanged-file.md
records the Rocq answer and names this arm.
kernel: mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem writev_file_past_eof_unreadable_source_declines (o : outcome SyscallEffect) :
    syscall_spec (writev_in 3 8192 1 (iov_array [(4096, 1)])) writev_hole_model o ↔ o = Unmodeled := by
  rw_norm

/-- …and Rocq's -EFAULT with the file untouched is refused.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_past_eof_unreadable_source_is_not_efault :
    ¬ syscall_spec (writev_in 3 8192 1 (iov_array [(4096, 1)])) writev_hole_model
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) writev_hole_model []) := by
  rw_refute

/-- AT the end of file the decline does not fire: with `pos` equal to
`i_size`, `pos + copied` at `copied` 0 does not pass it (`shmem_write_end`,
mm/shmem.c:3352, v6.18.46), so v6.18.46 leaves the modeled file — bytes,
length, offset — alone as every other implementation does, and -EFAULT
with the file untouched is in the intersection — the edge of the `<` in `writev_file_arm`'s past-end test.
The -EFAULT is `generic_perform_write`'s
(mm/filemap.c:4321-4323, :4331-4332, v6.18.46); the ledger is the
import's one read of the array.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_at_eof_unreadable_source_is_efault (o : outcome SyscallEffect) :
    syscall_spec (writev_in 3 8192 1 (iov_array [(4096, 1)])) wend_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) wend_model [] := by
  rw_norm

/-- …and is not the decline.
kernel: mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem writev_file_at_eof_unreadable_source_is_not_a_decline :
    ¬ syscall_spec (writev_in 3 8192 1 (iov_array [(4096, 1)])) wend_model Unmodeled := by
  rw_refute

/-- ONE byte past the end the decline fires: `pos + 0` is 3 against an
`i_size` of 2, so `shmem_write_end` (mm/shmem.c:3352-3353, v6.18.46) moves
the size by one byte before the -EFAULT.  The other side of the edge.
kernel: mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem writev_file_one_past_eof_unreadable_source_declines (o : outcome SyscallEffect) :
    syscall_spec (writev_in 4 8192 1 (iov_array [(4096, 1)])) wend_model o ↔ o = Unmodeled := by
  rw_norm

/-- …and the untouched-file -EFAULT is refused one byte past the end.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_one_past_eof_unreadable_source_is_not_efault :
    ¬ syscall_spec (writev_in 4 8192 1 (iov_array [(4096, 1)])) wend_model
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) wend_model []) := by
  rw_refute

/-- Past the hole the model could not build the same source declines, and
not for the hole's size: the decline sits ahead of `place`, so it is the
`Unmodeled` a readable byte's oversize hole would be
(`writev_file_far_offset_declines`), reached one test earlier.
kernel: mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem writev_file_far_offset_unreadable_source_declines (o : outcome SyscallEffect) :
    syscall_spec (writev_in 3 8192 1 (iov_array [(4096, 1)])) writev_far_offset_model o ↔ o = Unmodeled := by
  rw_norm

/-- …and Rocq's -EFAULT is refused there too.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_file_far_offset_unreadable_source_is_not_efault :
    ¬ syscall_spec (writev_in 3 8192 1 (iov_array [(4096, 1)])) writev_far_offset_model
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) writev_far_offset_model []) := by
  rw_refute

/-- THE ORDER: at `LLONG_MAX` with a one-byte unreadable source,
`rw_verify_area` (fs/read_write.c:451-478, the test at :467-469, v6.18.46)
answers -EINVAL from `vfs_writev` (:1051) before `write_iter` is called
(:1056-1057), so the decline, which models the loop, sits behind the
position test and is never reached.  Rocq's arm has the -EINVAL in the
same place.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_file_position_test_beats_the_decline (o : outcome SyscallEffect) :
    syscall_spec (writev_in 3 8192 1 (iov_array [(4096, 1)])) writev_llong_max_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) writev_llong_max_model [] := by
  rw_norm

/-- …and is not the decline.
kernel: fs/read_write.c:rw_verify_area@v6.18.46 -/
theorem writev_file_position_test_decline_rejected :
    ¬ syscall_spec (writev_in 3 8192 1 (iov_array [(4096, 1)])) writev_llong_max_model Unmodeled := by
  rw_refute

/-- An `FdFileW` on fd 3 whose path the file system does not hold: a
state no run reaches, since the entry is minted with its file. -/
def writev_orphan_model : Model := fixture_of (fds := [(3, .FdFileW [104] 0)]) (fs := read_fs)

/-- A path the file system does not hold declines rather than invent a
file — a state the kernel cannot be in, an open description always
holding its inode — `vfs_writev` (fs/read_write.c:1028-1066, v6.18.46)
never asks whether the file exists.  The place function's `none` is a
guard, not a behaviour.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_file_path_absent_declines (o : outcome SyscallEffect) :
    syscall_spec (writev_in 3 8192 2 mem_writev_ab) writev_orphan_model o ↔
      o = Unmodeled := by
  rw_norm

/-! ### The random device, /dev/null and the pipe ends -/

/-- For writev on read-only /dev/urandom fd 24, count 2 selects {4096,1},{4097,1} over readable
"ab". The pin declines this call as `Unmodeled`.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_urandom_declines (o : outcome SyscallEffect) :
    writev_spec 24 8192 2 (writev_in 24 8192 2 mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For writev on read-only /dev/urandom fd 24, count 2 selects {4096,1},{4097,1} over readable
"ab". The pin refuses the former concrete `-EBADF` outcome.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_urandom_declines_old_answer_refuted :
    ¬ writev_spec 24 8192 2 (writev_in 24 8192 2 mem_writev_ab) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- …so the count a writable description would answer is refused.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_urandom_count_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 24 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- For writev on read-only /dev/null fd 8, count 2 selects {4096,1},{4097,1} over readable
"ab". The pin declines this call as `Unmodeled`.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_devnull_read_only_declines (o : outcome SyscallEffect) :
    writev_spec 8 8192 2 (writev_in 8 8192 2 mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For writev on read-only /dev/null fd 8, count 2 selects {4096,1},{4097,1} over readable
"ab". The pin refuses the former concrete `-EBADF` outcome.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_devnull_read_only_declines_old_answer_refuted :
    ¬ writev_spec 8 8192 2 (writev_in 8 8192 2 mem_writev_ab) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- …not the count the write-only description answers.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_devnull_read_only_count_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 8 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- /dev/null open for writing swallows the aggregate: `write_iter_null`
advances the iterator by its count and returns it without touching a
source byte (drivers/char/mem.c:429-434, v6.18.46), so the ledger holds
the descriptor reads alone and the model is unchanged.
kernel: drivers/char/mem.c:write_iter_null@v6.18.46 -/
theorem writev_devnull_swallows_the_aggregate (o : outcome SyscallEffect) :
    syscall_spec (writev_in 9 8192 2 mem_writev_ab) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [] [])) read_model [] := by
  rw_norm

/-- …the source bytes are not in the ledger: a harness that gathered
them first is refused.
kernel: drivers/char/mem.c:write_iter_null@v6.18.46 -/
theorem writev_devnull_source_read_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 9 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- …an UNREADABLE source included: the null write never copies, so a
descriptor over unmapped memory is counted, not faulted.
kernel: drivers/char/mem.c:write_iter_null@v6.18.46 -/
theorem writev_devnull_unreadable_source_is_the_count (o : outcome SyscallEffect) :
    syscall_spec (writev_in 9 8192 1 (iov_array [(4096, 5)])) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 5 [] [])) read_model [] := by
  rw_norm

/-- …never -EFAULT, the answer every copying kind gives that shape.
kernel: drivers/char/mem.c:write_iter_null@v6.18.46 -/
theorem writev_devnull_unreadable_source_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 9 8192 1 (iov_array [(4096, 5)])) read_model
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw_refute

/-- …and an aggregate past the retired bound is still the count: the
null device copies nothing, so no bound on what the model can gather
applies (`import_iovec` clamps only at `MAX_RW_COUNT`, lib/iov_iter.c, v6.18.46).
kernel: drivers/char/mem.c:write_iter_null@v6.18.46 -/
theorem writev_devnull_over_the_retired_bound_is_the_count (o : outcome SyscallEffect) :
    syscall_spec (writev_in 9 8192 1 (iov_array [(4096, Z_to_bv 64 (rw_bytes_max + 1))])) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (Z_to_bv 64 (rw_bytes_max + 1)) [] [])) read_model [] := by
  rw_norm

/-- Zero descriptors on the null device: 0, nothing imported.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_devnull_zero_count_is_zero (o : outcome SyscallEffect) :
    syscall_spec (writev_in 9 8192 0 mem_writev_ab) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- The import's own errors come first on the null device: 1025
descriptors is -EINVAL (`import_iovec` runs ahead of the `write_iter`
dispatch, fs/read_write.c:1042-1044 then :1056-1057, v6.18.46).
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem writev_devnull_count_1025_is_einval (o : outcome SyscallEffect) :
    syscall_spec (writev_in 9 8192 1025 mem_writev_ab) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …and a descriptor whose range leaves the address space is -EFAULT at
import, both descriptors read.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem writev_devnull_import_range_fault_is_efault (o : outcome SyscallEffect) :
    syscall_spec (writev_in 9 8192 2 (mem_iov_pair 4096 1 1 at_top)) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- …not the count `write_iter_null` would answer had the import passed.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem writev_devnull_import_range_fault_count_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 9 8192 2 (mem_iov_pair 4096 1 1 at_top)) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- Nine all-zero descriptors: 144 zero bytes at 8192. -/
def mem_writev_nine_zero : word → Option byte := bytes_at 8192 (List.replicate 144 0)

/-- THE HEAP BAND IS JUDGED ON THE VECTORED WRITE: nine descriptors, one
past `UIO_FASTIOV`, put the array on the heap (`iovec_from_user`
allocates it, lib/iov_iter.c:1308-1312, v6.18.46), the band `readv_spec`
declines for the -ENOMEM it could answer (`readv_heap_iovecb`).  `writev_spec`
imports it as Rocq does — bugs/writev-heap-iovec-enomem-not-admitted.md
records the -ENOMEM left out — nine zero-length entries on the null device
being 0 with every descriptor in the ledger.
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem writev_devnull_nine_zero_descriptors_is_zero (o : outcome SyscallEffect) :
    syscall_spec (writev_in 9 8192 9 mem_writev_nine_zero) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
                            (8288, 16), (8304, 16), (8320, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- …and not `readv`'s band decline.
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem writev_devnull_nine_zero_descriptors_decline_rejected :
    ¬ syscall_spec (writev_in 9 8192 9 mem_writev_nine_zero) read_model Unmodeled := by
  rw_refute

/-- For writev on pipe read end fd 14, count 2 selects {4096,1},{4097,1} over readable "ab". The
pin declines this call as `Unmodeled`.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed --expect-unmodeled writev -- wrongend-writev -/
theorem writev_pipe_read_end_declines (o : outcome SyscallEffect) :
    writev_spec 14 8192 2 (writev_in 14 8192 2 mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- For writev on pipe read end fd 14, count 2 selects {4096,1},{4097,1} over readable "ab". The
pin refuses the former concrete `-EBADF` outcome.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed --expect-unmodeled writev -- wrongend-writev -/
theorem writev_pipe_read_end_declines_old_answer_refuted :
    ¬ writev_spec 14 8192 2 (writev_in 14 8192 2 mem_writev_ab) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- Writev on pipe read end fd 14 uses count 2 and {4096,1},{4097,1} over readable "ab". The
dispatcher pin refuses the concrete -EBADF outcome because the nonempty first entry makes the
call decline.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed --expect-unmodeled writev -- wrongend-writev -/
theorem writev_pipe_read_end_old_ebadf_refuted :
    ¬ syscall_spec (writev_in 14 8192 2 mem_writev_ab) read_model (Ok (mkEffect (errno_ret EBADF) [] []) read_model []) := by
  rw_refute

/-- A pipe's write end with zero descriptors: 0, `vfs_writev`'s `!tot_len`
exit (fs/read_write.c:1047-1049, v6.18.46) ahead of the pipe's own write.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_pipe_zero_count_is_zero (o : outcome SyscallEffect) :
    syscall_spec (writev_in 15 8192 0 mem_writev_ab) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …and so is an imported zero aggregate, the descriptor in the ledger.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_pipe_zero_aggregate_is_zero (o : outcome SyscallEffect) :
    syscall_spec (writev_in 15 8192 1 (iov_array [(4096, 0)])) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- …neither declines: the zero aggregate never reaches the pipe.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem writev_pipe_zero_aggregate_decline_rejected :
    ¬ syscall_spec (writev_in 15 8192 1 (iov_array [(4096, 0)])) read_model Unmodeled := by
  rw_refute

/-- A nonzero aggregate on the write end declines: vectored pipe writes
are outside the model (`writev_buf_gap` — the atomicity `anon_pipe_write`
grants, fs/pipe.c:431 on, v6.18.46, is argued per transfer, not per
vector).
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem writev_pipe_write_end_declines (o : outcome SyscallEffect) :
    syscall_spec (writev_in 15 8192 2 mem_writev_ab) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- …so the delivery the scalar `write` of the same bytes gives is
refused here.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem writev_pipe_write_end_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (writev_in 15 8192 2 mem_writev_ab) read_model
        (Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- The import's errors come ahead of the decline: 1025 descriptors is
-EINVAL on a pipe.
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem writev_pipe_count_1025_is_einval (o : outcome SyscallEffect) :
    syscall_spec (writev_in 15 8192 1025 mem_writev_ab) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …and a range fault at import is -EFAULT, both descriptors read.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem writev_pipe_import_range_fault_is_efault (o : outcome SyscallEffect) :
    syscall_spec (writev_in 15 8192 2 (mem_iov_pair 4096 1 1 at_top)) read_model o ↔
      o = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model [] := by
  rw_norm

/-- …neither a decline nor 0.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem writev_pipe_import_range_fault_decline_rejected :
    ¬ syscall_spec (writev_in 15 8192 2 (mem_iov_pair 4096 1 1 at_top)) read_model Unmodeled := by
  rw_refute

/-! ## lseek (62): the fixtures and the call

Rocq's `lseek_model`: a channel at fd 0 and the two-byte file "hi" held
for reading through fd 3 at offset 0, and nothing else in the table, so
fd 9 is closed.  The pins that want the other kinds — a write-only file,
a directory, the two devices, the pipes and the sockets — run on
`read_model`, whose table (`read_fds`) has one of each; fd 6 there holds
the same file at offset 2, its end, which is where `SEEK_CUR` tells and
what a negative displacement subtracts from.  The `whence` selector goes
through the dispatcher's `whence32` and the fd through `fd32`, both
because `SYSCALL_DEFINE3(lseek, unsigned int, fd, off_t, offset, unsigned
int, whence)` (fs/read_write.c:410-413, v6.18.46) takes both as `unsigned
int`; the offset alone is the full 64-bit `off_t`.

WHAT THE ARM READS OFF THE KERNEL.  `ksys_lseek` (fs/read_write.c:393-408)
resolves the fd first (`CLASS(fd_pos, f)(fd)`, :396, -EBADF on
`fd_empty`, :397-398), then compares `whence <= SEEK_MAX` (:401, -EINVAL
otherwise), and only then calls `vfs_llseek` (:402), which answers
-ESPIPE for a file opened without `FMODE_LSEEK` (:387-388) — every
channel, pipe and socket: their files are `alloc_file_pseudo`'s (the
pipe's read end `alloc_file_clone`'s, fs/file_table.c:464-475, v6.18.46),
whose `file_init_path` (fs/file_table.c:364-365, v6.18.46) sets the bit only
for a table with an `.llseek`, which `pipeanon_fops` (fs/pipe.c:1257-1266)
and `socket_file_ops` (net/socket.c:156-173) lack, and `stream_open`
(fs/open.c:1658) clears it besides
— and otherwise the file's `llseek` (:389).  For a regular file on tmpfs
that is `shmem_file_llseek` (mm/shmem.c:3669-3687, v6.18.46), which hands
SEEK_SET,
SEEK_CUR and SEEK_END to `generic_file_llseek_size` (:3674-3676) with
`MAX_LFS_FILESIZE` as the ceiling; the destination `vfs_setpos_cookie`
accepts is `0 ≤ offset ≤ maxsize` (fs/read_write.c:58-61, v6.18.46), so the
last
storable offset is 2^63 - 1 and a sum that wraps negative under the
kernel's `-fno-strict-overflow` arithmetic is -EINVAL.  SEEK_DATA and
SEEK_HOLE on a file are answered by the filesystem's own notion of a hole,
so the arm declines them; `/dev/null`'s `null_lseek` (drivers/char/mem.c:561-564,
v6.18.46) and `/dev/urandom`'s `noop_llseek` (fs/read_write.c:324-327,
v6.18.46) answer 0 for every whence the gate lets through, and a
directory — `offset_dir_llseek` on tmpfs (fs/libfs.c:433-448, v6.18.46),
which repositions on SEEK_SET and SEEK_CUR and is -EINVAL on every other
whence — is declined because the model holds no directory position. -/

/- `lseek_base` and `lseek_dest` are NOT registered: every pin applies them
to closed arguments, which the ground pass evaluates outright, and
registering their equations makes the kernel's check of the file arm's
rewriting run out of stack on every SEEK_CUR / SEEK_END call, whatever
kind the descriptor turns out to hold. -/
attribute [sys_simp low] lseek_spec.eq_1

/-- Rocq's `lseek_model`: a channel at fd 0, "hi" through fd 3 at offset 0. -/
def lseek_fds : List (word × FdEntry) := [(0, .FdChannel 0), (3, .FdFile [102] 0)]

def lseek_fs : Fs.Fs := [([102], [104, 105])]

def lseek_model : Model := fixture_of (fds := lseek_fds) (fs := lseek_fs)

/-- `lseek(fd, off, whence)` as the dispatcher sees it: syscall 62, the
three arguments in a0..a2, no memory readable or writable — the call
touches none. -/
def lseek_in (fd off whence : word) : SyscallInput :=
  SyscallInput.mkInput 62 [fd, off, whence, 0, 0, 0] (fun _ => none) (fun _ => none)

attribute [sys_simp low] lseek_in.eq_1

/-! ### `ksys_lseek`: the descriptor, then the whence, then the kind -/

/-- Rocq's `lseek_channel_espipe`: a channel is an unseekable stream.
`create_pipe_files` (fs/pipe.c:966-967, v6.18.46) opens the tracer's stdio
pipes through `stream_open` (fs/open.c:1656-1661, v6.18.46), which clears
`FMODE_LSEEK`
(fs/open.c:1658), and `vfs_llseek` answers -ESPIPE on that bit
(fs/read_write.c:387-388) before any `llseek` method is consulted.
rocq-twin: lseek_channel_espipe
probe: testing/syscall-check/tests/lseek_probe.c#conform -- chan -/
theorem lseek_channel_espipe (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 0 0 0) lseek_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) lseek_model [] := by
  rw_norm

/-- …and a channel that seeks is not one: 0 is refused.
probe: testing/syscall-check/tests/lseek_probe.c#reject --mutate lseek:ret=0 -- chan -/
theorem lseek_channel_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 0 0 0) lseek_model (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- Rocq's `lseek_channel_bad_whence_is_einval_not_espipe`, the accepting
half: whence 42 on the channel is -EINVAL, because `ksys_lseek` compares
`whence <= SEEK_MAX` (fs/read_write.c:401, v6.18.46) before it calls
`vfs_llseek`, so the fd's KIND is never reached.
rocq-twin: lseek_channel_bad_whence_is_einval_not_espipe
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_channel_bad_whence_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 0 0 42) lseek_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) lseek_model [] := by
  rw_norm

/-- …and the refusing half: -ESPIPE, the kind's answer, is a lie there.
rocq-twin: lseek_channel_bad_whence_is_einval_not_espipe
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_channel_bad_whence_espipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 0 0 42) lseek_model
        (Ok (mkEffect (errno_ret ESPIPE) [] []) m' evs) := by
  rw_refute

/-- Rocq's `lseek_channel_seek_hole_is_espipe`: whence 4 is `SEEK_HOLE`,
which is `SEEK_MAX` (include/uapi/linux/fs.h:56-57, v6.18.46), so the
gate lets it through to `vfs_llseek` and the channel answers -ESPIPE.
rocq-twin: lseek_channel_seek_hole_is_espipe
kernel: fs/read_write.c:ksys_lseek,vfs_llseek@v6.18.46 -/
theorem lseek_channel_seek_hole_is_espipe (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 0 0 4) lseek_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) lseek_model [] := by
  rw_norm

/-- One past `SEEK_MAX`: whence 5 is -EINVAL on the channel, the edge of
the gate `whence <= SEEK_MAX` draws.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_channel_whence_five_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 0 0 5) lseek_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) lseek_model [] := by
  rw_norm

/-- Rocq's `lseek_bad_fd_beats_a_bad_whence`, the accepting half: fd 9
is closed in `lseek_model`, and `ksys_lseek` answers -EBADF on an empty
descriptor (fs/read_write.c:397-398, v6.18.46) before it compares the
whence, so a whence no kernel accepts does not turn a bad fd into
-EINVAL.
rocq-twin: lseek_bad_fd_beats_a_bad_whence
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_bad_fd_beats_a_bad_whence (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 9 0 42) lseek_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) lseek_model [] := by
  rw_norm

/-- …and the refusing half: -EINVAL on the closed fd is a lie.
rocq-twin: lseek_bad_fd_beats_a_bad_whence
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_bad_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 9 0 42) lseek_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- The probe's closed-fd step, whence 0: -EBADF and the model unmoved.
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 9 0 0) lseek_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) lseek_model [] := by
  rw_norm

/-! ### The whence is 32 bits wide, and so is the fd -/

/-- Rocq's `lseek_whence_high_bits_einval_rejected`, the accepting half:
`lseek(3, 0, 2^32 + SEEK_END)` is a SEEK_END, because `SYSCALL_DEFINE3(lseek,
unsigned int, fd, off_t, offset, unsigned int, whence)`
(fs/read_write.c:410-413, v6.18.46) hands `ksys_lseek` the low 32 bits of
the register; it reports the size 2 and moves the offset there.
rocq-twin: lseek_whence_high_bits_einval_rejected
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_whence_high_bits_is_seek_end (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 0 (Z_to_bv 64 (2 ^ 32 + 2))) lseek_model o ↔
      o = Ok (mkEffect 2 [] [])
             (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 2)) lseek_model) [] := by
  rw_norm

/-- …and the refusing half: the -EINVAL a full-register comparison would
demand is a return no kernel produces.
rocq-twin: lseek_whence_high_bits_einval_rejected
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_whence_high_bits_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 3 0 (Z_to_bv 64 (2 ^ 32 + 2))) lseek_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- A whence whose register is NEGATIVE, `0xFFFFFFFF << 32 | SEEK_CUR`,
still selects SEEK_CUR on its low half: the probe's `HI_NEG` step.  On
fd 3 at offset 0, SEEK_CUR of 0 tells 0.
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_whence_negative_register_is_seek_cur (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 0 (Z_to_bv 64 (2 ^ 64 - 2 ^ 32 + 1))) lseek_model o ↔
      o = Ok (mkEffect 0 [] [])
             (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 0)) lseek_model) [] := by
  rw_norm

/-- Rocq's `bit31_is_part_of_the_32_bit_arguments`, the lseek conjunct of
four: bit 31 SURVIVES the truncation, so `2^31 | SEEK_END` names no origin
and is -EINVAL rather than SEEK_END.  (The write conjunct is
`write_bit31_fd_is_ebadf` above, and the two ioctl conjuncts are
`ioctl_bit31_fd_is_closed` and `ioctl_bit31_request_declines` beside it.)
rocq-twin: bit31_is_part_of_the_32_bit_arguments
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_bit31_whence_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 5 (Z_to_bv 64 (2 ^ 31 + 2))) lseek_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) lseek_model [] := by
  rw_norm

/-- …so the SEEK_END answer, 2 + 5 = 7, is refused there.
rocq-twin: bit31_is_part_of_the_32_bit_arguments
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_bit31_whence_seek_end_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 3 5 (Z_to_bv 64 (2 ^ 31 + 2))) lseek_model
        (Ok (mkEffect 7 [] []) m' evs) := by
  rw_refute

/-- The fd is 32 bits too: fd 2^32 + 3 is fd 3, and SEEK_END reports the
size through it.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (lseek_in (Z_to_bv 64 (2 ^ 32 + 3)) 0 2) lseek_model o ↔
      o = Ok (mkEffect 2 [] [])
             (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 2)) lseek_model) [] := by
  rw_norm

/-- …not the -EBADF a 64-bit lookup would answer.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_fd_high_bits_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in (Z_to_bv 64 (2 ^ 32 + 3)) 0 2) lseek_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- …and bit 31 survives that truncation: fd 2^31 + 3 is not fd 3 but a
closed fd, -EBADF from `ksys_lseek`'s lookup (fs/read_write.c:396-398,
v6.18.46) — `lseek`'s own fd half of the bit-31 argument `write` and
`ioctl` make for theirs.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_bit31_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (lseek_in (Z_to_bv 64 (2 ^ 31 + 3)) 0 2) lseek_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) lseek_model [] := by
  rw_norm

/-- …so the size fd 3 would report is refused.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_bit31_fd_size_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in (Z_to_bv 64 (2 ^ 31 + 3)) 0 2) lseek_model
        (Ok (mkEffect 2 [] []) m' evs) := by
  rw_refute

/-- The probe's `HI | 0` step: fd 2^32 is the channel at fd 0, -ESPIPE.
probe: testing/syscall-check/tests/lseek_probe.c#conform -- chan -/
theorem lseek_fd_2_32_is_the_channel (o : outcome SyscallEffect) :
    syscall_spec (lseek_in (Z_to_bv 64 (2 ^ 32)) 0 1) lseek_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) lseek_model [] := by
  rw_norm

/-! ### A regular file: the three origins, and the two ends of `off_t`

`generic_file_llseek_size` (fs/read_write.c:158-186, v6.18.46) turns the
three origins into an absolute destination — `must_set_pos` adds `eof`
for SEEK_END (:106-107) and answers the current position for a zero
SEEK_CUR without moving (:115-118), and the SEEK_CUR sum goes through
`vfs_setpos` (:170-183), SEEK_SET's offset straight to it (:185) — and
`vfs_setpos_cookie` (:55-69) refuses a negative destination (:58-59) and
one past `maxsize` (:60-61), which for tmpfs is `MAX_LFS_FILESIZE`
(mm/shmem.c:3676, v6.18.46; `((loff_t)LLONG_MAX)`, include/linux/fs.h:1279,
v6.18.46).  The
arm's `lseek_dest` is that window: `0 ≤ base + off < 2^63` over exact
integers, which is what the kernel's `loff_t` sum computes once
`-fno-strict-overflow` makes a wrapped sum negative rather than
undefined. -/

/-- Rocq's `lseek_seek_data_on_a_file_is_unmodeled`, the fourth conjunct:
SEEK_END on the two-byte file reports 2 and moves the offset there.
rocq-twin: lseek_seek_data_on_a_file_is_unmodeled
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_file_seek_end_reports_the_size (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 0 2) lseek_model o ↔
      o = Ok (mkEffect 2 [] [])
             (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 2)) lseek_model) [] := by
  rw_norm

/-- …and the offset MOVES: the pre-call table is refused as the
post-state.
kernel: fs/read_write.c:vfs_setpos_cookie@v6.18.46 -/
theorem lseek_file_seek_end_offset_unmoved_rejected (evs : List event) :
    ¬ syscall_spec (lseek_in 3 0 2) lseek_model (Ok (mkEffect 2 [] []) lseek_model evs) := by
  rw_refute

/-- Rocq's `lseek_seek_data_on_a_file_is_unmodeled`, the first conjunct:
SEEK_DATA (3) on a regular file is answered by the filesystem's own
notion of a hole (`shmem_file_llseek`, mm/shmem.c:3677-3686, v6.18.46),
so the arm declines rather than claim the -EINVAL it used to.
rocq-twin: lseek_seek_data_on_a_file_is_unmodeled
kernel: mm/shmem.c:shmem_file_llseek@v6.18.46 -/
theorem lseek_seek_data_on_a_file_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 0 3) lseek_model o ↔ o = Unmodeled := by
  rw_norm

/-- …its second conjunct: SEEK_HOLE (4) declines for the same reason —
where the first hole lies is the filesystem's answer (`shmem_file_llseek`,
mm/shmem.c:3677-3686, v6.18.46, on tmpfs; the host filesystem's under
qemu-user), so the size 2 a hole-free file would report is not claimed.
rocq-twin: lseek_seek_data_on_a_file_is_unmodeled
kernel: mm/shmem.c:shmem_file_llseek@v6.18.46 -/
theorem lseek_seek_hole_on_a_file_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 0 4) lseek_model o ↔ o = Unmodeled := by
  rw_norm

/-- SEEK_SET to 1: inside the file, the offset lands there.
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_file_seek_set_inside (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 1 0) lseek_model o ↔
      o = Ok (mkEffect 1 [] [])
             (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 1)) lseek_model) [] := by
  rw_norm

/-- …and from a descriptor that has moved: fd 6 sits at 2, and SEEK_SET's
base is 0, not that 2, so 1 lands at 1.  `lseek_file_seek_set_inside`
seeks fd 3 at offset 0, where a base of 0 and a base of the current
offset coincide; this is the call that tells them apart.
kernel: fs/read_write.c:generic_file_llseek_size,vfs_setpos_cookie@v6.18.46 -/
theorem lseek_file_seek_set_from_a_moved_offset (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 6 1 0) read_model o ↔
      o = Ok (mkEffect 1 [] [])
             (with_fds (fd_insert read_fds 6 (.FdFile [102] 1)) read_model) [] := by
  rw_norm

/-- …so 3, the answer of a SEEK_SET that added the current offset, is
refused.
kernel: fs/read_write.c:generic_file_llseek_size@v6.18.46 -/
theorem lseek_file_seek_set_plus_offset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 6 1 0) read_model (Ok (mkEffect 3 [] []) m' evs) := by
  rw_refute

/-- SEEK_SET to 100, past the two-byte end: legal, and the file does not
grow — `vfs_setpos_cookie` compares against `maxsize`, not `i_size`
(fs/read_write.c:60-61, v6.18.46).
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_file_past_eof_is_legal (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 100 0) lseek_model o ↔
      o = Ok (mkEffect 100 [] [])
             (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 100)) lseek_model) [] := by
  rw_norm

/-- …and does not grow the file: a post-state whose file is 100 bytes is
refused.
kernel: fs/read_write.c:vfs_setpos_cookie@v6.18.46 -/
theorem lseek_file_past_eof_grows_nothing (evs : List event) :
    ¬ syscall_spec (lseek_in 3 100 0) lseek_model
        (Ok (mkEffect 100 [] [])
            (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 100))
              (with_fs (fs_set lseek_fs [102] (List.replicate 100 0)) lseek_model)) evs) := by
  rw_refute

/-- SEEK_CUR from offset 2 (fd 6 of `read_model`, "hi" at its end):
`-1` tells 1.  The probe's `-5 SEEK_CUR` step from 11 is this rule at a
different size.
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_file_seek_cur_back_one (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 6 (Z_to_bv 64 (-1)) 1) read_model o ↔
      o = Ok (mkEffect 1 [] [])
             (with_fds (fd_insert read_fds 6 (.FdFile [102] 1)) read_model) [] := by
  rw_norm

/-- …and answers the offset exactly: 2 for 1 is refused.  (The probe's
`ret+1` mutation is on its tell, `lseek_file_tell_off_by_one_rejected`
below.)
kernel: fs/read_write.c:generic_file_llseek_size@v6.18.46 -/
theorem lseek_file_seek_cur_off_by_one_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 6 (Z_to_bv 64 (-1)) 1) read_model
        (Ok (mkEffect 2 [] []) m' evs) := by
  rw_refute

/-- A zero SEEK_CUR tells: 2, the table unchanged in value — `must_set_pos`
answers `file->f_pos` without a store (fs/read_write.c:115-118, v6.18.46).
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_file_tell (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 6 0 1) read_model o ↔
      o = Ok (mkEffect 2 [] [])
             (with_fds (fd_insert read_fds 6 (.FdFile [102] 2)) read_model) [] := by
  rw_norm

/-- …and tells exactly: 3 for 2 is refused, the probe's `ret+1` mutation
on its own tell.
probe: testing/syscall-check/tests/lseek_probe.c#reject --mutate lseek#1:ret+1 -/
theorem lseek_file_tell_off_by_one_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 6 0 1) read_model (Ok (mkEffect 3 [] []) m' evs) := by
  rw_refute

/-- A tell from the middle: fd 23 sits at 1 of the two bytes, and SEEK_CUR's
base is that 1, not the size — the call that tells SEEK_CUR's base from
SEEK_END's, which fd 6, at its end, cannot.
kernel: fs/read_write.c:must_set_pos@v6.18.46 -/
theorem lseek_file_tell_from_the_middle (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 23 0 1) read_model o ↔
      o = Ok (mkEffect 1 [] [])
             (with_fds (fd_insert read_fds 23 (.FdFile [102] 1)) read_model) [] := by
  rw_norm

/-- …so 2, the size, is refused there.
kernel: fs/read_write.c:must_set_pos@v6.18.46 -/
theorem lseek_file_tell_from_the_middle_size_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 23 0 1) read_model (Ok (mkEffect 2 [] []) m' evs) := by
  rw_refute

/-- SEEK_CUR by -2 from 2 lands at 0, the first legal destination.
kernel: fs/read_write.c:generic_file_llseek_size,vfs_setpos_cookie@v6.18.46 -/
theorem lseek_file_seek_cur_to_zero (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 6 (Z_to_bv 64 (-2)) 1) read_model o ↔
      o = Ok (mkEffect 0 [] [])
             (with_fds (fd_insert read_fds 6 (.FdFile [102] 0)) read_model) [] := by
  rw_norm

/-- SEEK_END by -2 on the two-byte file lands at 0 as well — the probe's
`seek(wfd, -11, SEEK_END)`, back to the start of its eleven bytes.
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_file_seek_end_back_to_start (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 6 (Z_to_bv 64 (-2)) 2) read_model o ↔
      o = Ok (mkEffect 0 [] [])
             (with_fds (fd_insert read_fds 6 (.FdFile [102] 0)) read_model) [] := by
  rw_norm

/-- …and by -3 lands below it: -EINVAL from `vfs_setpos_cookie`'s
`offset < 0` (fs/read_write.c:58-59, v6.18.46), the offset unmoved.
kernel: fs/read_write.c:vfs_setpos_cookie@v6.18.46 -/
theorem lseek_file_seek_cur_below_zero_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 6 (Z_to_bv 64 (-3)) 1) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- A negative absolute offset: `lseek(3, -1, SEEK_SET)` is -EINVAL.
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_negative_seek_set_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 (Z_to_bv 64 (-1)) 0) lseek_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) lseek_model [] := by
  rw_norm

/-- …not the unsigned reading of -1, which no `off_t` ever is.
kernel: fs/read_write.c:vfs_setpos_cookie@v6.18.46 -/
theorem lseek_negative_seek_set_unsigned_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 3 (Z_to_bv 64 (-1)) 0) lseek_model
        (Ok (mkEffect (Z_to_bv 64 (2 ^ 64 - 1)) [] []) m' evs) := by
  rw_refute

/-- A negative destination via SEEK_END: 2 - 3 < 0 is -EINVAL.
probe: testing/syscall-check/tests/lseek_probe.c#conform -/
theorem lseek_negative_via_seek_end_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 (Z_to_bv 64 (-3)) 2) lseek_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) lseek_model [] := by
  rw_norm

/-- The upper end: SEEK_END by 2^63 - 3 from the two-byte end lands at
2^63 - 1, the `LLONG_MAX` that `MAX_LFS_FILESIZE` (include/linux/fs.h:1279,
v6.18.46) lets `vfs_setpos_cookie`'s `offset > maxsize` (fs/read_write.c:60-61)
accept as tmpfs's ceiling.  A filesystem with a smaller `s_maxbytes`
answers -EINVAL here, an answer the arm does not yet accept
(bugs/lseek-destination-ceiling-is-tmpfs.md), so the pin is one-way:
it admits tmpfs's answer, and an `iff` would pin that refusal.
kernel: fs/read_write.c:vfs_setpos_cookie,generic_file_llseek_size; mm/shmem.c:shmem_file_llseek@v6.18.46 -/
theorem lseek_file_to_llong_max :
    syscall_spec (lseek_in 3 (Z_to_bv 64 (2 ^ 63 - 3)) 2) lseek_model
      (Ok (mkEffect (Z_to_bv 64 (2 ^ 63 - 1)) [] [])
          (with_fds (fd_insert lseek_fds 3 (.FdFile [102] (Z_to_bv 64 (2 ^ 63 - 1))))
            lseek_model) []) := by
  rw_norm

/-- …and not the displacement itself, 2^63 - 3, which a model reading the
origin as SEEK_SET would answer.  No filesystem gives it: tmpfs lands at
2^63 - 1 and a smaller `s_maxbytes` refuses both, since `must_set_pos`
adds `eof` for SEEK_END (fs/read_write.c:106-107, v6.18.46).
kernel: fs/read_write.c:must_set_pos,generic_file_llseek_size@v6.18.46 -/
theorem lseek_file_to_llong_max_displacement_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 3 (Z_to_bv 64 (2 ^ 63 - 3)) 2) lseek_model
        (Ok (mkEffect (Z_to_bv 64 (2 ^ 63 - 3)) [] []) m' evs) := by
  rw_refute

/-- …and one more wraps: `eof + offset` computed in `loff_t` under
`-fno-strict-overflow` is negative, `vfs_setpos_cookie`'s `offset < 0`
(fs/read_write.c:58-59, v6.18.46) answers -EINVAL, and the 2^63 a wider
sum would name is not a return.
kernel: fs/read_write.c:vfs_setpos_cookie,must_set_pos@v6.18.46 -/
theorem lseek_file_past_llong_max_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 (Z_to_bv 64 (2 ^ 63 - 2)) 2) lseek_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) lseek_model [] := by
  rw_norm

/-- SEEK_CUR reaches the same ceiling: fd 6 of `read_model` sits at offset
2 of "hi", so a displacement of 2^63 - 3 lands at 2^63 - 1 through
`generic_file_llseek_size`'s `vfs_setpos(file, file->f_pos + offset,
maxsize)` (fs/read_write.c:170-183, v6.18.46), which `vfs_setpos_cookie`'s
`offset > maxsize` (:60-61) lets through against tmpfs's
`MAX_LFS_FILESIZE`.  That ceiling is tmpfs's, and a filesystem with a
smaller `s_maxbytes` answers -EINVAL here, an answer the arm does not yet
accept (bugs/lseek-destination-ceiling-is-tmpfs.md), so the pin is
one-way, as its SEEK_END twin is.
kernel: fs/read_write.c:generic_file_llseek_size,vfs_setpos_cookie; mm/shmem.c:shmem_file_llseek@v6.18.46 -/
theorem lseek_file_seek_cur_to_llong_max :
    syscall_spec (lseek_in 6 (Z_to_bv 64 (2 ^ 63 - 3)) 1) read_model
      (Ok (mkEffect (Z_to_bv 64 (2 ^ 63 - 1)) [] [])
          (with_fds (fd_insert read_fds 6 (.FdFile [102] (Z_to_bv 64 (2 ^ 63 - 1))))
            read_model) []) := by
  rw_norm

/-- …and not the displacement itself, 2^63 - 3, which a model reading the
origin as SEEK_SET would answer.  No filesystem gives it: the sum
`f_pos + offset` (fs/read_write.c:170-183, v6.18.46) is 2^63 - 1, which
tmpfs accepts and a smaller `s_maxbytes` refuses along with 2^63 - 3.
kernel: fs/read_write.c:generic_file_llseek_size@v6.18.46 -/
theorem lseek_file_seek_cur_to_llong_max_displacement_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 6 (Z_to_bv 64 (2 ^ 63 - 3)) 1) read_model
        (Ok (mkEffect (Z_to_bv 64 (2 ^ 63 - 3)) [] []) m' evs) := by
  rw_refute

/-- …and one more wraps: `f_pos + offset` is 2^63, negative as a `loff_t`,
and `vfs_setpos_cookie`'s `offset < 0` (fs/read_write.c:58-59, v6.18.46)
answers -EINVAL on every filesystem, the offset unmoved.
kernel: fs/read_write.c:generic_file_llseek_size,vfs_setpos_cookie@v6.18.46 -/
theorem lseek_file_seek_cur_past_llong_max_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 6 (Z_to_bv 64 (2 ^ 63 - 2)) 1) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- SEEK_SET to 2^63 is the sign bit: a negative `off_t`, -EINVAL.
kernel: fs/read_write.c:vfs_setpos_cookie@v6.18.46 -/
theorem lseek_seek_set_sign_bit_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 (Z_to_bv 64 (2 ^ 63)) 0) lseek_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) lseek_model [] := by
  rw_norm

/-- The offset is the full 64-bit `off_t`, not truncated like the fd and
the whence: SEEK_SET to 2^32 + 1 lands at 2^32 + 1.  One-way like the
two ceiling pins above: a filesystem whose `s_maxbytes` is below 2^32 + 1
answers -EINVAL (bugs/lseek-destination-ceiling-is-tmpfs.md).
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_offset_is_64_bits :
    syscall_spec (lseek_in 3 (Z_to_bv 64 (2 ^ 32 + 1)) 0) lseek_model
      (Ok (mkEffect (Z_to_bv 64 (2 ^ 32 + 1)) [] [])
          (with_fds (fd_insert lseek_fds 3 (.FdFile [102] (Z_to_bv 64 (2 ^ 32 + 1))))
            lseek_model) []) := by
  rw_norm

/-- …so the truncated 1 is refused.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_offset_truncation_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 3 (Z_to_bv 64 (2 ^ 32 + 1)) 0) lseek_model
        (Ok (mkEffect 1 [] []) m' evs) := by
  rw_refute

/-- The write-only kind seeks the same way: fd 4 of `read_model` holds
"j" for writing at offset 0, and SEEK_END reports 1, the entry staying
write-only.
kernel: fs/read_write.c:generic_file_llseek_size@v6.18.46 -/
theorem lseek_write_only_file_seek_end (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 4 0 2) read_model o ↔
      o = Ok (mkEffect 1 [] [])
             (with_fds (fd_insert read_fds 4 (.FdFileW [103] 1)) read_model) [] := by
  rw_norm

/-- …and does not turn it into a readable one.
kernel: fs/read_write.c:generic_file_llseek_size@v6.18.46 -/
theorem lseek_write_only_file_kind_preserved (evs : List event) :
    ¬ syscall_spec (lseek_in 4 0 2) read_model
        (Ok (mkEffect 1 [] [])
            (with_fds (fd_insert read_fds 4 (.FdFile [103] 1)) read_model) evs) := by
  rw_refute

/-- …and refuses a negative destination the same way: SEEK_SET to -1 on
the write-only fd is -EINVAL from `vfs_setpos_cookie`'s `offset < 0`
(fs/read_write.c:58-59, v6.18.46), reached through the same `llseek`
operation whatever the open mode, the entry unmoved.
kernel: fs/read_write.c:vfs_setpos_cookie@v6.18.46 -/
theorem lseek_write_only_negative_seek_set_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 4 (Z_to_bv 64 (-1)) 0) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …not the unsigned reading of -1, which no `off_t` ever is.
kernel: fs/read_write.c:vfs_setpos_cookie@v6.18.46 -/
theorem lseek_write_only_negative_seek_set_unsigned_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 4 (Z_to_bv 64 (-1)) 0) read_model
        (Ok (mkEffect (Z_to_bv 64 (2 ^ 64 - 1)) [] []) m' evs) := by
  rw_refute

/-- SEEK_DATA on the write-only file declines as it does on the readable
one: `shmem_file_llseek` (mm/shmem.c:3677-3686, v6.18.46) answers from the
filesystem's own notion of a hole whatever the open mode, so the 0 a
one-byte file with data at its start would report is not claimed.
kernel: mm/shmem.c:shmem_file_llseek@v6.18.46 -/
theorem lseek_write_only_file_seek_data_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 4 0 3) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- …and SEEK_HOLE likewise, and neither is -EBADF: `vfs_llseek` tests
only FMODE_LSEEK (fs/read_write.c:387-388, v6.18.46), which `do_dentry_open`
sets on every open whatever its access mode (fs/open.c:961, v6.18.46) and
takes back for a file with no `llseek` operation (:976-977); the file's own
`open` may clear it too (:964-965), and tmpfs's (`shmem_file_open`,
mm/shmem.c:2982-2986, v6.18.46) does not.
kernel: fs/read_write.c:vfs_llseek@v6.18.46 -/
theorem lseek_write_only_file_seek_hole_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 4 0 4) read_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The write-only kind reports its own offset: fd 31 of `write_model`
holds "hi" for writing at offset 1, and a zero SEEK_CUR answers `f_pos`
without moving it (`must_set_pos`, fs/read_write.c:115-118, v6.18.46).
kernel: fs/read_write.c:must_set_pos,generic_file_llseek_size@v6.18.46 -/
theorem lseek_write_only_file_tell (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 31 0 1) write_model o ↔
      o = Ok (mkEffect 1 [] [])
             (with_fds (fd_insert write_fds 31 (.FdFileW [102] 1)) write_model) [] := by
  rw_norm

/-- …not 0, the offset a fresh write-only open would have.
kernel: fs/read_write.c:must_set_pos@v6.18.46 -/
theorem lseek_write_only_file_tell_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 31 0 1) write_model (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …and SEEK_CUR by 1 moves it from 1 to 2 (`vfs_setpos(file, file->f_pos
+ offset, maxsize)`, fs/read_write.c:170-183, v6.18.46), the entry staying
write-only.
kernel: fs/read_write.c:generic_file_llseek_size@v6.18.46 -/
theorem lseek_write_only_file_seek_cur_forward (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 31 1 1) write_model o ↔
      o = Ok (mkEffect 2 [] [])
             (with_fds (fd_insert write_fds 31 (.FdFileW [102] 2)) write_model) [] := by
  rw_norm

/-- A path the file system does not hold declines, as it does for `read`:
`openat` never mints such a descriptor.
kernel: fs/read_write.c:vfs_llseek@v6.18.46 -/
theorem lseek_file_path_absent_declines (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 7 0 2) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- …and so does the write-only kind: fd 27 of `write_model` is a
write-only descriptor on a path the tables do not hold, which no modeled
`openat` mints either. The decline is the missing file's, not the kind's.
kernel: fs/read_write.c:vfs_llseek@v6.18.46 -/
theorem lseek_write_only_path_absent_declines (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 27 0 2) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- …and not -EBADF: the descriptor is open, so `ksys_lseek`'s
`CLASS(fd_pos, f)(fd)` finds it and `fd_empty` does not fire
(fs/read_write.c:396-398, v6.18.46); the model has no file to seek rather
than an errno to give.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_write_only_path_absent_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 27 0 2) write_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-! ### The devices, a directory, the pipes and the sockets -/

/-- `/dev/null` answers 0 for every accepted whence and moves nothing:
`null_lseek` (drivers/char/mem.c:561-564, v6.18.46) stores 0 in `f_pos`
and returns it, and the model keeps no position for the device.
kernel: drivers/char/mem.c:null_lseek@v6.18.46 -/
theorem lseek_devnull_is_zero (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 8 5 0) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …never the offset asked for.
kernel: drivers/char/mem.c:null_lseek@v6.18.46 -/
theorem lseek_devnull_offset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 8 5 0) read_model (Ok (mkEffect 5 [] []) m' evs) := by
  rw_refute

/-- …and a negative offset is no -EINVAL there: `null_lseek` never reads
`offset`, so SEEK_SET -1 is 0 like every other call — where a regular
file's `vfs_setpos_cookie` (fs/read_write.c:58-59, v6.18.46) refuses.
kernel: drivers/char/mem.c:null_lseek@v6.18.46 -/
theorem lseek_devnull_negative_offset_is_zero (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 8 (Z_to_bv 64 (-1)) 0) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …so the file's -EINVAL is refused on the device.
kernel: drivers/char/mem.c:null_lseek@v6.18.46 -/
theorem lseek_devnull_negative_offset_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 8 (Z_to_bv 64 (-1)) 0) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- SEEK_HOLE on `/dev/null` is 0 as well — `null_lseek` ignores the
whence.
kernel: drivers/char/mem.c:null_lseek@v6.18.46 -/
theorem lseek_devnull_seek_hole_is_zero (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 8 0 4) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …but whence 42 never reaches it: -EINVAL from `ksys_lseek`.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_devnull_bad_whence_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 8 0 42) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- The write-only `/dev/null` (fd 9) seeks the same: `FMODE_LSEEK` is
set by `do_dentry_open` (fs/open.c:961, v6.18.46) whatever the access
mode.
kernel: drivers/char/mem.c:null_lseek@v6.18.46 -/
theorem lseek_devnull_write_only_is_zero (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 9 5 2) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- `/dev/urandom`: `noop_llseek` (fs/read_write.c:324-327, v6.18.46),
installed by `urandom_fops` (drivers/char/random.c:1578), returns
`file->f_pos`, which nothing on this device ever moves from 0.
kernel: fs/read_write.c:noop_llseek@v6.18.46 -/
theorem lseek_urandom_is_zero (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 24 5 0) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …not the 5 asked for.
kernel: fs/read_write.c:noop_llseek@v6.18.46 -/
theorem lseek_urandom_offset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 24 5 0) read_model (Ok (mkEffect 5 [] []) m' evs) := by
  rw_refute

/-- …and a negative offset is 0 too: `noop_llseek` returns `f_pos` and
reads neither `offset` nor `whence`.
kernel: fs/read_write.c:noop_llseek@v6.18.46 -/
theorem lseek_urandom_negative_offset_is_zero (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 24 (Z_to_bv 64 (-1)) 0) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …so a regular file's -EINVAL is refused on the device.
kernel: fs/read_write.c:noop_llseek@v6.18.46 -/
theorem lseek_urandom_negative_offset_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 24 (Z_to_bv 64 (-1)) 0) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- SEEK_DATA on `/dev/urandom` is 0 too: `noop_llseek` reads no whence.
kernel: fs/read_write.c:noop_llseek@v6.18.46 -/
theorem lseek_urandom_seek_data_is_zero (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 24 0 3) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- A directory declines — the probe's `lseek(dirfd, 0, SEEK_CUR)`.  On
tmpfs a directory's `.llseek` is `offset_dir_llseek` (fs/libfs.c:433-448,
v6.18.46, in the `simple_offset_dir_operations` that `shmem_get_inode`
installs, mm/shmem.c:3138): SEEK_SET and SEEK_CUR reposition the
directory's cursor and every other whence is -EINVAL.  The model holds no
directory position, so it declines every whence the gate lets through
rather than answer any.
probe: testing/syscall-check/tests/dirfd_spec.c#fail-closed -- lseek -/
theorem lseek_dir_declines (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 5 0 1) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- …but its whence is still gated first: 42 is -EINVAL on a directory
too, before the kind is consulted.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_dir_bad_whence_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 5 0 42) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- SEEK_SET on the directory declines too: `offset_dir_llseek` repositions
the cursor the model does not hold (fs/libfs.c:433-448, v6.18.46).
kernel: fs/libfs.c:offset_dir_llseek@v6.18.46 -/
theorem lseek_dir_seek_set_declines (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 5 0 0) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- …and SEEK_END, SEEK_DATA and SEEK_HOLE, which tmpfs's
`offset_dir_llseek` answers -EINVAL (fs/libfs.c:433-448, v6.18.46) and
another filesystem's directory `llseek` answers otherwise, decline rather
than claim either.
kernel: fs/libfs.c:offset_dir_llseek@v6.18.46 -/
theorem lseek_dir_seek_end_declines (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 5 0 2) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- SEEK_DATA on the directory: a decline.
kernel: fs/libfs.c:offset_dir_llseek@v6.18.46 -/
theorem lseek_dir_seek_data_declines (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 5 0 3) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- SEEK_HOLE on the directory: a decline.
kernel: fs/libfs.c:offset_dir_llseek@v6.18.46 -/
theorem lseek_dir_seek_hole_declines (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 5 0 4) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- A pipe's read end: -ESPIPE.  Both ends come from `create_pipe_files`
(fs/pipe.c:944, :956, v6.18.46) through alloc_file_pseudo and
alloc_file_clone, whose `file_init_path` (fs/file_table.c:364-365,
v6.18.46) sets `FMODE_LSEEK` only for a table with an `.llseek` —
`pipeanon_fops` (fs/pipe.c:1257-1266) has none — and the stream_open
call at fs/pipe.c:966-967 clears the bit besides (`stream_open`,
fs/open.c:1658, v6.18.46).
kernel: fs/read_write.c:vfs_llseek; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem lseek_pipe_read_end_is_espipe (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 14 0 1) read_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model [] := by
  rw_norm

/-- …and its write end.
kernel: fs/read_write.c:vfs_llseek; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem lseek_pipe_write_end_is_espipe (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 15 0 2) read_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model [] := by
  rw_norm

/-- …with the whence gate ahead of it: 42 on a pipe end is -EINVAL, because
`ksys_lseek` compares `whence <= SEEK_MAX` (fs/read_write.c:401, v6.18.46)
before `vfs_llseek` reads the missing `FMODE_LSEEK`.  The last two
conjuncts of Rocq's `lseek_on_a_pipe_end_is_espipe_but_whence_wins`
(`Checks/Cases/Fs/Pipe.v`), stated on this file's pipe end; its -ESPIPE
conjuncts are the two pins above.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_pipe_bad_whence_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 14 0 42) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …so the kind's -ESPIPE is refused there.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_pipe_bad_whence_espipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (lseek_in 14 0 42) read_model
        (Ok (mkEffect (errno_ret ESPIPE) [] []) m' evs) := by
  rw_refute

/-- A socket: -ESPIPE, `sock_alloc_file` (net/socket.c:494, v6.18.46) opening
it through `stream_open` (fs/open.c:1656-1661, v6.18.46).
kernel: fs/read_write.c:vfs_llseek; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem lseek_socket_is_espipe (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 10 0 0) read_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model [] := by
  rw_norm

/-- …with the whence gate ahead of it: 99 on a socket is -EINVAL.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_socket_bad_whence_is_einval (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 10 0 99) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- A closed fd in `read_model` too: 30 is -EBADF.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_closed_fd_thirty_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 30 0 0) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-! ### The helpers, at their edges -/

/-- `lseek_base` picks the origin: 0, the current offset, the length.
kernel: fs/read_write.c:generic_file_llseek_size,must_set_pos@v6.18.46 -/
theorem lseek_base_seek_set : lseek_base 0 7 2 = some 0 := by decide

/-- …SEEK_CUR is the current offset…
kernel: fs/read_write.c:must_set_pos@v6.18.46 -/
theorem lseek_base_seek_cur : lseek_base 1 7 2 = some 7 := by decide

/-- …SEEK_END the length…
kernel: fs/read_write.c:must_set_pos@v6.18.46 -/
theorem lseek_base_seek_end : lseek_base 2 7 2 = some 2 := by decide

/-- …and SEEK_DATA has no origin the model knows.
kernel: mm/shmem.c:shmem_file_llseek@v6.18.46 -/
theorem lseek_base_seek_data_is_none : lseek_base 3 7 2 = none := by decide

/-- `lseek_dest` admits 2^63 - 1, `LLONG_MAX`…
kernel: fs/read_write.c:vfs_setpos_cookie@v6.18.46 -/
theorem lseek_dest_admits_llong_max :
    lseek_dest 2 (Z_to_bv 64 (2 ^ 63 - 3)) = some (Z_to_bv 64 (2 ^ 63 - 1)) := by decide

/-- …refuses 2^63…
kernel: fs/read_write.c:vfs_setpos_cookie@v6.18.46 -/
theorem lseek_dest_refuses_past_llong_max :
    lseek_dest 2 (Z_to_bv 64 (2 ^ 63 - 2)) = none := by decide

/-- …and refuses -1.
kernel: fs/read_write.c:vfs_setpos_cookie@v6.18.46 -/
theorem lseek_dest_refuses_negative : lseek_dest 0 (Z_to_bv 64 (-1)) = none := by decide


/-! ## pread64 (67) and pwrite64 (68): the fixtures and the call

`read` and `write` at a position the CALL names.  The pread pins run on
`read_model` and `urandom_model` — the same tables as `read`'s, so every
kind is one fd away and the two arms can be read side by side — and the
pwrite pins on Rocq's `readv_write_only_model`, the EMPTY file at path
102 held for writing through fd 3 at offset 0 and nothing else open, so
that a byte landing anywhere is visible and fd 5 is closed; the kinds it
lacks are taken from `write_model`.  The position is the fourth argument,
a3, the full 64-bit `loff_t`.

WHAT THE ARMS READ OFF THE KERNEL.  `ksys_pread64` (fs/read_write.c:752-766,
v6.18.46) and `ksys_pwrite64` (:782-796) test `pos < 0` FIRST (:755-756,
:785-786), above the `CLASS(fd, f)(fd)` declaration that fetches the
descriptor (:758, :788), then answer -EBADF on an empty slot (:759-760,
:789-790), then test `FMODE_PREAD` / `FMODE_PWRITE` (:762, :792) — bits
`do_dentry_open` sets on every path open (fs/open.c:961, v6.18.46) and
nothing sets on a pipe end or a socket, whose `alloc_file_pseudo` and
`alloc_file_clone` files (fs/file_table.c:464-475, v6.18.46) never pass
there (`file_init_path`, fs/file_table.c:356-377, sets neither), `stream_open` (fs/open.c:1658) clearing them besides, so every
channel, pipe and socket is
-ESPIPE (:765, :795) — and only then call `vfs_read` / `vfs_write` with
`&pos`, a pointer to their own parameter (:763, :793).  So the descriptor's
own offset never moves, the -EBADF of `vfs_read`'s `FMODE_READ` test
(:556-557) is reached only past the -ESPIPE, and `rw_verify_area`'s
`(loff_t)(pos + count) < 0` (:467-469) is reached from the position the
call names.  Past that point the two are `read` and `write`, and the pins
say only what the position changes; what the kinds answer is argued on
the `read` and `write` sections above and not repeated. -/

attribute [sys_simp low] pread64_spec.eq_1 pwrite64_spec.eq_1 ppos_einvalb.eq_1

/-- `pread64(fd, buf, count, pos)` as the dispatcher sees it: syscall 67,
the four arguments in a0..a3, nothing readable, `wmem` the writable view. -/
def pread_in (fd buf count pos : word) (wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 67 [fd, buf, count, pos, 0, 0] (fun _ => none) wmem

/-- `pwrite64(fd, buf, count, pos)`: syscall 68, `mem` the readable view,
nothing writable. -/
def pwrite_in (fd buf count pos : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 68 [fd, buf, count, pos, 0, 0] mem (fun _ => none)

/-- Rocq's `readv_write_only_model`: the empty file at path 102, held for
writing through fd 3 at offset 0, and nothing else open. -/
def write_only_fds : List (word × FdEntry) := [(3, .FdFileW [102] 0)]

def write_only_fs : Fs.Fs := [([102], [])]

def readv_write_only_model : Model := fixture_of (fds := write_only_fds) (fs := write_only_fs)

attribute [sys_simp low] pread_in.eq_1 pwrite_in.eq_1

/-! ### The negative position precedes the descriptor

`ksys_pread64` and `ksys_pwrite64` test `pos < 0` above the `CLASS(fd,
f)(fd)` declaration (fs/read_write.c:755-758 and :785-788, v6.18.46), so
the answer is -EINVAL WHATEVER the fd table holds.  The symbolic pin takes
no premise about the table at all, which is the whole content of the
ordering claim; the concrete ones instantiate it on a closed fd, where a
descriptor-first order would answer -EBADF, and on a channel, where it
would answer -ESPIPE. -/

/-- Rocq's `pwrite64_negative_pos_precedes_the_descriptor`: for EVERY fd,
buffer, count, input and model, a negative position is -EINVAL and the
model is untouched.  Stated over every outcome, so the -EBADF and the
-ESPIPE of the table's kinds are not among them.
rocq-twin: pwrite64_negative_pos_precedes_the_descriptor
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem pwrite64_negative_pos_precedes_the_descriptor (fd buf count pos : word)
    (i : SyscallInput) (m : Model) (hpos : bv_signed pos < 0) (o : outcome SyscallEffect) :
    pwrite64_spec fd buf count pos i m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  have hb : ppos_einvalb pos = true := by
    unfold ppos_einvalb; exact decide_eq_true hpos
  rw [pwrite64_spec.eq_1, hb]
  simp only [↓reduceIte]
  rw_norm

/-- …and the read direction, the same statement.
kernel: fs/read_write.c:ksys_pread64@v6.18.46 -/
theorem pread64_negative_pos_precedes_the_descriptor (fd buf count pos : word)
    (i : SyscallInput) (m : Model) (hpos : bv_signed pos < 0) (o : outcome SyscallEffect) :
    pread64_spec fd buf count pos i m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  have hb : ppos_einvalb pos = true := by
    unfold ppos_einvalb; exact decide_eq_true hpos
  rw [pread64_spec.eq_1, hb]
  simp only [↓reduceIte]
  rw_norm

/-- Rocq's `pwrite64_negative_pos_rejects_ebadf`, the accepting half: fd 5
is closed in `readv_write_only_model`, and pos -1 is -EINVAL there.
rocq-twin: pwrite64_negative_pos_rejects_ebadf
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- closed -/
theorem pwrite64_negative_pos_on_a_closed_fd_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 5 4096 2 (Z_to_bv 64 (-1)) mem_ab) readv_write_only_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model [] := by
  rw_norm

/-- …and the refusing half: -EBADF, a descriptor-first order's answer, is
refused.
rocq-twin: pwrite64_negative_pos_rejects_ebadf
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pwrite64:ret=-EBADF -- closed -/
theorem pwrite64_negative_pos_rejects_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 5 4096 2 (Z_to_bv 64 (-1)) mem_ab) readv_write_only_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The read direction on the closed fd: -EINVAL…
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- closed -/
theorem pread64_negative_pos_on_a_closed_fd_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pread_in 30 4096 4 (Z_to_bv 64 (-1)) wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …never -EBADF.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64:ret=-EBADF -- closed -/
theorem pread64_negative_pos_rejects_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 30 4096 4 (Z_to_bv 64 (-1)) wmem_none) read_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The same closed fd at pos 0 is -EBADF: the position passed, and the
slot is empty (fs/read_write.c:759-760, v6.18.46).
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- closed -/
theorem pread64_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (pread_in 30 4096 4 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …and not -EINVAL: only a negative position is.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64#2:ret=-EINVAL -- closed -/
theorem pread64_closed_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 30 4096 4 0 wmem_none) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- The write direction at pos 0 on the closed fd: -EBADF.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- closed -/
theorem pwrite64_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 5 4096 2 0 mem_ab) readv_write_only_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) readv_write_only_model [] := by
  rw_norm

/-- A negative position on an OPEN write-only file is -EINVAL too — the
probe's `pwrite64 #3`.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -/
theorem pwrite64_negative_pos_on_an_open_fd_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 2 (Z_to_bv 64 (-1)) mem_ab) readv_write_only_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model [] := by
  rw_norm

/-- …and -EBADF there is a lie a kernel with the tests reversed would tell.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pwrite64#3:ret=-EBADF -/
theorem pwrite64_negative_pos_on_an_open_fd_rejects_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 2 (Z_to_bv 64 (-1)) mem_ab) readv_write_only_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- On a channel the position still comes first: pos -1 on stdout is
-EINVAL, not the -ESPIPE the kind answers.
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem pwrite64_negative_pos_on_a_channel_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 1 4096 2 (Z_to_bv 64 (-1)) mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) write_model [] := by
  rw_norm

/-- …so the -ESPIPE is refused there.
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem pwrite64_negative_pos_on_a_channel_rejects_espipe (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 1 4096 2 (Z_to_bv 64 (-1)) mem_ab) write_model
        (Ok (mkEffect (errno_ret ESPIPE) [] []) m' evs) := by
  rw_refute

/-- The sign bit alone makes the position negative: 2^63 is -EINVAL on
the readable file, the probe's `pread64 #4` at a different negative.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -/
theorem pread64_sign_bit_pos_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 2 (Z_to_bv 64 (2 ^ 63)) (wmem_first 2)) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- `ppos_einvalb` at its edge: -1 is negative…
kernel: fs/read_write.c:ksys_pread64,ksys_pwrite64@v6.18.46 -/
theorem ppos_minus_one_is_negative : ppos_einvalb (Z_to_bv 64 (-1)) = true := by decide

/-- …2^63 is negative…
kernel: fs/read_write.c:ksys_pread64,ksys_pwrite64@v6.18.46 -/
theorem ppos_sign_bit_is_negative : ppos_einvalb (Z_to_bv 64 (2 ^ 63)) = true := by decide

/-- …and 2^63 - 1, `LLONG_MAX`, is not.
kernel: fs/read_write.c:ksys_pread64,ksys_pwrite64@v6.18.46 -/
theorem ppos_llong_max_is_not_negative : ppos_einvalb (Z_to_bv 64 (2 ^ 63 - 1)) = false := by
  decide

/-! ### `FMODE_PREAD` / `FMODE_PWRITE`: -ESPIPE ahead of the kind's own verdict

A pipe end or a socket never holds either bit: `do_dentry_open`
(fs/open.c:961, v6.18.46) sets them on a path open, and a pipe end or a
socket is an alloc_file_pseudo file (`create_pipe_files`, fs/pipe.c:944;
`sock_alloc_file`, net/socket.c:483) or, for a pipe's read end, an
`alloc_file_clone` one (fs/pipe.c:956; fs/file_table.c:464-475), whose
`file_init_path`
(fs/file_table.c:356-377, v6.18.46) sets neither — and the `stream_open`
(fs/open.c:1658, v6.18.46) both run, at fs/pipe.c:966-967 and
net/socket.c:494, clears them besides — and the tracer's stdio channels
are pipes.  `ksys_pread64` tests the bit (fs/read_write.c:762, v6.18.46)
before `vfs_read` can test `FMODE_READ` (:556-557), so the write end of a
pipe — -EBADF to `read` — is -ESPIPE to `pread64`; the pipe pins are
that ordering on the `read_model` pipe at fds 14 and 15. -/

/-- Rocq's `pread64_pipe_end_is_espipe`: for EVERY fd holding either end
of a pipe, every buffer and count, every input, and every non-negative
position, pread64 is -ESPIPE and the model is untouched.  Stated over
every outcome, so `vfs_read`'s -EBADF on the write end is not among them.
rocq-twin: pread64_pipe_end_is_espipe
kernel: fs/read_write.c:ksys_pread64; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem pread64_pipe_end_is_espipe (fd buf count pos : word) (i : SyscallInput) (m : Model)
    (id : word) (w : Bool) (hpos : 0 ≤ bv_signed pos)
    (hfd : fd_lookup (m_fds m) fd = some (.FdPipe id w)) (o : outcome SyscallEffect) :
    pread64_spec fd buf count pos i m o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) m [] := by
  have hb : ppos_einvalb pos = false := by
    unfold ppos_einvalb; exact decide_eq_false (Int.not_lt.mpr hpos)
  rw [pread64_spec.eq_1, hb]
  simp only [Bool.false_eq_true, ↓reduceIte, bind_input_iff, bind_get_model_iff, hfd]
  rw_norm

/-- The write end concretely (fd 15 of `read_model`): -ESPIPE…
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- pipe -/
theorem pread64_pipe_write_end_is_espipe (o : outcome SyscallEffect) :
    syscall_spec (pread_in 15 4096 4 0 (wmem_first 4)) read_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model [] := by
  rw_norm

/-- …not the -EBADF `read` answers on that same descriptor.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64#2:ret=-EBADF -- pipe -/
theorem pread64_pipe_write_end_rejects_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 15 4096 4 0 (wmem_first 4)) read_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The read end too, its two bytes undelivered.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- pipe -/
theorem pread64_pipe_read_end_is_espipe (o : outcome SyscallEffect) :
    syscall_spec (pread_in 14 4096 4 0 (wmem_first 4)) read_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model [] := by
  rw_norm

/-- pwrite64 on the pipe's READ end: -ESPIPE…
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- pipe -/
theorem pwrite64_pipe_read_end_is_espipe (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 14 4096 2 0 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) write_model [] := by
  rw_norm

/-- …not `vfs_write`'s -EBADF.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pwrite64:ret=-EBADF -- pipe -/
theorem pwrite64_pipe_read_end_rejects_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 14 4096 2 0 mem_ab) write_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- …and the write end, nothing appended to the pipe.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- pipe -/
theorem pwrite64_pipe_write_end_is_espipe (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 15 4096 2 0 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) write_model [] := by
  rw_norm

/-- A channel: pread64 of stdin is -ESPIPE, the declared stream untouched.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- chan -/
theorem pread64_channel_is_espipe (b c d e f : byte) (o : outcome SyscallEffect) :
    syscall_spec (pread_in 0 4096 4 0 (wmem_first 4)) (stdin_model (hello b c d e f)) o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) (stdin_model (hello b c d e f)) [] := by
  rw_norm

/-- …never end-of-file.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64:ret=0 -- chan -/
theorem pread64_channel_zero_rejected (b c d e f : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 0 4096 4 0 (wmem_first 4)) (stdin_model (hello b c d e f))
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- pwrite64 of stdout: -ESPIPE, no event.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- chan -/
theorem pwrite64_channel_is_espipe (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 1 4096 5 0 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) write_model [] := by
  rw_norm

/-- …and no transfer: the probe's five-byte count is refused.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pwrite64:ret=5 -- chan -/
theorem pwrite64_channel_transfer_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 1 4096 5 0 mem_ab) write_model (Ok (mkEffect 5 [] []) m' evs) := by
  rw_refute

/-- …nor a delivery event.
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem pwrite64_channel_event_rejected (m' : Model) :
    ¬ syscall_spec (pwrite_in 1 4096 5 0 mem_ab) write_model
        (Ok (mkEffect (errno_ret ESPIPE) [] []) m' [WriteEv 1 97]) := by
  rw_refute

/-- A socket is -ESPIPE in both directions: fd 10 of `read_model`
(`SkFresh`) for pread64…
kernel: fs/read_write.c:ksys_pread64; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem pread64_socket_is_espipe (o : outcome SyscallEffect) :
    syscall_spec (pread_in 10 4096 4 0 (wmem_first 4)) read_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model [] := by
  rw_norm

/-- …and for pwrite64.
kernel: fs/read_write.c:ksys_pwrite64; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem pwrite64_socket_is_espipe (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 10 4096 2 0 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret ESPIPE) [] []) write_model [] := by
  rw_norm

/-! ### `vfs_read` / `vfs_write`: the mode, then the range, then the position

Past the `FMODE_PREAD` / `FMODE_PWRITE` gate the regular-file kinds keep
both bits, so `vfs_read` tests `FMODE_READ` (fs/read_write.c:556-557,
v6.18.46) and `vfs_write` `FMODE_WRITE` (:670-671) — -EBADF on the
write-only file for pread64 and on the read-only one for pwrite64 — then
`access_ok` on the count the call named (:560-561, :674-675), then
`rw_verify_area` (:563-565, :677-679), whose `(loff_t)(pos + count) < 0`
is -EINVAL (:467-469) from the position the call names. -/

/-- pread64 of the write-only file (fd 4 of `read_model`): -EBADF from
`vfs_read`'s `FMODE_READ` test, past the `FMODE_PREAD` gate the file
keeps.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -/
theorem pread64_write_only_file_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (pread_in 4 4096 4 0 (wmem_first 4)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …not end-of-file.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64:ret=0 -/
theorem pread64_write_only_file_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 4 4096 4 0 (wmem_first 4)) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …and the mode is tested before the buffer: a range one past the top
on the write-only file is still -EBADF (the probe's `big` mode).
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- big -/
theorem pread64_write_only_file_mode_precedes_the_range (o : outcome SyscallEffect) :
    syscall_spec (pread_in 4 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …so -EFAULT there is buffer-first ordering, refused.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64#2:ret=-EFAULT -- big -/
theorem pread64_write_only_file_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 4 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- pwrite64 of the read-only file (fd 3 of `write_model`): -EBADF from
`vfs_write`'s `FMODE_WRITE` test — the probe's `pwrite64 #4`.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -/
theorem pwrite64_read_only_file_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 2 0 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- …with no byte written: the two-byte transfer is refused.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_read_only_file_transfer_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 2 0 mem_ab) write_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-- A directory: pread64 reaches `vfs_read` (fs/read_write.c:552-581,
v6.18.46) and `generic_read_dir` (fs/libfs.c:224-227, v6.18.46) answers
-EISDIR — the directory keeps
`FMODE_PREAD`.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- dir -/
theorem pread64_dir_is_eisdir (o : outcome SyscallEffect) :
    syscall_spec (pread_in 5 4096 4 0 (wmem_first 4)) read_model o ↔
      o = Ok (mkEffect (errno_ret EISDIR) [] []) read_model [] := by
  rw_norm

/-- …not the -ESPIPE of a directory that had lost the bit.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64:ret=-ESPIPE -- dir -/
theorem pread64_dir_espipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 5 4096 4 0 (wmem_first 4)) read_model
        (Ok (mkEffect (errno_ret ESPIPE) [] []) m' evs) := by
  rw_refute

/-- …and its range is tested first: `pread64(dirfd, 0, 2^47 + 1, 0)` is
-EFAULT ahead of -EISDIR.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- big -/
theorem pread64_dir_range_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pread_in 5 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …and so is its position: count 1 at `LLONG_MAX` is `rw_verify_area`'s
-EINVAL, ahead of -EISDIR.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_dir_pos_past_llong_max_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pread_in 5 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1)) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …with a bad range too, -EFAULT wins on the directory: `vfs_read`'s
access_ok test (fs/read_write.c:560-561) precedes its `rw_verify_area`
call (:563-565), on every kind it reaches.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_dir_range_precedes_the_position (o : outcome SyscallEffect) :
    syscall_spec (pread_in 5 (Z_to_bv 64 (2 ^ 63)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …so the position test's -EINVAL is refused there.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_dir_range_precedes_the_position_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 5 (Z_to_bv 64 (2 ^ 63)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        read_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- `count = -1` on the directory is -EFAULT as on a file: `size <= TASK_SIZE`
fails in `__access_ok` (include/asm-generic/access_ok.h:31-41, v6.18.46,
behind riscv's `access_ok`, arch/riscv/include/asm/uaccess.h:42) before
`rw_verify_area`'s `(ssize_t) count < 0` (fs/read_write.c:456-457) could
answer -EINVAL, and before -EISDIR.
kernel: fs/read_write.c:vfs_read; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pread64_dir_negative_count_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pread_in 5 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …and its -EINVAL is refused.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_dir_negative_count_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 5 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 wmem_none) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- pwrite64 of a directory is `vfs_write`'s -EBADF: the directory was
opened read-only, and `FMODE_WRITE` is tested before anything else.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- dir -/
theorem pwrite64_dir_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 5 4096 2 0 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- …never -EISDIR, which write(2) on a directory does not give.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pwrite64:ret=-EISDIR -- dir -/
theorem pwrite64_dir_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 5 4096 2 0 mem_ab) write_model
        (Ok (mkEffect (errno_ret EISDIR) [] []) m' evs) := by
  rw_refute

/-- `/dev/urandom` was opened for reading: pwrite64 is -EBADF.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_urandom_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 24 4096 2 0 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- The read-only `/dev/null` (fd 8) for pwrite64: -EBADF…
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_devnull_read_only_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 8 4096 2 0 mem_ab) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- …ahead of the buffer: with a range past the top as well, -EBADF wins,
`vfs_write`'s `FMODE_WRITE` test (fs/read_write.c:670-671, v6.18.46)
running before its `access_ok` (:674-675).
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_devnull_read_only_precedes_the_range (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 8 (Z_to_bv 64 (2 ^ 63)) 8 0 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] := by
  rw_norm

/-- …so -EFAULT, the buffer-first order's answer, is refused.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_devnull_read_only_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 8 (Z_to_bv 64 (2 ^ 63)) 8 0 mem_none) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- …and the write-only one (fd 9) for pread64.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_devnull_write_only_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (pread_in 9 4096 4 0 (wmem_first 4)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …ahead of the buffer: with a range past the top as well, -EBADF wins,
`vfs_read`'s `FMODE_READ` test (fs/read_write.c:556-557, v6.18.46)
running before its `access_ok` (:560-561) — the order the probe's `big`
mode pins on a write-only file and `devnull_write_only_ebadf_beats_efault`
pins for `read`.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_devnull_write_only_precedes_the_range (o : outcome SyscallEffect) :
    syscall_spec (pread_in 9 (Z_to_bv 64 (2 ^ 63)) 8 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …so -EFAULT, the buffer-first order's answer, is refused.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_devnull_write_only_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 9 (Z_to_bv 64 (2 ^ 63)) 8 0 wmem_none) read_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-! ### /dev/null: the position is checked and then ignored

`read_null` (drivers/char/mem.c:412-416, v6.18.46) returns 0 and
`write_null` (:418-422) returns `count` whatever `*ppos` holds, but both
sit behind `vfs_read` / `vfs_write`'s `access_ok` and `rw_verify_area`,
so a range past the top is -EFAULT and `pos + count` past `LLONG_MAX` is
-EINVAL before the device is reached; a count of 0 at `LLONG_MAX` passes
both and answers 0. -/

/-- pread64 of `/dev/null` at position 5: 0, nothing written.
kernel: drivers/char/mem.c:read_null@v6.18.46 -/
theorem pread64_devnull_is_zero (o : outcome SyscallEffect) :
    syscall_spec (pread_in 8 4096 8 5 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …not a delivery.
kernel: drivers/char/mem.c:read_null@v6.18.46 -/
theorem pread64_devnull_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 8 4096 8 5 wmem_none) read_model
        (Ok (mkEffect 2 [(4096, [0, 0])] []) m' evs) := by
  rw_refute

/-- A range past the top on `/dev/null` is -EFAULT ahead of the device.
kernel: fs/read_write.c:vfs_read; drivers/char/mem.c:read_null@v6.18.46 -/
theorem pread64_devnull_range_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pread_in 8 (Z_to_bv 64 (2 ^ 63)) 8 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- `count = -1` on `/dev/null` is -EFAULT too: `__access_ok`'s
`size <= TASK_SIZE` (include/asm-generic/access_ok.h:31-41, v6.18.46)
fails at fs/read_write.c:560-561, before `rw_verify_area`'s
`(ssize_t) count < 0` (:456-457) and before `read_null`.
kernel: fs/read_write.c:vfs_read; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pread64_devnull_negative_count_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pread_in 8 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …and its -EINVAL is refused.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_devnull_negative_count_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 8 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 wmem_none) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- Count 1 at `LLONG_MAX` on `/dev/null`: `rw_verify_area`'s -EINVAL
(fs/read_write.c:467-469, v6.18.46), ahead of `read_null`'s 0.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_devnull_pos_past_llong_max_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pread_in 8 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …with a bad range too, -EFAULT wins: `access_ok`
(`__access_ok`, include/asm-generic/access_ok.h:31-41, v6.18.46) at fs/read_write.c:560-561
precedes `rw_verify_area` (fs/read_write.c:451-478, v6.18.46), called at
:563-565.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_devnull_range_precedes_the_position (o : outcome SyscallEffect) :
    syscall_spec (pread_in 8 (Z_to_bv 64 (2 ^ 63)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- Count 0 at `LLONG_MAX`: the sum stays at `LLONG_MAX`, and `read_null`
answers 0.
kernel: fs/read_write.c:rw_verify_area; drivers/char/mem.c:read_null@v6.18.46 -/
theorem pread64_devnull_zero_count_at_llong_max_is_zero (o : outcome SyscallEffect) :
    syscall_spec (pread_in 8 4096 0 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- pwrite64 of `/dev/null` (fd 9) at position 3: the count comes back
and the source is never read.
kernel: drivers/char/mem.c:write_null@v6.18.46 -/
theorem pwrite64_devnull_swallows_the_count (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 9 4096 5 3 mem_none) write_model o ↔
      o = Ok (mkEffect 5 [] []) write_model [] := by
  rw_norm

/-- …with no ledger…
kernel: drivers/char/mem.c:write_null@v6.18.46 -/
theorem pwrite64_devnull_reads_no_source (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 9 4096 5 3 mem_none) write_model
        (Ok (with_copyins [(4096, 5)] (mkEffect 5 [] [])) m' evs) := by
  rw_refute

/-- …and no -EFAULT for the unreadable source.
kernel: drivers/char/mem.c:write_null@v6.18.46 -/
theorem pwrite64_devnull_is_not_efault (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 9 4096 5 3 mem_none) write_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw_refute

/-- A range past the top on the write-only `/dev/null` is -EFAULT ahead
of the device, as for `pread64`: `access_ok`
(`__access_ok`, include/asm-generic/access_ok.h:31-41, v6.18.46) at fs/read_write.c:674-675
in `vfs_write` runs before `write_null`.
kernel: fs/read_write.c:vfs_write; drivers/char/mem.c:write_null@v6.18.46 -/
theorem pwrite64_devnull_range_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 9 (Z_to_bv 64 (2 ^ 63)) 8 0 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- …not the count the device would otherwise swallow.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_devnull_range_past_top_count_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 9 (Z_to_bv 64 (2 ^ 63)) 8 0 mem_none) write_model
        (Ok (mkEffect 8 [] []) m' evs) := by
  rw_refute

/-- `count = -1` on `/dev/null` is -EFAULT: `__access_ok`'s
`size <= TASK_SIZE` (include/asm-generic/access_ok.h:31-41, v6.18.46)
fails at fs/read_write.c:674-675, before `rw_verify_area`'s
`(ssize_t) count < 0` (:456-457) and before `write_null` could swallow it.
kernel: fs/read_write.c:vfs_write; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pwrite64_devnull_negative_count_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- …and its -EINVAL is refused.
kernel: fs/read_write.c:vfs_write,rw_verify_area@v6.18.46 -/
theorem pwrite64_devnull_negative_count_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 mem_none) write_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- A count over `MAX_RW_COUNT` comes back clamped: `vfs_write`
(fs/read_write.c:680-681, v6.18.46) before `write_null`.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_devnull_clamps_to_max_rw_count (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 40)) 0 mem_none) write_model o ↔
      o = Ok (mkEffect (Z_to_bv 64 0x7ffff000) [] []) write_model [] := by
  rw_norm

/-- Count 1 at `LLONG_MAX` on the write-only `/dev/null`: -EINVAL.
kernel: fs/read_write.c:vfs_write,rw_verify_area@v6.18.46 -/
theorem pwrite64_devnull_pos_past_llong_max_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 9 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none) write_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) write_model [] := by
  rw_norm

/-- …with a bad range too, -EFAULT wins on the device: `access_ok` at
fs/read_write.c:674-675 precedes `rw_verify_area` at :677-679.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_devnull_range_precedes_the_position (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 9 (Z_to_bv 64 (2 ^ 63)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none)
        write_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := by
  rw_norm

/-- …so the position test's -EINVAL is refused there.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_devnull_range_precedes_the_position_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 9 (Z_to_bv 64 (2 ^ 63)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none)
        write_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- …and count 0 there is 0.
kernel: fs/read_write.c:rw_verify_area; drivers/char/mem.c:write_null@v6.18.46 -/
theorem pwrite64_devnull_zero_count_at_llong_max_is_zero (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 9 4096 0 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none) write_model o ↔
      o = Ok (mkEffect 0 [] []) write_model [] := by
  rw_norm

/-- /dev/null opened for reading AND writing (fd 3). -/
def devnull_rdwr_model : Model := fixture_of (fds := [(3, .FdDevNull true true)])

/-- A read-write /dev/null passes `vfs_read`'s `FMODE_READ` test
(fs/read_write.c:556-557, v6.18.46) and `read_null` answers 0
(drivers/char/mem.c:412-416, v6.18.46).
kernel: fs/read_write.c:vfs_read; drivers/char/mem.c:read_null@v6.18.46 -/
theorem pread64_devnull_read_write_is_zero (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 8 5 (wmem_first 8)) devnull_rdwr_model o ↔
      o = Ok (mkEffect 0 [] []) devnull_rdwr_model [] := by
  rw_norm

/-- …not the -EBADF of a write-only one.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_devnull_read_write_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 3 4096 8 5 (wmem_first 8)) devnull_rdwr_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- …and passes `vfs_write`'s `FMODE_WRITE` test (fs/read_write.c:670-671,
v6.18.46), where `write_null` swallows the count (drivers/char/mem.c:418-422,
v6.18.46).
kernel: fs/read_write.c:vfs_write; drivers/char/mem.c:write_null@v6.18.46 -/
theorem pwrite64_devnull_read_write_swallows_the_count (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 2 3 mem_ab) devnull_rdwr_model o ↔
      o = Ok (mkEffect 2 [] []) devnull_rdwr_model [] := by
  rw_norm

/-- …not the -EBADF of a read-only one.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_devnull_read_write_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 2 3 mem_ab) devnull_rdwr_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-! ### /dev/urandom: the one field a pread may move

`urandom_read_iter` (drivers/char/random.c, v6.18.46) reads no position
and draws from the generator whatever `*ppos` holds, so a pread64 of the
device delivers the declared stream's next bytes exactly as `read` does
and leaves `m_urandom` at the remainder — the one thing about the model a
positional read changes. -/

/-- pread64 of `/dev/urandom` at position 7 delivers the stream's two
bytes and advances it, exactly as `read` of the same count would.
kernel: drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem pread64_urandom_delivers_and_advances (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (pread_in 24 4096 2 7 (wmem_first 2)) (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect 2 [(4096, [b, c])] []) (urandom_model IEof) [] := by
  rw_norm

/-- …so a post-state whose stream still holds the two bytes is refused.
kernel: drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem pread64_urandom_stream_unmoved_rejected (b c : byte) (evs : List event) :
    ¬ syscall_spec (pread_in 24 4096 2 7 (wmem_first 2)) (urandom_model (ICons b (ICons c IEof)))
        (Ok (mkEffect 2 [(4096, [b, c])] []) (urandom_model (ICons b (ICons c IEof))) evs) := by
  rw_norm
  intro h
  exact absurd h (ICons_ne_IEof b _)

/-- …and the range verdict precedes the device: -EFAULT with the stream
untouched.
kernel: fs/read_write.c:vfs_read; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem pread64_urandom_range_past_top_is_efault (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (pread_in 24 (Z_to_bv 64 (2 ^ 63)) 2 0 wmem_all)
        (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons b (ICons c IEof))) [] := by
  rw_norm

/-- …as does the position: count 1 at `LLONG_MAX` is -EINVAL there.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_urandom_pos_past_llong_max_is_einval (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (pread_in 24 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1))
        (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) (urandom_model (ICons b (ICons c IEof))) [] := by
  rw_norm

/-- …with a bad range too, -EFAULT wins, the stream untouched: `vfs_read`'s
access_ok test (fs/read_write.c:560-561) precedes its `rw_verify_area`
call (:563-565).
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_urandom_range_precedes_the_position (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (pread_in 24 (Z_to_bv 64 (2 ^ 63)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons b (ICons c IEof))) [] := by
  rw_norm

/-- …so the position test's -EINVAL is refused there.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_urandom_range_precedes_the_position_einval_rejected (b c : byte) (m' : Model)
    (evs : List event) :
    ¬ syscall_spec (pread_in 24 (Z_to_bv 64 (2 ^ 63)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (urandom_model (ICons b (ICons c IEof))) (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- `count = -1` on `/dev/urandom` is -EFAULT: `__access_ok`'s
`size <= TASK_SIZE` (include/asm-generic/access_ok.h:31-41, v6.18.46)
fails at fs/read_write.c:560-561, before `rw_verify_area`'s
`(ssize_t) count < 0` (:456-457) and before a byte of the stream moves.
kernel: fs/read_write.c:vfs_read; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pread64_urandom_negative_count_is_efault (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (pread_in 24 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 wmem_all)
        (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons b (ICons c IEof))) [] := by
  rw_norm

/-- …and its -EINVAL is refused.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_urandom_negative_count_einval_rejected (b c : byte) (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 24 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 wmem_all)
        (urandom_model (ICons b (ICons c IEof))) (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-! ### A regular file: the bytes at the NAMED position, the offset unmoved

`ksys_pread64` hands `vfs_read` the address of its own `pos` parameter
(fs/read_write.c:763, v6.18.46), so the advance `vfs_read` makes lands
in a stack slot the syscall discards: fd 3 of `read_model` stays at
offset 0 after every pin below, and the bytes delivered are the file's
at the position the call names, not at the descriptor's.  `file_read`
is the same reader `read` uses; what changes is whose position it is
given. -/

/-- pread64 of "hi" at position 1 delivers "i", the second byte: the
probe's `pread64 #3` reads five bytes at 6 and gets the file's tail.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -/
theorem pread64_file_at_the_named_position (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 100 1 (wmem_first 1)) read_model o ↔
      o = Ok (mkEffect 1 [(4096, [105])] []) read_model [] := by
  rw_norm

/-- …not "h", the byte at the descriptor's own offset 0: the position
argument is load-bearing.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64#3:arg3=0 -/
theorem pread64_file_head_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 3 4096 100 1 (wmem_first 1)) read_model
        (Ok (mkEffect 1 [(4096, [104])] []) m' evs) := by
  rw_refute

/-- …and the descriptor does not move: a post-state whose fd 3 sits at
offset 2 — the position plus the byte — is refused.
kernel: fs/read_write.c:ksys_pread64@v6.18.46 -/
theorem pread64_file_offset_advanced_rejected (evs : List event) :
    ¬ syscall_spec (pread_in 3 4096 100 1 (wmem_first 1)) read_model
        (Ok (mkEffect 1 [(4096, [105])] [])
            (with_fds (fd_insert read_fds 3 (.FdFile [102] 2)) read_model) evs) := by
  rw_refute

/-- The whole file at 0: both bytes, the model unchanged.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -/
theorem pread64_file_whole_at_zero (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 100 0 (wmem_first 2)) read_model o ↔
      o = Ok (mkEffect 2 [(4096, [104, 105])] []) read_model [] := by
  rw_norm

/-- …not end-of-file with nothing delivered…
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64#2:ret=0,drop-writes -/
theorem pread64_file_eof_claimed_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 3 4096 100 0 (wmem_first 2)) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …nor one byte more than the file holds…
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64#2:ret+1,grow-writes:1 -/
theorem pread64_file_over_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 3 4096 100 0 (wmem_first 2)) read_model
        (Ok (mkEffect 3 [(4096, [104, 105, 0])] []) m' evs) := by
  rw_refute

/-- …nor one byte fewer: the delivery is the file's tail from the
position, clamped by the count, exactly.
kernel: fs/read_write.c:vfs_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem pread64_file_short_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 3 4096 100 0 (wmem_first 2)) read_model
        (Ok (mkEffect 1 [(4096, [104])] []) m' evs) := by
  rw_refute

/-- The fd's OWN offset is not what is read from: fd 6 holds the same
file at offset 2, its end, and pread64 at position 0 still delivers
both bytes.
kernel: fs/read_write.c:ksys_pread64@v6.18.46 -/
theorem pread64_ignores_the_descriptor_offset (o : outcome SyscallEffect) :
    syscall_spec (pread_in 6 4096 100 0 (wmem_first 2)) read_model o ↔
      o = Ok (mkEffect 2 [(4096, [104, 105])] []) read_model [] := by
  rw_norm

/-- …where `read` on fd 6 would answer end-of-file: 0 is refused.
kernel: fs/read_write.c:ksys_pread64@v6.18.46 -/
theorem pread64_descriptor_offset_eof_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 6 4096 100 0 (wmem_first 2)) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- At end-of-file (position 2 of a two-byte file): 0, nothing written.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- eof -/
theorem pread64_file_at_eof_is_zero (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 8 2 (wmem_first 8)) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …and far past it (2^20): 0 as well.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- eof -/
theorem pread64_file_far_past_eof_is_zero (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 8 (Z_to_bv 64 (2 ^ 20)) (wmem_first 8)) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- Count 1 at `LLONG_MAX`: `pos + count` is 2^63, negative as `loff_t`,
and `rw_verify_area` answers -EINVAL (fs/read_write.c:467-469, v6.18.46)
before any byte is read — the probe's `pread64 #3` in `eof` mode.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- eof -/
theorem pread64_file_pos_past_llong_max_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1)) read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …not the end-of-file a reader that skipped the test would answer.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64#3:ret=0 -- eof -/
theorem pread64_file_pos_past_llong_max_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1)) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- Count 0 at `LLONG_MAX`: the sum is `LLONG_MAX` itself, not negative,
and the read past end-of-file is 0 — the probe's `pread64 #4`.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- eof -/
theorem pread64_file_zero_count_at_llong_max_is_zero (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 0 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- …and -EINVAL there is refused: the test is on the sum, not the position.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pread64#4:ret=-EINVAL -- eof -/
theorem pread64_file_zero_count_at_llong_max_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 3 4096 0 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- A range one past the top on the readable file: -EFAULT from
`access_ok` (`__access_ok`, include/asm-generic/access_ok.h:31-41,
v6.18.46) at fs/read_write.c:560-561, ahead of the transfer.  The probe's
`big` mode reaches this test on the directory and, in the write
direction, on a write-only file; on a readable file only the kernel is
cited.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_file_range_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_all) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …never end-of-file…
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_file_range_past_top_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 3 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_all) read_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- `count = -1` is -EFAULT on `pread64` as on `read`
(`stdin_negative_count_is_efault`): `size <= TASK_SIZE` fails in
`__access_ok` (include/asm-generic/access_ok.h:31-41, v6.18.46, behind
riscv's `access_ok`, arch/riscv/include/asm/uaccess.h:42) at
fs/read_write.c:560-561, before `rw_verify_area`'s `(ssize_t) count < 0`
(:456-457) could answer -EINVAL.
kernel: fs/read_write.c:vfs_read; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pread64_file_negative_count_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- …and the -EINVAL of `rw_verify_area` is refused: the range test is
ahead of it.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_file_negative_count_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 3 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 wmem_none) read_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- …while a range of exactly 2^47 at 0 passes, and the two bytes land
at address 0.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_file_range_at_top_is_judged (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 0 (Z_to_bv 64 (2 ^ 47)) 0 wmem_all) read_model o ↔
      o = Ok (mkEffect 2 [(0, [104, 105])] []) read_model [] := by
  rw_norm

/-- Range and position both bad: -EFAULT wins, `access_ok`
(`__access_ok`, include/asm-generic/access_ok.h:31-41, v6.18.46) at fs/read_write.c:560-561
before `rw_verify_area` (fs/read_write.c:451-478, v6.18.46), called at
:563-565.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_file_range_precedes_the_position (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 (Z_to_bv 64 (2 ^ 63)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_all)
        read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- An unwritable destination: -EFAULT, as for `read`.
kernel: mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem pread64_file_unwritable_destination_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 100 0 wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  rw_norm

/-- A hole inside the delivered prefix declines, as for `read`: the count
Linux answers is the copy routine's rounded progress.
kernel: mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem pread64_file_partial_destination_declines (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 100 0 (wmem_first 1)) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Count 0 at position 0: 0, the destination never inspected.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_file_zero_count_is_zero (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 0 0 wmem_none) read_model o ↔
      o = Ok (mkEffect 0 [] []) read_model [] := by
  rw_norm

/-- A path the file system does not hold declines, as for `read`: no run
reaches an `FdFile` over a path the image lacks — `openat` inserts the
path in the step that mints the descriptor — and the arm, which cannot
appeal to that invariant locally, fails closed rather than invent a file.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_file_path_absent_declines (o : outcome SyscallEffect) :
    syscall_spec (pread_in 7 4096 100 0 (wmem_first 2)) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- fd 2^32 + 3 is fd 3: `ksys_pread64`'s `unsigned int fd`
(fs/read_write.c:752, v6.18.46).
kernel: fs/read_write.c:ksys_pread64@v6.18.46 -/
theorem pread64_fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (pread_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 100 1 (wmem_first 1)) read_model o ↔
      o = Ok (mkEffect 1 [(4096, [105])] []) read_model [] := by
  rw_norm

/-- …and bit 31 survives it: fd 2^31 + 3 is a closed fd, -EBADF from the
lookup (fs/read_write.c:758-760, v6.18.46), not fd 3's byte.
kernel: fs/read_write.c:ksys_pread64@v6.18.46 -/
theorem pread64_bit31_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (pread_in (Z_to_bv 64 (2 ^ 31 + 3)) 4096 100 1 (wmem_first 1)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- …so the byte fd 3 holds at 1 is refused.
kernel: fs/read_write.c:ksys_pread64@v6.18.46 -/
theorem pread64_bit31_fd_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in (Z_to_bv 64 (2 ^ 31 + 3)) 4096 100 1 (wmem_first 1)) read_model
        (Ok (mkEffect 1 [(4096, [105])] []) m' evs) := by
  rw_refute

/-! ### A write-only file: the readable prefix lands at the NAMED position

`ksys_pwrite64` hands `vfs_write` its own `pos` (fs/read_write.c:793,
v6.18.46), `generic_perform_write` (mm/filemap.c:4244-4335) lands the
readable prefix of the source there — zero-filling the gap from the
file's end, as `write` does past end-of-file — and the descriptor's
offset does not move.  The empty file of `readv_write_only_model` makes
the position visible: two bytes at 4 leave a six-byte file whose first
four are zero. -/

/-- Rocq's `pwrite64_writes_at_the_named_position`, the accepting half:
"ab" at position 4 into the empty file leaves `[0, 0, 0, 0, 97, 98]`, the
ledger records the two-byte read, and fd 3 stays at offset 0.
rocq-twin: pwrite64_writes_at_the_named_position
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -/
theorem pwrite64_writes_at_the_named_position (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 2 4 mem_ab) readv_write_only_model o ↔
      o = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
             (with_fs (fs_set write_only_fs [102] [0, 0, 0, 0, 97, 98]) readv_write_only_model) [] := by
  rw_norm

/-- …and the refusing half: the same delivery with the return a write at
offset 0 into an empty file could not have made either — 1 for 2 is a
short write the arm does not allow.
rocq-twin: pwrite64_writes_at_the_named_position
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_short_return_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 2 4 mem_ab) readv_write_only_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-- …nor 0, a transfer that did not happen.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pwrite64:ret=0 -/
theorem pwrite64_zero_return_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 2 4 mem_ab) readv_write_only_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- …nor the bytes at the descriptor's offset 0.
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem pwrite64_at_the_descriptor_offset_rejected (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 2 4 mem_ab) readv_write_only_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
            (with_fs (fs_set write_only_fs [102] [97, 98]) readv_write_only_model) evs) := by
  rw_refute

/-- …nor an offset that moved: fd 3 at 6 is refused as the post-state.
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem pwrite64_offset_advanced_rejected (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 2 4 mem_ab) readv_write_only_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
            (with_fds (fd_insert write_only_fds 3 (.FdFileW [102] 6))
              (with_fs (fs_set write_only_fs [102] [0, 0, 0, 0, 97, 98]) readv_write_only_model)) evs) := by
  rw_norm
  intro h
  exact absurd (FdEntry.FdFileW.inj h).2 (by decide)

/-- The position is not the descriptor's: fd 31 of `write_model` holds
"hi" at offset 1, and pwrite64 of "a" at position 0 overwrites the "h",
leaving "ai" and the offset at 1.
kernel: fs/read_write.c:ksys_pwrite64; mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_ignores_the_descriptor_offset (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 31 4096 1 0 mem_a) write_model o ↔
      o = Ok (with_copyins [(4096, 1)] (mkEffect 1 [] []))
             (with_fs (fs_set write_fs [102] [97, 105]) write_model) [] := by
  rw_norm

/-- …where `write` on fd 31 would have left "ha": refused.
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem pwrite64_at_the_descriptor_offset_on_hi_rejected (evs : List event) :
    ¬ syscall_spec (pwrite_in 31 4096 1 0 mem_a) write_model
        (Ok (with_copyins [(4096, 1)] (mkEffect 1 [] []))
            (with_fs (fs_set write_fs [102] [104, 97]) write_model) evs) := by
  rw_refute

/-- Rocq's `pwrite64_over_rw_bytes_max_is_judged`, the accepting half: a
count one over the retired ceiling is JUDGED — a two-byte write, since
`mem_ab` maps two bytes and a regular-file write takes the readable
prefix — where the arm used to decline outright.  `vfs_write` clamps
only at `MAX_RW_COUNT` (fs/read_write.c:680-681, v6.18.46), and
`generic_perform_write` (mm/filemap.c:4290-4297) lands every readable
byte.  The probe moves all 131073 bytes; the fixture keeps two readable
so the normalizer can walk them.
rocq-twin: pwrite64_over_rw_bytes_max_is_judged
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- over -/
theorem pwrite64_over_rw_bytes_max_is_judged (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 mem_ab) readv_write_only_model o ↔
      o = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
             (with_fs (fs_set write_only_fs [102] [97, 98]) readv_write_only_model) [] := by
  rw_norm

/-- …and the refusing half: a SHORT write of one byte is refused, so the
accepting half is a claim about the only admissible answer.
rocq-twin: pwrite64_over_rw_bytes_max_is_judged
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_over_rw_bytes_max_short_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 mem_ab) readv_write_only_model
        (Ok (with_copyins [(4096, 1)] (mkEffect 1 [] [])) m' evs) := by
  rw_refute

/-- …as is a transfer capped at the retired bound…
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pwrite64:ret=RW_MAX -- over -/
theorem pwrite64_capped_at_the_retired_bound_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 mem_ab) readv_write_only_model
        (Ok (with_copyins [(4096, 2)] (mkEffect (Z_to_bv 64 rw_bytes_max) [] [])) m' evs) := by
  rw_refute

/-- …or one made without reading a user byte.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pwrite64:drop-copyins -- over -/
theorem pwrite64_over_rw_bytes_max_no_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 mem_ab) readv_write_only_model
        (Ok (mkEffect 2 [] []) m' evs) := by
  rw_refute

/-- An unmapped source at a count `access_ok` admits (2^20 at address 0,
into the EMPTY file at position 0): -EFAULT from the transfer, JUDGED
rather than declined now the count ceiling is gone — the probe's
`big-ok` mode.  `generic_perform_write` copies nothing and answers
-EFAULT under `if (!written)` (mm/filemap.c:4321-4332, v6.18.46).
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- big-ok -/
theorem pwrite64_unmapped_source_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 0 (Z_to_bv 64 (2 ^ 20)) 0 mem_none) readv_write_only_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model [] := by
  rw_norm

/-- …not a zero-byte transfer…
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pwrite64:ret=0 -- big-ok -/
theorem pwrite64_unmapped_source_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 0 (Z_to_bv 64 (2 ^ 20)) 0 mem_none) readv_write_only_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- …nor one capped at the retired bound.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pwrite64:ret=RW_MAX -- big-ok -/
theorem pwrite64_unmapped_source_capped_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 0 (Z_to_bv 64 (2 ^ 20)) 0 mem_none) readv_write_only_model
        (Ok (mkEffect (Z_to_bv 64 rw_bytes_max) [] []) m' evs) := by
  rw_refute

/-- A range one past the top: -EFAULT from `access_ok`
(`__access_ok`, include/asm-generic/access_ok.h:31-41, v6.18.46) at fs/read_write.c:674-675,
ahead of the transfer.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- big -/
theorem pwrite64_range_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 mem_none) readv_write_only_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model [] := by
  rw_norm

/-- …never a zero-byte transfer.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#reject --mutate pwrite64:ret=0 -- big -/
theorem pwrite64_range_past_top_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 mem_none) readv_write_only_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- `count = -1` is -EFAULT on `pwrite64` as on `write`: `size <= TASK_SIZE`
fails in `__access_ok` (include/asm-generic/access_ok.h:31-41, v6.18.46,
behind riscv's `access_ok`, arch/riscv/include/asm/uaccess.h:42) at
fs/read_write.c:674-675, before `rw_verify_area`'s `(ssize_t) count < 0`
(:456-457) could answer -EINVAL and before a byte is read.
kernel: fs/read_write.c:vfs_write; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pwrite64_file_negative_count_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 mem_none) readv_write_only_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model [] := by
  rw_norm

/-- …and the -EINVAL of `rw_verify_area` is refused: the range test is
ahead of it.
kernel: fs/read_write.c:vfs_write,rw_verify_area@v6.18.46 -/
theorem pwrite64_file_negative_count_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 mem_none) readv_write_only_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw_refute

/-- Count 1 at `LLONG_MAX`: `rw_verify_area`'s -EINVAL
(fs/read_write.c:467-469, v6.18.46), before any byte moves and before the
hole it would have opened is even considered.
kernel: fs/read_write.c:vfs_write,rw_verify_area@v6.18.46 -/
theorem pwrite64_pos_past_llong_max_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_ab) readv_write_only_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model [] := by
  rw_norm

/-- …with a bad range too, -EFAULT wins: `access_ok`
(`__access_ok`, include/asm-generic/access_ok.h:31-41, v6.18.46) at fs/read_write.c:674-675
precedes `rw_verify_area` (fs/read_write.c:451-478, v6.18.46), called at
:677-679.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_range_precedes_the_position (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 (Z_to_bv 64 (2 ^ 63)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_ab)
        readv_write_only_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model [] := by
  rw_norm

/-- Count 0 at `LLONG_MAX` on the write-only file: the sum does not pass
`LLONG_MAX`, `generic_write_checks_count` returns 0 (fs/read_write.c:1744-1745,
v6.18.46) and the empty file stays empty.
kernel: fs/read_write.c:rw_verify_area,generic_write_checks_count@v6.18.46 -/
theorem pwrite64_zero_count_at_llong_max_is_zero (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 0 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none) readv_write_only_model o ↔
      o = Ok (mkEffect 0 [] [])
             (with_fs (fs_set write_only_fs [102] []) readv_write_only_model) [] := by
  rw_norm

/-- A zero count at position 4 into the empty file: 0, no hole opened
(`generic_write_checks_count`, fs/read_write.c:1744-1745, v6.18.46), the
offset where it was.
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem pwrite64_zero_count_opens_no_hole (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 0 4 mem_ab) readv_write_only_model o ↔
      o = Ok (mkEffect 0 [] [])
             (with_fs (fs_set write_only_fs [102] []) readv_write_only_model) [] := by
  rw_norm

/-- …and even a zero-length source range claims a read that never
happened: the empty ledger entry is refused.
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem pwrite64_zero_count_rejects_zero_length_copyin (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 3 4096 0 4 mem_ab) readv_write_only_model
        (Ok (with_copyins [(4096, 0)] (mkEffect 0 [] [])) m' evs) := by
  rw_refute

/-- A zero count at a buffer past the top is still -EFAULT: `access_ok`
runs on the range whatever the count.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_zero_count_past_top_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 (Z_to_bv 64 (2 ^ 63)) 0 0 mem_none) readv_write_only_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model [] := by
  rw_norm

/-- The readable prefix stops at a hole in the source: "ab" of
`mem_hole`'s four bytes lands, the "c" past the hole does not.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_takes_the_readable_prefix (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 4 0 mem_hole) readv_write_only_model o ↔
      o = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
             (with_fs (fs_set write_only_fs [102] [97, 98]) readv_write_only_model) [] := by
  rw_norm

/-- A path the file system does not hold declines: fd 27 of `write_model`,
an `FdFileW` no `openat` can mint (it inserts the path in the same step),
so the arm fails closed rather than invent a file to write.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_file_path_absent_declines (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 27 4096 1 0 mem_a) write_model o ↔ o = Unmodeled := by
  rw_norm

/-- fd 2^32 + 3 is fd 3: `ksys_pwrite64`'s `unsigned int fd`
(fs/read_write.c:782, v6.18.46).
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem pwrite64_fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 2 4 mem_ab) readv_write_only_model o ↔
      o = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
             (with_fs (fs_set write_only_fs [102] [0, 0, 0, 0, 97, 98]) readv_write_only_model) [] := by
  rw_norm

/-- …and bit 31 survives it: fd 2^31 + 3 is a closed fd, -EBADF from the
lookup (fs/read_write.c:788-790, v6.18.46), and the file is untouched.
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem pwrite64_bit31_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in (Z_to_bv 64 (2 ^ 31 + 3)) 4096 2 4 mem_ab) readv_write_only_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) readv_write_only_model [] := by
  rw_norm

/-- …so the two-byte write fd 3 would take is refused.
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem pwrite64_bit31_fd_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in (Z_to_bv 64 (2 ^ 31 + 3)) 4096 2 4 mem_ab) readv_write_only_model
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' evs) := by
  rw_refute

/-! ### `rw_verify_area` reads the count the call named, not the clamped one

`vfs_read` and `vfs_write` call `rw_verify_area` on the count the call
passed (fs/read_write.c:563-565 and :677-679, v6.18.46) and clamp it to
`MAX_RW_COUNT` only afterwards (:566-567, :680-681).  So `pos + count` is
judged on the unclamped count: at position 2^63 - 2^31 a count of 2^32
passes 2^63 and is -EINVAL, where the clamped 0x7ffff000 would end at
2^63 - 4096 and be let through.  The position pins at `LLONG_MAX` with a
count of 1 cannot tell those two readings apart; these can.  Where the
buffer is wholly accessible, qemu-user's `lock_user`
(linux-user/syscall.c:12258-12261, :12275-12278, QEMU 11.1.1) passes and
the host call gives the same -EINVAL. -/

/-- /dev/null opened for reading (fd 8), a count of 2^32 at position
2^63 - 2^31: -EINVAL, the sum of the count the call named passing 2^63.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_devnull_unclamped_count_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pread_in 8 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_all)
        read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …not the 0 `read_null` would give had the clamped count been tested.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_devnull_unclamped_count_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 8 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_all)
        read_model (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- The same call on /dev/urandom (fd 24): -EINVAL, the stream untouched.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_urandom_unclamped_count_is_einval (b c : byte) (o : outcome SyscallEffect) :
    syscall_spec (pread_in 24 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_all)
        (urandom_model (ICons b (ICons c IEof))) o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) (urandom_model (ICons b (ICons c IEof))) [] := by
  rw_norm

/-- On the directory (fd 5): -EINVAL, `rw_verify_area` coming before
`generic_read_dir`'s -EISDIR (fs/libfs.c:224-227, v6.18.46).
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_dir_unclamped_count_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pread_in 5 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_all)
        read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …not -EISDIR.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_dir_unclamped_count_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 5 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_all)
        read_model (Ok (mkEffect (errno_ret EISDIR) [] []) m' evs) := by
  rw_refute

/-- On the regular file (fd 3): -EINVAL.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_file_unclamped_count_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_all)
        read_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  rw_norm

/-- …not the 0 of a position far past the end of "hi".
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem pread64_file_unclamped_count_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pread_in 3 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_all)
        read_model (Ok (mkEffect 0 [] []) m' evs) := by
  rw_refute

/-- /dev/null opened for writing (fd 9), the same count and position: -EINVAL
from `vfs_write` (fs/read_write.c:677-679, v6.18.46), whose position test
comes ahead of its clamp (:680-681).
kernel: fs/read_write.c:vfs_write,rw_verify_area@v6.18.46 -/
theorem pwrite64_devnull_unclamped_count_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) mem_below_top)
        write_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) write_model [] := by
  rw_norm

/-- …not the clamped count `write_null` would have swallowed.
kernel: fs/read_write.c:vfs_write,rw_verify_area@v6.18.46 -/
theorem pwrite64_devnull_unclamped_count_clamp_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) mem_below_top)
        write_model (Ok (mkEffect (Z_to_bv 64 MAX_RW_COUNT) [] []) m' evs) := by
  rw_refute

/-- The write-only file (fd 3 of `readv_write_only_model`) at the same
count and position admits Linux's -EINVAL, which `vfs_write` reaches
before the copy is attempted.  One-directional on purpose: the source is
unreadable so that a spec testing the clamped count evaluates cheaply
(it declines through `unreadable_source_past_eof`), and with an
unreadable source qemu-user's `lock_user` answers -EFAULT first
(linux-user/syscall.c:12275-12278, QEMU 11.1.1), an answer the arm does
not yet accept (bugs/read-write-transfer-answers-are-linux-order-not-qemu-user.md);
an `iff` here would pin that refusal.
kernel: fs/read_write.c:vfs_write,rw_verify_area@v6.18.46 -/
theorem pwrite64_file_unclamped_count_admits_einval :
    syscall_spec (pwrite_in 3 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) mem_none)
        readv_write_only_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model []) := by
  rw_norm

/-! ### The hole past end-of-file, and the one decline beyond Rocq's

Linux zero-fills from the file's end to the named position with no bound
of its own; the model walks that gap and stops at `rw_bytes_max`
(`modeled_file_gap`, the bound `Sys/Uaccess.lean` carries), exactly as
`write` does past end-of-file.  And the decline `write`'s twin makes
beyond Rocq's — a source with NO readable byte at a position past the
end — is made here too (`unreadable_source_past_eof`, tested after the
-EFAULT of the range and the -EINVAL of the position, and before the
-EFAULT it displaces): `generic_perform_write` faults in the source
page by page inside a loop that has already extended the file's size
when the copy comes up empty, so the kernel's answer there is not the
untouched file the arm would otherwise report.
bugs/write-file-past-eof-unreadable-source-answers-an-unchanged-file.md
records it for both calls: Rocq's `pwrite64_spec` answers the untouched
file too, and the entry closes only when both Rocq arms decline. -/

/-- One byte at position 2^63 - 2 into the empty file, from a source
with no readable byte: the position passes `rw_verify_area` (the sum is
`LLONG_MAX`), and what follows is a decline, not an answer — the
unreadable source past the end, tested ahead of the hole the model could
not walk.  The source is unreadable on purpose: a readable byte here
would make a spec with the hole guard removed build the 2^63-byte fill,
and a pin the tester cannot evaluate protects nothing; the hole guard
itself is pinned at the bound, below.
kernel: fs/read_write.c:rw_verify_area; mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_hole_far_past_eof_declines (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 2)) mem_none) readv_write_only_model o ↔
      o = Unmodeled := by
  rw_norm

/-- A hole one byte over the bound declines… the walk from the file's end
stops at `rw_bytes_max` (`modeled_file_gap`, the section header above).
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_hole_over_the_bound_declines (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 1 (Z_to_bv 64 (rw_bytes_max + 1)) mem_a) readv_write_only_model o ↔
      o = Unmodeled := by
  rw_norm

/-- …and the helper `pwrite64_spec` tests on `pos` admits a hole of
exactly the bound: a fact about `modeled_file_gap`, not a pwrite64 call.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_hole_at_the_bound_is_modeled :
    modeled_file_gap [] (Z_to_bv 64 rw_bytes_max) [97] = true := by
  decide

/-- An unreadable source at position 1 of the EMPTY file — one byte past
its end — declines: the decline beyond Rocq's, on the pwrite path.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_unreadable_source_past_eof_declines (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 1 1 mem_none) readv_write_only_model o ↔ o = Unmodeled := by
  rw_norm

/-- …while the same unreadable source AT the end (position 0 of the
empty file) is the judged -EFAULT: the decline is on the gap alone.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_unreadable_source_at_eof_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 1 0 mem_none) readv_write_only_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model [] := by
  rw_norm

/-- …and a READABLE byte at position 1 is judged: a hole of one zero,
then the byte.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_readable_byte_past_eof_zero_fills (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 1 1 mem_a) readv_write_only_model o ↔
      o = Ok (with_copyins [(4096, 1)] (mkEffect 1 [] []))
             (with_fs (fs_set write_only_fs [102] [0, 97]) readv_write_only_model) [] := by
  rw_norm

/-- The edge on a file that is not empty: "hi" through fd 4 of `wend_model`
(whose own offset, 3, is past the end), one unreadable byte at position 2,
exactly the end.  `shmem_write_end`'s `pos + copied > i_size`
(mm/shmem.c:3352-3353, v6.18.46) is false with `copied` 0, so the file is
untouched and the -EFAULT is every implementation's.
kernel: mm/filemap.c:generic_perform_write; mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem pwrite64_unreadable_source_at_the_end_of_hi_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 4 4096 1 2 mem_none) wend_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) wend_model [] := by
  rw_norm

/-- …while position 3, one past the end, declines, through fd 3 whose own
offset, 2, is exactly the end: the decline is on the position the call
names, not the descriptor's.
kernel: mm/filemap.c:generic_perform_write; mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem pwrite64_unreadable_source_past_the_end_of_hi_declines (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 1 3 mem_none) wend_model o ↔ o = Unmodeled := by
  rw_norm

/-- The position test comes before the decline: one byte at position
2^63 - 1 from an unreadable source admits `rw_verify_area`'s -EINVAL
(fs/read_write.c:467-469, v6.18.46), which Linux reaches before any byte
is copied, rather than declining as the same source past the end does at
a smaller position.  One-directional for the reason
`pwrite64_file_unclamped_count_admits_einval` gives: qemu-user answers
this unreadable source -EFAULT first.
kernel: fs/read_write.c:vfs_write,rw_verify_area@v6.18.46 -/
theorem pwrite64_position_test_precedes_the_decline :
    syscall_spec (pwrite_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none) readv_write_only_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model []) := by
  rw_norm

/-! ## The whole-surface twins

Three of Rocq's cases are not pins but lemmas over the relation, with
every fd kind, model, count, position and input free; in Rocq each walks
`check_pread64_complete_ok` / `check_pwrite64_complete_ok` and the
checker's arms.  The Lean checker has no completeness lemma to walk, so
each is proved on the spec itself by opening its gates one at a time —
`generalize` on every `match` discriminant and `cases` on every Bool
gate, the shape `Checks/Cases/Fs/File.lean`'s `dup_never_answers_a_held_fd`
uses, because `split at h` does not find an `if` or `match` that is
applied to the monad's arguments. -/

/-- Rocq's `pread64_leaves_the_model_alone`: whatever the descriptor, the
count, the position and the input, an `Ok` pread64 leaves the table, the
file image and stdin as they were and emits nothing.  `ksys_pread64` hands
`vfs_read` a stack copy of the call's own position (fs/read_write.c:763,
v6.18.46) — `&pos` is the local, not `&f.file->f_pos` — so no offset
moves; the one state a pread64 CAN change is the urandom stream, which is
why it is absent from the conjunction.
rocq-twin: pread64_leaves_the_model_alone
kernel: fs/read_write.c:ksys_pread64,vfs_read@v6.18.46 -/
theorem pread64_leaves_the_model_alone (fd buf count pos : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : pread64_spec fd buf count pos i m (Ok eff m' evs)) :
    m_fds m' = m_fds m ∧ m_fs m' = m_fs m ∧ m_stdin m' = m_stdin m ∧ evs = [] := by
  have bare : ∀ (e : SyscallEffect) (m0 : Model), Monad.pure e i m0 (Ok eff m' evs) →
      m_fds m0 = m_fds m → m_fs m0 = m_fs m → m_stdin m0 = m_stdin m →
      m_fds m' = m_fds m ∧ m_fs m' = m_fs m ∧ m_stdin m' = m_stdin m ∧ evs = [] := by
    intro e m0 he h1 h2 h3
    simp only [pure_iff, outcome.Ok.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    exact ⟨h1, h2, h3, rfl⟩
  unfold pread64_spec at h
  cases hb : ppos_einvalb pos with
  | true =>
    simp only [hb, ↓reduceIte, err_ret, ret_only] at h
    exact bare _ _ h rfl rfl rfl
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_input_iff, bind_get_model_iff] at h
    generalize fd_lookup (m_fds m) fd = l at h
    cases l with
    | none => simp only [err_ret, ret_only] at h; exact bare _ _ h rfl rfl rfl
    | some e =>
      cases e with
      | FdFileA p off => simp only [unmodeled_iff, reduceCtorEq] at h
      | FdFileRW p off => simp only [unmodeled_iff, reduceCtorEq] at h
      | FdChannel c => simp only [err_ret, ret_only] at h; exact bare _ _ h rfl rfl rfl
      | FdPipe id w => simp only [err_ret, ret_only] at h; exact bare _ _ h rfl rfl rfl
      | FdSocket sk => simp only [err_ret, ret_only] at h; exact bare _ _ h rfl rfl rfl
      | FdFileW p off => simp only [err_ret, ret_only] at h; exact bare _ _ h rfl rfl rfl
      | FdDevNull rd wr =>
        cases rd with
        | false =>
          simp only [Bool.not_false, ↓reduceIte, err_ret, ret_only] at h
          exact bare _ _ h rfl rfl rfl
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases ha : access_okb buf (bv_unsigned count) with
          | false =>
            simp only [ha, Bool.not_false, ↓reduceIte, err_ret, ret_only] at h
            exact bare _ _ h rfl rfl rfl
          | true =>
            simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            cases hp : rw_pos_einvalb pos (bv_unsigned count) with
            | true =>
              simp only [hp, ↓reduceIte, err_ret, ret_only] at h
              exact bare _ _ h rfl rfl rfl
            | false =>
              simp only [hp, Bool.false_eq_true, ↓reduceIte, ret_only] at h
              exact bare _ _ h rfl rfl rfl
      | FdDir =>
        cases ha : access_okb buf (bv_unsigned count) with
        | false =>
          simp only [ha, Bool.not_false, ↓reduceIte, err_ret, ret_only] at h
          exact bare _ _ h rfl rfl rfl
        | true =>
          simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hp : rw_pos_einvalb pos (bv_unsigned count) with
          | true =>
            simp only [hp, ↓reduceIte, err_ret, ret_only] at h
            exact bare _ _ h rfl rfl rfl
          | false =>
            simp only [hp, Bool.false_eq_true, ↓reduceIte, err_ret, ret_only] at h
            exact bare _ _ h rfl rfl rfl
      | FdUrandom =>
        cases ha : access_okb buf (bv_unsigned count) with
        | false =>
          simp only [ha, Bool.not_false, ↓reduceIte, err_ret, ret_only] at h
          exact bare _ _ h rfl rfl rfl
        | true =>
          simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hp : rw_pos_einvalb pos (bv_unsigned count) with
          | true =>
            simp only [hp, ↓reduceIte, err_ret, ret_only] at h
            exact bare _ _ h rfl rfl rfl
          | false =>
            simp only [hp, Bool.false_eq_true, ↓reduceIte, read_urandom] at h
            cases hz : w_is0 count with
            | true =>
              simp only [hz, ↓reduceIte, ret_only] at h
              exact bare _ _ h rfl rfl rfl
            | false =>
              simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
              generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = r1 at h
              cases r1 with
              | none => simp only [err_ret, ret_only] at h; exact bare _ _ h rfl rfl rfl
              | some _ =>
                simp only at h
                generalize stream_take_z (m_urandom m) (rw_count_clamp count) = r at h
                cases hlen : decide ((r.1.length : Int) = rw_count_clamp count) with
                | false =>
                  simp only [hlen, Bool.not_false, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
                | true =>
                  simp only [hlen, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
                  generalize read_bytes_map i.in_wmem buf (len_word r.1) = r2 at h
                  cases r2 with
                  | none => simp only [unmodeled_iff, reduceCtorEq] at h
                  | some _ =>
                    simp only [bind_set_urandom_iff] at h
                    exact bare _ _ h rfl rfl rfl
      | FdFile p off =>
        cases ha : access_okb buf (bv_unsigned count) with
        | false =>
          simp only [ha, Bool.not_false, ↓reduceIte, err_ret, ret_only] at h
          exact bare _ _ h rfl rfl rfl
        | true =>
          simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hp : rw_pos_einvalb pos (bv_unsigned count) with
          | true =>
            simp only [hp, ↓reduceIte, err_ret, ret_only] at h
            exact bare _ _ h rfl rfl rfl
          | false =>
            simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
            generalize fs_lookup (m_fs m) p = fl at h
            cases fl with
            | none => simp only [unmodeled_iff, reduceCtorEq] at h
            | some data =>
              simp only at h
              generalize read_bytes_map i.in_wmem buf
                (len_word (file_read data pos (Z_to_bv 64 (rw_count_clamp count)))) = r1 at h
              cases r1 with
              | some _ => simp only at h; exact bare _ _ h rfl rfl rfl
              | none =>
                generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = r2 at h
                cases r2 with
                | none => simp only [err_ret, ret_only] at h; exact bare _ _ h rfl rfl rfl
                | some _ => simp only [unmodeled_iff, reduceCtorEq] at h

/-- Rocq's `pread64_urandom_advances_the_stream`: on an fd holding
/dev/urandom, an `Ok` pread64 either leaves the stream alone (every
bare-return arm) or advances it by exactly the clamped count — the tail
`stream_take_z` leaves — never by any other amount.  `urandom_read_iter`
(drivers/char/random.c:1453, v6.18.46) ignores the position and draws the
requested bytes from the generator, so the position is no index into the
stream.
rocq-twin: pread64_urandom_advances_the_stream
kernel: drivers/char/random.c:urandom_read_iter,get_random_bytes_user@v6.18.46 -/
theorem pread64_urandom_advances_the_stream (fd buf count pos : word) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hfd : fd_lookup (m_fds m) fd = some .FdUrandom)
    (h : pread64_spec fd buf count pos i m (Ok eff m' evs)) :
    m_urandom m' = m_urandom m ∨
      m_urandom m' = (stream_take_z (m_urandom m) (rw_count_clamp count)).2 := by
  have bare : ∀ (e : SyscallEffect), Monad.pure e i m (Ok eff m' evs) →
      m_urandom m' = m_urandom m := by
    intro e he
    simp only [pure_iff, outcome.Ok.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    rfl
  unfold pread64_spec at h
  cases hb : ppos_einvalb pos with
  | true =>
    simp only [hb, ↓reduceIte, err_ret, ret_only] at h
    exact Or.inl (bare _ h)
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_input_iff, bind_get_model_iff, hfd] at h
    cases ha : access_okb buf (bv_unsigned count) with
    | false =>
      simp only [ha, Bool.not_false, ↓reduceIte, err_ret, ret_only] at h
      exact Or.inl (bare _ h)
    | true =>
      simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hp : rw_pos_einvalb pos (bv_unsigned count) with
      | true =>
        simp only [hp, ↓reduceIte, err_ret, ret_only] at h
        exact Or.inl (bare _ h)
      | false =>
        simp only [hp, Bool.false_eq_true, ↓reduceIte, read_urandom] at h
        cases hz : w_is0 count with
        | true =>
          simp only [hz, ↓reduceIte, ret_only] at h
          exact Or.inl (bare _ h)
        | false =>
          simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
          generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = r1 at h
          cases r1 with
          | none => simp only [err_ret, ret_only] at h; exact Or.inl (bare _ h)
          | some _ =>
            simp only at h
            generalize stream_take_z (m_urandom m) (rw_count_clamp count) = r at h ⊢
            cases hlen : decide ((r.1.length : Int) = rw_count_clamp count) with
            | false =>
              simp only [hlen, Bool.not_false, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
            | true =>
              simp only [hlen, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
              generalize read_bytes_map i.in_wmem buf (len_word r.1) = r2 at h
              cases r2 with
              | none => simp only [unmodeled_iff, reduceCtorEq] at h
              | some _ =>
                simp only [bind_set_urandom_iff, pure_iff, outcome.Ok.injEq] at h
                obtain ⟨-, rfl, rfl⟩ := h
                exact Or.inr rfl

/-- Rocq's `pwrite64_copyin_clamped`: whatever pwrite64 records as its one
copy-in, the length is at most `MAX_RW_COUNT`.  The ledger entry is the
readable prefix of the source at the CLAMPED count (the model's
write_source), and `vfs_write` (fs/read_write.c:680-681, v6.18.46) never
reads past
`MAX_RW_COUNT` (include/linux/fs.h:2838) bytes of it.
rocq-twin: pwrite64_copyin_clamped
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem pwrite64_copyin_clamped (fd buf count pos : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event) (a : word) (n : Nat)
    (h : pwrite64_spec fd buf count pos i m (Ok eff m' evs))
    (hc : eff.eff_copyins = [(a, n)]) : (n : Int) ≤ MAX_RW_COUNT := by
  have bare : ∀ (e : SyscallEffect) (m0 : Model), Monad.pure e i m0 (Ok eff m' evs) →
      e.eff_copyins = [] → False := by
    intro e m0 he hz
    simp only [pure_iff, outcome.Ok.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    rw [hz] at hc
    cases hc
  unfold pwrite64_spec at h
  cases hb : ppos_einvalb pos with
  | true =>
    simp only [hb, ↓reduceIte, err_ret, ret_only] at h
    exact (bare _ _ h rfl).elim
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_input_iff, bind_get_model_iff] at h
    generalize fd_lookup (m_fds m) fd = l at h
    cases l with
    | none => simp only [err_ret, ret_only] at h; exact (bare _ _ h rfl).elim
    | some e =>
      cases e with
      | FdFileA p off => simp only [unmodeled_iff, reduceCtorEq] at h
      | FdFileRW p off => simp only [unmodeled_iff, reduceCtorEq] at h
      | FdChannel c => simp only [err_ret, ret_only] at h; exact (bare _ _ h rfl).elim
      | FdPipe id w => simp only [err_ret, ret_only] at h; exact (bare _ _ h rfl).elim
      | FdSocket sk => simp only [err_ret, ret_only] at h; exact (bare _ _ h rfl).elim
      | FdFile p off => simp only [err_ret, ret_only] at h; exact (bare _ _ h rfl).elim
      | FdUrandom => simp only [err_ret, ret_only] at h; exact (bare _ _ h rfl).elim
      | FdDir => simp only [err_ret, ret_only] at h; exact (bare _ _ h rfl).elim
      | FdDevNull rd wr =>
        cases wr with
        | false =>
          simp only [Bool.not_false, ↓reduceIte, err_ret, ret_only] at h
          exact (bare _ _ h rfl).elim
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases ha : access_okb buf (bv_unsigned count) with
          | false =>
            simp only [ha, Bool.not_false, ↓reduceIte, err_ret, ret_only] at h
            exact (bare _ _ h rfl).elim
          | true =>
            simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            cases hp : rw_pos_einvalb pos (bv_unsigned count) with
            | true =>
              simp only [hp, ↓reduceIte, err_ret, ret_only] at h
              exact (bare _ _ h rfl).elim
            | false =>
              simp only [hp, Bool.false_eq_true, ↓reduceIte, ret_only] at h
              exact (bare _ _ h rfl).elim
      | FdFileW p off =>
        cases ha : access_okb buf (bv_unsigned count) with
        | false =>
          simp only [ha, Bool.not_false, ↓reduceIte, err_ret, ret_only] at h
          exact (bare _ _ h rfl).elim
        | true =>
          simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hp : rw_pos_einvalb pos (bv_unsigned count) with
          | true =>
            simp only [hp, ↓reduceIte, err_ret, ret_only] at h
            exact (bare _ _ h rfl).elim
          | false =>
            simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
            generalize hbs : write_source i.in_mem buf count = bs at h
            cases hu : unreadable_source_past_eof count bs (fs_lookup (m_fs m) p) pos with
            | true => simp only [hu, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
            | false =>
              simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
              cases hz : (!w_is0 count && bs.length == 0) with
              | true =>
                simp only [hz, ↓reduceIte, err_ret, ret_only] at h
                exact (bare _ _ h rfl).elim
              | false =>
                simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
                generalize fs_lookup (m_fs m) p = fl at h
                cases fl with
                | none => simp only [unmodeled_iff, reduceCtorEq] at h
                | some data =>
                  cases hg : modeled_file_gap data pos bs with
                  | false =>
                    simp only [hg, Bool.not_false, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
                  | true =>
                    simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                      bind_set_fs_iff] at h
                    cases hw : w_is0 count with
                    | true =>
                      simp only [hw, ↓reduceIte, ret_only] at h
                      exact (bare _ _ h rfl).elim
                    | false =>
                      simp only [hw, Bool.false_eq_true, ↓reduceIte, record_copyins_ok_iff,
                        ret_only, pure_iff, outcome.Ok.injEq] at h
                      obtain ⟨e0, ⟨rfl, -, -⟩, rfl⟩ := h
                      simp only [with_copyins, List.cons_append, List.nil_append,
                        List.cons.injEq, Prod.mk.injEq, and_true] at hc
                      obtain ⟨-, rfl⟩ := hc
                      subst hbs
                      exact Int.le_trans (write_source_length_le _ _ _)
                        (rw_count_clamp_range count).2


/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
rocq-twin: writev_stdin_channel_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_stdin_channel_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 0 8192 1 (writev_in 0 8192 1 (mem_iov_pair 4096 0 4096 0)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
rocq-twin: writev_stdin_alias_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_stdin_alias_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 26 8192 1 (writev_in 26 8192 1 (mem_iov_pair 4096 0 4096 0)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
rocq-twin: writev_urandom_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_urandom_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 24 8192 1 (writev_in 24 8192 1 (mem_iov_pair 4096 0 4096 0)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
rocq-twin: writev_devnull_read_only_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_devnull_read_only_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 8 8192 1 (writev_in 8 8192 1 (mem_iov_pair 4096 0 4096 0)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
rocq-twin: writev_read_only_file_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_read_only_file_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 3 8192 1 (writev_in 3 8192 1 (mem_iov_pair 4096 0 4096 0)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
rocq-twin: writev_directory_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_directory_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 5 8192 1 (writev_in 5 8192 1 (mem_iov_pair 4096 0 4096 0)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
rocq-twin: writev_pipe_read_end_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem writev_pipe_read_end_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 14 8192 1 (writev_in 14 8192 1 (mem_iov_pair 4096 0 4096 0)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
rocq-twin: readv_stdout_is_ebadf_before_import
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_stdout_is_ebadf_before_import (o : outcome SyscallEffect) :
    readv_spec 1 8192 1 (readv_in 1 8192 1 (mem_iov_pair 4096 0 4096 0) wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
rocq-twin: readv_stderr_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_stderr_is_ebadf (o : outcome SyscallEffect) :
    readv_spec 2 8192 1 (readv_in 2 8192 1 (mem_iov_pair 4096 0 4096 0) wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
rocq-twin: readv_devnull_write_only_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_devnull_write_only_is_ebadf (o : outcome SyscallEffect) :
    readv_spec 9 8192 1 (readv_in 9 8192 1 (mem_iov_pair 4096 0 4096 0) wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
rocq-twin: readv_pipe_write_end_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem readv_pipe_write_end_is_ebadf (o : outcome SyscallEffect) :
    readv_spec 15 8192 1 (readv_in 15 8192 1 (mem_iov_pair 4096 0 4096 0) wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm


/-- Nine complete empty descriptors isolate the old heap-allocation band. -/
def t139_nine_empty_iovecs : word → Option byte :=
  bytes_at 8192 (List.replicate 144 0)

def t139_eight_empty_iovecs : word → Option byte :=
  bytes_at 8192 (List.replicate 128 0)

/-- Eight complete empty descriptors stay on the fast path: UIO_FASTIOV is 8, so v4.17 through v6.7 import them without kmalloc_array (lib/iov_iter.c, iovec_from_user, v6.6) and then reach the mode error; v6.8+ tests the mode first (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46). This is the band's upper edge; nine entries are declined.
rocq-twin: t139_writev_open_eight_empty_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_eight_empty_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 0 8192 8 (writev_in 0 8192 8 t139_eight_empty_iovecs) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- Eight complete empty descriptors stay on the fast path: UIO_FASTIOV is 8, so v4.17 through v6.7 import them without kmalloc_array (lib/iov_iter.c, iovec_from_user, v6.6) and then reach the mode error; v6.8+ tests the mode first (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46). This is the band's upper edge; nine entries are declined.
rocq-twin: t139_readv_open_eight_empty_is_ebadf
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_readv_open_eight_empty_is_ebadf (o : outcome SyscallEffect) :
    readv_spec 1 8192 8 (readv_in 1 8192 8 t139_eight_empty_iovecs wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_high_empty_is_unmodeled
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- wrongmode-highbase -/
theorem t139_writev_open_high_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 0 8192 1 (writev_in 0 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_high_empty_ebadf_is_not_ok
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- wrongmode-highbase -/
theorem t139_writev_open_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 0 8192 1 (writev_in 0 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_readv_open_high_empty_is_unmodeled
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- wrongmode-highbase -/
theorem t139_readv_open_high_empty_is_unmodeled (o : outcome SyscallEffect) :
    readv_spec 1 8192 1 (readv_in 1 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0) wmem_none) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_readv_open_high_empty_ebadf_is_not_ok
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- wrongmode-highbase -/
theorem t139_readv_open_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ readv_spec 1 8192 1 (readv_in 1 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0) wmem_none) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_nine_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_nine_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 0 8192 9 (writev_in 0 8192 9 t139_nine_empty_iovecs) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_nine_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 0 8192 9 (writev_in 0 8192 9 t139_nine_empty_iovecs) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_uncapped_later_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_uncapped_later_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 0 8192 2 (writev_in 0 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_uncapped_later_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 0 8192 2 (writev_in 0 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_file_high_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_file_high_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 3 8192 1 (writev_in 3 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_file_high_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_file_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 3 8192 1 (writev_in 3 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_file_nine_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_file_nine_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 3 8192 9 (writev_in 3 8192 9 t139_nine_empty_iovecs) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_file_nine_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_file_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 3 8192 9 (writev_in 3 8192 9 t139_nine_empty_iovecs) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_file_uncapped_later_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_file_uncapped_later_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 3 8192 2 (writev_in 3 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_file_uncapped_later_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_file_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 3 8192 2 (writev_in 3 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_dir_high_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_dir_high_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 5 8192 1 (writev_in 5 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_dir_high_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_dir_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 5 8192 1 (writev_in 5 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_dir_nine_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_dir_nine_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 5 8192 9 (writev_in 5 8192 9 t139_nine_empty_iovecs) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_dir_nine_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_dir_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 5 8192 9 (writev_in 5 8192 9 t139_nine_empty_iovecs) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_dir_uncapped_later_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_dir_uncapped_later_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 5 8192 2 (writev_in 5 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_dir_uncapped_later_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_dir_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 5 8192 2 (writev_in 5 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_urandom_high_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_urandom_high_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 24 8192 1 (writev_in 24 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_urandom_high_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_urandom_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 24 8192 1 (writev_in 24 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_urandom_nine_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_urandom_nine_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 24 8192 9 (writev_in 24 8192 9 t139_nine_empty_iovecs) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_urandom_nine_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_urandom_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 24 8192 9 (writev_in 24 8192 9 t139_nine_empty_iovecs) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_urandom_uncapped_later_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_urandom_uncapped_later_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 24 8192 2 (writev_in 24 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_urandom_uncapped_later_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_urandom_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 24 8192 2 (writev_in 24 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_devnull_ro_high_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_devnull_ro_high_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 8 8192 1 (writev_in 8 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_devnull_ro_high_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_devnull_ro_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 8 8192 1 (writev_in 8 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_devnull_ro_nine_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_devnull_ro_nine_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 8 8192 9 (writev_in 8 8192 9 t139_nine_empty_iovecs) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_devnull_ro_nine_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_devnull_ro_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 8 8192 9 (writev_in 8 8192 9 t139_nine_empty_iovecs) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_devnull_ro_uncapped_later_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_devnull_ro_uncapped_later_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 8 8192 2 (writev_in 8 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_devnull_ro_uncapped_later_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_devnull_ro_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 8 8192 2 (writev_in 8 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_pipe_read_high_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_pipe_read_high_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 14 8192 1 (writev_in 14 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_pipe_read_high_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_pipe_read_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 14 8192 1 (writev_in 14 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_pipe_read_nine_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_pipe_read_nine_empty_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 14 8192 9 (writev_in 14 8192 9 t139_nine_empty_iovecs) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_pipe_read_nine_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_pipe_read_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 14 8192 9 (writev_in 14 8192 9 t139_nine_empty_iovecs) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_pipe_read_uncapped_later_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_pipe_read_uncapped_later_is_unmodeled (o : outcome SyscallEffect) :
    writev_spec 14 8192 2 (writev_in 14 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_writev_open_pipe_read_uncapped_later_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_writev_open_pipe_read_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ writev_spec 14 8192 2 (writev_in 14 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_readv_open_nine_empty_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_readv_open_nine_empty_is_unmodeled (o : outcome SyscallEffect) :
    readv_spec 1 8192 9 (readv_in 1 8192 9 t139_nine_empty_iovecs wmem_none) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_readv_open_nine_empty_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_readv_open_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ readv_spec 1 8192 9 (readv_in 1 8192 9 t139_nine_empty_iovecs wmem_none) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_readv_open_uncapped_later_is_unmodeled
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_readv_open_uncapped_later_is_unmodeled (o : outcome SyscallEffect) :
    readv_spec 1 8192 2 (readv_in 1 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62))) wmem_none) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
rocq-twin: t139_readv_open_uncapped_later_ebadf_is_not_ok
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem t139_readv_open_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    ¬ readv_spec 1 8192 2 (readv_in 1 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62))) wmem_none) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- A closed fd is rejected by fdget_pos in do_readv / do_writev before import on every supported Linux (fs/read_write.c, v4.17 and v6.18.46). QEMU skips locking a zero-length first buffer (linux-user/syscall.c, lock_iovec, QEMU 11.1.1), so the high empty base does not change -EBADF.
rocq-twin: t139_readv_closed_high_empty_is_ebadf
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_readv_closed_high_empty_is_ebadf (o : outcome SyscallEffect) :
    readv_spec 30 8192 1 (readv_in 30 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0) wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- A closed fd is rejected by fdget_pos in do_readv / do_writev before import on every supported Linux (fs/read_write.c, v4.17 and v6.18.46). QEMU skips locking a zero-length first buffer (linux-user/syscall.c, lock_iovec, QEMU 11.1.1), so the high empty base does not change -EBADF.
rocq-twin: t139_writev_closed_high_empty_is_ebadf
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_writev_closed_high_empty_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 30 8192 1 (writev_in 30 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- model: constant zero memory makes descriptor decoding independent of the address. -/
theorem t139_zero_iovec_entry (a : word) :
    read_iovec_entry (fun _ => some 0) a = IovEntry 0 0 := by
  rfl

/-- model: induction avoids reducing 1024 descriptor loads in each boundary pin. -/
theorem t139_copy_zero_iovecs (a : word) (k : Nat) :
    copy_iovecs_aux (fun _ => some 0) a k = ImpOk (List.replicate k (0, 0)) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
      simp only [copy_iovecs_aux, t139_zero_iovec_entry, ih, List.replicate_succ]

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_readv_closed_iov_max_is_ebadf (o : outcome SyscallEffect) :
    readv_spec 30 8192 1024 (readv_in 30 8192 1024 (fun _ => some 0) wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  unfold readv_spec
  rw [bind_input_iff, bind_get_model_iff]
  erw [t139_copy_zero_iovecs]
  rw [show word_to_nat (1024 : word) = 1023 + 1 from rfl, List.replicate_succ]
  rw_norm

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_readv_closed_iov_max_unmodeled_refuted :
    ¬ readv_spec 30 8192 1024 (readv_in 30 8192 1024 (fun _ => some 0) wmem_none) read_model Unmodeled := by
  rw [t139_readv_closed_iov_max_is_ebadf]; simp

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_readv_closed_iov_max_zero_refuted (m' : Model) (evs : List event) :
    ¬ readv_spec 30 8192 1024 (readv_in 30 8192 1024 (fun _ => some 0) wmem_none) read_model
      (Ok (mkEffect 0 [] []) m' evs) := by
  rw [t139_readv_closed_iov_max_is_ebadf]; rw_refute

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_readv_closed_nine_empty_is_ebadf (o : outcome SyscallEffect) :
    readv_spec 30 8192 9 (readv_in 30 8192 9 t139_nine_empty_iovecs wmem_none) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_readv_closed_nine_empty_unmodeled_refuted :
    ¬ readv_spec 30 8192 9 (readv_in 30 8192 9 t139_nine_empty_iovecs wmem_none) read_model Unmodeled := by
  rw [t139_readv_closed_nine_empty_is_ebadf]; simp

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_readv_closed_nine_empty_zero_refuted (m' : Model) (evs : List event) :
    ¬ readv_spec 30 8192 9 (readv_in 30 8192 9 t139_nine_empty_iovecs wmem_none) read_model
      (Ok (mkEffect 0 [] []) m' evs) := by
  rw [t139_readv_closed_nine_empty_is_ebadf]; rw_refute

/-- Linux rejects the closed fd first; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) rejects count > IOV_MAX before the host fd lookup.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_readv_closed_over_iov_max_declines (o : outcome SyscallEffect) :
    readv_spec 30 8192 1025 (readv_in 30 8192 1025 (fun _ => some 0) wmem_none) read_model o ↔ o = Unmodeled := by
  unfold readv_spec
  rw [bind_input_iff, bind_get_model_iff]
  erw [t139_copy_zero_iovecs]
  rw [show word_to_nat (1025 : word) = 1024 + 1 from rfl, List.replicate_succ]
  rw_norm

/-- Linux rejects the closed fd first; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) rejects count > IOV_MAX before the host fd lookup.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_readv_closed_over_iov_max_ebadf_refuted (m' : Model) (evs : List event) :
    ¬ readv_spec 30 8192 1025 (readv_in 30 8192 1025 (fun _ => some 0) wmem_none) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw [t139_readv_closed_over_iov_max_declines]; simp

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_writev_closed_iov_max_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 30 8192 1024 (writev_in 30 8192 1024 (fun _ => some 0)) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  unfold writev_spec
  rw [bind_input_iff, bind_get_model_iff]
  erw [t139_copy_zero_iovecs]
  rw [show word_to_nat (1024 : word) = 1023 + 1 from rfl, List.replicate_succ]
  rw_norm

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_writev_closed_iov_max_unmodeled_refuted :
    ¬ writev_spec 30 8192 1024 (writev_in 30 8192 1024 (fun _ => some 0)) read_model Unmodeled := by
  rw [t139_writev_closed_iov_max_is_ebadf]; simp

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_writev_closed_iov_max_zero_refuted (m' : Model) (evs : List event) :
    ¬ writev_spec 30 8192 1024 (writev_in 30 8192 1024 (fun _ => some 0)) read_model
      (Ok (mkEffect 0 [] []) m' evs) := by
  rw [t139_writev_closed_iov_max_is_ebadf]; rw_refute

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_writev_closed_nine_empty_is_ebadf (o : outcome SyscallEffect) :
    writev_spec 30 8192 9 (writev_in 30 8192 9 t139_nine_empty_iovecs) read_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) read_model [] := by
  rw_norm

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_writev_closed_nine_empty_unmodeled_refuted :
    ¬ writev_spec 30 8192 9 (writev_in 30 8192 9 t139_nine_empty_iovecs) read_model Unmodeled := by
  rw [t139_writev_closed_nine_empty_is_ebadf]; simp

/-- Linux rejects the closed fd before import; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) accepts the count and skips the empty buffers.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_writev_closed_nine_empty_zero_refuted (m' : Model) (evs : List event) :
    ¬ writev_spec 30 8192 9 (writev_in 30 8192 9 t139_nine_empty_iovecs) read_model
      (Ok (mkEffect 0 [] []) m' evs) := by
  rw [t139_writev_closed_nine_empty_is_ebadf]; rw_refute

/-- Linux rejects the closed fd first; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) rejects count > IOV_MAX before the host fd lookup.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_writev_closed_over_iov_max_declines (o : outcome SyscallEffect) :
    writev_spec 30 8192 1025 (writev_in 30 8192 1025 (fun _ => some 0)) read_model o ↔ o = Unmodeled := by
  unfold writev_spec
  rw [bind_input_iff, bind_get_model_iff]
  erw [t139_copy_zero_iovecs]
  rw [show word_to_nat (1025 : word) = 1024 + 1 from rfl, List.replicate_succ]
  rw_norm

/-- Linux rejects the closed fd first; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) rejects count > IOV_MAX before the host fd lookup.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem t139_writev_closed_over_iov_max_ebadf_refuted (m' : Model) (evs : List event) :
    ¬ writev_spec 30 8192 1025 (writev_in 30 8192 1025 (fun _ => some 0)) read_model
      (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw [t139_writev_closed_over_iov_max_declines]; simp

/-- Linux v6.18.46 fs/read_write.c, vfs_writev returns zero for an empty
aggregate before invoking the write operation; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) skips locking the empty buffer.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem t139_writev_stdout_empty_is_zero (o : outcome SyscallEffect) :
    writev_spec 1 8192 1 (writev_in 1 8192 1 (mem_iov_pair 4096 0 4096 0)) read_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) read_model [] := by
  rw_norm

/-- Linux v6.18.46 fs/read_write.c, vfs_writev returns zero for an empty
aggregate before invoking the write operation; QEMU 11.1.1 lock_iovec
(linux-user/syscall.c) skips locking the empty buffer.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem t139_writev_stdout_empty_efault_refuted (m' : Model) (evs : List event) :
    ¬ writev_spec 1 8192 1 (writev_in 1 8192 1 (mem_iov_pair 4096 0 4096 0)) read_model
      (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw [t139_writev_stdout_empty_is_zero]; rw_refute

/-- Linux narrows nr_segs to unsigned in lib/iov_iter.c, import_iovec
(v6.18.46); QEMU 11.1.1 lock_iovec (linux-user/syscall.c) tests the raw
count against IOV_MAX before reading descriptors.
kernel: lib/iov_iter.c:import_iovec@v6.18.46 -/
theorem t139_writev_wide_iov_max_any_memory_declines (mem : word → Option byte) (o : outcome SyscallEffect) :
    writev_spec 1 8192 (Z_to_bv 64 (2 ^ 32 + 1024))
      (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1024)) mem) read_model o ↔ o = Unmodeled := by
  rw_norm

/-- Linux narrows nr_segs to unsigned in lib/iov_iter.c, import_iovec
(v6.18.46); QEMU 11.1.1 lock_iovec (linux-user/syscall.c) tests the raw
count against IOV_MAX before reading descriptors.
kernel: lib/iov_iter.c:import_iovec@v6.18.46 -/
theorem t139_writev_wide_iov_max_declines (o : outcome SyscallEffect) :
    writev_spec 1 8192 (Z_to_bv 64 (2 ^ 32 + 1024))
      (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1024)) (fun _ => some 0)) read_model o ↔ o = Unmodeled := by
  exact t139_writev_wide_iov_max_any_memory_declines (fun _ => some 0) o

/-- Linux narrows nr_segs to unsigned in lib/iov_iter.c, import_iovec
(v6.18.46); QEMU 11.1.1 lock_iovec (linux-user/syscall.c) tests the raw
count against IOV_MAX before reading descriptors.
kernel: lib/iov_iter.c:import_iovec@v6.18.46 -/
theorem t139_writev_wide_iov_max_zero_refuted (reads : List (word × Nat)) (m' : Model) (evs : List event) :
    ¬ writev_spec 1 8192 (Z_to_bv 64 (2 ^ 32 + 1024))
      (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1024)) (fun _ => some 0)) read_model
      (Ok (with_copyins reads (mkEffect 0 [] [])) m' evs) := by
  rw [t139_writev_wide_iov_max_declines]; simp

/-! ## A17: FdFileRW and FdFileA -/

def a17_readwrite_model : Model :=
  fixture_of (fds := [(3, .FdFileRW [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_readwrite_model.eq_1

/-- Rocq: `ReadWrite.readable_fd`, ReadWrite.v:2130 at 96c2debdb.
O_RDWR passes FMODE_READ in fs/read_write.c, vfs_readv, Linux v6.18.46.
Keeping the kind prevents a read from turning the description read-only.
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem a17_rdwr_readable_keeps_kind :
    readable_fd (.FdFileRW [102] 7) = some (.RdFileRW [102] 7) := by
  rfl

/-- `read` of 0 bytes through a read-write file declines (the header of
`Sys/Fs/ReadWrite.lean` declares the narrowing).  The same call on an
`FdFile` answers 0 and leaves the offset at 0 (`vfs_read`,
fs/read_write.c, Linux v6.18.46, passes O_RDWR's `FMODE_READ` as it does
O_RDONLY's), so a mutant answering this kind as `FdFile` fails here.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem a17_rdwr_read_declines (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 4096 0 (fun _ => none)) a17_readwrite_model o ↔ o = Unmodeled := by
  rw_norm

/-- `write` of 0 bytes through a read-write file declines (the header of
`Sys/Fs/ReadWrite.lean` declares the narrowing).  The same call on an
`FdFileW` answers 0 and leaves the offset at 0 (`vfs_write`,
fs/read_write.c, Linux v6.18.46, passes O_RDWR's `FMODE_WRITE` as it
does O_WRONLY's), so a mutant answering this kind as `FdFileW` fails
here.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem a17_rdwr_write_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 3 4096 0 (fun _ => none)) a17_readwrite_model o ↔ o = Unmodeled := by
  rw_norm

/-- `pread64` of 0 bytes through a read-write file declines (the header
of `Sys/Fs/ReadWrite.lean` declares the narrowing).  The same call on an
`FdFile` answers 0 without moving the offset (`vfs_read`,
fs/read_write.c, Linux v6.18.46), so a mutant answering this kind as
`FdFile` fails here.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem a17_rdwr_pread64_declines (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 0 0 (fun _ => none)) a17_readwrite_model o ↔ o = Unmodeled := by
  rw_norm

/-- `pwrite64` of 0 bytes through a read-write file declines (the header
of `Sys/Fs/ReadWrite.lean` declares the narrowing).  The same call on an
`FdFileW` answers 0 without moving the offset (`vfs_write`,
fs/read_write.c, Linux v6.18.46), so a mutant answering this kind as
`FdFileW` fails here.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem a17_rdwr_pwrite64_declines (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 0 0 (fun _ => none)) a17_readwrite_model o ↔ o = Unmodeled := by
  rw_norm

/-- `writev` of an empty vector through a read-write file declines (the
header of `Sys/Fs/ReadWrite.lean` declares the narrowing).  The same
call on an `FdFileW` answers 0 (`vfs_writev`, fs/read_write.c, Linux
v6.18.46), so a mutant answering this kind as `FdFileW` fails here.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem a17_rdwr_writev_declines (o : outcome SyscallEffect) :
    syscall_spec (writev_in 3 8192 0 (fun _ => none)) a17_readwrite_model o ↔ o = Unmodeled := by
  rw_norm

/-- `readv` through a read-write file declines in `readv_imported` (the
header of `Sys/Fs/ReadWrite.lean` declares the narrowing; `readable_fd`
lets the kind through as Rocq's does).  The same call on an `FdFile`
answers 1, delivers the byte 120 and advances the offset to 1
(`vfs_readv`, fs/read_write.c, Linux v6.18.46), so a mutant answering
this kind as `FdFile` fails here.
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem a17_rdwr_readv_declines (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 1 mem_readv_iov wmem_readv_one) a17_readwrite_model o ↔ o = Unmodeled := by
  rw_norm

/-- O_RDWR passes `FMODE_READ` in `vfs_readv` (fs/read_write.c,
Linux v6.18.46).  `import_iovec` copies the one 16-byte iovec at 8192;
`iov_iter_count` is zero, so the call returns 0 before reading file data.
The read-write kind keeps the read path, unlike the append kind's
`a17_append_readv_is_ebadf`.  A mutant whose `readable_fd` turns
`FdFileRW` away answers -EBADF here and fails this pin.
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem a17_rdwr_readv_empty_vector_is_zero (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 1 (mem_iov_pair 4096 0 4096 0) wmem_none) a17_readwrite_model o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) a17_readwrite_model [] := by
  rw_norm

/-- Refutes the -EBADF a write-only or append file answers to the same
call: O_RDWR passes `FMODE_READ` in `vfs_readv` (fs/read_write.c,
Linux v6.18.46), and the empty imported vector returns 0.
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem a17_rdwr_readv_empty_vector_ebadf_refuted (m' : Model) (evs : List event) :
    ¬ syscall_spec (readv_in 3 8192 1 (mem_iov_pair 4096 0 4096 0) wmem_none) a17_readwrite_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw_refute

/-- `lseek(fd, 0, SEEK_SET)` through a read-write file declines (the
header of `Sys/Fs/ReadWrite.lean` declares the narrowing).  The same
call on an `FdFile` answers 0 and sets the offset to 0 (`ksys_lseek`,
fs/read_write.c, Linux v6.18.46), so a mutant answering this kind as
`FdFile` fails here.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem a17_rdwr_lseek_declines (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 0 0) a17_readwrite_model o ↔ o = Unmodeled := by
  rw_norm

def a17_readwrite_append_model : Model :=
  fixture_of (fds := [(3, .FdFileA [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_readwrite_append_model.eq_1

/-- Rocq: `ReadWrite.readable_fd`, ReadWrite.v:2136 at 96c2debdb.
The append word carries O_WRONLY, so FMODE_READ is clear and fs/read_write.c,
vfs_readv, Linux v6.18.46 answers -EBADF, as for a write-only file.
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem a17_append_readable_is_none :
    readable_fd (.FdFileA [102] 7) = none := by
  rfl

/-- `read` of 0 bytes through an append-mode file declines (the header of
`Sys/Fs/ReadWrite.lean` declares the narrowing).  Rocq's arm and an
`FdFileW` answer -EBADF (`vfs_read`, fs/read_write.c, Linux v6.18.46:
O_APPEND rides on O_WRONLY, so `FMODE_READ` is clear), so a mutant
answering this kind as `FdFileW` fails here.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem a17_append_read_declines (o : outcome SyscallEffect) :
    syscall_spec (read_in 3 4096 0 (fun _ => none)) a17_readwrite_append_model o ↔ o = Unmodeled := by
  rw_norm

/-- `write` of 0 bytes through an append-mode file declines (the header of
`Sys/Fs/ReadWrite.lean` declares the narrowing).  The same call on an
`FdFileW` answers 0 and leaves the offset at 0 (`vfs_write`,
fs/read_write.c, Linux v6.18.46), so a mutant answering this kind as
`FdFileW` fails here.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem a17_append_write_declines (o : outcome SyscallEffect) :
    syscall_spec (write_in 3 4096 0 (fun _ => none)) a17_readwrite_append_model o ↔ o = Unmodeled := by
  rw_norm

/-- `pread64` of 0 bytes through an append-mode file declines (the header
of `Sys/Fs/ReadWrite.lean` declares the narrowing).  Rocq's arm and an
`FdFileW` answer -EBADF (`vfs_read`, fs/read_write.c, Linux v6.18.46:
`FMODE_READ` is clear), so a mutant answering this kind as `FdFileW`
fails here.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem a17_append_pread64_declines (o : outcome SyscallEffect) :
    syscall_spec (pread_in 3 4096 0 0 (fun _ => none)) a17_readwrite_append_model o ↔ o = Unmodeled := by
  rw_norm

/-- `pwrite64` of 0 bytes through an append-mode file declines, as Rocq's arm
does (the header of `Sys/Fs/ReadWrite.lean`).  The same call on an
`FdFileW` answers 0 without moving the offset (`vfs_write`,
fs/read_write.c, Linux v6.18.46), so a mutant answering this kind as
`FdFileW` fails here.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem a17_append_pwrite64_declines (o : outcome SyscallEffect) :
    syscall_spec (pwrite_in 3 4096 0 0 (fun _ => none)) a17_readwrite_append_model o ↔ o = Unmodeled := by
  rw_norm

/-- `writev` of an empty vector through an append-mode file declines (the
header of `Sys/Fs/ReadWrite.lean` declares the narrowing).  The same call
on an `FdFileW` answers 0 (`vfs_writev`, fs/read_write.c, Linux
v6.18.46), so a mutant answering this kind as `FdFileW` fails here.
kernel: fs/read_write.c:vfs_writev@v6.18.46 -/
theorem a17_append_writev_declines (o : outcome SyscallEffect) :
    syscall_spec (writev_in 3 8192 0 (fun _ => none)) a17_readwrite_append_model o ↔ o = Unmodeled := by
  rw_norm

/-- `readv` through an append-mode file answers -EBADF, as through a
write-only file: `readable_fd` turns the kind away (`vfs_readv`,
fs/read_write.c, Linux v6.18.46: O_APPEND rides on O_WRONLY, so
`FMODE_READ` is clear).  The vector is one empty, in-range entry.
The `iff` refuses every other outcome, the decline among them, so a
`readable_fd` that let the kind through to `readv_imported` fails here.
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem a17_append_readv_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (readv_in 3 8192 1 (mem_iov_pair 4096 0 4096 0) wmem_none) a17_readwrite_append_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) a17_readwrite_append_model [] := by
  rw_norm

/-- `lseek(fd, 0, SEEK_SET)` through an append-mode file declines (the header
of `Sys/Fs/ReadWrite.lean` declares the narrowing).  The same call on an
`FdFileW` answers 0 and sets the offset to 0 (`ksys_lseek`,
fs/read_write.c, Linux v6.18.46, moves `f_pos` whatever O_APPEND says), so
a mutant answering this kind as `FdFileW` fails here.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem a17_append_lseek_declines (o : outcome SyscallEffect) :
    syscall_spec (lseek_in 3 0 0) a17_readwrite_append_model o ↔ o = Unmodeled := by
  rw_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.ReadWrite
