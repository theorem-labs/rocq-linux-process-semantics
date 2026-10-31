import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Net/Socket.v

/-! rocq-cases: f1006fe8178338a499b5e5c41be83006c4edd058
unpinned: socket_write_never_admitted -- a claim about `write_spec`'s FdSocket arm, which is theories/LinuxProcessSem/Sys/Fs/ReadWrite.v's and its twin `Sys/Fs/ReadWrite.lean`'s (`| some (.FdSocket _) => unmodeled`), not any spec this file's twin defines; `Checks/Cases/Fs/ReadWrite.lean` pins it as `write_socket_declines`, `write_socket_is_not_epipe` and `write_socket_delivers_nothing`, which a `covers:` line cannot name across files
unpinned: socket_writev_never_admitted -- the same claim for `writev_spec`'s FdSocket arm in theories/LinuxProcessSem/Sys/Fs/ReadWrite.v; `Sys/Fs/ReadWrite.lean` defines `writev_spec` (ticket S-Fs-ReadWrite-readv-writev) and `Checks/Cases/Fs/ReadWrite.lean` pins that arm as `writev_socket_declines` and `writev_socket_delivery_rejected`, which a `covers:` line cannot name across files; nothing this file's specs define is involved
unpinned: socket_is_readable -- a closed evaluation of `readable_fd` from theories/LinuxProcessSem/Sys/Fs/ReadWrite.v, which `Sys/Fs/ReadWrite.lean` defines (ticket S-Fs-ReadWrite-readv-writev; the Lean `read_spec` still decides the FMODE_READ gate arm by arm, and readv reads it); a definition of that file, not a claim about any Sys.Net.Socket arm
covers: conn_channel_unsigned -- conn_channel_unsigned
covers: conn_channel_injective -- conn_channel_injective
covers: conn_channel_not_std -- conn_channel_not_std
covers: accept_hands_over_the_head_connection -- accept4_listening_iff, accept_listening_iff
covers: accept_errno_set_is_exactly_these_three -- accept4_listening_iff, accept4_eagain_rejected, accept4_eintr_rejected, accept4_eopnotsupp_rejected
covers: accept_success_return_is_exactly_the_lowest_free_fd -- accept4_listening_iff, accept4_non_lowest_fd_rejected, accept4_open_fd_rejected, accept4_listener_fd_rejected
covers: accept_errno_arms_leave_the_queue_alone -- accept4_listening_iff, accept4_success_leaves_queue_rejected
covers: accept_refuses_errnos_outside_the_set -- accept4_eagain_rejected, accept4_eintr_rejected, accept4_eopnotsupp_rejected
covers: accept_arms_around_the_accepted_state -- accept4_accepted_socket_is_einval, accept4_channel_fd_is_enotsock, accept4_closed_fd_flag_is_ebadf, accept4_bad_flag_on_listening_is_einval, accept4_cloexec_iff
covers: accept_declined_arguments_are_unmodeled -- accept4_nonblock_declines, accept4_peer_address_declines, accept4_cloexec_iff
covers: conn_channel_at_the_wrap_is_stdin_stdout_stderr -- conn_channel_at_the_wrap_is_stdin_stdout_stderr
covers: conn_ix_not_exhausted_lt -- conn_ix_not_exhausted_lt
covers: guarded_conn_channel_not_std -- guarded_conn_channel_not_std
covers: guarded_conn_channel_injective -- guarded_conn_channel_injective
covers: accept_at_the_wrap_hands_over_no_descriptor_at_all -- accept_at_the_wrap_iff
covers: accept_at_the_wrap_rejects_the_allocated_fd -- accept_at_the_wrap_rejects_the_allocated_fd
covers: accept_one_below_the_wrap_still_hands_over -- accept_one_below_the_wrap_iff
covers: accept_one_below_the_wrap_uses_the_last_free_channel -- accept_one_below_the_wrap_uses_the_last_free_channel
covers: accept_at_the_wrap_still_answers_its_errnos -- accept_at_the_wrap_iff
covers: accept_at_the_wrap_errno_set_is_still_exactly_these_three -- accept_at_the_wrap_iff
covers: accept_at_the_wrap_never_declines -- accept_at_the_wrap_never_declines
covers: socket_packet_declines_at_every_protocol -- socket_packet_declines, socket_packet_negative_protocol_declines, socket_packet_at_ipproto_max_declines, socket_packet_einval_rejected, socket_packet_eperm_rejected, socket_dgram_truncated_protocol_iff
covers: socket_dgram_and_raw_still_take_the_protocol_range -- socket_dgram_truncated_protocol_iff, socket_raw_protocol_range_iff, socket_dgram_declines
covers: socket_kernel_build_answers_are_declined -- socket_stream_sctp_declines, socket_stream_mptcp_declines, socket_seqpacket_declines, socket_dccp_declines, socket_stream_udp_iff, socket_rdm_iff
covers: socket_still_answers_its_pure_argument_errors -- socket_stream_udp_iff, socket_rdm_iff, socket_type_zero_iff
covers: bind_input_reaches_the_state_match -- bind_fresh_socket_iff
covers: bind_on_a_reset_connection_declines -- bind_reset_connection_declines
covers: bind_copyin_ledger_marks_the_copy -- bind_fresh_socket_iff, bind_short_readable_address_is_einval_with_ledger, bind_short_readable_address_unledgered_rejected, bind_addrlen_over_storage_is_einval, bind_addrlen_over_storage_ledger_rejected, bind_unreadable_address_is_efault, bind_unreadable_address_ledger_rejected
covers: getsockopt_optlen_ledger_marks_the_read -- getsockopt_readable_optlen_is_eopnotsupp_with_ledger, getsockopt_readable_optlen_unledgered_rejected, getsockopt_unreadable_optlen_is_eopnotsupp_unledgered, getsockopt_unreadable_optlen_ledger_rejected, getsockopt_straddling_optlen_is_eopnotsupp_unledgered, getsockopt_straddling_optlen_ledger_rejected, getsockopt_closed_fd_readable_optlen_is_ebadf, getsockopt_closed_fd_readable_optlen_ledger_rejected, getsockopt_known_level_readable_optlen_declines, getsockopt_optlen_read_wrapping, getsockopt_wrapping_optlen_is_eopnotsupp_unledgered
unpinned: read_on_rst_delivers_econnreset_and_retires -- `read_spec`'s socket arm is theories/LinuxProcessSem/Sys/Fs/ReadWrite.v's and its twin `Sys/Fs/ReadWrite.lean`'s, pinned in `Checks/Cases/Fs/ReadWrite.lean` as `rst_is_connreset_once`, `rst_etimedout_rejected`, `rst_zero_rejected` and `rst_left_pending_rejected`, which a `covers:` line cannot name across files; the refused answers are what a pending reset cannot produce: `tcp_reset` (net/ipv4/tcp_input.c, Linux v6.18.46) records ECONNRESET, not ETIMEDOUT, on an established socket, and `tcp_recvmsg_locked` (net/ipv4/tcp.c, Linux v6.18.46) reports a pending error before it reports end-of-stream, so a zero return is not the first read's answer
unpinned: read_on_timeout_delivers_etimedout_and_retires -- `read_spec`'s socket arm is theories/LinuxProcessSem/Sys/Fs/ReadWrite.v's and its twin `Sys/Fs/ReadWrite.lean`'s, pinned in `Checks/Cases/Fs/ReadWrite.lean` as `timedout_is_etimedout_once` and `timedout_connreset_rejected`, which a `covers:` line cannot name across files; the refused ECONNRESET is not what a retransmission timeout records: `tcp_write_err` (net/ipv4/tcp_timer.c, Linux v6.18.46) reports ETIMEDOUT unless a soft error is already pending
unpinned: read_on_a_retired_connection_is_end_of_stream -- `read_spec`'s socket arm is theories/LinuxProcessSem/Sys/Fs/ReadWrite.v's and its twin `Sys/Fs/ReadWrite.lean`'s, pinned in `Checks/Cases/Fs/ReadWrite.lean` as `reset_socket_reads_zero`, `reset_socket_connreset_again_rejected` and `reset_socket_enotconn_rejected`, which a `covers:` line cannot name across files; the refused errnos were consumed by the read that retired the connection: `sock_error` (include/net/sock.h, Linux v6.18.46) clears sk_err as it reads it, so a second read finds none and reaches the end-of-stream return
unpinned: read_on_fin_is_end_of_stream_and_sticky -- `read_spec`'s socket arm is theories/LinuxProcessSem/Sys/Fs/ReadWrite.v's and its twin `Sys/Fs/ReadWrite.lean`'s, pinned in `Checks/Cases/Fs/ReadWrite.lean` as `fin_is_zero`, `fin_byte_rejected` and `fin_connreset_rejected`, which a `covers:` line cannot name across files; a byte after FIN is a lie: `tcp_fin` (net/ipv4/tcp_input.c, Linux v6.18.46) sets RCV_SHUTDOWN and SOCK_DONE, after which a read with nothing queued returns 0 and copies nothing
unpinned: read_on_a_byte_delivers_it_and_advances -- `read_spec`'s socket arm is theories/LinuxProcessSem/Sys/Fs/ReadWrite.v's and its twin `Sys/Fs/ReadWrite.lean`'s, pinned in `Checks/Cases/Fs/ReadWrite.lean` as `socket_delivers_a_prefix_iff` and `socket_over_queue_rejected`, which a `covers:` line cannot name across files; the refused two-byte delivery is more than the peer sent: `tcp_recvmsg_locked` (net/ipv4/tcp.c, Linux v6.18.46) copies only what the receive queue holds
unpinned: read_over_rw_bytes_max_is_judged -- `read_spec`'s socket arm is theories/LinuxProcessSem/Sys/Fs/ReadWrite.v's and its twin `Sys/Fs/ReadWrite.lean`'s, pinned in `Checks/Cases/Fs/ReadWrite.lean` as `socket_big_in_range_count_is_judged` — a 2^40 count judged on a fresh socket, so the delivery of a queued byte at `rw_bytes_max + 1` on a connected one is still unpinned in Lean, which a `covers:` line cannot name across files; the count bound is the model's `Uaccess.rw_bytes_max` (linux-process-semantics@ff0313ba4f:bugs/extraction-stack-limit-unpinned.md), not a kernel one: `vfs_read` (fs/read_write.c, Linux v6.18.46) clamps the count to MAX_RW_COUNT and hands it on, so a queued byte is delivered whatever the request and the refused zero return is not what Linux gives
covers: connect_on_a_listening_socket_is_eisconn -- connect_listening_socket_is_eisconn, connect_listening_socket_einval_rejected
covers: connect_eisconn_must_carry_its_copy -- connect_listening_socket_is_eisconn, connect_listening_socket_unledgered_rejected
covers: connect_on_an_accepted_socket_is_eisconn -- connect_accepted_socket_is_eisconn
covers: connect_on_a_reset_connection_is_eisconn -- connect_reset_socket_is_eisconn, connect_reset_socket_success_rejected, connect_reset_af_unspec_declines
covers: connect_is_eisconn_whatever_the_peer_has_left_to_say -- connect_accepted_socket_is_eisconn, connect_pending_reset_is_eisconn, connect_live_connection_is_eisconn
covers: connect_faults_before_it_reaches_enotsock -- connect_channel_fd_unreadable_is_efault, connect_channel_fd_unreadable_enotsock_rejected, bind_channel_fd_is_enotsock
covers: connect_on_a_channel_fd_is_enotsock -- connect_channel_fd_is_enotsock_with_ledger, connect_channel_fd_unledgered_enotsock_rejected
covers: connect_on_a_closed_fd_is_ebadf -- connect_closed_fd_is_ebadf, connect_closed_fd_ledger_rejected
covers: connect_length_thresholds -- connect_addrlen_over_storage_is_einval, connect_negative_addrlen_is_einval, connect_addrlen_zero_is_einval, connect_one_byte_is_einval_with_ledger
covers: connect_on_a_fresh_socket_reaches_tcp_v4_connect -- connect_fresh_four_bytes_is_einval, connect_fresh_af_unix_is_eafnosupport, connect_fresh_af_unix_einval_rejected
covers: connect_attempt_is_declined_not_refused -- connect_fresh_attempt_declines
covers: connect_af_unspec_is_a_disconnect -- connect_fresh_af_unspec_is_zero, connect_listening_af_unspec_declines, connect_accepted_af_unspec_declines
covers: connect_on_a_bound_socket_is_not_eisconn -- connect_bound_four_bytes_is_einval, connect_bound_four_bytes_eisconn_rejected, connect_bound_af_unix_is_eafnosupport, connect_bound_attempt_declines, connect_bound_af_unspec_declines
covers: connect_af_unspec_precedes_the_state_switch -- connect_listening_af_unspec_declines, connect_two_bytes_on_listening_is_eisconn, connect_two_bytes_on_fresh_is_einval
covers: socket_calls_decline_every_non_socket_fd_kind -- setsockopt_channel_is_enotsock, setsockopt_regular_file_is_enotsock, setsockopt_regular_file_success_rejected, setsockopt_write_only_file_is_enotsock, getsockopt_channel_success_rejected, getsockopt_regular_file_is_enotsock, getsockopt_regular_file_success_rejected, getsockopt_directory_is_enotsock, setsockopt_directory_is_enotsock, setsockopt_directory_success_rejected, getsockopt_directory_success_rejected, getsockopt_write_only_file_is_enotsock, getsockopt_write_only_file_success_rejected, setsockopt_write_only_file_success_rejected, getsockopt_channel_is_enotsock, setsockopt_channel_success_rejected, setsockopt_channel_ebadf_rejected, setsockopt_regular_file_ebadf_rejected, setsockopt_write_only_file_ebadf_rejected, setsockopt_directory_ebadf_rejected, getsockopt_channel_ebadf_rejected, getsockopt_regular_file_ebadf_rejected, getsockopt_write_only_file_ebadf_rejected, getsockopt_directory_ebadf_rejected
covers: socket_calls_unknown_level_never_beats_the_fd -- setsockopt_closed_fd_is_ebadf, setsockopt_regular_file_is_enotsock, setsockopt_regular_file_enoprotoopt_rejected, getsockopt_closed_fd_is_ebadf, getsockopt_regular_file_is_enotsock, getsockopt_regular_file_enoprotoopt_rejected
covers: setsockopt_negative_optlen_never_beats_the_fd -- setsockopt_negative_optlen_on_closed_fd_is_ebadf, setsockopt_negative_optlen_on_regular_file_is_enotsock, setsockopt_negative_optlen_on_regular_file_einval_rejected, setsockopt_negative_optlen_on_closed_fd_einval_rejected, setsockopt_negative_optlen_on_write_only_file_is_enotsock, setsockopt_negative_optlen_on_write_only_file_einval_rejected
covers: socket_calls_null_pointers_never_beat_the_fd -- getsockopt_null_pointers_on_regular_file_is_enotsock, getsockopt_null_pointers_on_regular_file_efault_rejected, getsockopt_null_pointers_on_regular_file_einval_rejected, getsockopt_null_pointers_on_write_only_file_is_enotsock, getsockopt_null_pointers_on_write_only_file_einval_rejected
covers: getpeername_enotconn_covers_reset_but_not_close_wait -- getpeername_fresh_is_enotconn, getpeername_bound_is_enotconn, getpeername_listening_is_enotconn, getpeername_reset_is_enotconn, getpeername_connected_declines
covers: getpeername_success_on_a_reset_socket_is_rejected -- getpeername_reset_is_enotconn
covers: getsockname_declines_on_every_socket_state -- getsockname_fresh_declines, getsockname_bound_declines, getsockname_listening_declines, getsockname_connected_declines, getsockname_reset_declines
covers: unknown_level_is_enoprotoopt_setting_and_eopnotsupp_getting -- setsockopt_unknown_level_is_enoprotoopt, setsockopt_unknown_level_eopnotsupp_rejected, getsockopt_unknown_level_is_eopnotsupp, getsockopt_unknown_level_enoprotoopt_rejected
covers: negative_optlen_beats_the_unknown_level -- setsockopt_negative_optlen_is_einval, setsockopt_negative_optlen_enoprotoopt_rejected
covers: a_known_level_is_declined -- setsockopt_sol_ip_declines, setsockopt_sol_socket_declines, setsockopt_sol_tcp_declines, getsockopt_sol_ip_declines, getsockopt_sol_socket_declines, getsockopt_sol_tcp_declines, setsockopt_unknown_level_is_enoprotoopt, getsockopt_unknown_level_is_eopnotsupp, setsockopt_level_two_pow_32_declines, getsockopt_level_two_pow_32_declines
covers: shutdown_rejects_a_bad_how_on_every_socket_state -- shutdown_bad_how_on_fresh_is_einval, shutdown_bad_how_on_bound_is_einval, shutdown_bad_how_on_listening_is_einval, shutdown_bad_how_on_connected_is_einval, shutdown_bad_how_on_reset_is_einval, shutdown_minus_one_how_is_einval
covers: shut_wr_on_a_listener_is_zero_and_a_no_op -- shut_wr_on_listening_is_zero, shut_wr_on_listening_enotconn_rejected, shut_wr_on_listening_einval_rejected
covers: shutdown_declines_where_it_would_have_to_drop_the_bits -- shut_rd_on_fresh_declines, shut_wr_on_fresh_declines, shut_rdwr_on_fresh_declines, shut_rd_on_bound_declines, shut_wr_on_bound_declines, shut_rdwr_on_bound_declines, shut_rd_on_connected_declines, shut_wr_on_connected_declines, shut_rdwr_on_connected_declines, shut_rd_on_reset_declines, shut_wr_on_reset_declines, shut_rdwr_on_reset_declines, shut_rd_on_listening_declines, shut_rdwr_on_listening_declines, shutdown_bad_how_on_fresh_is_einval, shut_wr_on_listening_is_zero
unpinned: send_emits_on_the_connections_channel -- the socket is `accepted_socket_model`'s, connected at a FIN, and this twin's `send_on_socket` declines every connected state beyond Rocq (the spec twin's send section): a reset the kernel has already processed behind the FIN makes the send -EPIPE, `tcp_reset` (net/ipv4/tcp_input.c, Linux v6.18.46) leaving TCP_CLOSE and `sk_stream_wait_connect` (net/core/stream.c, v6.18.46) reporting it, so Rocq's delivery is not the only answer; pinned as `sendto_close_wait_declines`, an `iff` with `Unmodeled` that refuses every `Ok` at this input, the unledgered send Rocq's second conjunct refuses included; Rocq's ledgered delivery is also refused by name as `sendto_close_wait_delivery_rejected`
unpinned: send_short_is_a_prefix_and_zero_is_not -- `tcp_sendmsg_locked` (net/ipv4/tcp.c, Linux v6.18.46) returns the bytes it copied, never more than asked, and on a non-empty request an errno rather than 0 when nothing was copied; but the socket is connected, which the dispatched arm declines (`sendto_close_wait_declines`, `sendto_established_declines`, `sendto_established_short_delivery_rejected`), so the claim is `send_bytes`'s, which no arm references, and is pinned on the definition directly by `send_bytes_delivers_a_prefix_iff`: the prefix and never more than asked by its `ds = List.take ds.length [97, 98]`, never empty by its `1 ≤`, with `send_bytes_readable_efault_rejected` refusing -EFAULT while the bytes read; never more than the request where fewer bytes are asked than read, a bound `take` cannot carry, by `send_bytes_short_total_delivers_a_prefix_iff` and `send_bytes_short_total_overrun_rejected`; the errno rather than 0 by `send_bytes_unreadable_is_efault` and `send_bytes_unreadable_zero_rejected`; and the edge of a non-empty request, a zero-length one answering 0, by `send_bytes_zero_length_is_zero` and `send_bytes_zero_length_efault_rejected`
unpinned: send_errno_return_rejected -- on `accepted_socket_model`'s connected socket, which the dispatched arm declines (`sendto_close_wait_declines`), so every answer there, the refused -EINTR included, is refused by that `iff`; -EINTR on a live connection with room to send needs a signal: `sk_stream_wait_memory` (net/core/stream.c, Linux v6.18.46) returns it only through sock_intr_errno when `signal_pending(current)` holds, and the model never reaches a syscall with an unblocked signal pending: its one pending signal, a blocked SIGABRT (`State.ProcState.procst_sigabrt_pending`), does not set TIF_SIGPENDING (`wants_signal`, kernel/signal.c:946-949, and `recalc_sigpending_tsk`, :159-175, Linux v6.18.46), the `rt_sigprocmask` that unblocks it kills the process (`Kernel.Signal.sigmask_deliver_model`), and no signal from outside the process is modeled
unpinned: send_flag_word_must_be_exactly_nosignal -- its third conjunct is a delivery on `accepted_socket_model`'s connected socket, which this twin declines beyond Rocq (`sendto_close_wait_declines`, Rocq's delivery refused as `sendto_close_wait_delivery_rejected`): a reset the kernel has already processed behind the FIN makes the send -EPIPE, `tcp_reset` (net/ipv4/tcp_input.c, Linux v6.18.46) leaving TCP_CLOSE and `sk_stream_wait_connect` (net/core/stream.c, v6.18.46) reporting it; the gate itself is pinned on both sides on the fresh socket, the two declines as `sendto_flagless_declines`, `sendto_flagless_epipe_rejected`, `sendto_dontwait_declines` and `sendto_dontwait_epipe_rejected`, and the exact word's answer as `sendto_fresh_socket_is_epipe` and `sendto_high_flag_half_is_dropped`
unpinned: send_consumes_the_pending_reset_once -- the first half is a connected socket with a reset at the head, which this twin declines beyond Rocq (`sendto_pending_reset_declines`, refusing Rocq's -ECONNRESET as `sendto_pending_reset_econnreset_rejected`): the segment may not have been processed when the send runs, and then `tcp_sendmsg_locked` (net/ipv4/tcp.c, Linux v6.18.46) copies bytes; the second half, the consumed reset's -EPIPE, is `sendto_reset_socket_is_epipe` and `sendto_reset_socket_econnreset_rejected`, because `sock_error` (include/net/sock.h, v6.18.46) clears the error as it reads it
unpinned: sendmsg_gathers_onto_the_same_channel -- a connected socket, which the dispatched arm declines beyond Rocq (`sendmsg_close_wait_declines`; Rocq's gather refused as `sendmsg_close_wait_delivery_rejected`); the reason is `send_emits_on_the_connections_channel`'s, `tcp_reset` (net/ipv4/tcp_input.c, Linux v6.18.46) and `sk_stream_wait_connect` (net/core/stream.c, v6.18.46); the gather's ledger, the header's and the descriptor's ranges first and then the payload's, is `send_bytes`'s and is pinned on the definition as `send_bytes_delivers_after_pre_iff`, `send_bytes_pre_after_payload_rejected` and `send_bytes_pre_dropped_rejected`
unpinned: sendmsg_reads_the_argument_never_the_struct_field -- its first conjunct is a gather on `accepted_socket_model`'s connected socket, which this twin declines beyond Rocq (`sendmsg_close_wait_declines`, Rocq's gather refused as `sendmsg_close_wait_delivery_rejected`), for `send_emits_on_the_connections_channel`'s reason, `tcp_reset` (net/ipv4/tcp_input.c, Linux v6.18.46) and `sk_stream_wait_connect` (net/core/stream.c, v6.18.46); the argument-not-field rule itself, `____sys_sendmsg` (net/socket.c, v6.18.46) overwriting `msg_flags` with the argument, is pinned on the fresh socket both ways as `sendmsg_field_flag_does_not_count`, `sendmsg_field_flag_epipe_rejected`, `sendmsg_field_dontwait_is_ignored` and `sendmsg_field_dontwait_unmodeled_rejected`
covers: sendmsg_resolves_the_fd_before_the_header -- sendmsg_closed_fd_is_ebadf_unledgered, sendmsg_prehost_channel_is_enotsock, sendmsg_closed_fd_unreadable_header_is_ebadf, sendmsg_closed_fd_unreadable_header_unmodeled_rejected
unpinned: sendto_unmapped_buffer_in_range_faults_on_the_copy -- its first two conjuncts are an in-range unmapped buffer on `accepted_socket_model`'s CONNECTED socket, which this twin declines beyond Rocq (the spec twin's send section): `send_state` reads the FIN at the head as `SendGoes` and `send_on_socket` declines both connected arms, so Rocq's -EFAULT is not the only answer there and the -EPIPE Rocq refuses is refused by the decline; pinned as `sendto_unmapped_buffer_in_range_connected_declines`, an `iff` with `Unmodeled` that refuses every `Ok` at that input.  Its third conjunct, the same buffer on the LISTENING socket, is answered and pinned as `sendto_unmapped_buffer_on_listening_is_epipe`, with `sendto_unmapped_buffer_on_a_dead_socket_is_epipe` the same claim on a fresh socket
covers: recv_on_a_non_socket_descriptor -- recvfrom_channel_is_enotsock, recvfrom_channel_write_rejected, recvmsg_channel_is_enotsock, recvmsg_channel_write_rejected, recvmsg_cmsg_compat_declines, recvmsg_cmsg_compat_enotsock_rejected
covers: recv_declines_a_socket_descriptor -- recvfrom_fresh_socket_declines, recvfrom_fresh_socket_enotsock_rejected, recvmsg_connected_socket_declines, recvmsg_connected_socket_enotsock_rejected, recvfrom_states_channel_is_enotsock, recvfrom_states_channel_unmodeled_rejected, recvmsg_states_regular_file_is_enotsock, recvmsg_states_regular_file_unmodeled_rejected
covers: recv_argument_order_is_opposite -- recvfrom_high_buffer_beats_the_fd, recvfrom_high_buffer_ebadf_rejected, recvmsg_closed_fd_beats_the_header, recvmsg_closed_fd_efault_rejected
covers: socketpair_writes_the_descriptors_before_it_fails -- socketpair_inet_stream_iff, socketpair_unwritten_eopnotsupp_rejected, socketpair_wrong_numbers_rejected, socketpair_success_rejected
covers: socketpair_flag_check_precedes_the_writes -- socketpair_bad_flag_dispatched_is_einval, socketpair_bad_flag_writes_rejected, socketpair_bad_flag_af_unix_is_einval, socketpair_af_unix_declines
covers: socketpair_declines_the_partial_destination -- socketpair_sv_task_size_is_efault, socketpair_sv_task_size_written_rejected, socketpair_sv_task_size_minus_5_declines
covers: socketpair_wrap_would_pass_the_bare_walk -- socketpair_wrap_would_pass_the_bare_walk
covers: socketpair_wrap_dest_is_not_writable -- socketpair_wrap_dest_is_not_writable
covers: socketpair_wrapping_destination_is_efault -- socketpair_wrapping_destination_is_efault, socketpair_wrapping_destination_writes_rejected
covers: socketpair_high_range_reads -- socketpair_high_range_reads
covers: socketpair_high_range_would_pass_a_no_wrap_test -- socketpair_high_range_would_pass_a_no_wrap_test
covers: socketpair_past_long_max_is_not_writable -- socketpair_past_long_max_is_not_writable
covers: socketpair_past_long_max_at_the_checker -- socketpair_past_long_max_is_efault, socketpair_past_long_max_writes_rejected
covers: socketpair_dest_width_is_eight -- socketpair_sv_task_size_minus_8_writes_both, socketpair_sv_task_size_minus_8_efault_rejected, socketpair_sv_task_size_minus_7_declines, socketpair_sv_task_size_minus_3_is_efault
-/

/-! # Checks.Cases.Net.Socket — what the socket arms allow, read off against Linux

Worked examples over `Sys.Net.Socket`'s `socket_spec`, `socketpair_spec`,
`bind_spec`, `listen_spec`, `accept4_spec`, `connect_spec`,
`getsockname_spec`, `getpeername_spec`, `setsockopt_spec`, `getsockopt_spec`,
`shutdown_spec`, `sendto_spec`, `sendmsg_spec`, `recvfrom_spec` and
`recvmsg_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Net/Socket.v` for the arms tickets
S-Net-Socket-lifecycle, S-Net-Socket-options, S-Net-Socket-socket-accept
and S-Net-Socket-io port.  Not part of the trusted
specification: this file is QA on the definitions, written to be READ, and
every claim in it is a claim about what the kernel does, with the citation
beside it — net/socket.c and net/ipv4/af_inet.c at Linux v6.18.46 (commit
1f99e9ab748f) unless a pin says otherwise.

HOW THESE ARE STATED.  Every call goes through the dispatcher —
`syscall_spec` on a `SyscallInput` numbered 198 to 212 or 242 — so the table's `fd32`/`int32` narrowing is
under test with the arm, as Rocq's `check_syscall (mkInput …)` cases have it,
and every `fd32` the table applies has a pin whose descriptor has its high
half set (by arm: the accept, getsockname and option sections, the
narrowings section, and for 206, 207, 211 and 212 the `fd32` subsection
at the end of the receive section); the two raw
`socketpair_spec` flag pins, which quantify over every input and model, and
the option section's gate, ledger-reader and table pins, which state a
decided function or the table at one value, and the send section's direct
reads of `send_state`, whose connected answers every arm declines, and of
`send_bytes`, which no arm references, are the exceptions.  A decision is
pinned twice: an `iff` over EVERY outcome `o`, which fixes the admitted set
and refuses every other answer, `Unmodeled` included; and a refutation of
the concrete lie a kernel could tell there — the neighbouring arm's errno,
a ledger the copy never made, a write that never landed.  Both close by
`sys_norm` / `sys_refute`.  Where an arm draws from an errno set the `iff`
has one disjunct per member, in the association the readings produce.

THE COPY-IN LEDGER IS PART OF EVERY ANSWER.  `bind` and `connect` copy the
address with `move_addr_to_kernel` (net/socket.c:248-257, v6.18.46), and the spec
records that copy on exactly the arms the kernel performed it: the pins
below state the ledger on both sides of the copy in both directions, so a
model that ledgers everywhere and one that never ledgers both fail.

HOW ROCQ'S `socket` AND `accept4` CASES ARE READ HERE.  Rocq states most
of them as FILTERS over the checker — `accept_errno_set_is_exactly_these_three`
runs `accept4_answering` over every errno the error window encodes and
keeps the three the arm admits, `accept_success_return_is_exactly_the_lowest_free_fd`
runs it over 4096 candidate descriptors and keeps one.  Each filter becomes an `iff` over EVERY
outcome, which says the same thing at once: `accept4_listening_iff` admits
exactly three errnos and exactly one descriptor, and refuses every other
value by being an `iff`.  The exhaustion cases at the end of the channel
section run the dispatched arm at both sides of `conn_ix_exhausted`'s
boundary, on fixtures whose counter is written field by field because no
setter reaches `2^64 - 3` honestly.  The six `conn_channel` lemmas Rocq
proves — three beside the definition and three guarded ones over
`conn_ix_exhausted` — are twinned in the same section.  Rocq's send/recv
cases are the send and receive sections below, where every connected
socket is a decline beyond Rocq (the spec twin's send section), so the
cases Rocq states on one are registered `unpinned:` with the decline that
answers them named; its `setsockopt`/`getsockopt` cases are the option
sections below.  The pipe, /dev/null and /dev/urandom kinds, which Rocq's
`socket_call_model` never held, are pinned here.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Net.Socket

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The register lines the specs owe `sys_simp`

`Checks/Cases/Tactic.lean`'s header asks each spec for its unfolding
equation, and for that of every builder its post-states are spelled with,
at low priority; gates are decided, never unfolded, so `shut_how_ok`,
`socketpair_flags_ok`, `socketpair_modeled_b`, `socketpair_dest_writable`
and the three `sockaddr_in` readers are not registered.  `record_copyins`
is `Syscall.lean`'s and not yet in the shared register, so its line is
here too.  The lines live in this file rather than in `Tactic.lean`'s
register so that ports merge in any order. -/

attribute [sys_simp low]
  socket_spec.eq_1 accept4_spec.eq_1
  bind_spec.eq_1 listen_spec.eq_1 connect_spec.eq_1 getsockname_spec.eq_1
  getpeername_spec.eq_1 shutdown_spec.eq_1 socketpair_spec.eq_1
  socketpair_written.eq_1 socketpair_faulted.eq_1 socketpair_writes.eq_1
  socket_errnos.eq_1 accept_errnos.eq_1 conn_channel.eq_1
  bind_errnos.eq_1 listen_errnos.eq_1 socketpair_reserve_errnos.eq_1
  socketpair_create_errnos.eq_1 sock_fd.eq_1 record_copyins.eq_1

-- `Fs.File.lowest_fd`, which `socket_spec` and `accept4_spec` allocate
-- through, enters the reading locally: `Checks/Cases/Fs/File.lean` registers
-- the same equation for its own pins, and this file does not import it.
attribute [local sys_simp low] Sys.Fs.File.lowest_fd.eq_1

/-! ## A reading the shared set lacks

Under `record_copyins`, or behind a `match` on a closed memory read, an
errno alternative is reached only by the second (`+ground`) pass of
`sys_norm`, which evaluates the closed `errno_from es` to its `choose`
before the parent `bind` is read — so the errno's membership lands LAST,
behind the forged outcome's injectivity equations, where
`Checks/Cases/Tactic.lean`'s enumeration-first reading no longer applies.
A refutation then stops at `∀ e, <ret eq> → <model eq> → <events eq> →
¬ e = errno`.  These readings turn that into the conjunction the same pass
decides; the Tactic header's `errno_demo_eperm_needs_two_passes` measures
the shape they close. -/

/-- The three-antecedent chain a forged `Ok` leaves behind the errno.
model: a propositional reading for the normal form; no kernel claim -/
theorem forall_imp3_not_eq {α : Sort _} {p q r : α → Prop} {b : α} :
    (∀ a, p a → q a → r a → ¬ a = b) ↔ ¬ (p b ∧ q b ∧ r b) := by
  constructor
  · intro h hc
    exact h b hc.1 hc.2.1 hc.2.2 rfl
  · intro h a hp hq hr hab
    subst hab
    exact h ⟨hp, hq, hr⟩

/-- The two-antecedent chain, when one equation was already decided.
model: a propositional reading for the normal form; no kernel claim -/
theorem forall_imp2_not_eq {α : Sort _} {p q : α → Prop} {b : α} :
    (∀ a, p a → q a → ¬ a = b) ↔ ¬ (p b ∧ q b) := by
  constructor
  · intro h hc
    exact h b hc.1 hc.2 rfl
  · intro h a hp hq hab
    subst hab
    exact h ⟨hp, hq⟩

attribute [sys_simp] forall_imp3_not_eq forall_imp2_not_eq

/-! ## The constants these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes; these pins say what each one is. -/

/-- The bind/connect address-length bounds: `sizeof(struct sockaddr_storage)`
is `_K_SS_MAXSIZE` (include/uapi/linux/socket.h:8, v6.18.46), 128.
model: SOCKADDR_STORAGE_SIZE is the model's name for _K_SS_MAXSIZE; Uapi/Net.lean carries the citation -/
example : SOCKADDR_STORAGE_SIZE = 128 := by decide

/-- `sizeof(struct sockaddr_in)`, padded to `__SOCK_SIZE__`
(include/uapi/linux/in.h:259-268, v6.18.46), 16.
model: SOCKADDR_IN_SIZE is the model's name for __SOCK_SIZE__; Uapi/Net.lean carries the citation -/
example : SOCKADDR_IN_SIZE = 16 := by decide

/-- `sizeof(sa_family_t)`: the model's own constant, since the kernel spells
it as a `sizeof` and not a macro.
model: SA_FAMILY_SIZE is the model's spelling of sizeof(sa_family_t); Uapi/Net.lean carries the citation -/
example : SA_FAMILY_SIZE = 2 := by decide

/-- The two type flags the socketpair gate admits, and the type mask: 524288
is `O_CLOEXEC` on riscv64, 2048 is `O_NONBLOCK`, 15 is `SOCK_TYPE_MASK`.
model: SOCK_CLOEXEC and SOCK_NONBLOCK are spelled as O_CLOEXEC and O_NONBLOCK in include/linux/net.h, v6.18.46, which the evidence checker cannot evaluate; Uapi/Net.lean carries both citations -/
example : SOCK_CLOEXEC = 524288 ∧ SOCK_NONBLOCK = 2048 ∧ SOCK_TYPE_MASK = 15 := by decide

/-- The two families the socket arms distinguish.
kernel: include/linux/socket.h:AF_UNSPEC,AF_INET@v6.18.46 -/
example : AF_UNSPEC = 0 ∧ AF_INET = 2 := by decide

/-- The Sv48 user limit the socketpair destination pins spell as a numeral:
`0x800000000000`.
model: TASK_SIZE is the model's Sv48 limit (State.lean); the pins below write it as the numeral 140737488355328 -/
example : TASK_SIZE = 140737488355328 := by decide

/-- The errno sets `socket` and `accept` draw from: the descriptor table
filling up (-EMFILE from `alloc_fd`, -ENOMEM from `alloc_fdtable`) and the
socket table filling up (-ENFILE from `__sock_create` for `socket`, from
`do_accept`'s `sock_alloc` for `accept`), and nothing else.  The lists
themselves; what the ARMS allow of them is `socket_inet_stream_iff` and
`accept4_listening_iff`, Rocq's `accept_errno_set_is_exactly_these_three`
stated through the dispatcher.
kernel: fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:__sock_create,do_accept@v6.18.46 -/
example : socket_errnos = [ENOMEM, EMFILE, ENFILE] ∧ accept_errnos = [ENOMEM, EMFILE, ENFILE] := by
  decide

/-- The errno the port table hands `bind` and `listen`.
kernel: include/uapi/asm-generic/errno.h:EADDRINUSE@v6.18.46 -/
example : bind_errnos = [98] ∧ listen_errnos = [98] := by decide

/-! ## The fixtures

Every model below is `fixture_of` at the fd slot (and the file-system slot
where a regular file is needed), or `with_accepted` over one — the sole
setter that advances the accept queue and bumps the handed-over count,
which is how an accepted connection is REACHED and the only honest way to
write one down.  fd 9 is closed in every fixture but `socket_states_model`,
where it is the connected socket: elsewhere it is the fd the -EBADF pins
name. -/

/-- The peer every accepted connection here talks to: 0.0.0.0:0, the quiet
environment's. -/
def peer0 : PeerAddr := PeerAddr.mkPeer (Z_to_bv 32 0) (Z_to_bv 16 0)

/-- Rocq's `listening_socket_model`: the three channels and a LISTENING
socket at fd 3. -/
def listening_socket_model : Model :=
  fixture_of (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
                       (3, .FdSocket .SkListening) ])

/-- Rocq's `accepted_socket_model`: the model a successful accept leaves
behind — fd 4 carries the head connection's peer on channel 3 with its
script at end-of-stream, the queue has advanced and the handed-over count
is 1.  `State.fd_insert` prepends, which is why the new entry heads the
table. -/
def accepted_socket_model : Model :=
  with_accepted
    [ (4, .FdSocket (.SkConnected peer0 3 NFin)),
      (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
      (3, .FdSocket .SkListening) ]
    listening_socket_model

/-- Rocq's `connected_socket_model`: the accepted model with fd 4's script
generalised. -/
def connected_socket_model (rx : NetStream) : Model :=
  with_accepted
    [ (4, .FdSocket (.SkConnected peer0 3 rx)),
      (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
      (3, .FdSocket .SkListening) ]
    listening_socket_model

/-- Rocq's `reset_socket_model`: fd 3 is a connection the peer has RESET
and the program has already read the error from.  Through `with_accepted`
for the same reason: a connected socket can only have come from an
accept. -/
def reset_socket_model : Model :=
  with_accepted
    [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
      (3, .FdSocket (.SkReset peer0 3)) ]
    listening_socket_model

/-- Rocq's `fresh_socket_model`: a socket nothing has been done to, at fd 3. -/
def fresh_socket_model : Model :=
  fixture_of (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
                       (3, .FdSocket .SkFresh) ])

/-- Rocq's `bound_socket_model`: a socket bound to INADDR_ANY:0 and NOT
listened on. -/
def bound_socket_model : Model :=
  fixture_of (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
                       (3, .FdSocket .SkBound) ])

/-- Rocq's `socket_call_model`: one fd of each non-socket kind Rocq's table
held — stdin at 0, a read-only file at 3, a write-only file at 4, a
directory at 5 — over a file system holding "hi" and an empty file. -/
def socket_call_model : Model :=
  fixture_of (fds := [ (0, .FdChannel 0), (3, .FdFile [102] 0), (4, .FdFileW [103] 0), (5, .FdDir) ])
             (fs := [([102], [104, 105]), ([103], [])])

/-- The three non-socket kinds Rocq's table never needed: the read end of a
pipe at 6, /dev/null open read-write at 7, /dev/urandom at 8. -/
def socket_kinds_model : Model :=
  fixture_of (fds := [ (0, .FdChannel 0), (6, .FdPipe 7 false), (7, .FdDevNull true true),
                       (8, .FdUrandom) ])

/-- The peer of Rocq's `socket_states_model`: 1.2.3.4:443, network order. -/
def peer_1234 : PeerAddr := PeerAddr.mkPeer (Z_to_bv 32 16909060) (Z_to_bv 16 443)

/-- Rocq's `socket_states_model`: one fd per `SockState` constructor, written
out rather than reached — fresh at 6, bound at 7, listening at 8,
connected at 9 (script at end-of-stream), reset at 10.  9 and 10 carry the
SAME peer on purpose: the two are told apart by the STATE, never by the
address. -/
def socket_states_model : Model :=
  fixture_of (fds := [ (0, .FdChannel 0), (3, .FdFile [102] 0),
                       (6, .FdSocket .SkFresh), (7, .FdSocket .SkBound), (8, .FdSocket .SkListening),
                       (9, .FdSocket (.SkConnected peer_1234 3 NFin)),
                       (10, .FdSocket (.SkReset peer_1234 3)) ])
             (fs := [([102], [104, 105])])

/-- What `socket(AF_INET, SOCK_STREAM, 0)` leaves of `listening_socket_model`:
a FRESH socket at 4, the lowest free number, heading the table because
`State.fd_insert` prepends. -/
def socket_created_model : Model :=
  fixture_of (fds := [ (4, .FdSocket .SkFresh), (0, .FdChannel 0), (1, .FdChannel 1),
                       (2, .FdChannel 2), (3, .FdSocket .SkListening) ])

/-- A table with a HOLE at 3 — fd 4 is open, 3 is not — so the lowest free
number is 3 and not 5: the probe's `close(s1)` followed by a second
`socket` (socket_spec.c, `alloc`). -/
def socket_hole_model : Model :=
  fixture_of (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
                       (4, .FdSocket .SkFresh) ])

/-- …and the hole filled. -/
def socket_hole_filled_model : Model :=
  fixture_of (fds := [ (3, .FdSocket .SkFresh), (0, .FdChannel 0), (1, .FdChannel 1),
                       (2, .FdChannel 2), (4, .FdSocket .SkFresh) ])

/-- Rocq's `exhausted_listening_model`: `listening_socket_model` with the
handed-over counter at `2^64 - 3`, the first index `conn_ix_exhausted`
fires on.  Written field by field, as Rocq writes it, because `fixture_of`
fixes the counter at 0 and `with_accepted` only ever adds one to it: no
honest chain of accepts reaches this fixture in a run anyone will execute,
which is the point of pinning the arm there
(linux-process-semantics@ff0313ba4f:bugs/socket-conn-channel-wraps-at-2-64.md). -/
def exhausted_listening_model : Model :=
  Model.mkModelOf
    (FdState.mkFdState (m_fds listening_socket_model) (m_pipes listening_socket_model))
    listening_socket_model.m_vm
    (IoState.mkIoState (m_stdin listening_socket_model) (m_urandom listening_socket_model)
                       (m_net listening_socket_model) (Z_to_bv 64 (2 ^ 64 - 3)))
    listening_socket_model.m_fsys listening_socket_model.m_proc
    listening_socket_model.m_lim listening_socket_model.m_time

/-- Rocq's `last_usable_listening_model`: the counter at `2^64 - 4`, the
last index whose channel does not wrap. -/
def last_usable_listening_model : Model :=
  Model.mkModelOf
    (FdState.mkFdState (m_fds listening_socket_model) (m_pipes listening_socket_model))
    listening_socket_model.m_vm
    (IoState.mkIoState (m_stdin listening_socket_model) (m_urandom listening_socket_model)
                       (m_net listening_socket_model) (Z_to_bv 64 (2 ^ 64 - 4)))
    listening_socket_model.m_fsys listening_socket_model.m_proc
    listening_socket_model.m_lim listening_socket_model.m_time

/-- What the accept one below the wrap leaves: the head connection on fd 4,
reported on channel `2^64 - 1`, the last free one, with the counter moved
onto the boundary. -/
def last_usable_accepted_model : Model :=
  with_accepted
    [ (4, .FdSocket (.SkConnected peer0 (Z_to_bv 64 (2 ^ 64 - 1)) NFin)),
      (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
      (3, .FdSocket .SkListening) ]
    last_usable_listening_model

attribute [sys_simp low]
  peer0.eq_1 peer_1234.eq_1 listening_socket_model.eq_1 accepted_socket_model.eq_1
  connected_socket_model.eq_1 reset_socket_model.eq_1 fresh_socket_model.eq_1
  bound_socket_model.eq_1 socket_call_model.eq_1 socket_kinds_model.eq_1
  socket_states_model.eq_1 socket_created_model.eq_1 socket_hole_model.eq_1
  socket_hole_filled_model.eq_1 exhausted_listening_model.eq_1
  last_usable_listening_model.eq_1 last_usable_accepted_model.eq_1

/-! ## The memories

Each is a partial map that answers on exactly its own bytes, so a walk that
reads back is a walk over MAPPED bytes and nothing else. -/

/-- Rocq's `sockaddr_in_any_mem`: sixteen readable bytes at 4096 holding a
`struct sockaddr_in` for AF_INET, port 0, INADDR_ANY — the one address
`bind` accepts.  `sa_family_t` is host order, so AF_INET (2) is the single
nonzero byte; port and address are network order and both zero. -/
def sockaddr_in_any_mem : word → Option byte := fun a =>
  if 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 4112
  then some (if a = 4096 then 2 else 0) else none

/-- Rocq's `connect_addr_mem`: sixteen readable bytes at 8192 holding
AF_INET, port 80, 127.0.0.1 — a well-formed address, so what stops a
connect is always the fd or the state and never the address. -/
def connect_addr_mem : word → Option byte := fun a =>
  if a = 8192 then some 2            -- sin_family lo: AF_INET
  else if a = 8193 then some 0       -- sin_family hi
  else if a = 8194 then some 0       -- sin_port hi
  else if a = 8195 then some 80      -- sin_port lo
  else if a = 8196 then some 127     -- sin_addr
  else if a = 8197 then some 0
  else if a = 8198 then some 0
  else if a = 8199 then some 1
  else if 8199 < bv_unsigned a ∧ bv_unsigned a < 8208 then some 0   -- sin_zero
  else none

/-- The same 16 bytes with `sin_family` set to AF_UNIX (1), which is what
makes the -EAFNOSUPPORT case different from a truncation. -/
def connect_unix_family_mem : word → Option byte := fun a =>
  if a = 8192 then some 1 else connect_addr_mem a

/-- `sin_family` AF_UNSPEC (0), the disconnect request. -/
def connect_unspec_mem : word → Option byte := fun a =>
  if a = 8192 then some 0 else connect_addr_mem a

/-- `sockaddr_in_any_mem` widened to 128 readable bytes at 4096: the largest
address `move_addr_to_kernel` copies, `sin_zero` and the storage tail all
zero. -/
def sockaddr_in_any_mem128 : word → Option byte := fun a =>
  if 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 4224
  then some (if a = 4096 then 2 else 0) else none

/-- `connect_addr_mem` widened to 128 readable bytes at 8192. -/
def connect_addr_mem128 : word → Option byte := fun a =>
  if 8207 < bv_unsigned a ∧ bv_unsigned a < 8320 then some 0 else connect_addr_mem a

/-- Rocq's `wmem_open`: a writable view that answers everywhere, for the
socketpair pins whose destination must be known writable. -/
def wmem_open : word → Option byte := fun _ => some 0

/-! ## The calls, as the dispatcher sees them -/

/-- `socket(domain, type, protocol)`; nothing readable or writable, since
the call reads and writes no user memory. -/
def socket_in (domain type protocol : word) : SyscallInput :=
  SyscallInput.mkInput 198 [domain, type, protocol, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `accept(fd, addrp, addrlenp)`, the three-argument spelling the table
hands `accept4_spec` with a zero flags word. -/
def accept_in (fd addrp addrlenp : word) : SyscallInput :=
  SyscallInput.mkInput 202 [fd, addrp, addrlenp, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `accept4(fd, addrp, addrlenp, flags)`. -/
def accept4_in (fd addrp addrlenp flags : word) : SyscallInput :=
  SyscallInput.mkInput 242 [fd, addrp, addrlenp, flags, 0, 0] (fun _ => none) (fun _ => none)

/-- `bind(fd, addrp, addrlen)` over the readable memory `mem`. -/
def bind_in (fd addrp addrlen : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 200 [fd, addrp, addrlen, 0, 0, 0] mem (fun _ => none)

/-- `listen(fd, backlog)`; nothing readable or writable. -/
def listen_in (fd backlog : word) : SyscallInput :=
  SyscallInput.mkInput 201 [fd, backlog, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `connect(fd, addrp, addrlen)` over the readable memory `mem`. -/
def connect_in (fd addrp addrlen : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 203 [fd, addrp, addrlen, 0, 0, 0] mem (fun _ => none)

/-- `getsockname(fd, 4096, 4104)`: the address arguments are never read
by the arms this file has, so they are fixed. -/
def getsockname_in (fd : word) : SyscallInput :=
  SyscallInput.mkInput 204 [fd, 4096, 4104, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `getpeername(fd, 4096, 4104)`. -/
def getpeername_in (fd : word) : SyscallInput :=
  SyscallInput.mkInput 205 [fd, 4096, 4104, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `shutdown(fd, how)`. -/
def shutdown_in (fd how : word) : SyscallInput :=
  SyscallInput.mkInput 210 [fd, how, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `socketpair(family, type, protocol, sv)` over the writable view `wmem`;
nothing is readable, since the call reads no user memory. -/
def socketpair_in (family type protocol sv : word) (wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 199 [family, type, protocol, sv, 0, 0] (fun _ => none) wmem

attribute [sys_simp low]
  socket_in.eq_1 accept_in.eq_1 accept4_in.eq_1
  bind_in.eq_1 listen_in.eq_1 connect_in.eq_1 getsockname_in.eq_1 getpeername_in.eq_1
  shutdown_in.eq_1 socketpair_in.eq_1

/-! ## socket (198): the validation order, then the lowest free descriptor

`__sys_socket_create` (net/socket.c:1686, v6.18.46) refuses an unknown flag
bit first (:1697-1698) and masks the type (:1699); `__sock_create` (:1535)
refuses the family range (:1545-1546), then the type range (:1547-1548),
then a family with no `net_families` entry (:1590-1594); `inet_create`
(net/ipv4/af_inet.c:254, v6.18.46) refuses the protocol range (:265-266) and walks
`inetsw` (:272-290), -ESOCKTNOSUPPORT for an empty list and
-EPROTONOSUPPORT for a list with no match; `sock_map_fd` (net/socket.c:504, v6.18.46)
reserves the descriptor LAST (:507).  The probe is
linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/socket_spec.c, whose `order` mode issues every
refusal below in this order; the fixture is `listening_socket_model`, whose
lowest free descriptor is 4. -/

/-- AN UNKNOWN TYPE-FLAG BIT IS -EINVAL, AND IT IS TESTED FIRST:
`__sys_socket_create` refuses `(type & ~SOCK_TYPE_MASK) & ~(SOCK_CLOEXEC |
SOCK_NONBLOCK)` (net/socket.c:1697-1698, v6.18.46) before the family, the
type range and the protocol, so bit 8 of 257 beats protocol 17.
kernel: net/socket.c:__sys_socket_create@v6.18.46 -/
theorem socket_flag_bit_beats_protocol_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 257 17) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- …and it beats a family out of range: 9999 alone is -EAFNOSUPPORT
(`__sock_create`, net/socket.c:1545-1546, v6.18.46), but `__sys_socket_create`
has already answered -EINVAL on the flag bit.
kernel: net/socket.c:__sys_socket_create@v6.18.46 -/
theorem socket_flag_bit_beats_family_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 9999 257 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- SOCK_NONBLOCK IS DECLINED: it marks the new file O_NONBLOCK
(`__sys_socket`, net/socket.c:1743, v6.18.46, passes them at :1757 to
`sock_map_fd`, net/socket.c:504, v6.18.46, which hands them to
`sock_alloc_file`, net/socket.c:476, v6.18.46, at :513),
a notion the model does not carry, so the call is neither an errno nor a
descriptor.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- socknonblock -/
theorem socket_nonblock_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 2049 0) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the descriptor Linux hands out there is not admitted either.
kernel: net/socket.c:sock_map_fd,sock_alloc_file@v6.18.46 -/
theorem socket_nonblock_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 2049 0) listening_socket_model
        (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- SOCK_NONBLOCK WITH AN UNKNOWN BIT IS -EINVAL: 2305 carries bit 8 as well
as SOCK_NONBLOCK, and the unknown-bit test (net/socket.c:1697-1698,
v6.18.46) answers before anything reads the O_NONBLOCK one, so the decline
above does not cover this call.
kernel: net/socket.c:__sys_socket_create@v6.18.46 -/
theorem socket_nonblock_with_bad_bit_is_einval (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 2305 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- The family range: 9999 is `family >= NPROTO`, -EAFNOSUPPORT (:1545-1546).
probe: testing/syscall-check/tests/socket_spec.c#conform -- order -/
theorem socket_family_range_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 9999 1 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#1:ret=-EINVAL -- order -/
theorem socket_family_range_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 9999 1 0) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The family is a signed `int`: -1 is `family < 0`.
probe: testing/syscall-check/tests/socket_spec.c#conform -- order -/
theorem socket_family_minus_one_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in (Z_to_bv 64 (2 ^ 64 - 1)) 1 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- `AF_MAX` itself, 46, is out of range: the test is `>= NPROTO`.
probe: testing/syscall-check/tests/socket_spec.c#conform -- order -/
theorem socket_family_af_max_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 46 1 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- …and it is the LOW 32 BITS that are signed: a register whose high half is
all ones and whose low half is 9999 is the family 9999, not a negative one,
and both are -EAFNOSUPPORT alike.
probe: testing/syscall-check/tests/socket_spec.c#conform -- order -/
theorem socket_family_negative_register_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in (Z_to_bv 64 (-(2 ^ 32) + 9999)) 1 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#19:ret=-EINVAL -- order -/
theorem socket_family_negative_register_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in (Z_to_bv 64 (-(2 ^ 32) + 9999)) 1 0) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The type range: `SOCK_MAX`, 11, is -EINVAL (:1547-1548), after the family.
probe: testing/syscall-check/tests/socket_spec.c#conform -- order -/
theorem socket_type_range_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 11 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#4:ret=-EAFNOSUPPORT -- order -/
theorem socket_type_range_eafnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 11 0) listening_socket_model
        (Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- 15, the top of `SOCK_TYPE_MASK`, is in the mask and out of the range.
probe: testing/syscall-check/tests/socket_spec.c#conform -- order -/
theorem socket_type_mask_top_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 15 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- Family 43 is below AF_MAX even in v4.17 (include/linux/socket.h:211).
The type check in `__sock_create` therefore returns -EINVAL on every supported
kernel (net/socket.c:1224-1227, v4.17; net/socket.c:1545-1548, v6.18.46).
The call is the first one of
`linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/socket_spec.c#fail-closed --expect-unmodeled socket -- afmaxold`.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem t172_socket_af43_type_range_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 43 11 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- -EAFNOSUPPORT cannot win for family 43 with type 11: `__sock_create`
passes the family range and fails the type range (net/socket.c:1224-1227,
v4.17; net/socket.c:1545-1548, v6.18.46).
probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#1:ret=-EAFNOSUPPORT -- afmaxold -/
theorem t172_socket_af43_type_range_eafnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 43 11 0) listening_socket_model
        (Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- AF_INET has no pre-host filter in qemu-user, so protocol 5 with type 11
keeps Linux's -EINVAL; a gate keyed on the protocol alone would decline it.
probe: testing/syscall-check/tests/socket_spec.c#conform -- netlinkkept -/
theorem t172_socket_inet_type_range_proto_5_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 11 5) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- Family 17 (AF_PACKET) with type 11 keeps -EINVAL: the type range in
`__sock_create` (net/socket.c:1547-1548, v6.18.46) answers the same for every
family inside `NPROTO`.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem t172_socket_packet_family_type_range_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 17 11 5) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#4:ret=-EPROTONOSUPPORT -- netlinkkept -/
theorem t172_socket_unix_type_range_eprotonosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 1 11 5) listening_socket_model
        (Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#6:ret=-EPROTONOSUPPORT -- netlinkkept -/
theorem t172_socket_inet_type_range_proto_5_eprotonosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 11 5) listening_socket_model
        (Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#7:ret=-EPROTONOSUPPORT -- netlinkkept -/
theorem t172_socket_packet_family_type_range_eprotonosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 17 11 5) listening_socket_model
        (Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- THE TYPE RANGE BEATS THE FAMILY'S REGISTRATION: AF_UNIX is declined
below, but with type 11 the range test answers first, so the call is
-EINVAL and not a decline.
probe: testing/syscall-check/tests/socket_spec.c#conform -- order -/
theorem socket_type_range_beats_unmodeled_family_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 1 11 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#6:ret=-EAFNOSUPPORT -- order -/
theorem socket_type_range_on_af_unix_eafnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 1 11 0) listening_socket_model
        (Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- …and a model that declined every AF_UNIX call would decline here wrongly.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem socket_type_range_on_af_unix_unmodeled_rejected :
    ¬ syscall_spec (socket_in 1 11 0) listening_socket_model Unmodeled := by
  sys_refute

/-- THE FAMILY RANGE BEATS THE TYPE RANGE: 9999 with type 11 is -EAFNOSUPPORT.
probe: testing/syscall-check/tests/socket_spec.c#conform -- order -/
theorem socket_family_range_beats_type_range_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 9999 11 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#7:ret=-EINVAL -- order -/
theorem socket_family_range_beats_type_range_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 9999 11 0) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- AF_UNIX IS DECLINED: whether an in-range family has a `net_families`
entry (:1590-1594) is the kernel build's, so neither the descriptor nor
-EAFNOSUPPORT can be asserted.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- unixfam -/
theorem socket_af_unix_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 1 1 0) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem socket_af_unix_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 1 1 0) listening_socket_model (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem socket_af_unix_eafnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 1 1 0) listening_socket_model
        (Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- THE PROTOCOL RANGE IS AF_INET's: `inet_create`'s `protocol >= IPPROTO_MAX`
(net/ipv4/af_inet.c:265-266) is reached only through `net_families[PF_INET]`,
so 263 under AF_UNIX is judged by `unix_create` (net/unix/af_unix.c:1155-1156),
-EPROTONOSUPPORT for any protocol but 0 and PF_UNIX — and the family decline
(:1590-1594) comes first here, as the family lookup does in `__sock_create`.
kernel: net/socket.c:__sock_create; net/unix/af_unix.c:unix_create@v6.18.46 -/
theorem socket_af_unix_protocol_range_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 1 1 263) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- A model testing `IPPROTO_MAX` before the family would answer -EINVAL,
which no family but AF_INET gives.
kernel: net/ipv4/af_inet.c:inet_create; net/unix/af_unix.c:unix_create@v6.18.46 -/
theorem socket_af_unix_protocol_range_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 1 1 263) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and the -EPROTONOSUPPORT a kernel with AF_UNIX gives is declined, not
asserted: the register is the build's.
kernel: net/unix/af_unix.c:unix_create@v6.18.46 -/
theorem socket_af_unix_protocol_range_eprotonosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 1 1 263) listening_socket_model
        (Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- The last in-range family, 45, is declined like any other non-AF_INET one.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem socket_af_max_minus_one_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 45 1 0) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and neither build's answer is asserted: -EAFNOSUPPORT is a kernel without
CONFIG_MCTP (`net_families[45]` NULL, net/socket.c:1590-1594), while one with
it registers `PF_MCTP` (net/mctp/af_mctp.c:842-846 and, at :858, the
net/socket.c `sock_register` call).
kernel: net/socket.c:__sock_create; net/mctp/af_mctp.c:mctp_pf_create@v6.18.46 -/
theorem socket_af_max_minus_one_eafnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 45 1 0) listening_socket_model
        (Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- …nor MCTP's own -ESOCKTNOSUPPORT for a type other than SOCK_DGRAM
(`mctp_pf_create`, :811-812), the other build's answer.
kernel: net/mctp/af_mctp.c:mctp_pf_create@v6.18.46 -/
theorem socket_af_max_minus_one_esocktnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 45 1 0) listening_socket_model
        (Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- AF_UNSPEC, 0, is in range and has no `net_families` entry on any build the
model knows of; it is declined rather than answered all the same, since
the register is the build's.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem socket_af_unspec_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 0 1 0) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- The answer every in-tree build gives — `sock_register` (net/socket.c:3250)
refuses only `family >= NPROTO` (:3254-3257), and no caller of it names
PF_UNSPEC, so `net_families[0]` is NULL (:1590-1594) — is still the
register's, not the argument's, and is refused as certain.
kernel: net/socket.c:__sock_create,sock_register@v6.18.46 -/
theorem socket_af_unspec_eafnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 0 1 0) listening_socket_model
        (Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- SOCK_PACKET IS DECLINED: `__sock_create` rewrites `(PF_INET, SOCK_PACKET)`
to `PF_PACKET` (net/socket.c:1555-1559, v6.18.46) before `inet_create` runs, so
`packet_create` (net/packet/af_packet.c:3361, v6.18.46) answers, with -EPERM without
CAP_NET_RAW (:3369-3370) and a descriptor with it.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- packet -/
theorem socket_packet_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 10 0) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- At the probe's own protocol, 0, the unprivileged guest's -EPERM (:3369-3370)
is declined, not given…
kernel: net/socket.c:__sock_create; net/packet/af_packet.c:packet_create@v6.18.46 -/
theorem socket_packet_eperm_at_protocol_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 10 0) listening_socket_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  sys_refute

/-- …and so is the descriptor a CAP_NET_RAW guest gets.
kernel: net/socket.c:__sock_create; net/packet/af_packet.c:packet_create@v6.18.46 -/
theorem socket_packet_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 10 0) listening_socket_model (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- A model that dropped the rewrite and walked `inetsw[SOCK_PACKET]` would
answer -ESOCKTNOSUPPORT (an empty list); `packet_create`'s type test
(:3371-3373) takes SOCK_PACKET, so Linux never does.
kernel: net/socket.c:__sock_create; net/packet/af_packet.c:packet_create@v6.18.46 -/
theorem socket_packet_esocktnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 10 0) listening_socket_model
        (Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- …AT EVERY PROTOCOL, the negative ones included: the rewrite moves the
decline above `inet_create`'s protocol range, which a rewritten call never
reaches — `packet_create` casts the protocol to a `__be16` (:3366).
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- packetproto -/
theorem socket_packet_negative_protocol_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 10 (Z_to_bv 64 (2 ^ 64 - 1))) listening_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …and `IPPROTO_MAX`, 263, which `inet_create` would refuse, likewise.
kernel: net/socket.c:__sock_create; net/packet/af_packet.c:packet_create@v6.18.46 -/
theorem socket_packet_at_ipproto_max_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 10 263) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- A model judging SOCK_PACKET by `IPPROTO_MAX` would answer -EINVAL where
Linux answers -EPERM or succeeds.
kernel: net/socket.c:__sock_create; net/packet/af_packet.c:packet_create@v6.18.46 -/
theorem socket_packet_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 10 263) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and the -EPERM of an unprivileged guest is not admitted either: it is
declined, since a privileged one gets a descriptor.
kernel: net/packet/af_packet.c:packet_create@v6.18.46 -/
theorem socket_packet_eperm_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 10 (Z_to_bv 64 (2 ^ 64 - 1))) listening_socket_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  sys_refute

/-- SOCK_DGRAM IS DECLINED: the call would SUCCEED (`inetsw_array`'s UDP
entry, net/ipv4/af_inet.c:1161-1167, v6.18.46) with a socket whose protocol this model
does not have.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- dgram -/
theorem socket_dgram_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 2 0) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_dgram_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 2 0) listening_socket_model (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- SOCK_RAW IS DECLINED for the same reason; the probe's -EPERM (no
CAP_NET_RAW, `inet_create` :315-318) is one of the two answers the decline
covers.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- raw -/
theorem socket_raw_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 3 6) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and neither of the two is given: not the -EPERM of an unprivileged guest
(`inet_create` :315-318)…
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_raw_eperm_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 3 6) listening_socket_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  sys_refute

/-- …nor the descriptor a CAP_NET_RAW guest gets from the wildcard SOCK_RAW
entry (`inetsw_array`, :1177-1183).
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_raw_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 3 6) listening_socket_model (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- THE PROTOCOL RANGE IS -EINVAL ALONE: `inet_create` (net/ipv4/af_inet.c:
265-266, v6.18.46) returns there, and the spec does not admit the -ENFILE
`sock_alloc` (net/socket.c:1570-1575, v6.18.46) can answer before it — the
narrowing `socket_spec`'s docstring states.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_dgram_protocol_range_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 2 263) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#18:ret=-ESOCKTNOSUPPORT -- order -/
theorem socket_dgram_protocol_range_esocktnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 2 263) listening_socket_model
        (Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- …a model declining every SOCK_DGRAM call would decline this answer.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_dgram_protocol_range_unmodeled_rejected :
    ¬ syscall_spec (socket_in 2 2 263) listening_socket_model Unmodeled := by
  sys_refute

/-- A negative protocol is the same arm, and the same single answer.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_dgram_truncated_protocol_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 2 (Z_to_bv 64 (2 ^ 64 - 1))) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- SOCK_RAW past `IPPROTO_MAX` is the protocol range too, -EINVAL alone.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_raw_protocol_range_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 3 263) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- UDP UNDER SOCK_STREAM IS -EPROTONOSUPPORT ALONE: 17 is in range and is
neither `IPPROTO_IP` nor `IPPROTO_TCP`, so the walk over a non-empty
`inetsw[SOCK_STREAM]` ends with no match (net/ipv4/af_inet.c:272-290,
v6.18.46), and no -ENFILE is admitted ahead of it.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_udp_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 17) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#8:ret=-EINVAL -- order -/
theorem socket_stream_udp_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 17) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `IPPROTO_MAX` itself is out of range: -EINVAL alone.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_ipproto_max_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 263) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#10:ret=-EPROTONOSUPPORT -- order -/
theorem socket_stream_ipproto_max_eprotonosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 263) listening_socket_model
        (Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- The protocol is a signed `int`: -1 is `protocol < 0`, -EINVAL alone.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_negative_protocol_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 (Z_to_bv 64 (2 ^ 64 - 1))) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#11:ret=-EPROTONOSUPPORT -- order -/
theorem socket_stream_negative_protocol_eprotonosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 (Z_to_bv 64 (2 ^ 64 - 1))) listening_socket_model
        (Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- …and it is the LOW 32 BITS that are read: a set bit 32 above 263 is 263,
-EINVAL alone.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_truncated_ipproto_max_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 (Z_to_bv 64 (2 ^ 32 + 263))) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#13:ret=-EPROTONOSUPPORT -- order -/
theorem socket_stream_truncated_ipproto_max_eprotonosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 (Z_to_bv 64 (2 ^ 32 + 263))) listening_socket_model
        (Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- SCTP UNDER SOCK_STREAM IS DECLINED: `sctp_stream_protosw` is registered
when SCTP is built (net/sctp/protocol.c:1169, at :1286), so the walk's
answer is the build's, a descriptor or -EPROTONOSUPPORT.
kernel: net/ipv4/af_inet.c:inet_create,inet_register_protosw@v6.18.46 -/
theorem socket_stream_sctp_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 132) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_sctp_eprotonosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 132) listening_socket_model
        (Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- MPTCP likewise: `mptcp_protosw` (net/mptcp/protocol.c:4198-4201, at :4271).
kernel: net/ipv4/af_inet.c:inet_create,inet_register_protosw@v6.18.46 -/
theorem socket_stream_mptcp_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 262) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_mptcp_eprotonosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 262) listening_socket_model
        (Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- PROTOCOL 256 UNDER SOCK_STREAM IS -EPROTONOSUPPORT: it is below
`IPPROTO_MAX` (263), it is neither SCTP nor MPTCP, and it is neither
`IPPROTO_IP` nor `IPPROTO_TCP`, so the walk over `inetsw[SOCK_STREAM]` ends
with no match (net/ipv4/af_inet.c:272-290, v6.18.46).  Only 132 and 262 are
carved out of that verdict, so this call is answered and not declined.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_protocol_256_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 256) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- …so a decline here is refused: it would lose the answer the walk gives.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_protocol_256_unmodeled_rejected :
    ¬ syscall_spec (socket_in 2 1 256) listening_socket_model Unmodeled := by
  sys_refute

/-- …and no descriptor is handed out: the walk returns before `sock_map_fd`
(net/socket.c:504-515, v6.18.46) reserves one.
kernel: net/socket.c:sock_map_fd; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_protocol_256_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 256) listening_socket_model (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- 257 IS THE SAME ARM: `IPPROTO_MAX` is 263 (include/uapi/linux/in.h:88-90,
Linux v6.18.46), so 257 passes `inet_create`'s range test
(net/ipv4/af_inet.c:265-266) and fails its walk (:272-290).
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_protocol_257_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 257) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- A decline is refused: no register of the kernel build decides 257.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_protocol_257_unmodeled_rejected :
    ¬ syscall_spec (socket_in 2 1 257) listening_socket_model Unmodeled := by
  sys_refute

/-- …and -EINVAL is refused: 257 is below `IPPROTO_MAX`, so the range test
(net/ipv4/af_inet.c:265-266, v6.18.46) does not fire.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_protocol_257_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 257) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- SOCK_RDM (4) AT 256 IS -ESOCKTNOSUPPORT: the protocol is in range and
`inetsw[SOCK_RDM]` is empty, the walk's other verdict
(net/ipv4/af_inet.c:272-290, v6.18.46).
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_rdm_protocol_256_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 4 256) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- …and a decline there is refused too.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_rdm_protocol_256_unmodeled_rejected :
    ¬ syscall_spec (socket_in 2 4 256) listening_socket_model Unmodeled := by
  sys_refute

/-- 255 IS IN RANGE AND UNREGISTERED, as 256 and 257 are: the walk's
-EPROTONOSUPPORT (net/ipv4/af_inet.c:272-290, v6.18.46), with no -ENFILE
alternative, since the spec narrows `sock_alloc`'s failure away on this arm.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_stream_255_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 255) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_proto_range.c#reject --mutate socket#1:ret=-EINVAL -- edges -/
theorem socket_stream_255_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 255) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- SOCK_RDM at 255 is the empty list's -ESOCKTNOSUPPORT, alone.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_rdm_255_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 4 255) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_proto_range.c#reject --mutate socket#2:ret=-EINVAL -- edges -/
theorem socket_rdm_255_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 4 255) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- SOCK_SEQPACKET IS DECLINED: `sctp_seqpacket_protosw` (net/sctp/protocol.c:1162,
at :1285) registers the type when SCTP is built.
kernel: net/ipv4/af_inet.c:inet_create,inet_register_protosw@v6.18.46 -/
theorem socket_seqpacket_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 5 0) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_seqpacket_esocktnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 5 0) listening_socket_model
        (Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- SOCK_DCCP IS DECLINED, on the older supported kernels' account: at
v6.18.46 nothing registers type 6 (`net/dccp` is gone from the tree), so
this kernel answers -ESOCKTNOSUPPORT, and the decline costs coverage here,
never soundness.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_dccp_declines (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 6 0) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_dccp_esocktnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 6 0) listening_socket_model
        (Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- SOCK_RDM at protocol 0 is the empty list's -ESOCKTNOSUPPORT, alone.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_rdm_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 4 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#14:ret=-EPROTONOSUPPORT -- order -/
theorem socket_rdm_eprotonosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 4 0) listening_socket_model
        (Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- Type 0 has an empty `inetsw` list too: -ESOCKTNOSUPPORT alone.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_type_zero_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 0 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#15:ret=-EPROTONOSUPPORT -- order -/
theorem socket_type_zero_eprotonosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 0 0) listening_socket_model
        (Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- Type 7, inside the range and with an empty list: -ESOCKTNOSUPPORT alone.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_type_seven_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 7 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) listening_socket_model [] := by
  sys_norm

/-- THE PROTOCOL RANGE BEATS THE TYPE's EMPTY LIST: SOCK_RDM at 263 is
-EINVAL, not -ESOCKTNOSUPPORT, since `inet_create` tests the range
(net/ipv4/af_inet.c:265-266, v6.18.46) before it walks `inetsw`.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem socket_rdm_protocol_range_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 4 263) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#17:ret=-ESOCKTNOSUPPORT -- order -/
theorem socket_rdm_protocol_range_esocktnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 4 263) listening_socket_model
        (Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- THE SUCCESS PATH: `socket(AF_INET, SOCK_STREAM, 0)` matches the TCP entry
through the wildcard (:283-285) and answers one of four things — the
descriptor-table errnos -EMFILE and -ENOMEM (`alloc_fd`, fs/file.c:591-598, v6.18.46,
through `get_unused_fd_flags` in `sock_map_fd`), the socket-table -ENFILE
(`__sock_create`, net/socket.c:1570-1575, v6.18.46), or the LOWEST free descriptor,
4 here, installed as a fresh socket.  Nothing else: not another number,
not another errno.
probe: testing/syscall-check/tests/socket_spec.c#conform -- alloc -/
theorem socket_inet_stream_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 0) listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) socket_created_model []) := by
  sys_norm

/-- `IPPROTO_TCP` spelled out matches the same entry directly (:278-280).
probe: testing/syscall-check/tests/socket_spec.c#conform -- alloc -/
theorem socket_inet_tcp_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 6) listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) socket_created_model []) := by
  sys_norm

/-- SOCK_CLOEXEC IS ACCEPTED AND CHANGES NOTHING HERE: it sets the
descriptor's close-on-exec bit (`sock_map_fd`'s `get_unused_fd_flags`,
:507), which the model does not carry and no arm reads.
probe: testing/syscall-check/tests/socket_spec.c#conform -- alloc -/
theorem socket_cloexec_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 524289 0) listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) socket_created_model []) := by
  sys_norm

/-- ALL THREE ARGUMENTS ARE 32 BITS: a register-negative family whose low
half is AF_INET, and a type and protocol with garbage above bit 31, are
the call `(2, 1, 6)`.
probe: testing/syscall-check/tests/socket_spec.c#conform -- alloc -/
theorem socket_truncated_arguments_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in (Z_to_bv 64 (-(2 ^ 32) + 2)) (Z_to_bv 64 (2 ^ 32 + 1))
                            (Z_to_bv 64 (2 ^ 32 + 6)))
                 listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) socket_created_model []) := by
  sys_norm

/-- A SOCKET IS THE LOWEST FREE FD: 5, with 4 free, is refused.
probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#1:ret+1 -- alloc -/
theorem socket_non_lowest_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 0) listening_socket_model (Ok (mkEffect 5 [] []) m' evs) := by
  sys_refute

/-- …and never one already open: 3 is the listener.
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem socket_open_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 0) listening_socket_model (Ok (mkEffect 3 [] []) m' evs) := by
  sys_refute

/-- -EPERM is not one of `socket`'s failures on this path: `inet_create`
raises it for SOCK_RAW alone (:315-318).  This and the four pins after it
are stated on the probe's call #5, the 32-bit-truncated `(2, 1, 6)` of
`socket_truncated_arguments_iff`: it is the one `alloc` call whose return
the CASE lines forge, placed last so a forged failure disturbs nothing.
probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#5:ret=-EPERM -- alloc -/
theorem socket_eperm_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in (Z_to_bv 64 (-(2 ^ 32) + 2)) (Z_to_bv 64 (2 ^ 32 + 1))
                            (Z_to_bv 64 (2 ^ 32 + 6)))
        listening_socket_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  sys_refute

/-- …nor -EAGAIN, which no function on the path spells.
probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#5:ret=-EAGAIN -- alloc -/
theorem socket_eagain_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in (Z_to_bv 64 (-(2 ^ 32) + 2)) (Z_to_bv 64 (2 ^ 32 + 1))
                            (Z_to_bv 64 (2 ^ 32 + 6)))
        listening_socket_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- THE THREE FAILURES STAY LIVE, each leaving the table alone: -EMFILE past
the soft `RLIMIT_NOFILE` (`alloc_fd`, fs/file.c:591-593, v6.18.46)…
probe: testing/syscall-check/tests/socket_spec.c#conform --mutate socket#5:ret=-EMFILE -- alloc -/
theorem socket_emfile_admitted :
    syscall_spec (socket_in (Z_to_bv 64 (-(2 ^ 32) + 2)) (Z_to_bv 64 (2 ^ 32 + 1))
                            (Z_to_bv 64 (2 ^ 32 + 6)))
        listening_socket_model
      (Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []) := by
  sys_norm

/-- …-ENFILE when `sock_alloc` fails (`__sock_create`, net/socket.c:1570-1575, v6.18.46)…
probe: testing/syscall-check/tests/socket_spec.c#conform --mutate socket#5:ret=-ENFILE -- alloc -/
theorem socket_enfile_admitted :
    syscall_spec (socket_in (Z_to_bv 64 (-(2 ^ 32) + 2)) (Z_to_bv 64 (2 ^ 32 + 1))
                            (Z_to_bv 64 (2 ^ 32 + 6)))
        listening_socket_model
      (Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model []) := by
  sys_norm

/-- …and -ENOMEM when the descriptor table cannot grow (`alloc_fdtable`,
fs/file.c:242, v6.18.46, through `expand_files` :595-598).
probe: testing/syscall-check/tests/socket_spec.c#conform --mutate socket#5:ret=-ENOMEM -- alloc -/
theorem socket_enomem_admitted :
    syscall_spec (socket_in (Z_to_bv 64 (-(2 ^ 32) + 2)) (Z_to_bv 64 (2 ^ 32 + 1))
                            (Z_to_bv 64 (2 ^ 32 + 6)))
        listening_socket_model
      (Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []) := by
  sys_norm

/-- A SUCCESS INSTALLS THE DESCRIPTOR: 4 with the table unchanged is refused,
since `fd_install` (fs/file.c, called at net/socket.c:515) is what makes the number a socket.
kernel: net/socket.c:sock_map_fd@v6.18.46 -/
theorem socket_success_leaves_table_rejected (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 0) listening_socket_model
        (Ok (mkEffect 4 [] []) listening_socket_model evs) := by
  sys_norm
  intro h
  exact h.elim

/-- A CLOSED NUMBER IS REUSED, AND IT IS THE LOWEST: with 3 free and 4 open the
socket lands on 3, not 5 — `alloc_fd`'s scan starts at the lowest free bit
(fs/file.c:570, v6.18.46).
probe: testing/syscall-check/tests/socket_spec.c#conform -- alloc -/
theorem socket_reuses_the_hole_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 0) socket_hole_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) socket_hole_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) socket_hole_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) socket_hole_model [])
       ∨ o = Ok (mkEffect 3 [] []) socket_hole_filled_model []) := by
  sys_norm

/-- The probe's forged answer: `ret+1` on the reused 3 is 4, a number the
table already holds — `alloc_fd`'s scan (fs/file.c:570, Linux v6.18.46) never
returns a set bit.
probe: testing/syscall-check/tests/socket_spec.c#reject --mutate socket#4:ret+1 -- alloc -/
theorem socket_hole_open_number_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 0) socket_hole_model (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- …and 5, the answer of an allocator that skips the hole for the top of the
table, is refused on the reading alone.
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem socket_hole_skipped_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socket_in 2 1 0) socket_hole_model (Ok (mkEffect 5 [] []) m' evs) := by
  sys_refute

/-- …down to a STANDARD STREAM's number: `socket_states_model` has stdout
closed, so the socket lands on 1.  This is the `conn_channel` docstring's
point about descriptors versus channels, on the creating side.
kernel: fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:__sock_create@v6.18.46 -/
theorem socket_on_states_model_iff (o : outcome SyscallEffect) :
    syscall_spec (socket_in 2 1 0) socket_states_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) socket_states_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) socket_states_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) socket_states_model [])
       ∨ o = Ok (mkEffect 1 [] [])
              (fixture_of (fds := [ (1, .FdSocket .SkFresh), (0, .FdChannel 0), (3, .FdFile [102] 0),
                                    (6, .FdSocket .SkFresh), (7, .FdSocket .SkBound),
                                    (8, .FdSocket .SkListening),
                                    (9, .FdSocket (.SkConnected peer_1234 3 NFin)),
                                    (10, .FdSocket (.SkReset peer_1234 3)) ])
                         (fs := [([102], [104, 105])])) []) := by
  sys_norm

/-! ## bind (200): the fd is resolved before the address

`__sys_bind` (net/socket.c:1889, v6.18.46): `fd_empty` is -EBADF (:1896-1897),
`sock_from_file` is -ENOTSOCK (:1898-1900), and only then
`move_addr_to_kernel` (:1902).  So neither errno carries a copy-in ledger,
and an unreadable address changes neither. -/

/-- A closed fd with an unreadable address is -EBADF and nothing else: the
address is never touched.
kernel: net/socket.c:__sys_bind@v6.18.46 -/
theorem bind_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (bind_in 9 8192 16 (fun _ => none)) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) listening_socket_model [] := by
  sys_norm

/-- …not -ENOTSOCK, which needs an open file to test.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#1:ret=-ENOTSOCK -- bad -/
theorem bind_closed_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 9 8192 16 (fun _ => none)) listening_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- A channel fd with an UNREADABLE address is -ENOTSOCK: the socket test
precedes the copy, so nothing faults and nothing is ledgered.  This is the
half that differs from `connect`, which copies first.
kernel: net/socket.c:__sys_bind,sock_from_file@v6.18.46 -/
theorem bind_channel_fd_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (bind_in 1 8192 16 (fun _ => none)) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) listening_socket_model [] := by
  sys_norm

/-- …and the -EFAULT a copy-first model would give is refuted: `bind`'s
`sock_from_file` (:1898) runs before `move_addr_to_kernel` (:1902).
kernel: net/socket.c:__sys_bind@v6.18.46 -/
theorem bind_channel_fd_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 1 8192 16 (fun _ => none)) listening_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A regular file is -ENOTSOCK however well-formed the address: the
verdict is `sock_from_file`'s one comparison against `socket_file_ops`.
kernel: net/socket.c:__sys_bind,sock_from_file@v6.18.46 -/
theorem bind_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 16 sockaddr_in_any_mem) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …not the -EINVAL a length or state check would give.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#3:ret=-EINVAL -- bad -/
theorem bind_regular_file_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 16 sockaddr_in_any_mem) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A directory fd: the same comparison, the same -ENOTSOCK.
kernel: net/socket.c:__sys_bind,sock_from_file@v6.18.46 -/
theorem bind_directory_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (bind_in 5 4096 16 sockaddr_in_any_mem) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- A pipe end: its `f_op` is `pipeanon_fops` (`create_pipe_files`,
fs/pipe.c:946), not `socket_file_ops`.
kernel: net/socket.c:__sys_bind,sock_from_file; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem bind_pipe_end_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (bind_in 6 4096 16 sockaddr_in_any_mem) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- /dev/null: `null_fops` (drivers/char/mem.c:644) fails the same
comparison.
kernel: net/socket.c:__sys_bind,sock_from_file@v6.18.46 -/
theorem bind_devnull_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (bind_in 7 4096 16 sockaddr_in_any_mem) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- /dev/urandom: `urandom_fops` (drivers/char/random.c:1572), the
constructor #712 added, takes the same answer explicitly.
kernel: net/socket.c:__sys_bind,sock_from_file@v6.18.46 -/
theorem bind_urandom_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (bind_in 8 4096 16 sockaddr_in_any_mem) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-! ## bind: `move_addr_to_kernel`, the length and then the copy

net/socket.c:248-257, v6.18.46: `ulen < 0 || ulen > 128` is -EINVAL (:250-251) and
`ulen == 0` returns 0 without copying (:252-253); both leave the ledger
EMPTY.  Past them `copy_from_user` (:254-255) either faults — -EFAULT,
nothing transferred — or has moved `ulen` bytes, which the ledger names on
every arm below it, the 16-byte -EINVAL of `inet_bind_sk` included. -/

/-- 129 bytes is past `sizeof(struct sockaddr_storage)`: -EINVAL before any
byte is read, so the ledger is empty although the address is readable.
kernel: net/socket.c:move_addr_to_kernel@v6.18.46 -/
theorem bind_addrlen_over_storage_is_einval (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 129 sockaddr_in_any_mem) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) fresh_socket_model [] := by
  sys_norm

/-- …a bind at that length cannot succeed.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#5:ret=0 -- bad -/
theorem bind_addrlen_over_storage_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 129 sockaddr_in_any_mem) fresh_socket_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and a ledger naming the 129 bytes is a copy the kernel never made.
kernel: net/socket.c:move_addr_to_kernel@v6.18.46 -/
theorem bind_addrlen_over_storage_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 129 sockaddr_in_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 129)]) m' evs) := by
  sys_refute

/-- `addrlen` is an `int`: all ones in the register is -1, refused by the
`ulen < 0` half with no copy.
probe: testing/syscall-check/tests/bind_listen_spec.c#conform -- bad -/
theorem bind_negative_addrlen_is_einval (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 (Z_to_bv 64 (2 ^ 64 - 1)) sockaddr_in_any_mem)
        fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) fresh_socket_model [] := by
  sys_norm

/-- …it does not wrap into a huge unsigned length that succeeds.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#4:ret=0 -- bad -/
theorem bind_negative_addrlen_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 (Z_to_bv 64 (2 ^ 64 - 1)) sockaddr_in_any_mem)
        fresh_socket_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A zero length copies nothing and cannot fault, even on an unreadable
address; `inet_bind_sk` then refuses it as shorter than 16.  The ledger is
empty.
probe: testing/syscall-check/tests/bind_listen_spec.c#conform -- bad -/
theorem bind_addrlen_zero_is_einval (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 8192 0 (fun _ => none)) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not -EFAULT: `if (ulen == 0) return 0;` (:252-253) precedes the copy.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#6:ret=-EFAULT -- bad -/
theorem bind_addrlen_zero_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 8192 0 (fun _ => none)) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …and not even a zero-length ledger entry: no `copy_from_user` ran.
kernel: net/socket.c:move_addr_to_kernel@v6.18.46 -/
theorem bind_addrlen_zero_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 8192 0 (fun _ => none)) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 0)]) m' evs) := by
  sys_refute

/-- An unreadable 16-byte address on a fresh socket is -EFAULT with an
empty ledger: the copy failed, so nothing left user memory.
probe: testing/syscall-check/tests/bind_listen_spec.c#conform -- fault -/
theorem bind_unreadable_address_is_efault (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 8192 16 (fun _ => none)) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] := by
  sys_norm

/-- An unreadable FOUR-byte address is -EFAULT as well: the copy fails
before `inet_bind_sk`'s 16-byte minimum is ever consulted.
probe: testing/syscall-check/tests/bind_listen_spec.c#conform -- fault -/
theorem bind_unreadable_four_bytes_is_efault (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 8192 4 (fun _ => none)) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] := by
  sys_norm

/-- …so -EFAULT precedes the 16-byte minimum: the -EINVAL a length-first
model would give four unreadable bytes is refuted.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#1:ret=-EINVAL -- fault -/
theorem bind_unreadable_address_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 8192 4 (fun _ => none)) fresh_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and a ledger beside the -EFAULT claims a copy that transferred nothing.
kernel: net/socket.c:move_addr_to_kernel@v6.18.46 -/
theorem bind_unreadable_address_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 8192 16 (fun _ => none)) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 16)]) m' evs) := by
  sys_refute

/-- Eight READABLE bytes are copied and then refused by `inet_bind_sk`'s
`addr_len < sizeof(struct sockaddr_in)` (net/ipv4/af_inet.c:453-454): the
-EINVAL carries the eight-byte ledger, because the copy came first.
kernel: net/ipv4/af_inet.c:inet_bind_sk; net/socket.c:move_addr_to_kernel@v6.18.46 -/
theorem bind_short_readable_address_is_einval_with_ledger (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 8 sockaddr_in_any_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 8)])
             fresh_socket_model [] := by
  sys_norm

/-- Fifteen bytes — one short of `sizeof(struct sockaddr_in)` — is the same
-EINVAL with a fifteen-byte ledger: the bound is `<`, not `≤`.
kernel: net/ipv4/af_inet.c:inet_bind_sk@v6.18.46 -/
theorem bind_fifteen_bytes_is_einval_with_ledger (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 15 sockaddr_in_any_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 15)])
             fresh_socket_model [] := by
  sys_norm

/-- The full `sizeof(struct sockaddr_storage)`, 128 bytes, is INSIDE
`move_addr_to_kernel`'s range (`ulen > 128` refuses, `ulen == 128` copies):
the fresh socket binds, with all 128 bytes ledgered.
probe: testing/syscall-check/tests/bind_listen_spec.c#conform -- addr -/
theorem bind_full_storage_length_binds (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 128 sockaddr_in_any_mem128) fresh_socket_model o ↔
      (o = Ok (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(4096, 128)])
              fresh_socket_model []
       ∨ o = Ok (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 128)])
              (fixture_of (fds := [ (3, .FdSocket .SkBound), (0, .FdChannel 0),
                                    (1, .FdChannel 1), (2, .FdChannel 2) ])) []) := by
  sys_norm

/-- …so -EINVAL at 128 is a lie: 129 is the first length refused.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#6:ret=-EINVAL -- addr -/
theorem bind_full_storage_length_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 128 sockaddr_in_any_mem128) fresh_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …the same -EINVAL WITHOUT its ledger is refused: the copy happened.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#2:drop-copyins -- fault -/
theorem bind_short_readable_address_unledgered_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 8 sockaddr_in_any_mem) fresh_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and readable bytes never fault.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#2:ret=-EFAULT -- fault -/
theorem bind_short_readable_address_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 8 sockaddr_in_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(4096, 8)]) m' evs) := by
  sys_refute

/-! ## bind: `__inet_bind`, the family, the address, the port

net/ipv4/af_inet.c:484-491, v6.18.46: a `sin_family` other than AF_INET is
-EAFNOSUPPORT unless it is AF_UNSPEC with `s_addr == INADDR_ANY`, which is
accepted as AF_INET.  A specific address (-EADDRNOTAVAIL's table, :504-507)
and a specific port (-EACCES's sysctl and -EADDRINUSE's port table,
:510-514 and :537-541) are declined. -/

/-- Sixteen bytes at 4096: `sin_family` low byte `fam`, port `port_hi:port_lo`
in network order, address `a0.a1.a2.a3`, `sin_zero` clear. -/
def sockaddr_mem (fam port_hi port_lo a0 a1 a2 a3 : byte) : word → Option byte := fun a =>
  if a = 4096 then some fam
  else if a = 4097 then some 0
  else if a = 4098 then some port_hi
  else if a = 4099 then some port_lo
  else if a = 4100 then some a0
  else if a = 4101 then some a1
  else if a = 4102 then some a2
  else if a = 4103 then some a3
  else if 4103 < bv_unsigned a ∧ bv_unsigned a < 4112 then some 0
  else none

/-- AF_UNIX (1), INADDR_ANY, port 0. -/
def sockaddr_unix_any_mem : word → Option byte := sockaddr_mem 1 0 0 0 0 0 0
/-- AF_UNSPEC (0), INADDR_ANY, port 0: the compatibility case. -/
def sockaddr_unspec_any_mem : word → Option byte := sockaddr_mem 0 0 0 0 0 0 0
/-- AF_UNSPEC with 127.0.0.1: outside the compatibility case. -/
def sockaddr_unspec_loopback_mem : word → Option byte := sockaddr_mem 0 0 0 127 0 0 1
/-- AF_INET, 127.0.0.1, port 0: a specific address. -/
def sockaddr_in_loopback_mem : word → Option byte := sockaddr_mem 2 0 0 127 0 0 1
/-- AF_INET, INADDR_ANY, port 80: a specific port. -/
def sockaddr_in_port80_mem : word → Option byte := sockaddr_mem 2 0 80 0 0 0 0

/-- A full-length AF_UNIX address on an AF_INET socket is -EAFNOSUPPORT
(:484-491), carrying the copy that read the family.
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_af_unix_is_eafnosupport (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 16 sockaddr_unix_any_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …NOT -EINVAL, the plausible guess.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#1:ret=-EINVAL -- addr -/
theorem bind_af_unix_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 16 sockaddr_unix_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)]) m' evs) := by
  sys_refute

/-- …and -EAFNOSUPPORT is decided FROM the copied family, so it carries the
ledger or it is not the kernel's answer.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#1:drop-copyins -- addr -/
theorem bind_af_unix_unledgered_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 16 sockaddr_unix_any_mem) fresh_socket_model
        (Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) m' evs) := by
  sys_refute

/-- AF_UNSPEC with INADDR_ANY is accepted as AF_INET (:485-490): the fresh
socket binds exactly as with AF_INET, the autobind's -EADDRINUSE included.
probe: testing/syscall-check/tests/bind_listen_spec.c#conform -- addr -/
theorem bind_af_unspec_any_binds (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 16 sockaddr_unspec_any_mem) fresh_socket_model o ↔
      (o = Ok (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(4096, 16)])
              fresh_socket_model []
       ∨ o = Ok (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)])
              (fixture_of (fds := [ (3, .FdSocket .SkBound), (0, .FdChannel 0),
                                    (1, .FdChannel 1), (2, .FdChannel 2) ])) []) := by
  sys_norm

/-- …so -EAFNOSUPPORT, the answer for every OTHER foreign family, is refuted
on it.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#2:ret=-EAFNOSUPPORT -- addr -/
theorem bind_af_unspec_any_eafnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 16 sockaddr_unspec_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 16)]) m' evs) := by
  sys_refute

/-- The compatibility case needs BOTH halves: AF_UNSPEC with a specific
address is -EAFNOSUPPORT (:489-490), not the declined specific-address
bind.
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_af_unspec_loopback_is_eafnosupport (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 16 sockaddr_unspec_loopback_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- A specific address is DECLINED: whether 127.0.0.1 is local is the
address table's answer (-EADDRNOTAVAIL, :504-507), which the model has no
way to give.  Both 0 and -EADDRNOTAVAIL are refused by the `iff`.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- bindaddr -/
theorem bind_specific_address_declines (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 16 sockaddr_in_loopback_mem) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- A specific port is DECLINED: -EACCES below the unprivileged floor
(:510-514) and -EADDRINUSE from the port table (:538-541) are both live on
Linux and neither is the model's to decide.
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_specific_port_declines (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 16 sockaddr_in_port80_mem) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …and the port is judged before the socket's state: on a BOUND socket,
where Linux would answer the double-bind -EINVAL, the same address still
declines — the probe's `bindport` case, which binds INADDR_ANY:0 first.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- bindport -/
theorem bind_specific_port_on_bound_declines (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 16 sockaddr_in_port80_mem) bound_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-! ## bind: the socket state

`__inet_bind` :527-529: `sk->sk_state != TCP_CLOSE || inet->inet_num` is
-EINVAL; past it `get_port` (:537-541) can answer only -EADDRINUSE
(`inet_csk_get_port`'s preset, net/ipv4/inet_connection_sock.c:506, v6.18.46) and
otherwise the socket is bound. -/

/-- A FRESH socket with INADDR_ANY:0 answers one of exactly two things, the
copy ledgered on both: -EADDRINUSE with the model untouched, or 0 with fd 3
moved to the bound state and the table otherwise unchanged
(`State.fd_insert` reseats the entry at the head).
probe: testing/syscall-check/tests/bind_listen_spec.c#conform -- addr -/
theorem bind_fresh_socket_iff (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 16 sockaddr_in_any_mem) fresh_socket_model o ↔
      (o = Ok (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(4096, 16)])
              fresh_socket_model []
       ∨ o = Ok (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)])
              (fixture_of (fds := [ (3, .FdSocket .SkBound), (0, .FdChannel 0),
                                    (1, .FdChannel 1), (2, .FdChannel 2) ])) []) := by
  sys_norm

/-- Port 0 never reaches the privileged-port test, so -EACCES is a lie here.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#6:ret=-EACCES -- addr -/
theorem bind_fresh_socket_eacces_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 16 sockaddr_in_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EACCES) [] [] [] [] [(4096, 16)]) m' evs) := by
  sys_refute

/-- A successful bind copied its 16 bytes: the success WITHOUT the ledger is
refused.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#4:drop-copyins -- addr -/
theorem bind_fresh_socket_unledgered_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 16 sockaddr_in_any_mem) fresh_socket_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- -EINVAL is a validation errno and not a `get_port` failure: it cannot
attach to the fresh socket's success path.
probe: testing/syscall-check/tests/errno_socket.c#reject --mutate bind:ret=-EINVAL -- bind -/
theorem bind_fresh_socket_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 16 sockaddr_in_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)]) m' evs) := by
  sys_refute

/-- A BOUND socket has `inet_num`, so a second bind is -EINVAL (:528), with
the copy ledgered.
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_bound_socket_is_einval (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 16 sockaddr_in_any_mem) bound_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)])
             bound_socket_model [] := by
  sys_norm

/-- …a second bind never succeeds.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate bind#3:ret=0 -- addr -/
theorem bind_bound_socket_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 16 sockaddr_in_any_mem) bound_socket_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)]) m' evs) := by
  sys_refute

/-- A LISTENING socket is TCP_LISTEN, the other conjunct of :528: -EINVAL.
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_listening_socket_is_einval (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 16 sockaddr_in_any_mem) listening_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)])
             listening_socket_model [] := by
  sys_norm

/-- A connection with BYTES pending and the peer's FIN behind them is
TCP_ESTABLISHED, or already TCP_CLOSE_WAIT, with a port either way, so
Linux answers -EINVAL from :528 — and the model DECLINES, because it reads
the head cell alone and cannot tell this script from the next pin's, where
the same head hides a reset.  Rocq answers -EINVAL here (`Sys/Net/Socket.v`,
`bind_spec`, its `NCons _ _` arm) and on the FIN head two pins below; the
connected arm is the one decline the twin makes beyond Rocq's, and this
pin states its cost.
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_live_connection_declines (o : outcome SyscallEffect) :
    syscall_spec (bind_in 4 4096 16 sockaddr_in_any_mem)
        (connected_socket_model (NCons (Z_to_bv 8 65) NFin)) o ↔ o = Unmodeled := by
  sys_norm

/-- THE REASON FOR THAT DECLINE: a byte with a RESET queued behind it.  The
RST is processed when the SEGMENT arrives — `tcp_validate_incoming` resets
on an in-order RST at once (net/ipv4/tcp_input.c:6183-6193, v6.18.46),
`tcp_reset` (:4678) purges the write queue only, through
`tcp_done_with_error` (:4663), and `tcp_done` runs `tcp_set_state(sk,
TCP_CLOSE)` (net/ipv4/tcp.c:5033), whose TCP_CLOSE arm puts the port back
(:2993-3000; `__inet_put_port`, net/ipv4/inet_hashtables.c:227) — while the
byte waits in `sk_receive_queue`, which `tcp_recvmsg_locked` drains before
it reports the error (net/ipv4/tcp.c:2703, ahead of :2744).  So before the
program has read anything, `bind(INADDR_ANY:0)` finds `sk_state ==
TCP_CLOSE` and `inet_num == 0`, passes :528 and AUTOBINDS: Linux answers 0
where a head-is-a-byte -EINVAL would be a confidently wrong answer.
kernel: net/ipv4/tcp_input.c:tcp_validate_incoming,tcp_reset; net/ipv4/tcp.c:tcp_done,tcp_recvmsg_locked; net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_byte_then_reset_declines (o : outcome SyscallEffect) :
    syscall_spec (bind_in 4 4096 16 sockaddr_in_any_mem)
        (connected_socket_model (NCons (Z_to_bv 8 65) NRst)) o ↔ o = Unmodeled := by
  sys_norm

/-- …so the -EINVAL Rocq's arm gives it, ledger and all, is refused: on
Linux that call can return 0.
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_byte_then_reset_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 4 4096 16 sockaddr_in_any_mem)
        (connected_socket_model (NCons (Z_to_bv 8 65) NRst))
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)]) m' evs) := by
  sys_refute

/-- A HALF-CLOSED connection (the peer's FIN consumed) is TCP_CLOSE_WAIT,
still with a port, so :528 would answer -EINVAL — and the model DECLINES,
because a reset can sit behind the FIN as it can behind a byte.  A peer
whose FIN came from a full `close` answers a RST to anything written to it
afterwards (a half-closed one, `shutdown(SHUT_WR)`, keeps reading), or
sends one when it closes with unread data; `tcp_rcv_state_process` runs
`tcp_validate_incoming` in CLOSE_WAIT too (net/ipv4/tcp_input.c:7019,
v6.18.46), so `tcp_reset` (:4678, err EPIPE there) has already run
`tcp_done` and put the port back (net/ipv4/tcp.c:5033, :2993-3000).  The
program cannot tell: `tcp_fin` set SOCK_DONE (net/ipv4/tcp_input.c:4727),
which `tcp_recvmsg_locked` tests (net/ipv4/tcp.c:2741) before `sk_err`
(:2744), so its read answers 0 on both sockets, while `bind(INADDR_ANY:0)`
answers -EINVAL on one and passes :528 to autobind on the other.  The model
holds the FIN cell and nothing behind it, so the only sound answer is a
decline; Rocq's `bind_spec` answers -EINVAL here and owes the change.
kernel: net/ipv4/tcp_input.c:tcp_rcv_state_process,tcp_validate_incoming,tcp_reset,tcp_fin; net/ipv4/tcp.c:tcp_done,tcp_recvmsg_locked; net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_half_closed_connection_declines (o : outcome SyscallEffect) :
    syscall_spec (bind_in 4 4096 16 sockaddr_in_any_mem) (connected_socket_model NFin) o ↔
      o = Unmodeled := by
  sys_norm

/-- …so the -EINVAL Rocq's arm gives the half-closed socket, ledger and all,
is refused: on Linux that call can return 0.
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_half_closed_connection_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 4 4096 16 sockaddr_in_any_mem) (connected_socket_model NFin)
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)]) m' evs) := by
  sys_refute

/-- A connection the peer has RESET, and the program has read the error
from, is DECLINED — not -EINVAL: `tcp_done` ran `tcp_set_state(sk,
TCP_CLOSE)` (net/ipv4/tcp.c:5033, v6.18.46), whose TCP_CLOSE arm calls
`inet_put_port` because `sk_clone_lock` cleared SOCK_BINDPORT_LOCK on the
accepted child (net/core/sock.c:2515), and `__inet_put_port` zeroed
`inet_num` (net/ipv4/inet_hashtables.c:227, v6.18.46).  Both conjuncts of :528 are
false: Linux AUTOBINDS and returns 0, a state the model cannot express.
kernel: net/ipv4/tcp.c:tcp_done,tcp_set_state; net/core/sock.c:sk_clone_lock; net/ipv4/inet_hashtables.c:__inet_put_port@v6.18.46 -/
theorem bind_reset_connection_declines (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 16 sockaddr_in_any_mem) reset_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- A connection whose script begins with a RESET the program has not read
yet: `tcp_done` runs when the SEGMENT arrives, so the socket may already be
unbound — declined for the same reason.
kernel: net/ipv4/tcp.c:tcp_done@v6.18.46 -/
theorem bind_pending_reset_declines (o : outcome SyscallEffect) :
    syscall_spec (bind_in 4 4096 16 sockaddr_in_any_mem) (connected_socket_model NRst) o ↔
      o = Unmodeled := by
  sys_norm

/-- …and a pending timeout likewise.
kernel: net/ipv4/tcp.c:tcp_done@v6.18.46 -/
theorem bind_pending_timeout_declines (o : outcome SyscallEffect) :
    syscall_spec (bind_in 4 4096 16 sockaddr_in_any_mem) (connected_socket_model NTimedOut) o ↔
      o = Unmodeled := by
  sys_norm

/-! ## listen (201)

`__sys_listen` (net/socket.c:1933, v6.18.46) resolves the fd first (:1938-1942);
`__sys_listen_socket` clamps the backlog and never refuses it (:1923-1925);
`inet_listen` (net/ipv4/af_inet.c:232) refuses a socket that is not
`SS_UNCONNECTED` (:239-240); `__inet_listen_sk` (:193-227) accepts
`TCPF_CLOSE | TCPF_LISTEN` (:198-199), re-listens by writing the backlog
alone (:201), and autobinds an unbound socket through
`inet_csk_listen_start` (net/ipv4/inet_connection_sock.c:1366, v6.18.46), the one call
on this path that can fail. -/

/-- A closed fd is -EBADF, resolved first.
kernel: net/socket.c:__sys_listen@v6.18.46 -/
theorem listen_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (listen_in 9 128) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_listen@v6.18.46 -/
theorem listen_closed_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (listen_in 9 128) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- A regular file is -ENOTSOCK.
kernel: net/socket.c:__sys_listen,sock_from_file@v6.18.46 -/
theorem listen_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (listen_in 3 128) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …and cannot listen.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate listen#4:ret=0 -- listen -/
theorem listen_regular_file_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (listen_in 3 128) socket_call_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- LISTEN WITHOUT BIND SUCCEEDS, or fails only as the autobind can: a fresh
socket answers -EADDRINUSE with the model untouched, or 0 with fd 3 moved
to the listening state.
probe: testing/syscall-check/tests/bind_listen_spec.c#conform -- listen -/
theorem listen_fresh_socket_iff (o : outcome SyscallEffect) :
    syscall_spec (listen_in 3 128) fresh_socket_model o ↔
      (o = Ok (mkEffect (errno_ret EADDRINUSE) [] []) fresh_socket_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (fixture_of (fds := [ (3, .FdSocket .SkListening), (0, .FdChannel 0),
                                    (1, .FdChannel 1), (2, .FdChannel 2) ])) []) := by
  sys_norm

/-- …-EINVAL, the connected socket's answer, is not the unbound socket's.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate listen#1:ret=-EINVAL -- listen -/
theorem listen_fresh_socket_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (listen_in 3 128) fresh_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …nor is -ENOMEM in the set: `inet_csk_get_port` presets -EADDRINUSE and
never overwrites it.
probe: testing/syscall-check/tests/errno_socket.c#reject --mutate listen:ret=-ENOMEM -- listen-unbound -/
theorem listen_fresh_socket_enomem_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (listen_in 3 128) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- A NEGATIVE backlog is clamped, not refused: `(unsigned int)backlog >
somaxconn` (:1924) wraps -1 to a huge count and clamps it down, so the
answer is the fresh socket's.  (The probe's `listen(s, -1)` is its third
listen on an already-listening socket, bind_listen_spec.c:223-225, so the
fresh-socket claim rests on the clamp.)
kernel: net/socket.c:__sys_listen_socket; net/ipv4/inet_connection_sock.c:inet_csk_get_port@v6.18.46 -/
theorem listen_negative_backlog_iff (o : outcome SyscallEffect) :
    syscall_spec (listen_in 3 (Z_to_bv 64 (2 ^ 64 - 1))) fresh_socket_model o ↔
      (o = Ok (mkEffect (errno_ret EADDRINUSE) [] []) fresh_socket_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (fixture_of (fds := [ (3, .FdSocket .SkListening), (0, .FdChannel 0),
                                    (1, .FdChannel 1), (2, .FdChannel 2) ])) []) := by
  sys_norm

/-- …and -EINVAL is refused on the fresh socket too; the -EINVAL the probe
refuses (bind_listen_spec.c, `listen#3`) is on a listening one.
kernel: net/socket.c:__sys_listen_socket@v6.18.46 -/
theorem listen_negative_backlog_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (listen_in 3 (Z_to_bv 64 (2 ^ 64 - 1))) fresh_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A BOUND socket already has a port, so `get_port` cannot fail: exactly 0,
with fd 3 moved to the listening state.
kernel: net/ipv4/inet_connection_sock.c:inet_csk_listen_start; net/ipv4/af_inet.c:__inet_listen_sk@v6.18.46 -/
theorem listen_bound_socket_is_zero (o : outcome SyscallEffect) :
    syscall_spec (listen_in 3 128) bound_socket_model o ↔
      o = Ok (mkEffect 0 [] [])
             (fixture_of (fds := [ (3, .FdSocket .SkListening), (0, .FdChannel 0),
                                   (1, .FdChannel 1), (2, .FdChannel 2) ])) [] := by
  sys_norm

/-- …so -EADDRINUSE, live on the unbound socket, is a lie on the bound one.
probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate listen#6:ret=-EADDRINUSE -- listen -/
theorem listen_bound_socket_eaddrinuse_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (listen_in 3 128) bound_socket_model
        (Ok (mkEffect (errno_ret EADDRINUSE) [] []) m' evs) := by
  sys_refute

/-- RE-LISTENING IS LEGAL: TCPF_LISTEN is in the accepted mask (:198), the
new backlog is written (:201) and `inet_csk_listen_start` is skipped
(:205-225), so a second listen is 0 and changes nothing.
kernel: net/ipv4/af_inet.c:__inet_listen_sk@v6.18.46 -/
theorem listen_relisten_is_zero (o : outcome SyscallEffect) :
    syscall_spec (listen_in 3 128) listening_socket_model o ↔
      o = Ok (mkEffect 0 [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/bind_listen_spec.c#reject --mutate listen#2:ret=-EADDRINUSE -- listen -/
theorem listen_relisten_eaddrinuse_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (listen_in 3 128) listening_socket_model
        (Ok (mkEffect (errno_ret EADDRINUSE) [] []) m' evs) := by
  sys_refute

/-- An ACCEPTED connection is `SS_CONNECTED`: `inet_listen`'s
`sock->state != SS_UNCONNECTED` (:239) is -EINVAL.
kernel: net/ipv4/af_inet.c:inet_listen@v6.18.46 -/
theorem listen_connected_socket_is_einval (o : outcome SyscallEffect) :
    syscall_spec (listen_in 4 128) accepted_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) accepted_socket_model [] := by
  sys_norm

/-- A RESET connection is -EINVAL too, from the same test and not from the
state mask: `tcp_done` left `sk_state` at TCP_CLOSE, which :198 would
ACCEPT, but never moved `sock->state` off SS_CONNECTED.
kernel: net/ipv4/af_inet.c:inet_listen; net/ipv4/tcp.c:tcp_done@v6.18.46 -/
theorem listen_reset_socket_is_einval (o : outcome SyscallEffect) :
    syscall_spec (listen_in 3 128) reset_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) reset_socket_model [] := by
  sys_norm

/-- …a model reading the state mask alone would let it succeed.
kernel: net/ipv4/af_inet.c:inet_listen@v6.18.46 -/
theorem listen_reset_socket_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (listen_in 3 128) reset_socket_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-! ## accept (202) and accept4 (242): the fd, the flags, the socket, the state

`__sys_accept4` (net/socket.c:2051, v6.18.46) resolves the fd first
(:2054-2057); `__sys_accept4_file` (:2012) refuses an unknown flag bit
(:2019-2020) and reserves the descriptor (:2025-2027); `do_accept` (:1952)
answers -ENOTSOCK (:1962-1964) and hands the socket's own `accept` the
queue, where `inet_csk_accept` (net/ipv4/inet_connection_sock.c:649, v6.18.46) is
-EINVAL off TCP_LISTEN (:662-663) and otherwise dequeues the head
connection (:679); `fd_install` (fs/file.c, called at net/socket.c:2035, v6.18.46) makes the number a
socket.  `accept` is `__sys_accept4(…, 0)` (:2071), so the pins on
`accept_in` are the same arm with a zero flags word.  The probes are
linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/accept_spec.c,
which refuses at every step and accepts nothing, and
linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/socket_read_peer.c,
which accepts. -/

/-- THE HAND-OVER: on the listening fixture `accept4(3, NULL, NULL, 0)` answers
one of four things — the descriptor-table errnos -EMFILE and -ENOMEM
(`alloc_fd`, fs/file.c:591-598, v6.18.46, through `get_unused_fd_flags`), the
socket-table -ENFILE (`sock_alloc` in `do_accept`, :1966-1968), each
leaving the model alone since steps 1 through 7 leave the queue untouched;
or the LOWEST free descriptor, 4, carrying the head connection's peer on
channel 3 with the queue advanced and the handed-over count at 1
(`accepted_socket_model`).  Rocq's `accept_hands_over_the_head_connection`,
`accept_errno_set_is_exactly_these_three`,
`accept_success_return_is_exactly_the_lowest_free_fd` and
`accept_errno_arms_leave_the_queue_alone`, as one `iff`.
probe: testing/syscall-check/tests/socket_read_peer.c#conform --peer 68656c6c6f -- bytes -/
theorem accept4_listening_iff (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 0) listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) accepted_socket_model []) := by
  sys_norm

/-- `accept(3, NULL, NULL)` is the same call: the table passes a zero flags
word, as `SYSCALL_DEFINE3(accept)` does.
kernel: fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:do_accept,__sys_accept4@v6.18.46 -/
theorem accept_listening_iff (o : outcome SyscallEffect) :
    syscall_spec (accept_in 3 0 0) listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) accepted_socket_model []) := by
  sys_norm

/-- `accept` NEVER READS a3: `SYSCALL_DEFINE3(accept)` (net/socket.c:2068-2072)
takes three arguments and hands `__sys_accept4` a literal 0 as the flags
(:2071), so SOCK_NONBLOCK|1 left in the fourth register is not the -EINVAL
`accept4` would answer it — the call is the plain one.  A table line reading
`in_arg i 3` on 202 would answer -EINVAL here; `accept_in` cannot state this,
since it zeroes a3 itself.
no-row: no recorded run loads a3 on accept(202); every corpus row of 202 has a3 = 0.
The corpus's 202 calls are `accept_spec`'s and `unmodeled_sockets`'s, so no row
of it is about this call.  A probe COULD load a3 --
linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/probe.h's `sc6`
takes six registers whatever the syscall's arity -- but the accepting row this
pin needs would owe
linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/socket_read_peer.c
a `--peer` recapture, to record what `SYSCALL_DEFINE3(accept)` settles by
passing a literal 0.
kernel: fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:accept,__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem accept_ignores_a3_flags_word (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 202 [3, 0, 0, 2049, 0, 0] (fun _ => none) (fun _ => none))
        listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) accepted_socket_model []) := by
  sys_norm

/-- The -EINVAL `accept4` answers a flags word with a bit outside
SOCK_NONBLOCK|SOCK_CLOEXEC -- `__sys_accept4_file`'s test (:2019-2020) -- is
refused on this call: the bad bit sits in a3, and a3 is dead on the
three-argument entry.
no-row: no recorded run loads a3 on accept(202); every corpus row of 202 has a3 = 0.
kernel: net/socket.c:accept,__sys_accept4,__sys_accept4_file@v6.18.46 -/
theorem accept_a3_bad_bit_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 202 [3, 0, 0, 2049, 0, 0] (fun _ => none) (fun _ => none))
        listening_socket_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and SOCK_NONBLOCK alone in a3 is not `accept4`'s decline either: the
register is dead on the three-argument entry.
kernel: net/socket.c:accept,__sys_accept4@v6.18.46 -/
theorem accept_a3_nonblock_not_declined :
    ¬ syscall_spec (SyscallInput.mkInput 202 [3, 0, 0, 2048, 0, 0] (fun _ => none) (fun _ => none))
        listening_socket_model Unmodeled := by
  sys_refute

/-- SOCK_CLOEXEC IS ACCEPTED AND IGNORED: it reaches `get_unused_fd_flags`
(:2025) as the descriptor's close-on-exec bit, which no arm reads, so the
answer is the plain call's.
kernel: fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:do_accept,__sys_accept4_file@v6.18.46 -/
theorem accept4_cloexec_iff (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 524288) listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) accepted_socket_model []) := by
  sys_norm

/-- WITH A NULL ADDRESS THE LENGTH POINTER IS NEVER TOUCHED: `do_accept`
guards both behind `if (upeer_sockaddr)` (:1993), so a non-NULL `addrlen`
beside a NULL `addr` is the plain call.
kernel: fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:do_accept,__sys_accept4@v6.18.46 -/
theorem accept4_null_addr_ignores_addrlen_iff (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 4104 0) listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) accepted_socket_model []) := by
  sys_norm

/-- -EAGAIN IS REFUSED: `inet_csk_accept` answers it only for a zero timeout
(:671), that is O_NONBLOCK or an expired SO_RCVTIMEO, neither of which the
model carries; its listener always has the environment's next connection
queued.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate accept4#1:ret=-EAGAIN --peer 68656c6c6f -- bytes -/
theorem accept4_eagain_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) listening_socket_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- -EINTR needs `signal_pending(current)` in `inet_csk_wait_for_connect`
(:635-636), and the model never reaches a syscall with an unblocked signal
pending: its one pending signal, a blocked SIGABRT
(`State.ProcState.procst_sigabrt_pending`), does not set TIF_SIGPENDING
(`wants_signal`, kernel/signal.c:946-949, and `recalc_sigpending_tsk`,
:159-175, Linux v6.18.46), the `rt_sigprocmask` that unblocks it kills the
process (`Kernel.Signal.sigmask_deliver_model`), and no signal from outside
the process is modeled.
kernel: net/ipv4/inet_connection_sock.c:inet_csk_wait_for_connect@v6.18.46 -/
theorem accept4_eintr_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) listening_socket_model
        (Ok (mkEffect (errno_ret EINTR) [] []) m' evs) := by
  sys_refute

/-- -EOPNOTSUPP is `sock_no_accept`, the accept of a socket type that cannot
accept; only AF_INET/SOCK_STREAM sockets enter this table.
kernel: net/core/sock.c:sock_no_accept@v6.18.46 -/
theorem accept4_eopnotsupp_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) listening_socket_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) m' evs) := by
  sys_refute

/-- THE DESCRIPTOR IS THE LOWEST FREE ONE: 5 with 4 free is refused.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate accept4#1:ret=5 --peer 61 --peer 62 -- two -/
theorem accept4_non_lowest_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) listening_socket_model
        (Ok (mkEffect 5 [] []) m' evs) := by
  sys_refute

/-- …and never one already open: 3 is the listener itself.
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem accept4_listener_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) listening_socket_model
        (Ok (mkEffect 3 [] []) m' evs) := by
  sys_refute

/-- …nor the descriptor the previous hand-over installed: with 4 open as the
accepted socket the lowest free number is 5, and the probe's second accept
forging 4 is refused.
probe: testing/syscall-check/tests/socket_read_peer.c#reject --mutate accept4#2:ret=4 --peer 61 --peer 62 -- two -/
theorem accept4_open_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) accepted_socket_model
        (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- A SUCCESS ADVANCES THE QUEUE: 4 with the model unchanged — the connection
still at the head, no socket at 4 — is refused, since `reqsk_queue_remove`
(:679) and `fd_install` both ran.
kernel: net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_success_leaves_queue_rejected (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) listening_socket_model
        (Ok (mkEffect 4 [] []) listening_socket_model evs) := by
  sys_refute

/-- A CLOSED FD IS -EBADF WHATEVER THE FLAGS: `__sys_accept4` resolves the
descriptor (:2054-2057) before `__sys_accept4_file` tests the flags word
(:2019-2020), so fd 9 with the unknown bit 0 set answers -EBADF and not the
-EINVAL the bit would earn on an open fd.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem accept4_closed_fd_flag_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 9 0 0 1) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) listening_socket_model [] := by
  sys_norm

/-- …so the flags-first -EINVAL is refused here: the lookup already decided
the answer.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file@v6.18.46 -/
theorem accept4_closed_fd_flag_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 9 0 0 1) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and the same with a garbage flags word on an fd that is -1 after the
32-bit cast: the lookup fails first, so the answer is -EBADF.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem accept4_bad_fd_garbage_flags_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (accept4_in (Z_to_bv 64 (2 ^ 64 - 1)) 0 0 3735928559) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) listening_socket_model [] := by
  sys_norm

/-- …and the -EINVAL those flag bits would earn on an open fd is refused.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file@v6.18.46 -/
theorem accept4_bad_fd_garbage_flags_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in (Z_to_bv 64 (2 ^ 64 - 1)) 0 0 3735928559) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- THE FD IS AN `int`: `SYSCALL_DEFINE4(accept4, int, fd, …)` (net/socket.c:2062)
reaches `__sys_accept4` through riscv64's `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-88) and `__SC_CAST`
(include/linux/syscalls.h:132), which drop the register's high half, so
`accept4(2^32 + 3, NULL, NULL, 0)` IS `accept4(3, …)` — the listener — and
answers what `accept4_listening_iff` does, not the -EBADF a table comparing
the whole register would find.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:accept4,__sys_accept4,do_accept@v6.18.46 -/
theorem accept4_fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (accept4_in (Z_to_bv 64 (2 ^ 32 + 3)) 0 0 0) listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) accepted_socket_model []) := by
  sys_norm

/-- Truncation ALIASES rather than REJECTS.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; net/socket.c:accept4,__sys_accept4@v6.18.46 -/
theorem accept4_fd_2_pow_32_plus_3_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in (Z_to_bv 64 (2 ^ 32 + 3)) 0 0 0) listening_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The same through `SYSCALL_DEFINE3(accept, int, fd, …)` (:2068).
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:accept,__sys_accept4,do_accept@v6.18.46 -/
theorem accept_fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (accept_in (Z_to_bv 64 (2 ^ 32 + 3)) 0 0) listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) accepted_socket_model []) := by
  sys_norm

/-- THE FLAGS WORD IS AN `int` TOO: `SYSCALL_DEFINE4(accept4, …, int, flags)`
(net/socket.c:2062-2063) narrows it through `__SC_CAST`
(include/linux/syscalls.h:132) before `__sys_accept4_file`'s
`flags & ~(SOCK_CLOEXEC | SOCK_NONBLOCK)` (:2019) runs, so a register holding
2^32 is the flags word 0 — the plain call — and not the -EINVAL a spec testing
the whole register would answer.  `accept4_spec`'s `abi_low32` is that cast.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem accept4_flags_truncate_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 (Z_to_bv 64 (2 ^ 32))) listening_socket_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) listening_socket_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) listening_socket_model [])
       ∨ o = Ok (mkEffect 4 [] []) accepted_socket_model []) := by
  sys_norm

/-- kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; net/socket.c:accept4,__sys_accept4_file@v6.18.46 -/
theorem accept4_flags_2_pow_32_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 (Z_to_bv 64 (2 ^ 32))) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and the low half is READ, not zeroed: 2^32 + 2048 is SOCK_NONBLOCK after
the cast, so this is `accept4_nonblock_declines` — bit 11 survives `abi_low32`
and the high bit that would be -EINVAL on the whole register is gone.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; net/socket.c:accept4,__sys_accept4_file,sock_alloc_file@v6.18.46 -/
theorem accept4_flags_high_half_dropped_nonblock_declines (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 (Z_to_bv 64 (2 ^ 32 + 2048))) listening_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; net/socket.c:accept4,__sys_accept4_file@v6.18.46 -/
theorem accept4_flags_high_half_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 (Z_to_bv 64 (2 ^ 32 + 2048))) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `accept(999, NULL, NULL)`: -EBADF through the three-argument spelling.
probe: testing/syscall-check/tests/accept_spec.c#conform -- err -/
theorem accept_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (accept_in 999 0 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/accept_spec.c#reject --mutate accept#1:ret=-EINVAL -- err -/
theorem accept_closed_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept_in 999 0 0) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A SOCKET THAT IS NOT LISTENING IS -EINVAL, and nothing else:
`inet_csk_accept` refuses a socket off TCP_LISTEN (:662-663), and the
descriptor this spec would hand back is allocated only on the listening
arm, so no allocation errno joins this answer.
kernel: net/socket.c:__sys_accept4_file,do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_fresh_socket_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 0) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) fresh_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/accept_spec.c#reject --mutate accept4#1:ret=0 -- err -/
theorem accept4_fresh_socket_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) fresh_socket_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …nor the descriptor the listening fixture would hand out.
kernel: net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_fresh_socket_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) fresh_socket_model (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- …and a BOUND socket reads the same: still not TCP_LISTEN.
kernel: net/socket.c:__sys_accept4_file,do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_bound_socket_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 0) bound_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) bound_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/accept_spec.c#reject --mutate accept4#2:ret=0 -- err -/
theorem accept4_bound_socket_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) bound_socket_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and a socket that is not listening is -EINVAL, not -ENOTSOCK: it IS a
socket, `sock_from_file` passes it.
probe: testing/syscall-check/tests/accept_spec.c#reject --mutate accept4#2:ret=-ENOTSOCK -- err -/
theorem accept4_bound_socket_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) bound_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …and a RESET connection is not listening either.
kernel: net/socket.c:__sys_accept4_file,do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_reset_socket_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 0) reset_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) reset_socket_model [] := by
  sys_norm

/-- …nor is the socket a previous accept just handed over.
kernel: net/socket.c:__sys_accept4_file,do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_accepted_socket_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 4 0 0 0) accepted_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) accepted_socket_model [] := by
  sys_norm

/-- kernel: net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_accepted_socket_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 4 0 0 0) accepted_socket_model (Ok (mkEffect 5 [] []) m' evs) := by
  sys_refute

/-- A NON-SOCKET FD IS -ENOTSOCK, and nothing else: `do_accept`'s
`sock_from_file` (:1962-1964) is the whole test, and the descriptor
allocation this spec performs sits on the listening arm alone.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept,sock_from_file@v6.18.46 -/
theorem accept4_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 0) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- kernel: net/socket.c:do_accept,sock_from_file@v6.18.46 -/
theorem accept4_regular_file_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …a write-only file at 4 reads the same.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept,sock_from_file@v6.18.46 -/
theorem accept4_write_only_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 4 0 0 0) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/accept_spec.c#reject --mutate accept4#3:ret=-EINVAL -- err -/
theorem accept4_write_only_file_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 4 0 0 0) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …a directory at 5…
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept,sock_from_file@v6.18.46 -/
theorem accept4_directory_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 5 0 0 0) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …a standard stream's channel at 1…
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept,sock_from_file@v6.18.46 -/
theorem accept4_channel_fd_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 1 0 0 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) listening_socket_model [] := by
  sys_norm

/-- …a pipe end, whose `f_op` is `pipeanon_fops`…
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept,sock_from_file@v6.18.46 -/
theorem accept4_pipe_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 6 0 0 0) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- …/dev/null…
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept,sock_from_file@v6.18.46 -/
theorem accept4_devnull_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 7 0 0 0) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- …and /dev/urandom.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept,sock_from_file@v6.18.46 -/
theorem accept4_urandom_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 8 0 0 0) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- AN UNKNOWN FLAG BIT IS -EINVAL on a listening socket too (:2019-2020),
ahead of the hand-over, so the connection stays queued.
kernel: net/socket.c:__sys_accept4_file@v6.18.46 -/
theorem accept4_bad_flag_on_listening_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 1) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_accept4_file@v6.18.46 -/
theorem accept4_bad_flag_on_listening_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 1) listening_socket_model (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- …and on a bound, unlistened one, where the state would answer -EINVAL as
well: the probe's bit 8, on the socket its `err` run has bound by call #4.
probe: testing/syscall-check/tests/accept_spec.c#conform -- err -/
theorem accept4_bad_flag_on_bound_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 256) bound_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) bound_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/accept_spec.c#reject --mutate accept4#4:ret=0 -- err -/
theorem accept4_bad_flag_on_bound_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 256) bound_socket_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- THE FLAGS ARE CHECKED BEFORE -ENOTSOCK: the write-only file at 4 with a
bad flag bit is -EINVAL, `__sys_accept4_file`'s test (:2019) running before
`do_accept`'s `sock_from_file` (:1962).
probe: testing/syscall-check/tests/accept_spec.c#conform -- err -/
theorem accept4_flags_beat_enotsock (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 4 0 0 256) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/accept_spec.c#reject --mutate accept4#5:ret=-ENOTSOCK -- err -/
theorem accept4_flags_beat_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 4 0 0 256) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- SOCK_CLOEXEC does not change the state's answer: it is accepted and
ignored, so the bound socket is -EINVAL just as with no flags at all.
kernel: net/socket.c:__sys_accept4_file,do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_cloexec_on_bound_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 524288) bound_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) bound_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/accept_spec.c#reject --mutate accept4#6:ret=0 -- err -/
theorem accept4_cloexec_on_bound_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 524288) bound_socket_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- SOCK_NONBLOCK IS DECLINED: it marks the NEW file O_NONBLOCK
(`sock_alloc_file` through `do_accept`, :1980 and :483-485), a notion the
model does not carry; on the listening fixture neither an errno nor the
descriptor is admitted.
kernel: net/socket.c:__sys_accept4_file,sock_alloc_file@v6.18.46 -/
theorem accept4_nonblock_declines (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 2048) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/socket.c:__sys_accept4_file,sock_alloc_file@v6.18.46 -/
theorem accept4_nonblock_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 2048) listening_socket_model
        (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- …the probe's shape, on a fresh socket: the decline precedes the state's
-EINVAL, since the flag is judged in `__sys_accept4_file` before `do_accept`
runs.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- acceptnonblock -/
theorem accept4_nonblock_on_fresh_declines (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 2048) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/socket.c:__sys_accept4_file@v6.18.46 -/
theorem accept4_nonblock_on_fresh_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 2048) fresh_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and before -ENOTSOCK, for the same reason.
kernel: net/socket.c:__sys_accept4_file@v6.18.46 -/
theorem accept4_nonblock_on_regular_file_declines (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 2048) socket_call_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -ENOTSOCK Linux gives here (`sock_from_file`, :1962-1964) is what the
decline withholds.
kernel: net/socket.c:__sys_accept4_file,do_accept,sock_from_file@v6.18.46 -/
theorem accept4_nonblock_on_regular_file_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 2048) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- Both known flags at once: the decline is SOCK_NONBLOCK's, whatever else
is set beside it.
kernel: net/socket.c:__sys_accept4_file,sock_alloc_file@v6.18.46 -/
theorem accept4_nonblock_and_cloexec_declines (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 526336) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/socket.c:__sys_accept4_file,sock_alloc_file@v6.18.46 -/
theorem accept4_nonblock_and_cloexec_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 526336) listening_socket_model
        (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- SOCK_NONBLOCK beside an unknown bit is -EINVAL, not a decline: the flag
test (:2019-2020) precedes any use of the flags.
kernel: net/socket.c:__sys_accept4_file@v6.18.46 -/
theorem accept4_nonblock_with_bad_bit_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 2049) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem accept4_nonblock_on_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 9 0 0 2048) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) listening_socket_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem accept4_nonblock_on_closed_fd_unmodeled_rejected :
    ¬ syscall_spec (accept4_in 9 0 0 2048) listening_socket_model Unmodeled := by
  sys_refute

/-- A NON-NULL ADDRESS IS DECLINED: `move_addr_to_user` (:1999-2000) writes
the peer's address; the hand-over with an address to fill is neither
refused nor admitted.
probe: testing/syscall-check/tests/socket_read_peer.c#fail-closed --expect-unmodeled accept4 --peer 68656c6c6f -- addr 4000 -/
theorem accept4_peer_address_declines (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 4096 4104 0) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/socket.c:do_accept,move_addr_to_user@v6.18.46 -/
theorem accept4_peer_address_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 4096 4104 0) listening_socket_model
        (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- `accept(3, addr, addrlen)` on the listener declines the same way.
kernel: net/socket.c:do_accept,move_addr_to_user@v6.18.46 -/
theorem accept_peer_address_declines (o : outcome SyscallEffect) :
    syscall_spec (accept_in 3 4096 4104) listening_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/socket.c:do_accept,move_addr_to_user@v6.18.46 -/
theorem accept_peer_address_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept_in 3 4096 4104) listening_socket_model
        (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- …and on a fresh socket, where Linux answers -EINVAL from the state
(`inet_csk_accept` :662-663, the address never written since `do_accept`
fails first): the model declines before it looks at the state, and the
probe's -EINVAL is what it declines to give.
probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- acceptaddr -/
theorem accept_peer_address_on_fresh_declines (o : outcome SyscallEffect) :
    syscall_spec (accept_in 3 4096 4104) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/socket.c:do_accept@v6.18.46 -/
theorem accept_peer_address_on_fresh_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept_in 3 4096 4104) fresh_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- probe: testing/syscall-check/tests/unmodeled_sockets.c#fail-closed -- accept4addr -/
theorem accept4_peer_address_on_fresh_declines (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 4096 4104 0) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- A NON-NULL ADDRESS DOES NOT SAVE A CLOSED FD: the address is looked at
only inside the socket arm, after the lookup has already answered, so fd 9
with an address to fill is -EBADF.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem accept4_peer_address_on_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 9 4096 4104 0) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) listening_socket_model [] := by
  sys_norm

/-- …so the address decline is refused on that input.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem accept4_peer_address_on_closed_fd_unmodeled_rejected :
    ¬ syscall_spec (accept4_in 9 4096 4104 0) listening_socket_model Unmodeled := by
  sys_refute

/-- …nor a NON-SOCKET fd: the address test sits inside the `FdSocket` arm,
which a regular file never enters, so `sock_from_file`'s -ENOTSOCK
(:1962-1964) is the whole answer.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept,sock_from_file@v6.18.46 -/
theorem accept4_peer_address_on_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 4096 4104 0) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …so the address decline is refused there too.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept,sock_from_file@v6.18.46 -/
theorem accept4_peer_address_on_regular_file_unmodeled_rejected :
    ¬ syscall_spec (accept4_in 3 4096 4104 0) socket_call_model Unmodeled := by
  sys_refute

/-- kernel: net/socket.c:__sys_accept4_file@v6.18.46 -/
theorem accept4_peer_address_bad_flag_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 4096 4104 1) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_accept4_file@v6.18.46 -/
theorem accept4_peer_address_bad_flag_unmodeled_rejected :
    ¬ syscall_spec (accept4_in 3 4096 4104 1) listening_socket_model Unmodeled := by
  sys_refute

/-- ON `socket_states_model`, one fd per state: the listener at 8 hands the
head connection over on fd 1 — stdout's number, closed in that fixture —
reported on channel 3, which is the `conn_channel` docstring's point about
descriptors versus channels, on the accepting side.
kernel: fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:do_accept@v6.18.46 -/
theorem accept4_states_listening_iff (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 8 0 0 0) socket_states_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) socket_states_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) socket_states_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) socket_states_model [])
       ∨ o = Ok (mkEffect 1 [] [])
              (with_accepted
                [ (1, .FdSocket (.SkConnected peer0 3 NFin)),
                  (0, .FdChannel 0), (3, .FdFile [102] 0),
                  (6, .FdSocket .SkFresh), (7, .FdSocket .SkBound), (8, .FdSocket .SkListening),
                  (9, .FdSocket (.SkConnected peer_1234 3 NFin)),
                  (10, .FdSocket (.SkReset peer_1234 3)) ]
                socket_states_model) []) := by
  sys_norm

/-- …and the same four states one fixture over: a FRESH socket is -EINVAL,
with no allocation errno beside it, since nothing is allocated off the
listening arm.
kernel: net/socket.c:__sys_accept4_file,do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_states_fresh_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 6 0 0 0) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- …a BOUND one…
kernel: net/socket.c:__sys_accept4_file,do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_states_bound_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 7 0 0 0) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- …a CONNECTED one…
kernel: net/socket.c:__sys_accept4_file,do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_states_connected_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 9 0 0 0) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- …and a RESET one.
kernel: net/socket.c:__sys_accept4_file,do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept4_states_reset_is_einval (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 10 0 0 0) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- …while the regular file at 3 is -ENOTSOCK, again alone.
kernel: net/socket.c:__sys_accept4_file,do_accept,sock_from_file@v6.18.46 -/
theorem accept4_states_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 0) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model [] := by
  sys_norm

/-! ## connect (203): the copy comes before the socket test

`__sys_connect` (net/socket.c:2109, v6.18.46): `fd_empty` is -EBADF (:2115-2116),
then `move_addr_to_kernel` (:2118-2120), and only `__sys_connect_file`
(:2086-2107) asks `sock_from_file` (:2092-2096).  So -ENOTSOCK sits BELOW
the copy and carries its ledger, while -EBADF and the length errnos carry
none, and an unreadable address on a non-socket is -EFAULT where `bind`'s
is -ENOTSOCK. -/

/-- A closed fd is -EBADF before the address is touched: no ledger.
kernel: net/socket.c:__sys_connect@v6.18.46 -/
theorem connect_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (connect_in 9 8192 16 (fun _ => none)) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) listening_socket_model [] := by
  sys_norm

/-- …and -EBADF cannot claim a copy, since it precedes it.
probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#1:smuggle-copyin:a1:16 -- bad -/
theorem connect_closed_fd_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 9 8192 16 connect_addr_mem) listening_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(8192, 16)]) m' evs) := by
  sys_refute

/-- A channel fd with an UNREADABLE address is -EFAULT: the copy fails
before the socket is examined.
probe: testing/syscall-check/tests/connect_spec.c#conform -- fault -/
theorem connect_channel_fd_unreadable_is_efault (o : outcome SyscallEffect) :
    syscall_spec (connect_in 1 8192 16 (fun _ => none)) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) listening_socket_model [] := by
  sys_norm

/-- …not -ENOTSOCK, which is `bind`'s answer to the same call.
probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#1:ret=-ENOTSOCK -- fault -/
theorem connect_channel_fd_unreadable_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 1 8192 16 (fun _ => none)) listening_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- A channel fd with a READABLE address is -ENOTSOCK carrying the 16-byte
ledger: the copy already happened when `sock_from_file` answered.
kernel: net/socket.c:__sys_connect,__sys_connect_file@v6.18.46 -/
theorem connect_channel_fd_is_enotsock_with_ledger (o : outcome SyscallEffect) :
    syscall_spec (connect_in 1 8192 16 connect_addr_mem) listening_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(8192, 16)])
             listening_socket_model [] := by
  sys_norm

/-- …-ENOTSOCK WITHOUT the ledger is refused, the one place connect's ledger
differs from bind's.
probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#3:drop-copyins -- bad -/
theorem connect_channel_fd_unledgered_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 1 8192 16 connect_addr_mem) listening_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#3:ret=-EBADF -- bad -/
theorem connect_channel_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 1 8192 16 connect_addr_mem) listening_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(8192, 16)]) m' evs) := by
  sys_refute

/-- A zero length on a channel fd copies nothing, so the copy cannot fault
and -ENOTSOCK is what is left — with an empty ledger.
kernel: net/socket.c:__sys_connect,move_addr_to_kernel,__sys_connect_file@v6.18.46 -/
theorem connect_channel_fd_zero_length_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (connect_in 1 8192 0 (fun _ => none)) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#7:ret=-EINVAL -- bad -/
theorem connect_channel_fd_zero_length_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 1 8192 0 (fun _ => none)) listening_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and even a zero-length ledger entry claims a read that never happened.
probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#7:smuggle-copyin:a1:0 -- bad -/
theorem connect_channel_fd_zero_length_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 1 8192 0 (fun _ => none)) listening_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(8192, 0)]) m' evs) := by
  sys_refute

/-! ## connect: the three length thresholds, in the kernel's order

`move_addr_to_kernel` refuses `> 128` and `< 0` (net/socket.c:250-251, v6.18.46) with
no copy; `__inet_stream_connect` refuses `< 2` (net/ipv4/af_inet.c:643-644)
after the copy; `tcp_v4_connect` refuses `< 16` (net/ipv4/tcp_ipv4.c:236-237)
after the state switch. -/

/-- 129 bytes: -EINVAL with no copy, the address being readable
notwithstanding.
probe: testing/syscall-check/tests/connect_spec.c#conform -- bad -/
theorem connect_addrlen_over_storage_is_einval (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 129 connect_addr_mem) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#5:smuggle-copyin:a1:16 -- bad -/
theorem connect_addrlen_over_storage_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 129 connect_addr_mem) listening_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 16)]) m' evs) := by
  sys_refute

/-- `addrlen` is an `int`: 2^32 - 1 is -1 and refused by `ulen < 0`.
probe: testing/syscall-check/tests/connect_spec.c#conform -- bad -/
theorem connect_negative_addrlen_is_einval (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 (Z_to_bv 64 (2 ^ 32 - 1)) connect_addr_mem)
        listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#4:ret=0 -- bad -/
theorem connect_negative_addrlen_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 (Z_to_bv 64 (2 ^ 32 - 1)) connect_addr_mem)
        listening_socket_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A zero length on a socket copies nothing, cannot fault, and lands on the
2-byte minimum: -EINVAL with an EMPTY ledger, whatever the address.
probe: testing/syscall-check/tests/connect_spec.c#conform -- bad -/
theorem connect_addrlen_zero_is_einval (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 0 (fun _ => none)) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#6:ret=-EFAULT -- bad -/
theorem connect_addrlen_zero_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 0 (fun _ => none)) listening_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- One READABLE byte is copied and refused by the 2-byte minimum: -EINVAL
with a one-byte ledger, and not -EISCONN, since the family test precedes
the state switch.
kernel: net/ipv4/af_inet.c:__inet_stream_connect; net/socket.c:move_addr_to_kernel@v6.18.46 -/
theorem connect_one_byte_is_einval_with_ledger (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 1 connect_addr_mem) listening_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 1)])
             listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#3:ret=-EISCONN -- state -/
theorem connect_one_byte_eisconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 1 connect_addr_mem) listening_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 1)]) m' evs) := by
  sys_refute

/-- …and one readable byte never faults (the probe's `connect#3` is four
bytes on a fresh socket, connect_spec.c:225; the one-byte call on a
listener has no recorded case, so this rests on the copy itself).
kernel: net/socket.c:move_addr_to_kernel; net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem connect_one_byte_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 1 connect_addr_mem) listening_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 1)]) m' evs) := by
  sys_refute

/-! ## connect: the state switch

`__inet_stream_connect` (net/ipv4/af_inet.c:654-671, v6.18.46): `SS_CONNECTED` is
-EISCONN; `SS_UNCONNECTED` pre-loads -EISCONN and keeps it unless
`sk->sk_state == TCP_CLOSE`.  `listen` moves only `sk_state`, so a
listener is caught by the second arm, an accepted socket by the first
(`__inet_accept`, :769), and a reset one by the first too (`tcp_done`
never moves `sock->state`). -/

/-- -EISCONN ON A LISTENING SOCKET, with the copy ledgered.
probe: testing/syscall-check/tests/connect_spec.c#conform -- state -/
theorem connect_listening_socket_is_eisconn (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 16 connect_addr_mem) listening_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 16)])
             listening_socket_model [] := by
  sys_norm

/-- The full 128 bytes are copied (`ulen == 128` is inside
`move_addr_to_kernel`'s range) and the listener answers -EISCONN with all
of them ledgered.
kernel: net/socket.c:move_addr_to_kernel; net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem connect_full_storage_length_is_eisconn (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 128 connect_addr_mem128) listening_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 128)])
             listening_socket_model [] := by
  sys_norm

/-- -EINVAL is the plausible guess and it is wrong.
probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#1:ret=-EINVAL -- state -/
theorem connect_listening_socket_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 16 connect_addr_mem) listening_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 16)]) m' evs) := by
  sys_refute

/-- -EISCONN is decided after the copy, so without its ledger it is refused.
probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#1:drop-copyins -- state -/
theorem connect_listening_socket_unledgered_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 16 connect_addr_mem) listening_socket_model
        (Ok (mkEffect (errno_ret EISCONN) [] []) m' evs) := by
  sys_refute

/-- An ACCEPTED socket is -EISCONN from the `SS_CONNECTED` arm.
kernel: net/ipv4/af_inet.c:__inet_stream_connect,__inet_accept@v6.18.46 -/
theorem connect_accepted_socket_is_eisconn (o : outcome SyscallEffect) :
    syscall_spec (connect_in 4 8192 16 connect_addr_mem) accepted_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 16)])
             accepted_socket_model [] := by
  sys_norm

/-- A RESET connection is -EISCONN too: `tcp_done` moved `sk_state` and left
`sock->state` at SS_CONNECTED.
kernel: net/ipv4/af_inet.c:__inet_stream_connect; net/ipv4/tcp.c:tcp_done@v6.18.46 -/
theorem connect_reset_socket_is_eisconn (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 16 connect_addr_mem) reset_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 16)])
             reset_socket_model [] := by
  sys_norm

/-- …so neither -EINVAL nor a fresh connection attempt is admitted there.
kernel: net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem connect_reset_socket_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 16 connect_addr_mem) reset_socket_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [] [] [(8192, 16)]) m' evs) := by
  sys_refute

/-- …whatever the peer has left to say: a pending reset is -EISCONN as well,
which is what fails the day someone mirrors `bind`'s script split into
connect, where `sock->state` and not `inet_num` is read.
kernel: net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem connect_pending_reset_is_eisconn (o : outcome SyscallEffect) :
    syscall_spec (connect_in 4 8192 16 connect_addr_mem) (connected_socket_model NRst) o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 16)])
             (connected_socket_model NRst) [] := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem connect_live_connection_is_eisconn (o : outcome SyscallEffect) :
    syscall_spec (connect_in 4 8192 16 connect_addr_mem)
        (connected_socket_model (NCons (Z_to_bv 8 65) NFin)) o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 16)])
             (connected_socket_model (NCons (Z_to_bv 8 65) NFin)) [] := by
  sys_norm

/-- Two bytes of AF_INET on a listener reach the switch and take -EISCONN:
the 16-byte minimum is `tcp_v4_connect`'s, below the switch.
kernel: net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem connect_two_bytes_on_listening_is_eisconn (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 2 connect_addr_mem) listening_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 2)])
             listening_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#2:ret=-EINVAL -- state -/
theorem connect_two_bytes_on_listening_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 2 connect_addr_mem) listening_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 2)]) m' evs) := by
  sys_refute

/-! ## connect: a fresh or bound socket reaches `tcp_v4_connect`

Both are TCP_CLOSE — `__inet_bind` never calls `tcp_set_state` — so the
`SS_UNCONNECTED` arm goes on to `tcp_v4_connect` (net/ipv4/tcp_ipv4.c, v6.18.46:
222-…): `addr_len < 16` is -EINVAL (:236-237), a foreign family
-EAFNOSUPPORT (:239-240), and past both the attempt itself is the
environment's and declined. -/

/-- Four bytes on a fresh socket: -EINVAL from the 16-byte minimum, with the
four bytes ledgered.
kernel: net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem connect_fresh_four_bytes_is_einval (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 4 connect_addr_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 4)])
             fresh_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#4:ret=-EISCONN -- state -/
theorem connect_fresh_four_bytes_eisconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 4 connect_addr_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 4)]) m' evs) := by
  sys_refute

/-- PRECEDENCE inside `tcp_v4_connect`: four bytes of an AF_UNIX address
are -EINVAL from the 16-byte minimum (:236-237), not the -EAFNOSUPPORT the
family test one line later (:239-240) would give a full-length one.
kernel: net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem connect_fresh_four_bytes_af_unix_is_einval (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 4 connect_unix_family_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 4)])
             fresh_socket_model [] := by
  sys_norm

/-- kernel: net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem connect_fresh_four_bytes_af_unix_eafnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 4 connect_unix_family_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(8192, 4)]) m' evs) := by
  sys_refute

/-- Fifteen bytes on a fresh socket: still under `tcp_v4_connect`'s 16-byte
minimum, -EINVAL with the fifteen bytes ledgered.
kernel: net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem connect_fresh_fifteen_bytes_is_einval (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 15 connect_addr_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 15)])
             fresh_socket_model [] := by
  sys_norm

/-- A full-length AF_UNIX address on a fresh AF_INET socket is
-EAFNOSUPPORT, NOT -EINVAL.
kernel: net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem connect_fresh_af_unix_is_eafnosupport (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 16 connect_unix_family_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(8192, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#5:ret=-EINVAL -- state -/
theorem connect_fresh_af_unix_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 16 connect_unix_family_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 16)]) m' evs) := by
  sys_refute

/-- THE ATTEMPT IS DECLINED, and declining is not refusing: a well-formed
AF_INET connect on a fresh socket is `Unmodeled`, so 0, -ECONNREFUSED and
-ETIMEDOUT all land on the same answer and none is admitted.
probe: testing/syscall-check/tests/connect_spec.c#fail-closed -- connectattempt -/
theorem connect_fresh_attempt_declines (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 16 connect_addr_mem) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- A BOUND socket groups with the fresh one, not the listener: four bytes
is -EINVAL and not -EISCONN.
kernel: net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem connect_bound_four_bytes_is_einval (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 4 connect_addr_mem) bound_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 4)])
             bound_socket_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#6:ret=-EISCONN -- state -/
theorem connect_bound_four_bytes_eisconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 4 connect_addr_mem) bound_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 4)]) m' evs) := by
  sys_refute

/-- kernel: net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem connect_bound_af_unix_is_eafnosupport (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 16 connect_unix_family_mem) bound_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(8192, 16)])
             bound_socket_model [] := by
  sys_norm

/-- …and the bound socket's attempt is declined like the fresh one's.
kernel: net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem connect_bound_attempt_declines (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 16 connect_addr_mem) bound_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- Two bytes of AF_INET on a FRESH socket pass the 2-byte minimum, pass
the switch, and are refused by the 16-byte one: -EINVAL, two bytes
ledgered.  With `connect_two_bytes_on_listening_is_eisconn` this is the two
orderings crossing.
kernel: net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem connect_two_bytes_on_fresh_is_einval (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 2 connect_addr_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 2)])
             fresh_socket_model [] := by
  sys_norm

/-! ## connect: AF_UNSPEC is a disconnect, read before the state switch

`__inet_stream_connect` :646-651: an AF_UNSPEC family runs
`sk->sk_prot->disconnect` and returns, ahead of the switch.  For TCP that
is `tcp_disconnect` (net/ipv4/tcp.c:3346, v6.18.46), which returns 0 (:3489)
and, on a fresh socket, changes nothing the model can see. -/

/-- On a FRESH socket the disconnect is 0 with the model untouched and the
two family bytes ledgered.
probe: testing/syscall-check/tests/connect_spec.c#conform -- unspec -/
theorem connect_fresh_af_unspec_is_zero (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 2 connect_unspec_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU 0 [] [] [] [] [(8192, 2)]) fresh_socket_model [] := by
  sys_norm

/-- …the one arm that answers a SUCCESS still read its `sa_family`.
probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#1:drop-copyins -- unspec -/
theorem connect_fresh_af_unspec_unledgered_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 2 connect_unspec_mem) fresh_socket_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and two bytes are enough to reach it: the 16-byte minimum is never
consulted for AF_UNSPEC.
probe: testing/syscall-check/tests/connect_spec.c#reject --mutate connect#2:ret=-EINVAL -- unspec -/
theorem connect_fresh_af_unspec_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 2 connect_unspec_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 2)]) m' evs) := by
  sys_refute

/-- On a LISTENING socket the disconnect takes `tcp_disconnect`'s listen
branch (net/ipv4/tcp.c:3359-3360, v6.18.46), `inet_csk_listen_stop`
(net/ipv4/inet_connection_sock.c:1479, v6.18.46), and destroys the accept queue,
which the model has no way to say: declined — and, since the family is read BEFORE the state
switch, the -EISCONN a listener otherwise takes is refused here.
probe: testing/syscall-check/tests/connect_spec.c#fail-closed -- unspecstate -/
theorem connect_listening_af_unspec_declines (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 2 connect_unspec_mem) listening_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- On an ACCEPTED socket the disconnect sends an RST (`tcp_need_reset`,
:3363-3365) and leaves a socket the model's vocabulary lacks: declined.
kernel: net/ipv4/tcp.c:tcp_disconnect,tcp_need_reset@v6.18.46 -/
theorem connect_accepted_af_unspec_declines (o : outcome SyscallEffect) :
    syscall_spec (connect_in 4 8192 2 connect_unspec_mem) accepted_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- On a BOUND socket whether the port survives is `inet_bhash2_reset_saddr`'s
(:3388) and the bind lock's business, not carried here: declined.
kernel: net/ipv4/tcp.c:tcp_disconnect@v6.18.46 -/
theorem connect_bound_af_unspec_declines (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 2 connect_unspec_mem) bound_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- On a RESET connection no RST is sent (TCP_CLOSE is outside
`tcp_need_reset`'s mask), but the queue and port bookkeeping it clears is
not carried either: declined, not 0.
kernel: net/ipv4/tcp.c:tcp_disconnect,tcp_need_reset@v6.18.46 -/
theorem connect_reset_af_unspec_declines (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 2 connect_unspec_mem) reset_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-! ## getsockname (204), getpeername (205), shutdown (210): the fd first

All three open with the lookup (net/socket.c:2144-2148, v6.18.46, :2181-2185,
:2481-2485), so on a descriptor that is NOT a socket the answer does not
depend on the address buffer or on `how`: -EBADF closed, -ENOTSOCK open.
`socket_calls.c`'s `fdfirst` run puts the same shapes on a real kernel. -/

/-- A closed fd is -EBADF on `getsockname`, with a `how`-like garbage word
in every other register.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem getsockname_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (getsockname_in 9) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockname#1:ret=-ENOTSOCK -/
theorem getsockname_closed_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockname_in 9) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- A regular file is -ENOTSOCK on `getsockname`…
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem getsockname_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockname_in 3) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …never -EBADF (it is open) and never a success.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockname#5:ret=-EBADF -/
theorem getsockname_regular_file_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockname_in 3) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockname#5:ret=0 -/
theorem getsockname_regular_file_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockname_in 3) socket_call_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A write-only file: -ENOTSOCK on `getsockname`, the kind the other pins
never put through `sock_fd`.
kernel: net/socket.c:__sys_getsockname,sock_from_file@v6.18.46 -/
theorem getsockname_write_only_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockname_in 4) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_getsockname@v6.18.46 -/
theorem getsockname_write_only_file_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockname_in 4) socket_call_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A directory fd: -ENOTSOCK on `getsockname`.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem getsockname_directory_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockname_in 5) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockname#8:ret=0 -/
theorem getsockname_directory_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockname_in 5) socket_call_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The channel at fd 0, on `getpeername`: -ENOTSOCK.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem getpeername_channel_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getpeername_in 0) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getpeername#5:ret=0 -/
theorem getpeername_regular_file_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getpeername_in 3) socket_call_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and `inet_getname`'s -ENOTCONN, the answer for an unconnected SOCKET,
never reaches a regular file.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getpeername#5:ret=-ENOTCONN -/
theorem getpeername_regular_file_enotconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getpeername_in 3) socket_call_model
        (Ok (mkEffect (errno_ret ENOTCONN) [] []) m' evs) := by
  sys_refute

/-- `shutdown(3, 99)` on a regular file is -ENOTSOCK: nothing in net/socket.c, v6.18.46
tests `how`, so the wild argument changes nothing.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem shutdown_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 3 99) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate shutdown#6:ret=-EINVAL -/
theorem shutdown_regular_file_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in 3 99) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `shutdown(9, 99)`: a closed fd is -EBADF however wild `how` is.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem shutdown_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 9 99) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate shutdown#2:ret=-EINVAL -/
theorem shutdown_closed_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in 9 99) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A channel fd on `shutdown`: -ENOTSOCK, never 0.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate shutdown#12:ret=0 -/
theorem shutdown_channel_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in 0 1) socket_call_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The fd is an `int`: bit 31 set makes 2^31 + 1 a descriptor that is not
open, -EBADF, not fd 1's -ENOTSOCK.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate shutdown#4:ret=-ENOTSOCK -/
theorem shutdown_high_bit_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in (Z_to_bv 64 (2 ^ 31 + 1)) 1) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …while the HIGH half of the register is discarded by `fd32`: 2^32 + 3
is fd 3, the open file, -ENOTSOCK and not -EBADF.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockname#7:ret=-EBADF -/
theorem getsockname_high_half_discarded_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockname_in (Z_to_bv 64 (2 ^ 32 + 3))) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The three kinds Rocq's table never held, on all three calls: a pipe end,
/dev/null and /dev/urandom are -ENOTSOCK, the `f_op` comparison failing for
`pipeanon_fops` (`create_pipe_files`, fs/pipe.c:946, v6.18.46), `null_fops`
(drivers/char/mem.c:644) and `urandom_fops` (drivers/char/random.c:1572).
kernel: net/socket.c:__sys_getsockname,sock_from_file; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem getsockname_pipe_end_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockname_in 6) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_getpeername,sock_from_file@v6.18.46 -/
theorem getpeername_devnull_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getpeername_in 7) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_shutdown,sock_from_file@v6.18.46 -/
theorem shutdown_urandom_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 8 1) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-! ## getsockname and getpeername on a socket

`inet_getname` (net/ipv4/af_inet.c:797, v6.18.46): with `peer = 1` it refuses on
`!inet_dport` or on `sk_state` in `TCPF_CLOSE | TCPF_SYN_SENT` (:808-813);
with `peer = 0` it has no error return and writes an address, which the
model cannot export. -/

/-- GETPEERNAME ON A FRESH SOCKET IS -ENOTCONN: `inet_dport == 0`, nothing
about the buffer consulted, no memory effect.
probe: testing/syscall-check/tests/socket_calls.c#conform -- sockets -/
theorem getpeername_fresh_is_enotconn (o : outcome SyscallEffect) :
    syscall_spec (getpeername_in 6) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model [] := by
  sys_norm

/-- …a fresh socket has no peer to report.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getpeername#1:ret=0 -- sockets -/
theorem getpeername_fresh_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getpeername_in 6) socket_states_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …it IS a socket: -ENOTSOCK is the other half's answer.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getpeername#1:ret=-ENOTSOCK -- sockets -/
theorem getpeername_fresh_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getpeername_in 6) socket_states_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …and -ENOTCONN writes no `sockaddr`: the 16 bytes `move_addr_to_user`
would have stored are refused beside it.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getpeername#1:smuggle-write:a1:16 -- sockets -/
theorem getpeername_fresh_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getpeername_in 6) socket_states_model
        (Ok (mkEffect (errno_ret ENOTCONN) [(4096, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [])
            m' evs) := by
  sys_refute

/-- A BOUND socket has a port and still no `inet_dport`: -ENOTCONN.
kernel: net/ipv4/af_inet.c:inet_getname@v6.18.46 -/
theorem getpeername_bound_is_enotconn (o : outcome SyscallEffect) :
    syscall_spec (getpeername_in 7) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model [] := by
  sys_norm

/-- A LISTENING socket has none either.
probe: testing/syscall-check/tests/socket_calls.c#conform -- sockets -/
theorem getpeername_listening_is_enotconn (o : outcome SyscallEffect) :
    syscall_spec (getpeername_in 8) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getpeername#2:ret=0 -- sockets -/
theorem getpeername_listening_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getpeername_in 8) socket_states_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- GETPEERNAME IS THE ARM `SkReset` EXISTS FOR: a peer RST ran `tcp_done`
(net/ipv4/tcp.c:5033, v6.18.46), so `sk_state` is TCP_CLOSE while `inet_dport`
survives — the STATE disjunct fires, -ENOTCONN.
kernel: net/ipv4/af_inet.c:inet_getname; net/ipv4/tcp.c:tcp_done@v6.18.46 -/
theorem getpeername_reset_is_enotconn (o : outcome SyscallEffect) :
    syscall_spec (getpeername_in 10) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model [] := by
  sys_norm

/-- …and the success Linux gives a CLOSE_WAIT connection — 0, with the
peer's `sockaddr_in` written through `move_addr_to_user` (net/socket.c:306,
v6.18.46) and the length written back (:297) — is refused on the RESET one:
the STATE disjunct fires first.  This is the lie a model that skipped the
state test would tell; `getpeername` never returns the length itself
(`__sys_getpeername` returns `move_addr_to_user`'s 0, :2196 and :309).
kernel: net/socket.c:__sys_getpeername,move_addr_to_user; net/ipv4/af_inet.c:inet_getname@v6.18.46 -/
theorem getpeername_reset_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getpeername_in 10) socket_states_model
        (Ok (mkEffect 0 [(4096, [2, 0, 1, 187, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0]),
                         (4104, [16, 0, 0, 0])] [])
            m' evs) := by
  sys_refute

/-- A consumed FIN leaves TCP_CLOSE_WAIT, in NEITHER disjunct: the connected
socket at fd 9 SUCCEEDS on Linux and is declined here, because the success
writes an address the model cannot export.  fd 9 and fd 10 differ only in
their constructor, and the model gives them different answers: that is the
claim.
kernel: net/ipv4/af_inet.c:inet_getname@v6.18.46 -/
theorem getpeername_connected_declines (o : outcome SyscallEffect) :
    syscall_spec (getpeername_in 9) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- GETSOCKNAME DECLINES ON EVERY SOCKET STATE, the fresh one included: its
answer really is 0.0.0.0:0, but the only answer available is a success that
writes it, and past the fresh state the port is an ephemeral one
`inet_csk_find_open_port` drew at random (net/ipv4/inet_connection_sock.c:
348).  Pinned on the fresh socket…
kernel: net/ipv4/af_inet.c:inet_getname; net/ipv4/inet_connection_sock.c:inet_csk_find_open_port@v6.18.46 -/
theorem getsockname_fresh_declines (o : outcome SyscallEffect) :
    syscall_spec (getsockname_in 6) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- …on the listening one, whose port is the drawn one…
kernel: net/ipv4/af_inet.c:inet_getname; net/ipv4/inet_connection_sock.c:inet_csk_find_open_port@v6.18.46 -/
theorem getsockname_listening_declines (o : outcome SyscallEffect) :
    syscall_spec (getsockname_in 8) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- …on the bound one, whose port is drawn too: `bind` to port 0 still
reaches `inet_csk_get_port` (net/ipv4/inet_connection_sock.c:500, v6.18.46)
from `__inet_bind` (net/ipv4/af_inet.c:538), and the port it lands is the
random one…
kernel: net/ipv4/af_inet.c:inet_getname,__inet_bind; net/ipv4/inet_connection_sock.c:inet_csk_find_open_port@v6.18.46 -/
theorem getsockname_bound_declines (o : outcome SyscallEffect) :
    syscall_spec (getsockname_in 7) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- …on the connected one, which inherited the listener's drawn port…
kernel: net/ipv4/af_inet.c:inet_getname@v6.18.46 -/
theorem getsockname_connected_declines (o : outcome SyscallEffect) :
    syscall_spec (getsockname_in 9) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and on the reset one, so that no later change quietly invents an
address for it.
kernel: net/ipv4/af_inet.c:inet_getname@v6.18.46 -/
theorem getsockname_reset_declines (o : outcome SyscallEffect) :
    syscall_spec (getsockname_in 10) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-! ## shutdown on a socket

`inet_shutdown` (net/ipv4/af_inet.c:888, v6.18.46): `how++` then the mask test
(:896-900) before `lock_sock`; `case TCP_LISTEN:` breaks out on SHUT_WR
(:927-929); `case TCP_CLOSE:` sets -ENOTCONN and FALLS THROUGH into the
store to `sk_shutdown` (:912-918). -/

/-- A bad `how` is -EINVAL on a fresh socket, decided before `lock_sock`
and before the state is read: the socket is bit for bit unchanged.
probe: testing/syscall-check/tests/socket_calls.c#conform -- sockets -/
theorem shutdown_bad_how_on_fresh_is_einval (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 6 3) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- …not the -ENOTCONN a fresh socket takes for a GOOD `how` (the probe's
`shutdown#1` refuses it for `how = 99`, socket_calls.c:270; this pin is
`how = 3`, the first value past the mask).
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shutdown_bad_how_on_fresh_enotconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in 6 3) socket_states_model
        (Ok (mkEffect (errno_ret ENOTCONN) [] []) m' evs) := by
  sys_refute

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate shutdown#3:ret=0 -- sockets -/
theorem shutdown_bad_how_on_fresh_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in 6 3) socket_states_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- `how = -1` passes the mask after `how++` and is caught by `!how`: the
kernel's `MAXINT->0` comment.  `int32` at the table keeps the low 32 bits.
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shutdown_minus_one_how_is_einval (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 9 (Z_to_bv 64 (2 ^ 64 - 1))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- A bad `how` on a LISTENING socket is -EINVAL too, ahead of the
`TCP_LISTEN` arm (the probe's `sockets` run issues no bad `how` on a
listener, so this is the kernel's claim alone).
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shutdown_bad_how_on_listening_is_einval (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 8 3) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shutdown_bad_how_on_listening_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in 8 3) socket_states_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and on a connected, a bound and a reset socket alike (99 is outside the
mask as 3 is).
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shutdown_bad_how_on_connected_is_einval (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 9 99) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shutdown_bad_how_on_bound_is_einval (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 7 (Z_to_bv 64 (2 ^ 31 - 1))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shutdown_bad_how_on_reset_is_einval (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 10 3) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- SHUT_WR ON A LISTENING SOCKET IS 0 AND CHANGES NOTHING: `case
TCP_LISTEN: if (!(how & RCV_SHUTDOWN)) break;` with the incremented `how`
at 2, so the `default:` arm never runs and the model comes back identical.
probe: testing/syscall-check/tests/socket_calls.c#conform -- sockets -/
theorem shut_wr_on_listening_is_zero (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 8 1) socket_states_model o ↔
      o = Ok (mkEffect 0 [] []) socket_states_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate shutdown#4:ret=-ENOTCONN -- sockets -/
theorem shut_wr_on_listening_enotconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in 8 1) socket_states_model
        (Ok (mkEffect (errno_ret ENOTCONN) [] []) m' evs) := by
  sys_refute

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate shutdown#4:ret=-EINVAL -- sockets -/
theorem shut_wr_on_listening_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in 8 1) socket_states_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and it unmaps nothing: a kernel reporting a change to the address
space beside the 0 is refused.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate shutdown#4:smuggle-unmap:4096:4096 -- sockets -/
theorem shut_wr_on_listening_unmap_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in 8 1) socket_states_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [(4096, 4096)] [] []) m' evs) := by
  sys_refute

/-- SHUT_RD on a listener falls through to `disconnect` (:928-932), which
purges the accept queue the model keeps in the environment: declined.
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shut_rd_on_listening_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 8 0) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- SHUT_RDWR on a listener has RCV_SHUTDOWN set too, so it takes the same
`disconnect` fall-through as SHUT_RD: declined.
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shut_rdwr_on_listening_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 8 2) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- THE MOST LOAD-BEARING DECLINE: SHUT_RD on a fresh socket.  The errno
would be -ENOTCONN and it would be right — but `case TCP_CLOSE:` falls
through and stores the bit (:912-918), and `tcp_recvmsg_locked` tests
`sk_shutdown & RCV_SHUTDOWN` (net/ipv4/tcp.c:2749, v6.18.46) BEFORE its TCP_CLOSE
-ENOTCONN (:2752-2756), so the next `read` is 0 where it would have been
-ENOTCONN.  A model with no shutdown bits declines rather than buy a right
errno with a wrong successor state.
kernel: net/ipv4/af_inet.c:inet_shutdown; net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem shut_rd_on_fresh_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 6 0) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- SHUT_WR on a fresh socket stores SEND_SHUTDOWN through the same
TCP_CLOSE fall-through, a bit the model does not carry: declined.
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shut_wr_on_fresh_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 6 1) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- A bound socket is still TCP_CLOSE (`bind` moves no state), so SHUT_RDWR
stores both bits behind -ENOTCONN: declined for the fresh socket's reason.
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shut_rdwr_on_bound_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 7 2) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- On a CONNECTED socket the `default:` arm stores the bits and
`tcp_shutdown` may send a FIN, moving the connection to a state the model
lacks: declined for every `how`.
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shut_wr_on_connected_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 9 1) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- SHUT_RD on a connected socket sets RCV_SHUTDOWN.  Bytes already queued
are still delivered — `tcp_recvmsg_locked` walks `sk_receive_queue` first
(net/ipv4/tcp.c:2702-2726, v6.18.46) — but a read that would otherwise WAIT
for the peer returns 0 (:2749, reached once the queue is empty), a
distinction between arrived and pending bytes the script cannot draw:
declined.
kernel: net/ipv4/af_inet.c:inet_shutdown; net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem shut_rd_on_connected_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 9 0) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- A RESET connection is TCP_CLOSE again, the same fall-through: declined.
kernel: net/ipv4/af_inet.c:inet_shutdown; net/ipv4/tcp.c:tcp_done@v6.18.46 -/
theorem shut_rdwr_on_reset_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 10 2) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- THE REST OF ROCQ'S GRID, so that no cell can later be answered -ENOTCONN
or 0 on its own: SHUT_RDWR on a fresh socket…
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shut_rdwr_on_fresh_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 6 2) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- …SHUT_RD and SHUT_WR on a bound one, still TCP_CLOSE…
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shut_rd_on_bound_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 7 0) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shut_wr_on_bound_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 7 1) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- …SHUT_RDWR on a connected one, the `default:` arm with both bits…
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shut_rdwr_on_connected_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 9 2) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and SHUT_RD and SHUT_WR on a reset one, TCP_CLOSE again.
kernel: net/ipv4/af_inet.c:inet_shutdown; net/ipv4/tcp.c:tcp_done@v6.18.46 -/
theorem shut_rd_on_reset_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 10 0) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:inet_shutdown; net/ipv4/tcp.c:tcp_done@v6.18.46 -/
theorem shut_wr_on_reset_declines (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 10 1) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-! ## setsockopt (208), getsockopt (209): the register lines, the calls and one memory

Ticket S-Net-Socket-options' section of this shared file.  The two option
arms and the shared ledger reader enter `sys_simp` here for the same
reason the lifecycle arms do above; `sock_level_known` and `int32_neg` are
gates, decided and not unfolded. -/

attribute [sys_simp low]
  setsockopt_spec.eq_1 getsockopt_spec.eq_1 getsockopt_optlen_read.eq_1

/-- `setsockopt(fd, level, optname, optval, optlen)`: nothing readable or
writable, since no arm of the call reads user memory. -/
def setsockopt_in (fd level optname optval optlen : word) : SyscallInput :=
  SyscallInput.mkInput 208 [fd, level, optname, optval, optlen, 0] (fun _ => none) (fun _ => none)

/-- `getsockopt(fd, level, optname, optval, optlenp)` over the readable
memory `mem`; `optlenp` is the one pointer the arms read. -/
def getsockopt_in (fd level optname optval optlenp : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 209 [fd, level, optname, optval, optlenp, 0] mem (fun _ => none)

/-- Four readable bytes at 4096 holding the `int` -1 (`0xFFFFFFFF`), the
`*optlen` value `socket_calls.c`'s `getlen-neg` run passes; nothing else is
mapped. -/
def optlen_minus_one_mem : word → Option byte := fun a =>
  if 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 4100 then some 255 else none

/-- `setsockopt(fd, level, optname, optval, optlen)` over the readable memory
`mem`, for the pins that state the set side reads nothing even when it
could. -/
def setsockopt_in_mem (fd level optname optval optlen : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 208 [fd, level, optname, optval, optlen, 0] mem (fun _ => none)

/-- Four readable bytes at `2^32 + 4096`, an `optlen` pointer with its high
half set — the shape of every real `&optlen` on the stack; nothing else is
mapped. -/
def optlen_high_mem : word → Option byte := fun a =>
  if 2 ^ 32 + 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 2 ^ 32 + 4100 then some 255 else none

attribute [sys_simp low] setsockopt_in.eq_1 getsockopt_in.eq_1 setsockopt_in_mem.eq_1

/-! ## setsockopt and getsockopt: the fd first

`__sys_setsockopt` (net/socket.c:2372-2387, v6.18.46) and `__sys_getsockopt`
(net/socket.c:2439-2453, v6.18.46) both open with `CLASS(fd, f)(fd)`, -EBADF
on `fd_empty` and -ENOTSOCK on a NULL `sock_from_file`, before `level`,
`optname`, `optval` or `optlen` is looked at.  So on a descriptor that is not
a socket the answer does not depend on any of the four — and on the get side
the pre-dispatch read of `*optlen` has not happened either, so the ledger is
empty whatever is mapped.  Level 999 and optname 999 below are Rocq's
garbage arguments: a level no dispatcher has an arm for, so on a SOCKET the
level would decide, and here it does not. -/

/-- A closed fd is -EBADF on `setsockopt`, whatever the level.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem setsockopt_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 9 999 999 4096 4) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- …not the level's errno: `ip_setsockopt` is never reached.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate setsockopt#4:ret=-ENOPROTOOPT -- levels -/
theorem setsockopt_closed_fd_enoprotoopt_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 9 999 999 4096 4) socket_call_model
        (Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) m' evs) := by
  sys_refute

/-- …and not -ENOTSOCK, which is an OPEN descriptor's answer.
kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem setsockopt_closed_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 9 999 999 4096 4) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- A closed fd is -EBADF on `getsockopt`, with an EMPTY ledger: the read
of `*optlen` sits in `do_sock_getsockopt`, which a closed fd never reaches.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem getsockopt_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 9 999 999 4096 4 (fun _ => none)) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#4:ret=-EOPNOTSUPP -- levels -/
theorem getsockopt_closed_fd_eopnotsupp_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 9 999 999 4096 4 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) m' evs) := by
  sys_refute

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#10:ret=-ENOTSOCK -/
theorem getsockopt_closed_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 9 999 999 4096 4 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- A regular file is -ENOTSOCK on `setsockopt`…
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem setsockopt_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 3 999 999 4096 4) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …never a success (the probe's round 5 puts this lie on the write-only
file, pinned below; the read-only round 9 is `conform` only)…
kernel: net/socket.c:__sys_setsockopt,sock_from_file@v6.18.46 -/
theorem setsockopt_regular_file_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 3 999 999 4096 4) socket_call_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and never the level's errno, since the level is not consulted (the
`fdfirst` run has an unknown level on a file only as `conform`, and on the
write-only file).
kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem setsockopt_regular_file_enoprotoopt_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 3 999 999 4096 4) socket_call_model
        (Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) m' evs) := by
  sys_refute

/-- A regular file is -ENOTSOCK on `getsockopt`, with an empty ledger.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem getsockopt_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 3 999 999 4096 4 (fun _ => none)) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- Never a success (round 5's lie is on the write-only file, pinned below).
kernel: net/socket.c:__sys_getsockopt,sock_from_file@v6.18.46 -/
theorem getsockopt_regular_file_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 999 999 4096 4 (fun _ => none)) socket_call_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …nor the get side's level errno (the probe's `levels` round 5 puts this
shape on a channel; the regular file is the kernel's claim alone).
kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_regular_file_eopnotsupp_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 999 999 4096 4 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) m' evs) := by
  sys_refute

/-- …nor -ENOPROTOOPT, the SET side's level errno — and `sk_getsockopt`'s
`default:` for a bad optname, the shape round 6 puts on the write-only file
below — which the lookup preempts.
kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_regular_file_enoprotoopt_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 999 999 4096 4 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) m' evs) := by
  sys_refute

/-- A write-only file: -ENOTSOCK on `setsockopt`.
kernel: net/socket.c:__sys_setsockopt,sock_from_file@v6.18.46 -/
theorem setsockopt_write_only_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 4 999 999 4096 4) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- A directory fd: -ENOTSOCK on `getsockopt`.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem getsockopt_directory_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 5 999 999 4096 4 (fun _ => none)) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- The channel at fd 0: -ENOTSOCK on `setsockopt`.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem setsockopt_channel_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 0 999 999 4096 4) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_channel_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 0 999 999 4096 4 (fun _ => none)) socket_call_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The channel is the fd the probe's `levels` round 5 puts an unknown level
on: -ENOTSOCK, never the level's errno, on either call.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate setsockopt#5:ret=-ENOPROTOOPT -- levels -/
theorem setsockopt_channel_enoprotoopt_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 0 999 999 4096 4) socket_call_model
        (Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) m' evs) := by
  sys_refute

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#5:ret=-EOPNOTSUPP -- levels -/
theorem getsockopt_channel_eopnotsupp_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 0 999 999 4096 4 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) m' evs) := by
  sys_refute

/-- The three kinds Rocq's fixture never held.  A pipe end's `f_op` is
`pipeanon_fops`, not `socket_file_ops`, so `sock_from_file` returns NULL:
-ENOTSOCK on `setsockopt`.
kernel: net/socket.c:__sys_setsockopt,sock_from_file@v6.18.46 -/
theorem setsockopt_pipe_end_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 999 999 4096 4) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- /dev/null (`null_fops`): -ENOTSOCK on `getsockopt`, no ledger.
kernel: net/socket.c:__sys_getsockopt,sock_from_file@v6.18.46 -/
theorem getsockopt_devnull_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 7 999 999 4096 4 (fun _ => none)) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- /dev/urandom (`urandom_fops`): -ENOTSOCK on `setsockopt`.
kernel: net/socket.c:__sys_setsockopt,sock_from_file@v6.18.46 -/
theorem setsockopt_urandom_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 8 999 999 4096 4) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-! ## The fd first: every cell of Rocq's `socket_calls_decline_every_non_socket_fd_kind`

Rocq walks fds 0, 3, 4 and 5 against both option calls with three
conjuncts each — -ENOTSOCK admitted, -EBADF refused, 0 refused.  The pins
above state some of those cells; these are the rest, and the same three
kinds Rocq's fixture never held on their other call.  Where the probe's
default run has the cell — rounds 5 and 6 are the WRITE-ONLY file (fd 4
here), round 8 the directory, rounds 12 and 13 the channel — the pin takes
the probe's own arguments, so its evidence line names a call the tracer
recorded; the read-only file (round 9) is `conform` only, which is why the
fd-3 refutations above cite the kernel. -/

/-- The directory: -ENOTSOCK on `setsockopt` (round 8).
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem setsockopt_directory_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 5 1 2 4096 4) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_setsockopt,sock_from_file@v6.18.46 -/
theorem setsockopt_directory_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 5 1 2 4096 4) socket_call_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- kernel: net/socket.c:__sys_getsockopt,sock_from_file@v6.18.46 -/
theorem getsockopt_directory_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 5 999 999 4096 4 (fun _ => none)) socket_call_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The write-only file: -ENOTSOCK on `getsockopt` with an EMPTY ledger even
though `optlen` is readable — round 5's `getsockopt(wfd, SOL_SOCKET,
SO_ERROR, optval, &optlen)`, a KNOWN level the fd verdict never lets reach
the table.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem getsockopt_write_only_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 4 1 4 4096 4104 sockaddr_in_any_mem) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#5:ret=0 -/
theorem getsockopt_write_only_file_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 4 1 4 4096 4104 sockaddr_in_any_mem) socket_call_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- Round 5's `setsockopt(wfd, SOL_SOCKET, SO_REUSEADDR, &one, 4)` never
succeeds either: the fd is resolved before the known level could.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate setsockopt#5:ret=0 -/
theorem setsockopt_write_only_file_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 4 1 2 4096 4) socket_call_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- Round 6's `getsockopt(wfd, SOL_SOCKET, 9999, …)`: not the -ENOPROTOOPT
`sk_getsockopt`'s `default:` arm gives that optname on a socket.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#6:ret=-ENOPROTOOPT -/
theorem getsockopt_write_only_file_enoprotoopt_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 4 1 9999 4096 4104 sockaddr_in_any_mem) socket_call_model
        (Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) m' evs) := by
  sys_refute

/-- Round 6's `setsockopt(wfd, SOL_SOCKET, SO_REUSEADDR, &one, -1)`: -ENOTSOCK…
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem setsockopt_negative_optlen_on_write_only_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 4 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …and not the -EINVAL the length earns once the fd is a socket.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate setsockopt#6:ret=-EINVAL -/
theorem setsockopt_negative_optlen_on_write_only_file_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 4 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `getsockopt(wfd, SOL_SOCKET, SO_ERROR, NULL, NULL)`, the `fdfirst` run's
sixth `getsockopt`: -ENOTSOCK, neither pointer read…
probe: testing/syscall-check/tests/socket_calls.c#conform -- fdfirst -/
theorem getsockopt_null_pointers_on_write_only_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 4 1 4 0 0 (fun _ => none)) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …and not the -EINVAL the probe offers there as the lie.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#6:ret=-EINVAL -- fdfirst -/
theorem getsockopt_null_pointers_on_write_only_file_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 4 1 4 0 0 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The channel at fd 0: -ENOTSOCK on `getsockopt`, no ledger (rounds 12 and
13 are the tracer's channels).
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem getsockopt_channel_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 0 1 4 4096 4104 sockaddr_in_any_mem) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_setsockopt,sock_from_file@v6.18.46 -/
theorem setsockopt_channel_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 0 999 999 4096 4) socket_call_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A LIVE descriptor is never -EBADF: `fd_empty` is false once the lookup
has found a file, and `sock_from_file`'s NULL is -ENOTSOCK — Rocq's second
conjunct on every cell.  The probe carries the lie only on `getsockname`
and `shutdown` (rounds 5 and 8), so these eight are the kernel's claim.
kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem setsockopt_channel_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 0 999 999 4096 4) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem setsockopt_regular_file_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 3 999 999 4096 4) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem setsockopt_write_only_file_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 4 1 2 4096 4) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem setsockopt_directory_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 5 1 2 4096 4) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_channel_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 0 1 4 4096 4104 sockaddr_in_any_mem) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_regular_file_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 999 999 4096 4 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_write_only_file_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 4 1 4 4096 4104 sockaddr_in_any_mem) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_directory_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 5 999 999 4096 4 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The three kinds Rocq's fixture never held, on their other call: a pipe
end on `getsockopt`…
kernel: net/socket.c:__sys_getsockopt,sock_from_file@v6.18.46 -/
theorem getsockopt_pipe_end_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 6 999 999 4096 4 (fun _ => none)) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- …/dev/null on `setsockopt`…
kernel: net/socket.c:__sys_setsockopt,sock_from_file@v6.18.46 -/
theorem setsockopt_devnull_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 7 999 999 4096 4) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- …and /dev/urandom on `getsockopt`.
kernel: net/socket.c:__sys_getsockopt,sock_from_file@v6.18.46 -/
theorem getsockopt_urandom_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 8 999 999 4096 4 (fun _ => none)) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-! ## setsockopt: the fd before the length; getsockopt: the fd before the pointers

`setsockopt`'s `optlen < 0` -EINVAL lives in `do_sock_setsockopt`
(net/socket.c:2335-2336, v6.18.46), which runs only once the fd has resolved
to a socket — v6.7 and later; up to v6.6 the check sat in `__sys_setsockopt`
ahead of the lookup, and the first pin below was -EINVAL.  `getsockopt`'s
pointers are read by `sk_getsockopt` (net/core/sock.c:1743-1746, v6.18.46) and
`do_ip_getsockopt`, both after the lookup, so the -EFAULT they would earn on
a socket is inadmissible on a descriptor that is not one. -/

/-- `setsockopt(9, SOL_SOCKET, 2, optval, -1)` on a closed fd is -EBADF.
probe: testing/syscall-check/tests/socket_calls.c#conform -/
theorem setsockopt_negative_optlen_on_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 9 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- …not the -EINVAL a v6.6 kernel gave, or a reader of the man page expects.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate setsockopt#2:ret=-EINVAL -/
theorem setsockopt_negative_optlen_on_closed_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 9 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The same call on a regular file is -ENOTSOCK (the probe's round 6 has
it on the write-only file, pinned in the fd-kind cells above)…
kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem setsockopt_negative_optlen_on_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 3 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …and the length is still not consulted.
kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem setsockopt_negative_optlen_on_regular_file_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 3 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `getsockopt(3, 0, 0, NULL, NULL)` on a regular file is -ENOTSOCK: neither
pointer is read (the `fdfirst` run's file is the write-only one, pinned in
the fd-kind cells above).
kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_null_pointers_on_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 3 0 0 0 0 (fun _ => none)) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_null_pointers_on_regular_file_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 0 0 0 0 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and the -EFAULT a NULL `optlen` earns inside `sk_getsockopt` is
inadmissible here.
kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_null_pointers_on_regular_file_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 0 0 0 0 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- The same NULL pointers on a closed fd: -EBADF.
probe: testing/syscall-check/tests/socket_calls.c#conform -- fdfirst -/
theorem getsockopt_null_pointers_on_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 9 0 0 0 0 (fun _ => none)) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#3:ret=-EFAULT -- fdfirst -/
theorem getsockopt_null_pointers_on_closed_fd_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 9 0 0 0 0 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A READABLE `optlen` on a closed fd is still not read: -EBADF with an
empty ledger, since `do_sock_getsockopt` never runs.
probe: testing/syscall-check/tests/socket_calls.c#conform -- levels -/
theorem getsockopt_closed_fd_readable_optlen_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 9 17 4 4096 4096 sockaddr_in_any_mem) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- …so a ledger beside the -EBADF is a read the kernel did not perform.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#4:smuggle-copyin:a4:4 -- levels -/
theorem getsockopt_closed_fd_readable_optlen_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 9 17 4 4096 4096 sockaddr_in_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(4096, 4)]) m' evs) := by
  sys_refute

/-- …and likewise on a live non-socket fd, whose -ENOTSOCK is decided by
`__sys_getsockopt` before that function runs.
kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_regular_file_readable_optlen_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 17 4 4096 4096 sockaddr_in_any_mem) socket_call_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)]) m' evs) := by
  sys_refute

/-! ## setsockopt and getsockopt on a socket: the level

`socket_states_model`, fd 6 fresh: the set side walks `ip_setsockopt`
(net/ipv4/ip_sockglue.c:1414-1415, v6.18.46), `if (level != SOL_IP) return
-ENOPROTOOPT;`, the get side `do_ip_getsockopt` (net/ipv4/ip_sockglue.c:
1515-1516, v6.18.46), `if (level != SOL_IP) return -EOPNOTSUPP;`.  Two
functions, one file, two errnos: each pin here refuses the other's, which is
the half that makes the pair non-vacuous.  `socket_calls.c`'s `levels` run
measures the same pair at SOL_UDP (17) against the pinned kernel; Rocq's
cases use 999, and both are kept.  The memory is unmapped in this section,
so the get side's ledger is empty; the ledger itself is the section after
the next. -/

/-- An unknown level on `setsockopt` is -ENOPROTOOPT.
probe: testing/syscall-check/tests/socket_calls.c#conform -- levels -/
theorem setsockopt_unknown_level_is_enoprotoopt (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 999 2 4096 4) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- …not the get side's -EOPNOTSUPP…
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate setsockopt#1:ret=-EOPNOTSUPP -- levels -/
theorem setsockopt_unknown_level_eopnotsupp_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 6 999 2 4096 4) socket_states_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) m' evs) := by
  sys_refute

/-- …never a success…
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate setsockopt#1:ret=0 -- levels -/
theorem setsockopt_unknown_level_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 6 999 2 4096 4) socket_states_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …not -EINVAL, the length being 4…
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_unknown_level_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 6 999 2 4096 4) socket_states_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and with NO ledger: the set side reads nothing, `ip_setsockopt`
returns before `optval` is touched.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate setsockopt#1:smuggle-copyin:a3:4 -- levels -/
theorem setsockopt_unknown_level_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 6 999 2 4096 4) socket_states_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOPROTOOPT) [] [] [] [] [(4096, 4)]) m' evs) := by
  sys_refute

/-- SOL_UDP, the level the probe measures, is the same -ENOPROTOOPT.
probe: testing/syscall-check/tests/socket_calls.c#conform -- levels -/
theorem setsockopt_sol_udp_is_enoprotoopt (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 17 1 4096 4) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- The set side reads NOTHING even when it could: with `optval` readable,
the -ENOPROTOOPT still carries an empty ledger — `ip_setsockopt` returns
before `do_ip_setsockopt`'s first copy — so a ledger gated on readability
is refused as much as an unconditional one.
kernel: net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_unknown_level_readable_optval_is_unledgered (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in_mem 6 999 2 4096 4 sockaddr_in_any_mem) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#reject --mutate setsockopt#1:smuggle-copyin:a3:4 -- levels -/
theorem setsockopt_unknown_level_readable_optval_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in_mem 6 999 2 4096 4 sockaddr_in_any_mem) socket_states_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOPROTOOPT) [] [] [] [] [(4096, 4)]) m' evs) := by
  sys_refute

/-- …and the -EINVAL arm returns before the LSM hook and before any copy:
empty ledger over readable memory there too.
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_negative_optlen_readable_optval_is_unledgered (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in_mem 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)) sockaddr_in_any_mem)
        socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- THE HEADLINE SHAPE, on a socket: `getsockopt(sockfd, 999, …, NULL, NULL)`
is -EOPNOTSUPP and not -EFAULT.  The length that could fault the CALL is
read by `sk_getsockopt` and `do_ip_getsockopt`, both past the level; the
pre-dispatch read at NULL faults the COPY, whose result is discarded, and
records nothing.
kernel: net/ipv4/ip_sockglue.c:do_ip_getsockopt; net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_null_pointers_on_socket_is_eopnotsupp (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 6 999 2 0 0 (fun _ => none)) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_null_pointers_on_socket_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 6 999 2 0 0 (fun _ => none)) socket_states_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- The ledger does not depend on the socket state: on the CONNECTED socket
a readable `optlen` is recorded exactly as on a fresh one.
`do_sock_getsockopt` reads `optlen` before `sock->ops` is even loaded
(:2409-2412).
kernel: net/socket.c:do_sock_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_connected_readable_optlen_is_ledgered (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 9 999 2 4104 4096 optlen_minus_one_mem) socket_states_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
             socket_states_model [] := by
  sys_norm

/-- An unknown level on `getsockopt` is -EOPNOTSUPP, here with nothing mapped
at `optlen`, so the ledger is empty.
kernel: net/ipv4/ip_sockglue.c:do_ip_getsockopt; net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_unknown_level_is_eopnotsupp (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 6 999 2 4096 4104 (fun _ => none)) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model [] := by
  sys_norm

/-- …not the set side's -ENOPROTOOPT…
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#1:ret=-ENOPROTOOPT -- levels -/
theorem getsockopt_unknown_level_enoprotoopt_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 6 999 2 4096 4104 (fun _ => none)) socket_states_model
        (Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) m' evs) := by
  sys_refute

/-- …never a success…
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#1:ret=0 -- levels -/
theorem getsockopt_unknown_level_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 6 999 2 4096 4104 (fun _ => none)) socket_states_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …not -EFAULT for the unmapped `optlen`: the level wins, the read's
result is discarded.
kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_unknown_level_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 6 999 2 4096 4104 (fun _ => none)) socket_states_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …and it writes no `optval`…
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#1:smuggle-write:a3:4 -- levels -/
theorem getsockopt_unknown_level_optval_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 6 999 2 4096 4104 (fun _ => none)) socket_states_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [(4096, [0, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- …nor the in/out `optlen` a socket really rewrites on a known level.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#1:smuggle-write:a4:4 -- levels -/
theorem getsockopt_unknown_level_optlen_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 6 999 2 4096 4104 (fun _ => none)) socket_states_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [(4104, [0, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- The level test reads no socket state: bound, listening, connected and
reset sockets answer the set side's -ENOPROTOOPT alike.
kernel: net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_unknown_level_on_bound_is_enoprotoopt (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 7 999 2 4096 4) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_unknown_level_on_listening_is_enoprotoopt (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 8 999 2 4096 4) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_unknown_level_on_connected_is_enoprotoopt (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 9 999 2 4096 4) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_unknown_level_on_reset_is_enoprotoopt (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 10 999 2 4096 4) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- …and the get side's -EOPNOTSUPP alike.
kernel: net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_unknown_level_on_bound_is_eopnotsupp (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 7 999 2 4096 4104 (fun _ => none)) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_unknown_level_on_listening_is_eopnotsupp (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 8 999 2 4096 4104 (fun _ => none)) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_unknown_level_on_connected_is_eopnotsupp (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 9 999 2 4096 4104 (fun _ => none)) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_unknown_level_on_reset_is_eopnotsupp (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 10 999 2 4096 4104 (fun _ => none)) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model [] := by
  sys_norm

/-! ## setsockopt: a negative `optlen` beats the level; getsockopt has no such test

`do_sock_setsockopt` (net/socket.c:2335-2336, v6.18.46) tests `optlen < 0`
first — before the LSM hook, before the BPF hook, before any dispatch — so
the call that is -ENOPROTOOPT at length 4 is -EINVAL at length -1, on a
known level as on an unknown one.  `optlen` is an `int`: the pins walk the
sign bit of the LOW 32 bits, which `int32` at the table and `sint32` in the
gate both read.  `getsockopt`'s length is a USER VALUE read downstream of the
level, so there the unknown level still wins. -/

/-- `optlen = -1` at an unknown level is -EINVAL…
probe: testing/syscall-check/tests/socket_calls.c#conform -- optlen-neg -/
theorem setsockopt_negative_optlen_is_einval (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- …and -ENOPROTOOPT there is inadmissible: the level was never reached.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate setsockopt:ret=-ENOPROTOOPT -- optlen-neg -/
theorem setsockopt_negative_optlen_enoprotoopt_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_states_model
        (Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) m' evs) := by
  sys_refute

/-- kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_negative_optlen_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_states_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A negative `optlen` at a KNOWN level is -EINVAL too, not the option
table's decline: the length test precedes the dispatch.
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_negative_optlen_on_known_level_is_einval (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- INT_MIN, `0x80000000`, is the smallest negative `int`: -EINVAL.
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_int_min_optlen_is_einval (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 31))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- INT_MAX, `0x7fffffff`, is not negative: the level decides, -ENOPROTOOPT.
kernel: net/socket.c:do_sock_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_int_max_optlen_is_enoprotoopt (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 31 - 1))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_int_max_optlen_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 31 - 1))) socket_states_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `optlen = 0` is not negative either — the test is `<`, not `≤` — so the
unknown level answers.
kernel: net/socket.c:do_sock_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_zero_optlen_is_enoprotoopt (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 999 2 4096 0) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_zero_optlen_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 6 999 2 4096 0) socket_states_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The sign test reads no socket state: -EINVAL on a bound, a listening, a
connected and a reset socket alike.
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_negative_optlen_on_bound_is_einval (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 7 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_negative_optlen_on_listening_is_einval (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 8 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_negative_optlen_on_connected_is_einval (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 9 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_negative_optlen_on_reset_is_einval (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 10 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-- `getsockopt` with `*optlen = -1` at an unknown level: the level wins,
-EOPNOTSUPP, and the four bytes holding the -1 are in the ledger — the
`len < 0` -EINVAL of `sk_getsockopt` sits downstream of the level.
probe: testing/syscall-check/tests/socket_calls.c#conform -- getlen-neg -/
theorem getsockopt_negative_optlen_value_is_eopnotsupp (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem) socket_states_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
             socket_states_model [] := by
  sys_norm

/-- …not the -EINVAL a kernel that tested `*optlen` before the level would give.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt:ret=-EINVAL -- getlen-neg -/
theorem getsockopt_negative_optlen_value_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem) socket_states_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 4)]) m' evs) := by
  sys_refute

/-! ## getsockopt: the `optlen` read happens before the level and after the fd

`fresh_socket_model` over `sockaddr_in_any_mem`, reused purely as a MEMORY
MAP: `[4096, 4112)` is readable and nothing else is, so 4096 is a readable
four-byte `optlen`, 8192 an unreadable one, 4108 the last readable one and
4109 one that STRADDLES the boundary with three readable bytes.
`do_sock_getsockopt` (net/socket.c:2405-2410, v6.18.46) runs the LSM hook and
then `copy_from_sockptr(&max_optlen, optlen, sizeof(int))` with no level test
in between, so every -EOPNOTSUPP past the fd has moved four bytes — and its
result is discarded, which is exactly why no probe can see the unreadable
rows: the errno is the same whatever is at `optlen`.  Stated in both
directions: accepting-with-a-ledger alone is satisfied by a spec that ledgers
unconditionally, refusing-a-ledger alone by one that never ledgers.  Rows on
8192 and 4109 pin the DECISION that an unreadable range records nothing; the
straddle is the named residue — Linux touches the page under 4109 before
faulting on 4112, the model records nothing, an under-record of one page in
the accept-more direction — and if it is ever closed, those two pins are
what has to change. -/

/-- Past the fd, on an unknown level: the four bytes are required.
probe: testing/syscall-check/tests/socket_calls.c#conform -- levels -/
theorem getsockopt_readable_optlen_is_eopnotsupp_with_ledger (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 3 17 4 4096 4096 sockaddr_in_any_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
             fresh_socket_model [] := by
  sys_norm

/-- …an empty ledger is a lie: `do_sock_getsockopt` copied them.
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#1:drop-copyins -- levels -/
theorem getsockopt_readable_optlen_unledgered_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 17 4 4096 4096 sockaddr_in_any_mem) fresh_socket_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) m' evs) := by
  sys_refute

/-- …at `optlen` itself, not one byte past it…
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#1:shift-copyins:1 -- levels -/
theorem getsockopt_readable_optlen_shifted_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 17 4 4096 4096 sockaddr_in_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4097, 4)]) m' evs) := by
  sys_refute

/-- …`sizeof(int)`, not five bytes…
probe: testing/syscall-check/tests/socket_calls.c#reject --mutate getsockopt#1:grow-copyins:1 -- levels -/
theorem getsockopt_readable_optlen_grown_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 17 4 4096 4096 sockaddr_in_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 5)]) m' evs) := by
  sys_refute

/-- …and not three.
kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_readable_optlen_short_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 17 4 4096 4096 sockaddr_in_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 3)]) m' evs) := by
  sys_refute

/-- The last readable `optlen`, 4108: bytes 4108-4111 are mapped, so the
ledger names them.  The bound is on the whole four-byte range.
kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_last_readable_optlen_is_ledgered (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 3 17 4 4096 4108 sockaddr_in_any_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4108, 4)])
             fresh_socket_model [] := by
  sys_norm

/-- An UNREADABLE `optlen` is the copy failing, which transfers nothing —
and the errno is unchanged, because the copy's result is discarded.
kernel: net/socket.c:do_sock_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_unreadable_optlen_is_eopnotsupp_unledgered (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 3 17 4 4096 8192 sockaddr_in_any_mem) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) fresh_socket_model [] := by
  sys_norm

/-- …so a ledger there names bytes `copy_from_user` never moved.
kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_unreadable_optlen_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 17 4 4096 8192 sockaddr_in_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(8192, 4)]) m' evs) := by
  sys_refute

/-- …and -EFAULT is not what an unreadable `optlen` earns: the level
answers.
kernel: net/socket.c:do_sock_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_unreadable_optlen_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 17 4 4096 8192 sockaddr_in_any_mem) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A range straddling the mapped boundary is unreadable AS A WHOLE: the
model records nothing.  THE NAMED RESIDUE — see the section header.
kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_straddling_optlen_is_eopnotsupp_unledgered (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 3 17 4 4096 4109 sockaddr_in_any_mem) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) fresh_socket_model [] := by
  sys_norm

/-- kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_straddling_optlen_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 17 4 4096 4109 sockaddr_in_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4109, 4)]) m' evs) := by
  sys_refute

/-- …nor the three readable bytes: a longest-readable-prefix ledger is not
what this spec records (the residue, again).
kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_straddling_optlen_partial_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 3 17 4 4096 4109 sockaddr_in_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4109, 3)]) m' evs) := by
  sys_refute

/-- A KNOWN level with a readable `optlen` is the option table, declined
whatever the ledger — so no pin above is the level test in disguise.  The
intersection is empty: `do_tcp_getsockopt` on SOL_TCP writes back a
truncated `*optlen`, a memory write with no export here.  (The probe's
`level-tcp` run makes one option call, a `setsockopt`, so the get side here
is the kernel's claim.)
kernel: net/ipv4/tcp.c:do_tcp_getsockopt@v6.18.46 -/
theorem getsockopt_known_level_readable_optlen_declines (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 3 6 4 4096 4096 sockaddr_in_any_mem) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-! ## setsockopt and getsockopt: a known level is declined

Why the option table — SOL_SOCKET (1), SOL_IP (0) and SOL_TCP (6), on
either call — is declined as an empty intersection rather than as hard:
on the set side an unknown optname is -ENOPROTOOPT at every layer and
not -EINVAL (`sk_setsockopt`, net/core/sock.c:1668-1669, v6.18.46), while
SO_BSDCOMPAT (net/core/sock.c:1417-1418) and TCP_THIN_DUPACK
(`do_tcp_setsockopt`, net/ipv4/tcp.c:3963-3966, v6.18.46) accept, store
nothing and return 0, and every option that does store changes later
behaviour; on the get side `*optlen` is rewritten.  A spec answering any of
it would be right only by luck.  `socket_calls.c`'s `level-tcp`,
`level-socket` and `level-ip` runs are the same three declines against the
pinned kernel, and they are the boundary that keeps the two unknown-level
errnos from being an answer to everything. -/

/-- The probe's `level-socket` run makes one option call, a `getsockopt`,
so this half is the kernel's claim: `sk_setsockopt` is the table.
kernel: net/core/sock.c:sk_setsockopt@v6.18.46 -/
theorem setsockopt_sol_socket_declines (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 1 2 4096 4) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#fail-closed -- level-ip -/
theorem setsockopt_sol_ip_declines (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 0 2 4096 4) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#fail-closed -- level-tcp -/
theorem setsockopt_sol_tcp_declines (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 6 2 4096 4) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- SO_BSDCOMPAT (14) at SOL_SOCKET, the accept-and-discard option: the same
decline, because `setsockopt_spec` takes no optname — the level alone puts
the call in the table, so the option that returns 0 storing nothing is not
answered 0 here, and a reader looking for it finds the level's answer.
kernel: net/core/sock.c:sk_setsockopt@v6.18.46 -/
theorem setsockopt_so_bsdcompat_declines (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 1 14 4096 4) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- probe: testing/syscall-check/tests/socket_calls.c#fail-closed -- level-socket -/
theorem getsockopt_sol_socket_declines (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 6 1 2 4096 4104 (fun _ => none)) socket_states_model o ↔
      o = Unmodeled := by
  sys_norm

/-- The `level-ip` run's one option call is a `setsockopt`; on the get side
`do_ip_getsockopt` past its level test is the table.
kernel: net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_sol_ip_declines (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 6 0 2 4096 4104 (fun _ => none)) socket_states_model o ↔
      o = Unmodeled := by
  sys_norm

/-- Likewise `level-tcp`; `do_tcp_getsockopt` is the table.
kernel: net/ipv4/tcp.c:do_tcp_getsockopt@v6.18.46 -/
theorem getsockopt_sol_tcp_declines (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 6 6 2 4096 4104 (fun _ => none)) socket_states_model o ↔
      o = Unmodeled := by
  sys_norm

/-- The decline holds on every socket state: a listener at SOL_TCP…
kernel: net/ipv4/tcp.c:do_tcp_setsockopt@v6.18.46 -/
theorem setsockopt_sol_tcp_on_listening_declines (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 8 6 2 4096 4) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and a connected socket at SOL_SOCKET on the get side.
kernel: net/core/sock.c:sk_getsockopt@v6.18.46 -/
theorem getsockopt_sol_socket_on_connected_declines (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 9 1 2 4096 4104 (fun _ => none)) socket_states_model o ↔
      o = Unmodeled := by
  sys_norm

/-! ## setsockopt and getsockopt: the narrowings the table and the arms perform

`SYSCALL_DEFINE5(setsockopt, int, fd, int, level, int, optname, …, int,
optlen)` (net/socket.c:2389-2390, v6.18.46) and `SYSCALL_DEFINE5(getsockopt,
int, fd, int, level, int, optname, …)` (net/socket.c:2455-2456, v6.18.46):
the kernel sees the LOW 32 BITS of `fd`, `level` and `optlen`, so the table
applies `fd32` to the descriptor and `int32` to the level on both arms and
to `optlen` on the set side (`Sys/Registry/Net/Socket.lean`), and
`int32_neg` reads the sign of what `int32` kept.  Every input above keeps
its high half clear; these are the inputs that separate a twin that
narrows from one that does not. -/

/-- `2^32 + 6` names fd 6, the fresh socket: the unknown level answers.
kernel: net/socket.c:__sys_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_fd_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- …not the -EBADF a 64-bit descriptor lookup would give.
kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem setsockopt_fd_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4) socket_states_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: net/socket.c:__sys_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_fd_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4104 (fun _ => none))
        socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_fd_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4104 (fun _ => none))
        socket_states_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `2^32 | SOL_TCP` as the level truncates onto a KNOWN level: declined,
not the unknown level's -ENOPROTOOPT.
probe: testing/syscall-check/tests/socket_calls.c#fail-closed -- level-hi -/
theorem setsockopt_level_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 6)) 2 4096 4) socket_states_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …and on the get side, where the `level-hi` run (declined at its
`setsockopt`) records nothing: `int level` in `__sys_getsockopt`.
kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_level_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 6)) 2 4096 4104 (fun _ => none))
        socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- `2^32 | 17` on the get side is SOL_UDP, unknown: -EOPNOTSUPP, the
probe's third `levels` shape.
kernel: net/socket.c:__sys_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_level_high_half_unknown_is_eopnotsupp (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 17)) 2 4096 4104 (fun _ => none))
        socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model [] := by
  sys_norm

/-- THE ONE ARGUMENT THAT IS NOT NARROWED: `getsockopt`'s `optlen` is a
pointer, `int __user *optlen` in `__sys_getsockopt` (net/socket.c:2439-2440,
v6.18.46), handed on whole as a `USER_SOCKPTR` (:2452) and read at the full
address (:2410).  Every real `&optlen` sits high on the stack, so a twin
that applied `int32` to it would ledger a truncated address on every real
run while passing every pin below 2^32; this one separates them.
kernel: net/socket.c:__sys_getsockopt,do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_optlen_pointer_is_not_narrowed (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4096)) optlen_high_mem)
        socket_states_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] []
                [(Z_to_bv 64 (2 ^ 32 + 4096), 4)]) socket_states_model [] := by
  sys_norm

/-- …so an empty ledger there is a truncated read, refused.
kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_optlen_pointer_truncated_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4096)) optlen_high_mem)
        socket_states_model (Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) m' evs) := by
  sys_refute

/-- …and the ledger at the LOW half is the lie a narrowing twin would tell.
kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_optlen_pointer_low_half_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4096)) optlen_high_mem)
        socket_states_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)]) m' evs) := by
  sys_refute

/-- `2^32 | 999` is level 999: still unknown, still -ENOPROTOOPT.
kernel: net/socket.c:__sys_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_level_high_half_unknown_is_enoprotoopt (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 999)) 2 4096 4) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- `optlen = 2^32 + 4` is `optlen = 4`: not negative, the level answers.
kernel: net/socket.c:__sys_setsockopt,do_sock_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_optlen_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_optlen_high_half_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4))) socket_states_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `optlen = 2^63` has bit 63 set and a clear low half: the `int` is 0, not
negative — a twin testing the 64-bit sign would answer -EINVAL here.
kernel: net/socket.c:__sys_setsockopt,do_sock_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_optlen_bit63_only_is_enoprotoopt (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 63))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  sys_norm

/-- `optlen = 2^32 - 1` is the `int` -1 with a clear high half: -EINVAL — a
twin testing the 64-bit sign would let it through to the level.
kernel: net/socket.c:__sys_setsockopt,do_sock_setsockopt@v6.18.46 -/
theorem setsockopt_optlen_low_word_minus_one_is_einval (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 - 1))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] := by
  sys_norm

/-! ## The two gates, at their values

`sock_level_known` and `int32_neg` are decided inside the arms above; these
state them at the boundaries the arms' inputs walk, so a change to either
is seen where it is made.  Neither narrows: the table's `int32` does, and
`int32_neg` reads the sign of the low half `sint32` keeps. -/

/-- The three levels with a handler.
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem sock_level_known_sol_socket : sock_level_known (Z_to_bv 64 1) = true := by decide

/-- kernel: net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem sock_level_known_sol_ip : sock_level_known (Z_to_bv 64 0) = true := by decide

/-- kernel: net/ipv4/tcp.c:tcp_setsockopt@v6.18.46 -/
theorem sock_level_known_sol_tcp : sock_level_known (Z_to_bv 64 6) = true := by decide

/-- SOL_UDP has no handler on a stream socket.
kernel: net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem sock_level_known_sol_udp : sock_level_known (Z_to_bv 64 17) = false := by decide

/-- The gate does not narrow: `2^32 + 6` is unknown to it, and it is the
table's `int32` that makes it SOL_TCP.
kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem sock_level_known_high_half : sock_level_known (Z_to_bv 64 (2 ^ 32 + 6)) = false := by
  decide

/-- All ones is -1.
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem int32_neg_minus_one : int32_neg (Z_to_bv 64 (2 ^ 64 - 1)) = true := by decide

/-- INT_MIN.
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem int32_neg_int_min : int32_neg (Z_to_bv 64 (2 ^ 31)) = true := by decide

/-- INT_MAX.
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem int32_neg_int_max : int32_neg (Z_to_bv 64 (2 ^ 31 - 1)) = false := by decide

/-- kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem int32_neg_zero : int32_neg (Z_to_bv 64 0) = false := by decide

/-- Bit 63 alone is the `int` 0: the sign read is of the low half.
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem int32_neg_bit63_only : int32_neg (Z_to_bv 64 (2 ^ 63)) = false := by decide

/-- The 32-bit seam from both sides: all ones in the low word alone is -1…
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem int32_neg_low_word_minus_one : int32_neg (Z_to_bv 64 (2 ^ 32 - 1)) = true := by decide

/-- …and `2^32` itself is the `int` 0.
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem int32_neg_two_pow_32 : int32_neg (Z_to_bv 64 (2 ^ 32)) = false := by decide

/-- `2^32` is unknown to the gate, which does not narrow; the table's `int32`
makes it SOL_IP (0), which the two arm pins below state.
kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem sock_level_known_two_pow_32 : sock_level_known (Z_to_bv 64 (2 ^ 32)) = false := by decide

/-- Level `2^32` through the table is SOL_IP, so declined and not
-ENOPROTOOPT: the seam where a 64-bit value no gate knows becomes a known
`int`.  Both arms.
kernel: net/socket.c:__sys_setsockopt@v6.18.46 -/
theorem setsockopt_level_two_pow_32_declines (o : outcome SyscallEffect) :
    syscall_spec (setsockopt_in 6 (Z_to_bv 64 (2 ^ 32)) 2 4096 4) socket_states_model o ↔
      o = Unmodeled := by
  sys_norm

/-- kernel: net/socket.c:__sys_getsockopt@v6.18.46 -/
theorem getsockopt_level_two_pow_32_declines (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 6 (Z_to_bv 64 (2 ^ 32)) 2 4096 4104 (fun _ => none)) socket_states_model o ↔
      o = Unmodeled := by
  sys_norm

/-- The ledger reader at the three shapes the pins above walk: readable,
unreadable, straddling.
kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_optlen_read_readable :
    getsockopt_optlen_read (getsockopt_in 3 17 4 4096 4096 sockaddr_in_any_mem) 4096 = [(4096, 4)] := by
  decide

/-- kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_optlen_read_unreadable :
    getsockopt_optlen_read (getsockopt_in 3 17 4 4096 8192 sockaddr_in_any_mem) 8192 = [] := by
  decide

/-- kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_optlen_read_straddling :
    getsockopt_optlen_read (getsockopt_in 3 17 4 4096 4109 sockaddr_in_any_mem) 4109 = [] := by
  decide

/-- A range that wraps past `2^64`: the walk visits `2^64-2`, `2^64-1`, 0 and
1 and finds the first two unmapped, as every user memory has them, where
`access_ok` refuses the range before the kernel copies a byte.
kernel: include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem getsockopt_optlen_read_wrapping :
    getsockopt_optlen_read
      (getsockopt_in 3 17 4 4096 (Z_to_bv 64 (2 ^ 64 - 2)) sockaddr_in_any_mem)
      (Z_to_bv 64 (2 ^ 64 - 2)) = [] := by
  decide

/-- …and through the arm: -EOPNOTSUPP with an empty ledger.
kernel: net/socket.c:do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_wrapping_optlen_is_eopnotsupp_unledgered (o : outcome SyscallEffect) :
    syscall_spec (getsockopt_in 3 17 4 4096 (Z_to_bv 64 (2 ^ 64 - 2)) sockaddr_in_any_mem)
        fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) fresh_socket_model [] := by
  sys_norm

/-! ## The table: the two option arms -/

/-- kernel: include/uapi/asm-generic/unistd.h:__NR_setsockopt@v6.18.46 -/
theorem setsockopt_is_dispatched : (208 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_getsockopt@v6.18.46 -/
theorem getsockopt_is_dispatched : (209 : Int) ∈ modeled_sysnos := by decide

/-! ## socketpair (199): the writes land before the failure

`__sys_socketpair` (net/socket.c:1769, v6.18.46): the flag test (:1776-1778),
two descriptor reservations (:1788-1796), two `put_user`s (:1798-1804),
then `sock_create` twice and `sock_no_socketpair`'s -EOPNOTSUPP (:1828,
net/core/sock.c:3444-3447), whose `out:` releases both numbers
(:1855-1858).  On the three standard channels the two lowest free numbers
are 3 and 4, stored little-endian at `sv` and `sv + 4`. -/

/-- The demo process: fds 0, 1, 2 open and nothing else, so the reserved
numbers are 3 and 4. -/
def socketpair_model : Model := fixture_of

attribute [sys_simp low] socketpair_model.eq_1

/-- AF_INET/SOCK_STREAM at the default protocol into a writable destination
answers one of five things: a reservation errno with nothing written
(-EMFILE past `RLIMIT_NOFILE`, -ENOMEM when the table cannot grow), or the
two writes carrying -ENFILE, -ENOMEM, or the -EOPNOTSUPP every AF_INET
`proto_ops` answers.
probe: testing/syscall-check/tests/socketpair_spec.c#conform -- inet -/
theorem socketpair_inet_stream_iff (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 1 0 4096 wmem_open) socketpair_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) socketpair_model [])
       ∨ ((o = Ok (mkEffect (errno_ret ENFILE) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model []
           ∨ o = Ok (mkEffect (errno_ret ENOMEM) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model [])
          ∨ o = Ok (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model [])) := by
  sys_norm

/-- A kernel that failed with -EOPNOTSUPP WITHOUT writing skipped two
`put_user`s Linux always runs first.
probe: testing/syscall-check/tests/socketpair_spec.c#reject --mutate socketpair:drop-writes -- inet -/
theorem socketpair_unwritten_eopnotsupp_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 4096 wmem_open) socketpair_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) m' evs) := by
  sys_refute

/-- The numbers are the two LOWEST free descriptors, not any pair.
probe: testing/syscall-check/tests/socketpair_spec.c#reject --mutate socketpair:drop-writes,smuggle-write-bytes:a3:ffffffff,smuggle-write-bytes:a3+4:ffffffff -- pinnedfds -/
theorem socketpair_wrong_numbers_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 4096 wmem_open) socketpair_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [(4096, [4, 0, 0, 0]), (4100, [5, 0, 0, 0])] [])
            m' evs) := by
  sys_refute

/-- …and the failure is never turned into a success.
kernel: net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem socketpair_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 4096 wmem_open) socketpair_model
        (Ok (mkEffect 0 [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- A reservation errno comes BEFORE either `put_user`: -EMFILE beside the
writes is a lie.
probe: testing/syscall-check/tests/socketpair_spec.c#reject --mutate socketpair:ret=-EMFILE -- inet -/
theorem socketpair_emfile_with_writes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 4096 wmem_open) socketpair_model
        (Ok (mkEffect (errno_ret EMFILE) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- The reservation set is a SET: -EACCES with nothing written is not in it.
probe: testing/syscall-check/tests/socketpair_spec.c#reject --mutate socketpair:ret=-EACCES,drop-writes -- inet -/
theorem socketpair_eacces_unwritten_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 4096 wmem_open) socketpair_model
        (Ok (mkEffect (errno_ret EACCES) [] []) m' evs) := by
  sys_refute

/-- …nor is the post-write -EACCES an LSM could answer: the model is
narrower than Linux there (linux-process-semantics@ff0313ba4f:bugs/socketpair-lsm-denials-not-admitted.md).
probe: testing/syscall-check/tests/socketpair_spec.c#reject --mutate socketpair:ret=-EACCES -- pinnedfds -/
theorem socketpair_eacces_written_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 4096 wmem_open) socketpair_model
        (Ok (mkEffect (errno_ret EACCES) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- SOCK_DGRAM takes the same `sock_no_socketpair` answer.
probe: testing/syscall-check/tests/socketpair_spec.c#conform -- dgram -/
theorem socketpair_inet_dgram_iff (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 2 0 4096 wmem_open) socketpair_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) socketpair_model [])
       ∨ ((o = Ok (mkEffect (errno_ret ENFILE) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model []
           ∨ o = Ok (mkEffect (errno_ret ENOMEM) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model [])
          ∨ o = Ok (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model [])) := by
  sys_norm

/-- probe: testing/syscall-check/tests/socketpair_spec.c#reject --mutate socketpair:drop-writes -- dgram -/
theorem socketpair_inet_dgram_unwritten_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 2 0 4096 wmem_open) socketpair_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) m' evs) := by
  sys_refute

/-- SOCK_CLOEXEC (524288) is a KNOWN type flag: accepted, then the same
write-then-fail.
probe: testing/syscall-check/tests/socketpair_spec.c#conform -- cloexec -/
theorem socketpair_cloexec_iff (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 524289 0 4096 wmem_open) socketpair_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) socketpair_model [])
       ∨ ((o = Ok (mkEffect (errno_ret ENFILE) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model []
           ∨ o = Ok (mkEffect (errno_ret ENOMEM) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model [])
          ∨ o = Ok (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model [])) := by
  sys_norm

/-- SOCK_NONBLOCK (2048) is answered here, unlike in `socket`: the flag
never reaches a file, because the call fails for every modeled triple
after both writes.
kernel: net/socket.c:__sys_socketpair,__sock_create; net/core/sock.c:sock_no_socketpair; fs/file.c:alloc_fd,alloc_fdtable@v6.18.46 -/
theorem socketpair_nonblock_iff (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 2049 0 4096 wmem_open) socketpair_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) socketpair_model [])
       ∨ ((o = Ok (mkEffect (errno_ret ENFILE) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model []
           ∨ o = Ok (mkEffect (errno_ret ENOMEM) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model [])
          ∨ o = Ok (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model [])) := by
  sys_norm

/-- An unknown type-flag bit is -EINVAL, and the test runs BEFORE the two
descriptor reservations (`__sys_socketpair`, net/socket.c:1776-1778), so the
answer carries no write.
kernel: net/socket.c:__sys_socketpair@v6.18.46 -/
theorem socketpair_bad_flag_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    socketpair_spec 2 257 0 4096 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- The same at the dispatcher: -EINVAL with `sv` untouched.
kernel: net/socket.c:__sys_socketpair@v6.18.46 -/
theorem socketpair_bad_flag_dispatched_is_einval (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 257 0 4096 wmem_open) socketpair_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) socketpair_model [] := by
  sys_norm

/-- …so -EINVAL beside the two descriptor writes is a lie: the flag test
precedes both reservations and both `put_user`s.
kernel: net/socket.c:__sys_socketpair@v6.18.46 -/
theorem socketpair_bad_flag_writes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 257 0 4096 wmem_open) socketpair_model
        (Ok (mkEffect (errno_ret EINVAL) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- The flag test is answered for EVERY family, not just the modeled one:
AF_UNIX with an unknown type-flag bit is -EINVAL too, ahead of the AF_UNIX
decline below.
kernel: net/socket.c:__sys_socketpair@v6.18.46 -/
theorem socketpair_bad_flag_af_unix_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    socketpair_spec 1 257 0 4096 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- AF_UNIX SUCCEEDS on Linux and hands back two sockets connected to each
other, a shape `State.SockState` cannot express: declined.
probe: testing/syscall-check/tests/socketpair_spec.c#fail-closed -- unix -/
theorem socketpair_af_unix_declines (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 1 1 0 4096 wmem_open) socketpair_model o ↔ o = Unmodeled := by
  sys_norm

/-- A nonzero protocol reaches `inet_create`'s range test and `inetsw` match
after both writes: declined.
probe: testing/syscall-check/tests/socketpair_spec.c#fail-closed -- proto -/
theorem socketpair_nonzero_protocol_declines (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 1 6 4096 wmem_open) socketpair_model o ↔ o = Unmodeled := by
  sys_norm

/-- SOCK_RAW reaches `inet_create`'s CAP_NET_RAW test: declined.
probe: testing/syscall-check/tests/socketpair_spec.c#fail-closed -- raw -/
theorem socketpair_raw_declines (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 3 0 4096 wmem_open) socketpair_model o ↔ o = Unmodeled := by
  sys_norm

/-! ## socketpair: the destination

`put_user` on riscv64 is `access_ok(p, 4) ? __put_user(x, p) : -EFAULT`
(arch/riscv/include/asm/uaccess.h:408-415, v6.18.46) and `__access_ok` is
`(size <= limit) && (addr <= limit - size)` (include/asm-generic/access_ok.h:
40) with `limit = TASK_SIZE`, 0x800000000000 under Sv48
(`TASK_SIZE = 140737488355328` above).  The two stores carry SEPARATE
tests over their own 4-byte ranges; the band where the first passes and the
second is refused is a PARTIAL outcome the model declines. -/

/-- `sv = TASK_SIZE` is refused at the FIRST store: -EFAULT with nothing
written joins the two reservation errnos.  (The probe's `faultsv` passes
`(void *)-1`, socketpair_spec.c:165 — the wrapping pin's shape below.)
kernel: arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok; fs/file.c:alloc_fd,alloc_fdtable@v6.18.46 -/
theorem socketpair_sv_task_size_is_efault (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 1 0 140737488355328 (fun _ => none)) socketpair_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) socketpair_model [])
       ∨ o = Ok (mkEffect (errno_ret EFAULT) [] []) socketpair_model []) := by
  sys_norm

/-- A kernel that never touched `usockvec` before failing with -EOPNOTSUPP
skipped a store `access_ok` refuses.
probe: testing/syscall-check/tests/socketpair_spec.c#reject --mutate socketpair:ret=-EOPNOTSUPP -- faultsv -/
theorem socketpair_sv_task_size_eopnotsupp_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 140737488355328 (fun _ => none)) socketpair_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) m' evs) := by
  sys_refute

/-- …and a post-write errno is not admissible where no write can land.
probe: testing/syscall-check/tests/socketpair_spec.c#reject --mutate socketpair:ret=-ENFILE -- faultsv -/
theorem socketpair_sv_task_size_enfile_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 140737488355328 (fun _ => none)) socketpair_model
        (Ok (mkEffect (errno_ret ENFILE) [] []) m' evs) := by
  sys_refute

/-- …nor is -EFAULT with `fd1` stored: the first store is the refused one.
kernel: arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem socketpair_sv_task_size_written_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 140737488355328 (fun _ => none)) socketpair_model
        (Ok (mkEffect (errno_ret EFAULT) [(140737488355328, [3, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- `sv = TASK_SIZE - 3` is the LOWEST destination whose first store is
refused: the -EFAULT band begins here.
probe: testing/syscall-check/tests/socketpair_spec.c#conform -- edgefaultsv -/
theorem socketpair_sv_task_size_minus_3_is_efault (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 1 0 140737488355325 wmem_open) socketpair_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) socketpair_model [])
       ∨ o = Ok (mkEffect (errno_ret EFAULT) [] []) socketpair_model []) := by
  sys_norm

/-- probe: testing/syscall-check/tests/socketpair_spec.c#reject --mutate socketpair:ret=-EOPNOTSUPP -- edgefaultsv -/
theorem socketpair_sv_task_size_minus_3_eopnotsupp_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 140737488355325 wmem_open) socketpair_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [(140737488355325, [3, 0, 0, 0]), (140737488355329, [4, 0, 0, 0])] [])
            m' evs) := by
  sys_refute

/-- One byte lower, `sv = TASK_SIZE - 4`: the first store passes its own
`access_ok` and the second is refused.  Linux stores `fd1` if the page is
mapped and nothing if it is not, then -EFAULT — a partial outcome, declined.
probe: testing/syscall-check/tests/socketpair_spec.c#fail-closed -- edgefarsv -/
theorem socketpair_sv_task_size_minus_4_declines (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 1 0 140737488355324 wmem_open) socketpair_model o ↔
      o = Unmodeled := by
  sys_norm

/-- `sv = TASK_SIZE - 5`: the same band, from Rocq's own worked case.
kernel: arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem socketpair_sv_task_size_minus_5_declines (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 1 0 140737488355323 (fun _ => none)) socketpair_model o ↔
      o = Unmodeled := by
  sys_norm

/-- `sv = TASK_SIZE - 7`: still in the band — the 8-byte test fails while
the first 4-byte test passes.  Narrow the destination conjunct to 4 and this
case turns into two writes Linux never produces.
kernel: arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem socketpair_sv_task_size_minus_7_declines (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 1 0 140737488355321 wmem_open) socketpair_model o ↔
      o = Unmodeled := by
  sys_norm

/-- `sv = TASK_SIZE - 8` is the LAST destination whose two stores are both
accepted: both writes land, at `TASK_SIZE - 8` and `TASK_SIZE - 4`.  Widen
the conjunct to 16 and this case falls through instead.
kernel: net/socket.c:__sys_socketpair,__sock_create; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok; net/core/sock.c:sock_no_socketpair; fs/file.c:alloc_fd,alloc_fdtable@v6.18.46 -/
theorem socketpair_sv_task_size_minus_8_writes_both (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 1 0 140737488355320 wmem_open) socketpair_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) socketpair_model [])
       ∨ ((o = Ok (mkEffect (errno_ret ENFILE) [(140737488355320, [3, 0, 0, 0]), (140737488355324, [4, 0, 0, 0])] [])
               socketpair_model []
           ∨ o = Ok (mkEffect (errno_ret ENOMEM) [(140737488355320, [3, 0, 0, 0]), (140737488355324, [4, 0, 0, 0])] [])
               socketpair_model [])
          ∨ o = Ok (mkEffect (errno_ret EOPNOTSUPP) [(140737488355320, [3, 0, 0, 0]), (140737488355324, [4, 0, 0, 0])] [])
               socketpair_model [])) := by
  sys_norm

/-- …so -EFAULT there is a lie: the conjunct costs the walk nothing it was
entitled to.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem socketpair_sv_task_size_minus_8_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 140737488355320 wmem_open) socketpair_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- An in-range destination that is NOT mapped: Linux's `put_user` faults,
and the model knows the page neither writable nor refused — declined.
probe: testing/syscall-check/tests/socketpair_spec.c#fail-closed -- farsv -/
theorem socketpair_unmapped_sv_declines (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 1 0 65536 (fun _ => none)) socketpair_model o ↔
      o = Unmodeled := by
  sys_norm

/-! ## socketpair: the destination that walks off the top of the address
space

Rocq's mutation test made permanent: the walk `State.read_bytes_map` wraps
at `2^64`, `__access_ok`'s subtraction does not, and the guard is what
separates them. -/

/-- The last four bytes of the address space, so an 8-byte walk covers
them and then the four at 0. -/
def socketpair_wrap_sv : word := Z_to_bv 64 (2 ^ 64 - 4)

/-- A memory mapping EXACTLY those eight bytes and nothing else. -/
def socketpair_wrap_mem : word → Option byte := fun a =>
  if bv_unsigned a < 4 ∨ 2 ^ 64 - 4 ≤ bv_unsigned a then some 0 else none

/-- THE BARE WALK PASSES: it reads all eight bytes back off a memory that
maps only those eight.  This is what the spec used to consult alone.
model: a closed evaluation of State.read_bytes_map over a fixture memory; the kernel claim is the guard pin beside it -/
theorem socketpair_wrap_would_pass_the_bare_walk :
    read_bytes_map socketpair_wrap_mem socketpair_wrap_sv (Z_to_bv 64 8) ≠ none := by
  decide

/-- …and the guard declines it on `__access_ok`'s `addr <= (limit - size)`
half (include/asm-generic/access_ok.h:40, Linux v6.18.46), the subtraction
that `access_okb` spells and that a wrapping sum would have passed.  Delete
the conjunct from `socketpair_dest_writable` and this fails; the answer at
the dispatcher is `socketpair_wrapping_destination_is_efault` below.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem socketpair_wrap_dest_is_not_writable :
    socketpair_dest_writable socketpair_wrap_mem socketpair_wrap_sv = false := by
  decide

/-- THE ONE THAT MATTERS: the first `put_user` is refused by `access_ok`,
so -EFAULT with nothing written is the answer.
kernel: arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok; fs/file.c:alloc_fd,alloc_fdtable@v6.18.46 -/
theorem socketpair_wrapping_destination_is_efault (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 1 0 socketpair_wrap_sv socketpair_wrap_mem) socketpair_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) socketpair_model [])
       ∨ o = Ok (mkEffect (errno_ret EFAULT) [] []) socketpair_model []) := by
  sys_norm

/-- …and the write the spec used to allow — two numbers stored at
`2^64 - 4` and, after the word wrapped, at 0 — is refused.
kernel: arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem socketpair_wrapping_destination_writes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 socketpair_wrap_sv socketpair_wrap_mem) socketpair_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP) [(socketpair_wrap_sv, [3, 0, 0, 0]), (0, [4, 0, 0, 0])] [])
            m' evs) := by
  sys_refute

/-- Eight mapped bytes at `2^63`: a range that does NOT wrap and is refused
anyway. -/
def socketpair_high_mem : word → Option byte := fun a =>
  if 2 ^ 63 ≤ bv_unsigned a ∧ bv_unsigned a < 2 ^ 63 + 8 then some 0 else none

/-- The control: the range really is mapped end to end.
model: a closed evaluation of State.read_bytes_map over a fixture memory -/
theorem socketpair_high_range_reads :
    read_bytes_map socketpair_high_mem (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 8) ≠ none := by
  decide

/-- …and its sum is under `2^64`, so a bare no-wrap test would allow it.
model: a closed evaluation of two_pow_64 against a fixture address; the kernel claim is socketpair_past_long_max_is_efault -/
theorem socketpair_high_range_would_pass_a_no_wrap_test :
    decide (two_pow_64 ≤ bv_unsigned (Z_to_bv 64 (2 ^ 63) : word) + bv_unsigned (Z_to_bv 64 8 : word))
      = false := by
  decide

/-- The guard refuses it because `addr <= (limit - size)` fails with
`limit = TASK_SIZE_MAX` (include/asm-generic/access_ok.h:40, Linux
v6.18.46): `2^63` is above the top of user space, whether or not the sum
wraps.  The answer at the dispatcher is `socketpair_past_long_max_is_efault`
below.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem socketpair_past_long_max_is_not_writable :
    socketpair_dest_writable socketpair_high_mem (Z_to_bv 64 (2 ^ 63)) = false := by
  decide

/-- …and at the dispatcher: -EFAULT with nothing written, the two writes
refused, because `__access_ok` tests `addr <= limit - size` and not a wrap.
kernel: include/asm-generic/access_ok.h:__access_ok; arch/riscv/include/asm/uaccess.h:put_user; fs/file.c:alloc_fd,alloc_fdtable@v6.18.46 -/
theorem socketpair_past_long_max_is_efault (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in 2 1 0 9223372036854775808 socketpair_high_mem) socketpair_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) socketpair_model [])
       ∨ o = Ok (mkEffect (errno_ret EFAULT) [] []) socketpair_model []) := by
  sys_norm

/-- kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem socketpair_past_long_max_writes_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in 2 1 0 9223372036854775808 socketpair_high_mem) socketpair_model
        (Ok (mkEffect (errno_ret EOPNOTSUPP)
              [(9223372036854775808, [3, 0, 0, 0]), (9223372036854775812, [4, 0, 0, 0])] [])
            m' evs) := by
  sys_refute

/-! ## The channel of an accepted connection

Twins of the three lemmas Rocq proves beside `conn_channel`, the
exhaustion boundary as a computation, and then `accept4_spec`'s listening
arm run through the dispatcher on both sides of that boundary: the guard
the lemmas discharge is the one the arm consults. -/

/-- Below the wrap the channel is the index plus three, in `Int`.
rocq-twin: conn_channel_unsigned -/
theorem conn_channel_unsigned (ix : word) (h : bv_unsigned ix < 2 ^ 64 - 3) :
    bv_unsigned (conn_channel ix) = bv_unsigned ix + 3 := by
  have h3 : (Z_to_bv 64 3 : word).toNat = 3 := by decide
  have hlt : ix.toNat + 3 < 2 ^ 64 := by
    simp only [bv_unsigned] at h
    omega
  simp only [conn_channel, bv_unsigned, BitVec.toNat_add, h3, Nat.mod_eq_of_lt hlt]
  omega

/-- …so two issued channels agree only on equal indices.
rocq-twin: conn_channel_injective -/
theorem conn_channel_injective (ix1 ix2 : word) (h1 : bv_unsigned ix1 < 2 ^ 64 - 3)
    (h2 : bv_unsigned ix2 < 2 ^ 64 - 3) (heq : conn_channel ix1 = conn_channel ix2) :
    bv_unsigned ix1 = bv_unsigned ix2 := by
  have e1 := conn_channel_unsigned ix1 h1
  have e2 := conn_channel_unsigned ix2 h2
  rw [heq] at e1
  omega

/-- …and none of them is stdin's, stdout's or stderr's.
rocq-twin: conn_channel_not_std -/
theorem conn_channel_not_std (ix : word) (h : bv_unsigned ix < 2 ^ 64 - 3) :
    2 < bv_unsigned (conn_channel ix) := by
  rw [conn_channel_unsigned ix h]
  simp only [bv_unsigned]
  omega

/-- The guard's `false` is exactly the hypothesis the three lemmas above
carry, so `accept4_spec`'s test turns them into lemmas about every index it
still hands a connection over at.
rocq-twin: conn_ix_not_exhausted_lt -/
theorem conn_ix_not_exhausted_lt (ix : word) (h : conn_ix_exhausted ix = false) :
    bv_unsigned ix < two_pow_64 - 3 := by
  simp only [conn_ix_exhausted, decide_eq_false_iff_not, Int.not_le] at h
  exact h

/-- …so past the guard no issued channel is a standard stream…
rocq-twin: guarded_conn_channel_not_std -/
theorem guarded_conn_channel_not_std (ix : word) (h : conn_ix_exhausted ix = false) :
    2 < bv_unsigned (conn_channel ix) :=
  conn_channel_not_std ix
    (by have h' := conn_ix_not_exhausted_lt ix h; unfold two_pow_64 at h'; exact h')

/-- …and two issued channels agree only on equal indices.
rocq-twin: guarded_conn_channel_injective -/
theorem guarded_conn_channel_injective (ix1 ix2 : word) (h1 : conn_ix_exhausted ix1 = false)
    (h2 : conn_ix_exhausted ix2 = false) (heq : conn_channel ix1 = conn_channel ix2) :
    bv_unsigned ix1 = bv_unsigned ix2 :=
  conn_channel_injective ix1 ix2
    (by have h' := conn_ix_not_exhausted_lt ix1 h1; unfold two_pow_64 at h'; exact h')
    (by have h' := conn_ix_not_exhausted_lt ix2 h2; unfold two_pow_64 at h'; exact h')
    heq

/-- At the wrap the three next channels ARE the standard streams, which is
what the exhaustion guard exists to keep unreachable.
model: a closed evaluation of Net.Socket.conn_channel at the three indices the guard refuses -/
theorem conn_channel_at_the_wrap_is_stdin_stdout_stderr :
    conn_channel (Z_to_bv 64 (2 ^ 64 - 3)) = 0 ∧ conn_channel (Z_to_bv 64 (2 ^ 64 - 2)) = 1
      ∧ conn_channel (Z_to_bv 64 (2 ^ 64 - 1)) = 2 := by
  decide

/-- The guard fires at exactly `2^64 - 3` and not one below.  It sits on
`accept4_spec`'s listening arm (the wrap pins below run it there), and
Linux has no counterpart to fire: `do_accept` (net/socket.c:1952, Linux v6.18.46) and `inet_csk_accept`
(net/ipv4/inet_connection_sock.c:649) bound an accept by the listener's
queue and the descriptor table (`alloc_fd`'s -EMFILE, fs/file.c:591), never
by a count of the connections accepted before it.  The counter that wraps
is the model's channel index, so the decline is the model's own bound,
placed at the last index whose channel is not a standard stream
(linux-process-semantics@ff0313ba4f:bugs/socket-conn-channel-wraps-at-2-64.md);
this pins that it declines no
earlier than it must.
kernel: net/socket.c:do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept; fs/file.c:alloc_fd@v6.18.46 -/
theorem conn_ix_exhausted_boundary :
    conn_ix_exhausted (Z_to_bv 64 (2 ^ 64 - 3)) = true
      ∧ conn_ix_exhausted (Z_to_bv 64 (2 ^ 64 - 4)) = false := by
  decide

/-- AT THE WRAP NO DESCRIPTOR IS HANDED OVER AT ALL: with the counter at
`2^64 - 3` the success branch is EMPTY — `choose (fun _ => False)`, not a
decline — and the three errnos are all the arm admits, each leaving the
model alone.  The bound is the model's (`conn_ix_exhausted`'s docstring),
not the kernel's, which hands the descriptor out whenever `alloc_fd` and
`inet_csk_accept` succeed; what the kernel does fix is the errno set, which
is unchanged here.  Rocq's `accept_at_the_wrap_hands_over_no_descriptor_at_all`,
`accept_at_the_wrap_still_answers_its_errnos` and
`accept_at_the_wrap_errno_set_is_still_exactly_these_three`.
kernel: fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept_at_the_wrap_iff (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 0) exhausted_listening_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) exhausted_listening_model []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) exhausted_listening_model []
       ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) exhausted_listening_model []) := by
  sys_norm

/-- …so the descriptor Linux would allocate, 4, is refused there: the
model's own bound, placed so that the channel separation stays true
(linux-process-semantics@ff0313ba4f:bugs/socket-conn-channel-wraps-at-2-64.md).
kernel: net/socket.c:__sys_accept4_file@v6.18.46 -/
theorem accept_at_the_wrap_rejects_the_allocated_fd (m' : Model) (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) exhausted_listening_model
        (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- …AND IT NEVER DECLINES: the empty branch is not `unmodeled`, because the
`alt` sibling answers a concrete errno at the same input and model, and the
checker's totality needs the arm to answer there.
kernel: net/socket.c:do_accept@v6.18.46 -/
theorem accept_at_the_wrap_never_declines :
    ¬ syscall_spec (accept4_in 3 0 0 0) exhausted_listening_model Unmodeled := by
  sys_refute

/-- ONE BELOW THE WRAP THE HAND-OVER STILL HAPPENS: at `2^64 - 4` the guard
does not fire (`conn_ix_exhausted_boundary`), fd 4 is handed over on
channel `2^64 - 1`, and the counter moves onto the boundary.  Rocq's
`accept_one_below_the_wrap_still_hands_over`.
kernel: fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem accept_one_below_the_wrap_iff (o : outcome SyscallEffect) :
    syscall_spec (accept4_in 3 0 0 0) last_usable_listening_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) last_usable_listening_model []
         ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) last_usable_listening_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) last_usable_listening_model [])
       ∨ o = Ok (mkEffect 4 [] []) last_usable_accepted_model []) := by
  sys_norm

/-- …on the LAST FREE CHANNEL, `2^64 - 1`: the three above it are the standard
streams' (`conn_channel_at_the_wrap_is_stdin_stdout_stderr`), which is
what the guard exists to keep the arm off.
model: a closed evaluation of Net.Socket.conn_channel at the last index below the wrap -/
theorem accept_one_below_the_wrap_uses_the_last_free_channel :
    conn_channel (Z_to_bv 64 (2 ^ 64 - 4)) = Z_to_bv 64 (2 ^ 64 - 1) := by
  decide

/-- …and a hand-over reported on stdin's channel, the wrapped value, is
refused: the channel is `conn_channel`'s, not a free choice.
kernel: net/socket.c:do_accept@v6.18.46 -/
theorem accept_one_below_the_wrap_wrapped_channel_rejected (evs : List event) :
    ¬ syscall_spec (accept4_in 3 0 0 0) last_usable_listening_model
        (Ok (mkEffect 4 [] [])
            (with_accepted
              [ (4, .FdSocket (.SkConnected peer0 0 NFin)),
                (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
                (3, .FdSocket .SkListening) ]
              last_usable_listening_model) evs) := by
  sys_norm
  intro h
  injection h with h
  injection h with _ h _
  exact absurd h (by decide)

/-! ## The exhausted descriptor scan, stated over every table

`socketpair_fds` answers `none` when `State.alloc_fd`'s scan finds no free
number, and `socketpair_spec` then DECLINES: Linux has no such bound — past
RLIMIT_NOFILE `alloc_fd` answers -EMFILE (fs/file.c:591, v6.18.46), which the
reservation errnos already carry — so the arm is the model's own fail-closed
answer to its own scan.  No 4096-descriptor fixture is needed to pin it: the
statement quantifies over the model and assumes the exhausted scan, which is
why a mutant answering an errno there is killed rather than allowlisted. -/

/-- Over any model whose table exhausts the scan, the modeled triple declines.
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem socketpair_exhausted_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (h : socketpair_fds m.m_fd.fdst_table = none) :
    socketpair_spec 2 1 0 4096 i m o ↔ o = Unmodeled := by
  sys_norm
  simp only [h]
  sys_norm

/-- …and no errno stands in for that decline: -EINVAL is refused (so would
any other answer be, by the `iff` above).
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem socketpair_exhausted_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event)
    (h : socketpair_fds m.m_fd.fdst_table = none) :
    ¬ socketpair_spec 2 1 0 4096 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  intro hc
  exact absurd ((socketpair_exhausted_declines i m _ h).mp hc) (by simp)

/-! ## The narrowings the table and the arms perform

Every parameter these seven calls take, bar the two pointers, is an `int`
(net/socket.c, Linux v6.18.46: `SYSCALL_DEFINE3(bind, int, fd, …, int,
addrlen)` :1909, `SYSCALL_DEFINE2(listen, int, fd, int, backlog)` :1947,
`connect` :2125, `getpeername` :2199, `SYSCALL_DEFINE2(shutdown, int, fd,
int, how)` :2490, `SYSCALL_DEFINE4(socketpair, int, family, int, type, int,
protocol, …)` :1861), so the kernel sees the LOW 32 BITS of each register:
the table applies `fd32` to every descriptor and `int32` to `how`
(`Sys/Registry/Net/Socket.lean`), the arms read `addrlen` through `sint32`
and socketpair's three through `abi_low32`.  Every input elsewhere in this
file keeps its high half clear, so none of those pins can tell a twin that
dropped a narrowing from one that kept it — a twin reading `addrlen` as an
unsigned 64-bit count, or a table line without `fd32`, passed all of them
(the deep review of #832 built each and watched it survive).  These are the
inputs that separate them: a high half set over a low half the arm answers. -/

/-- `bind(3, addr, 2^32 + 16)` is `bind(3, addr, 16)` — `__sys_bind`'s
`int addrlen` (net/socket.c:1889, v6.18.46) — so the fresh socket binds and
the ledger records the 16 bytes the low half named.
kernel: net/socket.c:__sys_bind; net/ipv4/inet_connection_sock.c:inet_csk_get_port@v6.18.46 -/
theorem bind_addrlen_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 (Z_to_bv 64 (2 ^ 32 + 16)) sockaddr_in_any_mem)
        fresh_socket_model o ↔
      (o = Ok (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(4096, 16)])
              fresh_socket_model []
       ∨ o = Ok (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)])
              (fixture_of (fds := [ (3, .FdSocket .SkBound), (0, .FdChannel 0),
                                    (1, .FdChannel 1), (2, .FdChannel 2) ])) []) := by
  sys_norm

/-- …and the -EINVAL an unsigned 64-bit reading of `addrlen` would give,
with nothing copied, is refused.
kernel: net/socket.c:__sys_bind,move_addr_to_kernel@v6.18.46 -/
theorem bind_addrlen_high_half_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 (Z_to_bv 64 (2 ^ 32 + 16)) sockaddr_in_any_mem)
        fresh_socket_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The same on `connect`: `__sys_connect`'s `int addrlen` (net/socket.c:2109,
v6.18.46) makes `2^32 + 16` sixteen bytes, copied and ledgered, and the
listening socket answers -EISCONN past them.
kernel: net/socket.c:__sys_connect; net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem connect_addrlen_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (connect_in 3 8192 (Z_to_bv 64 (2 ^ 32 + 16)) connect_addr_mem)
        listening_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 16)])
             listening_socket_model [] := by
  sys_norm

/-- …not the unledgered -EINVAL of a 64-bit count over 128.
kernel: net/socket.c:__sys_connect,move_addr_to_kernel@v6.18.46 -/
theorem connect_addrlen_high_half_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in 3 8192 (Z_to_bv 64 (2 ^ 32 + 16)) connect_addr_mem)
        listening_socket_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `socketpair(2^32 + AF_INET, 2^32 + SOCK_STREAM, 2^32, sv)` is the plain
AF_INET stream call: `__sys_socketpair` takes three `int`s (net/socket.c:1769,
v6.18.46), so each high half is gone before the flag test, the triple test
and `sock_create` see the values.  One input, three narrowings: dropping any
one of them changes the answer below.
kernel: net/socket.c:__sys_socketpair,__sock_create; fs/file.c:alloc_fd,alloc_fdtable; net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem socketpair_high_halves_discarded (o : outcome SyscallEffect) :
    syscall_spec (socketpair_in (Z_to_bv 64 (2 ^ 32 + 2)) (Z_to_bv 64 (2 ^ 32 + 1))
                                (Z_to_bv 64 (2 ^ 32)) 4096 wmem_open) socketpair_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) socketpair_model [])
       ∨ ((o = Ok (mkEffect (errno_ret ENFILE) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model []
           ∨ o = Ok (mkEffect (errno_ret ENOMEM) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model [])
          ∨ o = Ok (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
               socketpair_model [])) := by
  sys_norm

/-- …so a `type` read at 64 bits, whose high bit fails `flags & ~(SOCK_CLOEXEC |
SOCK_NONBLOCK)`, does not make it -EINVAL…
kernel: net/socket.c:__sys_socketpair@v6.18.46 -/
theorem socketpair_high_half_type_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (socketpair_in (Z_to_bv 64 (2 ^ 32 + 2)) (Z_to_bv 64 (2 ^ 32 + 1))
                                  (Z_to_bv 64 (2 ^ 32)) 4096 wmem_open) socketpair_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and a `family` or `protocol` read at 64 bits, which would miss the
modeled triple, does not make it a decline.
kernel: net/socket.c:__sys_socketpair@v6.18.46 -/
theorem socketpair_high_half_family_unmodeled_rejected :
    ¬ syscall_spec (socketpair_in (Z_to_bv 64 (2 ^ 32 + 2)) (Z_to_bv 64 (2 ^ 32 + 1))
                                  (Z_to_bv 64 (2 ^ 32)) 4096 wmem_open) socketpair_model
        Unmodeled := by
  sys_refute

/-- `shutdown(listener, 2^32 + SHUT_WR)` is SHUT_WR: `__sys_shutdown`'s `int how`
(net/socket.c:2476, v6.18.46), narrowed by the table's `int32`, so the
listener answers 0…
kernel: net/socket.c:__sys_shutdown@v6.18.46 -/
theorem shutdown_how_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in 8 (Z_to_bv 64 (2 ^ 32 + 1))) socket_states_model o ↔
      o = Ok (mkEffect 0 [] []) socket_states_model [] := by
  sys_norm

/-- …not the -EINVAL a 64-bit `how` outside {0, 1, 2} would draw.
kernel: net/socket.c:__sys_shutdown; net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shutdown_how_high_half_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in 8 (Z_to_bv 64 (2 ^ 32 + 1))) socket_states_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `fd32` ON EACH ARM: `2^32 + 3` names fd 3 (`__sys_bind`'s `int fd`,
net/socket.c:1889, v6.18.46), so the fresh socket binds…
kernel: net/socket.c:__sys_bind; net/ipv4/inet_connection_sock.c:inet_csk_get_port@v6.18.46 -/
theorem bind_fd_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (bind_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 16 sockaddr_in_any_mem)
        fresh_socket_model o ↔
      (o = Ok (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(4096, 16)])
              fresh_socket_model []
       ∨ o = Ok (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)])
              (fixture_of (fds := [ (3, .FdSocket .SkBound), (0, .FdChannel 0),
                                    (1, .FdChannel 1), (2, .FdChannel 2) ])) []) := by
  sys_norm

/-- …and is not -EBADF.
kernel: net/socket.c:__sys_bind@v6.18.46 -/
theorem bind_fd_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 16 sockaddr_in_any_mem)
        fresh_socket_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `listen(2^32 + 3, 128)` on the bound socket listens (`__sys_listen`'s
`int fd`, net/socket.c:1933, v6.18.46)…
kernel: net/socket.c:__sys_listen@v6.18.46 -/
theorem listen_fd_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (listen_in (Z_to_bv 64 (2 ^ 32 + 3)) 128) bound_socket_model o ↔
      o = Ok (mkEffect 0 [] [])
             (fixture_of (fds := [ (3, .FdSocket .SkListening), (0, .FdChannel 0),
                                   (1, .FdChannel 1), (2, .FdChannel 2) ])) [] := by
  sys_norm

/-- …and is not -EBADF.
kernel: net/socket.c:__sys_listen@v6.18.46 -/
theorem listen_fd_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (listen_in (Z_to_bv 64 (2 ^ 32 + 3)) 128) bound_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `connect(2^32 + 3, …)` on the listening socket is -EISCONN with the copy
ledgered (`__sys_connect`'s `int fd`, net/socket.c:2109, v6.18.46)…
kernel: net/socket.c:__sys_connect; net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem connect_fd_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (connect_in (Z_to_bv 64 (2 ^ 32 + 3)) 8192 16 connect_addr_mem)
        listening_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 16)])
             listening_socket_model [] := by
  sys_norm

/-- …and is not -EBADF.
kernel: net/socket.c:__sys_connect@v6.18.46 -/
theorem connect_fd_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (connect_in (Z_to_bv 64 (2 ^ 32 + 3)) 8192 16 connect_addr_mem)
        listening_socket_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `getpeername(2^32 + 6)` is the fresh socket's -ENOTCONN
(`__sys_getpeername`'s `int fd`, net/socket.c:2173, v6.18.46)…
kernel: net/socket.c:__sys_getpeername; net/ipv4/af_inet.c:inet_getname@v6.18.46 -/
theorem getpeername_fd_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (getpeername_in (Z_to_bv 64 (2 ^ 32 + 6))) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model [] := by
  sys_norm

/-- …and is not -EBADF.
kernel: net/socket.c:__sys_getpeername@v6.18.46 -/
theorem getpeername_fd_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getpeername_in (Z_to_bv 64 (2 ^ 32 + 6))) socket_states_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `shutdown(2^32 + 8, SHUT_WR)` is the listener's 0 (`__sys_shutdown`'s
`int fd`, net/socket.c:2476, v6.18.46)…
kernel: net/socket.c:__sys_shutdown@v6.18.46 -/
theorem shutdown_fd_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (shutdown_in (Z_to_bv 64 (2 ^ 32 + 8)) 1) socket_states_model o ↔
      o = Ok (mkEffect 0 [] []) socket_states_model [] := by
  sys_norm

/-- …and is not -EBADF.
kernel: net/socket.c:__sys_shutdown@v6.18.46 -/
theorem shutdown_fd_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (shutdown_in (Z_to_bv 64 (2 ^ 32 + 8)) 1) socket_states_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-! ## Two orders inside `bind` that only a two-flaw address can see

`inet_bind_sk`'s 16-byte minimum (net/ipv4/af_inet.c:453, v6.18.46) fires
before `__inet_bind`'s family test (:484), and that family test fires before
the state test (:528).  An address that is BOTH short and of the wrong
family, or of the wrong family on a socket in the wrong state, is the only
input on which the order shows; the pins elsewhere use one flaw at a time,
so a twin with either pair swapped passed them all (the deep review of
#832 built both). -/

/-- EIGHT BYTES OF AF_UNIX on a fresh socket: -EINVAL from the length, with
the eight bytes ledgered, and not the -EAFNOSUPPORT the family would draw
one test later.
kernel: net/ipv4/af_inet.c:inet_bind_sk,__inet_bind@v6.18.46 -/
theorem bind_short_af_unix_is_einval (o : outcome SyscallEffect) :
    syscall_spec (bind_in 3 4096 8 sockaddr_unix_any_mem) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 8)])
             fresh_socket_model [] := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:inet_bind_sk,__inet_bind@v6.18.46 -/
theorem bind_short_af_unix_eafnosupport_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 3 4096 8 sockaddr_unix_any_mem) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 8)]) m' evs) := by
  sys_refute

/-- AF_UNIX ON A BOUND SOCKET: -EAFNOSUPPORT from :484, before :528 can say
-EINVAL for the second bind…
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_af_unix_on_bound_is_eafnosupport (o : outcome SyscallEffect) :
    syscall_spec (bind_in 7 4096 16 sockaddr_unix_any_mem) socket_states_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 16)])
             socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_af_unix_on_bound_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 7 4096 16 sockaddr_unix_any_mem) socket_states_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)]) m' evs) := by
  sys_refute

/-- …on a LISTENING one likewise…
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_af_unix_on_listening_is_eafnosupport (o : outcome SyscallEffect) :
    syscall_spec (bind_in 8 4096 16 sockaddr_unix_any_mem) socket_states_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 16)])
             socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_af_unix_on_listening_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (bind_in 8 4096 16 sockaddr_unix_any_mem) socket_states_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)]) m' evs) := by
  sys_refute

/-- …and on a RESET one the family is refused before the state would have
been declined.
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_af_unix_on_reset_is_eafnosupport (o : outcome SyscallEffect) :
    syscall_spec (bind_in 10 4096 16 sockaddr_unix_any_mem) socket_states_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 16)])
             socket_states_model [] := by
  sys_norm

/-- kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem bind_af_unix_on_reset_unmodeled_rejected :
    ¬ syscall_spec (bind_in 10 4096 16 sockaddr_unix_any_mem) socket_states_model Unmodeled := by
  sys_refute

/-! ## sendto (206), sendmsg (211): the send path

Both calls are read in `__sys_sendto`'s and `__sys_sendmsg`'s order
(net/socket.c:2210-2246 and :2700-2718, Linux v6.18.46), after the model's
own first gate, the flag word.  The probe is
linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/send_spec.c, whose sockets are never
connected: every modeled answer below is either an argument's or a
no-connection state's, and the probe's `dead` walk issues them fresh,
bound, listening, closed and non-socket in that order.  The CONNECTED
states decline in this twin (the spec's send section says why), so the
pins on `accepted_socket_model` and `connected_socket_model` are
declines, each refuting the answer Rocq's twin admits there. -/

attribute [sys_simp low]
  sendto_spec.eq_1 sendmsg_spec.eq_1 send_on_socket.eq_1 send_state.eq_1
  send_bytes.eq_1 recvfrom_spec.eq_1 recvmsg_spec.eq_1 recv_fd_answer.eq_1
  sockfd_lookup_errno.eq_1

/- `access_ok_zero` is `Sys/Uaccess.lean`'s, the range verdict `sendto`
and `recvfrom` answer before the fd; its unfolding enters `local`ly, as
`Checks/Cases/Fs/ReadWrite.lean` registers it for its own pins, because
this file does not import that one. -/
attribute [local sys_simp low] Sys.Uaccess.access_ok_zero.eq_1

/-- `sendto(fd, buf, len, flags, addr, addrlen)` over the readable memory
`mem`. -/
def sendto_in (fd buf len flags addr addrlen : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 206 [fd, buf, len, flags, addr, addrlen] mem (fun _ => none)

/-- `sendmsg(fd, msgp, flags)` over the readable memory `mem`. -/
def sendmsg_in (fd msgp flags : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 211 [fd, msgp, flags, 0, 0, 0] mem (fun _ => none)

/-- `recvfrom(fd, buf, size, flags, NULL, NULL)` over the writable view
`wmem`; nothing is readable.  So a non-NULL, nonzero-length `buf` in range
is at best WRITE-ONLY, which qemu-user refuses: its lock is
`VERIFY_WRITE`, `PAGE_READ | PAGE_WRITE` (linux-user/qemu.h:185, QEMU 11.1.1),
and `page_check_range` fails a page without `PAGE_READ`
(accel/tcg/user-exec.c:538-541, QEMU 11.1.1).  Every pin over such a `buf`
whose `size` the count gate admits, at most `Uaccess.rw_bytes_max`, and
whose descriptor is not a socket states Linux v6.18.46's answer, the
descriptor's, where qemu-user answers -EFAULT; above that bound the gate
declines first (`recvfrom_big_count_unwritable_declines`,
`recvfrom_count_past_the_clamp_declines`), which is what keeps those
shapes sound.  The inherited answer is
named at a page `wmem` maps by `recvfrom_write_only_buffer_efault_rejected`,
and `recvfrom_rw_in` is the shape the lock passes. -/
def recvfrom_in (fd buf size flags : word) (wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 207 [fd, buf, size, flags, 0, 0] (fun _ => none) wmem

/-- `recvfrom(fd, buf, size, flags, NULL, NULL)` with `mem` as BOTH the
readable and the writable view: a destination qemu-user can lock for
writing, since its `VERIFY_WRITE` is `PAGE_READ | PAGE_WRITE`
(linux-user/qemu.h:185, QEMU 11.1.1) and `page_check_range` refuses a
page without `PAGE_READ` (accel/tcg/user-exec.c:538-541, QEMU 11.1.1) and
one the guest cannot write, without `PAGE_WRITE_ORG` (:543-547), wherever
it examines the page (`recvfrom_spec` names the one it can skip); a
readable, writable page QEMU write-protected for translated code it
unprotects and accepts (:548-559).  The arm reads neither view. -/
def recvfrom_rw_in (fd buf size flags : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 207 [fd, buf, size, flags, 0, 0] mem mem

/-- `recvmsg(fd, msgp, flags)`; nothing readable or writable, since the
arm never reads the header. -/
def recvmsg_in (fd msgp flags : word) : SyscallInput :=
  SyscallInput.mkInput 212 [fd, msgp, flags, 0, 0, 0] (fun _ => none) (fun _ => none)

attribute [sys_simp low] sendto_in.eq_1 sendmsg_in.eq_1 recvfrom_in.eq_1 recvfrom_rw_in.eq_1
  recvmsg_in.eq_1

/-- A `struct user_msghdr` as the 56 bytes `copy_msghdr_from_user` copies
(include/linux/socket.h:83-91, v6.18.46): `msg_name`, `msg_namelen`,
`msg_iov` (fixed at 8320), `msg_iovlen`, `msg_control`, `msg_controllen`,
`msg_flags`, each an eight-byte little-endian slot, the two 4-byte fields
in the low half of theirs. -/
def msghdr_bytes (name namelen iovlen ctl ctllen sflags : word) : List byte :=
  word_le8 name ++ word_le8 namelen ++ word_le8 8320 ++ word_le8 iovlen
    ++ word_le8 ctl ++ word_le8 ctllen ++ word_le8 sflags

/-- Rocq's `send_msghdr_mem`, with every field a parameter: "ab" at 4096,
the header at 8192, and the descriptor array `iovs` at 8320, each entry
`iov_base` then `iov_len` (include/uapi/linux/uio.h `struct iovec`,
v6.18.46).  Nothing else is readable.  The guards keep a lookup past each
block a closed `none`, for the reason `Checks/Cases/Fs/ReadWrite.lean`'s
`mem_readv_iov` gives. -/
def send_msghdr_mem (name namelen iovlen ctl ctllen sflags : word)
    (iovs : List (word × word)) : word → Option byte :=
  fun a =>
    if bv_ltu a 8192 then mem_ab a
    else if bv_ltu a 8248 then bytes_at 8192 (msghdr_bytes name namelen iovlen ctl ctllen sflags) a
    else if bv_ltu a 8320 then none
    else if bv_ltu a (Z_to_bv 64 (8320 + 16 * (iovs.length : Int)))
    then bytes_at 8320 (iovs.flatMap fun bl => word_le8 bl.1 ++ word_le8 bl.2) a
    else none

/-- The ordinary gather: one descriptor naming "ab". -/
def msg_ab : word → Option byte := send_msghdr_mem 0 0 1 0 0 0 [(4096, 2)]
/-- …with MSG_NOSIGNAL in the header's own `msg_flags`. -/
def msg_ab_field_nosignal : word → Option byte := send_msghdr_mem 0 0 1 0 0 16384 [(4096, 2)]
/-- …with MSG_DONTWAIT (64) in `msg_flags`. -/
def msg_ab_field_dontwait : word → Option byte := send_msghdr_mem 0 0 1 0 0 64 [(4096, 2)]
/-- …with a destination address at 4096, sixteen bytes long. -/
def msg_named : word → Option byte := send_msghdr_mem 4096 16 1 0 0 0 [(4096, 2)]
/-- …with no address and a NEGATIVE `msg_namelen` (the `int` -1). -/
def msg_negnamelen : word → Option byte := send_msghdr_mem 0 4294967295 1 0 0 0 [(4096, 2)]
/-- …with `msg_iovlen` one past `UIO_MAXIOV`. -/
def msg_iovlen_1025 : word → Option byte := send_msghdr_mem 0 0 1025 0 0 0 [(4096, 2)]
/-- …and a sixteen-byte control block beside it. -/
def msg_iovlen_1025_ctl : word → Option byte := send_msghdr_mem 0 0 1025 8400 16 0 [(4096, 2)]
/-- …with no control block and a non-NULL `msg_name` the guest cannot
read, sixteen bytes at 65536, beside `msg_iovlen` 1025. -/
def msg_badname_1025 : word → Option byte := send_msghdr_mem 65536 16 1025 0 0 0 [(4096, 2)]
/-- …with a non-NULL `msg_name`, a NEGATIVE `msg_namelen` (the `int` -1)
and `msg_iovlen` 1025. -/
def msg_negname_1025 : word → Option byte := send_msghdr_mem 4096 4294967295 1025 0 0 0 [(4096, 2)]
/-- …with `msg_iovlen` 9, one past `UIO_FASTIOV`, and all nine one-byte
descriptors readable, as the probe's `msgiovgap` hands them: the band's
decline is then the only thing between the import and the dead socket's
-EPIPE. -/
def msg_iovlen_9 : word → Option byte :=
  send_msghdr_mem 0 0 9 0 0 0
    [(4096, 1), (4096, 1), (4096, 1), (4096, 1), (4096, 1), (4096, 1), (4096, 1), (4096, 1),
     (4096, 1)]
/-- …with the full 64-bit `msg_iovlen` `2^32 + 1`, whose low half is 1. -/
def msg_iovlen_wide : word → Option byte := send_msghdr_mem 0 0 4294967297 0 0 0 [(4096, 2)]
/-- …with a sixteen-byte control block. -/
def msg_ctl : word → Option byte := send_msghdr_mem 0 0 1 8400 16 0 [(4096, 2)]
/-- …with a control POINTER and a zero control length. -/
def msg_ctlptr : word → Option byte := send_msghdr_mem 0 0 1 8400 0 0 [(4096, 2)]
/-- …with a descriptor naming a kernel address. -/
def msg_kbase : word → Option byte := send_msghdr_mem 0 0 1 0 0 0 [(Z_to_bv 64 (2 ^ 63), 1)]
/-- …the same address under a ZERO length. -/
def msg_kbase_zero : word → Option byte := send_msghdr_mem 0 0 1 0 0 0 [(Z_to_bv 64 (2 ^ 63), 0)]
/-- …a good first descriptor, then one naming a kernel address. -/
def msg_kbase_second : word → Option byte :=
  send_msghdr_mem 0 0 2 0 0 0 [(4096, 1), (Z_to_bv 64 (2 ^ 63), 1)]
/-- …a kernel address FIRST of two, then a good descriptor. -/
def msg_kbase_first_of_two : word → Option byte :=
  send_msghdr_mem 0 0 2 0 0 0 [(Z_to_bv 64 (2 ^ 63), 1), (4096, 1)]
/-- …a zero-length kernel address first of two, then a good descriptor. -/
def msg_kbase_zero_first_of_two : word → Option byte :=
  send_msghdr_mem 0 0 2 0 0 0 [(Z_to_bv 64 (2 ^ 63), 0), (4096, 1)]
/-- …with a descriptor whose length is negative as an `ssize_t`. -/
def msg_neglen : word → Option byte := send_msghdr_mem 0 0 1 0 0 0 [(4096, Z_to_bv 64 (2 ^ 63))]
/-- …with two one-byte descriptors, the multi-entry import path. -/
def msg_two : word → Option byte := send_msghdr_mem 0 0 2 0 0 0 [(4096, 1), (4097, 1)]
/-- …with no descriptors at all. -/
def msg_none : word → Option byte := send_msghdr_mem 0 0 0 0 0 0 []
/-- …with one descriptor one byte past `Uaccess.rw_bytes_max`. -/
def msg_big : word → Option byte := send_msghdr_mem 0 0 1 0 0 0 [(4096, 131073)]
/-- …with one descriptor `(16384, 131072)`, exactly `Uaccess.rw_bytes_max`,
and every byte from 16384 on readable, so the whole descriptor is mapped
and the gathered total is exactly the bound. -/
def msg_at_max : word → Option byte :=
  fun a =>
    if bv_ltu a 16384 then send_msghdr_mem 0 0 1 0 0 0 [(16384, 131072)] a
    else some 0

/-- …with `msg_iovlen` exactly `UIO_MAXIOV`. -/
def msg_iovlen_1024 : word → Option byte := send_msghdr_mem 0 0 1024 0 0 0 [(4096, 2)]
/-- …with eight one-byte descriptors, exactly `UIO_FASTIOV`. -/
def msg_eight : word → Option byte :=
  send_msghdr_mem 0 0 8 0 0 0
    [(4096, 1), (4096, 1), (4096, 1), (4096, 1), (4096, 1), (4096, 1), (4096, 1), (4096, 1)]
/-- …a descriptor naming a kernel address, beside a sixteen-byte control
block. -/
def msg_kbase_ctl : word → Option byte :=
  send_msghdr_mem 0 0 1 8400 16 0 [(Z_to_bv 64 (2 ^ 63), 1)]
/-- …a negative `iov_len`, beside a sixteen-byte control block. -/
def msg_neglen_ctl : word → Option byte :=
  send_msghdr_mem 0 0 1 8400 16 0 [(4096, Z_to_bv 64 (2 ^ 63))]
/-- …a descriptor naming a kernel address under a length one byte past
`Uaccess.rw_bytes_max`. -/
def msg_kbase_big : word → Option byte :=
  send_msghdr_mem 0 0 1 0 0 0 [(Z_to_bv 64 (2 ^ 63), 131073)]
/-- …a negative `iov_len` whose base is a kernel address too. -/
def msg_kbase_neglen : word → Option byte :=
  send_msghdr_mem 0 0 1 0 0 0 [(Z_to_bv 64 (2 ^ 63), Z_to_bv 64 (2 ^ 63))]
/-- …two descriptors, the first `(4096, 2^47)`: its UNCAPPED end is past
`TASK_SIZE`, while the `MAX_RW_COUNT` it would be capped to ends in range. -/
def msg_long_head : word → Option byte :=
  send_msghdr_mem 0 0 2 0 0 0 [(4096, Z_to_bv 64 (2 ^ 47)), (4096, 1)]

/-- A header naming `iovlen` descriptors at `iov`, with nothing readable
past it: the fixture for the ARRAY's own faults, which `msghdr_bytes`
cannot express because it fixes `msg_iov` at 8320. -/
def msghdr_iov_bytes (iov iovlen : word) : List byte :=
  word_le8 0 ++ word_le8 0 ++ word_le8 iov ++ word_le8 iovlen
    ++ word_le8 0 ++ word_le8 0 ++ word_le8 0

/-- "ab" at 4096 and the header at 8192, naming the array at `iov`. -/
def msg_array_at (iov iovlen : word) : word → Option byte :=
  fun a =>
    if bv_ltu a 8192 then mem_ab a
    else if bv_ltu a 8248 then bytes_at 8192 (msghdr_iov_bytes iov iovlen) a
    else none

/-- …with one descriptor named at 12288, the page after the header's, and
nothing mapped there: an unreadable array on a page of its own, which is
the shape real memory can have. -/
def msg_noarray : word → Option byte := msg_array_at 12288 1

/-- The header naming one descriptor at `2^47 - 8`, straddling `TASK_SIZE`,
with every byte past the header readable as zero, so the entry would read
as `(0, 0)`: only a range test on the whole sixteen bytes separates the
-EFAULT from a decline.  The readable bytes past `TASK_SIZE` lie outside
the run's premise (no guest page there); the fixture is about the spec's
own range test, as `rmem_open`'s pins are. -/
def msg_straddle_readable : word → Option byte :=
  fun a =>
    if bv_ltu a 8192 then mem_ab a
    else if bv_ltu a 8248 then bytes_at 8192 (msghdr_iov_bytes (Z_to_bv 64 (2 ^ 47 - 8)) 1) a
    else some 0

/-- The header naming TWO descriptors at `2^47 - 16`, so the array's last
sixteen bytes are past `TASK_SIZE`, with every byte past the header
readable as zero: both entries read as `(0, 0)` wherever the walk reaches
them.  The bytes
past `TASK_SIZE` are outside the run's premise, as
`msg_straddle_readable`'s are. -/
def msg_straddle_readable_two : word → Option byte :=
  fun a =>
    if bv_ltu a 8192 then mem_ab a
    else if bv_ltu a 8248 then bytes_at 8192 (msghdr_iov_bytes (Z_to_bv 64 (2 ^ 47 - 16)) 2) a
    else some 0

/-- The header naming TWO descriptors at `2^47 - 16`, the first — the last
sixteen bytes below `TASK_SIZE` — readable as `(4096, 2^63)`, a negative
`iov_len`, and nothing past `TASK_SIZE` readable: the array straddles the
edge, and its first entry is the -EINVAL a walk without the array's range
test reaches. -/
def msg_neglen_straddle : word → Option byte :=
  fun a =>
    if bv_ltu a 8192 then mem_ab a
    else if bv_ltu a 8248 then bytes_at 8192 (msghdr_iov_bytes (Z_to_bv 64 (2 ^ 47 - 16)) 2) a
    else if bv_ltu a (Z_to_bv 64 (2 ^ 47 - 16)) then none
    else if bv_ltu a (Z_to_bv 64 (2 ^ 47)) then
      bytes_at (Z_to_bv 64 (2 ^ 47 - 16)) (word_le8 4096 ++ word_le8 (Z_to_bv 64 (2 ^ 63))) a
    else none

/-- Every byte readable, as zeros: a header read from ANY address succeeds
wherever the range test lets it. -/
def rmem_open : word → Option byte := fun _ => some 0

/-! ### The flag word, first -/

/-- A FLAGLESS SEND IS DECLINED on a socket that would answer -EPIPE: the
gate runs before the fd, the buffer and the state (`send_flags_modeled`).
kernel: net/core/stream.c:sk_stream_error@v6.18.46 -/
theorem sendto_flagless_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 0 0 0 mem_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -EPIPE the socket would give is not admitted there: without
MSG_NOSIGNAL it comes with SIGPIPE, which the model does not deliver.
kernel: net/core/stream.c:sk_stream_error@v6.18.46 -/
theorem sendto_flagless_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 0 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- MSG_NOSIGNAL|MSG_DONTWAIT is declined too: the word must be EXACTLY
MSG_NOSIGNAL.
probe: testing/syscall-check/tests/send_spec.c#fail-closed -- dontwait -/
theorem sendto_dontwait_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 16448 0 0 mem_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the kernel's own answer there, -EPIPE, is not admitted either.
probe: testing/syscall-check/tests/send_spec.c#fail-closed -- dontwait -/
theorem sendto_dontwait_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16448 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- THE HIGH HALF IS DROPPED: `flags` is `unsigned int` in
`SYSCALL_DEFINE6(sendto)`, so `2^32 + MSG_NOSIGNAL` is modeled and the fresh
socket answers -EPIPE.
probe: testing/syscall-check/tests/send_spec.c#conform -- hiflags -/
theorem sendto_high_flag_half_is_dropped (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 (Z_to_bv 64 (2 ^ 32 + 16384)) 0 0 mem_ab)
        fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model [] := by
  sys_norm

/-- …with -EPIPE the only answer.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#1:ret=-EAGAIN -- hiflags -/
theorem sendto_high_flag_half_eagain_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 (Z_to_bv 64 (2 ^ 32 + 16384)) 0 0 mem_ab)
        fresh_socket_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- …and not a decline, which a gate reading all 64 bits would give.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_high_flag_half_unmodeled_rejected :
    ¬ syscall_spec (sendto_in 3 4096 1 (Z_to_bv 64 (2 ^ 32 + 16384)) 0 0 mem_ab)
        fresh_socket_model Unmodeled := by
  sys_refute

/-- THE GATE RUNS BEFORE THE FD: a flagless send on a CLOSED fd declines,
where Linux answers -EBADF without a signal, and so does qemu-user, whose
lock of the readable "ab" passes — the cost the spec's send section names
for keeping Rocq's order.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_closed_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 4096 1 0 0 0 mem_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the -EBADF a gate placed after the fd would give is refused.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_closed_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 4096 1 0 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and over a buffer qemu-user cannot lock, the same place KEEPS THE SPEC
SOUND: `sendto(9, 0x10000, 1, 0)` on the closed 9.  Linux's `import_ubuf`
passes the in-range buffer (lib/iov_iter.c:1433-1442, v6.18.46) and the
closed fd answers -EBADF (net/socket.c:2222-2224), but qemu-user's
`do_sendto` locks the unreadable byte before the host call
(linux-user/syscall.c:3648-3652, QEMU 11.1.1) and answers -EFAULT.  It
declines, admitting both…
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_unreadable_closed_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 65536 1 0 0 0 mem_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the -EBADF a flag gate after the fd would prove as certain is
refused: it is not qemu-user's answer.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_unreadable_closed_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 65536 1 0 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and on an open non-socket, stdout here, over the same buffer, the
place keeps the spec sound as well: `sendto(1, 0x10000, 1, 0)`.  Linux's
`import_ubuf` passes the in-range buffer and `sock_from_file` refuses the
channel with -ENOTSOCK (net/socket.c:2225-2227, v6.18.46), but qemu-user's
`do_sendto` locks the unreadable byte first (linux-user/syscall.c:3648-3652,
QEMU 11.1.1) and answers -EFAULT.  It declines…
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto,sock_from_file@v6.18.46 -/
theorem sendto_flagless_unreadable_channel_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 1 65536 1 0 0 0 mem_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the -ENOTSOCK a flag gate after the fd would prove as certain is
refused: it is not qemu-user's answer.
kernel: net/socket.c:__sys_sendto,sock_from_file@v6.18.46 -/
theorem sendto_flagless_unreadable_channel_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 1 65536 1 0 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …AND BEFORE THE BUFFER: a flagless send from a kernel-half buffer on
the same closed fd declines too.  Linux answers -EFAULT there, since
`import_ubuf` runs before any flag is looked at (net/socket.c:2218-2220,
v6.18.46), and so does qemu-user, whose `do_sendto` locks the buffer
before the host call (linux-user/syscall.c:3648-3652, QEMU 11.1.1): the
decline gives up that answer, the -EFAULT half of the cost the spec's send
section names.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_kernel_buffer_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 0 0 0 mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so the -EFAULT a gate placed after the range test would give is not
the spec's answer.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_kernel_buffer_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 0 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …while at LENGTH 0 the flag gate's place before the range test keeps
the spec sound: `sendto(9, 2^63, 0, 0)` is -EFAULT under Linux, whose
`access_ok` refuses `2^63` at length 0 (`import_ubuf`, lib/iov_iter.c:1437,
v6.18.46), but qemu-user's `do_sendto` never locks a zero length
(linux-user/syscall.c:3648, QEMU 11.1.1) and answers what the host's
sendto answers on the closed 9, -EBADF.  It declines…
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_zero_length_kernel_buffer_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 0 0 0 0 mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so Linux's -EFAULT, which a flag gate after the range test would
prove as certain, is refused: it is not qemu-user's answer.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_zero_length_kernel_buffer_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 0 0 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …and at a NEGATIVE `addrlen` too: `sendto(3, 4096, 1, 0, NULL,
0xffffffff)` on the fresh socket is -EPIPE with SIGPIPE under Linux, whose
`__sys_sendto` reads `addr_len` only under a non-NULL `addr`
(net/socket.c:2234-2240, v6.18.46), so the unconnected socket's
`sk_stream_wait_connect` answers -EPIPE (net/core/stream.c:70-71,
v6.18.46) and `sk_stream_error` raises SIGPIPE (:190-197); qemu-user's
`do_sendto` tests `(int)addrlen < 0` first and answers -EINVAL
(linux-user/syscall.c:3644-3646, QEMU 11.1.1).  It declines…
kernel: net/socket.c:__sys_sendto; net/core/stream.c:sk_stream_error@v6.18.46 -/
theorem sendto_flagless_negative_addrlen_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 0 0 (Z_to_bv 64 (2 ^ 32 - 1)) mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so qemu-user's -EINVAL, which a flag gate answering it rather than
declining would prove as certain, is refused: it is not Linux's answer.  A
sign test ahead of the gate, which proves it at every flag word, is
refused by `sendto_negative_addrlen_einval_rejected` as well; one inside
the gate's decline, at the flagless call alone, by this pair and by the
`iff`s at the channel 1 and the closed 9
(`sendto_flagless_negative_addrlen_channel_fd_declines`,
`sendto_flagless_negative_addrlen_closed_fd_declines`).
kernel: net/socket.c:__sys_sendto; net/core/stream.c:sk_stream_error@v6.18.46 -/
theorem sendto_flagless_negative_addrlen_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 0 0 (Z_to_bv 64 (2 ^ 32 - 1)) mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and beside a readable buffer on the closed 9, a non-NULL `addr` the
guest cannot read declines as well: Linux answers -EBADF, resolving the fd
(net/socket.c:2222-2224, v6.18.46) before `move_addr_to_kernel` reads
`addr` (:2234-2240), and qemu-user answers -EFAULT, locking `addr` for
`addrlen` bytes before the host call (`target_to_host_sockaddr`,
linux-user/syscall.c:1687-1689, via :3665, QEMU 11.1.1).  It declines…
kernel: net/socket.c:__sys_sendto,move_addr_to_kernel@v6.18.46 -/
theorem sendto_flagless_unreadable_addr_closed_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 4096 1 0 65536 16 mem_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so Linux's -EBADF, which a spec resolving the fd before both the flag
gate and the address gate would prove as certain, is refused: it is not
qemu-user's answer.  Such a spec is refused by
`sendto_flagless_closed_fd_ebadf_rejected` as well, and one moving only
the address gate after the fd by `sendto_address_closed_fd_ebadf_rejected`.
A flag gate that, at a flagless call with a non-NULL `addr`, resolves the
fd rather than declining is refused by this pair and by the channel pair
(`sendto_flagless_unreadable_addr_channel_fd_declines`,
`sendto_flagless_unreadable_addr_channel_fd_enotsock_rejected`); one
resolving only a closed fd there by this pair alone, and one resolving
only a non-socket fd by the channel pair alone.
kernel: net/socket.c:__sys_sendto,move_addr_to_kernel@v6.18.46 -/
theorem sendto_flagless_unreadable_addr_closed_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 4096 1 0 65536 16 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The same input on the channel 1 declines too: Linux answers -ENOTSOCK,
`sock_from_file` refusing the fd (net/socket.c:2225-2227, v6.18.46) before
`move_addr_to_kernel` reads `addr` (:2234-2240), and qemu-user answers
-EFAULT, as on the closed 9.  It declines…
kernel: net/socket.c:__sys_sendto,sock_from_file,move_addr_to_kernel@v6.18.46 -/
theorem sendto_flagless_unreadable_addr_channel_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 1 4096 1 0 65536 16 mem_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so Linux's -ENOTSOCK, which a flag gate resolving the fd at a
flagless call with a non-NULL `addr` would prove as certain, is refused:
it is not qemu-user's answer.
kernel: net/socket.c:__sys_sendto,sock_from_file,move_addr_to_kernel@v6.18.46 -/
theorem sendto_flagless_unreadable_addr_channel_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 1 4096 1 0 65536 16 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- A NULL `addr` with a NEGATIVE `addrlen` declines off a socket too.  On
the channel 1 Linux answers -ENOTSOCK, reading `addr_len` only under a
non-NULL `addr` (net/socket.c:2234-2240, v6.18.46), and qemu-user answers
-EINVAL, testing `(int)addrlen < 0` first (linux-user/syscall.c:3644-3646,
QEMU 11.1.1).  It declines…
kernel: net/socket.c:__sys_sendto,sock_from_file@v6.18.46 -/
theorem sendto_flagless_negative_addrlen_channel_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 1 4096 1 0 0 (Z_to_bv 64 (2 ^ 32 - 1)) mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so Linux's -ENOTSOCK is refused: it is not qemu-user's answer.
kernel: net/socket.c:__sys_sendto,sock_from_file@v6.18.46 -/
theorem sendto_flagless_negative_addrlen_channel_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 1 4096 1 0 0 (Z_to_bv 64 (2 ^ 32 - 1)) mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …and on the closed 9, where Linux answers -EBADF (net/socket.c:2222-2224,
v6.18.46) and qemu-user -EINVAL as on the channel.  It declines…
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_negative_addrlen_closed_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 4096 1 0 0 (Z_to_bv 64 (2 ^ 32 - 1)) mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so Linux's -EBADF is refused: it is not qemu-user's answer.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_negative_addrlen_closed_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 4096 1 0 0 (Z_to_bv 64 (2 ^ 32 - 1)) mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- A ZERO-LENGTH buffer at `2^63` declines on the channel 1 as on the
closed 9: Linux answers -EFAULT, its `access_ok` refusing `2^63` at length 0
(`import_ubuf`, lib/iov_iter.c:1437, v6.18.46), and qemu-user hands the host
a NULL buffer at length 0, locking nothing (linux-user/syscall.c:3648, :3671,
QEMU 11.1.1), so the host's sendto answers on the channel, -ENOTSOCK.  It
declines…
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_zero_length_kernel_buffer_channel_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 1 (Z_to_bv 64 (2 ^ 63)) 0 0 0 0 mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so Linux's -EFAULT is refused: it is not qemu-user's answer.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_flagless_zero_length_kernel_buffer_channel_fd_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 1 (Z_to_bv 64 (2 ^ 63)) 0 0 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- The same on sendmsg: a flagless call on a closed fd declines…
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_flagless_closed_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 9 8192 0 msg_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …not the fd's -EBADF.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_flagless_closed_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 9 8192 0 msg_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and over a header qemu-user cannot lock, the place KEEPS THE SPEC
SOUND: `sendmsg(9, 0x10000, 0)` on the closed 9 is -EBADF under Linux,
whose `__sys_sendmsg` resolves the fd before the header is copied
(net/socket.c:2709-2712, v6.18.46), and -EFAULT under qemu-user, whose
`do_sendrecvmsg` locks the unreadable header first
(linux-user/syscall.c:3445-3450, QEMU 11.1.1).  It declines…
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_flagless_unreadable_closed_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 9 65536 0 mem_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the -EBADF a flag gate after the fd would prove as certain is
refused: it is not qemu-user's answer.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_flagless_unreadable_closed_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 9 65536 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and on an open non-socket, stdout here, it declines too…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_flagless_channel_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 1 8192 0 msg_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …not the descriptor's -ENOTSOCK.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_flagless_channel_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 1 8192 0 msg_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …and on stdout over a header qemu-user cannot lock, the place KEEPS
THE SPEC SOUND: `sendmsg(1, 0x10000, 0)` is -ENOTSOCK under Linux
(net/socket.c:2713-2715, v6.18.46) and -EFAULT under qemu-user
(linux-user/syscall.c:3445-3450, QEMU 11.1.1).  It declines…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_flagless_unreadable_channel_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 1 65536 0 mem_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the -ENOTSOCK a flag gate after the fd would prove as certain is
refused: it is not qemu-user's answer.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_flagless_unreadable_channel_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 1 65536 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- THE WORD IS EXACT OVER ALL 32 BITS, not the low sixteen:
MSG_CMSG_COMPAT beside MSG_NOSIGNAL (`0x80004000`) on a closed fd
declines.  With CONFIG_COMPAT, riscv64's default
(arch/riscv/Kconfig:1083-1086, v6.18.46), `__sys_sendmsg` answers -EINVAL
before the fd (net/socket.c:2706-2707, v6.18.46); without it the bit is 0
(include/linux/socket.h:337-341, v6.18.46) and the answer is -EBADF.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 9 8192 (Z_to_bv 64 2147500032) msg_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so the -EBADF a gate comparing the low sixteen bits would give is
refused: it is not every kernel's answer.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 9 8192 (Z_to_bv 64 2147500032) msg_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and on the channel 1 too, where Linux with CONFIG_COMPAT answers
-EINVAL before the fd (net/socket.c:2706-2707, v6.18.46) and without it
-ENOTSOCK, `sock_from_file` refusing stdout (:2713-2715).  It declines…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_channel_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 1 8192 (Z_to_bv 64 2147500032) msg_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so the -ENOTSOCK of a kernel built without CONFIG_COMPAT, which a flag
gate after the non-socket arms would prove as certain, is refused: it is
not every kernel's answer.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_channel_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 1 8192 (Z_to_bv 64 2147500032) msg_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …and so is CONFIG_COMPAT's -EINVAL, which is not every kernel's either.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_channel_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 1 8192 (Z_to_bv 64 2147500032) msg_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and on the write-only file at 4 of `socket_call_model`, where Linux
without CONFIG_COMPAT answers -ENOTSOCK, `sock_from_file` refusing a
regular file (net/socket.c:2713-2715, v6.18.46), and with it -EINVAL
before the fd (:2706-2707).  It declines…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_file_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 4 8192 (Z_to_bv 64 2147500032) msg_ab) socket_call_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so that -ENOTSOCK, which a flag gate after the file arms would prove
as certain, is refused: it is not every kernel's answer.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_file_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 4 8192 (Z_to_bv 64 2147500032) msg_ab) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …and on the read-only file at 3 of `socket_call_model`, for the same
reason: -EINVAL with CONFIG_COMPAT (net/socket.c:2706-2707, v6.18.46),
-ENOTSOCK without it (:2713-2715).  It declines…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_read_only_file_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 (Z_to_bv 64 2147500032) msg_ab) socket_call_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so that -ENOTSOCK is refused there too.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_read_only_file_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 (Z_to_bv 64 2147500032) msg_ab) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …and on the directory at 5 of `socket_call_model`, where
`sock_from_file` refuses a directory as it does a file (net/socket.c:2713-2715,
v6.18.46).  It declines…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_dir_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 5 8192 (Z_to_bv 64 2147500032) msg_ab) socket_call_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so that -ENOTSOCK is refused.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_dir_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 5 8192 (Z_to_bv 64 2147500032) msg_ab) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …and on the pipe's read end at 6 of `socket_kinds_model`, which
`sock_from_file` refuses the same way (net/socket.c:2713-2715,
v6.18.46).  It declines…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_pipe_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 6 8192 (Z_to_bv 64 2147500032) msg_ab) socket_kinds_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so that -ENOTSOCK is refused.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_pipe_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 6 8192 (Z_to_bv 64 2147500032) msg_ab) socket_kinds_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …and on the fresh socket at 3 of `fresh_socket_model`, where Linux
with CONFIG_COMPAT answers -EINVAL before the fd (net/socket.c:2706-2707,
v6.18.46), while without it the bit is 0 (include/linux/socket.h:337-341,
v6.18.46), every `MSG_CMSG_COMPAT & flags` test in net/socket.c is false,
and the call is `sendmsg(3, 8192, MSG_NOSIGNAL)` with bit 31 carried
along: the unconnected socket's -EPIPE, header and descriptor ledgered
(`sk_stream_wait_connect`, net/core/stream.c, v6.18.46).  It declines…
kernel: net/socket.c:__sys_sendmsg; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_socket_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 (Z_to_bv 64 2147500032) msg_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so that -EPIPE, which a flag gate treating bit 31 as inert would
prove as certain, is refused: it is not every kernel's answer.
kernel: net/socket.c:__sys_sendmsg; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_socket_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 (Z_to_bv 64 2147500032) msg_ab) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- MSG_FASTOPEN beside MSG_NOSIGNAL (`0x20004000`) on the fresh socket
declines: `tcp_sendmsg_locked` hands it to `tcp_sendmsg_fastopen`, which
answers -EOPNOTSUPP with client Fast Open disabled
(net/ipv4/tcp.c:1040-1044, v6.18.46), -ENOBUFS if its request cannot be
allocated, and otherwise connects to the NULL address, -EINVAL from
`tcp_v4_connect` (net/ipv4/tcp_ipv4.c:236-237, v6.18.46).
kernel: net/ipv4/tcp.c:tcp_sendmsg_fastopen; net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem sendto_fastopen_flag_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 (Z_to_bv 64 536887296) 0 0 mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …and the dead socket's -EPIPE, which a low-sixteen-bit gate would
answer, is refused: neither Fast Open answer is -EPIPE.
kernel: net/ipv4/tcp.c:tcp_sendmsg_fastopen; net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem sendto_fastopen_flag_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 (Z_to_bv 64 536887296) 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-! ### The two other gates -/

/-- A DESTINATION ADDRESS DECLINES: validated by `move_addr_to_kernel` and
then ignored by TCP, so two errnos for a value nothing reads.
probe: testing/syscall-check/tests/send_spec.c#fail-closed -- addrgate -/
theorem sendto_address_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 16384 8192 16 mem_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the -EPIPE a spec ignoring the address would give is not
admitted in its place.  Linux itself answers -EFAULT here: 8192 is
unreadable in `mem_ab`, and once fd 3 has resolved to a socket
(net/socket.c:2222-2227, v6.18.46) `move_addr_to_kernel` copies the
address (:248-257, called at :2234-2240) before `__sock_sendmsg` (:2245)
could answer the dead socket's -EPIPE.
probe: testing/syscall-check/tests/send_spec.c#fail-closed -- addrgate -/
theorem sendto_address_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 8192 16 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- A count past `Uaccess.rw_bytes_max` declines, before the buffer and the fd.
probe: testing/syscall-check/tests/send_spec.c#fail-closed -- bigcount -/
theorem sendto_big_count_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 131073 16384 0 0 mem_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and its -EPIPE is not admitted.
probe: testing/syscall-check/tests/send_spec.c#fail-closed -- bigcount -/
theorem sendto_big_count_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 131073 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- BOTH GATES RUN BEFORE THE RANGE TEST.  An address beside a kernel-half
buffer on a closed fd declines, where Linux answers -EFAULT from
`import_ubuf` (lib/iov_iter.c:1433-1442, v6.18.46), called at
net/socket.c:2218-2220 before the fd or the address, and qemu-user
-EFAULT from its buffer lock
(linux-user/syscall.c:3648-3652, QEMU 11.1.1) before the address lock
(:3663-3668).  Both answers agree here, so at this input the address
gate's place costs an answer rather than keeping the spec sound; the
inputs where a gate's place does keep it sound follow: the count gate's at
a count past the clamp, the address gate's at a negative `addrlen`.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_address_kernel_buffer_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 16384 8192 16 mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so the -EFAULT an address gate after the range test would give is not
the spec's answer.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_address_kernel_buffer_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 16384 8192 16 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A count past `Uaccess.rw_bytes_max` beside the same kernel-half buffer
declines too, where Linux answers -EFAULT: `import_ubuf`'s cap to
`MAX_RW_COUNT` (lib/iov_iter.c:1435-1436, v6.18.46) leaves 131073 alone,
and its `access_ok` (:1437) refuses `2^63`.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_big_count_kernel_buffer_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 131073 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so the -EFAULT a count gate after the range test would give is not the
spec's answer.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_big_count_kernel_buffer_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 131073 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- THE COUNT GATE'S PLACE KEEPS THE SPEC SOUND.  `sendto(9, 0x10000,
2^47)` on the closed 9 ends past `TASK_SIZE` only at its full count:
`import_ubuf` caps the count to `MAX_RW_COUNT` (lib/iov_iter.c:1435-1436,
v6.18.46) before its range test (:1437), which then passes, so Linux
answers the closed fd's -EBADF (net/socket.c:2222-2224).  qemu-user's
`do_sendto` locks the whole uncapped length
(linux-user/syscall.c:3648-3652, QEMU 11.1.1) and answers -EFAULT unless
every page of it is mapped readable.  It declines.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_count_past_the_clamp_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 65536 (Z_to_bv 64 (2 ^ 47)) 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so the -EFAULT a range test over the uncapped count would prove as
certain is refused: it is qemu-user's answer, not Linux's.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_count_past_the_clamp_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 65536 (Z_to_bv 64 (2 ^ 47)) 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- THE ADDRESS GATE'S PLACE KEEPS IT SOUND AT A NEGATIVE `addrlen`.
`sendto(9, 2^63, 1, MSG_NOSIGNAL, 8192, -1)` is -EFAULT under Linux,
whose `import_ubuf` runs first (net/socket.c:2218-2220, v6.18.46): nothing
tests `addr_len` before it or the fd, and the first test is
`move_addr_to_kernel`'s `ulen < 0` (:248-257, called at :2234-2240, after
the fd).  qemu-user's `do_sendto` tests
`(int)addrlen < 0` before the buffer (linux-user/syscall.c:3644-3646,
QEMU 11.1.1) and answers -EINVAL.  It declines.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto,move_addr_to_kernel@v6.18.46 -/
theorem sendto_negative_addrlen_kernel_buffer_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 16384 8192 (Z_to_bv 64 (2 ^ 32 - 1)) mem_ab)
        fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so Linux's -EFAULT, which an address gate after the range test would
prove as certain, is not the spec's answer: qemu-user's -EINVAL is as real.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_negative_addrlen_kernel_buffer_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 16384 8192 (Z_to_bv 64 (2 ^ 32 - 1)) mem_ab)
        fresh_socket_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …AND BEFORE THE FD.  An address beside an in-range buffer on a closed
fd declines.  Here the place of the gate is what keeps the spec sound:
Linux answers -EBADF, the fd resolving (net/socket.c:2222-2224, v6.18.46)
before `move_addr_to_kernel` (:2234-2240), but qemu-user's `do_sendto`
hands the address to `target_to_host_sockaddr` (linux-user/syscall.c:3665,
QEMU 11.1.1), which locks it (:1687-1689) before the host call ever sees
the fd, and answers -EFAULT for the unreadable 8192.
kernel: net/socket.c:__sys_sendto,move_addr_to_kernel@v6.18.46 -/
theorem sendto_address_closed_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 4096 1 16384 8192 16 mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so the -EBADF an address gate after the fd would prove as certain is
refused: it is not qemu-user's answer.
kernel: net/socket.c:__sys_sendto,move_addr_to_kernel@v6.18.46 -/
theorem sendto_address_closed_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 4096 1 16384 8192 16 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and on the channel 1, where Linux answers -ENOTSOCK, `sock_from_file`
refusing the fd (net/socket.c:2225-2227, v6.18.46) before
`move_addr_to_kernel` (:2234-2240), and qemu-user -EFAULT as on the closed 9.
It declines…
kernel: net/socket.c:__sys_sendto,sock_from_file,move_addr_to_kernel@v6.18.46 -/
theorem sendto_address_channel_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 1 4096 1 16384 8192 16 mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so Linux's -ENOTSOCK, which an address gate after the fd would prove
as certain, is refused: it is not qemu-user's answer.
kernel: net/socket.c:__sys_sendto,sock_from_file,move_addr_to_kernel@v6.18.46 -/
theorem sendto_address_channel_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 1 4096 1 16384 8192 16 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- THE COUNT GATE'S PLACE BEFORE THE FD KEEPS THE SPEC SOUND too.  A count
past `Uaccess.rw_bytes_max` beside an in-range buffer on a closed fd
declines, where Linux answers -EBADF (net/socket.c:2222-2224, v6.18.46).
The bound is the model's, not a kernel one, but its place is what admits
qemu-user's answer here: `do_sendto` locks all 131073 bytes before the
host call (linux-user/syscall.c:3648-3652, QEMU 11.1.1), and only "ab" at
4096 is readable, so it answers -EFAULT.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_big_count_closed_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 4096 131073 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so the -EBADF a count gate after the fd would give is not the spec's
answer.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_big_count_closed_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 4096 131073 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and on the channel 1, where Linux answers -ENOTSOCK, `sock_from_file`
refusing stdout (net/socket.c:2225-2227, v6.18.46), and qemu-user -EFAULT
as on the closed 9.  It declines…
kernel: net/socket.c:__sys_sendto,sock_from_file@v6.18.46 -/
theorem sendto_big_count_channel_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 1 4096 131073 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so the -ENOTSOCK a count gate after the non-socket arms would give is
not the spec's answer.
kernel: net/socket.c:__sys_sendto,sock_from_file@v6.18.46 -/
theorem sendto_big_count_channel_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 1 4096 131073 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- The bound itself is modeled: `rw_bytes_max` bytes on the fresh socket
are its -EPIPE.  Every byte is readable (`rmem_open`), so the whole count
is mapped, and `access_ok` passes the range before the fd is resolved.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_count_at_the_bound_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 131072 16384 0 0 rmem_open) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model [] := by
  sys_norm


/-- …not a decline.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_count_at_the_bound_unmodeled_rejected :
    ¬ syscall_spec (sendto_in 3 4096 131072 16384 0 0 rmem_open) fresh_socket_model Unmodeled := by
  simp only [sendto_count_at_the_bound_is_epipe, reduceCtorEq, not_false_eq_true]

/-! ### The buffer before the fd -/

/-- THE RANGE VERDICT PRECEDES THE FD: `import_ubuf`'s `access_ok` runs
before `CLASS(fd, f)`, so a closed fd with a kernel-half buffer is -EFAULT.
probe: testing/syscall-check/tests/send_spec.c#conform -- hibuf -/
theorem sendto_high_buffer_beats_the_fd (o : outcome SyscallEffect) :
    syscall_spec (sendto_in (Z_to_bv 64 (-1)) (Z_to_bv 64 (2 ^ 63)) 1 16384 0 0 mem_ab)
        fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] := by
  sys_norm

/-- …and -EBADF there is the wrong order.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#1:ret=-EBADF -- hibuf -/
theorem sendto_high_buffer_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in (Z_to_bv 64 (-1)) (Z_to_bv 64 (2 ^ 63)) 1 16384 0 0 mem_ab)
        fresh_socket_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- At the edge: `2^47 - 7` with length 8 ends one byte past `TASK_SIZE`.
probe: testing/syscall-check/tests/send_spec.c#conform -- edgebuf -/
theorem sendto_edge_buffer_beats_the_fd (o : outcome SyscallEffect) :
    syscall_spec (sendto_in (Z_to_bv 64 (-1)) (Z_to_bv 64 (2 ^ 47 - 7)) 8 16384 0 0 mem_ab)
        fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] := by
  sys_norm

/-- …with -EBADF refused there too.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#1:ret=-EBADF -- edgebuf -/
theorem sendto_edge_buffer_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in (Z_to_bv 64 (-1)) (Z_to_bv 64 (2 ^ 47 - 7)) 8 16384 0 0 mem_ab)
        fresh_socket_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- THE RANGE VERDICT WRAPS EVERY FD ANSWER, not only the closed one's: on
the fresh socket a kernel-half buffer is -EFAULT, before the fd resolves.
qemu-user agrees: `do_sendto` locks a nonzero buffer before the host call
(linux-user/syscall.c:3648-3652, QEMU 11.1.1).
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_high_buffer_on_a_socket_is_efault (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 (Z_to_bv 64 (2 ^ 63)) 1 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not the dead socket's -EPIPE.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_high_buffer_on_a_socket_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 (Z_to_bv 64 (2 ^ 63)) 1 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- …and on an open non-socket, stdout, the same -EFAULT…
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_high_buffer_on_a_channel_is_efault (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 1 (Z_to_bv 64 (2 ^ 63)) 1 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not its -ENOTSOCK.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_high_buffer_on_a_channel_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 1 (Z_to_bv 64 (2 ^ 63)) 1 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- A ZERO LENGTH IS JUDGED TOO: `import_ubuf` applies `access_ok`
whatever the length, and `2^63` is outside the user range, so the call is
-EFAULT before the closed 9 is reached.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_zero_length_high_buffer_is_efault (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 0 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not a decline: the range verdict covers the zero-length call as well.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_zero_length_high_buffer_unmodeled_rejected :
    ¬ syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 0 16384 0 0 mem_ab) fresh_socket_model
        Unmodeled := by
  sys_refute

/-- …and -EBADF is refused: the range test runs before the fd is
resolved, so the closed 9 never answers.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_zero_length_high_buffer_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 0 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- THE LAST RANGE `access_ok` ADMITS: seven bytes ending exactly at
`TASK_SIZE` pass the test, so the closed 9 answers -EBADF although
nothing is mapped there — `import_ubuf` reads no byte.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_buffer_below_the_edge_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 47 - 7)) 7 16384 0 0 mem_ab)
        fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_buffer_below_the_edge_unmodeled_rejected :
    ¬ syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 47 - 7)) 7 16384 0 0 mem_ab)
        fresh_socket_model Unmodeled := by
  sys_refute

/-- …and not the -EFAULT one byte more would give: at length 8 the range
ends past `TASK_SIZE` (`sendto_edge_buffer_beats_the_fd`).
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_buffer_below_the_edge_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 (Z_to_bv 64 (2 ^ 47 - 7)) 7 16384 0 0 mem_ab)
        fresh_socket_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- AN UNMAPPED BUT IN-RANGE BUFFER IS THE SOCKET'S ANSWER, NOT THE
BUFFER'S: 46912512909312 = 0x2AAAABAAE000 is the address the probe's
`page_before_hole() + 4096` resolved to, and it is below `TASK_SIZE`, so
`import_ubuf`'s `access_ok` passes it and reads no byte.  The fresh
socket has no connection, so `sk_stream_wait_connect` answers -EPIPE
with the ledger empty.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_unmapped_buffer_on_a_dead_socket_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 46912512909312 1 16384 0 0 (fun _ => none)) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not a decline: nothing between the flag word and the socket looks at
the buffer's contents.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_unmapped_buffer_on_a_dead_socket_unmodeled_rejected :
    ¬ syscall_spec (sendto_in 3 46912512909312 1 16384 0 0 (fun _ => none)) fresh_socket_model
        Unmodeled := by
  sys_refute

/-- …and -EFAULT, the answer of a copy Linux never makes here, is
refused: the state is decided before `tcp_sendmsg_locked` would copy.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_unmapped_buffer_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 46912512909312 1 16384 0 0 (fun _ => none)) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- The same buffer on the LISTENING socket is the same -EPIPE: a
listener has no connection either.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_unmapped_buffer_on_listening_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 46912512909312 1 16384 0 0 (fun _ => none)) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) listening_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_unmapped_buffer_on_listening_unmodeled_rejected :
    ¬ syscall_spec (sendto_in 3 46912512909312 1 16384 0 0 (fun _ => none)) listening_socket_model
        Unmodeled := by
  sys_refute

/-- …and not the copy's -EFAULT, for the reason
`sendto_unmapped_buffer_efault_rejected` gives.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_unmapped_buffer_on_listening_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 46912512909312 1 16384 0 0 (fun _ => none)) listening_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- `addrlen` CARRIES NO CONDITION WHEN `addr` IS NULL: `__sys_sendto`
reads it only inside `if (addr)`, so a negative one is the fresh socket's
-EPIPE, ledger empty.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_negative_addrlen_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 16384 0 (Z_to_bv 64 (-1)) mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not a decline: no gate reads `addrlen`.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_negative_addrlen_unmodeled_rejected :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 (Z_to_bv 64 (-1)) mem_ab) fresh_socket_model
        Unmodeled := by
  sys_refute

/-- …and its sign is not an -EINVAL.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_negative_addrlen_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 (Z_to_bv 64 (-1)) mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and beside a buffer whose eight bytes end past `TASK_SIZE` the
range test answers first: -EFAULT, and the `addrlen` is still unread.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_negative_addrlen_past_task_size_is_efault (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 (Z_to_bv 64 (2 ^ 47 - 4)) 8 16384 0 (Z_to_bv 64 (2 ^ 32 - 1)) mem_ab)
        fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_negative_addrlen_past_task_size_unmodeled_rejected :
    ¬ syscall_spec (sendto_in 3 (Z_to_bv 64 (2 ^ 47 - 4)) 8 16384 0 (Z_to_bv 64 (2 ^ 32 - 1)) mem_ab)
        fresh_socket_model Unmodeled := by
  sys_refute

/-- …and its sign is not an -EINVAL here either.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_negative_addrlen_past_task_size_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 (Z_to_bv 64 (2 ^ 47 - 4)) 8 16384 0 (Z_to_bv 64 (2 ^ 32 - 1)) mem_ab)
        fresh_socket_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ### The descriptor, and every state without a connection -/

/-- A NEVER-BOUND socket is -EPIPE, ledger empty: TCP does not autobind on
send, and `sk_stream_wait_connect` answers -EPIPE before its -EAGAIN.
probe: testing/syscall-check/tests/send_spec.c#conform -- dead -/
theorem sendto_fresh_socket_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model [] := by
  sys_norm

/-- …no autobind, so no -EAGAIN.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#1:ret=-EAGAIN -- dead -/
theorem sendto_fresh_socket_eagain_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- …no -ENOTCONN, which is read(2)'s answer on this socket and not send's.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#1:ret=-ENOTCONN -- dead -/
theorem sendto_fresh_socket_enotconn_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret ENOTCONN) [] []) m' evs) := by
  sys_refute

/-- …no pending peer error to consume.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#1:ret=-ECONNRESET -- dead -/
theorem sendto_fresh_socket_econnreset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret ECONNRESET) [] []) m' evs) := by
  sys_refute

/-- …and no byte sent, with or without its ledger.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#1:ret=1 -- dead -/
theorem sendto_fresh_socket_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU 1 [] [] [] [] [(4096, 1)]) m' evs) := by
  sys_refute

/-- …and the -EPIPE never carries the buffer in its ledger: `import_ubuf`
tests a range and copies nothing, and the state answers before
`tcp_sendmsg_locked`'s copy loop.
kernel: lib/iov_iter.c:import_ubuf; net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem sendto_fresh_socket_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(4096, 1)]) m' evs) := by
  sys_refute

/-- A ZERO-LENGTH send on the same socket is the same -EPIPE: the state is
read before the loop that would return 0.
probe: testing/syscall-check/tests/send_spec.c#conform -- dead -/
theorem sendto_zero_length_on_a_fresh_socket_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 0 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not 0.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#2:ret=0 -- dead -/
theorem sendto_zero_length_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 0 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A BOUND socket is still TCP_CLOSE: -EPIPE.
probe: testing/syscall-check/tests/send_spec.c#conform -- dead -/
theorem sendto_bound_socket_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) bound_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) bound_socket_model [] := by
  sys_norm

/-- …not -EAGAIN.  The port changes nothing: `inet_send_prepare`'s
autobind, whose failure answers -EAGAIN (net/ipv4/af_inet.c:838-840,
v6.18.46), is skipped by TCP (`no_autobind`, net/ipv4/tcp_ipv4.c:3549),
and `sk_stream_wait_connect` answers -EPIPE (net/core/stream.c:70-71)
before its -EAGAIN (:72-73).
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#3:ret=-EAGAIN -- dead -/
theorem sendto_bound_socket_eagain_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) bound_socket_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- A LISTENING socket is outside SYN_SENT/SYN_RECV too: -EPIPE.
probe: testing/syscall-check/tests/send_spec.c#conform -- dead -/
theorem sendto_listening_socket_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) listening_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) listening_socket_model [] := by
  sys_norm

/-- …listen's own errno does not reach the send path.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#4:ret=-EADDRINUSE -- dead -/
theorem sendto_listening_socket_eaddrinuse_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) listening_socket_model
        (Ok (mkEffect (errno_ret EADDRINUSE) [] []) m' evs) := by
  sys_refute

/-- A RESET connection whose error was consumed is -EPIPE: `sock_error`
has nothing left to report and the state is TCP_CLOSE.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_reset_socket_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) reset_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) reset_socket_model [] := by
  sys_norm

/-- …the consumed -ECONNRESET is not reported twice.
kernel: include/net/sock.h:sock_error@v6.18.46 -/
theorem sendto_reset_socket_econnreset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) reset_socket_model
        (Ok (mkEffect (errno_ret ECONNRESET) [] []) m' evs) := by
  sys_refute

/-- A CLOSED fd with a good buffer is -EBADF.
probe: testing/syscall-check/tests/send_spec.c#conform -- dead -/
theorem sendto_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 4096 1 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not the last state's -EPIPE.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#5:ret=-EPIPE -- dead -/
theorem sendto_closed_fd_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 9 4096 1 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- An OPEN non-socket is -ENOTSOCK: stdout here.
probe: testing/syscall-check/tests/send_spec.c#conform -- dead -/
theorem sendto_channel_fd_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 1 4096 1 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) fresh_socket_model [] := by
  sys_norm

/-- …and -ENOTSOCK, not -EBADF: the fd IS open.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendto#6:ret=-EBADF -- dead -/
theorem sendto_channel_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 1 4096 1 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The other non-socket kinds take the same -ENOTSOCK: a regular file.
kernel: net/socket.c:__sys_sendto,sock_from_file@v6.18.46 -/
theorem sendto_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …never a write to the file.
kernel: net/socket.c:__sys_sendto,sock_from_file@v6.18.46 -/
theorem sendto_regular_file_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 0 mem_ab) socket_call_model
        (Ok (SyscallEffect.mkEffectU 1 [] [] [] [] [(4096, 1)]) m' evs) := by
  sys_refute

/-- A pipe's read end: -ENOTSOCK.
kernel: net/socket.c:__sys_sendto,sock_from_file@v6.18.46 -/
theorem sendto_pipe_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 6 4096 1 16384 0 0 mem_ab) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- …not the -EBADF of a closed fd.
kernel: net/socket.c:__sys_sendto,sock_from_file@v6.18.46 -/
theorem sendto_pipe_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 6 4096 1 16384 0 0 mem_ab) socket_kinds_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-! ### A connected socket: declined, beyond Rocq

Rocq's twin sends on these and answers the pending error once; this twin
declines every connected state, because the head of the script does not
decide what the kernel has processed (the spec's send section).  Each
refutation below is the answer Rocq admits at that input. -/

/-- CLOSE_WAIT (a FIN at the head), the socket `accept` really hands over:
declined, because a reset behind the FIN would already have made the send
-EPIPE through `tcp_reset` and `sk_stream_wait_connect`'s `sock_error`.
kernel: net/ipv4/tcp_input.c:tcp_reset; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_close_wait_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 4 4096 2 16384 0 0 mem_ab) accepted_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …Rocq's full delivery on channel 3 is not admitted.
kernel: net/ipv4/tcp_input.c:tcp_reset; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_close_wait_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 4 4096 2 16384 0 0 mem_ab) accepted_socket_model
        (Ok (SyscallEffect.mkEffectU 2 [] [] [] [] [(4096, 2)]) m' evs) := by
  sys_refute

/-- …nor the dead socket's -EPIPE as the one answer, which an arm treating
every state as `SendDead` would give.  -EPIPE is one of Linux's answers
here, after a reset processed behind the FIN, but a send that goes out,
CLOSE_WAIT being inside `TCPF_ESTABLISHED | TCPF_CLOSE_WAIT`, is another,
and the arm declines rather than choose.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; net/ipv4/tcp_input.c:tcp_reset@v6.18.46 -/
theorem sendto_close_wait_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 4 4096 2 16384 0 0 mem_ab) accepted_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- A byte at the head (ESTABLISHED): declined, for the same reason.
kernel: net/ipv4/tcp_input.c:tcp_reset; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_established_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 4 4096 2 16384 0 0 mem_ab) (connected_socket_model (NCons 97 NFin)) o ↔
      o = Unmodeled := by
  sys_norm

/-- …Rocq's one-byte short send is not admitted.
kernel: net/ipv4/tcp_input.c:tcp_reset; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_established_short_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 4 4096 2 16384 0 0 mem_ab) (connected_socket_model (NCons 97 NFin))
        (Ok (SyscallEffect.mkEffectU 1 [] [] [] [] [(4096, 1)]) m' evs) := by
  sys_refute

/-- A RESET at the head: declined, because the segment may not have been
processed when the send runs, and then the bytes go out.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; net/ipv4/tcp_input.c:tcp_reset@v6.18.46 -/
theorem sendto_pending_reset_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 4 4096 2 16384 0 0 mem_ab) (connected_socket_model NRst) o ↔
      o = Unmodeled := by
  sys_norm

/-- …Rocq's once-only -ECONNRESET is not admitted.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; net/ipv4/tcp_input.c:tcp_reset@v6.18.46 -/
theorem sendto_pending_reset_econnreset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 4 4096 2 16384 0 0 mem_ab) (connected_socket_model NRst)
        (Ok (mkEffect (errno_ret ECONNRESET) [] []) m' evs) := by
  sys_refute

/-- …nor -EPIPE: the arm declines the pending error rather than answering the
dead socket's errno for it.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; net/ipv4/tcp_input.c:tcp_reset@v6.18.46 -/
theorem sendto_pending_reset_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 4 4096 2 16384 0 0 mem_ab) (connected_socket_model NRst)
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- A TIMEOUT at the head: declined for the same reason.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; net/ipv4/tcp_timer.c:tcp_write_err@v6.18.46 -/
theorem sendto_pending_timeout_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 4 4096 2 16384 0 0 mem_ab) (connected_socket_model NTimedOut) o ↔
      o = Unmodeled := by
  sys_norm

/-- …Rocq's -ETIMEDOUT is not admitted.
kernel: net/ipv4/tcp_timer.c:tcp_write_err@v6.18.46 -/
theorem sendto_pending_timeout_etimedout_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 4 4096 2 16384 0 0 mem_ab) (connected_socket_model NTimedOut)
        (Ok (mkEffect (errno_ret ETIMEDOUT) [] []) m' evs) := by
  sys_refute

/-- An unmapped buffer on the connected socket declines too, where Rocq
answers the copy's -EFAULT.
kernel: net/ipv4/tcp_input.c:tcp_reset; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_unmapped_buffer_on_close_wait_declines (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 4 46912512909312 1 16384 0 0 (fun _ => none)) accepted_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …Rocq's -EFAULT is not admitted.
kernel: net/ipv4/tcp_input.c:tcp_reset; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_unmapped_buffer_on_close_wait_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in 4 46912512909312 1 16384 0 0 (fun _ => none)) accepted_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-! ### Rocq's classification, and its delivery body, read directly

No arm reaches `send_state`'s connected answers or `send_bytes`: the pins
above decline there.  These read the two definitions at the values Rocq's
twin sends at, so a change to either at those values fails a pin here
whether or not an arm uses it — `send_bytes`'s `pre` included, which is
pinned both empty, as `sendto` passes it, and as the header and
descriptor `sendmsg` passes, in front of the payload's range. -/

/-- A reset at the head is -ECONNRESET on an established connection.
kernel: net/ipv4/tcp_input.c:tcp_reset@v6.18.46 -/
theorem send_state_reset_is_econnreset :
    send_state (.SkConnected peer0 3 NRst) = .SendErr ECONNRESET peer0 3 := by
  rfl

/-- A retransmission timeout is -ETIMEDOUT.
kernel: net/ipv4/tcp_timer.c:tcp_write_err@v6.18.46 -/
theorem send_state_timeout_is_etimedout :
    send_state (.SkConnected peer0 3 NTimedOut) = .SendErr ETIMEDOUT peer0 3 := by
  rfl

/-- A FIN is CLOSE_WAIT, inside `TCPF_ESTABLISHED | TCPF_CLOSE_WAIT`: the
send goes out on the connection's channel.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem send_state_fin_goes_out :
    send_state (.SkConnected peer0 3 NFin) = .SendGoes 3 := by
  rfl

/-- A byte at the head is ESTABLISHED: the send goes out.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem send_state_byte_goes_out :
    send_state (.SkConnected peer0 7 (NCons 97 NFin)) = .SendGoes 7 := by
  rfl

/-- `send_bytes` on "ab": exactly the nonempty prefixes, one `WriteEv` per
byte on the channel, the ledger the ranges the prefix came out of.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem send_bytes_delivers_a_prefix_iff (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    send_bytes [] (fun n => [(4096, n)]) 2 [97, 98] 3 i m o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) m
               (List.map (WriteEv 3) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 2
        ∧ ds = List.take ds.length [97, 98] := by
  sys_norm

/-- …and never the -EFAULT of an unreadable source while the bytes read.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; include/net/sock.h:skb_do_copy_data_nocache@v6.18.46 -/
theorem send_bytes_readable_efault_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ send_bytes [] (fun n => [(4096, n)]) 2 [97, 98] 3 i m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- Asked for ONE byte of the readable "ab", it delivers exactly that byte:
`[97, 98]` is a prefix too, so here the bound on the count is not the
prefix rule's but the request's.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem send_bytes_short_total_delivers_a_prefix_iff (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    send_bytes [] (fun n => [(4096, n)]) 1 [97, 98] 3 i m o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(4096, ds.length)] (mkEffect (len_word ds) [] [])) m
               (List.map (WriteEv 3) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 1
        ∧ ds = List.take ds.length [97, 98] := by
  sys_norm

/-- …never both bytes.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem send_bytes_short_total_overrun_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ send_bytes [] (fun n => [(4096, n)]) 1 [97, 98] 3 i m
        (Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m' evs) := by
  sys_norm
  intro x _ hlen _ _ _ hle
  omega

/-- With sendmsg's `pre`, the header and one descriptor, the ledger is
`pre` FIRST and then the payload's range: the order the bytes were read.
kernel: net/socket.c:___sys_sendmsg,sendmsg_copy_msghdr; net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem send_bytes_delivers_after_pre_iff (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    send_bytes [(8192, 56), (8320, 16)] (fun n => [(4096, n)]) 2 [97, 98] 3 i m o ↔
      ∃ ds : List byte,
        o = Ok (with_copyins [(8192, 56), (8320, 16), (4096, ds.length)]
                 (mkEffect (len_word ds) [] [])) m
               (List.map (WriteEv 3) ds)
        ∧ 1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ 2
        ∧ ds = List.take ds.length [97, 98] := by
  sys_norm

/-- …never the payload's range ahead of `pre`…
kernel: net/socket.c:___sys_sendmsg,sendmsg_copy_msghdr; net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem send_bytes_pre_after_payload_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ send_bytes [(8192, 56), (8320, 16)] (fun n => [(4096, n)]) 2 [97, 98] 3 i m
        (Ok (with_copyins [(4096, 1), (8192, 56), (8320, 16)] (mkEffect 1 [] [])) m' evs) := by
  sys_refute

/-- …and never the payload's range without `pre`.
kernel: net/socket.c:___sys_sendmsg,sendmsg_copy_msghdr; net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem send_bytes_pre_dropped_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ send_bytes [(8192, 56), (8320, 16)] (fun n => [(4096, n)]) 2 [97, 98] 3 i m
        (Ok (with_copyins [(4096, 1)] (mkEffect 1 [] [])) m' evs) := by
  sys_refute

/-- A zero-length request is 0, with only `pre` ledgered.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem send_bytes_zero_length_is_zero (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    send_bytes [(8192, 56)] (fun n => [(4096, n)]) 0 [] 3 i m o ↔
      o = Ok (with_copyins [(8192, 56)] (mkEffect 0 [] [])) m [] := by
  sys_norm

/-- …not -EFAULT: nothing was asked for.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; include/net/sock.h:skb_do_copy_data_nocache@v6.18.46 -/
theorem send_bytes_zero_length_efault_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ send_bytes [(8192, 56)] (fun n => [(4096, n)]) 0 [] 3 i m
        (Ok (with_copyins [(8192, 56)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  sys_refute

/-- …and not 0 with `pre` dropped.
kernel: net/socket.c:___sys_sendmsg,sendmsg_copy_msghdr; net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem send_bytes_zero_length_pre_dropped_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ send_bytes [(8192, 56)] (fun n => [(4096, n)]) 0 [] 3 i m
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- An unreadable first byte is -EFAULT, with only `pre` ledgered.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; include/net/sock.h:skb_do_copy_data_nocache@v6.18.46 -/
theorem send_bytes_unreadable_is_efault (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    send_bytes [(8192, 56)] (fun n => [(4096, n)]) 1 [] 3 i m o ↔
      o = Ok (with_copyins [(8192, 56)] (mkEffect (errno_ret EFAULT) [] [])) m [] := by
  sys_norm

/-- …not 0.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; include/net/sock.h:skb_do_copy_data_nocache@v6.18.46 -/
theorem send_bytes_unreadable_zero_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ send_bytes [(8192, 56)] (fun n => [(4096, n)]) 1 [] 3 i m
        (Ok (with_copyins [(8192, 56)] (mkEffect 0 [] [])) m' evs) := by
  sys_refute

/-- …and not -EFAULT with `pre` dropped.
kernel: net/socket.c:___sys_sendmsg,sendmsg_copy_msghdr; net/ipv4/tcp.c:tcp_sendmsg_locked; include/net/sock.h:skb_do_copy_data_nocache@v6.18.46 -/
theorem send_bytes_unreadable_pre_dropped_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ send_bytes [(8192, 56)] (fun n => [(4096, n)]) 1 [] 3 i m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-! ### sendmsg: the argument, the fd, the header, the import -/

/-- THE ARGUMENT IS READ, NEVER THE FIELD: argument 0 with MSG_NOSIGNAL in
`msg_flags` declines, because `____sys_sendmsg` overwrites the field with
the argument and the call takes SIGPIPE.
kernel: net/socket.c:____sys_sendmsg,__sys_sendmsg@v6.18.46 -/
theorem sendmsg_field_flag_does_not_count (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 0 msg_ab_field_nosignal) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …the -EPIPE a field-reading spec would answer is refused.
kernel: net/socket.c:____sys_sendmsg,__sys_sendmsg@v6.18.46 -/
theorem sendmsg_field_flag_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 0 msg_ab_field_nosignal) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- …and the other way: argument MSG_NOSIGNAL with MSG_DONTWAIT in the
field is the plain -EPIPE, header and descriptor ledgered.
kernel: net/socket.c:____sys_sendmsg; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_field_dontwait_is_ignored (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_ab_field_dontwait) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: net/socket.c:____sys_sendmsg@v6.18.46 -/
theorem sendmsg_field_dontwait_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ab_field_dontwait) fresh_socket_model Unmodeled := by
  sys_refute

/-- The flag gate runs first, with the same exactness as `sendto`'s.
kernel: net/core/stream.c:sk_stream_error@v6.18.46 -/
theorem sendmsg_dontwait_argument_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16448 msg_ab) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the kernel's own answer there, the dead socket's -EPIPE with header
and descriptor ledgered, is not admitted either.
kernel: net/core/stream.c:sk_stream_error@v6.18.46 -/
theorem sendmsg_dontwait_argument_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16448 msg_ab) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- …and the high half of the argument is dropped here as well.
kernel: net/socket.c:__sys_sendmsg; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_high_flag_half_is_dropped (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 (Z_to_bv 64 (2 ^ 32 + 16384)) msg_ab) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …with -EPIPE the only answer.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_high_flag_half_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 (Z_to_bv 64 (2 ^ 32 + 16384)) msg_ab) fresh_socket_model
        Unmodeled := by
  sys_refute

/-- THE FD IS RESOLVED BEFORE THE HEADER IS COPIED, so a closed fd with an
unreadable header is -EBADF, the ledger empty: nothing was copied.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_closed_fd_unreadable_header_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 9 8192 16384 (fun _ => none)) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_closed_fd_unreadable_header_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 9 8192 16384 (fun _ => none)) fresh_socket_model Unmodeled := by
  sys_refute

/-- …and -EFAULT, the answer of a copy before the fd, is refused.  It is
qemu-user's answer: `do_sendrecvmsg` (linux-user/syscall.c:3439-3454,
QEMU 11.1.1) locks the header before the fd is looked at.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_closed_fd_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 9 8192 16384 (fun _ => none)) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …and with a good header the closed fd is still -EBADF, ledger empty.
probe: testing/syscall-check/tests/send_spec.c#conform -- msgdead -/
theorem sendmsg_closed_fd_is_ebadf_unledgered (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 9 8192 16384 msg_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not the dead socket's -EPIPE.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendmsg#3:ret=-EPIPE -- msgdead -/
theorem sendmsg_closed_fd_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 9 8192 16384 msg_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- A channel fd with an absent header is -ENOTSOCK, the ledger empty:
`sock_from_file` answers before `___sys_sendmsg` copies anything.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_channel_fd_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 1 8192 16384 (fun _ => none)) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_channel_fd_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 1 8192 16384 (fun _ => none)) fresh_socket_model Unmodeled := by
  sys_refute

/-- …not the dead socket's -EPIPE…
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_channel_fd_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 1 8192 16384 (fun _ => none)) fresh_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- …and not the -EFAULT of a header copied before the socket test:
`sock_from_file` answers before `___sys_sendmsg` copies anything.  It is
qemu-user's answer, as at `sendmsg_closed_fd_efault_rejected`.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_channel_fd_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 1 8192 16384 (fun _ => none)) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- Every other non-socket kind, arm by arm: a regular file…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_ab) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …never with the header ledgered: it is not copied.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_regular_file_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ab) socket_call_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- …a write-only file…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_write_only_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 4 8192 16384 msg_ab) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_write_only_file_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 4 8192 16384 msg_ab) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …a directory…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_directory_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 5 8192 16384 msg_ab) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_directory_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 5 8192 16384 msg_ab) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …a pipe's read end…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_pipe_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 6 8192 16384 msg_ab) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_pipe_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 6 8192 16384 msg_ab) socket_kinds_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …/dev/null…
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_devnull_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 7 8192 16384 msg_ab) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_devnull_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 7 8192 16384 msg_ab) socket_kinds_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and /dev/urandom.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_urandom_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 8 8192 16384 msg_ab) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_urandom_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 8 8192 16384 msg_ab) socket_kinds_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- AN UNREADABLE HEADER on a socket is -EFAULT with nothing ledgered: the
56-byte `copy_from_user` failed.
kernel: net/socket.c:copy_msghdr_from_user@v6.18.46 -/
theorem sendmsg_unreadable_header_is_efault (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 (fun _ => none)) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not the dead socket's -EPIPE: the state is never reached.
kernel: net/socket.c:copy_msghdr_from_user@v6.18.46 -/
theorem sendmsg_unreadable_header_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 (fun _ => none)) fresh_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- …and the header it failed to copy is not ledgered.
kernel: net/socket.c:copy_msghdr_from_user@v6.18.46 -/
theorem sendmsg_unreadable_header_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 (fun _ => none)) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- A HEADER THAT WRAPS past `2^64` IS READ: `read_bytes_map` walks the
56 bytes in word arithmetic and has no range test, so over memory that
maps every byte the walk reaches the header reads as zeros and the call
goes on to the dead socket's -EPIPE, the header ledgered at the address
the walk started from.
kernel: net/socket.c:copy_msghdr_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_wrapping_header_is_read (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 (Z_to_bv 64 (2 ^ 64 - 8)) 16384 rmem_open) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
                [(Z_to_bv 64 (2 ^ 64 - 8), 56)]) fresh_socket_model [] := by
  sys_norm

/-- …the -EFAULT a range test ahead of the walk would answer is refused.
kernel: net/socket.c:copy_msghdr_from_user@v6.18.46 -/
theorem sendmsg_wrapping_header_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 (Z_to_bv 64 (2 ^ 64 - 8)) 16384 rmem_open) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A header whose last byte is the first past `TASK_SIZE` IS READ as
well, for the same reason: the walk advances address by address and tests
no range, and `rmem_open` maps every byte it reaches.  The zeroed header
is a send of nothing on the dead socket: -EPIPE with the header ledgered.
kernel: net/socket.c:copy_msghdr_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_header_past_task_size_is_read (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 (Z_to_bv 64 (2 ^ 47 - 55)) 16384 rmem_open) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
                [(Z_to_bv 64 (2 ^ 47 - 55), 56)]) fresh_socket_model [] := by
  sys_norm

/-- …and one byte lower, where the header ends exactly at `TASK_SIZE`,
the same -EPIPE with the header ledgered.
kernel: net/socket.c:copy_msghdr_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_header_at_task_size_is_read (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 (Z_to_bv 64 (2 ^ 47 - 56)) 16384 rmem_open) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
                [(Z_to_bv 64 (2 ^ 47 - 56), 56)]) fresh_socket_model [] := by
  sys_norm

/-- …not -EFAULT.
kernel: include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem sendmsg_header_at_task_size_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 (Z_to_bv 64 (2 ^ 47 - 56)) 16384 rmem_open) fresh_socket_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A DESTINATION ADDRESS in the header declines, as `sendto`'s does.
kernel: net/socket.c:__copy_msghdr@v6.18.46 -/
theorem sendmsg_named_header_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_named) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …its -EPIPE is not admitted.
kernel: net/socket.c:__copy_msghdr@v6.18.46 -/
theorem sendmsg_named_header_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_named) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- With `msg_name` NULL a negative `msg_namelen` is forced to 0 before its
sign test: the plain -EPIPE.
kernel: net/socket.c:__copy_msghdr; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_null_name_negative_namelen_is_ignored (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_negnamelen) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …not `__copy_msghdr`'s -EINVAL.
kernel: net/socket.c:__copy_msghdr@v6.18.46 -/
theorem sendmsg_null_name_negative_namelen_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_negnamelen) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- `msg_iovlen` past `UIO_MAXIOV` IS -EMSGSIZE, with the header ledgered.
probe: testing/syscall-check/tests/send_spec.c#conform -- msgemsgsize -/
theorem sendmsg_iovlen_over_uio_maxiov_is_emsgsize (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_1025) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)])
             fresh_socket_model [] := by
  sys_norm

/-- …not writev's -EINVAL for the same shape.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendmsg#1:ret=-EINVAL -- msgemsgsize -/
theorem sendmsg_iovlen_over_uio_maxiov_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_1025) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- …and never without the header it was decided on.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendmsg#1:drop-copyins -- msgemsgsize -/
theorem sendmsg_iovlen_over_uio_maxiov_unledgered_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_1025) fresh_socket_model
        (Ok (mkEffect (errno_ret EMSGSIZE) [] []) m' evs) := by
  sys_refute

/-- …and it comes before the heap band's decline, which 1025 is also past.
kernel: net/socket.c:__copy_msghdr@v6.18.46 -/
theorem sendmsg_iovlen_over_uio_maxiov_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_1025) fresh_socket_model Unmodeled := by
  sys_refute

/-- kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem sendmsg_iovlen_over_uio_maxiov_write_only_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 4 8192 16384 msg_iovlen_1025) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …the fd answers before the header is copied, so the oversized iovec
count is never read.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_iovlen_over_uio_maxiov_write_only_file_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 4 8192 16384 msg_iovlen_1025) socket_call_model Unmodeled := by
  sys_refute

/-- …so qemu-user's -EMSGSIZE, a real answer, is refused, with the header
in the ledger as on the socket…
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_iovlen_over_uio_maxiov_write_only_file_emsgsize_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 4 8192 16384 msg_iovlen_1025) socket_call_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- …and without it.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_iovlen_over_uio_maxiov_write_only_file_bare_emsgsize_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 4 8192 16384 msg_iovlen_1025) socket_call_model
        (Ok (mkEffect (errno_ret EMSGSIZE) [] []) m' evs) := by
  sys_refute

/-- A control block beside it changes nothing: `msg_controllen` is read
only after the import.
probe: testing/syscall-check/tests/send_spec.c#conform -- msgctl -/
theorem sendmsg_iovlen_over_uio_maxiov_with_control_is_emsgsize (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_1025_ctl) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)])
             fresh_socket_model [] := by
  sys_norm

/-- …still not -EINVAL.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendmsg#1:ret=-EINVAL -- msgctl -/
theorem sendmsg_iovlen_over_uio_maxiov_with_control_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_1025_ctl) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- …and not the control block's decline, which is `____sys_sendmsg`'s and
comes after.
kernel: net/socket.c:__copy_msghdr,____sys_sendmsg@v6.18.46 -/
theorem sendmsg_iovlen_over_uio_maxiov_with_control_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_1025_ctl) fresh_socket_model Unmodeled := by
  sys_refute

/-- A NAMED HEADER PAST `UIO_MAXIOV` DECLINES: the name sixteen unreadable
bytes at 65536, `msg_iovlen` 1025.  Linux's `__copy_msghdr` reads the name
first, `move_addr_to_kernel` answering -EFAULT (net/socket.c:2532-2538,
v6.18.46), and tests `msg_iovlen` only after (:2545-2546); qemu-user's
`do_sendrecvmsg_locked` hands a name it cannot lock on as `(void *)-1`
(linux-user/syscall.c:3336-3349, QEMU 11.1.1) and answers -EMSGSIZE for a
count over `IOV_MAX` (linux-user/syscall.c:3365-3371, QEMU 11.1.1) before
any host call.  It declines…
kernel: net/socket.c:__copy_msghdr,move_addr_to_kernel@v6.18.46 -/
theorem sendmsg_named_header_over_uio_maxiov_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_badname_1025) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so qemu-user's -EMSGSIZE, which a `UIO_MAXIOV` test ahead of the name
gate would prove as certain, is refused: it is not Linux's answer.
kernel: net/socket.c:__copy_msghdr,move_addr_to_kernel@v6.18.46 -/
theorem sendmsg_named_header_over_uio_maxiov_emsgsize_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_badname_1025) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- …and with a NEGATIVE `msg_namelen` beside the name: Linux answers
-EINVAL (net/socket.c:2523-2524, v6.18.46) before `msg_iovlen`, and
qemu-user, asked to lock 2^32 - 1 bytes of the name, hands it on as
`(void *)-1` and answers -EMSGSIZE as above.  It declines…
kernel: net/socket.c:__copy_msghdr@v6.18.46 -/
theorem sendmsg_negative_namelen_over_uio_maxiov_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_negname_1025) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so -EMSGSIZE is refused there too.
kernel: net/socket.c:__copy_msghdr@v6.18.46 -/
theorem sendmsg_negative_namelen_over_uio_maxiov_emsgsize_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_negname_1025) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- THE FULL 64-BIT FIELD: `2^32 + 1` is -EMSGSIZE, although its low half,
the count `import_iovec` would take, is 1.
kernel: net/socket.c:__copy_msghdr@v6.18.46 -/
theorem sendmsg_wide_iovlen_is_emsgsize (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_wide) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)])
             fresh_socket_model [] := by
  sys_norm

/-- …not the one-descriptor send the low half would be.
kernel: net/socket.c:__copy_msghdr@v6.18.46 -/
theorem sendmsg_wide_iovlen_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_wide) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- The heap-backed band declines: nine readable descriptors, where
`iovec_from_user` allocates (lib/iov_iter.c:1308-1311, v6.18.46) and
Linux answers -ENOMEM if the allocation fails and the dead socket's -EPIPE
if it does not.
probe: testing/syscall-check/tests/send_spec.c#fail-closed -- msgiovgap -/
theorem sendmsg_heap_band_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_9) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and that -EPIPE, with the header and all nine descriptors ledgered as
the import would leave them, is not admitted in its place: it is not
certain while the allocation can fail.
probe: testing/syscall-check/tests/send_spec.c#fail-closed -- msgiovgap -/
theorem sendmsg_heap_band_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_9) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
               [(8192, 56), (8320, 16), (8336, 16), (8352, 16), (8368, 16), (8384, 16),
                (8400, 16), (8416, 16), (8432, 16), (8448, 16)]) m' evs) := by
  sys_refute

/-- `UIO_MAXIOV` ITSELF IS NOT -EMSGSIZE: the test is `msg_iovlen >
UIO_MAXIOV`, so 1024 goes on to the import and lands in the heap band,
which declines for `Fs.ReadWrite.readv_heap_gap`'s reason.  qemu-user's
`count > IOV_MAX` (linux-user/syscall.c:3365, QEMU 11.1.1) passes it too.
kernel: net/socket.c:__copy_msghdr@v6.18.46 -/
theorem sendmsg_iovlen_at_uio_maxiov_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_1024) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so -EMSGSIZE is refused there.
kernel: net/socket.c:__copy_msghdr@v6.18.46 -/
theorem sendmsg_iovlen_at_uio_maxiov_emsgsize_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_iovlen_1024) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- `UIO_FASTIOV` ITSELF IS THE STACK PATH: eight descriptors are
imported and the dead socket answers -EPIPE, the header and all eight
entries ledgered.  `iovec_from_user` allocates only when
`nr_segs > fast_segs` (lib/iov_iter.c:1308, v6.18.46).
kernel: lib/iov_iter.c:__import_iovec,iovec_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_eight_descriptors_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_eight) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
                [(8192, 56), (8320, 16), (8336, 16), (8352, 16), (8368, 16),
                 (8384, 16), (8400, 16), (8416, 16), (8432, 16)]) fresh_socket_model [] := by
  sys_norm

/-- …not the heap band's decline.
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem sendmsg_eight_descriptors_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_eight) fresh_socket_model Unmodeled := by
  sys_refute

/-- A DESCRIPTOR NAMING A KERNEL ADDRESS IS IMPORTED AS IT STANDS: the
walk reads both fields of the descriptor and tests only the length, so
the base reaches the send unexamined and the dead socket answers -EPIPE,
header and descriptor ledgered.
kernel: lib/iov_iter.c:copy_iovec_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_kernel_segment_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_kbase) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …the -EFAULT an `access_ok` on the base would answer is refused.
kernel: lib/iov_iter.c:import_ubuf,__import_iovec_ubuf@v6.18.46 -/
theorem sendmsg_kernel_segment_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_kbase) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- THE SAME ADDRESS UNDER A ZERO LENGTH is the same -EPIPE: the walk
reads the descriptor, finds a length that is not negative, and hands the
base on without a range test of any kind.
kernel: lib/iov_iter.c:copy_iovec_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_zero_length_kernel_segment_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_zero) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …not the -EFAULT an `access_ok` applied to a zero length would give.
kernel: lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem sendmsg_zero_length_kernel_segment_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_zero) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- A KERNEL ADDRESS AT INDEX 1 is the same -EPIPE, all three ranges
ledgered: the walk has no second pass over the bases, so index 1 is
handed on like index 0.
kernel: lib/iov_iter.c:copy_iovec_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_kernel_second_segment_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_second) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
                [(8192, 56), (8320, 16), (8336, 16)]) fresh_socket_model [] := by
  sys_norm

/-- …not the -EFAULT a second pass over the bases would answer.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem sendmsg_kernel_second_segment_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_second) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] []
               [(8192, 56), (8320, 16), (8336, 16)]) m' evs) := by
  sys_refute

/-- A KERNEL ADDRESS FIRST OF TWO, under a nonzero length, is the same
-EPIPE on the array path, both descriptors ledgered.
kernel: lib/iov_iter.c:copy_iovec_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_kernel_head_of_two_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_first_of_two) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
                [(8192, 56), (8320, 16), (8336, 16)]) fresh_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem sendmsg_kernel_head_of_two_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_first_of_two) fresh_socket_model
        Unmodeled := by
  sys_refute

/-- …nor the -EFAULT a pass over the bases would answer.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem sendmsg_kernel_head_of_two_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_first_of_two) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] []
               [(8192, 56), (8320, 16), (8336, 16)]) m' evs) := by
  sys_refute

/-- A ZERO-LENGTH KERNEL ADDRESS FIRST OF TWO is the same -EPIPE: a zero
length is read and handed on like any other.
kernel: lib/iov_iter.c:copy_iovec_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_zero_length_kernel_head_of_two_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_zero_first_of_two) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
                [(8192, 56), (8320, 16), (8336, 16)]) fresh_socket_model [] := by
  sys_norm

/-- …not the -EFAULT a pass over the bases would answer.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem sendmsg_zero_length_kernel_head_of_two_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_zero_first_of_two) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] []
               [(8192, 56), (8320, 16), (8336, 16)]) m' evs) := by
  sys_refute

/-- A FIRST DESCRIPTOR WHOSE UNCAPPED END IS PAST `TASK_SIZE` DECLINES:
the walk reads `(4096, 2^47)` and `(4096, 1)` and tests no base, so the
import succeeds, and `cap_iovecs` then caps the head to `MAX_RW_COUNT`,
a total far past `Uaccess.rw_bytes_max`, which is the decline.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem sendmsg_long_head_of_two_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_long_head) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …not the -EFAULT an `access_ok` on the UNCAPPED length would answer.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem sendmsg_long_head_of_two_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_long_head) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] []
               [(8192, 56), (8320, 16), (8336, 16)]) m' evs) := by
  sys_refute

/-- A NEGATIVE `iov_len` is -EINVAL.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_negative_segment_is_einval (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_neglen) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …not -EFAULT.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_negative_segment_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_neglen) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- …nor -EINVAL with the header alone ledgered: `copy_iovec_from_user`
loads `iov_len` and `iov_base` (lib/iov_iter.c:1272-1273, v6.18.46)
before its `len < 0` test (:1276).
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_negative_segment_header_only_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_neglen) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- A NEGATIVE `iov_len` UNDER A KERNEL BASE is still -EINVAL: the length
test is `copy_iovec_from_user`'s, inside the walk, and the walk is all
there is — no pass over the bases follows it.  qemu-user's `lock_iovec`
tests `len < 0` before it locks (linux-user/syscall.c:3113-3115,
QEMU 11.1.1), once `g_try_new0` has allocated the host vector
(:3091-3095).
kernel: lib/iov_iter.c:copy_iovec_from_user,__import_iovec_ubuf@v6.18.46 -/
theorem sendmsg_negative_kernel_segment_is_einval (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_neglen) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …not the base's -EFAULT.
kernel: lib/iov_iter.c:copy_iovec_from_user,import_ubuf@v6.18.46 -/
theorem sendmsg_negative_kernel_segment_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_neglen) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- An UNREADABLE descriptor array, on an unmapped page of its own, is
-EFAULT, the entry it tried ledgered: the walk's first load of the
descriptor fails.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_unreadable_array_is_efault (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_noarray) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (12288, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …and not a decline: every fault the walk gives is answered.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_unreadable_array_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_noarray) fresh_socket_model Unmodeled := by
  sys_refute

/-- AN ARRAY AT A KERNEL ADDRESS is -EFAULT with the entry the walk tried
ledgered: there is no range test on the array, so the walk loads at the
address it was given and the load is what fails.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_kernel_array_is_efault (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 (msg_array_at (Z_to_bv 64 (2 ^ 63)) 1))
        fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] []
                [(8192, 56), (Z_to_bv 64 (2 ^ 63), 16)]) fresh_socket_model [] := by
  sys_norm

/-- …the header-only ledger a range test ahead of the load would leave is
refused.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_kernel_array_header_only_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 (msg_array_at (Z_to_bv 64 (2 ^ 63)) 1))
        fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- …and two descriptors there are the same -EFAULT, on the array path,
with the first entry ledgered.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_kernel_array_of_two_is_efault (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 (msg_array_at (Z_to_bv 64 (2 ^ 63)) 2))
        fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] []
                [(8192, 56), (Z_to_bv 64 (2 ^ 63), 16)]) fresh_socket_model [] := by
  sys_norm

/-- …not a decline: the load fault is answered.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_kernel_array_of_two_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 (msg_array_at (Z_to_bv 64 (2 ^ 63)) 2))
        fresh_socket_model Unmodeled := by
  sys_refute

/-- AN ARRAY STRADDLING `TASK_SIZE` (its last eight bytes past it) is
-EFAULT with the entry the walk tried ledgered: nothing it walks onto
past the header is mapped, so the load fails.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_array_straddling_task_size_is_efault (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 (msg_array_at (Z_to_bv 64 (2 ^ 47 - 8)) 1))
        fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] []
                [(8192, 56), (Z_to_bv 64 (2 ^ 47 - 8), 16)]) fresh_socket_model [] := by
  sys_norm

/-- …and the header-only ledger a range test ahead of the load would
leave is refused.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_array_straddling_task_size_header_only_ledger_rejected
    (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 (msg_array_at (Z_to_bv 64 (2 ^ 47 - 8)) 1))
        fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- THERE IS NO RANGE TEST ON THE ENTRY AT ALL: with every byte past the
header readable (`msg_straddle_readable`), the straddling entry reads as
`(0, 0)`, the import succeeds, and the dead socket answers -EPIPE with
the header and the entry ledgered.
kernel: lib/iov_iter.c:copy_iovec_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_readable_straddle_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_straddle_readable) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
                [(8192, 56), (Z_to_bv 64 (2 ^ 47 - 8), 16)]) fresh_socket_model [] := by
  sys_norm

/-- …not the header-only -EFAULT a range test over the whole entry would
answer.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_readable_straddle_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_straddle_readable) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- …and on the ARRAY path too: two entries at `2^47 - 16`, everything
past the header readable (`msg_straddle_readable_two`), read as two
`(0, 0)` entries and answer the dead socket's -EPIPE, both entries
ledgered.
kernel: lib/iov_iter.c:copy_iovec_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_readable_straddle_of_two_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_straddle_readable_two) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
                [(8192, 56), (Z_to_bv 64 (2 ^ 47 - 16), 16), (Z_to_bv 64 (2 ^ 47), 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_readable_straddle_of_two_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_straddle_readable_two) fresh_socket_model
        Unmodeled := by
  sys_refute

/-- …nor the header-only -EFAULT a range test over the whole array would
answer.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_readable_straddle_of_two_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_straddle_readable_two) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- THE FIRST ENTRY'S LENGTH TEST IS ALL THERE IS: two entries at
`2^47 - 16`, the in-range first naming a negative `iov_len`
(`msg_neglen_straddle`), are -EINVAL with that entry ledgered, since the
walk loads it and tests its length before it reaches the second, which
nothing maps.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_negative_straddle_is_einval (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_neglen_straddle) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] []
                [(8192, 56), (Z_to_bv 64 (2 ^ 47 - 16), 16)]) fresh_socket_model [] := by
  sys_norm

/-- …not the header-only -EFAULT a range test over the whole array would
answer ahead of the length.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_negative_straddle_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_neglen_straddle) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- AN IN-RANGE ARRAY OF TWO THAT NOTHING MAPS, on the page after the
header's, is -EFAULT from the walk's first `unsafe_get_user`, the entry it
tried ledgered.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_unmapped_array_of_two_is_efault (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 (msg_array_at 12288 2)) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (12288, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …not a decline: the load fault is answered.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_unmapped_array_of_two_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 (msg_array_at 12288 2)) fresh_socket_model
        Unmodeled := by
  sys_refute

/-- A CONTROL BLOCK declines once the import has passed.
kernel: net/socket.c:____sys_sendmsg@v6.18.46 -/
theorem sendmsg_control_block_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_ctl) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …its -EPIPE is not admitted.
kernel: net/socket.c:____sys_sendmsg@v6.18.46 -/
theorem sendmsg_control_block_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ctl) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- THE CONTROL BLOCK'S DECLINE COMES FIRST HERE: a kernel descriptor
beside a sixteen-byte control block (`msg_kbase_ctl`) imports without a
complaint, since the walk tests no base, and `____sys_sendmsg`'s
`msg_controllen` is then the decline.
kernel: net/socket.c:copy_msghdr_from_user,____sys_sendmsg@v6.18.46 -/
theorem sendmsg_kernel_segment_beside_control_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_ctl) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …not the -EFAULT an `access_ok` on the base would answer.
kernel: lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem sendmsg_kernel_segment_beside_control_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_ctl) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- THE IMPORT'S -EINVAL COMES BEFORE THE CONTROL BLOCK'S DECLINE: a
negative `iov_len` beside the control block (`msg_neglen_ctl`) is
-EINVAL, since `import_iovec` runs in `sendmsg_copy_msghdr`, before
`____sys_sendmsg` reads `msg_controllen`.
kernel: net/socket.c:copy_msghdr_from_user,____sys_sendmsg; lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_negative_segment_beside_control_is_einval (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_neglen_ctl) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …not the control block's decline.
kernel: net/socket.c:copy_msghdr_from_user,____sys_sendmsg@v6.18.46 -/
theorem sendmsg_negative_segment_beside_control_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_neglen_ctl) fresh_socket_model Unmodeled := by
  sys_refute

/-- A control POINTER with length 0 is a plain send: the gate is
`else if (ctl_len)`.
kernel: net/socket.c:____sys_sendmsg; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_control_pointer_without_length_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_ctlptr) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: net/socket.c:____sys_sendmsg@v6.18.46 -/
theorem sendmsg_control_pointer_without_length_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ctlptr) fresh_socket_model Unmodeled := by
  sys_refute

/-- A gathered total past `Uaccess.rw_bytes_max` declines.
probe: testing/syscall-check/tests/send_spec.c#fail-closed -- msgbigcount -/
theorem sendmsg_big_total_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_big) fresh_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and its -EPIPE is not admitted.
probe: testing/syscall-check/tests/send_spec.c#fail-closed -- msgbigcount -/
theorem sendmsg_big_total_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_big) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- THE `rw_bytes_max` DECLINE COMES FIRST HERE: a kernel descriptor one
byte past the bound (`msg_kbase_big`) imports without a complaint, since
the walk tests no base, and the gathered total past the bound is then the
decline.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_big_kernel_segment_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_big) fresh_socket_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …not the -EFAULT an `access_ok` on the base would answer.
kernel: lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem sendmsg_big_kernel_segment_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_kbase_big) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- A gathered total of exactly `Uaccess.rw_bytes_max` is modeled: the
dead socket's -EPIPE, over a descriptor mapped whole (`msg_at_max`), where
qemu-user answers it too under the allocation premise `msg_at_max`
states.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_total_at_the_bound_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_at_max) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  change sendmsg_spec 3 8192 16384 (sendmsg_in 3 8192 16384 msg_at_max) fresh_socket_model o ↔ _
  simp only [sendmsg_spec, show send_flags_modeled 16384 = true by decide,
    not_true_eq_false, ↓reduceIte, bind_input_iff, bind_get_model_iff, sendmsg_in.eq_1,
    show fd_lookup (m_fds fresh_socket_model) 3 = some (.FdSocket .SkFresh) from rfl,
    show read_bytes_map msg_at_max 8192 (Z_to_bv 64 MSGHDR_SIZE) =
      some (msghdr_bytes 0 0 1 0 0 0) by decide]
  simp only [show le_bytes_to_word ((msghdr_bytes 0 0 1 0 0 0).take 8) = 0 by decide,
    show le_bytes_to_word (((msghdr_bytes 0 0 1 0 0 0).drop 16).take 8) = 8320 by decide,
    show le_bytes_to_word (((msghdr_bytes 0 0 1 0 0 0).drop 24).take 8) = 1 by decide,
    show le_bytes_to_word (((msghdr_bytes 0 0 1 0 0 0).drop 40).take 8) = 0 by decide,
    show copy_iovecs_aux msg_at_max 8320 (word_to_nat 1) = .ImpOk [(16384, 131072)] by decide,
    show copy_iovecs_accesses msg_at_max 8320 (word_to_nat 1) = [(8320, 16)] by decide]
  sys_norm

/-- …not a decline.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_total_at_the_bound_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_at_max) fresh_socket_model Unmodeled := by
  simp only [sendmsg_total_at_the_bound_is_epipe, reduceCtorEq, not_false_eq_true]

/-- THE DEAD SOCKET, through sendmsg: -EPIPE with the header and the
descriptor in the ledger, in the order they were read.
probe: testing/syscall-check/tests/send_spec.c#conform -- msgdead -/
theorem sendmsg_fresh_socket_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_ab) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …the -EFAULT of a model that read an empty header is refused.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendmsg#1:ret=-EFAULT -- msgdead -/
theorem sendmsg_fresh_socket_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ab) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- …and no autobind on this path either.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendmsg#1:ret=-EAGAIN -- msgdead -/
theorem sendmsg_fresh_socket_eagain_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ab) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- …and the right errno with the header alone in the ledger is refused: the
one descriptor at 8320 was read too.  `copy_msghdr_from_user` imports
the vector at net/socket.c:2568 (v6.18.46), and a single entry takes
`__import_iovec_ubuf` (lib/iov_iter.c:1330-1350), whose
`copy_iovec_from_user` loads it (:1342), all before `____sys_sendmsg`
hands the message to the socket at net/socket.c:2631.
kernel: lib/iov_iter.c:__import_iovec_ubuf,__import_iovec@v6.18.46 -/
theorem sendmsg_fresh_socket_header_only_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ab) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- NO DESCRIPTORS: the state is read before the copy loop, -EPIPE with the
header alone ledgered.
probe: testing/syscall-check/tests/send_spec.c#conform -- msgdead -/
theorem sendmsg_no_descriptors_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_none) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56)])
             fresh_socket_model [] := by
  sys_norm

/-- …not 0.
probe: testing/syscall-check/tests/send_spec.c#reject --mutate sendmsg#2:ret=0 -- msgdead -/
theorem sendmsg_no_descriptors_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_none) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [] [] [(8192, 56)]) m' evs) := by
  sys_refute

/-- TWO descriptors take the array path: both are ledgered after the header.
kernel: lib/iov_iter.c:copy_iovec_from_user,__import_iovec; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_two_descriptors_ledger_both (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_two) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
                [(8192, 56), (8320, 16), (8336, 16)]) fresh_socket_model [] := by
  sys_norm

/-- …never the first alone.
kernel: lib/iov_iter.c:copy_iovec_from_user,__import_iovec@v6.18.46 -/
theorem sendmsg_two_descriptors_one_ledgered_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_two) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- The listening socket: the same -EPIPE through sendmsg, header and
descriptor ledgered.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_listening_socket_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_ab) listening_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             listening_socket_model [] := by
  sys_norm

/-- …listen's own errno does not reach the send path here either.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_listening_socket_eaddrinuse_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ab) listening_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- The consumed reset: the same -EPIPE, `sock_error` having nothing left
to report.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_reset_socket_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_ab) reset_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             reset_socket_model [] := by
  sys_norm

/-- …the consumed -ECONNRESET is not reported twice.
kernel: include/net/sock.h:sock_error@v6.18.46 -/
theorem sendmsg_reset_socket_econnreset_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ab) reset_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ECONNRESET) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- A BOUND socket is still TCP_CLOSE: the same -EPIPE through sendmsg.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_bound_socket_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_ab) bound_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             bound_socket_model [] := by
  sys_norm

/-- …not -EAGAIN, for sendto's reason: TCP skips `inet_send_prepare`'s
autobind (net/ipv4/af_inet.c:838-840, net/ipv4/tcp_ipv4.c:3549,
v6.18.46), and `sk_stream_wait_connect` answers -EPIPE
(net/core/stream.c:70-71) before its -EAGAIN (:72-73).
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_bound_socket_eagain_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ab) bound_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- A connected socket declines through sendmsg as through sendto.
kernel: net/ipv4/tcp_input.c:tcp_reset; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_close_wait_declines (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 4 8192 16384 msg_ab) accepted_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …Rocq's gather onto channel 3 is not admitted.
kernel: net/ipv4/tcp_input.c:tcp_reset; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_close_wait_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 4 8192 16384 msg_ab) accepted_socket_model
        (Ok (SyscallEffect.mkEffectU 2 [] [] [] [] [(8192, 56), (8320, 16), (4096, 2)]) m' evs) := by
  sys_refute

/-! ## recvfrom (207), recvmsg (212): the order, then the descriptor

The probe is linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/recv_spec.c.  Both entry points
decline a socket (the spec's recv section); every modeled answer is an
argument's or a non-socket descriptor's. -/

/-- THE BUFFER BEFORE THE FD: a closed fd with a kernel-half destination is
-EFAULT.
rocq-twin: recv_argument_order_is_opposite
probe: testing/syscall-check/tests/recv_spec.c#conform -- buffirst -/
theorem recvfrom_high_buffer_beats_the_fd (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 999 (Z_to_bv 64 (2 ^ 63)) 1 0 (fun _ => none)) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) socket_call_model [] := by
  sys_norm

/-- …-EBADF there is recvmsg's order, not recvfrom's.
probe: testing/syscall-check/tests/recv_spec.c#reject --mutate recvfrom:ret=-EBADF -- buffirst -/
theorem recvfrom_high_buffer_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 999 (Z_to_bv 64 (2 ^ 63)) 1 0 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- At the edge: `2^47 - 7` with size 8.
probe: testing/syscall-check/tests/recv_spec.c#conform -- edgebuf -/
theorem recvfrom_edge_buffer_beats_the_fd (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 999 (Z_to_bv 64 (2 ^ 47 - 7)) 8 0 (fun _ => none)) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/recv_spec.c#reject --mutate recvfrom:ret=-EBADF -- edgebuf -/
theorem recvfrom_edge_buffer_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 999 (Z_to_bv 64 (2 ^ 47 - 7)) 8 0 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- A size past `Uaccess.rw_bytes_max` declines, here into a destination
readable and writable throughout, which qemu-user locks too, so both
implementations reach stdin's -ENOTSOCK: the decline costs that answer.
probe: testing/syscall-check/tests/recv_spec.c#fail-closed -- bigcount -/
theorem recvfrom_big_count_declines (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_rw_in 0 4096 131073 0 wmem_open) socket_call_model o ↔ o = Unmodeled := by
  sys_norm

/-- …its -ENOTSOCK is not admitted.
probe: testing/syscall-check/tests/recv_spec.c#fail-closed -- bigcount -/
theorem recvfrom_big_count_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_rw_in 0 4096 131073 0 wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- …and into a destination qemu-user cannot lock for writing, the size
gate's place before the fd KEEPS THE SPEC SOUND: `recvfrom(0, 0x1000,
131073)` passes Linux's range test (`import_ubuf`,
lib/iov_iter.c:1433-1442, v6.18.46) and stdin answers -ENOTSOCK
(net/socket.c:2285-2291), while qemu-user's `do_recvfrom` locks all 131073
bytes for writing before the host call (linux-user/syscall.c:3695-3697,
QEMU 11.1.1) and answers -EFAULT.  It declines…
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_big_count_unwritable_declines (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 0 4096 131073 0 (fun _ => none)) socket_call_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …so the -ENOTSOCK a size gate after the fd would prove as certain is
refused: it is not qemu-user's answer.
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_big_count_unwritable_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 0 4096 131073 0 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- THE SIZE GATE RUNS BEFORE THE RANGE TEST, and its place keeps the spec
sound: `recvfrom(999, 0x10000, 2^47)` ends past `TASK_SIZE` only at its
full size, and `import_ubuf` (lib/iov_iter.c:1433-1442, v6.18.46) caps
the size to `MAX_RW_COUNT` (:1435-1436) before its range test (:1437), so
the range test passes and Linux answers the closed fd's -EBADF
(net/socket.c:2287-2288).  It declines.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_count_past_the_clamp_declines (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 999 65536 (Z_to_bv 64 (2 ^ 47)) 0 (fun _ => none))
        socket_call_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the -EFAULT a range test over the uncapped size would prove as
certain is refused: it is not Linux's answer.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_count_past_the_clamp_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 999 65536 (Z_to_bv 64 (2 ^ 47)) 0 (fun _ => none))
        socket_call_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A size of exactly `Uaccess.rw_bytes_max` is modeled: stdin is
-ENOTSOCK.
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_count_at_the_bound_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 0 4096 131072 0 wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …not a decline: `Uaccess.modeled_rw_count` admits the bound itself.
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_count_at_the_bound_unmodeled_rejected :
    ¬ syscall_spec (recvfrom_in 0 4096 131072 0 wmem_open) socket_call_model Unmodeled := by
  sys_refute

/-- A CLOSED fd with a good buffer is -EBADF.
probe: testing/syscall-check/tests/recv_spec.c#conform -- badfd -/
theorem recvfrom_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 9 4096 8 0 wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/recv_spec.c#reject --mutate recvfrom:ret=-ENOTSOCK -- badfd -/
theorem recvfrom_closed_fd_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 9 4096 8 0 wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- An OPEN non-socket is -ENOTSOCK: stdin here.
rocq-twin: recv_on_a_non_socket_descriptor
probe: testing/syscall-check/tests/recv_spec.c#conform -- notsock -/
theorem recvfrom_channel_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 0 4096 8 0 wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …with no byte of the destination written.
probe: testing/syscall-check/tests/recv_spec.c#reject --mutate recvfrom:smuggle-write:a1:1 -- notsock -/
theorem recvfrom_channel_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 0 4096 8 0 wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [(4096, [97])] []) m' evs) := by
  sys_refute

/-- …and never a short receive.
probe: testing/syscall-check/tests/recv_spec.c#reject --mutate recvfrom:ret=0 -- notsock -/
theorem recvfrom_channel_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 0 4096 8 0 wmem_open) socket_call_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A NULL DESTINATION is the descriptor's -ENOTSOCK as well: Linux's
`import_ubuf` tests NULL against the range alone (lib/iov_iter.c:1437,
v6.18.46), and qemu-user never locks it (linux-user/syscall.c:3692-3693,
QEMU 11.1.1), so the host's recvfrom answers on the fd.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_null_destination_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 0 0 8 0 (fun _ => none)) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …not -EFAULT.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_null_destination_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 0 0 8 0 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- MSG_PEEK changes nothing before the descriptor.
probe: testing/syscall-check/tests/recv_spec.c#conform -- peek -/
theorem recvfrom_peek_flag_is_not_read (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 0 4096 8 2 wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …nor is it a decline.
probe: testing/syscall-check/tests/recv_spec.c#conform -- peek -/
theorem recvfrom_peek_flag_unmodeled_rejected :
    ¬ syscall_spec (recvfrom_in 0 4096 8 2 wmem_open) socket_call_model Unmodeled := by
  sys_refute

/-- MSG_CMSG_COMPAT is not read either: `recvfrom(0, 4096, 8,
MSG_CMSG_COMPAT)` on stdin, over a destination qemu-user can lock, is
-ENOTSOCK.  `__sys_recvfrom` (net/socket.c:2270-2304, v6.18.46) tests no
flag before it resolves the fd (:2281-2291), unlike `__sys_recvmsg`
(:2909-2927), whose test is at :2915-2916, and qemu-user's `do_recvfrom`
hands `flags` to the host untranslated (linux-user/syscall.c:3711 or
:3716, QEMU 11.1.1)…
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_cmsg_compat_flag_is_not_read (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_rw_in 0 4096 8 (Z_to_bv 64 (2 ^ 31)) wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …so recvmsg's -EINVAL is refused here: no implementation gives it, since
qemu-user's only -EINVAL before the host call needs a non-NULL `src_addr`
(linux-user/syscall.c:3705-3708, QEMU 11.1.1).
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_cmsg_compat_flag_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_rw_in 0 4096 8 (Z_to_bv 64 (2 ^ 31)) wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- AT A CLOSED FD MSG_CMSG_COMPAT is not read either: `recvfrom(9, 4096,
8, MSG_CMSG_COMPAT)` is -EBADF, Linux testing no flag before the fd
(net/socket.c:2281-2291, v6.18.46) and qemu-user handing the flag to the
host's recvfrom untranslated (linux-user/syscall.c:3711 or :3716,
QEMU 11.1.1), which tests none before the fd either…
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_cmsg_compat_flag_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_rw_in 9 4096 8 (Z_to_bv 64 (2 ^ 31)) wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- …so recvmsg's -EINVAL is refused there too.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_cmsg_compat_flag_closed_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_rw_in 9 4096 8 (Z_to_bv 64 (2 ^ 31)) wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The flag word's HIGH HALF is dropped: `recvfrom(0, 4096, 8, 2^32)` is
-ENOTSOCK.  `SYSCALL_DEFINE6(recvfrom)` takes `unsigned int flags`
(net/socket.c:2306-2308, v6.18.46), which riscv's wrapper narrows through
`__SC_CAST` (arch/riscv/include/asm/syscall_wrapper.h:88, v6.18.46;
include/linux/syscalls.h:132, v6.18.46), and qemu-user's `do_recvfrom`
takes `int flags` (linux-user/syscall.c:3683, QEMU 11.1.1)…
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_high_flag_half_is_dropped (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_rw_in 0 4096 8 (Z_to_bv 64 (2 ^ 32)) wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …so an -EINVAL for the high half is refused.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_high_flag_half_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_rw_in 0 4096 8 (Z_to_bv 64 (2 ^ 32)) wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- AT A CLOSED FD a set high half is -EBADF too: `recvfrom(9, 4096, 8,
2^32)`.  Linux narrows it away (above) and resolves the fd
(net/socket.c:2285-2291, v6.18.46); qemu-user's `int flags` drops it and
the host answers on that fd (linux-user/syscall.c:3683, :3716,
QEMU 11.1.1)…
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_high_flag_half_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_rw_in 9 4096 8 (Z_to_bv 64 (2 ^ 32)) wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- …so an -EINVAL for the high half is refused there as well.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_high_flag_half_closed_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_rw_in 9 4096 8 (Z_to_bv 64 (2 ^ 32)) wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- AN UNMAPPED DESTINATION IN RANGE passes the range test, and the
descriptor answers before any byte would move.
probe: testing/syscall-check/tests/recv_spec.c#conform -- farbuf -/
theorem recvfrom_unmapped_buffer_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 0 46912512909312 8 0 (fun _ => none)) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …and -EFAULT is refused.  It is qemu-user's answer: `do_recvfrom`
(linux-user/syscall.c:3683-3741, QEMU 11.1.1) locks the destination
before the host call.  The refusal is Linux v6.18.46's order, carried
from Rocq and reported to the lead.
probe: testing/syscall-check/tests/recv_spec.c#reject --mutate recvfrom:ret=-EFAULT -- farbuf -/
theorem recvfrom_unmapped_buffer_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 0 46912512909312 8 0 (fun _ => none)) socket_call_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A READ-ONLY DESTINATION (readable, not writable) passes the range test
too, and the channel answers -ENOTSOCK.
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination unmapped and none can state a read-only one.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_read_only_buffer_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 207 [0, 4096, 8, 0, 0, 0] (fun _ => some 0) (fun _ => none))
        socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …and -EFAULT is refused.  It is qemu-user's answer: `do_recvfrom`
locks the destination with `VERIFY_WRITE` (linux-user/syscall.c:3695,
QEMU 11.1.1), which a read-only page fails.  The refusal is Linux
v6.18.46's order, carried from Rocq and reported to the lead.
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination unmapped and none can state a read-only one.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_read_only_buffer_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 207 [0, 4096, 8, 0, 0, 0] (fun _ => some 0) (fun _ => none))
        socket_call_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A WRITE-ONLY DESTINATION (writable, not readable), `recvfrom_in`'s own
shape and `recvfrom_channel_is_enotsock`'s input, is -ENOTSOCK too, and
-EFAULT is refused.  It is qemu-user's answer: `do_recvfrom` locks the
destination with `VERIFY_WRITE` (linux-user/syscall.c:3695, QEMU 11.1.1),
`PAGE_READ | PAGE_WRITE` (linux-user/qemu.h:185, QEMU 11.1.1), and
`page_check_range` fails a page without `PAGE_READ`
(accel/tcg/user-exec.c:538-541, QEMU 11.1.1).  The refusal is Linux
v6.18.46's order, carried from Rocq and reported to the lead.
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination unmapped and none can state a write-only one.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_write_only_buffer_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 0 4096 8 0 wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- Readable and writable below 65536 and nothing above: an `*addrlen` at
65536 cannot be read. -/
def recvfrom_low_mem : word → Option byte := fun a => if bv_ltu a 65536 then some 0 else none

/-- Readable and writable everywhere, with the `int` at 8200 equal to -1. -/
def recvfrom_neg_addrlen_mem : word → Option byte := fun a =>
  if bv_ltu a 8200 then some 0 else if bv_ltu a 8204 then some 255 else some 0

attribute [sys_simp low] recvfrom_low_mem.eq_1 recvfrom_neg_addrlen_mem.eq_1

/-- A NON-NULL `src_addr` BESIDE A READABLE, NONNEGATIVE `*addrlen` changes
nothing before the descriptor: `recvfrom(0, 4096, 8, 0, 8192, 8200)` on
stdin, `*addrlen` 0, is -ENOTSOCK.  Linux's `__sys_recvfrom` reads only
the value of the pointer `addr` before the receive (`msg.msg_name`,
net/socket.c:2276, v6.18.46) and dereferences `addr` and `addr_len` only
under `err >= 0 && addr != NULL` (:2297-2302), and qemu-user's
`do_recvfrom` reads `*addrlen` (linux-user/syscall.c:3700-3708,
QEMU 11.1.1), passes it to the host call (:3709-3712) and hands back the
host's answer on the fd…
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
probe: testing/syscall-check/tests/recv_spec.c#conform -- srcaddr -/
theorem recvfrom_source_address_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 207 [0, 4096, 8, 0, 8192, 8200] rmem_open rmem_open)
        socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …not -EINVAL, which neither gives there: qemu-user's needs a negative
`*addrlen` (linux-user/syscall.c:3705-3708, QEMU 11.1.1)…
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_source_address_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 207 [0, 4096, 8, 0, 8192, 8200] rmem_open rmem_open)
        socket_call_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and `*addrlen` is not written: Linux writes it only after a receive
(net/socket.c:2297-2302, v6.18.46), and qemu-user only after a host call
that did not fail (linux-user/syscall.c:3718-3733, QEMU 11.1.1).
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_source_address_addrlen_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 207 [0, 4096, 8, 0, 8192, 8200] rmem_open rmem_open)
        socket_call_model (Ok (mkEffect (errno_ret ENOTSOCK) [(8200, [0, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- AT A CLOSED FD the same call is -EBADF: `recvfrom(9, 4096, 8, 0, 8192,
8200)`, `*addrlen` 0.  Linux resolves the fd (net/socket.c:2285-2291,
v6.18.46) and never dereferences `addr` or `addr_len` off a socket
(:2297-2302), and qemu-user hands the host that fd after reading
`*addrlen` (linux-user/syscall.c:3700-3712, QEMU 11.1.1)…
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_source_address_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 207 [9, 4096, 8, 0, 8192, 8200] rmem_open rmem_open)
        socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- …so -EINVAL, which neither gives there, is refused…
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_source_address_closed_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 207 [9, 4096, 8, 0, 8192, 8200] rmem_open rmem_open)
        socket_call_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and so is a written `*addrlen`: Linux returns -EBADF
(net/socket.c:2287-2288, v6.18.46) before its only write (:2297-2302),
and qemu-user writes it only after a host call that did not fail
(linux-user/syscall.c:3718 and :3727-3733, QEMU 11.1.1).
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_source_address_closed_fd_addrlen_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 207 [9, 4096, 8, 0, 8192, 8200] rmem_open rmem_open)
        socket_call_model (Ok (mkEffect (errno_ret EBADF) [(8200, [0, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- AT THE READ-ONLY FILE at 3 the same call is -ENOTSOCK: `recvfrom(3,
4096, 8, 0, 8192, 8200)`, `*addrlen` 0.  Linux's `sock_from_file`
refuses a regular file (net/socket.c:2289-2291, v6.18.46) before any
dereference of `addr` or `addr_len` (:2297-2302), and qemu-user hands the
host that fd after reading `*addrlen` (linux-user/syscall.c:3700-3712,
QEMU 11.1.1)…
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_source_address_file_fd_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 207 [3, 4096, 8, 0, 8192, 8200] rmem_open rmem_open)
        socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …so -EINVAL, which neither gives there, is refused.
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_source_address_file_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 207 [3, 4096, 8, 0, 8192, 8200] rmem_open rmem_open)
        socket_call_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- AN UNREADABLE `*addrlen` beside a non-NULL `src_addr` is the
descriptor's -ENOTSOCK too: `recvfrom(0, 4096, 8, 0, 8192, 65536)` over a
view readable and writable below 65536 only.  That is Linux v6.18.46's
answer, `addr_len` untouched off a socket (net/socket.c:2297-2302), and
Rocq's (`Net.Socket.recvfrom_spec`), but not qemu-user's: `do_recvfrom`
reads `*addrlen` before the host call and answers -EFAULT
(linux-user/syscall.c:3700-3704, QEMU 11.1.1).  The twin proves Linux's
answer as certain there, a priority-1 residual inherited from Rocq and
reported to the lead…
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_unreadable_addrlen_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 207 [0, 4096, 8, 0, 8192, 65536] recvfrom_low_mem recvfrom_low_mem)
        socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …so qemu-user's -EFAULT, a real answer, is refused: the refusal is
Linux's order, carried from Rocq.
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_unreadable_addrlen_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 207 [0, 4096, 8, 0, 8192, 65536] recvfrom_low_mem recvfrom_low_mem)
        socket_call_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A NEGATIVE `*addrlen`, -1 at 8200, is -ENOTSOCK as well: Linux never
reads it off a socket (net/socket.c:2297-2302, v6.18.46), while
qemu-user's `(int)addrlen < 0` answers -EINVAL before the host call
(linux-user/syscall.c:3705-3708, QEMU 11.1.1), the same inherited
residual…
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_negative_addrlen_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 207 [0, 4096, 8, 0, 8192, 8200] recvfrom_neg_addrlen_mem
          recvfrom_neg_addrlen_mem) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …so qemu-user's -EINVAL, a real answer, is refused, as above.
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders its destination and `*addrlen` unmapped and none can state the mapped destination this view gives.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_negative_addrlen_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 207 [0, 4096, 8, 0, 8192, 8200] recvfrom_neg_addrlen_mem
          recvfrom_neg_addrlen_mem) socket_call_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A ZERO-LENGTH DESTINATION PAST `TASK_SIZE` is -EFAULT from the range
test before the fd, even on the channel.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_zero_length_past_task_size_is_efault (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 + 4096)) 0 0 (fun _ => none))
        socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) socket_call_model [] := by
  sys_norm

/-- …and -ENOTSOCK is refused.  It is qemu-user's answer on a host whose
own user range holds `g2h(buf)`: `do_recvfrom` locks even a zero-length
destination (linux-user/syscall.c:3692-3699, QEMU 11.1.1), `lock_user`
hands back `buf` plus `guest_base` (`g2h_untagged`, linux-user/uaccess.c:16,
QEMU 11.1.1), and `safe_recvfrom` passes that to the host (syscall.c:3716),
whose own `import_ubuf` range test runs before the fd.  On x86-64 that
test is `__access_ok`'s `valid_user_address`, `<= USER_PTR_MAX`
(arch/x86/include/asm/uaccess_64.h:56-57, :98-107, v6.18.46), which
`arch_cpu_finalize_init` sets to `TASK_SIZE_MAX`
(arch/x86/kernel/cpu/common.c:2592, v6.18.46): `2^47 - 4096` with
4-level paging, `2^56 - 4096` under LA57 (`task_size_max`,
arch/x86/include/asm/page_64.h:86-97, v6.18.46).  On arm64 it is
`access_ok` (arch/arm64/include/asm/uaccess.h:38-50, v6.18.46) into
`__access_ok` (include/asm-generic/access_ok.h:31-41, v6.18.46) against
`TASK_SIZE_MAX = 1 << VA_BITS` (arch/arm64/include/asm/processor.h:57,
v6.18.46), 2^48 at 48-bit VA.  So with `guest_base` 0 an LA57 x86-64
host or a 48-bit arm64 host answers -ENOTSOCK here, and a 4-level x86-64
host -EFAULT.  The refusal is Linux v6.18.46's order, carried from Rocq
and reported to the lead.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_zero_length_past_task_size_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 + 4096)) 0 0 (fun _ => none))
        socket_call_model (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- BESIDE A ZERO-LENGTH DESTINATION PAST `TASK_SIZE`, `src_addr` set and
`*addrlen` -1 at 8200, the answer is still the range test's -EFAULT, on
any fd: `__sys_recvfrom` imports the destination before it resolves the
fd or dereferences `addr` or `addr_len` (net/socket.c:2281-2283, ahead of
:2285-2291 and :2297-2302, v6.18.46), and `import_ubuf`'s `access_ok`
refuses it (lib/iov_iter.c:1433-1442, v6.18.46).  That is Linux's answer
and Rocq's (`Net.Socket.recvfrom_spec`), but not qemu-user's wherever
`buf` is at most `guest_addr_max` (`~0ul` without `-R`, `reserved_va`
under it, which riscv64 lets reach past `TASK_SIZE`: linux-user/main.c:109-120,
:839-842 and :847-853, target/riscv/cpu-param.h:11-12, QEMU 11.1.1) and
`g2h(buf)`, `buf` plus `guest_base`, is not NULL (linux-user/uaccess.c:16,
QEMU 11.1.1): `do_recvfrom`'s lock passes a zero-length destination there
(linux-user/syscall.c:3692-3699, linux-user/qemu.h:187-195,
accel/tcg/user-exec.c:502-504, QEMU 11.1.1), and `(int)addrlen < 0`
answers -EINVAL before any host call (linux-user/syscall.c:3705-3707,
QEMU 11.1.1).  The twin proves Linux's answer as certain there, a
priority-1 residual inherited from Rocq and reported to the lead…
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders `*addrlen` unmapped and none can state the negative one this view gives.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_negative_addrlen_zero_length_past_task_size_is_efault (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 207 [0, Z_to_bv 64 (2 ^ 47 + 4096), 0, 0, 8192, 8200]
          recvfrom_neg_addrlen_mem recvfrom_neg_addrlen_mem) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) socket_call_model [] := by
  sys_norm

/-- …so qemu-user's -EINVAL, a real answer, is refused: the refusal is
Linux's order, carried from Rocq…
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders `*addrlen` unmapped and none can state the negative one this view gives.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_negative_addrlen_zero_length_past_task_size_einval_rejected (m' : Model)
    (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 207 [0, Z_to_bv 64 (2 ^ 47 + 4096), 0, 0, 8192, 8200]
          recvfrom_neg_addrlen_mem recvfrom_neg_addrlen_mem) socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and so is the fd's -ENOTSOCK.
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders `*addrlen` unmapped and none can state the negative one this view gives.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_negative_addrlen_zero_length_past_task_size_enotsock_rejected (m' : Model)
    (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 207 [0, Z_to_bv 64 (2 ^ 47 + 4096), 0, 0, 8192, 8200]
          recvfrom_neg_addrlen_mem recvfrom_neg_addrlen_mem) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- AT A CLOSED FD the same call is -EFAULT too: Linux's range test runs
before its fd check (net/socket.c:2281-2283 ahead of :2287-2288,
v6.18.46).  Wherever qemu-user's lock passes the destination (above), its
-EINVAL there, before any host call, is the residual fd 0's pins above
carry…
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders `*addrlen` unmapped and none can state the negative one this view gives.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_negative_addrlen_zero_length_past_task_size_closed_fd_is_efault
    (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 207 [9, Z_to_bv 64 (2 ^ 47 + 4096), 0, 0, 8192, 8200]
          recvfrom_neg_addrlen_mem recvfrom_neg_addrlen_mem) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) socket_call_model [] := by
  sys_norm

/-- …so the fd's -EBADF is refused.
no-row: a recvfrom row captures no memory, since linux-process-semantics@ff0313ba4f:testing/syscall-check/main.ml records only what an arm reads and this one reads none, so every row renders `*addrlen` unmapped and none can state the negative one this view gives.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_negative_addrlen_zero_length_past_task_size_closed_fd_ebadf_rejected
    (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 207 [9, Z_to_bv 64 (2 ^ 47 + 4096), 0, 0, 8192, 8200]
          recvfrom_neg_addrlen_mem recvfrom_neg_addrlen_mem) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- A ZERO-LENGTH DESTINATION ON `TASK_SIZE`'s LAST PAGE passes the range
test (`addr <= limit - 0`), and the channel answers -ENOTSOCK.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_zero_length_last_page_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 - 8)) 0 0 (fun _ => none))
        socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …and -EFAULT is refused.  It is qemu-user's answer wherever `buf` is
past `guest_addr_max` (`reserved_va` under `-R`, linux-user/main.c:847-848;
`access_ok_untagged`, linux-user/qemu.h:187-195; both QEMU 11.1.1), or
`g2h(buf)` past the host's own user range: with `guest_base` 0 on a
4-level x86-64 host, whose `USER_PTR_MAX` is `2^47 - 4096`
(`arch_cpu_finalize_init`, arch/x86/kernel/cpu/common.c:2592;
`task_size_max`, arch/x86/include/asm/page_64.h:86-97; both v6.18.46),
the host's `import_ubuf` refuses `2^47 - 8` before the fd.  The refusal
is Linux v6.18.46's order, carried from Rocq and reported to the lead.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_zero_length_last_page_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 - 8)) 0 0 (fun _ => none))
        socket_call_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- Every other non-socket kind, arm by arm of `sockfd_lookup_errno`: a
regular file…
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 3 4096 8 0 wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_regular_file_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 3 4096 8 0 wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …a write-only file…
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_write_only_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 4 4096 8 0 wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_write_only_file_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 4 4096 8 0 wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …a directory…
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_directory_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 5 4096 8 0 wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_directory_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 5 4096 8 0 wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …a pipe's read end…
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_pipe_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 6 4096 8 0 wmem_open) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_pipe_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 6 4096 8 0 wmem_open) socket_kinds_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- A pipe's WRITE end at 6, the other end Rocq's
`socket_calls_on_a_pipe_end_are_enotsock` asks recvfrom on (`pipe_model`'s
fd 4), which `socket_kinds_model` does not hold. -/
def pipe_write_end_model : Model :=
  fixture_of (fds := [ (0, .FdChannel 0), (6, .FdPipe 7 true) ])

attribute [sys_simp low] pipe_write_end_model.eq_1

/-- …its write end, the same `pipeanon_fops`…
kernel: net/socket.c:__sys_recvfrom,sock_from_file; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem recvfrom_pipe_write_end_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 6 4096 8 0 wmem_open) pipe_write_end_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) pipe_write_end_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_pipe_write_end_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 6 4096 8 0 wmem_open) pipe_write_end_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …/dev/null…
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_devnull_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 7 4096 8 0 wmem_open) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_devnull_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 7 4096 8 0 wmem_open) socket_kinds_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and /dev/urandom.
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_urandom_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 8 4096 8 0 wmem_open) socket_kinds_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  sys_norm

/-- kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_urandom_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 8 4096 8 0 wmem_open) socket_kinds_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- A SOCKET DECLINES, fresh at 6: the entry point, not the state.
rocq-twin: recv_declines_a_socket_descriptor
probe: testing/syscall-check/tests/recv_spec.c#fail-closed -- sockfd -/
theorem recvfrom_fresh_socket_declines (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 6 4096 8 0 wmem_open) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- …handed -ENOTSOCK, the answer a wildcard would give, it still declines.
rocq-twin: recv_declines_a_socket_descriptor -/
theorem recvfrom_fresh_socket_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 6 4096 8 0 wmem_open) socket_states_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- THE RANGE VERDICT WRAPS THE SOCKET'S DECLINE: the same socket with a
kernel-half destination is -EFAULT, `import_ubuf` answering
(net/socket.c:2281-2283, v6.18.46) before the fd resolves.  qemu-user
agrees: `do_recvfrom` locks a non-NULL buffer for writing before the host
call (linux-user/syscall.c:3692-3699, QEMU 11.1.1).
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_high_buffer_on_a_socket_is_efault (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 6 (Z_to_bv 64 (2 ^ 63)) 1 0 (fun _ => none)) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) socket_states_model [] := by
  sys_norm

/-- …not the socket's decline.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_high_buffer_on_a_socket_unmodeled_rejected :
    ¬ syscall_spec (recvfrom_in 6 (Z_to_bv 64 (2 ^ 63)) 1 0 (fun _ => none)) socket_states_model
        Unmodeled := by
  sys_refute

/-- A SOCKET DECLINES connected at 9 too, its script already at
end-of-stream: the decline is the fd kind's, not the state's.
probe: testing/syscall-check/tests/socket_read_peer.c#fail-closed --expect-unmodeled recvfrom --peer 68656c6c6f -- recv -/
theorem recvfrom_connected_socket_declines (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 9 4096 8 0 wmem_open) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- …where `read`'s end-of-stream 0 is not admitted.
kernel: net/socket.c:sock_read_iter,__sys_recvfrom@v6.18.46 -/
theorem recvfrom_connected_socket_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 9 4096 8 0 wmem_open) socket_states_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and with a byte queued: `connected_socket_model`'s fd 4 holding "A"
ahead of its FIN, which Linux's `tcp_recvmsg` would copy out.  The decline
is the fd kind's, so it declines…
kernel: net/socket.c:__sys_recvfrom; net/ipv4/tcp.c:tcp_recvmsg@v6.18.46 -/
theorem recvfrom_established_socket_declines (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 4 4096 8 0 wmem_open)
        (connected_socket_model (NCons (Z_to_bv 8 65) NFin)) o ↔ o = Unmodeled := by
  sys_norm

/-- …and the byte's delivery is not admitted.
kernel: net/socket.c:__sys_recvfrom; net/ipv4/tcp.c:tcp_recvmsg@v6.18.46 -/
theorem recvfrom_established_socket_delivery_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_in 4 4096 8 0 wmem_open)
        (connected_socket_model (NCons (Z_to_bv 8 65) NFin))
        (Ok (mkEffect 1 [(4096, [Z_to_bv 8 65])] []) m' evs) := by
  sys_refute

/-- THE FD BEFORE THE HEADER: recvmsg on a closed fd with a kernel-half
`msg` is -EBADF.
rocq-twin: recv_argument_order_is_opposite
probe: testing/syscall-check/tests/recv_spec.c#conform -- msgbadfd -/
theorem recvmsg_closed_fd_beats_the_header (o : outcome SyscallEffect) :
    syscall_spec (recvmsg_in 999 (Z_to_bv 64 (2 ^ 63)) 0) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- …-EFAULT is recvfrom's order, and qemu-user's answer here:
`do_sendrecvmsg` (linux-user/syscall.c:3439-3454, QEMU 11.1.1) locks the
header before the fd is looked at.  The refusal is Linux v6.18.46's
order, carried from Rocq and reported to the lead (`recvmsg_spec`'s
docstring).
rocq-twin: recv_argument_order_is_opposite -/
theorem recvmsg_closed_fd_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvmsg_in 999 (Z_to_bv 64 (2 ^ 63)) 0) socket_call_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- An OPEN non-socket is -ENOTSOCK, the header never read.
probe: testing/syscall-check/tests/recv_spec.c#conform -- msghdrfirst -/
theorem recvmsg_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvmsg_in 3 (Z_to_bv 64 (2 ^ 63)) 0) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …not -EFAULT, qemu-user's answer for the same reason (the pin above).
probe: testing/syscall-check/tests/recv_spec.c#reject --mutate recvmsg:ret=-EFAULT -- msghdrfirst -/
theorem recvmsg_regular_file_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvmsg_in 3 (Z_to_bv 64 (2 ^ 63)) 0) socket_call_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- stdin: -ENOTSOCK.
rocq-twin: recv_on_a_non_socket_descriptor
probe: testing/syscall-check/tests/recv_spec.c#conform -- msgnotsock -/
theorem recvmsg_channel_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvmsg_in 0 4096 0) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- probe: testing/syscall-check/tests/recv_spec.c#reject --mutate recvmsg:smuggle-write:a1:1 -- msgnotsock -/
theorem recvmsg_channel_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvmsg_in 0 4096 0) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [(4096, [97])] []) m' evs) := by
  sys_refute

/-- MSG_CMSG_COMPAT declines, even on a non-socket: its value is a kernel
configuration.
rocq-twin: recv_on_a_non_socket_descriptor
probe: testing/syscall-check/tests/recv_spec.c#fail-closed -- msgcompat -/
theorem recvmsg_cmsg_compat_declines (o : outcome SyscallEffect) :
    syscall_spec (recvmsg_in 0 4096 (Z_to_bv 64 (2 ^ 31))) socket_call_model o ↔ o = Unmodeled := by
  sys_norm

/-- …-ENOTSOCK, the answer without CONFIG_COMPAT, is not admitted.
probe: testing/syscall-check/tests/recv_spec.c#fail-closed -- msgcompat -/
theorem recvmsg_cmsg_compat_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvmsg_in 0 4096 (Z_to_bv 64 (2 ^ 31))) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- The bit is read in the low 32: `2^32` there is zero, and the call goes
on to the descriptor.
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_high_flag_half_is_dropped (o : outcome SyscallEffect) :
    syscall_spec (recvmsg_in 0 4096 (Z_to_bv 64 (2 ^ 32))) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …not a decline.
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_high_flag_half_unmodeled_rejected :
    ¬ syscall_spec (recvmsg_in 0 4096 (Z_to_bv 64 (2 ^ 32))) socket_call_model Unmodeled := by
  sys_refute

/-- A SOCKET DECLINES, connected at 9.  The decline is the fd kind's, not
the state's, which is why the probe row, on a fresh socket, evidences it.
rocq-twin: recv_declines_a_socket_descriptor
probe: testing/syscall-check/tests/recv_spec.c#fail-closed -- msgsockfd -/
theorem recvmsg_connected_socket_declines (o : outcome SyscallEffect) :
    syscall_spec (recvmsg_in 9 4096 0) socket_states_model o ↔ o = Unmodeled := by
  sys_norm

/-- …handed -ENOTSOCK, it still declines.
rocq-twin: recv_declines_a_socket_descriptor -/
theorem recvmsg_connected_socket_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvmsg_in 9 4096 0) socket_states_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- The non-socket descriptors of the SAME model are still answered:
stdin at 0 is -ENOTSOCK from recvfrom…
rocq-twin: recv_declines_a_socket_descriptor
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_states_channel_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_in 0 4096 8 0 wmem_open) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model [] := by
  sys_norm

/-- …not declined with the sockets beside it.
rocq-twin: recv_declines_a_socket_descriptor
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_states_channel_unmodeled_rejected :
    ¬ syscall_spec (recvfrom_in 0 4096 8 0 wmem_open) socket_states_model Unmodeled := by
  sys_refute

/-- …and the regular file at 3 is -ENOTSOCK from recvmsg…
rocq-twin: recv_declines_a_socket_descriptor
kernel: net/socket.c:__sys_recvmsg,sock_from_file@v6.18.46 -/
theorem recvmsg_states_regular_file_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (recvmsg_in 3 4096 0) socket_states_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model [] := by
  sys_norm

/-- …not declined.
rocq-twin: recv_declines_a_socket_descriptor
kernel: net/socket.c:__sys_recvmsg,sock_from_file@v6.18.46 -/
theorem recvmsg_states_regular_file_unmodeled_rejected :
    ¬ syscall_spec (recvmsg_in 3 4096 0) socket_states_model Unmodeled := by
  sys_refute

/-! ### `fd32` on the four arms

Each of the four entry points takes an `int fd` — `__sys_sendto`
(net/socket.c:2210), `__sys_recvfrom` (:2270), `__sys_sendmsg` (:2700) and
`__sys_recvmsg` (:2909), v6.18.46 — and qemu-user's `do_sendto`,
`do_recvfrom` and `do_sendrecvmsg` take an `int fd` too
(linux-user/syscall.c:3636, :3683, :3439, QEMU 11.1.1), so the register's
high half is gone before the lookup.  The other pins in the send and
receive sections keep it clear, but for four that pass fd -1, whose high
half is set: `sendto_high_buffer_beats_the_fd`,
`sendto_edge_buffer_beats_the_fd` and their -EBADF refutations.  Those
cannot separate a table line without `fd32` from this one either: their
buffer fails `access_ok_zero` before the fd is read, and the low half,
`2^32 - 1`, is as closed in `fresh_socket_model` as `2^64 - 1`.

The four `*_fd_high_half_*` pairs below add bits at 32 and above only to
the fd they name (`2^32 + 3` for sendto and sendmsg, `2^32` for recvfrom
and recvmsg), leaving bits 16 to 31 clear, so a lookup narrowing the fd
further, to its low thirty-one or sixteen bits, drops them the same way.  Each arm's `*_fd_bit_31_*` pair sets bit 31, which
only a lookup keeping all thirty-two bits reads, and finds closed:
`fdget` takes the `int` as `unsigned int` (fs/file.c:1179-1182,
v6.18.46), and no table grows past `sysctl_nr_open_max`, which is below
`2^31` (:100-101). -/

/-- `sendto(2^32 + 3, …)` names the fresh socket at 3: -EPIPE…
kernel: net/socket.c:__sys_sendto; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_fd_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (sendto_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 1 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not -EBADF.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_fd_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 1 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `sendto(2^31 + 3, …)` keeps bit 31: `fdget` takes the `int` as
`unsigned int` (fs/file.c:1179-1182, v6.18.46), 2^31 + 3, past the
largest table `sysctl_nr_open_max` allows (:100-101), so the answer is
the closed fd's -EBADF (net/socket.c:2222-2224)…
kernel: fs/file.c:fdget; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_fd_bit_31_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (sendto_in (Z_to_bv 64 (2 ^ 31 + 3)) 4096 1 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not the socket at 3's -EPIPE, which a lookup narrowing the fd to its
low sixteen or thirty-one bits would find.
kernel: fs/file.c:fdget; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_fd_bit_31_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendto_in (Z_to_bv 64 (2 ^ 31 + 3)) 4096 1 16384 0 0 mem_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EPIPE) [] []) m' evs) := by
  sys_refute

/-- `sendmsg(2^32 + 3, …)` likewise: -EPIPE, header and descriptor
ledgered…
kernel: net/socket.c:__sys_sendmsg; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_fd_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in (Z_to_bv 64 (2 ^ 32 + 3)) 8192 16384 msg_ab) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
             fresh_socket_model [] := by
  sys_norm

/-- …not -EBADF.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_fd_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in (Z_to_bv 64 (2 ^ 32 + 3)) 8192 16384 msg_ab) fresh_socket_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `recvfrom(2^32, …)` names stdin: -ENOTSOCK, into a destination
readable and writable (`recvfrom_rw_in` over `wmem_open`), which
qemu-user can lock for writing, so its `do_recvfrom` reaches the host call
(linux-user/syscall.c:3695-3697, QEMU 11.1.1) and gives the same answer…
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_fd_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_rw_in (Z_to_bv 64 (2 ^ 32)) 4096 1 0 wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …not -EBADF.
kernel: net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_fd_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_rw_in (Z_to_bv 64 (2 ^ 32)) 4096 1 0 wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `recvmsg(fd, 8192, flags)` over a header qemu-user can lock for writing,
readable and writable at 8192, with one descriptor at 8320 naming a
zero-length buffer at 4096: its `lock_iovec` locks the descriptor array
for reading (linux-user/syscall.c:3097-3102, QEMU 11.1.1), which this view
makes readable, and never locks the zero-length buffer (:3116-3118).
There qemu-user reaches
the host call and gives the host's answer on the fd, as Linux does,
wherever `lock_iovec`'s `g_try_new0` allocates the one-entry host vector
(:3091-3095); where it cannot, qemu-user answers -ENOMEM without a host
call (:3375-3379), a Limits row
of the port.  The arm reads none of it. -/
def recvmsg_hdr_in (fd flags : word) : SyscallInput :=
  SyscallInput.mkInput 212 [fd, 8192, flags, 0, 0, 0]
    (send_msghdr_mem 0 0 1 0 0 0 [(4096, 0)]) (send_msghdr_mem 0 0 1 0 0 0 [(4096, 0)])

attribute [sys_simp low] recvmsg_hdr_in.eq_1

/-- `recvmsg(2^32, …)` names stdin: -ENOTSOCK, the header never read, and
qemu-user's answer too wherever its host vector is allocated: it locks
`recvmsg_hdr_in`'s header and reaches the host call, under the premise
`recvmsg_hdr_in` states…
kernel: net/socket.c:__sys_recvmsg,sock_from_file@v6.18.46 -/
theorem recvmsg_fd_high_half_discarded (o : outcome SyscallEffect) :
    syscall_spec (recvmsg_hdr_in (Z_to_bv 64 (2 ^ 32)) 0) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …not -EBADF.
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_fd_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvmsg_hdr_in (Z_to_bv 64 (2 ^ 32)) 0) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- MSG_CMSG_COMPAT declines AHEAD OF A CLOSED fd too: `recvmsg(999, 8192,
MSG_CMSG_COMPAT)`.  `__sys_recvmsg` tests the bit (net/socket.c:2915-2916,
v6.18.46) before `fd_empty` (:2920-2921), and the bit is a configuration:
0x80000000 under CONFIG_COMPAT, riscv64's default
(arch/riscv/Kconfig:1083-1086, v6.18.46), giving -EINVAL, and 0 without
it (include/linux/socket.h:337-341, v6.18.46), giving -EBADF; qemu-user
hands the bit to the host's recvmsg unchanged (linux-user/syscall.c:3405,
QEMU 11.1.1).  It declines…
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_cmsg_compat_closed_fd_declines (o : outcome SyscallEffect) :
    syscall_spec (recvmsg_hdr_in 999 (Z_to_bv 64 (2 ^ 31))) socket_call_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the -EBADF of a kernel built without CONFIG_COMPAT, which a spec
testing the fd before the flag word would prove as certain, is refused.
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_cmsg_compat_closed_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvmsg_hdr_in 999 (Z_to_bv 64 (2 ^ 31))) socket_call_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `recvmsg(0, 8192, 0)` over a header readable and writable at 8192 whose
`msg_iovlen` is 1025, one past `IOV_MAX`. -/
def recvmsg_iovlen_1025_in : SyscallInput :=
  SyscallInput.mkInput 212 [0, 8192, 0, 0, 0, 0]
    (send_msghdr_mem 0 0 1025 0 0 0 [(4096, 0)]) (send_msghdr_mem 0 0 1025 0 0 0 [(4096, 0)])

/-- …and over one whose `msg_iovlen` is 0. -/
def recvmsg_no_iov_in : SyscallInput :=
  SyscallInput.mkInput 212 [0, 8192, 0, 0, 0, 0]
    (send_msghdr_mem 0 0 0 0 0 0 []) (send_msghdr_mem 0 0 0 0 0 0 [])

attribute [sys_simp low] recvmsg_iovlen_1025_in.eq_1 recvmsg_no_iov_in.eq_1

/-- A `msg_iovlen` PAST `IOV_MAX` on stdin is -ENOTSOCK: `__sys_recvmsg`
resolves the fd (net/socket.c:2920-2924, v6.18.46) before
`___sys_recvmsg` reads the header.  That is Linux's answer and Rocq's
(`Net.Socket.recvmsg_spec`), but not qemu-user's: `do_sendrecvmsg_locked`
answers -EMSGSIZE for a count over `IOV_MAX` before any host call
(linux-user/syscall.c:3365-3371, QEMU 11.1.1), an errno its comment
chooses on purpose (:3366-3367), though the comment argues nothing about
answering ahead of the fd.  The twin proves Linux's answer as certain there, a
priority-1 residual inherited from Rocq and reported to the lead…
kernel: net/socket.c:__sys_recvmsg,sock_from_file@v6.18.46 -/
theorem recvmsg_iovlen_over_iov_max_channel_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec recvmsg_iovlen_1025_in socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …so qemu-user's -EMSGSIZE, a real answer, is refused: the refusal is
Linux's order, carried from Rocq…
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_iovlen_over_iov_max_channel_emsgsize_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec recvmsg_iovlen_1025_in socket_call_model
        (Ok (mkEffect (errno_ret EMSGSIZE) [] []) m' evs) := by
  sys_refute

/-- …and so is an -EINVAL, which no implementation gives there.
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_iovlen_over_iov_max_channel_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec recvmsg_iovlen_1025_in socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `recvmsg(9, 8192, 0)` over the same header, readable and writable, whose
`msg_iovlen` is 1025. -/
def recvmsg_iovlen_1025_closed_in : SyscallInput :=
  SyscallInput.mkInput 212 [9, 8192, 0, 0, 0, 0]
    (send_msghdr_mem 0 0 1025 0 0 0 [(4096, 0)]) (send_msghdr_mem 0 0 1025 0 0 0 [(4096, 0)])

attribute [sys_simp low] recvmsg_iovlen_1025_closed_in.eq_1

/-- AT A CLOSED FD the same header is -EBADF: `__sys_recvmsg` resolves the
fd (net/socket.c:2920-2924, v6.18.46) before `___sys_recvmsg` reads it.
qemu-user's -EMSGSIZE there (linux-user/syscall.c:3365-3371, QEMU 11.1.1)
is the residual stdin's pins above carry…
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_iovlen_over_iov_max_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec recvmsg_iovlen_1025_closed_in socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- …and -EINVAL, which no implementation gives there, is refused.
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_iovlen_over_iov_max_closed_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec recvmsg_iovlen_1025_closed_in socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `recvmsg(3, 8192, 0)` over the same header, readable and writable, whose
`msg_iovlen` is 1025: the read-only file at 3 of `socket_call_model`. -/
def recvmsg_iovlen_1025_file_in : SyscallInput :=
  SyscallInput.mkInput 212 [3, 8192, 0, 0, 0, 0]
    (send_msghdr_mem 0 0 1025 0 0 0 [(4096, 0)]) (send_msghdr_mem 0 0 1025 0 0 0 [(4096, 0)])

attribute [sys_simp low] recvmsg_iovlen_1025_file_in.eq_1

/-- AT A REGULAR FILE the same header is -ENOTSOCK: `__sys_recvmsg`'s
`sock_from_file` refuses it (net/socket.c:2922-2924, v6.18.46) before
`___sys_recvmsg` reads the header.  qemu-user's -EMSGSIZE there
(linux-user/syscall.c:3365-3371, QEMU 11.1.1) is the residual stdin's
pins above carry…
kernel: net/socket.c:__sys_recvmsg,sock_from_file@v6.18.46 -/
theorem recvmsg_iovlen_over_iov_max_file_fd_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec recvmsg_iovlen_1025_file_in socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …and -EINVAL, which no implementation gives there, is refused.
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_iovlen_over_iov_max_file_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec recvmsg_iovlen_1025_file_in socket_call_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A header with NO DESCRIPTORS, `msg_iovlen` 0, on stdin is -ENOTSOCK as
well, for the same order.  qemu-user's `lock_iovec` returns NULL with
`errno` 0 for a zero count (linux-user/syscall.c:3082-3085, QEMU 11.1.1),
and `do_sendrecvmsg_locked` answers that 0 for a receive without a host
call (:3373-3379), the same inherited residual…
kernel: net/socket.c:__sys_recvmsg,sock_from_file@v6.18.46 -/
theorem recvmsg_no_descriptors_channel_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec recvmsg_no_iov_in socket_call_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] := by
  sys_norm

/-- …so qemu-user's 0 is refused.
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_no_descriptors_channel_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec recvmsg_no_iov_in socket_call_model
        (Ok (mkEffect (Z_to_bv 64 0) [] []) m' evs) := by
  sys_refute

/-- `sendmsg(2^31 + 3, …)` keeps bit 31, as sendto's does: the closed fd's
-EBADF (net/socket.c:2709-2712, v6.18.46), before the header is copied…
kernel: fs/file.c:fdget; net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_fd_bit_31_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in (Z_to_bv 64 (2 ^ 31 + 3)) 8192 16384 msg_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not the socket at 3's -EPIPE, with the header and descriptor that
answer reads, which a lookup narrowing the fd to its low sixteen or
thirty-one bits would find.
kernel: fs/file.c:fdget; net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_fd_bit_31_epipe_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in (Z_to_bv 64 (2 ^ 31 + 3)) 8192 16384 msg_ab) fresh_socket_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)]) m' evs) := by
  sys_refute

/-- `recvfrom(2^31, …)` likewise: the range test passes and the fd is
closed, -EBADF (net/socket.c:2285-2288, v6.18.46), qemu-user's answer too
over the same readable and writable destination…
kernel: fs/file.c:fdget; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_fd_bit_31_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (recvfrom_rw_in (Z_to_bv 64 (2 ^ 31)) 4096 8 0 wmem_open) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- …not stdin's -ENOTSOCK, which a lookup narrowed to sixteen or
thirty-one bits finds at 0.
kernel: fs/file.c:fdget; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_fd_bit_31_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvfrom_rw_in (Z_to_bv 64 (2 ^ 31)) 4096 8 0 wmem_open) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- `recvmsg(2^31, …)` likewise: -EBADF (net/socket.c:2918-2921,
v6.18.46), and qemu-user's too over `recvmsg_hdr_in`'s header, under the
same allocation premise…
kernel: fs/file.c:fdget; net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_fd_bit_31_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (recvmsg_hdr_in (Z_to_bv 64 (2 ^ 31)) 0) socket_call_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] := by
  sys_norm

/-- …not stdin's -ENOTSOCK.
kernel: fs/file.c:fdget; net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_fd_bit_31_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (recvmsg_hdr_in (Z_to_bv 64 (2 ^ 31)) 0) socket_call_model
        (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-! ## The table

One pin per dispatched number.  The three declines this file carried for
198, 202 and 242 while their arms waited on `Fs.File.lowest_fd` are gone
with the arms landed; the register reader
(`tools/check_decline_registers.py`) compares what remains declined against
the table. -/

/-- kernel: include/uapi/asm-generic/unistd.h:__NR_socket@v6.18.46 -/
theorem socket_is_dispatched : (198 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_socketpair@v6.18.46 -/
theorem socketpair_is_dispatched : (199 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_bind@v6.18.46 -/
theorem bind_is_dispatched : (200 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_listen@v6.18.46 -/
theorem listen_is_dispatched : (201 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_accept@v6.18.46 -/
theorem accept_is_dispatched : (202 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_connect@v6.18.46 -/
theorem connect_is_dispatched : (203 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_getsockname@v6.18.46 -/
theorem getsockname_is_dispatched : (204 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_getpeername@v6.18.46 -/
theorem getpeername_is_dispatched : (205 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_sendto@v6.18.46 -/
theorem sendto_is_dispatched : (206 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_recvfrom@v6.18.46 -/
theorem recvfrom_is_dispatched : (207 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_shutdown@v6.18.46 -/
theorem shutdown_is_dispatched : (210 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_sendmsg@v6.18.46 -/
theorem sendmsg_is_dispatched : (211 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_recvmsg@v6.18.46 -/
theorem recvmsg_is_dispatched : (212 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_accept4@v6.18.46 -/
theorem accept4_is_dispatched : (242 : Int) ∈ modeled_sysnos := by decide



/-! ## The recv and send gates over every fd and model

Each pin below states its answer over every fd (every open non-socket fd,
for the two -ENOTSOCK pins) and every model, so a branch the arm takes only
on an fd kind or a model no fixture reaches cannot survive it (issue #1393,
item 1). -/

/-- For every fd, header pointer, readable memory view and model, sendmsg
with MSG_CMSG_COMPAT beside MSG_NOSIGNAL declines: with CONFIG_COMPAT
`__sys_sendmsg` answers -EINVAL before it looks at the fd, and without it
the bit is 0 and the call goes on to the fd, so no one answer is every
kernel's.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_cmsg_compat_flag_declines_everywhere (fd msgp : word)
    (mem : word → Option byte) (M : Model) (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in fd msgp (Z_to_bv 64 2147500032) mem) M o ↔ o = Unmodeled := by
  sys_norm
  all_goals (simp only [in_arg, List.getD_cons_succ, List.getD_cons_zero]; sys_norm)

/-- For every fd, header pointer and model, recvmsg with MSG_CMSG_COMPAT
and an empty memory view declines: with CONFIG_COMPAT `__sys_recvmsg`
answers -EINVAL before it looks at the fd, and without it the bit is 0 and
the call goes on to the fd, so no one answer is every kernel's.
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_cmsg_compat_declines_everywhere (fd msgp : word)
    (M : Model) (o : outcome SyscallEffect) :
    syscall_spec (recvmsg_in fd msgp (Z_to_bv 64 2147483648)) M o ↔ o = Unmodeled := by
  sys_norm
  all_goals (simp only [in_arg, List.getD_cons_succ, List.getD_cons_zero]; sys_norm)

/-- For every open non-socket fd in every model, recvfrom with a readable,
writable destination and source addrlen zero returns ENOTSOCK without changing the model.
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem recvfrom_nonsocket_fd_is_enotsock_everywhere (fd : word) (M : Model) (e : FdEntry)
    (he : fd_lookup (m_fds M) (fd32 fd) = some e) (hk : ∀ s, e ≠ .FdSocket s)
    (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 207 [fd, 4096, 8, 0, 8192, 8200] rmem_open rmem_open) M o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) M [] := by
  sys_norm
  all_goals simp only [in_arg, List.getD_cons_succ, List.getD_cons_zero]
  all_goals sys_norm
  simp only [m_fds] at he
  all_goals simp only [he]
  all_goals (cases e <;> first | (exact absurd rfl (hk _)) | sys_norm)

/-- For every open non-socket fd in every model, recvmsg over the readable,
writable header at 8192 (`recvmsg_iovlen_1025_in`'s) with msg_iovlen 1025
returns ENOTSOCK without changing the model.
kernel: net/socket.c:__sys_recvmsg,sock_from_file@v6.18.46 -/
theorem recvmsg_iovlen_1025_nonsocket_fd_is_enotsock_everywhere
    (fd : word) (M : Model) (e : FdEntry)
    (he : fd_lookup (m_fds M) (fd32 fd) = some e) (hk : ∀ s, e ≠ .FdSocket s)
    (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 212 [fd, 8192, 0, 0, 0, 0]
        (send_msghdr_mem 0 0 1025 0 0 0 [(4096, 0)])
        (send_msghdr_mem 0 0 1025 0 0 0 [(4096, 0)])) M o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) M [] := by
  sys_norm
  all_goals simp only [in_arg, List.getD_cons_succ, List.getD_cons_zero]
  all_goals sys_norm
  simp only [m_fds] at he
  all_goals simp only [he]
  all_goals (cases e <;> first | (exact absurd rfl (hk _)) | sys_norm)

/-- For every fd and model, recvfrom with a zero-length destination at
2^47 + 4096, past the Sv48 `TASK_SIZE` the model pins, and a negative
source addrlen returns EFAULT without changing the model.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_negative_addrlen_zero_length_past_task_size_is_efault_everywhere
    (fd : word) (M : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 207 [fd, Z_to_bv 64 (2 ^ 47 + 4096), 0, 0, 8192, 8200]
        recvfrom_neg_addrlen_mem recvfrom_neg_addrlen_mem) M o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) M [] := by
  sys_norm
  all_goals (simp only [in_arg, List.getD_cons_succ, List.getD_cons_zero]; sys_norm)

/-- For every fd and model, recvfrom with a one-byte destination at 2^63
and a non-null source address returns EFAULT without changing the model.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_high_buffer_source_address_is_efault_everywhere
    (fd : word) (M : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 207 [fd, Z_to_bv 64 (2 ^ 63), 1, 0, 8192, 8200]
        rmem_open rmem_open) M o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) M [] := by
  sys_norm
  all_goals (simp only [in_arg, List.getD_cons_succ, List.getD_cons_zero]; sys_norm)

def t172_msg_unreadable_head : word → Option byte :=
  send_msghdr_mem 0 0 1 0 0 0 [(12288, 1)]

def t172_msg_negative_after_unreadable_head : word → Option byte :=
  send_msghdr_mem 0 0 2 0 0 0 [(12288, 1), (4096, Z_to_bv 64 (2 ^ 63))]

def t172_msg_negative_after_readable_head : word → Option byte :=
  send_msghdr_mem 0 0 2 0 0 0 [(4096, 1), (4097, Z_to_bv 64 (2 ^ 63))]

attribute [sys_simp low] t172_msg_unreadable_head.eq_1
  t172_msg_negative_after_unreadable_head.eq_1 t172_msg_negative_after_readable_head.eq_1

/-- A negative LOW half of `addrlen` is read by nothing: with `addr` NULL
`__sys_sendto` never looks at it, so the fresh socket answers -EPIPE.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_negative_low_addrlen_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 16384 0 (Z_to_bv 64 (2 ^ 31)) mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not a decline: bit 31 of `addrlen` carries no gate.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_negative_low_addrlen_unmodeled_rejected :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 (Z_to_bv 64 (2 ^ 31)) mem_ab) fresh_socket_model
      Unmodeled := by
  sys_refute

/-- An unreadable but IN-RANGE buffer reaches the fd: `import_ubuf`'s
`access_ok` is a range test and reads no byte, so the closed 9 answers
-EBADF.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_unreadable_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 9 12288 1 16384 0 0 mem_ab) fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not a decline: nothing reads the buffer before the fd.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_unreadable_closed_fd_unmodeled_rejected :
    ¬ syscall_spec (sendto_in 9 12288 1 16384 0 0 mem_ab) fresh_socket_model Unmodeled := by
  sys_refute

/-- An unreadable PAYLOAD under a readable descriptor is the socket's
answer: `copy_iovecs_aux` reads the descriptor array alone, so the import
succeeds and the fresh socket answers -EPIPE with the header and the one
descriptor ledgered.
kernel: lib/iov_iter.c:__import_iovec,copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_unreadable_segment_zero_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 t172_msg_unreadable_head) fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
        [(8192, 56), (8320, 16)]) fresh_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: lib/iov_iter.c:__import_iovec,copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_unreadable_segment_zero_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 t172_msg_unreadable_head) fresh_socket_model
      Unmodeled := by
  sys_refute

/-- A later negative `iov_len` behind an unreadable first payload is
-EINVAL all the same: the walk reads descriptors, not payloads, and the
first error in INDEX ORDER decides the call.
kernel: lib/iov_iter.c:__import_iovec,copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_negative_after_unreadable_head_is_einval (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 t172_msg_negative_after_unreadable_head)
      fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] []
        [(8192, 56), (8320, 16), (8336, 16)]) fresh_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: lib/iov_iter.c:__import_iovec,copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_negative_after_unreadable_head_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 t172_msg_negative_after_unreadable_head)
      fresh_socket_model Unmodeled := by
  sys_refute

/-- The readable zero header leaves the closed-fd answer intact.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_zero_header_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 9 8192 16384 (bytes_at 8192 (List.replicate 56 0)))
      fresh_socket_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- The readable zero header gives no header fault ahead of the closed fd.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_zero_header_closed_fd_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 9 8192 16384 (bytes_at 8192 (List.replicate 56 0)))
      fresh_socket_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- The readable first payload preserves EINVAL for the second negative length.
kernel: lib/iov_iter.c:__import_iovec,copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_negative_after_readable_head_is_einval (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 t172_msg_negative_after_readable_head)
      fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] []
        [(8192, 56), (8320, 16), (8336, 16)]) fresh_socket_model [] := by
  sys_norm

/-- The readable descriptors and first payload give no fault ahead of the negative length.
kernel: lib/iov_iter.c:__import_iovec,copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_negative_after_readable_head_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 t172_msg_negative_after_readable_head)
      fresh_socket_model (Ok (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] []
        [(8192, 56), (8320, 16), (8336, 16)]) m' evs) := by
  sys_refute

/-- The readable header and payload preserve the channel-fd ENOTSOCK answer.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_prehost_channel_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 1 8192 16384 msg_ab) accepted_socket_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) accepted_socket_model [] := by
  sys_norm

/-- AN UNMAPPED BUT IN-RANGE BUFFER IS THE SOCKET'S ANSWER, NOT THE
BUFFER'S.  `access_ok` passes the range and reads no byte, so the fd
resolves and the socket's state decides.  On the accepted CONNECTION this
twin declines every connected state (the spec's send section), so neither
the copy's -EFAULT nor -EPIPE stands there; on the LISTENING socket, which
has no connection, `sk_stream_wait_connect` answers -EPIPE with the ledger
empty.  That is what separates the two: the socket's state, not the buffer.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_unmapped_buffer_in_range_connected_declines (o : outcome SyscallEffect) :
    (syscall_spec (sendto_in 4 46912512909312 1 16384 0 0 (fun _ => none))
      accepted_socket_model o ↔ o = Unmodeled) ∧
    (syscall_spec (sendto_in 3 46912512909312 1 16384 0 0 (fun _ => none))
      listening_socket_model o ↔
        o = Ok (mkEffect (errno_ret EPIPE) [] []) listening_socket_model []) := by
  constructor <;> sys_norm

/-- The high address-length bit is discarded before the dead socket answers.
kernel: net/socket.c:__sys_sendto; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_addrlen_high_sign_is_ignored (o : outcome SyscallEffect) :
    syscall_spec (sendto_in 3 4096 1 16384 0 (Z_to_bv 64 (2 ^ 63)) mem_ab)
      fresh_socket_model o ↔ o = Ok (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model [] := by
  sys_norm

/-- The discarded high address-length bit does not force a decline.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem sendto_addrlen_high_sign_unmodeled_rejected :
    ¬ syscall_spec (sendto_in 3 4096 1 16384 0 (Z_to_bv 64 (2 ^ 63)) mem_ab)
      fresh_socket_model Unmodeled := by
  sys_refute

/-- The closed fd answers before the header is copied, so a later
unreadable payload cannot matter.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_later_unreadable_segment_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 9 8192 16384 (send_msghdr_mem 0 0 2 0 0 0 [(4096, 1), (12288, 1)]))
      fresh_socket_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- The later unreadable payload does not force a decline ahead of this closed fd.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_later_unreadable_segment_closed_fd_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 9 8192 16384 (send_msghdr_mem 0 0 2 0 0 0 [(4096, 1), (12288, 1)]))
      fresh_socket_model Unmodeled := by
  sys_refute

/-- THE FD IS RESOLVED BEFORE THE HEADER, so a header at `2^63` on a
CLOSED fd is -EBADF and the header is never read — the opposite of
`sendto`, where the buffer's range is judged first.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_kernel_range_header_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 9 (Z_to_bv 64 (2 ^ 63)) 16384 rmem_open)
      fresh_socket_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] := by
  sys_norm

/-- …not a decline, and not the header's -EFAULT.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_kernel_range_header_closed_fd_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 9 (Z_to_bv 64 (2 ^ 63)) 16384 rmem_open)
      fresh_socket_model Unmodeled := by
  sys_refute

/-- A later unreadable PAYLOAD does not stop the import: `copy_iovecs_aux`
reads the two descriptors and nothing else, so the fresh socket answers
-EPIPE with the header and both descriptors ledgered.
kernel: lib/iov_iter.c:__import_iovec,copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_later_unreadable_segment_socket_is_epipe (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 (send_msghdr_mem 0 0 2 0 0 0 [(4096, 1), (12288, 1)]))
      fresh_socket_model o ↔
      o = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
        [(8192, 56), (8320, 16), (8336, 16)]) fresh_socket_model [] := by
  sys_norm

/-- …not a decline.
kernel: lib/iov_iter.c:__import_iovec,copy_iovec_from_user@v6.18.46 -/
theorem sendmsg_later_unreadable_segment_socket_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 (send_msghdr_mem 0 0 2 0 0 0 [(4096, 1), (12288, 1)]))
      fresh_socket_model Unmodeled := by
  sys_refute

/-! ## A17: FdFileRW and FdFileA -/

def a17_socket_model : Model :=
  fixture_of (fds := [(3, .FdFileRW [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_socket_model.eq_1

/-- Rocq: `Socket.sock_fd`, Socket.v:1006 at 96c2debdb.
An O_RDWR regular file is not a socket: `sockfd_lookup` (net/socket.c,
Linux v6.18.46) turns `sock_from_file`'s miss, an `f_op` other than
`socket_file_ops`, into -ENOTSOCK.
kernel: net/socket.c:sockfd_lookup@v6.18.46 -/
theorem a17_rdwr_sock_fd_enotsock :
    sock_fd a17_socket_model 3 = .inr ENOTSOCK := by
  rfl

/-- Rocq: `Socket.sockfd_lookup_errno`, Socket.v:2085 at 96c2debdb.
An O_RDWR regular file fails the socket-file test in net/socket.c,
sock_from_file, Linux v6.18.46; __sys_sendmsg turns that failure into
-ENOTSOCK.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem a17_rdwr_lookup_enotsock :
    sockfd_lookup_errno [(3, .FdFileRW [102] 0)] 3 = some ENOTSOCK := by
  rfl

/-- `sendmsg` through a read-write file is -ENOTSOCK, the answer every
non-socket kind gets: `__sys_sendmsg` (net/socket.c, Linux v6.18.46) looks
the socket up first, and `sock_from_file` (net/socket.c:530-536) is the one
comparison `file->f_op == &socket_file_ops`, which an `FdFileRW` fails as an
`FdFile` does.  So this pin and `sendmsg_regular_file_is_enotsock` agree, and
a mutant that treats this kind as a socket fails here.

Its flags word is MSG_NOSIGNAL because `send_flags_modeled` declines every
other word ahead of the fd lookup, where no kind is told apart.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem a17_rdwr_sendmsg_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_ab) a17_socket_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) a17_socket_model [] := by
  sys_norm

/-- …and the decline the twin used to give there is refused.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem a17_rdwr_sendmsg_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ab) a17_socket_model Unmodeled := by
  sys_refute

def a17_socket_append_model : Model :=
  fixture_of (fds := [(3, .FdFileA [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_socket_append_model.eq_1

/-- Rocq: `Socket.sock_fd`, Socket.v:1005 at 96c2debdb.
An append-mode regular file is not a socket: `sockfd_lookup` (net/socket.c,
Linux v6.18.46) turns `sock_from_file`'s miss, an `f_op` other than
`socket_file_ops`, into -ENOTSOCK.
kernel: net/socket.c:sockfd_lookup@v6.18.46 -/
theorem a17_append_sock_fd_enotsock :
    sock_fd a17_socket_append_model 3 = .inr ENOTSOCK := by
  rfl

/-- Rocq: `Socket.sockfd_lookup_errno`, Socket.v:2084 at 96c2debdb.
An append-mode regular file fails the socket-file test in net/socket.c,
sock_from_file, Linux v6.18.46; __sys_sendmsg turns that failure into
-ENOTSOCK.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem a17_append_lookup_enotsock :
    sockfd_lookup_errno [(3, .FdFileA [102] 0)] 3 = some ENOTSOCK := by
  rfl

/-- `sendmsg` through an append-mode file is -ENOTSOCK, for
`a17_rdwr_sendmsg_is_enotsock`'s reason: `sock_from_file`
(net/socket.c:530-536, Linux v6.18.46) is one comparison against
`socket_file_ops`, which an `FdFileA` fails as an `FdFileW` does, and
`__sys_sendmsg` answers it before the header is read.

That call is the one `sendmsg_write_only_file_is_enotsock` pins, with
MSG_NOSIGNAL for the reason `a17_rdwr_sendmsg_is_enotsock` gives.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem a17_append_sendmsg_is_enotsock (o : outcome SyscallEffect) :
    syscall_spec (sendmsg_in 3 8192 16384 msg_ab) a17_socket_append_model o ↔
      o = Ok (mkEffect (errno_ret ENOTSOCK) [] []) a17_socket_append_model [] := by
  sys_norm

/-- …and the decline the twin used to give there is refused.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem a17_append_sendmsg_unmodeled_rejected :
    ¬ syscall_spec (sendmsg_in 3 8192 16384 msg_ab) a17_socket_append_model Unmodeled := by
  sys_refute

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Net.Socket
