(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module names changed; 358 of its 430 lines of code are new or changed and 371 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickCut.v, with its module paths and module names changed; 203 of its 254 lines of code are new or changed and 379 lines of the source are left out. *)
(* diginet_session_tick_cg: image B's ASan walk contract of diginet_session_tick (transport/src/diginet_session.c:
   414-472, with session_lost (:160-165), retransmit (:403-412), send_raw (:88-94) and ms (:77) inlined and set_state
   (:79-86) CALLED; model lib/TModel/TSess.v diginet_session_tick_m, retransmit_m, session_lost_m, set_state_m,
   send_raw_m, and lib/TModel/TSess0.v take_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x8909c =
   transportb_sigma TB_diginet_session_tick, size 2640, as STATEMENTS only (no proof). It stores into g_s, a harness
   global, takes a class-5 side-stack frame for its three locals (the struct diginet_notice n of the ack-lost arm, the
   keepalive byte ka and the body buffer body[1484]), calls set_state, take and send_data (G-form callees), calls
   notice through the session's notify pointer and io_send through its send pointer (the inlined send_raw of
   retransmit), so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx
   (image-free) over G = lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post is
   lib/A/Prog/TransportGCg.v transport_cg_post (image-free; acall_kept_g over G_HARNESS_B). Form: image A's
   lib/A/Prog/diginet_session_tick_cg.v at image B's names; the out cells it gives take (body_len, has_display) lie in
   its OWN machine frame, so they are not out cells of this statement: take_cg.v's post hands them back, and this walk
   reads them. The frame is released by a CALL of __asan_stack_free_5, and the locals are marked usable and out of
   scope by calls of __asan_set_shadow_00 / _f8; those two callee texts are lib/A/Prog/TransportRtCg.v
   (aset_shadow_realizes, astack_free_cls_realizes: image-free, each a text at the entry's pc, so image B's walk
   takes them at transportb_sigma's values and needs no twin of that file). The differences are listed at the end of
   this comment.

   The contract. a0 = s = &g_s = 0x5df640 (TWorldB.v TB_g_s), a1 = now (uint64_t). TF is the current heap frame
   (check_state_data_cg.v trans_tframe_at at this call's window); the read-only bytes the callees' callees read are
   the image's (trans_rom_view_rd). The memory relates to the world Bw by image B's world relation (TWorldG.v tw_at at
   TWorldB.v TMAP_B, read through aview), g_fail_next Bw <= 1, and diginet_session_tick_m timg_B TF Bw now =
   Some (Bw', r). No byte the call stores is a byte of TF (tick_apart). Class 5 of the side stack has a free frame
   (its own), class 0 one (send_data's) and class 2 one (set_state's on a lost arm; diginet_body_check's inside take
   and inside diginet_frame_build inside send_data; never two at once, so one free frame covers them all). The
   function returns to ra with a0 = r (sign-extended), the callee-saved registers kept, no allocator event and no
   meter charge (its side-stack frame changes the state's st_fs only: ameter_fs_laws), its side-stack frame released
   (the caller's frames exactly), the caller's blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at
   or above alloc_ceiling outside the call's stack window [sp - TICK_STK, sp), the image bytes outside G, the owned
   statics and errno, the caller's block and frame bytes outside tick_wr Bw), the world relation at Bw', and
   g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/U/Prog/T/diginet_session_tick_c.v): a0 =
   W_BASE_UBSAN + OFF_g_s -> a0 = TB_g_s; a1 = now with 0 <= now < 2 ^ 64, kept; wmem -> tw_at; g_fail_next B <= 1
   kept as a premise (set_state's, send_data's and io_send's statements ask it), and the post's g_fail_next B' <= 1
   kept in X (set_state's and send_data's X give it; io_send's model gives 0 after its own; on a path with no send and
   no set_state the byte is not written: the g_s stores, the N_ACK_LOST notice (it writes M.fly.on) and take's stores
   leave it alone); diginet_session_tick_m verbatim at timg_B (timg_ubsan -> timg_B); tframe_at -> trans_tframe_at at
   TICK_STK, and its off_world clause -> tick_apart (set_state_cg.v sstate_apart's form); relro_img ->
   trans_rom_view_rd; stk, lo + FRAME <= sp, sp mod 16 and w_off_stack -> the journal's window premises; mem_inv is
   dropped. The post's munch, wmono, stk and mem_inv -> transport_cg_post (the journal at the return, acall_kept_g
   over tick_wr Bw); wmem -> X's tw_at.

   Premises the plain contract does not have:
   - count_cid 5 (frames Sc) < fs_frames 5 (its own class-5 frame), count_cid 0 (frames Sc) < fs_frames 0 (send_data's
     class-0 frame, whose statement asks it at its call state, where the frames are the own class-5 frame ::
     frames Sc, so the class-0 count is unchanged) and count_cid 2 (frames Sc) < fs_frames 2 (set_state's class-2
     frame on a lost arm, and diginet_body_check's class-2 frame inside take and inside diginet_frame_build inside
     send_data; set_state's, take's and send_data's statements each ask the class-2 count at their call state, where
     the class-2 count is again unchanged). With the first __asan_stack_malloc_5 returns a frame
     (astack_malloc_realizes), so the real-stack arm is not taken and the three locals lie in the own side-stack
     frame.
   - tick_apart (above).
   (The plain contract's relro_img is translated above as trans_rom_view_rd W memc: set_state's, notice's, io_send's
     and send_data's premise, taken at entry. It still holds at each call: the stack malloc's acall_kept and each
     callee's acall_kept_g keep every TRANS_RO_RD byte (trans_ro_rd_scoped, from trans_ro_rd_unowned and
     trans_rom_no_errno), the memset and the shadow fills keep every byte outside their destination and the ESTACK
     window, and no store of this function reaches a read-only byte.)
   - the two cfg bounds take asks, 1 <= S_cfg_max_cmds and 1 <= S_cfg_max_body, at the world take is called with
     (tick_tail's take_m argument): the walk needs them on its own Bw and carries them, since tick writes no byte of
     g_s.cfg on any path before the call (the stores are inflight, inflight_retries, inflight_frame[26], [27],
     inflight_sent_us, desk_counter_valid, next_keepalive_us, display_sent, last_display_us and the stats counters;
     g_s.cfg is [s, s + 60)), and neither does any callee before it (io_send and notice write M, GOT, g_cmd, g_q, g_nq,
     g_fail_next, g_last_counter; set_state, reached only on a lost arm, which returns, writes g_s.state and GOT).
   - in the holds statement: trans_tick_cells (g_s's zero shadow), the side-stack laws, and trans_g_unowned,
     trans_g_no_errno, trans_ro_rd_unowned and trans_rom_no_errno (send_data_cg.v's form): they carry TF's
     trans_src_ok (inside trans_tframe_at) across the stack malloc (DgnTransportBCg.v trans_src_ok_inner, the stack
     malloc adding the own frame and keeping the blocks, TF's bytes kept by its acall_kept and its decode_rd_ok by
     trans_rd_ok_sh, TF apart from the fresh frame and that frame's shadow: trans_src_ok_disj_own) to set_state and to
     the notice call, the only readers of TF; no set_state or notice call
     follows io_send (0x894c0), send_data (0x89830, 0x898c0) or take (0x89874) on any path, so TF is carried across no
     acall_kept_g and needs no fact that it lies outside G. They carry the body / ka / notice ranges' placement across
     the stack malloc's acall_kept and across each callee's acall_kept_g (its core trans_src_ok_kept, clause by clause
     over what acall_kept_g keeps: trans_src_ok_acall_g itself asks every byte of G to be kept, which a callee that
     writes G does not give), the TRANS_RO_RD bytes, and G (TransportGCg.v gx_kept_of_acall_kept with gx_ok and
     gx_noerrno, which DgnTransportBCg.v G_HARNESS_gx_ok and G_HARNESS_gx_noerrno give from the first two).
   Run invariants carried (on its own Bw): (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME and (4)
   every PENDING command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX (io_send's and send_data's premises),
   (2) every queued command has S_queue_len Bw i <= DIGINET_CMD_MAX_LEN for i < S_queued Bw and (5)
   1 <= S_cfg_max_cmds Bw and 1 <= S_cfg_max_body Bw (take's premises; (5) is the fifth run invariant, which
   diginet_session_tick carries up, here as its two conjuncts, the form take_cg.v states). Each is carried to the
   world of the call that needs it: the invariants read M.fly.on (world offsets 0x60 .. 0x63), M.fly.len (0x668 ..
   0x66f), g_ncmd (0xfdd8 ..), g_cmd's st / len fields (0x4dc8 ..), g_s.queue (0x670 + 1760 ..), g_s.queued
   (0x670 + 18144 ..) and g_s.cfg (0x670 ..); between Bw and each call this function writes only the g_s fields listed
   above (none of them cfg, queue or queued) and the callees before it write M.fly.on to 0 (the N_ACK_LOST notice,
   TCb.v notice_m, which makes (1) vacuous at the later send) or bytes of M / GOT / g_q / g_nq / g_cmd.st, so each
   invariant holds at the world of the call that asks it. That needs the two index bounds stated beside (2) and (4),
   TW.S_queued Bw <= TC.QUEUE_MAX and TW.g_ncmd Bw <= TC.CMDS_MAX: past them g_s.queue[i] (i >= 512) and g_cmd[s]
   (s >= 1024) are other world bytes (g_s's stats, g_cmd, g_q, GOT, ...), which this function and those callees
   write (A_S_queue_len 514 is g_s.stats.tx_retransmits, which this function stores at 0x8946c, and 513 is
   g_s.stats.tx_data, which send_data stores at 0x89fbc; GOT.t[5].old, a notice's store, is A_Cmd_st 1131: TWorld.v's
   offsets, the same world for both images), so (2) and (4) without the bounds could not be carried across them. No
   entry of g_s.queue or g_cmd is read by this function's own code (it reads queued only, 0x89744): take reads queued
   (0x8a200) and queue[i].len (0x8a2d0) for i < queued (take_cg.v), and
   io_send's check_latest_sent reads g_cmd[s].len (0x849c8 - 0x849e0) for a serial s < g_ncmd that tagged_of tests
   (check_latest_sent_cg.v). Image B's set_state (a function here; image A inlines it in session_lost) writes
   g_s.state and, through its N_STATE notice, GOT.t[GOT.n] and GOT.n: GOT bytes, not an index of g_cmd or g_q; it is
   called only on a lost arm (0x8951c), which returns, so no call that asks an invariant follows it, and set_state
   itself carries none, so it takes neither bound. No function this one calls writes g_ncmd, and take only lowers
   queued (TSess0.v take_m stores the count it keeps: lib/TSim/TickTakeW.v te_queued), so both bounds hold at each
   call; the caller has them from the plain run (lib/TSim/Agree.v d3_ncmd and d3_ops, OPS_MAX = CMDS_MAX;
   lib/TSim/Deadline.v queued_le). io_send does write g_cmd's st fields (io_send_cg.v iosend_wr), which (4) reads,
   but no second call needs (4) after it: the only io_send call is the inlined send_raw
   of retransmit, and on that path S_inflight is still not 0 (neither retransmit nor io_send writes g_s.inflight), so
   the tail test at 0x89670 - 0x8967c returns at 0x896a0 (TSess.v, :445). After the N_ACK_LOST notice (which sets
   M.fly.on to 0, so (1) is vacuous at the later send) and after take (which writes only the queue and queued), the
   walk re-derives (1) and (4) for the later send from the model's world, not from a callee's X. set_state carries
   none (its notice has kind N_STATE: set_state_cg.v). The others (check_latest_queue's own, check_state_data's body
   range) are not asked of this function: take carries none, and the notice it makes itself has kind N_ACK_LOST, so
   notice's N_DATA premise is vacuous. diginet_session_tick's own accesses are at fixed offsets of g_s (s + 24 ..
   s + 243, s + 1736 .. s + 1759, s + 18144, s + 18192 .. s + 18247) and of its own frames, and its one memset fills
   64 bytes of its own frame, so its code needs no bound the model does not give.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 2640 code bytes and the 55 bytes of its frame
   description at 0x1a5d9 are equal in both files), 660 words:
     0x8909c - 0x890d8 sp = sp - 192; 0x890a0 stores 8 zero bytes at sp; ra at sp + 184, s0 .. s11 at sp + 176 ..
                      sp + 88, loaded back at 0x896d8 - 0x89708; s0 = sp + 192 (the entry sp, kept to 0x896d4).
     0x890dc - 0x890e0 sp = sp & -32 (at most 0x10 below entry - 192); s1 = the realigned sp.
     0x890e4          the 8-byte store of now (a1) at s1 + 56 (its own machine frame; read back at 0x89294, 0x8932c,
                      0x89398, 0x89448, 0x89698, 0x8972c, 0x8979c, 0x897e4, 0x897ec, 0x8982c, 0x898a8, 0x898bc).
     0x890e8 - 0x89100 a2 = the 8-byte load of the GOT word 0xa3d48 (it holds 0xac680), then the 4-byte load of the
                      flag word at 0xac680; a1 = the 8-byte load of the GOT word 0xa3cf0 (it holds 0xac678), s8 = the
                      8-byte load at 0xac678 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s4 = s.
     0x89104 - 0x89118 the flag word = 0 goes to 0x89118 (s2 = 0); transport_cells row 6 gives 1. a0 = 0x700 = 1792
                      and the call of __asan_stack_malloc_5 (frame_alloc_5, 0x3dd40 = transportb_sigma
                      TB___asan_stack_malloc_5) at 0x8910c, return address 0x89110: a class-5 side-stack frame
                      (fs_frame_bytes 5 = 2048 bytes); s2 = the result.
     0x8911c - 0x8913c s11 = s2; s2 <> 0 goes to 0x89140. The real-stack arm (s2 = 0): s11 = (sp - 1792) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s11), then sp = s11. With
                      count_cid 5 (frames Sc) < fs_frames 5 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s11 = s2.
     0x89140          the 8-byte store of frame at s1 + 64 (its own machine frame).
     0x89144 - 0x8916c the frame header: 0x41b58ab3 at frame, the description string 0x1a5d9 ("3 32 72 5 n:438 144 1 6
                      ka:450 160 1484 11 body154:461": three variables, 72 bytes at frame + 32, 1 at frame + 144 and
                      1484 at frame + 160) at frame + 8, the function's address 0x8909c at frame + 16.
     0x89150, 0x89170 - 0x891c8 s3 = (frame >> 3) + 0x7fff8000; the frame's shadow bytes by plain stores: 0..3 = 0xf1
                      (the left guard), 4..12 = 0xf8 (the notice, out of scope), 13..17 = 0xf2 (the guard between it
                      and ka), 18 = 0xf8 (ka), 19 = 0xf2.
     0x891cc - 0x891d8 a0 = s6 = s3 + 20 (the shadow byte of frame + 160) and a1 = 0xba = 186; the call of
                      __asan_set_shadow_f8 (meta_fill_f8, 0x553cc = transportb_sigma TB___asan_set_shadow_f8) at
                      0x891d8, return address 0x891dc: the body's 186 shadow bytes (1484 bytes, the last granule
                      partial) marked out of scope.
     0x891dc - 0x89224 shadow bytes 206..223 = 0xf3 (the right guard; plain stores at s3 + 0xce .. s3 + 0xdf).
     0x89228          s = 0 goes to 0x892e0 (s10 = -1, :416-417); s = 0x5df640, so not taken.
     0x8922c - 0x89230 s & 7 <> 0 (the UBSan alignment check of struct diginet_session *s) goes to the trap word at
                      0x898e0.
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 1-byte access,
                      (a & 7) < k (signed) goes on; for a 4-byte access, ((a & 7) + 3) < k (signed) goes on; for an
                      8-byte access any k <> 0 goes to the error path.
     0x89234 - 0x89248 s7 = s + 112, s5 = the address of its shadow byte; the check of the 4-byte load; s9 = the
                      4-byte signed load at s + 112 (S_state Bw).
     0x8924c - 0x89260 s10 = 0; s9 > 1 (signed) goes to 0x892e8 (the S_ONLINE / S_CLOSED tests); s9 = 0 (S_IDLE)
                      goes to 0x896a4 (return 0, :418-419); s9 <> 1 goes to 0x89340 (the step: taken when s9 < 0,
                      the load at 0x89248 being signed).
     0x892e8 - 0x892f8 s9 = 2 goes to 0x892fc (S_ONLINE); s9 <> 3 goes to 0x89340 (the step: taken when s9 >= 4);
                      s9 = 3 (S_CLOSED) goes to 0x896a4 (return 0, :418). So every state outside 0 .. 3 takes the
                      step, as the model does (TSess.v diginet_session_tick_m).
     the S_WAKING arm (:421-423), 0x89264 - 0x892dc, 0x89514 - 0x89520:
     0x89264 - 0x892a4 the checks of the 8-byte load at s + 152 and the 4-byte load at s + 44; a1 = the 8-byte load at
                      s + 152 (S_wake_sent_us Bw), a0 = the 4-byte unsigned load at s + 44 (S_cfg_wake_timeout_ms Bw);
                      now - a1 (mod 2 ^ 64) below a0 * 1000 goes to 0x89340 (no timeout); else the session is lost
                      (:422).
     0x892a8 - 0x892bc the check of the 4-byte store at s + 212, then the store of 0 there (S_inflight, :162).
     0x892c0 - 0x892d4 the check of the 4-byte store at s + 168, then the store of 0 there (S_desk_counter_valid,
                      :163). The world is now slost_w1 Bw.
     0x892d8 - 0x892dc a2 = 6 (R_WAKE_TIMEOUT); to 0x89514.
     0x89514 - 0x8951c a0 = s, a1 = 0 (S_IDLE); the call of set_state (0x872cc = transportb_sigma TB_set_state) at
                      0x8951c, return address 0x89520 (:164); to 0x896a0 (s10 = 0, the result DIGINET_OK, :423).
     the S_ONLINE silence arm (:425-427), 0x892fc - 0x8933c, 0x894e0 - 0x89520: the same shape at the other fields.
     0x892fc - 0x8933c the checks of the 8-byte load at s + 176 and the 4-byte load at s + 40; a1 = the 8-byte load at
                      s + 176 (S_last_rx_us Bw), a0 = the 4-byte unsigned load at s + 40 (S_cfg_offline_ms Bw);
                      now - a1 (mod 2 ^ 64) at least a0 * 1000 goes to 0x894e0 (the silence path); else to 0x89340.
     0x894e0 - 0x8950c the checks and the stores of 0 at s + 212 and s + 168 (:162-163); the world is now
                      slost_w1 Bw.
     0x89510 - 0x8951c a2 = 4 (R_SILENCE); a0 = s, a1 = 0; the call of set_state at 0x8951c, return address 0x89520;
                      to 0x896a0 (s10 = 0, :427).
     the ack-timeout step (:430-443), 0x89340 - 0x8962c:
     0x89340 - 0x89364 t0 = s + 212, t1 = the address of its shadow byte; the check of the 4-byte load; the load
                      (S_inflight Bw) = 0 goes to 0x8965c (no inflight); a7 = s + 0x46e0 = s + 18144 (g_s.queued).
     0x89368 - 0x893a8 the checks of the 8-byte load at s + 1752 (a3 = the address of its shadow byte) and the 4-byte
                      load at s + 28; a2 = the 8-byte load at s + 1752 (S_inflight_sent_us Bw), a1 = the 4-byte
                      unsigned load at s + 28 (S_cfg_ack_timeout_ms Bw); now - a2 (mod 2 ^ 64) below a1 * 1000 goes to
                      0x8965c; else the inflight frame timed out (:430).
     0x893ac - 0x893e4 the checks of the 4-byte loads at s + 1748 (a4 = the address of its shadow byte) and s + 32;
                      t2 = the load at s + 1748 (S_inflight_retries Bw), a2 = the load at s + 32 (S_cfg_max_retries Bw);
                      t0 and t1 saved at s1 + 48 and s1 + 40; t2 >= a2 (unsigned) goes to 0x89524 (the ack-lost arm,
                      :436-441).
     the retransmit arm (:432-434), 0x893e8 - 0x894dc:
     0x893e8 - 0x893fc the check of the 4-byte store at s + 1748 (its shadow byte read again through a4); a4 = t2 + 1;
                      a1 = s + 216 (g_s.inflight_frame); the store of a4 at s + 1748 (S_inflight_retries = u32 (+1),
                      :405).
     0x89400          s + 216 >= 2 ^ 64 - 26 (unsigned: the UBSan pointer-overflow check of
                      &inflight_frame[DIGINET_ETH_HDR_LEN + 12]) goes to the trap word at 0x898e0.
     0x89404 - 0x89420 the check of the 1-byte store at s + 242; the store of the low byte of (a4 mod 2 ^ 32) >> 8 at
                      s + 242 (the high byte of the 16-bit retry at inflight_frame + 14 + 12, :407).
     0x89424          2 ^ 64 - 28 < s + 216 (unsigned: the check of &inflight_frame[DIGINET_ETH_HDR_LEN + 13]) goes to
                      the trap word at 0x898e0.
     0x89428 - 0x8943c the check of the 1-byte store at s + 243; the store of the low byte of a4 at s + 243 (:408).
     0x89440 - 0x8944c the check of the 8-byte store at s + 1752 (through a3), then the store of now there
                      (S_inflight_sent_us, :409).
     0x89450 - 0x8946c the check of the 8-byte access at s + 18232 (a7 + 0x58 = g_s.stats.tx_retransmits); the load,
                      + 1, the store back (:410).
     0x89470 - 0x894a8 the checks of the 8-byte loads at s + 1736 (S_inflight_len), s + 72 (S_io_send) and s + 64
                      (S_io_ctx).
     0x894ac - 0x894bc s9 = a7; a2 = the inflight length, a3 = ctx, a4 = the send pointer, a0 = ctx; a1 = s + 216 (since
                      0x893f4).
     0x894c0          the indirect call (jalr a4), return address 0x894c4 (:411, send_raw :90; struct
                      diginet_session + 72, io.send -> io_send).
     0x894c4 - 0x894dc the result 0 goes to 0x89630 (send_raw :91-92: t0, t1 loaded back from s1 + 48 and s1 + 40,
                      the check of the 8-byte access at s + 18192 (s9 + 0x30 = g_s.stats.tx_frames), a7 = s9, the
                      load, + 1, the store back, then 0x8965c); else s10 = r, a7 = s9, t0 and t1 loaded back; r at
                      least 0 goes to 0x8965c (:433-434: r >= 0 goes on); a negative r goes to 0x896a4 (the return,
                      :434).
     the ack-lost arm (:436-441), 0x89524 - 0x8962c:
     0x89524 - 0x89534 the check of the 4-byte store at s + 212 (through t1); t2 (the retries) saved at s1 + 24; the
                      store of 0 at s + 212 (:436); a7 saved at s1 + 32.
     0x89538 - 0x89558 the check of the 8-byte access at s + 18240 (a7 + 0x60 = g_s.stats.ack_lost); the load, + 1, the
                      store back (:437); s10 = frame + 32 = p, the notice (n).
     0x8955c - 0x8958c shadow bytes 4..12 = 0 (p usable); a0 = p + 8, a1 = 0, a2 = 64; the call of __asan_memset
                      (checked_memset, 0x52888 = transportb_sigma TB___asan_memset) at 0x8958c, return address
                      0x89590: p's bytes 8 .. 71 set to 0 (:438, the designated initialiser).
     0x89590 - 0x895c0 plain stores: the 4 bytes 5 at p (kind = N_ACK_LOST) and the low 32 bits of s9 at p + 4
                      (state = the state loaded at 0x89248, S_state Bw: any value other than S_IDLE and S_CLOSED); the
                      check of the 4-byte load at s + 1744 (S_inflight_counter) and the store of it at p + 64 (counter,
                      :439); the 2-byte store of the saved retries (loaded back from s1 + 24) at p + 68 (retry =
                      u16 (S_inflight_retries Bw), :440). The 72 bytes at p are then tick_ack_ntc Bw as trans_ntc_at
                      reads them.
     0x895c4 - 0x895f4 the checks of the 8-byte loads at s + 96 and s + 104; a2 = the 8-byte load at s + 96 (S_notify:
                      tw_read, and call_notify gives TI.ti_notice timg_B = 0x8341c), a0 = the 8-byte load at s + 104
                      (notify_ctx), a1 = p; the indirect call (jalr a2) at 0x895f4, return address 0x895f8 (:441;
                      struct diginet_session + 96, notify -> notice).
     0x895f8 - 0x8962c shadow bytes 4..12 = 0xf8; a7, t0 and t1 loaded back from s1 + 32, s1 + 48 and s1 + 40; to
                      0x8965c.
     the keepalive / queue tail (:445-471), 0x8965c - 0x898dc:
     0x8965c - 0x8966c the check of the 4-byte load at s + 112 (through s5); the load <> 2 (S_ONLINE) goes to 0x896a0
                      (s10 = 0, the return DIGINET_OK, :445-446).
     0x89670 - 0x8967c the check of the 4-byte load at s + 212 (through t1); the load <> 0 goes to 0x896a0.
     0x89680 - 0x8969c the check of the 8-byte load at s + 192 (S_backoff_until_us); now below it goes to 0x896a0;
                      else to 0x89714.
     0x89714 - 0x89730 the check of the 8-byte load at s + 184 (S_next_keepalive_us; a3 = the address of its shadow
                      byte); the load at most now goes to 0x897b0 (the keepalive, :449-455); else to 0x89734 (the
                      queue, :458-471).
     the keepalive (:449-455), 0x897b0 - 0x89840:
     0x897b0 - 0x897c0 a1 = frame + 144 = ka; shadow byte 18 = 1 (ka's one byte usable; the plain store at s3 + 0x12)
                      and the 1-byte store of 0 at ka (:450).
     0x897c4 - 0x897fc the check of the 4-byte load at s + 24; a2 = the 4-byte unsigned load at s + 24
                      (S_cfg_keepalive_ms Bw) * 1000; a4 = a2 + the old next_keepalive (:451); when now is below it,
                      a4 stays; else a4 = a2 + now (:452-453); the check of the 8-byte store at s + 184 (through a3)
                      and the store of a4 there.
     0x89800 - 0x8981c the check of the 8-byte access at s + 18216 (a7 + 0x48 = g_s.stats.tx_keepalives); the load,
                      + 1, the store back (:454).
     0x89820 - 0x89830 a2 = 1, a3 = 1, a0 = s, a4 = now, a1 = ka; the call of send_data (0x89d78 = transportb_sigma
                      TB_send_data) at 0x89830, return address 0x89834 (:455); s10 = its result.
     0x89838 - 0x89840 shadow byte 18 = 0xf8 (ka out of scope); to 0x896a4.
     the queue (:458-471), 0x89734 - 0x898dc:
     0x89734 - 0x89748 the check of the 4-byte load at a7 = s + 18144; the load (S_queued Bw) = 0 goes to 0x896a0
                      (s10 = 0, :458-459).
     0x8974c - 0x8976c a4 = s + 208, s5 = the address of its shadow byte; the check of the 4-byte load; the load
                      (S_display_sent Bw) at 0x89760; s7 = s + 200 (g_s.last_display_us); a4 saved at s1 + 48; the
                      load = 0 goes to 0x89844 (s10 = allow = 1).
     0x89770 - 0x897ac the checks of the 8-byte load at s + 200 and the 4-byte load at s + 48; a1 = the load at
                      s + 200 (S_last_display_us Bw), a0 = the 4-byte unsigned load at s + 48
                      (S_cfg_display_gap_us Bw); s10 = allow = 1 when now - a1 (mod 2 ^ 64) is at least a0, else 0
                      (:460); to 0x89848.
     0x89848 - 0x8985c s9 = frame + 160 = body; a0 = s6 (the shadow byte of body) and a1 = 0xb9 = 185; the call of
                      __asan_set_shadow_00 (meta_fill_00, 0x552ac = transportb_sigma TB___asan_set_shadow_00) at
                      0x89854, return address 0x89858: the body's first 185 shadow bytes 0; then the plain store of 4
                      at s3 + 0xcd (shadow byte 205: the last 4 of the 1484 bytes usable).
     0x89860 - 0x89874 a2 = s1 + 80 (body_len, in its own machine frame), a4 = s1 + 76 (has_display, in its own
                      machine frame), a0 = s, a1 = body, a3 = s10 (allow); the call of take (0x8a160 = transportb_sigma
                      TB_take) at 0x89874, return address 0x89878 (:461-464).
     0x89878 - 0x8987c take's result 0 goes to 0x898cc (s10 = 0, :465-466); else a3 = the result (n).
     0x89880 - 0x898ac the 4-byte load of has_display at s1 + 76 (its own frame, no check); 0 goes to 0x898b0; else
                      the check of the 4-byte store at s + 208 (through s5) and the store of 1 there (S_display_sent,
                      :467-469), then the check of the 8-byte store at s + 200 (through s7) and the store of now there
                      (S_last_display_us, :470).
     0x898b0 - 0x898c4 a2 = the 8-byte load of body_len at s1 + 80 (its own frame, no check); a0 = s, a1 = body,
                      a4 = now, a3 = n; the call of send_data at 0x898c0, return address 0x898c4 (:471); s10 = its
                      result.
     0x898d0 - 0x898dc a0 = s6, a1 = 0xba = 186; the call of __asan_set_shadow_f8 at 0x898d8, return address 0x898dc:
                      the body's 186 shadow bytes out of scope; to 0x896a4.
     the epilogue, 0x896a0 - 0x89710:
     0x896a0          s10 = 0 (the paths that return DIGINET_OK without a send).
     0x896a4 - 0x896ac the header word 0x45e0360e stored at frame (every path).
     0x896b0          s2 = 0 goes to 0x896c4 (the real-stack arm; not taken).
     0x896b4 - 0x896bc a1 = 0x700 = 1792, a0 = s2 = frame; the call of __asan_stack_free_5 (frame_release_5, 0x3df4c =
                      transportb_sigma TB___asan_stack_free_5) at 0x896bc, return address 0x896c0: the frame's 256
                      shadow bytes = 0xf5 and the zero store at its flag byte (TransportRtCg.v
                      astack_free_cls_realizes); to 0x896d0.
     0x896c4 - 0x896cc the real-stack arm's release: a0 = s3, a1 = 0xe0 = 224, the call of __asan_set_shadow_00 at
                      0x896cc (not taken).
     0x896d0 - 0x89710 a0 = s10 (the result); sp = s0 - 192, ra and s0 .. s11 loaded back, sp = sp + 192, return.
                      a1 .. a7 at the return are not stated.
     0x898e0          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path.
     0x898e4 - 0x89ae8 the slow paths of the checks and the 41 error calls.
   No tail jump: the calls are jal with link (the stack malloc, the memset, the four shadow fills (0x891d8 and 0x898d8
   to __asan_set_shadow_f8, 0x89854 and 0x896cc to __asan_set_shadow_00), the stack free, set_state, send_data twice,
   take, and the 41 error-path calls) and two jalr with link (io_send at 0x894c0, notice at 0x895f4); every j is
   inside the function, and the function's own return is the ret at 0x89710.
   The model and the code: the state tests at 0x89254 - 0x892f4 are diginet_session_tick_m's S_CLOSED / S_IDLE /
   S_WAKING / S_ONLINE tests; the two timeout tests are ms_m (S_cfg_wake_timeout_ms Bw) <=? u64 (now -
   S_wake_sent_us Bw) and ms_m (S_cfg_offline_ms Bw) <=? u64 (now - S_last_rx_us Bw) (each a 4-byte unsigned read
   times 1000, so the product is below 2 ^ 42); each lost arm is session_lost_m at Bw with why = R_WAKE_TIMEOUT /
   R_SILENCE, whose two stores (slost_w1) are the code's own and whose set_state_m step at slost_w1 Bw with S_IDLE and
   why is the call of set_state (slost_model_sstate; set_state's test of S_state (slost_w1 Bw) against S_IDLE is its
   own, its 0x8741c); tick_model states the whole branch structure, with the step of :430-443 as tick_step and the
   tail of :445-471 as tick_tail; the step test is negb (S_inflight Bw =? 0) && (ms_m (S_cfg_ack_timeout_ms Bw) <=?
   u64 (now - S_inflight_sent_us Bw)), the retry test S_inflight_retries Bw <? S_cfg_max_retries Bw (two 4-byte
   loads compared by bgeu, the u32 order the model's <? on two u32 fields has); the retransmit arm is retransmit_m
   (set_S_inflight_retries, the two inflight_frame bytes, set_S_inflight_sent_us, set_S_stats_tx_retransmits, then
   send_raw_m at inflight_bytes, whose call_send is the indirect call and whose r = 0 branch adds 1 to
   stats.tx_frames); the ack-lost arm is set_S_inflight 0, set_S_stats_ack_lost +1 and call_notify with the Ntc of
   :438-440 (tick_ack_w1, tick_ack_ntc); the tail tests are negb (S_state =? S_ONLINE) || negb (S_inflight =? 0) ||
   (now <? S_backoff_until_us) (:445), S_next_keepalive_us <=? now (:449), S_queued =? 0 (:458) and the display test
   (:460); the keepalive is set_S_next_keepalive_us (u64 of the sum, twice), set_S_stats_tx_keepalives +1 and
   send_data_m with the one byte 0, ncmds 1; the queue path is take_m Bw allow, then (when n <> 0 and has_display)
   set_S_display_sent 1 and set_S_last_display_us now, then send_data_m with firstn body_len body and ncmds = n. The
   model's None cases are retransmit_m's inflight_bytes (1514 < S_inflight_len), call_send's and call_notify's
   pointer tests, io_send's, notice's, set_state_m's, take_m's and send_data_m's, all ruled out by the model premise;
   the code's three trap branches and its real-stack arm are ruled out by facts outside the model (the constant s,
   the side-stack premises).
   Trap path (the unimp word at 0x898e0, from 3 branches) and the facts that refute them: 0x89230 (s & 7 <> 0): s =
   0x5df640, a multiple of 8; 0x89400 (s + 216 >= 2 ^ 64 - 26) and 0x89424 (2 ^ 64 - 28 < s + 216): s + 216 =
   0x5df718.
   Error paths (41 calls; no abort) and the facts that rule them out:
     __asan_report_load4 (0x59644) at 0x898f4 (s + 112), 0x89908 (s + 212), 0x8991c (s + 112), 0x89930 (s + 28),
       0x89940 (s + 44), 0x89950 (s + 40), 0x89964 (s + 212), 0x89978 (s + 1748), 0x8998c (s + 32),
       0x89a04 (s + 1744), 0x89a38 (s + 18144), 0x89a4c (s + 24), 0x89a60 (s + 208), 0x89a70 (s + 48);
     __asan_report_store4 (0x59964) at 0x8999c (s + 212), 0x899ac (s + 168), 0x899bc (s + 212), 0x899cc (s + 168),
       0x899e0 (s + 1748), 0x899f4 (s + 212), 0x89a88 (s + 208);
     __asan_report_store1 (0x59824) at 0x89a14 (s + 242) and 0x89a24 (s + 243);
     __asan_report_load8 (0x596e4) at 0x89a8c (s + 1752), 0x89a94 (s + 152), 0x89a9c (s + 176), 0x89aa0 (s + 192),
       0x89aa8 (s + 18232), 0x89aac (s + 1736), 0x89ab0 (s + 72), 0x89ab8 (s + 64), 0x89abc (s + 18240),
       0x89ac0 (s + 96), 0x89ac8 (s + 104), 0x89acc (s + 184), 0x89ad0 (s + 18192), 0x89ad8 (s + 18216),
       0x89ae0 (s + 200);
     __asan_report_store8 (0x59a04) at 0x89aa4 (s + 1752), 0x89ad4 (s + 184), 0x89ae8 (s + 200).
     Each guards a naturally aligned access inside g_s's payload [0x5df640, 0x5e3d98) (2283 whole granules), whose
     shadow bytes are 0 (trans_tick_cells, read at each AR state by DgnTransportBCg.v decode_zshadow_rd), so k = 0; the
     two 1-byte stores at s + 242 and s + 243 are inside it too (inflight_frame + 26, + 27).
     The memset's own check (aintrin_realizes' pre, from the G journal through TransportGCg.v gx_intrin_at): the
     destination [frame + 40, frame + 104) lies in the frame this function took; its shadow bytes are 0 since the
     plain sb stores just before it (0x8955c - 0x8957c; no shadow-fill call marks them) and their hull is visible
     (astack_malloc_realizes' zero_shadow); each destination byte is a byte of the journal's own frame list after the
     stack malloc (YCbq.v awr_byte's in_frames: transport_twr_ok_g), not owned, not in the ESTACK bytes below sp.
     The shadow fills' own premise (aset_shadow_realizes; the calls at 0x891d8, 0x89854 and 0x898d8, and the one at
     0x896cc that the count premise excludes): the range lies inside
     [shadow_addr frame, shadow_addr frame + fs_frame_bytes 5 / 8) = the frame's 256 shadow bytes (the body's shadow
     starts at byte 20 and 20 + 186 = 206 <= 256), and the frame is a live frame of the state.
     The stack free's own premise (astack_free_cls_realizes): a0 = frame, the frame is live, and the word at
     frame + 2040 still holds the flag byte's address (astack_malloc_realizes' rdword; no store of this function or of
     a callee writes it: the locals end at frame + 1644, the shadow stores go to the shadow band, and each callee's
     acall_kept_g keeps the bytes of this frame outside the callee's own window).
   Writes: g_s's inflight, desk_counter_valid, inflight_retries, inflight_frame[26], [27], inflight_sent_us,
   next_keepalive_us, display_sent, last_display_us, stats.tx_frames, stats.tx_keepalives, stats.tx_retransmits and
   stats.ack_lost (bytes of G); its own machine frame (the 8 zero bytes at entry sp - 192 (0x890a0), ra and s0 .. s11
   at sp + 88 .. sp + 184, and s1 + 24 .. s1 + 80 after the realignment); its own side-stack frame, that frame's
   shadow bytes and its flag byte; set_state's (set_state_cg.v sstate_wr (slost_w1 Bw) S_IDLE why: g_s's state and
   notice's N_STATE stores, GOT; tick_wr_sstate); the N_ACK_LOST notice's stores (notice_wr: M.fly.on); io_send's
   (io_send_cg.v iosend_wr for a frame of at most 1514 bytes); take's (take_cg.v take_wr: the queue entries, queued,
   and the three cells bp / blp / hdp, all in g_s or in its own frames); and send_data's (send_data_cg.v
   senddata_wr: g_s's inflight fields and io_send's). No byte of a caller's frame or block is written, so tick_wr is
   the written range. The G kit for the own frame is image B's set_state_cg.v's (TransportGCg.v dk_kept_own_g with
   dkg_nf and dkg_nf_sep, dk_kept_trans_nf_g for every callee, dkg_frame_al64, gx_intrin_at for the memset,
   dk_kept_frame_byte_g; image B's CanKit.v can_stack_malloc_at read inside the G journal through gx_lift), with the
   shadow fills and the stack free as steps whose written bytes are the own frame's shadow bytes and its flag byte.
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_5 as astack_malloc_realizes ... TICK_CID (with pc_stack_malloc (as_code B) TICK_CID =
       transportb_sigma TB___asan_stack_malloc_5): count_cid 5 (frames Sc) < fs_frames 5 from the count premise.
     __asan_set_shadow_f8 as TransportRtCg.v aset_shadow_realizes (transportb_sigma TB___asan_set_shadow_f8) 0xf8,
       calls at 0x891d8 and 0x898d8: ecall_pre from the journal; the own frame is live; a0 = shadow_addr frame + 20,
       a1 = 186, and 20 + 186 <= fs_frame_bytes 5 / 8 = 256.
     io_send as io_send_cg.v transport_io_send_cg at TI.ti_io_send timg_B (= 0x82ffc, io_send_cg.v io_send_at; the
       call at 0x894c0, the inlined send_raw of retransmit; a G-form callee in the same G journal):
       the journal at the call state; ra = 0x894c4; gp, tp kept; a1 = p = s + 216 = g_s.inflight_frame,
         a2 = S_inflight_len of the world after retransmit's stores, and frame = the model's inflight_bytes of it;
       sp' 32-aligned, sp0 - STK <= sp' - IOSEND_STK (TICK_STK = 208 + SENDDATA_STK >= 208 + IOSEND_STK), sp' <= sp0;
       0 < p; garr8 of frame through tw_at; trans_src_ok of [p, p + n) by DgnTransportBCg.v trans_src_ok_G_range
         (inside g_s's payload) with trans_sh_any (trans_sh_any_zshadow over trans_tick_cells; g_s starts on 64 bytes)
         and decode_rd_ok; decode_off_win at IOSEND_STK (G lies below the stack); iosend_frame_at's second disjunct
         (TB_g_s <= p, p + n <= TB_g_s + SZ_g_s: n <= 1514 by inflight_bytes, and 216 + 1514 <= 18264);
       g_fail_next of the handed world <= 1 (the premise; g_fail_next is not in g_s and no store before the call
         writes it); trans_rom_view_rd at the call memory; tw_at at the handed world (the premise's Bw with the
         tw_writes of retransmit's stores); io_send_m timg_B at that world and frame = Some (B1, r): the model premise
         through retransmit_m, send_raw_m and call_send; run invariants (1) and (4): carried (above); st_nev +
         IOSEND_EV <= EV_MAX (IOSEND_EV = 0).
       Its X: a0 = r and tw_at at B1.
     set_state as set_state_cg.v transport_set_state_cg at transportb_sigma TB_set_state (the call at 0x8951c, on
       both lost arms; a G-form callee composed in the same G journal, no gx_call_cg):
       the journal at the call state (the own frame live); ra = 0x89520 (ret_ok, 4096 <= ra); gp, tp kept;
         a0 = SSTATE_S = s, a1 = st = 0 (S_IDLE), a2 = why = 6 (R_WAKE_TIMEOUT) / 4 (R_SILENCE), 0 <= st, why < 2 ^ 31;
       sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - SSTATE_STK: sp' >= sp - 208 and
         TICK_STK = 208 + SENDDATA_STK >= 208 + SSTATE_STK; sp' <= sp0;
       tw_at at slost_w1 Bw: tw_at at Bw carried through the stack malloc (gx_kept_of_acall_kept) and the shadow fill
         (the own frame's shadow bytes), then the tw_writes of the two stores; g_fail_next (slost_w1 Bw) <= 1 (the
         premise; the stores do not touch the byte);
       set_state_m timg_B TF (slost_w1 Bw) S_IDLE why = Some (Bw', tt): the model premise through tick_model (which
         names the branch the call lies on) and slost_model_sstate; the arm's result is DIGINET_OK = 0, the a0 of
         0x896a0;
       trans_tframe_at TF at SSTATE_STK: the entry's at TICK_STK, carried across the stack malloc
         (trans_src_ok_inner with TF's bytes kept, trans_rd_ok_sh and trans_src_ok_disj_own; the four record facts),
         the shadow fill (the own frame's shadow bytes) and the g_s stores (tick_apart). No
         program callee runs before a set_state call: the lost arms are the first branches of the state dispatch;
       trans_rom_view_rd at the call memory (above);
       sstate_apart TF (slost_w1 Bw) S_IDLE why: tick_apart, since sstate_wr (slost_w1 Bw) S_IDLE why lies inside
         tick_wr Bw for both whys (tick_wr_sstate);
       count_cid SSTATE_CID at the call state = count_cid 2 (frames Sc) < fs_frames 2 (the class-2 premise; the own
         frame is of class 5);
       st_nev S + k + SSTATE_EV <= EV_MAX: SSTATE_EV = NOTICE_EV = 0 and TICK_EV = 0.
       Its X: tw_at at Bw' and g_fail_next Bw' <= 1.
     __asan_memset as aintrin_realizes ... OSet (transportb_sigma TB___asan_memset), the call at 0x8958c (above).
     notice as notice_cg.v transport_notice_cg at TI.ti_notice timg_B (= 0x8341c = transportb_obj 10, notice_cg.v
       notice_at; the call at 0x895f4, the N_ACK_LOST notice; a G-form callee composed in the same G journal, no
       gx_call_cg). Each premise:
       the journal at the call state (the own frame live); ra = 0x895f8 (ret_ok, 4096 <= ra); gp, tp kept; a1 = p;
       sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - NOTICE_STK: sp' >= sp - 208 and
         TICK_STK = 208 + SENDDATA_STK >= 208 + NOTICE_STK; sp' <= sp0;
       trans_ntc_at p (tick_ack_ntc Bw): 0 < p and p mod 8 = 0 (p = frame + 32, dkg_frame_al64); trans_src_ok by
         decode_in_fake at the call state (the 72 bytes inside the 2048 bytes of a frame of its frames) with
         decode_rd_ok (the bytes present by astack_malloc_realizes, the nine shadow bytes 0 since the plain sb stores
         before the memset, their hull visible); decode_off_win (the frame lies below alloc_ceiling, notice's window
         above it); NB = the 72 bytes the memset and the plain stores left, whose fields are the Ntc's; the body:
         pointer 0, length 0, garr8 of [], trans_src_ok of the empty range at 0 (DgnTransportBCg.v trans_src_ok_null),
         decode_off_win of it; the announce: n_ann = None with the pointer 0;
       trans_tframe_at TF at NOTICE_STK: the entry's at TICK_STK, carried across the stack malloc
         (trans_src_ok_inner with TF's bytes kept, trans_rd_ok_sh and trans_src_ok_disj_own; the four record
         facts), the shadow fill, the memset (the own frame) and the g_s stores
         (tick_apart). No program callee runs before the notice call: the ack-lost arm at 0x89524 is the taken side of
         the bgeu at 0x893e4 whose fall-through holds the io_send call, and both send_data calls are past 0x8965c;
       trans_rom_view_rd at the call memory (above);
       tw_at at tick_ack_w1 Bw: tw_at at Bw carried through the stack malloc (gx_kept_of_acall_kept) and the tw_writes
         of the stores before it;
       notice_m timg_B TF (tick_ack_w1 Bw) (tick_ack_ntc Bw) = Some (_, tt): the model premise through tick_model and
         tick_step's second arm, whose call_notify is at tick_ack_w1 Bw with tick_ack_ntc Bw;
       notice_apart: a byte of notice_wr is a byte of M.fly.on (N_ACK_LOST), a byte of G, so not a byte of p's frame
         (a frame byte is outside the image: AR_laws' al_client_img); the body range is empty and n_ann = None; TF's
         range: tick_apart, since notice_wr (tick_ack_w1 Bw) (tick_ack_ntc Bw) lies inside tick_wr Bw;
       the N_DATA premise: vacuous (n_kind = N_ACK_LOST);
       st_nev S + k + NOTICE_EV <= EV_MAX: NOTICE_EV = 0 and TICK_EV = 0.
     __asan_stack_free_5 as TransportRtCg.v astack_free_cls_realizes (transportb_sigma TB___asan_stack_free_5)
       TICK_CID, the call at 0x896bc (above).
     __asan_set_shadow_00 as TransportRtCg.v aset_shadow_realizes (transportb_sigma TB___asan_set_shadow_00) 0, the
       call at 0x89854 (a0 = shadow_addr frame + 20, a1 = 185). The call at 0x896cc is on the real-stack arm, which
       the count premise excludes.
     send_data as send_data_cg.v transport_send_data_cg at transportb_sigma TB_send_data (the calls at 0x89830, the
       keepalive, and 0x898c0, the data frame; a G-form callee in the same G journal):
       the journal at the call state (the own frame live); ra = 0x89834 / 0x898c4; gp, tp kept; a0 = SENDDATA_S = s,
         a1 = bodyp = frame + 144 (ka) / frame + 160 (body), a2 = the length of the bytes at it (1, or the body_len
         take returned, at most 1484), a3 = bv_swrap 32 ncmds (1, or take's n, below 2 ^ 32 by take_m_out),
         a4 = now (0 <= now < 2 ^ 64);
       sp' 32-aligned, sp0 - STK <= sp' - SENDDATA_STK (TICK_STK = 208 + SENDDATA_STK), sp' <= sp0;
       0 < bodyp (a frame address, at least 4096 by AR_sep_law); garr8 of the bytes at bodyp (the store of 0 at ka;
         take's X for the body, whose first body_len bytes are the model's); trans_src_ok by decode_in_fake at the
         call state (the range inside the 2048 bytes of a frame of its frames) with decode_rd_ok (the shadow bytes
         set usable at 0x897bc / by the fill at 0x89854 and the store at 0x8985c, kept by take's acall_kept_g);
         decode_off_win at SENDDATA_STK (the frame lies below alloc_ceiling); the range apart from G (a frame byte is
         outside the image: al_client_img);
       tw_at at the world the model has there and g_fail_next of it <= 1 (the premise, carried through the stores
         and take's X); send_data_m timg_B TF (that world) (the bytes) ncmds now = Some (Bw', r): the model premise;
       trans_rom_view_rd at the call memory; run invariants (1) and (4): carried; count_cid 0 (frames Sc) and
         count_cid 2 (frames Sc) at the call state are the premises' (the own frame is of class 5);
         st_nev + SENDDATA_EV <= EV_MAX (SENDDATA_EV = 0).
       Its X: a0 = r, tw_at at Bw' and g_fail_next Bw' <= 1.
     take as take_cg.v transport_take_cg at transportb_sigma TB_take (the call at 0x89874; a G-form callee in the same
       G journal):
       the journal at the call state; ra = 0x89878; gp, tp kept; a0 = TAKE_S = s, a1 = bp = frame + 160,
         a2 = blp = s1 + 80, a3 = allow (0 or 1, so -2 ^ 31 <= allow < 2 ^ 31), a4 = hdp = s1 + 76;
       sp' 32-aligned, sp0 - STK <= sp' - TAKE_STK (TICK_STK = 208 + SENDDATA_STK >= 208 + TAKE_STK), sp' <= sp0;
       bp: 0 < bp, decode_in_fake at the call state ([frame + 160, frame + 1644) inside the frame's 2048 bytes),
         transport_twr_ok_g at sp' (each byte an awr_byte of the own frame list: in_frames), decode_rd_ok (the bytes
         present by astack_malloc_realizes, the 186 shadow bytes 0, 0, .., 4 since 0x89854 - 0x8985c, their hull
         visible), decode_off_win at TAKE_STK (the frame lies below alloc_ceiling, take's window above it), and the
         range apart from G (a frame byte is outside the image);
       blp and hdp: both in this function's own machine frame, which the journal's window covers: blp = s1 + 80 with
         s1 32-aligned, so blp mod 8 = 0, and hdp = s1 + 76, so hdp mod 4 = 0; transport_twr_ok_g at sp' (a byte of
         the window [sp0 - STK, sp0) above sp', awr_byte's stack clause), decode_rd_ok (the machine stack's shadow is
         0 at every AR state: YG0n.v zero_shadow_ranges' first row [ly_stk_lo, ly_stk_hi), CanKit.v
         can_stack_addressable, and the bytes are present: the journal's window), decode_off_win at TAKE_STK
         (s1 + 76 >= sp' > sp' - TAKE_STK, the second disjunct spZ regs <= q), and apart from G (a stack byte is
         outside the image);
       the three disjointness premises: [bp, bp + 1484) is in the side-stack frame and blp / hdp are in the machine
         stack, which lies above alloc_ceiling > every frame address; blp + 8 = s1 + 88 <= hdp is false, hdp + 4 =
         s1 + 80 <= blp holds;
       tw_at at the world take is called with and g_fail_next of it <= 1 (take's statement asks both; the premises,
         carried); take_m of that world and allow = Some (Bw1, (body, len, hd, taken)): the model premise; the
         queue-length invariant (2) and the two cfg bounds (5): carried (above); count_cid 2 (frames Sc) <
         fs_frames 2 (the premise; the own frame is of class 5); st_nev + TAKE_EV <= EV_MAX (TAKE_EV = 0).
       Its X: a0 = the 32-bit taken sign-extended, tw_at at Bw1, g_fail_next Bw1 <= 1, the 1484 bytes at bp agreeing
       with body on the first len, len at blp and hd at hdp (read at the memory with those 12 bytes put back:
       transport_cg_post_out's gover, which this walk uses at once, the two loads at 0x89880 and 0x898b0).
   Each callee's own record facts are premises of its holds statement.
   Stack: 192 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the memset, the shadow fills, the stack free), io_send's IOSEND_STK,
   set_state's SSTATE_STK, notice's NOTICE_STK, send_data's SENDDATA_STK or take's TAKE_STK: TICK_STK =
   208 + SENDDATA_STK (tick_stk_eq).

   The callers (each with the return address after its jal): LLVMFuzzerTestOneInput at 0x81fa4 (return 0x81fa8):
   a0 = 0x5df640 (&g_s, formed at 0x81f9c - 0x81fa0), a1 = the new g_now (the 8-byte load at 0x81f98 of g_now at
   s6 + 0x68c, s6 = 0x5de6f4 loaded at 0x81f7c; g_now was loaded at 0x81f80, raised at 0x81f84 - 0x81f8c and stored
   back at 0x81f90 before the call of m_tick at 0x81f94, which is a jal, not an inlined copy); diginet_session_rx at
   0x87c4c (return 0x87c50): a0 = s4 (its own a0, &g_s, saved at 0x877f0), a1 = s3 (its now_us argument a3, saved at
   0x877cc); diginet_session_poll at 0x8ad28 (return 0x8ad2c): a0 = s3 (its own a0, &g_s, saved at 0x8aafc), a1 = the
   value its io.now call returned (the indirect call at 0x8acfc through the 8-byte load at s7 = s + 88), moved to a3
   at 0x8ad00 and kept in s10 across the optional diginet_session_rx call (0x8ad14 and 0x8ad1c). Each supplies its G
   journal, tw_at, g_fail_next, the model premise (its branch of the model), trans_tframe_at and tick_apart of its
   TF, trans_rom_view_rd, the four run invariants with the two index bounds, and the three frame counts:
   LLVMFuzzerTestOneInput and diginet_session_rx hold a class-2 / class-1 frame of their own while they call
   (__asan_stack_malloc_2 at 0x81310, __asan_stack_malloc_1 at 0x877fc), and diginet_session_poll holds a class-5
   frame (__asan_stack_malloc_5 at 0x8ab08, a0 = 0x6a0), so its own class-5 count must leave room for this call's
   frame.

   Against image A's statement (lib/A/Prog/diginet_session_tick_cg.v): the same definitions (TICK_FRAME, TICK_ALIGN,
   TICK_EV, TICK_CID, TICK_S, tick_ack_w1, tick_ack_ntc, tick_step, tick_tail, tick_model, tick_wr, tick_apart,
   trans_tick_cells), premises and post, at image B's names (TMAP_B, timg_B, TB_g_s, transportb_sigma, G_HARNESS_B,
   lib/B/Prog/DgnTransportBCg.v, lib/B/Prog/m_set_cg.v twb_fld, image B's callee statements); TransportRtCg.v is image
   A's file, image-free. What image B's code forces: (1) set_state is a function, called at 0x8951c on both lost arms,
   where image A inlines session_lost's set_state there (two struct diginet_notice in the own frame, two memsets,
   the state stores and two notify calls): the own frame holds one notice, ka and body (a0 = 1792, still class 5; the
   body's shadow starts at byte 20, image A: 48), the holds statement adds set_state's contract (pc order: after
   io_send), and session_lost_cg.v's slost_w1, slost_w2 and slost_ntc, which tick_wr names, are restated here
   (image B has no session_lost function; its copies are inlined into their callers, which call set_state), with
   three lemmas that read them as set_state's (slost_model_sstate, slost_sstate, tick_wr_sstate); TICK_STK adds
   set_state's SSTATE_STK (the maximum is still SENDDATA_STK, so tick_stk_eq is image A's), tick_cid_callees adds
   SSTATE_CID = TRANS_BC_CID (the class-2 premise covers set_state's frame) and tick_s_eq adds TICK_S = SSTATE_S; the
   pc order of the holds statement's callee contracts is image B's. (2) Three UBSan branches to the trap word 0x898e0
   (the alignment check of s, the pointer-overflow checks of &inflight_frame[26] and [27]), refuted by the constant
   s, a fact image A's form already has. (3) 41 error calls of its own (image A's 47 include the state stores' and
   the two lost notices' notify loads' checks, which on image B are set_state's). No premise of the contract is added
   or dropped; the holds statement's callee contracts change as (1) says. *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_session_tick's frame (`sp = sp - 192` at TB_diginet_session_tick), the at most 0x10 bytes of
   `sp = sp & -32` (0x890dc) below it, and the largest stack a callee uses below the realigned sp: ESTACK for
   __asan_stack_malloc_5, __asan_memset, __asan_set_shadow_f8 / _00 and __asan_stack_free_5 (YG0d.v ecall_pre),
   notice's NOTICE_STK, io_send's IOSEND_STK, set_state's SSTATE_STK, send_data's SENDDATA_STK, take's TAKE_STK. *)
Definition TICK_FRAME : Z := 192.
Definition TICK_ALIGN : Z := 0x10.
Definition TICK_STK : Z :=
  TICK_FRAME + TICK_ALIGN +
  Z.max ESTACK (Z.max NOTICE_STK (Z.max IOSEND_STK (Z.max SSTATE_STK (Z.max SENDDATA_STK TAKE_STK)))).
Lemma tick_stk_eq : TICK_STK = TICK_FRAME + TICK_ALIGN + SENDDATA_STK.
Proof. reflexivity. Qed.
(* No allocator event: notice, io_send, set_state, take and send_data record none, and the class-5 stack malloc, the
   shadow fills and the stack free record none (YG00.v stack_malloc, stack_free). *)
Definition TICK_EV : Z := 0.
(* The side-stack class (a0 = 0x700 at 0x89108, the call of __asan_stack_malloc_5 at 0x8910c), and the class-0 and
   class-2 classes its callees take below it (send_data's own frame; set_state's own frame, and diginet_body_check's
   inside take and inside diginet_frame_build inside send_data). *)
Definition TICK_CID : Z := 5.
Lemma tick_cid_callees :
  SENDDATA_CID = 0 /\ TRANS_BC_CID = 2 /\ SSTATE_CID = TRANS_BC_CID /\
  TICK_CID <> SENDDATA_CID /\ TICK_CID <> TRANS_BC_CID.
Proof. repeat split; try reflexivity; discriminate. Qed.
(* Its first argument, g_s's base in image B. *)
Definition TICK_S : Z := TB_g_s.
Lemma tick_s_eq : TICK_S = 0x5df640 /\ TICK_S = TAKE_S /\ TICK_S = SENDDATA_S /\ TICK_S = SSTATE_S.
Proof. repeat split; reflexivity. Qed.
(* The addresses of the g_s fields the code reads or writes (s + 24, s + 28, s + 32, s + 40, s + 44, s + 48, s + 64,
   s + 72, s + 96, s + 104, s + 112, s + 152, s + 168, s + 176, s + 184, s + 192, s + 200, s + 208, s + 212,
   s + 242, s + 243, s + 1736, s + 1744, s + 1748, s + 1752, s + 18144, s + 18192, s + 18216, s + 18232,
   s + 18240). *)
Lemma tick_addrs :
  TICK_S + (TW.A_S_cfg_keepalive_ms - TW.OFF_g_s) = 0x5df658 /\
  TICK_S + (TW.A_S_cfg_ack_timeout_ms - TW.OFF_g_s) = 0x5df65c /\
  TICK_S + (TW.A_S_cfg_max_retries - TW.OFF_g_s) = 0x5df660 /\
  TICK_S + (TW.A_S_cfg_offline_ms - TW.OFF_g_s) = 0x5df668 /\
  TICK_S + (TW.A_S_cfg_wake_timeout_ms - TW.OFF_g_s) = 0x5df66c /\
  TICK_S + (TW.A_S_cfg_display_gap_us - TW.OFF_g_s) = 0x5df670 /\
  TICK_S + (TW.A_S_io_ctx - TW.OFF_g_s) = 0x5df680 /\
  TICK_S + (TW.A_S_io_send - TW.OFF_g_s) = 0x5df688 /\
  TICK_S + (TW.A_S_notify - TW.OFF_g_s) = 0x5df6a0 /\
  TICK_S + (TW.A_S_notify_ctx - TW.OFF_g_s) = 0x5df6a8 /\
  TICK_S + (TW.A_S_state - TW.OFF_g_s) = 0x5df6b0 /\
  TICK_S + (TW.A_S_wake_sent_us - TW.OFF_g_s) = 0x5df6d8 /\
  TICK_S + (TW.A_S_desk_counter_valid - TW.OFF_g_s) = 0x5df6e8 /\
  TICK_S + (TW.A_S_last_rx_us - TW.OFF_g_s) = 0x5df6f0 /\
  TICK_S + (TW.A_S_next_keepalive_us - TW.OFF_g_s) = 0x5df6f8 /\
  TICK_S + (TW.A_S_backoff_until_us - TW.OFF_g_s) = 0x5df700 /\
  TICK_S + (TW.A_S_last_display_us - TW.OFF_g_s) = 0x5df708 /\
  TICK_S + (TW.A_S_display_sent - TW.OFF_g_s) = 0x5df710 /\
  TICK_S + (TW.A_S_inflight - TW.OFF_g_s) = 0x5df714 /\
  TICK_S + (TW.A_S_inflight_frame + TS0.DIGINET_ETH_HDR_LEN + 12 - TW.OFF_g_s) = 0x5df732 /\
  TICK_S + (TW.A_S_inflight_frame + TS0.DIGINET_ETH_HDR_LEN + 13 - TW.OFF_g_s) = 0x5df733 /\
  TICK_S + (TW.A_S_inflight_len - TW.OFF_g_s) = 0x5dfd08 /\
  TICK_S + (TW.A_S_inflight_counter - TW.OFF_g_s) = 0x5dfd10 /\
  TICK_S + (TW.A_S_inflight_retries - TW.OFF_g_s) = 0x5dfd14 /\
  TICK_S + (TW.A_S_inflight_sent_us - TW.OFF_g_s) = 0x5dfd18 /\
  TICK_S + (TW.A_S_queued - TW.OFF_g_s) = 0x5e3d20 /\
  TICK_S + (TW.A_S_stats_tx_frames - TW.OFF_g_s) = 0x5e3d50 /\
  TICK_S + (TW.A_S_stats_tx_keepalives - TW.OFF_g_s) = 0x5e3d68 /\
  TICK_S + (TW.A_S_stats_tx_retransmits - TW.OFF_g_s) = 0x5e3d78 /\
  TICK_S + (TW.A_S_stats_ack_lost - TW.OFF_g_s) = 0x5e3d80.
Proof. repeat split; reflexivity. Qed.

(* session_lost's steps (TSess.v session_lost_m, :160-165), as image A's lib/A/Prog/session_lost_cg.v names them:
   the world after the two stores of :162-163, the world after set_state's store of the state (:84), and set_state's
   notice (:83). Image B has no session_lost function: its copies are inlined into their callers (this function's two
   lost arms), which make the two stores and call set_state; so the names are restated here, and three lemmas read
   them as set_state's. *)
Definition slost_w1 (Bw : list byte) : list byte := TW.set_S_desk_counter_valid (TW.set_S_inflight Bw 0) 0.
Definition slost_w2 (Bw : list byte) : list byte := TW.set_S_state (slost_w1 Bw) TS0.DIGINET_S_IDLE.
Definition slost_ntc (Bw : list byte) (why : Z) : TI.ntc :=
  TI.Ntc TS0.DIGINET_N_STATE TS0.DIGINET_S_IDLE (TW.S_state (slost_w1 Bw)) why 0 0 0 0 None [] 0.
(* Image B's code makes session_lost_m's set_state_m step a call of set_state at slost_w1 Bw (st = S_IDLE). *)
Lemma slost_model_sstate : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (why : Z),
  TSS.session_lost_m I F Bw why = TSS.set_state_m I F (slost_w1 Bw) TS0.DIGINET_S_IDLE why.
Proof. intros I F Bw why. reflexivity. Qed.
Lemma slost_sstate : forall (Bw : list byte) (why : Z),
  slost_w2 Bw = sstate_w (slost_w1 Bw) TS0.DIGINET_S_IDLE /\
  slost_ntc Bw why = sstate_ntc (slost_w1 Bw) TS0.DIGINET_S_IDLE why.
Proof. intros Bw why. split; reflexivity. Qed.

(* The model's branches (TSess.v diginet_session_tick_m). The two lost arms are session_lost_m at Bw (above). The
   ack-lost arm's world and notice (:436-440): *)
Definition tick_ack_w1 (Bw : list byte) : list byte :=
  TW.set_S_stats_ack_lost (TW.set_S_inflight Bw 0) (TS0.u64 (TW.S_stats_ack_lost (TW.set_S_inflight Bw 0) + 1)).
Definition tick_ack_ntc (Bw : list byte) : TI.ntc :=
  TI.Ntc TS0.DIGINET_N_ACK_LOST (TW.S_state (tick_ack_w1 Bw)) 0 0
         (TW.S_inflight_counter (tick_ack_w1 Bw)) (DSpec.u16 (TW.S_inflight_retries (tick_ack_w1 Bw))) 0 0 None [] 0.

(* The step of :430-443 (the ack-timeout work), whose left answer returns at once and whose right answer goes on to
   the tail; and the tail of :445-471 (the keepalive and the queue). Both are the model's own text. *)
Definition tick_step (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (now : Z)
    : option (sum (list byte * Z) (list byte)) :=
  if negb (TW.S_inflight Bw =? 0) &&
     (TS0.ms_m (TW.S_cfg_ack_timeout_ms Bw) <=? TS0.u64 (now - TW.S_inflight_sent_us Bw)) then
    if TW.S_inflight_retries Bw <? TW.S_cfg_max_retries Bw then
      match TSS.retransmit_m I F Bw now with
      | None => None
      | Some (B, r) => if r <? 0 then Some (inl (B, r)) else Some (inr B)
      end
    else
      match TSS.call_notify I F (tick_ack_w1 Bw) (tick_ack_ntc Bw) with
      | None => None
      | Some (B, _) => Some (inr B)
      end
  else Some (inr Bw).
Definition tick_tail (I : TI.timg) (F : option TI.tframe) (B : list byte) (now : Z) : option (list byte * Z) :=
  if negb (TW.S_state B =? TS0.DIGINET_S_ONLINE) || negb (TW.S_inflight B =? 0) ||
     (now <? TW.S_backoff_until_us B) then Some (B, DLib.DIGINET_OK)
  else if TW.S_next_keepalive_us B <=? now then
    let B := TW.set_S_next_keepalive_us B
               (TS0.u64 (TW.S_next_keepalive_us B + TS0.ms_m (TW.S_cfg_keepalive_ms B))) in
    let B := if TW.S_next_keepalive_us B <=? now
             then TW.set_S_next_keepalive_us B (TS0.u64 (now + TS0.ms_m (TW.S_cfg_keepalive_ms B))) else B in
    let B := TW.set_S_stats_tx_keepalives B (TS0.u64 (TW.S_stats_tx_keepalives B + 1)) in
    TSS.send_data_m I F B [DSpec.b8 0] 1 now
  else if TW.S_queued B =? 0 then Some (B, DLib.DIGINET_OK)
  else
    let allow := DLib.int_of_bool ((TW.S_display_sent B =? 0) ||
                   (TW.S_cfg_display_gap_us B <=? TS0.u64 (now - TW.S_last_display_us B))) in
    match TS0.take_m B allow with
    | None => None
    | Some (B, (body, body_len, has_display, n)) =>
        if n =? 0 then Some (B, DLib.DIGINET_OK)
        else
          let B := if has_display =? 0 then B
                   else TW.set_S_last_display_us (TW.set_S_display_sent B 1) now in
          TSS.send_data_m I F B (firstn (Z.to_nat body_len) body) n now
    end.

(* The whole model, branch by branch: the state dispatch of :418-427, then the step and the tail. *)
Lemma tick_model : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (now : Z),
  TSS.diginet_session_tick_m I F Bw now =
  (let st := TW.S_state Bw in
   if (st =? TS0.DIGINET_S_CLOSED) || (st =? TS0.DIGINET_S_IDLE) then Some (Bw, DLib.DIGINET_OK)
   else if (st =? TS0.DIGINET_S_WAKING) &&
           (TS0.ms_m (TW.S_cfg_wake_timeout_ms Bw) <=? TS0.u64 (now - TW.S_wake_sent_us Bw)) then
     match TSS.session_lost_m I F Bw TS0.DIGINET_R_WAKE_TIMEOUT with
     | None => None
     | Some (B, _) => Some (B, DLib.DIGINET_OK)
     end
   else if (st =? TS0.DIGINET_S_ONLINE) &&
           (TS0.ms_m (TW.S_cfg_offline_ms Bw) <=? TS0.u64 (now - TW.S_last_rx_us Bw)) then
     match TSS.session_lost_m I F Bw TS0.DIGINET_R_SILENCE with
     | None => None
     | Some (B, _) => Some (B, DLib.DIGINET_OK)
     end
   else
     match tick_step I F Bw now with
     | None => None
     | Some (inl (B, r)) => Some (B, r)
     | Some (inr B) => tick_tail I F B now
     end).
Proof. intros I F Bw now. reflexivity. Qed.

(* The bytes some path of the call stores outside its own frames, field by field: g_s's inflight,
   desk_counter_valid, state, inflight_retries, the two retry bytes of inflight_frame, inflight_sent_us,
   next_keepalive_us, display_sent, last_display_us and the four stats counters; the two kinds of notice
   (notice_cg.v notice_wr: GOT.t[GOT.n] and GOT.n for an N_STATE notice at either lost world, made by set_state on
   image B, M.fly.on for the N_ACK_LOST one); io_send's for a frame of at most 1514 bytes (io_send_cg.v iosend_wr,
   the inlined send_raw of retransmit); take's queue stores (take_cg.v take_wr's two G rows, widened: every queue
   entry q < 512, not only q < queued (S_queued at take's world is S_queued Bw, since no store before the call writes
   it; the row is widened so that it names no world), and queued; its three cell rows lie in this function's own
   frames, which the own-frame kit keeps, not E); and send_data's (send_data_cg.v senddata_wr, which contains
   io_send's). Each path stores a subset. *)
Definition tick_wr (Bw : list byte) (a : Z) : Prop :=
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_desk_counter_valid 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_state 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight_retries 4 a \/
  twb_fld TW.OFF_g_s TB_g_s (TW.A_S_inflight_frame + TS0.DIGINET_ETH_HDR_LEN + 12) 2 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight_sent_us 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_next_keepalive_us 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_display_sent 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_last_display_us 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_tx_frames 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_tx_keepalives 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_tx_retransmits 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_ack_lost 8 a \/
  notice_wr (slost_w2 Bw) (slost_ntc Bw TS0.DIGINET_R_WAKE_TIMEOUT) a \/
  notice_wr (slost_w2 Bw) (slost_ntc Bw TS0.DIGINET_R_SILENCE) a \/
  notice_wr (tick_ack_w1 Bw) (tick_ack_ntc Bw) a \/
  iosend_wr TC.SPEC_MAX_FRAME a \/
  (exists q, 0 <= q < TW.S_queue_N /\ twb_fld TW.OFF_g_s TB_g_s (TW.A_S_queue_bytes q) TW.S_queue_ESZ a) \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_queued 4 a \/
  senddata_wr a.
(* set_state's written range on either lost arm lies inside it (its state row, or its notice at slost_w2 Bw). *)
Lemma tick_wr_sstate : forall (Bw : list byte) (why a : Z),
  why = TS0.DIGINET_R_WAKE_TIMEOUT \/ why = TS0.DIGINET_R_SILENCE ->
  sstate_wr (slost_w1 Bw) TS0.DIGINET_S_IDLE why a -> tick_wr Bw a.
Proof.
  intros Bw why a Hwhy [_ [Hs | Hn]]; unfold tick_wr.
  - right; right; left. exact Hs.
  - destruct Hwhy as [-> | ->].
    + do 13 right. left. exact Hn.
    + do 14 right. left. exact Hn.
Qed.

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. set_state (its notice's callees) and notice read TF after the stores before them (set_state_cg.v
   sstate_apart, notice_cg.v notice_apart). *)
Definition tick_apart (Fr : option TI.tframe) (Bw : list byte) : Prop :=
  forall x, tick_wr Bw x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow
   (lib/B/YF0m.v Tfib_zero_shadow row (0x5df640, 0x5e3d98 - 0x5df640)). The instrumented checks of the accesses at
   s + 24 .. s + 18247 read it, and the trans_sh_any of io_send's frame (s + 216) comes from it. *)
Definition trans_tick_cells (B : asyms) : Prop := decode_zshadow_at B TICK_S (TICK_S + TW.SZ_g_s).

Section tick. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range tick_wr Bw,
   no meter charge (the side-stack frame changes st_fs only), and X: a0 = r (sign-extended), the world relation at
   the model's world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this
   function takes is released (by the call of __asan_stack_free_5). *)
Definition transport_tick_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs TICK_STK TICK_EV 0 (tick_wr Bw)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 r /\
       tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_diginet_session_tick_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 TICK_S -> YK11.getr regs 11 = w64 now ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TICK_STK -> spZ regs <= sp0 ->
    0 <= now < 2 ^ 64 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.diginet_session_tick_m timg_B TF Bw now = Some (Bw', r) ->
    trans_tframe_at B lyc Sc W memc regs TICK_STK TF ->
    trans_rom_view_rd W memc ->
    tick_apart TF Bw ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN) ->
    TW.S_queued Bw <= TC.QUEUE_MAX ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    TW.g_ncmd Bw <= TC.CMDS_MAX ->
    1 <= TW.S_cfg_max_cmds Bw -> 1 <= TW.S_cfg_max_body Bw ->
    count_cid TICK_CID (frames Sc) < fs_frames TICK_CID ->
    count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID ->
    count_cid TRANS_BC_CID (frames Sc) < fs_frames TRANS_BC_CID ->
    st_nev S + k + TICK_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_tick_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The statement the walk will prove: the class-5 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the record facts that no byte of G and
   no TRANS_RO_RD byte is an owned static or errno (they carry TF's trans_src_ok across the stack malloc's
   acall_kept, and the frame ranges, G and the TRANS_RO_RD bytes across it and each callee's acall_kept_g;
   DgnTransportBCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno give gx_ok and gx_noerrno from the first two), the
   allocator, meter and side-stack laws (frame_flag_lawP: the stack free's flag byte is an owned static;
   astack_free_law is not taken, since this function releases its frame by the call, not by an inline flag store),
   and the contracts of __asan_stack_malloc_5, __asan_set_shadow_f8, io_send (at the value the session's send
   pointer holds), set_state, __asan_memset, notice (at the value the session's notify pointer holds),
   __asan_stack_free_5, __asan_set_shadow_00, send_data and take (pc order of their first call: 0x8910c, 0x891d8,
   0x894c0, 0x8951c, 0x8958c, 0x895f4, 0x896bc, 0x896cc, 0x89830, 0x89874) give the contract at
   TB_diginet_session_tick. *)
Definition transport_diginet_session_tick_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) TICK_CID = transportb_sigma TB___asan_stack_malloc_5 ->
  transport_cells B -> trans_tick_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B TICK_CID) ->
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transportb_sigma TB___asan_set_shadow_f8) 0xf8) ->
  (forall fx' : YK11.FPState, @transport_io_send_cg fx' rc B MT (TI.ti_io_send timg_B)) ->
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_B)) ->
  (forall fx' : YK11.FPState,
     @astack_free_cls_realizes fx' rc segs B (transportb_sigma TB___asan_stack_free_5) TICK_CID) ->
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transportb_sigma TB___asan_set_shadow_00) 0) ->
  (forall fx' : YK11.FPState, @transport_send_data_cg fx' rc B MT (transportb_sigma TB_send_data)) ->
  (forall fx' : YK11.FPState, @transport_take_cg fx' rc B MT (transportb_sigma TB_take)) ->
  transport_diginet_session_tick_cg (transportb_sigma TB_diginet_session_tick).
End tick.
