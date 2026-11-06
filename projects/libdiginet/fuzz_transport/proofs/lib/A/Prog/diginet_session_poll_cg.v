(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module names changed; 358 of its 430 lines of code are new or changed and 371 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickCut.v, with its module paths and module names changed; 203 of its 254 lines of code are new or changed and 379 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_tick_cg.v, with its module paths and module names changed; 111 of its 173 lines of code are new or changed and 192 lines of the source are left out. *)
(* diginet_session_poll_cg: the ASan walk contract of diginet_session_poll (transport/src/diginet_session.c:505-527;
   model lib/TModel/TSess.v diginet_session_poll_m and poll_drain_m) on fuzz_transport.asan (e89be137db17) at
   0x8ad88 = transport_sigma TS_diginet_session_poll, size 1000, as STATEMENTS only (no proof). It takes a class-5
   side-stack frame for its local uint8_t buf[1514] (:507), calls io_now and io_recv through the session's now_us and
   recv pointers, diginet_session_deadline (a leaf), and diginet_session_rx and diginet_session_tick (G-form callees)
   while that frame is live, so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v
   ajournal_gx over G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), and the post is
   lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS). It stores no byte of G itself: every
   byte of G it changes, a callee stores. Its form is diginet_session_tick_cg.v's: a G walk with a class-5 frame of its
   own, released by a CALL of __asan_stack_free_5, whose locals are marked usable and out of scope by calls of
   __asan_set_shadow_00 / _f8 (lib/A/Prog/TransportRtCg.v aset_shadow_realizes, astack_free_cls_realizes).

   The contract. a0 = s = &g_s = 0x5df9c0 (TWorldA.v TA_g_s), a1 = max_wait_ms (an int, sign-extended). TF is the
   current heap frame (check_state_data_cg.v trans_tframe_at at this call's window), no byte of it is a byte of G
   (check_state_data_cg.v trans_tf_off_g) and no byte the call stores is a byte of it (poll_apart); the read-only bytes
   the callees read and the 8 bytes this function loads at 0x10350 are the image's (trans_rom_view_rd). The memory
   relates to the world Bw by image A's world relation (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview),
   g_fail_next Bw <= 1, and diginet_session_poll_m timg_A TF Bw max_wait_ms = Some (Bw', r). Class 5 of the side stack
   has two free frames (its own, and diginet_session_tick's below it, which tick takes directly and inside
   diginet_session_rx); class 1 has one (diginet_session_rx's), class 4 one (on_announce's), class 0 one (send_data's)
   and class 2 three (the deepest chain below diginet_session_rx). The function returns to ra with a0 = r
   (sign-extended), the callee-saved registers kept, no allocator event and no meter charge (its side-stack frame
   changes the state's st_fs only: ameter_fs_laws), its side-stack frame released (the caller's frames exactly), the
   caller's blocks exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or above alloc_ceiling outside the
   call's stack window [sp - POLL_STK, sp), the image bytes outside G, the owned statics and errno, the caller's block
   and frame bytes outside poll_wr), the world relation at Bw', and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/diginet_session_poll_c.v): a0 =
   W_BASE_PLAIN + OFF_g_s -> a0 = TA_g_s; a1 = w with -2 ^ 31 <= w < 2 ^ 31, kept; wmem -> tw_at; g_fail_next B <= 1
   kept as a premise (the code neither reads nor writes g_fail_next; io_recv's, diginet_session_rx's and
   diginet_session_tick's statements ask it) and the post's g_fail_next B' <= 1 kept in X (from the premise on the
   :508-509 path, else from the X of the last callee that returns a world: io_recv's on the paths that end at a
   recv); diginet_session_poll_m verbatim at timg_A (timg_plain -> timg_A); tframe_at -> trans_tframe_at at POLL_STK,
   and its off_world clause -> two facts (trans_src_ok alone admits a range of G, so trans_tframe_at gives neither):
   trans_tf_off_g (no byte of TF is a byte of G) and poll_apart (no byte the call stores is a byte of TF); tframe_ok
   TF is dropped (where a callee needs a bound on TF's end, trans_src_ok gives it below 2 ^ 63: DgnTransportCg.v
   trans_src_ok_rd); relro_img -> trans_rom_view_rd; stk, lo + FRAME <= sp, sp mod 16 and w_off_stack -> the
   journal's window premises; mem_inv is dropped. The post's munch, wmono, stk and mem_inv -> transport_cg_post (the
   journal at the return, acall_kept_g over poll_wr); wmem -> X's tw_at; the result register -> X's a0 = r.
   Premises the plain contract does not have:
   - the five frame counts: count_cid 5 (frames Sc) + 1 < fs_frames 5 (its own class-5 frame, and
     diginet_session_tick's, whose statement asks count_cid 5 < fs_frames 5 at its call state, where the frames are
     the own frame :: frames Sc, directly at 0x8b010 and inside diginet_session_rx, whose statement asks the same
     class-5 count at its call state); count_cid 1 (frames Sc) < fs_frames 1, count_cid 4 (frames Sc) < fs_frames 4,
     count_cid 0 (frames Sc) < fs_frames 0 and count_cid 2 (frames Sc) + 2 < fs_frames 2 (diginet_session_rx's other
     four counts, which it asks at its call state, where they are the counts of frames Sc: the own frame is of class
     5; diginet_session_tick's class-0 and class-2 counts are the same or weaker). With the first,
     __asan_stack_malloc_5 returns a frame (astack_malloc_realizes), so the real-stack arm is not taken and buf lies
     in the own side-stack frame (the argument of diginet_body_check_cg.v's code paragraph on its real-stack arm and of
     diginet_session_tick_cg.v's).
   - trans_tf_off_g TF and poll_apart TF (above). Every row of poll_wr is a byte of G, so trans_tf_off_g gives
     poll_apart; both are stated, in the form of diginet_session_rx_cg.v (srx_apart with trans_tf_off_g).
   - iorecv_rx_in TF Bw (io_recv_cg.v): io_recv's premise, taken on poll's own Bw and carried to both io_recv calls.
     The program's only stores of g_rx are receive's and LLVMFuzzerTestOneInput's (io_recv_cg.v), so no function that
     runs inside this one stores a byte of it: g_rx of the world each io_recv call is handed is g_rx Bw (the walk reads
     it from the model's world: io_recv_m, diginet_session_rx_m and diginet_session_tick_m change no byte of g_rx).
     receive's walk discharges it (it stores g_rx = tf_addr of its frame, TCb.v frame_from_base).
   - the four run invariants, on its own Bw: (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <=
     TC.SPEC_MAX_FRAME, (2) TW.S_queue_len Bw i <= DIGINET_CMD_MAX_LEN for every i < TW.S_queued Bw, (4) every PENDING
     command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX, and (5) 1 <= TW.S_cfg_max_cmds Bw and 1 <=
     TW.S_cfg_max_body Bw, in diginet_session_tick_cg.v's two-premise form. diginet_session_rx and
     diginet_session_tick ask all four at the world they are called with; io_recv, io_now and diginet_session_deadline
     ask none. Each is carried to the world of each call by the model: io_recv_m (g_rx_fail, g_rx_times, and m_rx_m's
     or m_tick_m's stores, m_rx_cg.v mrx_wr: M and OW only; M.fly.on is only set to 0) touches none of M.fly.len,
     g_s, g_cmd or g_ncmd and never sets M.fly.on non-zero; for diginet_session_rx_m and diginet_session_tick_m the
     walk proves the model facts that they keep them (no X of theirs states them, and no lemma of lib/TModel states
     them yet): the only writer of M.fly is io_send, whose stored length is the frame's, at most SPEC_MAX_FRAME;
     io_send's check_latest_sent only takes commands out of the PENDING set; no callee writes g_s.cfg; take, inside
     diginet_session_tick, removes queue entries and keeps the rest (lib/TSim/TickTakeW.v te_sq, sq Bf = unpick m
     (sq B), with lib/TSim/TakeOk.v Forall_pick). The walk reads the model's world at each call for the fields each
     invariant names, as diginet_session_rx's walk does for diginet_session_tick.
   - with (2) and (4), their index bounds TW.S_queued Bw <= TC.QUEUE_MAX and TW.g_ncmd Bw <= TC.CMDS_MAX, which
     diginet_session_rx and diginet_session_tick ask beside them (diginet_session_tick_cg.v says why): past those
     bounds g_s.queue[i] and g_cmd[s] are other world bytes, among them OW (m_rx_m's stores), GOT and g_q (the
     session callees' stores), so (2) and (4) are carried to each call only below them. No function this one calls
     writes g_ncmd, and take only lowers queued, so both bounds hold at each call; receive supplies them from the
     plain run (lib/TSim/Agree.v d3_ncmd and d3_ops, OPS_MAX = CMDS_MAX; lib/TSim/Deadline.v queued_le).
   - (3) check_state_data's invariant, which diginet_session_rx asks (guarded by the accept path of a data frame to
     on_data's N_DATA notice: fr_code b = 0, srx_mac_bad Bx b = false, S_desk_known Bx <> 0, memeq 6 (fr_src b)
     (S_desk_mac Bx) = true, S_state Bx <> S_CLOSED, fr_cmd b = DIGINET_CMD_DATA, ondata_dup Bx b = false,
     fr_keepalive b = false -> trans_src_ok and decode_off_win of [OW_dn_body Bx (GOT_ndata Bx), + fr_body_len b))
     at the world Bx and the bytes b of each of its calls. Those are the world io_recv leaves (whose m_rx_m stores
     OW.dn) and the bytes it hands over, neither of which is a function of Bw by a world invariant, so this statement
     takes (3) along the model's run, in the model's terms: poll_rx_each timg_A TF (poll_dn_in TF) Bw says, for every
     call of diginet_session_rx_m that diginet_session_poll_m makes at Bw, that under the same guards the range lies
     in TF's range. The walk gives diginet_session_rx's premise from it: trans_src_ok of a sub-range of TF from
     trans_tframe_at's trans_src_ok of TF at the call state (DgnTransportCg.v trans_src_ok_sub when fr_body_len b >
     0; for the empty range at a point of TF's closed range, each placement of TF holds of it), and decode_off_win
     from TF's at POLL_STK at entry (decode_off_win_sub for the range, then lia for the window: the call's sp' -
     SRX_STK >= sp - POLL_STK and sp' <= sp). receive carries it up (lib/TSim/RxData.v and RxOpLib.v are the plain
     sim's facts of the same pair: for an accepted data frame, m_rx's OW.dn entry at the frame's tf_addr + 30 with
     the frame's body length).
   - in the holds statement: trans_poll_cells (g_s's zero shadow), the side-stack laws, and trans_g_unowned,
     trans_g_no_errno, trans_ro_rd_unowned and trans_rom_no_errno (diginet_session_tick_cg.v's form): they carry TF's
     trans_src_ok across the stack malloc (its placement by DgnTransportCg.v trans_src_ok_inner, the stack malloc
     adding the own frame to the frames and keeping the blocks, and its decode_rd_ok by trans_rd_ok_sh, the range,
     its shadow bytes and its hull lying outside the fresh frame and that frame's shadow: trans_src_ok_disj_own; TF's
     bytes by the stack malloc's acall_kept with these record facts), across the frame's header stores, the plain
     shadow stores and the shadow fills (all in the own frame or its shadow, apart from TF by
     trans_src_ok_disj_own), across the leaves (every byte outside their windows kept; decode_off_win puts TF outside
     them) and across each G-form callee's acall_kept_g (trans_src_ok_kept over its clauses: TF lies outside G by
     trans_tf_off_g and outside the callee's written range by poll_apart, and for the buf the own frame is apart from
     TF's placement), the TRANS_RO_RD bytes (trans_ro_rd_scoped), and G (TransportGCg.v gx_kept_of_acall_kept with
     gx_ok and gx_noerrno, which DgnTransportCg.v G_HARNESS_gx_ok and G_HARNESS_gx_noerrno give from the first two).
   poll's own accesses are at fixed offsets of g_s (the 8-byte loads at s + 64, s + 80, s + 88), of its own frames,
   and the 8 bytes at 0x10350; the buf it hands io_recv and diginet_session_rx is 1514 bytes of its own frame; so its
   code needs no bound that the model does not give.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   1000 code bytes are equal in both files), 250 words:
     0x8ad88 - 0x8adc4 sp = sp - 160; 0x8ad8c stores 8 zero bytes at sp; ra at sp + 152, s0 .. s11 at sp + 144 ..
                      sp + 56, loaded back at 0x8b0d4 - 0x8b104; s0 = sp + 160 (the entry sp, kept to 0x8b0d0).
     0x8adc8 - 0x8add0 sp = sp & -32 (at most 0x10 below entry - 160); s1 = the realigned sp; s9 = max_wait_ms.
     0x8add4 - 0x8adec a2 = the 8-byte load of the GOT word 0xa40e8 (it holds 0xaca00), then the 4-byte load of the
                      flag word at 0xaca00; a1 = the 8-byte load of the GOT word 0xa4090 (it holds 0xac9f8), s5 = the
                      8-byte load at 0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s3 = s.
     0x8adf0 - 0x8ae00 the flag word = 0 goes to 0x8ae04 (s6 = 0); transport_cells row 6 gives 1. a0 = 0x6a0 = 1696
                      and the call of __asan_stack_malloc_5 (frame_alloc_5, 0x3dd04 = transport_sigma
                      TS___asan_stack_malloc_5) at 0x8adf8, return address 0x8adfc: a class-5 side-stack frame
                      (fs_frame_bytes 5 = 2048 bytes); s6 = the result.
     0x8ae08 - 0x8ae28 s2 = s6; s6 <> 0 goes to 0x8ae2c. The real-stack arm (s6 = 0): s2 = (sp - 1696) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s2), then sp = s2. With
                      count_cid 5 (frames Sc) + 1 < fs_frames 5 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s2 = s6.
     0x8ae2c          the 8-byte store of frame at s1 + 48 (its own machine frame).
     0x8ae30 - 0x8ae54 the frame header: 0x41b58ab3 at frame, the description string 0x1d88d ("1 32 1514 7 buf:507":
                      one variable, the 1514 bytes of buf at frame + 32) at frame + 8, the function's address 0x8ad88
                      at frame + 16.
     0x8ae3c, 0x8ae58 - 0x8ae6c s4 = (frame >> 3) + 0x7fff8000 (the frame's first shadow byte); shadow bytes 0..3 =
                      0xf1 (the left guard, by plain stores).
     0x8ae70 - 0x8ae7c s7 = s4 + 4 (the shadow byte of frame + 32); a0 = s7, a1 = 0xbe = 190; the call of
                      __asan_set_shadow_f8 (meta_fill_f8, 0x55390 = transport_sigma TS___asan_set_shadow_f8) at
                      0x8ae7c, return address 0x8ae80: shadow bytes 4..193 marked out of scope.
     0x8ae80 - 0x8aec8 shadow bytes 194..211 = 0xf3 (the right guard; plain stores at s4 + 0xc2 .. s4 + 0xd3).
     0x8aecc - 0x8aed4 a0 = s7, a1 = 0xbd = 189; the call of __asan_set_shadow_00 (meta_fill_00, 0x55270 =
                      transport_sigma TS___asan_set_shadow_00) at 0x8aed4, return address 0x8aed8: shadow bytes 4..192
                      = 0 (buf's 189 whole granules usable).
     0x8aed8 - 0x8aedc the plain store of 2 at s4 + 0xc1 (shadow byte 193: the last 2 of buf's 1514 bytes usable).
     0x8aee0 - 0x8aee8 s10 = -1 (DIGINET_E_ARG); the 8-byte stores of s6 (frame) at s1 + 16 and of s7 at s1 + 8.
     0x8aeec          s = 0 goes to 0x8b094 (the return of -1, :508); s = 0x5df9c0, so not taken.
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; for an 8-byte access any k <> 0 goes
                      to the error path. The three checked fields are s + 80 (shadow byte address s11), s + 88 (its
                      shadow byte address kept at s1 + 24 from 0x8af18) and s + 64 (shadow byte address s5 from
                      0x8af34; the shadow base in s5 is not used again).
     0x8aef0 - 0x8af08 s6 = s + 80; the check of the 8-byte load at s + 80; a0 = the 8-byte load there (S_io_recv
                      Bw); 0 goes to 0x8b094 (the return of -1, :508-509).
     0x8af0c - 0x8af28 s7 = s + 88; the check of the 8-byte load at s + 88; a1 = the 8-byte load there (S_io_now_us
                      Bw); 0 goes to 0x8b094.
     0x8af2c - 0x8af40 s8 = s + 64; the check of the 8-byte load at s + 64; a0 = the 8-byte load there (S_io_ctx).
     0x8af44          the indirect call (jalr a1) through the now_us pointer, return address 0x8af48 (:510;
                      struct diginet_session + 88, io.now_us -> io_now): a1 = S_io_now_us
                      Bw, which the model's call_now tests against TI.ti_io_now timg_A = 0x8356c (TPoll.v
                      call_now_inv). s10 = its result now.
     0x8af4c - 0x8af54 a0 = s, a1 = now; the call of diginet_session_deadline (0x8a9d4 = transport_sigma
                      TS_diginet_session_deadline) at 0x8af54, return address 0x8af58 (:511); a0 = its result due.
     0x8af58 - 0x8af7c now >= due (unsigned) gives a3 = 0; else a1 = the 8-byte load at 0x10350
                      (0x20c49ba5e353f7cf, TRANS_K_POLL, read through trans_rom_view_rd), a0 = ((due - now + 999)
                      mod 2 ^ 64) >> 3, a3 = the high 64 bits of the unsigned product a0 * a1, >> 4: (due - now + 999)
                      / 1000 (:512-513).
     0x8af80 - 0x8af90 a0 = a3 sign-extended from bit 31; a0 < max_wait_ms keeps a0, else a0 = max_wait_ms;
                      max_wait_ms >= 0 sets a3 = a0 (:514-515).
     0x8af94 - 0x8afb8 the checks of the 8-byte loads at s + 80 and s + 64; a0 = S_io_ctx, a4 = S_io_recv; s9 =
                      frame + 32 = buf; a3 = a3 sign-extended from bit 31 (the timeout, which io_recv does not read);
                      a2 = 0x5ea = 1514; a1 = buf.
     0x8afbc          the indirect call (jalr a4) through the recv pointer, return address 0x8afc0 (:516; struct
                      diginet_session + 80, io.recv -> io_recv): a4 = S_io_recv Bw, which call_recv tests against
                      TI.ti_io_recv timg_A = 0x834c4 (TPoll.v call_recv_inv). s10 = its result r1.
     0x8afc4          r1 < 0 goes to 0x8b094 (the return of r1, :517-518).
     0x8afc8 - 0x8afe0 the checks of the 8-byte loads at s + 88 (through the address at s1 + 24) and s + 64; a0 =
                      S_io_ctx, a1 = S_io_now_us.
     0x8afe4          the indirect call (jalr a1) through the now_us pointer, return address 0x8afe8 (:519); a3 = its
                      result now2.
     0x8afec          r1 = 0 goes to 0x8b008 (no diginet_session_rx call, :520).
     0x8aff0 - 0x8b000 a0 = s, a1 = buf, a2 = r1, s10 = now2; the call of diginet_session_rx (0x87594 = transport_sigma
                      TS_diginet_session_rx) at 0x8b000, return address 0x8b004 (:521); a3 = s10 (now2).
     0x8b008 - 0x8b010 a0 = s, a1 = now2; the call of diginet_session_tick (0x892b8 = transport_sigma
                      TS_diginet_session_tick) at 0x8b010, return address 0x8b014 (:522).
     the drain (:523-526):
     0x8b014 - 0x8b020 the checks of the 8-byte loads at s + 80 and s + 64.
     0x8b024 - 0x8b034 (the loop's head) a0 = S_io_ctx, a4 = S_io_recv, a2 = 1514, a1 = buf, a3 = 0.
     0x8b038          the indirect call (jalr a4) through the recv pointer, return address 0x8b03c (:524); s10 = its
                      result r.
     0x8b040          r <= 0 goes to 0x8b094 (the return of r, :526: r < 0 ? r : 0 is r here).
     0x8b044 - 0x8b060 the checks of the 8-byte loads at s + 88 and s + 64; a1 = S_io_now_us, a0 = S_io_ctx; s10 = r
                      sign-extended from bit 31.
     0x8b064          the indirect call (jalr a1) through the now_us pointer, return address 0x8b068 (:525); a3 = its
                      result now.
     0x8b06c - 0x8b078 a0 = s, a1 = buf, a2 = r; the call of diginet_session_rx at 0x8b078, return address 0x8b07c.
     0x8b07c - 0x8b088 the checks of the 8-byte loads at s + 80 and s + 64; the second one at k = 0 goes to the loop's
                      head 0x8b024.
     the epilogue, 0x8b094 - 0x8b10c (every path):
     0x8b094 - 0x8b09c a1 = 190, a0 = the 8-byte load at s1 + 8 (s7: the shadow byte of buf); the call of
                      __asan_set_shadow_f8 at 0x8b09c, return address 0x8b0a0: shadow bytes 4..193 marked out of scope.
     0x8b0a0 - 0x8b0a8 the header word 0x45e0360e stored at frame.
     0x8b0ac - 0x8b0b0 a0 = the 8-byte load at s1 + 16 (the stack malloc's result); 0 goes to 0x8b0c0 (the
                      real-stack arm; not taken).
     0x8b0b4 - 0x8b0b8 a1 = 0x6a0 = 1696; the call of __asan_stack_free_5 (frame_release_5, 0x3df10 = transport_sigma
                      TS___asan_stack_free_5) at 0x8b0b8, return address 0x8b0bc: the frame's 256 shadow bytes = 0xf5
                      and the zero store at its flag byte (TransportRtCg.v astack_free_cls_realizes); to 0x8b0cc.
     0x8b0c0 - 0x8b0c8 the real-stack arm's release: a1 = 0xd4 = 212, a0 = s4, the call of __asan_set_shadow_00 at
                      0x8b0c8 (not taken).
     0x8b0cc - 0x8b10c a0 = s10 (the result); sp = s0 - 160, ra and s0 .. s11 loaded back, sp = sp + 160, return. a1 ..
                      a7 at the return are not stated.
   No tail jump: the calls are jal with link (the stack malloc, the four shadow fills (0x8ae7c and 0x8b09c to
   __asan_set_shadow_f8, 0x8aed4 and 0x8b0c8 to __asan_set_shadow_00), diginet_session_deadline, diginet_session_rx
   twice, diginet_session_tick, the stack free, and the 13 error-path calls) and five jalr with link (io_now at
   0x8af44, 0x8afe4 and 0x8b064, io_recv at 0x8afbc and 0x8b038); every j is inside the function, and the function's
   own return is the ret at 0x8b10c.
   The model and the code (lib/TModel/TPoll.v poll_cases and poll_drain_cases cut diginet_session_poll_m and
   poll_drain_m at these branches): the tests at 0x8af08 and 0x8af28 are S_io_recv Bw =? 0 and S_io_now_us Bw =? 0
   (:508-509, the result DIGINET_E_ARG = -1 with the world unchanged); the call at 0x8af44 is call_now at Bw, the one
   at 0x8af54 diginet_session_deadline_m Bw now; the wait of :512-515 goes only to a3 of the recv call, which io_recv
   does not read, so it is not a fact of the model's world; the call at 0x8afbc is call_recv at Bw with cap
   DIGINET_MAX_FRAME_LEN = 1514; r1 < 0 returns r1 with io_recv's world; the call at 0x8afe4 is call_now at that world,
   the call at 0x8b000 (when 0 < r1) is diginet_session_rx_m at it with the bytes io_recv handed over and now2, the
   call at 0x8b010 diginet_session_tick_m at the world after; the loop is poll_drain_m with the fuel
   Z.to_nat (g_rx_times B3) at its start (each turn: call_recv, and when 0 < r, call_now and diginet_session_rx_m;
   r <= 0 returns r, which is the model's (if r <? 0 then r else 0)). io_recv's result r with 0 < r is the number of
   bytes it handed over (TPoll.v io_recv_m_ret), which the code passes as diginet_session_rx's length. The code has no
   trap of its own; the model's None cases are call_now's and call_recv's pointer tests, diginet_session_deadline_m's,
   io_recv_m's, diginet_session_rx_m's, diginet_session_tick_m's and the drain out of fuel, all ruled out by the model
   premise.
   Error paths (13 calls; no abort) and the facts that rule them out:
     TS___asan_report_load8 0x596a8 (errpath_load8) at 0x8b090 (s + 64), 0x8b114 (s + 88), 0x8b11c (s + 64),
       0x8b124 (s + 80), 0x8b12c (s + 80), 0x8b134 (s + 88), 0x8b13c (s + 64), 0x8b144 (s + 80), 0x8b14c (s + 64),
       0x8b154 (s + 88), 0x8b15c (s + 64), 0x8b164 (s + 80), 0x8b16c (s + 64).
     Each guards a naturally aligned 8-byte access inside g_s's payload [0x5df9c0, 0x5e4118) (2283 whole granules),
     whose shadow bytes are 0 (trans_poll_cells, read at each AR state by DgnTransportCg.v decode_zshadow_rd), so
     k = 0.
     The shadow fills' own premise (aset_shadow_realizes; the calls at 0x8ae7c, 0x8aed4 and 0x8b09c, and the one at
     0x8b0c8 that the count premise excludes): a0 = shadow_addr frame + 4 with a1 = 190 or 189, inside
     [shadow_addr frame, shadow_addr frame + fs_frame_bytes 5 / 8) = the frame's 256 shadow bytes (4 + 190 <= 256), and
     the frame is a live frame of the state.
     The stack free's own premise (astack_free_cls_realizes): a0 = frame, the frame is live, and the word at
     frame + 2040 still holds the flag byte's address (astack_malloc_realizes' rdword; no store of this function or of
     a callee writes it: buf ends at frame + 1546, the shadow stores go to the shadow band, and each callee's
     acall_kept_g keeps the bytes of this frame outside the callee's written range, io_recv's being buf).
   Writes: its own machine frame (the 8 zero bytes at entry sp - 160 (0x8ad8c), ra and s0 .. s11 at sp + 56 ..
   sp + 152, and s1 + 8, s1 + 16, s1 + 24, s1 + 48 after the realignment); its own side-stack frame (the header and
   buf, which io_recv fills), that frame's shadow bytes and its flag byte; io_recv's (io_recv_cg.v iorecv_wr:
   g_rx_fail, g_rx_times, m_rx's mrx_wr or m_tick's mtick_wr, and buf), diginet_session_rx's (srx_wr) and
   diginet_session_tick's (tick_wr) stores; io_now and diginet_session_deadline store nothing outside their own
   windows. No byte of a caller's frame or block is written, so poll_wr, the bytes of G the callees store, is the
   written range. The G kit for the own frame is diginet_session_tick_cg.v's (TransportGCg.v dk_kept_own_g with dkg_nf
   and dkg_nf_sep, dk_kept_trans_nf_g for every callee, dkg_frame_al64, dk_kept_frame_byte_g; CanKit.v
   can_stack_malloc_at read inside the G journal through gx_lift), with the shadow fills and the stack free as steps
   whose written bytes are the own frame's shadow bytes and its flag byte.
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_5 as astack_malloc_realizes ... POLL_CID (with pc_stack_malloc (as_code B) POLL_CID =
       transport_sigma TS___asan_stack_malloc_5): count_cid 5 (frames Sc) < fs_frames 5 from the count premise.
     __asan_set_shadow_f8 as TransportRtCg.v aset_shadow_realizes (transport_sigma TS___asan_set_shadow_f8) 0xf8, calls
       at 0x8ae7c and 0x8b09c: ecall_pre from the journal; the own frame is live; a0 = shadow_addr frame + 4, a1 = 190.
     __asan_set_shadow_00 as TransportRtCg.v aset_shadow_realizes (transport_sigma TS___asan_set_shadow_00) 0, the call
       at 0x8aed4 (a0 = shadow_addr frame + 4, a1 = 189). The call at 0x8b0c8 is on the real-stack arm, which the
       count premise excludes.
     io_now as its leaf statement (io_now_cg.v transport_io_now_cg, at io_now_c.v IO_NOW = TI.ti_io_now timg_A =
       0x8356c, io_now_cg.v io_now_at_timg; read at this unit's model by DgnTransportCg.v transport_leaf_at, through
       TransportGCg.v gx_call_leaf and the leaf bridge; calls at 0x8af44, 0x8afe4, 0x8b064): the pointer the code
       loads is S_io_now_us of the world there (tw_read), equal to TI.ti_io_now timg_A by call_now; ecall_pre from the
       journal at the call state (sp' the realigned sp); tw_at at csw_view of the call memory (the world relation,
       read on G's image bytes, which are never hidden); the leaf's stk / rng premises at g_now's 8 bytes (image
       bytes, outside every window). Its X: a0 = io_now_m of that world (g_now, 0 <= now < 2 ^ 64); no byte outside
       its window [sp' - ESTACK, sp') changes.
     diginet_session_deadline as its leaf statement (diginet_session_deadline_cg.v
       transport_diginet_session_deadline_cg at transport_sigma TS_diginet_session_deadline, read by
       transport_leaf_at; call at 0x8af54): a0 = DIGINET_SESSION_DEADLINE_S = s, a1 = now (0 <= now < 2 ^ 64); tw_at
       at csw_view of the call memory at Bw (io_now changes no byte outside its window);
       diginet_session_deadline_m Bw now = Some due (the model premise); asan_cells (transport_cells rows 1-2); g_s's
       payload addressable (trans_poll_cells); its stk / off_stk / app_mem / rng premises from the journal's window
       and the image layout. Its X: a0 = due; no byte outside its window changes.
     io_recv as io_recv_cg.v transport_io_recv_cg at TI.ti_io_recv timg_A (= 0x834c4, io_recv_cg.v io_recv_at; calls
       at 0x8afbc and 0x8b038; a G-form callee composed in the same G journal, no gx_call_cg): the pointer the code
       loads is S_io_recv of the world there, equal to TI.ti_io_recv timg_A by call_recv; the journal at the call
       state (the own frame live); ra = 0x8afc0 / 0x8b03c (ret_ok, 4096 <= ra); gp, tp kept; a1 = bp = buf =
       frame + 32, a2 = cap = 1514 (0 <= cap < 2 ^ 32); sp' 32-aligned, sp0 - STK <= sp' - IORECV_STK (POLL_STK =
       176 + max of the callee windows >= 176 + IORECV_STK), sp' <= sp0;
       decode_in_fake of [buf, buf + 1514) (32 + 1514 <= 2048, the own frame, in the frames of the call state);
       transport_twr_ok_g at sp' (each byte an awr_byte of the journal's own frame list: in_frames); decode_rd_ok
       (the bytes present by astack_malloc_realizes; shadow bytes 4..192 = 0 and 193 = 2 since 0x8aedc, so the 1514
       bytes are marked usable; the hull is inside the frame's 256 shadow bytes, visible); decode_off_win at
       IORECV_STK (the frame lies below alloc_ceiling, io_recv's window above it); buf apart from G (a frame byte is
       outside the image: AR_laws' al_client_img); trans_tframe_at TF at IORECV_STK (this walk's at POLL_STK,
       carried); trans_tf_off_g TF; iorecv_apart TF Bx buf 1514 (its G rows are rows of poll_wr: poll_apart; buf lies
       in the own frame, a fresh side-stack frame apart from TF's placement: a heap block, another frame, the machine
       stack or a read-only range; a range of G is excluded by trans_tf_off_g); iorecv_rx_in TF Bx (the premise at
       Bw, with g_rx Bx = g_rx Bw); trans_rom_view_rd at the call memory (the stack malloc's acall_kept, the shadow
       fills, the leaves and each callee's acall_kept_g keep every TRANS_RO_RD byte: trans_ro_rd_scoped); tw_at at
       the world Bx of the call (Bw at 0x8afbc; the world after diginet_session_tick or after the last
       diginet_session_rx at 0x8b038) and g_fail_next Bx <= 1; io_recv_m timg_A TF Bx 1514 = Some (B1, r, got): the
       model premise through call_recv; st_nev S + k + IORECV_EV <= EV_MAX (IORECV_EV = 0). Its X: a0 = r, tw_at at
       B1, g_fail_next B1 <= 1, and the 1514 bytes at buf agree with got on its length.
     diginet_session_rx as diginet_session_rx_cg.v transport_diginet_session_rx_cg at transport_sigma
       TS_diginet_session_rx (calls at 0x8b000 and 0x8b078; a G-form callee in the same G journal): the journal at
       the call state (the own frame live); ra = 0x8b004 / 0x8b07c; gp, tp kept; a0 = SRX_S = s, a1 = buf, a2 = r =
       Z.of_nat (length got) (TPoll.v io_recv_m_ret: 0 < r), a3 = now (0 <= now < 2 ^ 64, io_now's X); sp'
       32-aligned, sp0 - STK <= sp' - SRX_STK, sp' <= sp0;
       0 < buf; garr8 of got at buf (io_recv's X, firstn (length got)); trans_src_ok of [buf, buf + r) by
       decode_in_fake at the call state with decode_rd_ok (inside buf's 1514 bytes, whose bytes and shadow bytes
       io_recv's acall_kept_g keeps outside its written range and the copy left present, and io_now's leaf post
       keeps); decode_off_win at SRX_STK; srx_buf_off_g (a frame byte is outside the image);
       tw_at at the world B1 io_recv left and g_fail_next B1 <= 1 (io_recv's X; io_now writes no world byte);
       diginet_session_rx_m timg_A TF B1 got now = Some (B2, _) (the model premise through poll_cases /
       poll_drain_cases); trans_tframe_at TF at SRX_STK; trans_tf_off_g TF; trans_rom_view_rd at the call memory;
       srx_apart TF got (srx_wr got is a row of poll_wr: poll_apart); the four run invariants and the two index
       bounds at B1 (above); the guarded (3) at B1 and got: from poll_rx_each, which gives poll_dn_in TF B1 got for
       this call (above);
       count_cid 5 at the call state = count_cid 5 (frames Sc) + 1 < fs_frames 5, and the class-1, 4, 0 and 2 counts
       = those of frames Sc (the count premises); st_nev S + k + SRX_EV <= EV_MAX (SRX_EV = 0). Its X: a0 = the
       result (not used), tw_at at B2, g_fail_next B2 <= 1.
     diginet_session_tick as diginet_session_tick_cg.v transport_diginet_session_tick_cg at transport_sigma
       TS_diginet_session_tick (the call at 0x8b010; a G-form callee in the same G journal): the journal at the call
       state; ra = 0x8b014; gp, tp kept; a0 = TICK_S = s, a1 = now2 (0 <= now2 < 2 ^ 64); sp' 32-aligned, sp0 - STK
       <= sp' - TICK_STK, sp' <= sp0; tw_at at B2 (the world diginet_session_rx left, or io_recv's when r1 = 0) and
       g_fail_next B2 <= 1; diginet_session_tick_m timg_A TF B2 now2 = Some (B3, _) (the model premise through
       poll_cases); trans_tframe_at TF at TICK_STK; trans_rom_view_rd; tick_apart TF B2 (tick_wr B2 is a row of
       poll_wr: poll_apart); the four run invariants and the two index bounds at B2; count_cid 5 at the call state =
       count_cid 5 (frames Sc) + 1 < fs_frames 5, count_cid 0 and count_cid 2 as the premises; st_nev + TICK_EV <=
       EV_MAX (TICK_EV = 0). Its X:
       a0 (not used), tw_at at B3, g_fail_next B3 <= 1.
     __asan_stack_free_5 as TransportRtCg.v astack_free_cls_realizes (transport_sigma TS___asan_stack_free_5)
       POLL_CID, the call at 0x8b0b8 (above).
   Each callee's own record facts are premises of its holds statement.
   Stack: 160 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the shadow fills, the stack free, the two leaves), io_recv's IORECV_STK,
   diginet_session_rx's SRX_STK or diginet_session_tick's TICK_STK: POLL_STK = 176 + SRX_STK (poll_stk_eq).

   The caller (with the return address after its jal): receive at 0x83a08 (return 0x83a0c): a0 = 0x5df9c0 (&g_s,
   formed at 0x839fc - 0x83a00), a1 = 0 (max_wait_ms), with g_rx = receive's heap frame (stored at 0x839e8), g_rx_len =
   min (n, 1514), g_rx_times = 1 or 2 and g_rx_fail = bit 1 of its poll_flags (:1012-1015). It supplies its G journal,
   tw_at, g_fail_next, the model premise (receive_m's by-poll branch), trans_tframe_at, trans_tf_off_g and poll_apart
   of its frame (a heap block, outside the image), iorecv_rx_in (g_rx = the frame's tf_addr: TCb.v frame_from_base),
   trans_rom_view_rd, the four run invariants with the two index bounds, poll_rx_each (from its own premise) and the
   five frame counts (receive takes no side-stack frame). *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require io_now_cg diginet_session_deadline_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LIN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.io_now_cg.
Module LSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_deadline_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_session_poll's frame (`sp = sp - 160` at TS_diginet_session_poll), the at most 0x10 bytes of
   `sp = sp & -32` (0x8adc8) below it, and the largest stack a callee uses below the realigned sp: ESTACK for
   __asan_stack_malloc_5, __asan_set_shadow_f8 / _00 and __asan_stack_free_5 (YG0d.v ecall_pre) and for the leaves
   io_now and diginet_session_deadline (LeafCgKit.v ecall_pre), io_recv's IORECV_STK, diginet_session_rx's SRX_STK
   and diginet_session_tick's TICK_STK. *)
Definition POLL_FRAME : Z := 160.
Definition POLL_ALIGN : Z := 0x10.
Definition POLL_STK : Z :=
  POLL_FRAME + POLL_ALIGN + Z.max ESTACK (Z.max IORECV_STK (Z.max SRX_STK TICK_STK)).
Lemma poll_stk_eq : POLL_STK = POLL_FRAME + POLL_ALIGN + SRX_STK.
Proof. reflexivity. Qed.
(* No allocator event: io_recv, diginet_session_rx and diginet_session_tick record none (each turn of the drain
   adds SRX_EV = 0), and the class-5 stack malloc, the shadow fills and the stack free record none (YG00.v
   stack_malloc, stack_free). *)
Definition POLL_EV : Z := 0.
Lemma poll_ev_callees : IORECV_EV = 0 /\ SRX_EV = 0 /\ TICK_EV = 0.
Proof. repeat split; reflexivity. Qed.
(* The side-stack class of its own frame (a0 = 1696 at 0x8adf4, the call of __asan_stack_malloc_5 at 0x8adf8): the
   class diginet_session_tick takes too, below it. diginet_session_rx's own class and those of its callees other than
   diginet_session_tick are others. *)
Definition POLL_CID : Z := 5.
Lemma poll_cid_callees :
  POLL_CID = TICK_CID /\ SRX_CID = 1 /\ ONANN_CID = 4 /\ SENDDATA_CID = 0 /\ ONDATA_CID = 2 /\
  POLL_CID <> SRX_CID /\ POLL_CID <> ONANN_CID /\ POLL_CID <> SENDDATA_CID /\ POLL_CID <> ONDATA_CID.
Proof. repeat split; try reflexivity; cbv; congruence. Qed.
(* Its first argument: g_s's base in image A; buf, its one local, at offset 32 of its class-5 frame (the description
   string at 0x1d88d), DIGINET_MAX_FRAME_LEN bytes inside the frame's 2048. *)
Definition POLL_S : Z := TA_g_s.
Definition POLL_BUF : Z := 32.
Definition POLL_CAP : Z := 1514.
Lemma poll_frame_fits :
  POLL_S = 0x5df9c0 /\ POLL_S = SRX_S /\ POLL_S = TICK_S /\ POLL_CAP = TS0.DIGINET_MAX_FRAME_LEN /\
  POLL_BUF + POLL_CAP = 1546 /\ 1546 <= fs_frame_bytes POLL_CID.
Proof. repeat split; cbv; congruence. Qed.
(* The addresses of the g_s fields the code reads (s + 64 io.ctx, s + 80 io.recv, s + 88 io.now_us) and of the
   read-only constant it loads. *)
Lemma poll_addrs :
  POLL_S + (TW.A_S_io_ctx - TW.OFF_g_s) = 0x5dfa00 /\
  POLL_S + (TW.A_S_io_recv - TW.OFF_g_s) = 0x5dfa10 /\
  POLL_S + (TW.A_S_io_now_us - TW.OFF_g_s) = 0x5dfa18 /\
  TRANS_K_POLL = 0x10350.
Proof. repeat split; reflexivity. Qed.

(* check_state_data's run invariant (3) at one call of diginet_session_rx_m, in the model's terms: at the world Bx and
   the bytes b of the call, under diginet_session_rx_cg.v's guards of its premise (3) (the accept path of a data frame
   to on_data's N_DATA notice: diginet_session_rx_cg.v srx_model), the range [OW.dn[GOT.ndata].body,
   + fr_body_len b) lies in the current heap frame F. *)
Definition poll_dn_in (F : option TI.tframe) (Bx b : list byte) : Prop :=
  DSpec.fr_code b = 0 -> srx_mac_bad Bx b = false -> TW.S_desk_known Bx <> 0 ->
  TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bx) = true -> TW.S_state Bx <> TS0.DIGINET_S_CLOSED ->
  DSpec.fr_cmd b = TS0.DIGINET_CMD_DATA -> ondata_dup Bx b = false -> DSpec.fr_keepalive b = false ->
  exists fr, F = Some fr /\
    TI.tf_addr fr <= TC.OW_dn_body Bx (TW.GOT_ndata Bx) /\
    TC.OW_dn_body Bx (TW.GOT_ndata Bx) + DSpec.fr_body_len b <= TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)).

(* P at every call of diginet_session_rx_m that poll_drain_m makes from the world Bx with the fuel (:524-525): a call
   follows each recv that hands over a frame (0 < r) while fuel is left; a recv that hands over a frame with no fuel
   left makes the model None. *)
Fixpoint poll_drain_rx (I : TI.timg) (F : option TI.tframe) (P : list byte -> list byte -> Prop)
    (Bx : list byte) (fuel : nat) {struct fuel} : Prop :=
  match fuel with
  | O => True
  | S f =>
      forall B1 r got, TSS.call_recv I F Bx TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r, got) -> 0 < r ->
        P B1 got /\
        (forall now B2 r2, TSS.call_now I B1 = Some now ->
           TSS.diginet_session_rx_m I F B1 got now = Some (B2, r2) -> poll_drain_rx I F P B2 f)
  end.

(* P at every call of diginet_session_rx_m that diginet_session_poll_m makes at Bw: the call after the first recv
   (:520-521, when it handed over a frame) and those of the drain, which starts after diginet_session_tick (:522) with
   the fuel g_rx_times. call_now and diginet_session_deadline_m leave the world as it is, so the first recv is at Bw. *)
Definition poll_rx_each (I : TI.timg) (F : option TI.tframe) (P : list byte -> list byte -> Prop) (Bw : list byte)
    : Prop :=
  forall B1 r1 got, TSS.call_recv I F Bw TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r1, got) -> 0 <= r1 ->
    (0 < r1 -> P B1 got) /\
    (forall now B2 B3 r3,
       TSS.call_now I B1 = Some now ->
       (if 0 <? r1 then exists r2, TSS.diginet_session_rx_m I F B1 got now = Some (B2, r2) else B2 = B1) ->
       TSS.diginet_session_tick_m I F B2 now = Some (B3, r3) ->
       poll_drain_rx I F P B3 (Z.to_nat (TW.g_rx_times B3))).

(* The bytes some path of the call stores outside its own frames (each path stores a subset): io_recv's g_rx_fail and
   g_rx_times and its callees' (m_rx_cg.v mrx_wr; m_tick_cg.v mtick_wr at any world), diginet_session_rx's
   (diginet_session_rx_cg.v srx_wr, at any bytes) and diginet_session_tick's (diginet_session_tick_cg.v tick_wr, at
   any world). The worlds and bytes of the callees' calls are the model's, which this statement does not name, so each
   row is that callee's range at any world: every disjunct of each is a byte of G. io_recv's buffer rows are buf, in
   this function's own frame, which the own-frame kit keeps, not the written range. *)
Definition poll_wr (a : Z) : Prop :=
  twa_fld TW.OFF_g_rx_fail TA_g_rx_fail TW.OFF_g_rx_fail TW.SZ_g_rx_fail a \/
  twa_fld TW.OFF_g_rx_times TA_g_rx_times TW.OFF_g_rx_times TW.SZ_g_rx_times a \/
  mrx_wr a \/
  (exists Bx : list byte, mtick_wr Bx a) \/
  (exists b : list byte, srx_wr b a) \/
  (exists Bx : list byte, tick_wr Bx a).

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. Each callee reads TF after the stores before it (io_recv_cg.v iorecv_apart, diginet_session_rx_cg.v
   srx_apart, diginet_session_tick_cg.v tick_apart). *)
Definition poll_apart (Fr : option TI.tframe) : Prop :=
  forall x, poll_wr x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented checks of the 8-byte loads at s + 64, s + 80 and s + 88 read it, and diginet_session_deadline's
   statement asks the payload addressable. *)
Definition trans_poll_cells (B : asyms) : Prop := decode_zshadow_at B POLL_S (POLL_S + TW.SZ_g_s).

Section poll. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range poll_wr, no
   meter charge (the side-stack frame changes st_fs only), and X: a0 = r (sign-extended), the world relation at the
   model's world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this
   function takes is released (by the call of __asan_stack_free_5). *)
Definition transport_poll_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    POLL_STK POLL_EV 0 poll_wr
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 r /\
       tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_diginet_session_poll_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (w r : Z) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 POLL_S -> YK11.getr regs 11 = w64 w ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - POLL_STK -> spZ regs <= sp0 ->
    - 2 ^ 31 <= w < 2 ^ 31 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.diginet_session_poll_m timg_A TF Bw w = Some (Bw', r) ->
    trans_tframe_at B lyc Sc W memc regs POLL_STK TF ->
    trans_tf_off_g TF ->
    trans_rom_view_rd W memc ->
    poll_apart TF ->
    iorecv_rx_in TF Bw ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN) ->
    TW.S_queued Bw <= TC.QUEUE_MAX ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    TW.g_ncmd Bw <= TC.CMDS_MAX ->
    1 <= TW.S_cfg_max_cmds Bw -> 1 <= TW.S_cfg_max_body Bw ->
    poll_rx_each timg_A TF (poll_dn_in TF) Bw ->
    count_cid POLL_CID (frames Sc) + 1 < fs_frames POLL_CID ->
    count_cid SRX_CID (frames Sc) < fs_frames SRX_CID ->
    count_cid ONANN_CID (frames Sc) < fs_frames ONANN_CID ->
    count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID ->
    count_cid ONDATA_CID (frames Sc) + 2 < fs_frames ONDATA_CID ->
    st_nev S + k + POLL_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_poll_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' r).

(* The statement the walk will prove: the class-5 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the record facts that no byte of G and
   no TRANS_RO_RD byte is an owned static or errno (they carry TF's trans_src_ok across the stack malloc's acall_kept
   and each callee's acall_kept_g, buf's placement, G and the TRANS_RO_RD bytes; DgnTransportCg.v G_HARNESS_gx_ok /
   G_HARNESS_gx_noerrno give gx_ok and gx_noerrno from the first two), the allocator, meter and side-stack laws
   (frame_flag_lawP: the stack free's flag byte is an owned static; astack_free_law is not taken, since this function
   releases its frame by the call, not by an inline flag store), and the contracts of __asan_stack_malloc_5,
   __asan_set_shadow_f8, __asan_set_shadow_00, io_now (at the value the session's now_us pointer holds),
   diginet_session_deadline, io_recv (at the value its recv pointer holds), diginet_session_rx, diginet_session_tick
   and __asan_stack_free_5 (pc order of their first call: 0x8adf8, 0x8ae7c, 0x8aed4, 0x8af44, 0x8af54, 0x8afbc,
   0x8b000, 0x8b010, 0x8b0b8) give the contract at TS_diginet_session_poll. *)
Definition transport_diginet_session_poll_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) POLL_CID = transport_sigma TS___asan_stack_malloc_5 ->
  transport_cells B -> trans_poll_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B POLL_CID) ->
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transport_sigma TS___asan_set_shadow_f8) 0xf8) ->
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transport_sigma TS___asan_set_shadow_00) 0) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIN.transport_io_now_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSD.transport_diginet_session_deadline_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_io_recv_cg fx' rc B MT (TI.ti_io_recv timg_A)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_session_rx_cg fx' rc B MT (transport_sigma TS_diginet_session_rx)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_session_tick_cg fx' rc B MT (transport_sigma TS_diginet_session_tick)) ->
  (forall fx' : YK11.FPState,
     @astack_free_cls_realizes fx' rc segs B (transport_sigma TS___asan_stack_free_5) POLL_CID) ->
  transport_diginet_session_poll_cg (transport_sigma TS_diginet_session_poll).
End poll.
