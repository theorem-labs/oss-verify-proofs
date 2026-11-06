(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module names changed; 358 of its 430 lines of code are new or changed and 371 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickCut.v, with its module paths and module names changed; 203 of its 254 lines of code are new or changed and 379 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_tick_cg.v, with its module paths and module names changed; 167 of its 226 lines of code are new or changed and 195 lines of the source are left out. *)
(* receive_cg: the ASan walk contract of receive (fuzz/fuzz_transport.c:995-1025, fuzz_dup, fuzz_alloc, op_begin and
   spec_read_frame inlined; model lib/TModel/TOps.v receive_m, with TCb.v op_begin_m, m_rx_m and settle_m) on
   fuzz_transport.asan (e89be137db17) at 0x837d0 = transport_sigma TS_receive, size 1124, as STATEMENTS only (no
   proof). It allocates the heap block of the frame it receives (the malloc wrapper), copies the input bytes into it,
   stores into OW, GOT, M, g_rx_send, g_rx, g_rx_len, g_rx_times and g_rx_fail (harness globals), calls
   diginet_session_poll, m_rx and diginet_session_rx (G-form callees) and settle (a donor-form callee), and frees the
   block by a tail jump to the free wrapper, so it is a G-form caller-journal walk that calls the allocator: the
   caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0,
   OUT = []), the post is lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS) with two
   allocator events and the meter charged for one malloc and one free, and the statement is stated for call contexts
   CTX with the trace facts of its two allocator calls, in the allocator-calling form of fuzz_decode's
   check_round_trip_cg.v (origin/ossv/recipes, projects/libreac/fuzz_decode/proofs/lib/A/Prog/check_round_trip_cg.v:
   first malloc before s0 changes, tail free). It takes no side-stack frame.
   receive is a direct call target: LLVMFuzzerTestOneInput and build_and_receive call it by jal at TS_receive (it is
   not reached through a pointer of the session, so it is stated at transport_sigma TS_receive, not at a TImg.v
   field).

   The contract. a0 = p, a1 = n = the length of bytes (a size_t, n <= 65535: the plain contract's bound), a2 = by_poll
   (an int, sign-extended), a3 = poll_flags (its low 32 bits pf; the code reads bits 0 and 1). The n bytes at p are
   bytes (garr8), and when n is not 0 they are placed by trans_src_ok (a heap block of the caller, a caller's
   side-stack frame, G, a read-only range or the machine stack) outside this call's stack window. The memory relates
   to the world Bw by image A's world relation (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview), g_fail_next
   Bw <= 1, and receive_m timg_A Bw a bytes by_poll pf is not None for every address a the malloc can return
   (recv_addr_ok: the plain contract's h_addr_ok). The read-only bytes the callees read are the image's
   (trans_rom_view_rd). The function returns to ra with the callee-saved registers kept, at most two allocator events,
   the block it allocated freed (the caller's blocks exactly), the caller's side-stack frames exactly, the meter
   charged at most recv_cost n, the bytes acall_kept_g G_HARNESS keeps (the bytes at or above alloc_ceiling outside the
   call's stack window [sp - RECV_STK, sp), the image bytes outside G, the owned statics and errno, the caller's block
   and frame bytes outside recv_wr bytes), and X: for the address a the malloc returned (recv_addr_ok a),
   receive_m timg_A Bw a bytes by_poll pf = Some (Bw', tt), the world relation at Bw' and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/receive_c.v, an SR contract with the allocator state): h_binds
   and the allocator's call_pre_k / call_post_k -> the G journal and transport_cg_post
   with the two allocator call rules (YC5d.v amalloc04_rule, afree04_rule) at the listing's trampolines and the trace
   facts trans_recv_uctx; receive_args: a0 = p, a1 = Z_to_bv 64 (length bytes), a2 = by_poll with -2 ^ 31 <=
   by_poll < 2 ^ 31, the low 32 bits of a3 = pf with 0 <= pf < 2 ^ 32, length bytes <= 65535 kept;
   blk_data B mem p bytes -> garr8 of bytes at p; h_src (n = 0, or off_world and in a user block of A, or above the
   caller's sp) -> when 0 < n, trans_src_ok and decode_off_win at RECV_STK (the off_world part is not needed: the
   bytes at p are read once, by the memcpy at 0x83830, before any store into G, and no callee is handed p); the model
   premise (forall a, h_addr_ok a -> receive_m timg_plain Bw a bytes by_poll pf <> None) verbatim at timg_A; wmem ->
   tw_at; g_fail_next Bw <= 1 kept (the code neither writes g_fail_next nor lets a callee write it out of range:
   the callees' statements ask it and give it back) and given back in X; relro_img -> trans_rom_view_rd;
   res_ok_slots / room_slots (the budget) -> st_nev S + k + RECV_EV <= EV_MAX, blocks_bytes Sc + RECV_LIVE <=
   LIVE_MAX and the meter premise mo_ok MT Sc T with recv_cost n <= T; the stack premises -> the journal's window
   premises; frm_zero of the entry's float state is not needed (transport_cg_post returns at the same float state,
   and no callee changes it). The post's
   receive_ret: the address a with h_addr_ok a and receive_m ... = Some (Bw', tt) -> X; the footprint (the world, the
   freed frame and the allocator's ctx) -> transport_cg_post's acall_kept_g over recv_wr bytes (the freed block is not
   a block of the caller, and the allocator's ctx is the allocator's: the journal keeps the caller's view outside
   them); wmem -> X's tw_at; blocks L' A' = blocks L A -> Permutation of ablocks.
   Premises the plain contract does not have:
   - the call context: the frame-pointer chain ch at entry (YCbq.v achain at sp and s0) and raZ regs :: spine ch in
     CTX. receive does not change s0 before its malloc call (0x83814; s0 is first written at 0x8381c) and restores s0
     and ra before its tail jump to free (0x83a70), so the malloc's trace is its return address 0x83818 followed by the
     tail of the entry context, and the free's trace is the entry context itself (trans_recv_uctx), the split of
     fuzz_decode's check_round_trip_cg.v dec_crt_uctx.
   - the five frame counts, diginet_session_poll_cg.v's (its count premises at the call state, where the frames are
     frames Sc: receive takes no side-stack frame); diginet_session_rx, called directly on the by_poll = 0 path, asks
     the class-5 count without the + 1 and the other four the same.
   - the four run invariants on its own Bw: (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <=
     TC.SPEC_MAX_FRAME, (2) TW.S_queue_len Bw i <= DIGINET_CMD_MAX_LEN for i < TW.S_queued Bw, (4) every PENDING command
     g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX, (5) 1 <= TW.S_cfg_max_cmds Bw and 1 <= TW.S_cfg_max_body Bw.
     diginet_session_poll and diginet_session_rx ask all four at their call world, settle asks (2) at its call world,
     m_rx asks none. Before those calls receive stores OW and GOT (the memsets), M.fail, OW.desk_off, g_rx_send and on
     the by-poll path g_rx, g_rx_len, g_rx_times and g_rx_fail, none of which an invariant reads below the index
     bounds (M.fail is M + 88, M.fly starts at M + 96; the invariants read M.fly, g_s, g_cmd[0 .. CMDS_MAX) and
     g_ncmd); m_rx_m stores M and OW only and sets M.fly.on to 0 only. For diginet_session_poll_m and
     diginet_session_rx_m (settle's world after either) the walk
     proves the model facts that they keep them: no X states them and no lemma of lib/TModel states them yet (the
     only writer of M.fly is io_send, whose stored length is the frame's; io_send's check_latest_sent only takes
     commands out of the PENDING set; no callee writes g_s.cfg; take, inside diginet_session_tick, removes queue
     entries and keeps the rest: lib/TSim/TickTakeW.v te_sq, sq Bf = unpick m (sq B), with lib/TSim/TakeOk.v
     Forall_pick). The walk reads the model's world at each call for the fields each invariant names.
   - with (2) and (4), their index bounds TW.S_queued Bw <= TC.QUEUE_MAX and TW.g_ncmd Bw <= TC.CMDS_MAX, which
     diginet_session_poll and diginet_session_rx ask beside them (diginet_session_tick_cg.v says why): past those
     bounds g_s.queue[i] and g_cmd[s] are other world bytes, among them OW and GOT (the memsets), the harness
     globals receive stores (g_rx_send, g_rx, g_rx_len, g_rx_times, g_rx_fail) and the callees' stores, so (2) and
     (4) are carried to each call, settle's included, only below them. No store of receive and no function it calls
     writes g_ncmd, and take only lowers queued, so both bounds hold at each call; the caller has them from the plain
     run (lib/TSim/Agree.v d3_ncmd and d3_ops, OPS_MAX = CMDS_MAX; lib/TSim/Deadline.v queued_le).
   - (3) check_state_data's invariant, in the model's terms (recv_dn_each): for every address a the malloc can return,
     with the frame F = Some (TFrame a bytes), at the call of diginet_session_rx on the by_poll = 0 path, at the world
     m_rx_m leaves and the bytes, diginet_session_poll_cg.v poll_dn_in F holds (under diginet_session_rx_cg.v's
     accept-path guards of its premise (3), the range lies in F); on the by-poll path, diginet_session_poll_cg.v
     poll_rx_each F (poll_dn_in F) holds at the world receive hands diginet_session_poll. The walk gives
     diginet_session_rx's premise (3) from it as diginet_session_poll's walk does (the range lies in the frame's
     block: decode_in_block), and passes poll_rx_each to diginet_session_poll. The caller carries it up; the plain
     sim's facts of the same pair are lib/TSim/RxData.v and RxOpLib.v (for an accepted data frame, m_rx's OW.dn
     entry at tf_addr + 30 with the frame's body length).
   - in the holds statement: trans_recv_cells (the zero shadow of OW's and GOT's payloads, and the shadow bytes of the
     rest of the two memsets' hulls), the record facts trans_g_unowned, trans_g_no_errno, trans_ro_rd_unowned and
     trans_rom_no_errno (they carry the bytes at p across the malloc to the memcpy: the malloc's acall_kept keeps
     them, with these facts for a range of G or of TRANS_RO_RD; their placement by DgnTransportCg.v
     trans_src_ok_inner, the malloc adding a block and keeping the frames, and their decode_rd_ok: for a heap block
     the placement alone, for a range of a side-stack frame the bytes and shadow bytes the malloc's acall_kept keeps,
     for a range of G, of TRANS_RO_RD or of the machine stack the shadow facts at the new AR state (trans_sh_any,
     stack_zshadow_ra), as DgnTransportCg.v trans_src_ok_kept's proof takes them; the TRANS_RO_RD bytes and G across
     the malloc, the memcpy, the memsets and each callee:
     trans_ro_rd_scoped, gx_kept_of_acall_kept with G_HARNESS_gx_ok and G_HARNESS_gx_noerrno), and the allocator and
     meter laws.
   The frame's placement: the heap block of max (n, 1) bytes the malloc returns (amalloc04_rule: 4096 <= a, the block
   (a, max (n, 1)) added to ablocks; AR_laws' al_blocks: a + max (n, 1) <= alloc_ceiling, so recv_addr_ok a) holds the
   n copied bytes; it is TF = Some (TFrame a bytes) for every callee: trans_tframe_at by decode_in_block,
   trans_tf_off_g and each callee's *_apart because a heap block is outside the image (AR_laws' al_client_img) and
   every callee's written range lies in G, and diginet_session_poll's iorecv_rx_in because g_rx = a (TCb.v
   frame_from_base).

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   1124 code bytes are equal in both files), 281 words:
     0x837d0 - 0x837ec sp = sp - 64; ra at sp + 56, s0 .. s5 at sp + 48 .. sp + 8, loaded back at 0x83a50 - 0x83a68
                      (sp = sp + 64 at 0x83a6c). No side-stack frame, no frame pointer.
     0x837f0 - 0x837fc s1 = poll_flags (a3), s3 = by_poll (a2), s2 = n (a1), s4 = p (a0).
     0x83800 - 0x83808 s5 = the 8-byte load at the GOT word 0xa4090, then at the cell 0xac9f8 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     0x8380c - 0x83814 a0 = n + (n = 0 ? 1 : 0) = max (n, 1) (fuzz_alloc's n ? n : 1); the call of the malloc wrapper
                      (0x53704 = transport_sigma TS___interceptor_trampoline_malloc = pc_wrap_malloc) at 0x83814, return
                      address 0x83818 = RECV_RA_MALLOC; s0 (the caller's) is not yet written.
     0x83818          a0 = 0 goes to 0x83b6c (the trap: the call of __asan_handle_no_return at 0x83b6c, then abort at
                      0x83b70; fuzz.h:86); amalloc04_rule returns 4096 <= a, so not taken. s0 = a = frame.
     0x83820 - 0x83830 n = 0 goes to 0x83834 (no copy, fuzz_dup); a0 = frame, a1 = p, a2 = n; the call of __asan_memcpy
                      (checked_memcpy, 0x523b0 = transport_sigma TS___asan_memcpy) at 0x83830, return address 0x83834.
     0x83834 - 0x83848 s4 = &OW = 0x5f3060 (TA_OW); a0 = OW, a1 = 0, a2 = 0x130 = 304; the call of __asan_memset
                      (checked_memset, 0x5284c = transport_sigma TS___asan_memset) at 0x83848, return address 0x8384c
                      (op_begin :390).
     0x8384c - 0x8385c a0 = &GOT = 0x5e52e0 (TA_GOT), a1 = 0, a2 = 0xe0 = 224; the call of __asan_memset at 0x8385c,
                      return address 0x83860 (:391).
     0x83860 - 0x83878 a1 = the 1-byte load of g_fail_next (0x5df120); the 4-byte store of -1 at OW + 232 (OW.desk_off,
                      :392) and of a1 at M + 88 = 0x5df1b8 (M.fail, :393). These and every later access at a constant
                      address of a global carry no instrumented check.
     each instrumented check below: before a 1-byte load at x, the shadow byte k at (x >> 3) + 0x7fff8000 (a signed
                      1-byte load); k = 0 goes on; else (x & 7) < k (signed) goes on; else the error path.
     the frame's code and send (spec_read_frame, :1002-1003), 0x8387c - 0x83914:
     0x8387c          n < 30 (unsigned) goes to 0x8390c.
     0x83880 - 0x838c0 the checks of the 1-byte loads at frame + 12 and frame + 13; the 16-bit big-endian ethertype from
                      them <> 0x885f goes to 0x8390c.
     0x838c4 - 0x83908 the checks of the 1-byte loads at frame + 14 and frame + 15; numbytes, big-endian, < 16 goes to
                      0x8390c; n - 14 >= numbytes (unsigned) goes to 0x83a74; else 0x8390c.
     0x83a74 - 0x83aec the checks of the 1-byte loads at frame + 18 .. frame + 21; a0 = the 32-bit big-endian send from
                      them; to 0x83910.
     0x8390c - 0x83914 a0 = 0 (from 0x8390c); the 4-byte store of a0 at g_rx_send (0x5e53e0 = TA_g_rx_send): the
                      model's fr_code bytes =? 0 ? fr_send bytes : 0 (DgnSpec.v fr_code / fr_send, the code of
                      spec_read_frame, decided by these tests).
     0x83918          by_poll = 0 (the 64-bit register: by_poll sign-extended) goes to 0x83a18.
     the by-poll path (:1005-1018), 0x8391c - 0x83a14:
     0x8391c - 0x83928 a1 = got = n when n < 1514 (unsigned), else 1514 (:1005).
     0x8392c - 0x839bc the same tests on the frame for the got bytes: n < 30 goes to 0x839c0 (got < 30 exactly when
                      n < 30, as 1514 >= 30); the checks and loads at frame + 12 .. frame + 15; got - 14 >= numbytes
                      goes to 0x83af0 (the checks and loads at frame + 18 .. frame + 21, a0 = send, to 0x839c4); else
                      0x839c0 (a0 = 0) (:1007-1008, fr_code / fr_send of firstn got bytes).
     0x839c4 - 0x839f8 a3 = (poll_flags & 1) + 1; a0 = bit 1 of poll_flags; s1 = a0 xor 1 (ticked, :1011); the 4-byte
                      store of the send value at g_rx_send, the 8-byte stores of got at g_rx_len (0x5f3040) and of frame
                      at g_rx (0x5df9a0), the 4-byte stores of a3 at g_rx_times (0x5f3020) and of a0 at g_rx_fail
                      (0x5f3000) (:1012-1015).
     0x839fc - 0x83a08 a0 = &g_s = 0x5df9c0, a1 = 0; the call of diginet_session_poll (0x8ad88 = transport_sigma
                      TS_diginet_session_poll) at 0x83a08, return address 0x83a0c (:1016).
     0x83a0c - 0x83a14 the 8-byte store of 0 at g_rx and the 4-byte store of 0 at g_rx_fail (:1017-1018); to 0x83a44.
     the m_rx path (:1020-1021), 0x83a18 - 0x83a40:
     0x83a18 - 0x83a20 a0 = frame, a1 = n; the call of m_rx (0x8488c = transport_sigma TS_m_rx) at 0x83a20, return
                      address 0x83a24; s1 = its result (ticked).
     0x83a24 - 0x83a40 a3 = the 8-byte load of g_now (0x5df100); a0 = &g_s, a1 = frame, a2 = n; the call of
                      diginet_session_rx (0x87594 = transport_sigma TS_diginet_session_rx) at 0x83a40, return address
                      0x83a44 (its result is not used).
     0x83a44 - 0x83a48 a0 = s1 (ticked, 0 or 1); the call of settle (0x83cac = transport_sigma TS_settle) at 0x83a48,
                      return address 0x83a4c (:1023).
     0x83a4c - 0x83a70 a0 = frame; ra and s0 .. s5 loaded back, sp = sp + 64; the jump without link to the free wrapper
                      (0x53700 = transport_sigma TS___interceptor_trampoline_free = pc_wrap_free) at 0x83a70, from the
                      entry sp with the entry ra and s0: the free's return is receive's return (:1024). a0 .. a7 at
                      the return are not stated (receive returns void).
   The model and the code (recv_model): every test is receive_m's, read through garr8 of the frame's bytes (the copy of
   bytes), tw_at and the registers: the malloc result 0 (fuzz_alloc_m's None), the spec_read_frame tests (fr_code of
   bytes, and of firstn got bytes on the by-poll path), by_poll =? 0; the stores are op_begin_m's (two memsets of
   0, set_OW_desk_off -1, set_M_fail (g_fail_next)), set_g_rx_send, and on the by-poll path set_g_rx_send, set_g_rx_len,
   set_g_rx, set_g_rx_times, set_g_rx_fail (recv_w2c), then set_g_rx 0 and set_g_rx_fail 0; the calls are
   diginet_session_poll_m at recv_w2c with max_wait_ms 0, or m_rx_m at recv_w2 with n and diginet_session_rx_m at its
   world with bytes and g_now of that world; then settle_m with ticked. The code has no trap of its own besides the
   malloc's NULL test; the model's None cases are fuzz_alloc_m's (a = 0) and the callees', all ruled out by the model
   premise (at the address the malloc returned, recv_addr_ok).
   Error paths (16 calls of TS___asan_report_load1 0x594c8, errpath_load1; the trap 0x83b6c / 0x83b70) and the facts
   that rule them out:
     at 0x83b7c (frame + 12), 0x83b88 (frame + 13), 0x83bac (frame + 14), 0x83bb8 (frame + 15), 0x83bdc .. 0x83c00
     (frame + 18 .. frame + 21), and on the by-poll path 0x83b94 (frame + 12), 0x83ba0 (frame + 13), 0x83bc4
     (frame + 14), 0x83bd0 (frame + 15), 0x83c0c .. 0x83c30 (frame + 18 .. frame + 21): each byte is below frame + 30
     <= frame + n (the tests read them only when n >= 30), inside the block the malloc returned, whose first n bytes are
     marked usable (AR_laws' al_blocks: the block's shadow).
     The trap: amalloc04_rule's 4096 <= a.
     The memcpy's own checks (aintrin_realizes' pre, through TransportGCg.v gx_intrin_at): the destination
     [frame, frame + n) is a block allocated since the journal's start (awr_byte), present and marked usable; the source
     [p, p + n) from trans_src_ok at the call state (across the malloc: its placement by trans_src_ok_inner, the malloc
     adding a block and keeping the frames, its bytes by the malloc's acall_kept and its decode_rd_ok as in the holds
     paragraph above; then trans_src_ok_rd: decode_rd_ok) and decode_off_win at RECV_STK; the two are apart (a heap
     block of the caller is another block, a side-stack frame is apart from every block (AR_laws' sep law), G and the
     read-only ranges are image bytes, the machine stack lies at or above alloc_ceiling); n < 2 ^ 32 (n <= 65535).
     The memsets' own checks: the destinations OW (304 bytes) and GOT (224 bytes) are bytes of G (writable through the
     G journal by TransportGRwA.v G_HARNESS_rw, not owned by trans_g_unowned), their shadow is 0 (trans_recv_cells) and
     their hulls' shadow bytes are visible: OW's hull is the shadow of [0x5f3040, 0x5f31c0) (g_rx_len's payload granule
     and three guard granules, OW's payload, six of OW's guard granules), GOT's the shadow of [0x5e52c0, 0x5e53c0) (four
     guard granules of g_s, GOT's payload) (trans_recv_cells).
   Writes: its own machine frame (ra, s0 .. s5 at sp + 8 .. sp + 56 after sp = sp - 64); the block it allocates (the
   copy; freed before the return); OW's and GOT's payloads, M.fail, g_rx_send, and on the by-poll path g_rx_len, g_rx,
   g_rx_times and g_rx_fail (bytes of G); m_rx's (m_rx_cg.v mrx_wr), diginet_session_rx's (srx_wr bytes) and
   diginet_session_poll's (diginet_session_poll_cg.v poll_wr) stores; settle stores nothing outside its frame; the
   allocator's own bytes are the runtime's (owned statics, the journal). No byte of a caller's frame or block is
   written, so recv_wr bytes, the bytes of G it and its callees store, is the written range.
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     the malloc wrapper as YC5d.v amalloc04_rule (with pc_wrap_malloc (as_code B) = transport_sigma
       TS___interceptor_trampoline_malloc), call at 0x83814, read inside the G journal (TransportGCg.v gx_open, the
       rule at the donor journal, gx_pack0; the rule's acall_kept keeps every byte of G: gx_kept_of_acall_kept): a0 =
       max (n, 1) < MALLOC_MAX; blocks_bytes Sc + max (n, 1) <= LIVE_MAX (the premise with RECV_LIVE); sp = entry sp -
       64, so ASTACK - o <= STK by the window premise (RECV_STK = 64 + ASTACK); gp, tp, ra = 0x83818 (ret_ok);
       st_nev Sc < EV_MAX; chain_pre at that sp with the entry s0 and the entry chain ch (the 56 bytes the prologue
       stores lie below the entry sp, the chain's records above it: YCbq.v achain); the trace decode_utrace
       (pc_malloc_ra0) (0x83818 :: tl c) of trans_recv_uctx; mo_ok MT Sc (mo_malloc MT (max (n, 1))) from the meter
       premise. Its post: the journal at k + 1, the block (a, max (n, 1)) added, 4096 <= a, frames kept, acall_kept
       outside its ASTACK window and the block, mo_le Sc S1 (mo_malloc MT (max (n, 1))).
     __asan_memcpy as aintrin_realizes ... OCpy (transport_sigma TS___asan_memcpy), call at 0x83830 (above).
     __asan_memset as aintrin_realizes ... OSet (transport_sigma TS___asan_memset), calls at 0x83848 and 0x8385c
       (above).
     diginet_session_poll as diginet_session_poll_cg.v transport_diginet_session_poll_cg at transport_sigma
       TS_diginet_session_poll (call at 0x83a08; a G-form callee in the same G journal): the journal at the call state;
       ra = 0x83a0c; gp, tp kept; a0 = POLL_S, a1 = w = 0; sp - 64 16-aligned, sp0 - STK <= sp - 64 - POLL_STK
       (RECV_STK = 64 + ASTACK >= 64 + POLL_STK), sp - 64 <= sp0; tw_at at recv_w2c Bw bytes a pf (the tw_fills of the
       memsets and the tw_writes of the stores) and g_fail_next of it <= 1 (no store writes g_fail_next);
       diginet_session_poll_m timg_A F (recv_w2c ...) 0 = Some (B2d, _) (the model premise through recv_model);
       trans_tframe_at F at POLL_STK (0 < a; garr8 of bytes at a: the memcpy's post, kept by the memsets and the
       stores, which write G; decode_in_block of [a, a + n) in (a, max (n, 1)); decode_off_win: the block lies below
       alloc_ceiling); trans_tf_off_g F and poll_apart F (the block is outside the image); trans_rom_view_rd at the
       call memory (the malloc's acall_kept, the memcpy, the memsets and the stores keep every TRANS_RO_RD byte:
       trans_ro_rd_scoped); iorecv_rx_in F (recv_w2c ...): g_rx of it is a, and TCb.v frame_from_base; the four run
       invariants and the two index bounds at recv_w2c (above); poll_rx_each F (poll_dn_in F) (recv_w2c ...) from
       recv_dn_each; the five counts (the premises: the frames are frames Sc); st_nev S + (k + 1) + POLL_EV <= EV_MAX.
       Its X: tw_at at B2d,
       g_fail_next B2d <= 1; the two stores after it give tw_at at set_g_rx_fail (set_g_rx B2d 0) 0.
     m_rx as m_rx_cg.v transport_m_rx_cg at transport_sigma TS_m_rx (call at 0x83a20; G-form, the same journal): a0 =
       tf_addr fr = a, a1 = n; ra = 0x83a24; sp - 64, MRX_STK <= ASTACK; trans_tframe_at (Some fr) at MRX_STK (as for
       diginet_session_poll); a + n < 2 ^ 64 (a + max (n, 1) <= alloc_ceiling); mrx_apart fr (mrx_wr lies in G, the
       block outside the image); trans_rom_view_rd; tw_at at recv_w2 Bw bytes; m_rx_m timg_A (Some fr) (recv_w2 ...) n =
       Some (Bx, ticked) (the model premise); MRX_EV = 0. Its X: a0 = ticked, tw_at at Bx.
     diginet_session_rx as diginet_session_rx_cg.v transport_diginet_session_rx_cg at transport_sigma
       TS_diginet_session_rx (call at 0x83a40; G-form, the same journal): ra = 0x83a44; a0 = SRX_S, a1 = buf = a, a2 =
       n, a3 = g_now Bx (the 8-byte load at 0x83a28, tw_read; 0 <= g_now < 2 ^ 64); sp - 64, SRX_STK <= ASTACK; 0 < a;
       garr8 of bytes at a (kept across m_rx: the block lies outside mrx_wr); trans_src_ok and decode_off_win of
       [a, a + n) (decode_in_block); srx_buf_off_g (the block is outside the image); tw_at at Bx and g_fail_next Bx <= 1
       (m_rx_m stores M and OW only); diginet_session_rx_m timg_A (Some fr) Bx bytes (g_now Bx) = Some (By, _) (the
       model premise); trans_tframe_at (Some fr) at SRX_STK; trans_tf_off_g (Some fr); trans_rom_view_rd; srx_apart
       (Some fr) bytes (srx_wr lies in G); the four run invariants and the two index bounds at Bx (above); the
       guarded (3) at Bx and bytes: from recv_dn_each's poll_dn_in, the range lies in the block (decode_in_block of a
       sub-range, or of the empty range
       at a point of [a, a + n]), off this call's window; count_cid 5 (frames Sc) < fs_frames 5 (from + 1) and the
       other four counts; SRX_EV = 0. Its X: tw_at at By, g_fail_next By <= 1.
     settle as settle_cg.v transport_settle_cg at transport_sigma TS_settle (call at 0x83a48; donor form, lifted with
       TransportGCg.v gx_call_cg: settle stores nothing outside its frame, so the world relation after it is the one it
       was handed): a0 = ticked (0 or 1); ra = 0x83a4c; sp - 64, SETTLE_STK <= ASTACK; tw_at at B3 (the by-poll
       path's world after the two stores at 0x83a0c - 0x83a10, or By); settle_m B3 ticked = Some (B4, tt) (the model
       premise); (2) at B3; SETTLE_EV = 0. Its X: B4 = B3.
     the free wrapper as YC5d.v afree04_rule (with pc_wrap_free (as_code B) = transport_sigma
       TS___interceptor_trampoline_free), the tail jump at 0x83a70: a0 = a with (a, max (n, 1)) in the blocks of that
       state (added by the malloc, kept by every callee's Permutation of ablocks); sp = the entry sp (o = spZ regs -
       sp0, ASTACK - o <= STK by the window premise); gp, tp, ra = the entry ra (ret_ok); st_nev < EV_MAX (k + 1 +
       0 < k + 2); chain_pre at the entry sp and s0 with ch (the records above the entry sp are kept: every callee
       keeps the bytes at or above alloc_ceiling outside its window); the trace decode_utrace (pc_free_ra0) c of
       trans_recv_uctx; the footprint premise (a block of the journal's start state is in FP): the block (a,
       max (n, 1)) is not live at the call state Sc (the malloc returned a block apart from every live one), so if it
       is a block of the start state it is one the journal no longer holds, which YCbq.v ajournal's clause for a start
       block not in the current blocks puts in FP; mo_ok MT S (mo_free MT) at that state from the meter premise
       (mo_ok MT Sc T, recv_cost n <= T) by ameter_laws' mo_ok_step over the malloc's mo_le (mo_malloc MT (max (n, 1)))
       and each callee's mo_le ... 0 (diginet_session_poll's, m_rx's, diginet_session_rx's and settle's posts). Its
       post is receive's: the journal at k + 2, the block removed (so the caller's blocks up to permutation), frames
       kept, acall_kept outside [sp - ASTACK, sp) and the block.
   Each callee's own record facts are premises of its holds statement.
   Stack: 64 bytes of its own; below sp - 64 the largest window is the malloc's ASTACK (diginet_session_poll's
   POLL_STK, m_rx's MRX_STK, diginet_session_rx's SRX_STK, settle's SETTLE_STK and the intrinsics' ESTACK are smaller);
   the tail free uses ASTACK from the entry sp: RECV_STK = 64 + ASTACK (recv_stk_eq).

   The callers (each with the return address after its jal): LLVMFuzzerTestOneInput at 0x81b6c (return 0x81b70): a0 =
   s8, a record of the input (in the input's block), a1 = its length, a2 = 0 (0x81b64) or 1 (0x81aac, the by-poll
   operation, which joins the call at 0x81ab4), a3 = 0 or, on the by-poll operation, the input byte loaded at 0x81960
   (0 when the input is used up, 0x81a88); build_and_receive at 0x85a88 (return 0x85a8c): a0 = s10, the frame it built
   in its class-5 side-stack frame, a1 = its length, a2 = 0, a3 = 0. Each supplies its G journal, the chain and its
   context in CTX, the placement of p, tw_at, g_fail_next, the model premise, trans_rom_view_rd, the four run
   invariants with the two index bounds, recv_dn_each, the five frame counts, and the allocator budget. The counts
   are of the caller's frames at the call: LLVMFuzzerTestOneInput holds a class-2 side-stack frame of its own
   (__asan_stack_malloc_2 at 0x812d4),
   so its class-2 count must leave room for it as well; build_and_receive holds a class-5 frame of its own, so its
   class-5 count must leave room for it (the + 1 of the class-5 premise is for diginet_session_poll's frame, which
   only the by-poll path takes; build_and_receive passes by_poll = 0). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_inflight_settle_cg check_latest_queue_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import settle_cg diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* receive's entry, a direct call target. *)
Lemma receive_at : transport_sigma TS_receive = 0x837d0.
Proof. reflexivity. Qed.

(* receive's frame (`sp = sp - 64` at its entry; no realignment). Its calls run from sp - 64: the malloc wrapper
   (ASTACK, amalloc04_rule), __asan_memcpy and __asan_memset (ESTACK), diginet_session_poll (POLL_STK), m_rx (MRX_STK),
   diginet_session_rx (SRX_STK) and settle (SETTLE_STK); the tail jump to the free wrapper runs from the entry sp
   (ASTACK, afree04_rule). The malloc's is the largest. *)
Definition RECV_FRAME : Z := 64.
Definition RECV_STK : Z :=
  Z.max ASTACK
    (RECV_FRAME + Z.max (Z.max ASTACK ESTACK) (Z.max POLL_STK (Z.max MRX_STK (Z.max SRX_STK SETTLE_STK)))).
Lemma recv_stk_eq : RECV_STK = RECV_FRAME + ASTACK.
Proof. reflexivity. Qed.
(* Two allocator events: the malloc and the free. The callees record none. *)
Definition RECV_EV : Z := 2.
Lemma recv_ev_callees : POLL_EV = 0 /\ MRX_EV = 0 /\ SRX_EV = 0 /\ SETTLE_EV = 0.
Proof. repeat split; reflexivity. Qed.
(* The live bytes it adds: one block of max (n, 1) <= 65535 bytes (n <= 65535). *)
Definition RECV_LIVE : Z := 65535.
(* The return address of its malloc call (the jal at 0x83814, 0x44 bytes after the entry). *)
Definition RECV_RA_MALLOC : Z := transport_sigma TS_receive + 0x48.
Lemma recv_ra_malloc_at : RECV_RA_MALLOC = 0x83818.
Proof. reflexivity. Qed.
(* g_s's base, which it hands diginet_session_poll and diginet_session_rx, and the addresses of the globals it stores
   or loads at constant addresses. *)
Definition RECV_S : Z := TA_g_s.
Lemma recv_addrs :
  RECV_S = POLL_S /\ RECV_S = SRX_S /\
  TA_OW = 0x5f3060 /\ TW.SZ_OW = 304 /\ TA_GOT = 0x5e52e0 /\ TW.SZ_GOT = 224 /\
  TA_OW + (TW.A_OW_desk_off - TW.OFF_OW) = 0x5f3148 /\ TA_M + (TW.A_M_fail - TW.OFF_M) = 0x5df1b8 /\
  TA_g_fail_next = 0x5df120 /\ TA_g_rx_send = 0x5e53e0 /\ TA_g_rx_len = 0x5f3040 /\ TA_g_rx = 0x5df9a0 /\
  TA_g_rx_times = 0x5f3020 /\ TA_g_rx_fail = 0x5f3000 /\ TA_g_now = 0x5df100.
Proof. repeat split; reflexivity. Qed.

(* Every address a successful malloc can return, as the plain contract asks of its model premise
   (lib/Prog/T/receive_c.v h_addr_ok). *)
Definition recv_addr_ok (a : Z) : Prop := 0 < a /\ a + 65536 <= 2 ^ 64.

(* The model's steps (TOps.v receive_m, :997-1024): the world after op_begin (:1001), after the first g_rx_send store
   (:1002-1003), the got of the by-poll path (:1005), the send value of the frame's code, the world handed to
   diginet_session_poll (:1007-1015) and the ticked of the by-poll path (:1011). *)
Definition recv_w1 (Bw : list byte) : list byte :=
  match TC.op_begin_m Bw with Some (B1, _) => B1 | None => Bw end.
Definition recv_send (b : list byte) : Z := if DSpec.fr_code b =? 0 then DSpec.fr_send b else 0.
Definition recv_w2 (Bw bytes : list byte) : list byte := TW.set_g_rx_send (recv_w1 Bw) (recv_send bytes).
Definition recv_got (bytes : list byte) : Z :=
  if TC.SPEC_MAX_FRAME <? Z.of_nat (length bytes) then TC.SPEC_MAX_FRAME else Z.of_nat (length bytes).
Definition recv_w2c (Bw bytes : list byte) (a pf : Z) : list byte :=
  TW.set_g_rx_fail
    (TW.set_g_rx_times
       (TW.set_g_rx_len
          (TW.set_g_rx (TW.set_g_rx_send (recv_w2 Bw bytes) (recv_send (firstn (Z.to_nat (recv_got bytes)) bytes))) a)
          (recv_got bytes))
       (if Z.land pf 1 =? 0 then 1 else 2))
    (Z.land (Z.shiftr pf 1) 1).
Definition recv_ticked (pf : Z) : Z := if Z.land (Z.shiftr pf 1) 1 =? 0 then 1 else 0.

(* The whole model, branch by branch. *)
Lemma recv_model : forall (I : TI.timg) (Bw : list byte) (a : Z) (bytes : list byte) (by_poll pf : Z),
  TOP.receive_m I Bw a bytes by_poll pf =
  if a =? 0 then None
  else
    match (if negb (by_poll =? 0) then
             match TSS.diginet_session_poll_m I (Some (TI.TFrame a bytes)) (recv_w2c Bw bytes a pf) 0 with
             | None => None
             | Some (B2d, _) => Some (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0, recv_ticked pf)
             end
           else
             match TC.m_rx_m I (Some (TI.TFrame a bytes)) (recv_w2 Bw bytes) (Z.of_nat (length bytes)) with
             | None => None
             | Some (Bx, ticked) =>
                 match TSS.diginet_session_rx_m I (Some (TI.TFrame a bytes)) Bx bytes (TW.g_now Bx) with
                 | None => None
                 | Some (By, _) => Some (By, ticked)
                 end
             end) with
    | None => None
    | Some (B3, ticked) =>
        match TC.settle_m B3 ticked with
        | None => None
        | Some (B4, _) => Some (B4, tt)
        end
    end.
Proof.
  intros I Bw a bytes by_poll pf. unfold TOP.receive_m, TOP.fuzz_dup_m, TOP.fuzz_alloc_m.
  destruct (a =? 0); reflexivity.
Qed.

(* check_state_data's run invariant (3) for every call of diginet_session_rx_m receive_m makes, in the model's terms,
   for every address the malloc can return: on the by_poll = 0 path at the world m_rx_m leaves and the bytes; on the
   by-poll path at every call diginet_session_poll_m makes (diginet_session_poll_cg.v poll_rx_each). *)
Definition recv_dn_each (I : TI.timg) (Bw bytes : list byte) (by_poll pf : Z) : Prop :=
  forall a, recv_addr_ok a ->
    if by_poll =? 0 then
      forall Bx ticked,
        TC.m_rx_m I (Some (TI.TFrame a bytes)) (recv_w2 Bw bytes) (Z.of_nat (length bytes)) = Some (Bx, ticked) ->
        poll_dn_in (Some (TI.TFrame a bytes)) Bx bytes
    else
      poll_rx_each I (Some (TI.TFrame a bytes)) (poll_dn_in (Some (TI.TFrame a bytes))) (recv_w2c Bw bytes a pf).

(* The bytes some path of the call stores outside its own frame and the block it allocates and frees (each path stores
   a subset): OW's and GOT's payloads (the memsets, OW.desk_off), M.fail, g_rx_send, g_rx_len, g_rx, g_rx_times,
   g_rx_fail; m_rx's (m_rx_cg.v mrx_wr), diginet_session_rx's at the input bytes (diginet_session_rx_cg.v srx_wr) and
   diginet_session_poll's (diginet_session_poll_cg.v poll_wr); settle stores none. Every disjunct is a byte of G. *)
Definition recv_wr (bytes : list byte) (a : Z) : Prop :=
  twa_fld TW.OFF_OW TA_OW TW.OFF_OW TW.SZ_OW a \/
  twa_fld TW.OFF_GOT TA_GOT TW.OFF_GOT TW.SZ_GOT a \/
  twa_fld TW.OFF_M TA_M TW.A_M_fail 4 a \/
  twa_fld TW.OFF_g_rx_send TA_g_rx_send TW.OFF_g_rx_send TW.SZ_g_rx_send a \/
  twa_fld TW.OFF_g_rx_len TA_g_rx_len TW.OFF_g_rx_len TW.SZ_g_rx_len a \/
  twa_fld TW.OFF_g_rx TA_g_rx TW.OFF_g_rx TW.SZ_g_rx a \/
  twa_fld TW.OFF_g_rx_times TA_g_rx_times TW.OFF_g_rx_times TW.SZ_g_rx_times a \/
  twa_fld TW.OFF_g_rx_fail TA_g_rx_fail TW.OFF_g_rx_fail TW.SZ_g_rx_fail a \/
  mrx_wr a \/
  srx_wr bytes a \/
  poll_wr a.

(* The shadow facts of the record (lib/A/AF0m.v Tfib_zero_shadow and Tfib_const_shadow rows) the two memsets need:
   OW's payload (304 bytes, 38 whole granules) and GOT's (224 bytes, 28 whole granules) have shadow 0, and the rest of
   their hulls' aligned groups of 8 shadow bytes is visible: for OW, g_rx_len's payload granule (0x5f3040, a zero
   shadow row) and its three guard granules (0xf9), and OW's first six guard granules after its payload (0xf9); for
   GOT, the last four guard granules of g_s (0xf9), which share GOT's first group. *)
Definition trans_recv_cells (B : asyms) : Prop :=
  decode_zshadow_at B TA_OW (TA_OW + TW.SZ_OW) /\
  decode_zshadow_at B TA_GOT (TA_GOT + TW.SZ_GOT) /\
  decode_zshadow_at B TA_g_rx_len (TA_g_rx_len + TW.SZ_g_rx_len) /\
  forall ly,
    In (z1 (ANum (ACells.shadow_addr (TA_g_rx_len + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_g_rx_len + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_g_rx_len + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_OW + TW.SZ_OW))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_OW + TW.SZ_OW + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_OW + TW.SZ_OW + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_OW + TW.SZ_OW + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_OW + TW.SZ_OW + 32))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_OW + TW.SZ_OW + 40))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_GOT - 32))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_GOT - 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_GOT - 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_GOT - 8))) 0xf9) (as_const B ly).
Lemma trans_recv_cells_rows :
  map ACells.shadow_addr [TA_g_rx_len; TA_g_rx_len + 8; TA_g_rx_len + 24; TA_OW; TA_OW + TW.SZ_OW;
                          TA_OW + TW.SZ_OW + 40; TA_GOT - 32; TA_GOT - 8; TA_GOT] =
  [0x800b6608; 0x800b6609; 0x800b660b; 0x800b660c; 0x800b6632; 0x800b6637; 0x800b4a58; 0x800b4a5b; 0x800b4a5c].
Proof. reflexivity. Qed.

(* The traces its two allocator calls record, which the call rules ask to be in the trace universe (YC5d.v
   amalloc04_rule, afree04_rule): the malloc at 0x83814 runs before receive writes s0, so the frame-pointer chain is
   the entry's and the trace is its return address 0x83818 followed by the tail of the entry context
   c = raZ regs :: spine ch; the tail jump to free at 0x83a70 runs with the entry's ra, s0 and sp restored, so the
   trace is c itself (fuzz_decode's check_round_trip_cg.v dec_crt_uctx). *)
Definition trans_recv_uctx (B : asyms) (CTX : list (list Z)) : Prop :=
  forall c, In c CTX ->
    In (decode_utrace (pc_malloc_ra0 (as_code B)) (RECV_RA_MALLOC :: tl c)) (as_universe B) /\
    In (decode_utrace (pc_free_ra0 (as_code B)) c) (as_universe B).

Section recv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The meter cost of one call: the malloc of max (n, 1) bytes and the free. *)
Definition recv_cost (n : Z) : Z := mo_malloc MT (Z.max 1 n) + mo_free MT.

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with at most two events, the written range
   recv_wr bytes, the meter charged at most recv_cost n, and X: for the address a the malloc returned, the model's
   world Bw' of receive_m at a, the world relation at it and g_fail_next Bw' <= 1. transport_cg_post states the
   caller's blocks up to permutation (the block is freed) and frames S2 = frames Sc. *)
Definition transport_recv_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw bytes : list byte) (by_poll pf : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    RECV_STK RECV_EV (recv_cost (Z.of_nat (length bytes))) (recv_wr bytes)
    (fun regs2 W2 mem2 =>
       exists (a : Z) (Bw' : list byte),
         recv_addr_ok a /\ TOP.receive_m timg_A Bw a bytes by_poll pf = Some (Bw', tt) /\
         tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a0, for call contexts CTX (the entry's return address followed by the
   frame-pointer chain's), in the G-form caller-journal form. *)
Definition transport_receive_cg (a0 : Z) (CTX : list (list Z)) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p by_poll pf T : Z) (bytes : list byte) (Bw : list byte) ch,
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 p -> YK11.getr regs 11 = w64 (Z.of_nat (length bytes)) ->
    YK11.getr regs 12 = w64 by_poll -> bv_unsigned (YK11.getr regs 13) mod 2 ^ 32 = pf ->
    @achain rc lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RECV_STK -> spZ regs <= sp0 ->
    - 2 ^ 31 <= by_poll < 2 ^ 31 -> 0 <= pf < 2 ^ 32 -> Z.of_nat (length bytes) <= 65535 ->
    garr8 segs (mrestrict (w_H W) memc) p (TW.zs bytes) ->
    ((0 < length bytes)%nat ->
       trans_src_ok B lyc Sc W memc p (Z.of_nat (length bytes)) /\
       decode_off_win regs RECV_STK p (Z.of_nat (length bytes))) ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    (forall a, recv_addr_ok a -> TOP.receive_m timg_A Bw a bytes by_poll pf <> None) ->
    trans_rom_view_rd W memc ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN) ->
    TW.S_queued Bw <= TC.QUEUE_MAX ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    TW.g_ncmd Bw <= TC.CMDS_MAX ->
    1 <= TW.S_cfg_max_cmds Bw -> 1 <= TW.S_cfg_max_body Bw ->
    recv_dn_each timg_A Bw bytes by_poll pf ->
    count_cid POLL_CID (frames Sc) + 1 < fs_frames POLL_CID ->
    count_cid SRX_CID (frames Sc) < fs_frames SRX_CID ->
    count_cid ONANN_CID (frames Sc) < fs_frames ONANN_CID ->
    count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID ->
    count_cid ONDATA_CID (frames Sc) + 2 < fs_frames ONDATA_CID ->
    st_nev S + k + RECV_EV <= EV_MAX -> blocks_bytes Sc + RECV_LIVE <= LIVE_MAX ->
    mo_ok MT Sc T -> recv_cost (Z.of_nat (length bytes)) <= T ->
    SRr segs W (@cfg_at fx segs a0 regs memc mdc)
      (transport_recv_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).

(* The statement the walk will prove: the call rules' code addresses (the listing's trampolines), the runtime cells,
   the shadow of OW, GOT and their memsets' hulls, the record facts that no byte of G and no TRANS_RO_RD byte is an
   owned static or errno, the allocator and meter laws, the trace facts, and the contracts of the malloc wrapper,
   __asan_memcpy, __asan_memset, diginet_session_poll, m_rx, diginet_session_rx, settle and the free wrapper (pc order
   of their first call: 0x83814, 0x83830, 0x83848, 0x83a08, 0x83a20, 0x83a40, 0x83a48, 0x83a70) give the contract at
   TS_receive for the contexts CTX. *)
Definition transport_receive_cg_holds_stmt (CTX : list (list Z)) : Prop :=
  pc_wrap_malloc (as_code B) = transport_sigma TS___interceptor_trampoline_malloc ->
  pc_wrap_free (as_code B) = transport_sigma TS___interceptor_trampoline_free ->
  transport_cells B -> trans_recv_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  trans_recv_uctx B CTX ->
  (forall fx' : YK11.FPState, @amalloc04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_session_poll_cg fx' rc B MT (transport_sigma TS_diginet_session_poll)) ->
  (forall fx' : YK11.FPState, @transport_m_rx_cg fx' rc B MT (transport_sigma TS_m_rx)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_session_rx_cg fx' rc B MT (transport_sigma TS_diginet_session_rx)) ->
  (forall fx' : YK11.FPState, @transport_settle_cg fx' rc B MT (transport_sigma TS_settle)) ->
  (forall fx' : YK11.FPState, @afree04_rule fx' rc tfib_sink_head segs B MT) ->
  transport_receive_cg (transport_sigma TS_receive) CTX.
End recv.
