(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module names changed; 358 of its 430 lines of code are new or changed and 371 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickCut.v, with its module paths and module names changed; 203 of its 254 lines of code are new or changed and 379 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_tick_cg.v, with its module names changed; 166 of its 229 lines of code are new or changed and 191 lines of the source are left out. *)
(* receive_cg: image B's ASan walk contract of receive (fuzz/fuzz_transport.c:995-1025, fuzz_dup, fuzz_alloc and
   op_begin inlined, spec_read_frame CALLED; model lib/TModel/TOps.v receive_m, with TCb.v op_begin_m, m_rx_m and
   settle_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x836a8 = transportb_sigma TB_receive, size 404, as
   STATEMENTS only (no proof). It allocates the heap block of the frame it receives (the malloc wrapper), copies the
   input bytes into it, stores into OW, GOT, M, g_rx_send, g_rx, g_rx_len, g_rx_times and g_rx_fail (harness
   globals), calls spec_read_frame (a G-form callee with one out cell: the struct spec_frame in receive's own machine
   frame), diginet_session_poll, m_rx and diginet_session_rx (G-form callees) and settle (a donor-form callee), and
   frees the block by a CALL of the free wrapper, so it is a G-form caller-journal walk that calls the allocator: the
   caller's journal is lib/A/W_journalG.v ajournal_gx (image-free) over G = lib/B/TransportGB.v G_HARNESS_B with no
   out cell (XO = 0, OUT = []), the post is lib/A/Prog/TransportGCg.v transport_cg_post (image-free; acall_kept_g over
   G_HARNESS_B) with two allocator events and the meter charged for one malloc and one free, and the statement is
   stated for call contexts CTX with the trace facts of its two allocator calls, in the allocator-calling form of
   fuzz_decode's image-B check_round_trip_cg.v (origin/ossv/recipes,
   projects/libreac/fuzz_decode/proofs/lib/B/Prog/check_round_trip_cg.v, 820554da266b: a malloc before s0 changes,
   whose trace follows the entry context, and a free called with s0 holding a heap block, whose trace is fixed). It
   takes no side-stack frame. Form: image A's lib/A/Prog/receive_cg.v at image B's names; the differences image B's
   code forces are listed at the end of this comment.
   receive is a direct call target: LLVMFuzzerTestOneInput and build_and_receive call it by jal at TB_receive (it is
   not reached through a pointer of the session, so it is stated at transportb_sigma TB_receive, not at a TImg.v
   field).

   The contract. a0 = p, a1 = n = the length of bytes (a size_t, n <= 65535: the plain contract's bound), a2 = by_poll
   (an int, sign-extended), a3 = poll_flags (its low 32 bits pf; the code reads bits 0 and 1). The n bytes at p are
   bytes (garr8), and when n is not 0 they are placed by trans_src_ok (a heap block of the caller, a caller's
   side-stack frame, G, a read-only range or the machine stack) outside this call's stack window. The memory relates
   to the world Bw by image B's world relation (TWorldG.v tw_at at TWorldB.v TMAP_B, read through aview), g_fail_next
   Bw <= 1, and receive_m timg_B Bw a bytes by_poll pf is not None for every address a the malloc can return
   (recv_addr_ok: the plain contract's h_addr_ok). The read-only bytes the callees read are the image's
   (trans_rom_view_rd). The function returns to ra with the callee-saved registers kept, at most two allocator events,
   the block it allocated freed (the caller's blocks exactly), the caller's side-stack frames exactly, the meter
   charged at most recv_cost n, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at or above alloc_ceiling outside
   the call's stack window [sp - RECV_STK, sp), the image bytes outside G, the owned statics and errno, the caller's
   block and frame bytes outside recv_wr bytes), and X: for the address a the malloc returned (recv_addr_ok a),
   receive_m timg_B Bw a bytes by_poll pf = Some (Bw', tt), the world relation at Bw' and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/U/Prog/T/receive_c.v receive_contract, an SR contract with the
   allocator state; its receive_contract_cf is the cut-free form of the same contract, which this statement does not
   restate): h_binds and the allocator's call_pre_k / call_post_k -> the G journal and
   transport_cg_post with the two allocator call rules (YC5d.v amalloc04_rule, afree04_rule) at the listing's
   trampolines and the trace facts trans_recv_uctx; receive_args: a0 = p, a1 = Z_to_bv 64 (length bytes), a2 =
   by_poll with -2 ^ 31 <= by_poll < 2 ^ 31, the low 32 bits of a3 = pf with 0 <= pf < 2 ^ 32, length bytes <= 65535
   kept; blk_data B mem p bytes -> garr8 of bytes at p; h_src (n = 0, or off_world and in a user block of A, or above
   the caller's sp) -> when 0 < n, trans_src_ok and decode_off_win at RECV_STK (the off_world part is not needed: the
   bytes at p are read once, by the memcpy at 0x836f8, before any store into G, and no callee is handed p); the model
   premise (forall a, h_addr_ok a -> receive_m timg_ubsan Bw a bytes by_poll pf <> None) verbatim at timg_B; wmem ->
   tw_at; g_fail_next Bw <= 1 kept (the code neither writes g_fail_next nor lets a callee write it out of range: the
   callees' statements ask it and give it back) and given back in X; relro_img -> trans_rom_view_rd; res_ok_slots /
   room_slots (the budget) -> st_nev S + k + RECV_EV <= EV_MAX, blocks_bytes Sc + RECV_LIVE <= LIVE_MAX and the meter
   premise mo_ok MT Sc T with recv_cost n <= T; the stack premises -> the journal's window premises; frm_zero of the
   entry's float state is not needed (transport_cg_post returns at the same float state, and no callee changes it).
   The post's receive_ret: the address a with h_addr_ok a and receive_m ... = Some (Bw', tt) -> X; the footprint (the
   world, the freed frame and the allocator's ctx) -> transport_cg_post's acall_kept_g over recv_wr bytes (the freed
   block is not a block of the caller, and the allocator's ctx is the allocator's: the journal keeps the caller's view
   outside them); wmem -> X's tw_at; blocks L' A' = blocks L A -> Permutation of ablocks.
   Premises the plain contract does not have:
   - the call context: the frame-pointer chain ch at entry (YCbq.v achain at sp and s0) and raZ regs :: spine ch in
     CTX. receive does not change s0 before its malloc call (0x836dc; s0 is first written at 0x836e4), so the
     malloc's trace is its return address 0x836e0 followed by the tail of the entry context; it calls free (0x8380c)
     with s0 = the heap block, below sp, so the free's chain is empty and its trace is [0x83810] whatever the context
     (trans_recv_uctx).
   - the five frame counts, diginet_session_poll_cg.v's (its count premises at the call state, where the frames are
     frames Sc: receive takes no side-stack frame); diginet_session_rx, called directly on the by_poll = 0 path, asks
     the class-5 count without the + 1 and the other four the same.
   - the four run invariants on its own Bw: (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME, (2)
     TW.S_queue_len Bw i <= DIGINET_CMD_MAX_LEN for i < TW.S_queued Bw, (4) every PENDING command g_cmd[s], s < g_ncmd
     Bw, has Cmd_len <= SPEC_CMD_MAX, (5) 1 <= TW.S_cfg_max_cmds Bw and 1 <= TW.S_cfg_max_body Bw. diginet_session_poll
     and diginet_session_rx ask all four at their call world, settle asks (2) at its call world, m_rx and
     spec_read_frame ask none. Before those calls receive stores OW and GOT (the memsets), M.fail, OW.desk_off,
     g_rx_send and on the by-poll path g_rx, g_rx_len, g_rx_times and g_rx_fail, none of which an invariant reads below
     the index bounds (M.fail is M + 88, M.fly starts at M + 96; the invariants read M.fly, g_s, g_cmd[0 .. CMDS_MAX)
     and g_ncmd); spec_read_frame stores no byte of G; m_rx_m stores M and OW only and sets M.fly.on to 0 only. For
     diginet_session_poll_m and diginet_session_rx_m (settle's world after either) the walk proves the model facts that
     they keep them: no X states them and no lemma of lib/TModel states them yet (the only writer of M.fly is io_send,
     whose stored length is the frame's; io_send's check_latest_sent only takes commands out of the PENDING set; no
     callee writes g_s.cfg; take, inside diginet_session_tick, removes queue entries and keeps the rest:
     lib/TSim/TickTakeW.v te_sq, sq Bf = unpick m (sq B), with lib/TSim/TakeOk.v Forall_pick). The walk reads the
     model's world at each call for the fields each invariant names.
   - with (2) and (4), their index bounds TW.S_queued Bw <= TC.QUEUE_MAX and TW.g_ncmd Bw <= TC.CMDS_MAX, which
     diginet_session_poll and diginet_session_rx ask beside them (diginet_session_tick_cg.v says why): past those
     bounds g_s.queue[i] and g_cmd[s] are other world bytes, among them OW and GOT (the memsets), the harness
     globals receive stores (g_rx_send, g_rx, g_rx_len, g_rx_times, g_rx_fail) and the callees' stores, so (2) and
     (4) are carried to each call, settle's included, only below them. receive's own code reads no index of
     g_s.queue or g_cmd (its loads are g_fail_next, the struct's send field and g_now); take, check_latest_sent and
     settle's check_latest_queue read them (diginet_session_tick_cg.v, settle_cg.v). No store of receive and no
     function it calls writes g_ncmd, and take only lowers queued, so both bounds hold at each call; the caller has
     them from the plain run (lib/TSim/Agree.v d3_ncmd and d3_ops, OPS_MAX = CMDS_MAX; lib/TSim/Deadline.v
     queued_le).
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
     them, with these facts for a range of G or of TRANS_RO_RD; their placement by DgnTransportBCg.v
     trans_src_ok_inner, the malloc adding a block and keeping the frames, and their decode_rd_ok: for a heap block
     the placement alone, for a range of a side-stack frame the bytes and shadow bytes the malloc's acall_kept keeps,
     for a range of G, of TRANS_RO_RD or of the machine stack the shadow facts at the new AR state (trans_sh_any,
     stack_zshadow_ra), as DgnTransportBCg.v trans_src_ok_kept's proof takes them; the TRANS_RO_RD bytes and G across
     the malloc, the memcpy, the memsets and each callee: trans_ro_rd_scoped, gx_kept_of_acall_kept with
     G_HARNESS_gx_ok and G_HARNESS_gx_noerrno), and the allocator and meter laws.
   The frame's placement: the heap block of max (n, 1) bytes the malloc returns (amalloc04_rule: 4096 <= a, the block
   (a, max (n, 1)) added to ablocks; AR_laws' al_blocks: a + max (n, 1) <= alloc_ceiling, so recv_addr_ok a) holds the
   n copied bytes; it is TF = Some (TFrame a bytes) for every callee: trans_tframe_at by decode_in_block,
   trans_tf_off_g and each callee's *_apart because a heap block is outside the image (AR_laws' al_client_img) and
   every callee's written range lies in G (spec_read_frame's, srf_wr sp, in receive's own frame), and
   diginet_session_poll's iorecv_rx_in because g_rx = a (TCb.v frame_from_base).

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 404 code bytes are equal in both files), 101
   words:
     0x836a8 - 0x836c0 sp = sp - 128; ra at sp + 120, s0 .. s4 at sp + 112 .. sp + 80, loaded back at 0x83810 -
                      0x83824 (sp = sp + 128 at 0x83828, return at 0x8382c). No side-stack frame, no frame pointer. Own
                      frame cells: sp + 0 .. sp + 80 (the struct spec_frame fr, 80 bytes, written by spec_read_frame).
     0x836c4 - 0x836d0 s2 = poll_flags (a3), s3 = by_poll (a2), s1 = n (a1), s4 = p (a0).
     0x836d4 - 0x836dc a0 = n + (n = 0 ? 1 : 0) = max (n, 1) (fuzz_alloc's n ? n : 1); the call of the malloc wrapper
                      (0x53740 = transportb_sigma TB___interceptor_trampoline_malloc = pc_wrap_malloc) at 0x836dc,
                      return address 0x836e0 = RECV_RA_MALLOC; s0 (the caller's) is not yet written.
     0x836e0          a0 = 0 goes to 0x83830 (the trap: the call of __asan_handle_no_return (0x5a500 = transportb_sigma
                      TB___asan_handle_no_return) at 0x83830, then abort (0x93390 = transportb_sigma TB_abort) at
                      0x83834; fuzz.h:86); amalloc04_rule returns 4096 <= a, so not taken. 0x836e4 s0 = a = frame.
     0x836e8 - 0x836f8 n = 0 goes to 0x836fc (no copy, fuzz_dup); a0 = frame, a1 = p, a2 = n; the call of __asan_memcpy
                      (checked_memcpy, 0x523ec = transportb_sigma TB___asan_memcpy) at 0x836f8, return address 0x836fc.
     0x836fc - 0x83710 s4 = &OW = 0x5f2ce0 (TB_OW); a0 = OW, a1 = 0, a2 = 0x130 = 304; the call of __asan_memset
                      (checked_memset, 0x52888 = transportb_sigma TB___asan_memset) at 0x83710, return address 0x83714
                      (op_begin :390).
     0x83714 - 0x83724 a0 = &GOT = 0x5e4f60 (TB_GOT), a1 = 0, a2 = 0xe0 = 224; the call of __asan_memset at 0x83724,
                      return address 0x83728 (:391).
     0x83728 - 0x8373c a0 = the 1-byte load of g_fail_next (0x5deda0); the 4-byte store of -1 at OW + 232 (OW.desk_off,
                      :392, 0x83734) and of a0 at M + 88 = 0x5dee38 (M.fail, :393, 0x8373c). These and every later
                      access at a constant address of a global carry no instrumented check, and receive's own code makes
                      no instrumented access at all: the frame's bytes are read by spec_read_frame.
     the frame's code and send (spec_read_frame, :1002-1003), 0x83740 - 0x83758:
     0x83740 - 0x8374c a2 = sp (the struct fr), a0 = frame, a1 = n; the call of spec_read_frame (0x839c0 =
                      transportb_sigma TB_spec_read_frame) at 0x8374c, return address 0x83750.
     0x83750 - 0x83758 a0 = the 4-byte load at sp + 32 (fr.send: its X's TContract.sf_bytes frame f, f = DgnSpec
                      spec_read_frame (zs bytes) n, whose send field is fr_send bytes when the code is SPEC_OK and 0
                      else, the model's recv_send bytes); the 4-byte store of a0 at g_rx_send (0x5e5060 =
                      TB_g_rx_send).
     0x8375c          by_poll = 0 (the 64-bit register: by_poll sign-extended) goes to 0x837d4.
     the by-poll path (:1005-1018), 0x83760 - 0x837d0:
     0x83760 - 0x83768 s1 = got = n when n < 1514 (unsigned), else 1514 (:1005).
     0x8376c - 0x83778 a2 = sp, a0 = frame, a1 = got; the call of spec_read_frame at 0x83778, return address 0x8377c
                      (:1007-1008; its X at len = got: the send field is recv_send (firstn got bytes)).
     0x8377c - 0x837b4 a0 = bit 1 of poll_flags; a1 = (poll_flags & 1) + 1; a2 = fr.send (the 4-byte load at sp + 32);
                      s2 = a0 xor 1 (ticked, :1011); the 8-byte store of got at g_rx_len (0x5f2cc0, at 0x8378c), the
                      4-byte store of a1 at g_rx_times (0x5f2ca0, at 0x8379c), the 8-byte store of frame at g_rx
                      (0x5df620, at 0x837a8), the 4-byte stores of a2 at g_rx_send (at 0x837b0) and of a0 at g_rx_fail
                      (0x5f2c80, at 0x837b4) (:1012-1015; five distinct fields, so their order, which is not the
                      model's recv_w2c order, does not matter).
     0x837b8 - 0x837c4 a0 = &g_s = 0x5df640, a1 = 0; the call of diginet_session_poll (0x8aa98 = transportb_sigma
                      TB_diginet_session_poll) at 0x837c4, return address 0x837c8 (:1016).
     0x837c8 - 0x837d0 the 8-byte store of 0 at g_rx and the 4-byte store of 0 at g_rx_fail (:1017-1018); to 0x83800.
     the m_rx path (:1020-1021), 0x837d4 - 0x837fc:
     0x837d4 - 0x837dc a0 = frame, a1 = n; the call of m_rx (0x84c1c = transportb_sigma TB_m_rx) at 0x837dc, return
                      address 0x837e0; s2 = its result (ticked, 0x837e8).
     0x837e0 - 0x837fc a3 = the 8-byte load of g_now (0x5ded80); a0 = &g_s, a1 = frame, a2 = n; the call of
                      diginet_session_rx (0x87784 = transportb_sigma TB_diginet_session_rx) at 0x837fc, return address
                      0x83800 (its result is not used).
     0x83800 - 0x83804 a0 = s2 (ticked, 0 or 1); the call of settle (0x838c0 = transportb_sigma TB_settle) at 0x83804,
                      return address 0x83808 (:1023).
     0x83808 - 0x8380c a0 = frame; the call of the free wrapper (0x5373c = transportb_sigma
                      TB___interceptor_trampoline_free = pc_wrap_free) at 0x8380c from sp - 128 with s0 = frame, return
                      address 0x83810 = RECV_RA_FREE (:1024).
     0x83810 - 0x8382c ra and s0 .. s4 loaded back, sp = sp + 128, return. a0 .. a7 at the return are not stated
                      (receive returns void).
     0x83838          the word 0xc0001073 (unimp), after the call of abort, which does not return: not reached.
   The model and the code (recv_model): every test is receive_m's, read through spec_read_frame's X (the struct's send
   field), tw_at and the registers: the malloc result 0 (fuzz_alloc_m's None), by_poll =? 0; the code tests no byte of
   the frame itself (spec_read_frame's code tests fr_code of bytes, and of firstn got bytes on the by-poll path, and
   its X gives the send value the model's recv_send names); the stores are op_begin_m's (two memsets of 0,
   set_OW_desk_off -1, set_M_fail (g_fail_next)), set_g_rx_send, and on the by-poll path set_g_rx_len,
   set_g_rx_times, set_g_rx, set_g_rx_send, set_g_rx_fail (recv_w2c), then set_g_rx 0 and set_g_rx_fail 0; the calls
   are diginet_session_poll_m at recv_w2c with max_wait_ms 0, or m_rx_m at recv_w2 with n and diginet_session_rx_m at
   its world with bytes and g_now of that world; then settle_m with ticked. The code has no trap of its own besides
   the malloc's NULL test; the model's None cases are fuzz_alloc_m's (a = 0) and the callees', all ruled out by the
   model premise (at the address the malloc returned, recv_addr_ok).
   Trap (the call of __asan_handle_no_return at 0x83830, then abort at 0x83834) and the fact that rules it out:
   amalloc04_rule's 4096 <= a. Error paths: none (no instrumented access of its own; receive calls no report
   function).
     The memcpy's own checks (aintrin_realizes' pre, through TransportGCg.v gx_intrin_at): the destination
     [frame, frame + n) is a block allocated since the journal's start (awr_byte), present and marked usable; the source
     [p, p + n) from trans_src_ok at the call state (across the malloc: its placement by trans_src_ok_inner, the malloc
     adding a block and keeping the frames, its bytes by the malloc's acall_kept and its decode_rd_ok as in the holds
     paragraph above; then trans_src_ok_rd: decode_rd_ok) and decode_off_win at RECV_STK; the two are apart (a heap
     block of the caller is another block, a side-stack frame is apart from every block (AR_laws' sep law), G and the
     read-only ranges are image bytes, the machine stack lies at or above alloc_ceiling); n < 2 ^ 32 (n <= 65535).
     The memsets' own checks: the destinations OW (304 bytes) and GOT (224 bytes) are bytes of G (writable through the
     G journal by lib/B/Prog/TransportGRwB.v G_HARNESS_B_rw, not owned by trans_g_unowned), their shadow is 0
     (trans_recv_cells) and their hulls' shadow bytes are visible: OW's hull is the shadow of [0x5f2cc0, 0x5f2e40)
     (g_rx_len's payload granule and three guard granules, OW's payload, six of OW's guard granules), GOT's the shadow
     of [0x5e4f40, 0x5e5040) (four guard granules of g_s, GOT's payload) (trans_recv_cells).
   Writes: its own machine frame (ra, s0 .. s4 at sp + 80 .. sp + 127 after sp = sp - 128, and the struct fr at
   sp + 0 .. sp + 79, which spec_read_frame writes); the block it allocates (the copy; freed before the return); OW's
   and GOT's payloads, M.fail, g_rx_send, and on the by-poll path g_rx_len, g_rx, g_rx_times and g_rx_fail (bytes of
   G); m_rx's (m_rx_cg.v mrx_wr), diginet_session_rx's (srx_wr bytes) and diginet_session_poll's
   (diginet_session_poll_cg.v poll_wr) stores; spec_read_frame stores nothing outside the struct and settle nothing
   outside its frame; the allocator's own bytes are the runtime's (owned statics, the journal). No byte of a caller's
   frame or block is written, so recv_wr bytes, the bytes of G it and its callees store, is the written range.
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     the malloc wrapper as YC5d.v amalloc04_rule (with pc_wrap_malloc (as_code B) = transportb_sigma
       TB___interceptor_trampoline_malloc), call at 0x836dc, read inside the G journal (TransportGCg.v gx_open, the
       rule at the donor journal, gx_pack0; the rule's acall_kept keeps every byte of G: gx_kept_of_acall_kept): a0 =
       max (n, 1) < MALLOC_MAX; blocks_bytes Sc + max (n, 1) <= LIVE_MAX (the premise with RECV_LIVE); sp = entry sp -
       128, so ASTACK - o <= STK by the window premise (RECV_STK = 128 + ASTACK); gp, tp, ra = 0x836e0 (ret_ok);
       st_nev Sc < EV_MAX; chain_pre at that sp with the entry s0 and the entry chain ch (the 48 bytes the prologue
       stores lie below the entry sp, the chain's records above it: YCbq.v achain); the trace decode_utrace
       (pc_malloc_ra0) (0x836e0 :: tl c) of trans_recv_uctx; mo_ok MT Sc (mo_malloc MT (max (n, 1))) from the meter
       premise. Its post: the journal at k + 1, the block (a, max (n, 1)) added, 4096 <= a, frames kept, acall_kept
       outside its ASTACK window and the block, mo_le Sc S1 (mo_malloc MT (max (n, 1))).
     __asan_memcpy as aintrin_realizes ... OCpy (transportb_sigma TB___asan_memcpy), call at 0x836f8 (above).
     __asan_memset as aintrin_realizes ... OSet (transportb_sigma TB___asan_memset), calls at 0x83710 and 0x83724
       (above).
     spec_read_frame as spec_read_frame_cg.v transport_spec_read_frame_cg at transportb_sigma TB_spec_read_frame
       (calls at 0x8374c and 0x83778; G form, the same journal; its post, TransportGCg.v transport_cg_post_out
       [(sp, 80)], used as written, as m_rx_cg.v uses it): b = a (0 < a), len = n at 0x8374c and got = min (n, 1514)
       at 0x83778 (0 <= len <= length bytes); garr8 of TW.zs bytes at a (the memcpy's post, kept by the memsets and
       the stores, which write G, and at the second call by the first call's acall_kept_g outside srf_wr sp);
       trans_src_ok and decode_off_win (SRF_STK <= RECV_STK - 128) of [a, a + len) (decode_in_block in
       (a, max (n, 1)); the block lies below alloc_ceiling); [a, a + len) apart from srf_wr sp (a heap block and the
       machine stack); fp = sp: fp mod 8 = 0 (sp mod 16 = 0 and 128 mod 16 = 0), transport_twr_ok_g (the struct's
       bytes lie in receive's own frame, above the call's window, present by the journal), decode_rd_ok
       (lib/B/Prog/CanKit.v can_stack_addressable / can_stack_hull; amem_range: a stack range), decode_off_win (the
       struct lies at and above the call's sp), not in G (the stack lies above G); st_nev S + (k + 1) + SRF_EV <=
       EV_MAX. Its X: a0 = sf_code f (not used), the 80 bytes at sp = TContract.sf_bytes a f with f = srf_f bytes len,
       whose send field the code loads, and gx_kept (G as it was, so the world relation holds after it).
     diginet_session_poll as diginet_session_poll_cg.v transport_diginet_session_poll_cg at transportb_sigma
       TB_diginet_session_poll (call at 0x837c4; a G-form callee in the same G journal): the journal at the call
       state; ra = 0x837c8; gp, tp kept; a0 = POLL_S, a1 = w = 0; sp - 128 16-aligned, sp0 - STK <= sp - 128 -
       POLL_STK (RECV_STK = 128 + ASTACK >= 128 + POLL_STK), sp - 128 <= sp0; tw_at at recv_w2c Bw bytes a pf (the
       tw_fills of the memsets and the tw_writes of the stores; spec_read_frame keeps G) and g_fail_next of it <= 1
       (no store writes g_fail_next); diginet_session_poll_m timg_B F (recv_w2c ...) 0 = Some (B2d, _) (the model
       premise through recv_model); trans_tframe_at F at POLL_STK (0 < a; garr8 of bytes at a: the memcpy's post, kept
       by the memsets, the stores, which write G, and spec_read_frame, which writes the struct; decode_in_block of
       [a, a + n) in (a, max (n, 1)); decode_off_win: the block lies below alloc_ceiling); trans_tf_off_g F and
       poll_apart F (the block is outside the image); trans_rom_view_rd at the call memory (the malloc's acall_kept,
       the memcpy, the memsets, the stores and spec_read_frame's acall_kept_g keep every TRANS_RO_RD byte:
       trans_ro_rd_scoped); iorecv_rx_in F (recv_w2c ...): g_rx of it is a, and TCb.v frame_from_base; the four run
       invariants and the two index bounds at recv_w2c (above); poll_rx_each F (poll_dn_in F) (recv_w2c ...) from
       recv_dn_each; the five counts (the premises: the frames are frames Sc); st_nev S + (k + 1) + POLL_EV <= EV_MAX.
       Its X: tw_at at B2d,
       g_fail_next B2d <= 1; the two stores after it give tw_at at set_g_rx_fail (set_g_rx B2d 0) 0.
     m_rx as m_rx_cg.v transport_m_rx_cg at transportb_sigma TB_m_rx (call at 0x837dc; G-form, the same journal): a0 =
       tf_addr fr = a, a1 = n; ra = 0x837e0; sp - 128, MRX_STK <= ASTACK; trans_tframe_at (Some fr) at MRX_STK (as for
       diginet_session_poll); a + n < 2 ^ 64 (a + max (n, 1) <= alloc_ceiling); mrx_apart fr (mrx_wr lies in G, the
       block outside the image); trans_rom_view_rd; tw_at at recv_w2 Bw bytes; m_rx_m timg_B (Some fr) (recv_w2 ...) n =
       Some (Bx, ticked) (the model premise); MRX_EV = 0. Its X: a0 = ticked, tw_at at Bx.
     diginet_session_rx as diginet_session_rx_cg.v transport_diginet_session_rx_cg at transportb_sigma
       TB_diginet_session_rx (call at 0x837fc; G-form, the same journal): ra = 0x83800; a0 = SRX_S, a1 = buf = a, a2 =
       n, a3 = g_now Bx (the 8-byte load at 0x837e4, tw_read; 0 <= g_now < 2 ^ 64); sp - 128, SRX_STK <= ASTACK; 0 < a;
       garr8 of bytes at a (kept across m_rx: the block lies outside mrx_wr); trans_src_ok and decode_off_win of
       [a, a + n) (decode_in_block); srx_buf_off_g (the block is outside the image); tw_at at Bx and g_fail_next Bx <= 1
       (m_rx_m stores M and OW only); diginet_session_rx_m timg_B (Some fr) Bx bytes (g_now Bx) = Some (By, _) (the
       model premise); trans_tframe_at (Some fr) at SRX_STK; trans_tf_off_g (Some fr); trans_rom_view_rd; srx_apart
       (Some fr) bytes (srx_wr lies in G); the four run invariants and the two index bounds at Bx (above); the
       guarded (3) at Bx and bytes: from recv_dn_each's poll_dn_in, the range lies in the block (decode_in_block of a
       sub-range, or of the empty range at a point of [a, a + n]), off this call's window; count_cid 5 (frames Sc) <
       fs_frames 5 (from + 1), count_cid 1 (frames Sc) + 1 < fs_frames 1 and the class-3, 0 and 2 counts; SRX_EV = 0.
       Its X: tw_at at By, g_fail_next By <= 1.
     settle as settle_cg.v transport_settle_cg at transportb_sigma TB_settle (call at 0x83804; donor form, lifted with
       TransportGCg.v gx_call_cg: settle stores nothing outside its frame, so the world relation after it is the one it
       was handed): a0 = ticked (0 or 1); ra = 0x83808; sp - 128, SETTLE_STK <= ASTACK; tw_at at B3 (the by-poll
       path's world after the two stores at 0x837c8 - 0x837cc, or By); settle_m B3 ticked = Some (B4, tt) (the model
       premise); (2) at B3; SETTLE_EV = 0. Its X: B4 = B3.
     the free wrapper as YC5d.v afree04_rule (with pc_wrap_free (as_code B) = transportb_sigma
       TB___interceptor_trampoline_free), the call at 0x8380c: a0 = a with (a, max (n, 1)) in the blocks of that state
       (added by the malloc, kept by every callee's Permutation of ablocks); sp = the entry sp - 128 (o = spZ regs -
       128 - sp0, ASTACK - o <= STK by the window premise); gp, tp, ra = 0x83810 (ret_ok); st_nev < EV_MAX (k + 1 +
       0 < k + 2); chain_pre at that sp with s0 = a and ch = [] (a + max (n, 1) <= alloc_ceiling, below that sp, so
       YG00.v bad_next holds); the trace decode_utrace (pc_free_ra0) [0x83810] of trans_recv_uctx; the footprint
       premise (a block of the journal's start state is in FP): the block (a, max (n, 1)) is not live at the call state
       Sc (the malloc returned a block apart from every live one), so if it is a block of the start state it is one the
       journal no longer holds, which YCbq.v ajournal's clause for a start block not in the current blocks puts in FP;
       mo_ok MT S (mo_free MT) at that state from the meter premise (mo_ok MT Sc T, recv_cost n <= T) by
       ameter_laws' mo_ok_step over the malloc's mo_le (mo_malloc MT (max (n, 1))) and each callee's mo_le ... 0
       (spec_read_frame's, diginet_session_poll's, m_rx's, diginet_session_rx's and settle's posts). Its post: the
       journal at k + 2, the block removed (so the caller's blocks up to permutation), frames kept, acall_kept outside
       the free's window [entry sp - 128 - ASTACK, entry sp - 128) (the call runs from receive's frame sp = entry
       sp - 128) and the block, which keeps the six saved registers for the epilogue: they lie at entry sp - 48 ..
       entry sp - 1 = frame sp + 80 .. frame sp + 127, above the free's window.
   Each callee's own record facts are premises of its holds statement.
   Stack: 128 bytes of its own; below sp - 128 the largest window is the malloc's and the free's ASTACK
   (spec_read_frame's SRF_STK, diginet_session_poll's POLL_STK, m_rx's MRX_STK, diginet_session_rx's SRX_STK,
   settle's SETTLE_STK and the intrinsics' ESTACK are smaller): RECV_STK = 128 + ASTACK (recv_stk_eq).

   The differences from image A's form (lib/A/Prog/receive_cg.v), each forced by image B's code: (1) spec_read_frame
   is called, not inlined: image A's receive reads frame + 12 .. frame + 21 itself under 16 instrumented checks (16
   report calls), image B's hands spec_read_frame the struct spec_frame at its sp (80 bytes of its own machine frame,
   RECV_SF) at 0x8374c (len n) and 0x83778 (len got) and loads only the struct's send field; so the holds statement
   takes spec_read_frame_cg.v's contract, receive's own code makes no instrumented access, the frame is 128 bytes
   (image A: 64) and RECV_STK counts SRF_STK. (2) The free is a call with link at 0x8380c from sp - 128 with s0
   holding the block (image A: a tail jump from the entry sp with the entry's s0 and ra), so its trace is the fixed
   decode_utrace (pc_free_ra0) [RECV_RA_FREE] (image A: the entry context c), the second conjunct of
   trans_recv_uctx, and RECV_STK = 128 + ASTACK covers both allocator calls from sp - 128 (image A: Z.max ASTACK
   (64 + ...), its free running from the entry sp); RECV_RA_MALLOC is 0x836e0. (3) The count premises are image B's
   diginet_session_poll_cg.v's: count_cid 1 (frames Sc) + 1 < fs_frames 1 and the on_announce count of class 3
   (image A: count_cid 1 (frames Sc) < fs_frames 1 and class 4), what image B's diginet_session_poll and
   diginet_session_rx ask at their call states (receive holds no frame); the class-5, class-0 and class-2 premises
   are image A's. (4) The addresses; trans_recv_cells names image B's rows, which lie as image A's do relative to OW,
   GOT, g_rx_len and g_s; each field of G is named by lib/B/Prog/m_set_cg.v twb_fld (image A's m_lost_cg.v twa_fld).
   The by-poll path's five stores come in another order (g_rx_len, g_rx_times, g_rx, g_rx_send, g_rx_fail; image A:
   g_rx_send, g_rx_len, g_rx, g_rx_times, g_rx_fail), on five distinct fields, which changes no premise. The model
   premise, the run invariants, recv_dn_each, recv_wr and the post are image A's at timg_B and TMAP_B.

   The callers (each with the return address after its jal): LLVMFuzzerTestOneInput at 0x81ea0 (return 0x81ea4): a0
   = s8, a record of the input (in the input's block), a1 = its length, a2 = 0 (0x81e98) or 1 (0x81cf4, the by-poll
   operation, which joins the call by the jump at 0x81cfc), a3 = 0 (0x81e9c) or, on the by-poll operation, the input
   byte loaded at 0x81bcc (0 when the input is used up, 0x81cc8); build_and_receive at 0x85d08 (return 0x85d0c): a0 =
   s9, the frame it built in its class-5 side-stack frame, a1 = its length (s5 + 30, 0x85cf8), a2 = 0, a3 = 0. Each
   supplies its G journal, the chain and its context in CTX, the placement of p, tw_at, g_fail_next, the model
   premise, trans_rom_view_rd, the four run invariants with the two index bounds, recv_dn_each, the five frame
   counts, and the allocator budget.
   The counts are of the caller's frames at the call: LLVMFuzzerTestOneInput holds a class-2 side-stack frame of its
   own (__asan_stack_malloc_2 at 0x81310), so its class-2 count must leave room for it as well; build_and_receive
   holds a class-5 frame of its own (__asan_stack_malloc_5 at 0x85a20), so its class-5 count must leave room for it
   (the + 1 of the class-5 premise is for diginet_session_poll's frame, which only the by-poll path takes;
   build_and_receive passes by_poll = 0). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import spec_read_frame_cg settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
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
Lemma receive_at : transportb_sigma TB_receive = 0x836a8.
Proof. reflexivity. Qed.

(* receive's frame (`sp = sp - 128` at its entry; no realignment). Every call runs from sp - 128: the malloc and free
   wrappers (ASTACK, amalloc04_rule, afree04_rule), __asan_memcpy and __asan_memset (ESTACK), spec_read_frame
   (SRF_STK), diginet_session_poll (POLL_STK), m_rx (MRX_STK), diginet_session_rx (SRX_STK) and settle (SETTLE_STK).
   The allocator's is the largest. *)
Definition RECV_FRAME : Z := 128.
Definition RECV_STK : Z :=
  RECV_FRAME + Z.max (Z.max ASTACK ESTACK) (Z.max SRF_STK (Z.max POLL_STK (Z.max MRX_STK (Z.max SRX_STK SETTLE_STK)))).
Lemma recv_stk_eq : RECV_STK = RECV_FRAME + ASTACK.
Proof. reflexivity. Qed.
(* Two allocator events: the malloc and the free. The callees record none. *)
Definition RECV_EV : Z := 2.
Lemma recv_ev_callees : SRF_EV = 0 /\ POLL_EV = 0 /\ MRX_EV = 0 /\ SRX_EV = 0 /\ SETTLE_EV = 0.
Proof. repeat split; reflexivity. Qed.
(* The live bytes it adds: one block of max (n, 1) <= 65535 bytes (n <= 65535). *)
Definition RECV_LIVE : Z := 65535.
(* The return addresses of its malloc call (the jal at 0x836dc, 0x34 bytes after the entry) and of its free call (the
   jal at 0x8380c, 0x164 bytes after the entry). *)
Definition RECV_RA_MALLOC : Z := transportb_sigma TB_receive + 0x38.
Definition RECV_RA_FREE : Z := transportb_sigma TB_receive + 0x168.
Lemma recv_ra_at : RECV_RA_MALLOC = 0x836e0 /\ RECV_RA_FREE = 0x83810.
Proof. split; reflexivity. Qed.
(* The struct spec_frame fr it hands spec_read_frame: the 80 bytes at offset 0 of its own machine frame (`mv a2, sp`
   at 0x83740 and 0x8376c), below the six saved registers at sp + 80 .. sp + 127; the code reads its send field, the
   4 bytes at offset 32 (0x83750, 0x83784). *)
Definition RECV_SF : Z := 0.
Lemma recv_sf_fits : RECV_SF + SRF_SIZE = 80 /\ 80 + 48 = RECV_FRAME.
Proof. split; reflexivity. Qed.
(* g_s's base, which it hands diginet_session_poll and diginet_session_rx, and the addresses of the globals it stores
   or loads at constant addresses. *)
Definition RECV_S : Z := TB_g_s.
Lemma recv_addrs :
  RECV_S = POLL_S /\ RECV_S = SRX_S /\
  TB_OW = 0x5f2ce0 /\ TW.SZ_OW = 304 /\ TB_GOT = 0x5e4f60 /\ TW.SZ_GOT = 224 /\
  TB_OW + (TW.A_OW_desk_off - TW.OFF_OW) = 0x5f2dc8 /\ TB_M + (TW.A_M_fail - TW.OFF_M) = 0x5dee38 /\
  TB_g_fail_next = 0x5deda0 /\ TB_g_rx_send = 0x5e5060 /\ TB_g_rx_len = 0x5f2cc0 /\ TB_g_rx = 0x5df620 /\
  TB_g_rx_times = 0x5f2ca0 /\ TB_g_rx_fail = 0x5f2c80 /\ TB_g_now = 0x5ded80.
Proof. repeat split; reflexivity. Qed.

(* Every address a successful malloc can return, as the plain contract asks of its model premise
   (lib/U/Prog/T/receive_c.v h_addr_ok). *)
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
  twb_fld TW.OFF_OW TB_OW TW.OFF_OW TW.SZ_OW a \/
  twb_fld TW.OFF_GOT TB_GOT TW.OFF_GOT TW.SZ_GOT a \/
  twb_fld TW.OFF_M TB_M TW.A_M_fail 4 a \/
  twb_fld TW.OFF_g_rx_send TB_g_rx_send TW.OFF_g_rx_send TW.SZ_g_rx_send a \/
  twb_fld TW.OFF_g_rx_len TB_g_rx_len TW.OFF_g_rx_len TW.SZ_g_rx_len a \/
  twb_fld TW.OFF_g_rx TB_g_rx TW.OFF_g_rx TW.SZ_g_rx a \/
  twb_fld TW.OFF_g_rx_times TB_g_rx_times TW.OFF_g_rx_times TW.SZ_g_rx_times a \/
  twb_fld TW.OFF_g_rx_fail TB_g_rx_fail TW.OFF_g_rx_fail TW.SZ_g_rx_fail a \/
  mrx_wr a \/
  srx_wr bytes a \/
  poll_wr a.

(* The shadow facts of the record (lib/B/YF0m.v Tfib_zero_shadow and Tfib_const_shadow rows) the two memsets need:
   OW's payload (304 bytes, 38 whole granules) and GOT's (224 bytes, 28 whole granules) have shadow 0, and the rest of
   their hulls' aligned groups of 8 shadow bytes is visible: for OW, g_rx_len's payload granule (0x5f2cc0, a zero
   shadow row) and its three guard granules (0xf9), and OW's first six guard granules after its payload (0xf9); for
   GOT, the last four guard granules of g_s (0xf9), which share GOT's first group. *)
Definition trans_recv_cells (B : asyms) : Prop :=
  decode_zshadow_at B TB_OW (TB_OW + TW.SZ_OW) /\
  decode_zshadow_at B TB_GOT (TB_GOT + TW.SZ_GOT) /\
  decode_zshadow_at B TB_g_rx_len (TB_g_rx_len + TW.SZ_g_rx_len) /\
  forall ly,
    In (z1 (ANum (ACells.shadow_addr (TB_g_rx_len + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_g_rx_len + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_g_rx_len + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_OW + TW.SZ_OW))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_OW + TW.SZ_OW + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_OW + TW.SZ_OW + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_OW + TW.SZ_OW + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_OW + TW.SZ_OW + 32))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_OW + TW.SZ_OW + 40))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_GOT - 32))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_GOT - 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_GOT - 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TB_GOT - 8))) 0xf9) (as_const B ly).
Lemma trans_recv_cells_rows :
  map ACells.shadow_addr [TB_g_rx_len; TB_g_rx_len + 8; TB_g_rx_len + 24; TB_OW; TB_OW + TW.SZ_OW;
                          TB_OW + TW.SZ_OW + 40; TB_GOT - 32; TB_GOT - 8; TB_GOT] =
  [0x800b6598; 0x800b6599; 0x800b659b; 0x800b659c; 0x800b65c2; 0x800b65c7; 0x800b49e8; 0x800b49eb; 0x800b49ec].
Proof. reflexivity. Qed.

(* The traces its two allocator calls record, which the call rules ask to be in the trace universe (YC5d.v
   amalloc04_rule, afree04_rule; YCbq.v call_trace0, YG0d.v chain_pre, YG00.v bad_next): the malloc at 0x836dc runs
   before receive writes s0, so the frame-pointer chain is the entry's and the trace is its return address 0x836e0
   followed by the tail of the entry context c = raZ regs :: spine ch; the free at 0x8380c is a call with s0 holding
   the heap block (`mv s0, a0` at 0x836e4), an address below alloc_ceiling and so below sp, hence bad_next and an
   empty chain: its trace is its return address 0x83810 alone, the same for every context (the split of fuzz_decode's
   image-B check_round_trip_cg.v, projects/libreac/fuzz_decode/proofs/lib/B/Prog/check_round_trip_cg.v
   820554da266b: dec_crt_uctx for a trace that follows the context, dec_crt_ufix for a fixed one; here one
   predicate). *)
Definition trans_recv_uctx (B : asyms) (CTX : list (list Z)) : Prop :=
  (forall c, In c CTX ->
     In (decode_utrace (pc_malloc_ra0 (as_code B)) (RECV_RA_MALLOC :: tl c)) (as_universe B)) /\
  In (decode_utrace (pc_free_ra0 (as_code B)) [RECV_RA_FREE]) (as_universe B).

Section recv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The meter cost of one call: the malloc of max (n, 1) bytes and the free. *)
Definition recv_cost (n : Z) : Z := mo_malloc MT (Z.max 1 n) + mo_free MT.

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with at most two events, the written range
   recv_wr bytes, the meter charged at most recv_cost n, and X: for the address a the malloc returned, the model's
   world Bw' of receive_m at a, the world relation at it and g_fail_next Bw' <= 1. transport_cg_post states the
   caller's blocks up to permutation (the block is freed) and frames S2 = frames Sc. *)
Definition transport_recv_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw bytes : list byte) (by_poll pf : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs RECV_STK RECV_EV (recv_cost (Z.of_nat (length bytes))) (recv_wr bytes)
    (fun regs2 W2 mem2 =>
       exists (a : Z) (Bw' : list byte),
         recv_addr_ok a /\ TOP.receive_m timg_B Bw a bytes by_poll pf = Some (Bw', tt) /\
         tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a0, for call contexts CTX (the entry's return address followed by the
   frame-pointer chain's), in the G-form caller-journal form. *)
Definition transport_receive_cg (a0 : Z) (CTX : list (list Z)) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p by_poll pf T : Z) (bytes : list byte) (Bw : list byte) ch,
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
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
    tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    (forall a, recv_addr_ok a -> TOP.receive_m timg_B Bw a bytes by_poll pf <> None) ->
    trans_rom_view_rd W memc ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN) ->
    TW.S_queued Bw <= TC.QUEUE_MAX ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    TW.g_ncmd Bw <= TC.CMDS_MAX ->
    1 <= TW.S_cfg_max_cmds Bw -> 1 <= TW.S_cfg_max_body Bw ->
    recv_dn_each timg_B Bw bytes by_poll pf ->
    count_cid POLL_CID (frames Sc) + 1 < fs_frames POLL_CID ->
    count_cid SRX_CID (frames Sc) + 1 < fs_frames SRX_CID ->
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
   __asan_memcpy, __asan_memset, spec_read_frame, diginet_session_poll, m_rx, diginet_session_rx, settle and the free
   wrapper (pc order of their first call: 0x836dc, 0x836f8, 0x83710, 0x8374c, 0x837c4, 0x837dc, 0x837fc, 0x83804,
   0x8380c) give the contract at TB_receive for the contexts CTX. *)
Definition transport_receive_cg_holds_stmt (CTX : list (list Z)) : Prop :=
  pc_wrap_malloc (as_code B) = transportb_sigma TB___interceptor_trampoline_malloc ->
  pc_wrap_free (as_code B) = transportb_sigma TB___interceptor_trampoline_free ->
  transport_cells B -> trans_recv_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  trans_recv_uctx B CTX ->
  (forall fx' : YK11.FPState, @amalloc04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_spec_read_frame_cg fx' rc B MT (transportb_sigma TB_spec_read_frame)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_session_poll_cg fx' rc B MT (transportb_sigma TB_diginet_session_poll)) ->
  (forall fx' : YK11.FPState, @transport_m_rx_cg fx' rc B MT (transportb_sigma TB_m_rx)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_session_rx_cg fx' rc B MT (transportb_sigma TB_diginet_session_rx)) ->
  (forall fx' : YK11.FPState, @transport_settle_cg fx' rc B MT (transportb_sigma TB_settle)) ->
  (forall fx' : YK11.FPState, @afree04_rule fx' rc tfib_sink_head segs B MT) ->
  transport_receive_cg (transportb_sigma TB_receive) CTX.
End recv.
