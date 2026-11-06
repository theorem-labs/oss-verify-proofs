(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: Section h of proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_cg.v (origin/ossv/recipes 88154566652a; cgif_file_fuzzer lib/A/ACfn.v / lib/A/ACfj.v) for reac-repacer/fuzz_uci's image A: the slot is the relocated core's lib/A/ACfn.v tfib_lib_contract_x_all (so decode's own slot, Section a, is not copied) at the core's lib_shape checksum_shape, the core's sink names in place of Section Variables, and fuzz_uci's three callees; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/LLVMFuzzerTestOneInput_cg.v, with its module paths and module names changed; 122 of its 153 lines of code are new or changed and 32 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_cg: image B's statement of the walk of fuzz_transport.asan-ubsan's (41113a03c82f)
   LLVMFuzzerTestOneInput (fuzz/fuzz_transport.c:1124-1218, with op_frame (:1035-1050), op_announce (:1052-1066),
   op_submit (:1068-1122), op_begin, m_close, coalescable, spec_system_at and fuzz.h's cursor inlined; model
   lib/TModel/TOps.v LLVMFuzzerTestOneInput_m and LLVMFuzzerTestOneInput_op_m) at 0x812a0 = transportb_text =
   lib/B/YCfn.v A_LLVMF, size 7516, as a STATEMENT only (no proof): the callee contracts and the facts about the
   record give the core's slot, lib/B/YCfn.v tfib_lib_contract_x_all at G = lib/B/TransportGB.v G_HARNESS_B: from the
   slot's pre (input (p, n) in a driver block or the empty input, 0 < n < 2 ^ 26 or n = 0, no side-stack frame live)
   the call returns 0 to RA_LLVMF with the callee-saved registers kept, the G journal of the call (lib/A/W_journalG.v
   ajournal_gx over G_HARNESS_B, no out cell), at most EV_LIB allocator events, the driver's blocks up to
   permutation, the input bytes unchanged, the sink untouched and the meter charged at most XL n. Form: image A's
   lib/A/Prog/LLVMFuzzerTestOneInput_cg.v at image B's names; the differences image B's code forces are listed at the
   end of this comment.

   The slot's event bound EV_LIB (lib/B/YCfn.v; the pre's st_nev S + EV_LIB <= EV_MAX, the post's k <= EV_LIB) must
   cover the run: a run makes at most OPS_MAX = 1024 operations (the loop test, below), each receives at most once
   (TOps.v LLVMFuzzerTestOneInput_op_m: ops 0, 1, 2 and 8), and each reception is one call of receive, whose malloc
   and free are its two events (receive_cg.v RECV_EV = 2); no other call of this function's closure records an event.
   So OPS_MAX * RECV_EV = 2048 events are reachable, within the core's EV_LIB (transport_llvmf_events, a computation
   at the slot's EV_LIB by name: transport_llvmf_events_ok).

   The run invariants are DISCHARGED inside the walk, not stated: the statement has no premise on the world. The walk
   takes the world from the memory at entry (TWorldB.v tw_exists_B: the G payload bytes are image bytes, read through
   aview), and the model's run from the plain simulation: TSim/TopOk.v harness_model_ok's proof at timg_B (timg_ok
   timg_B by computation), that is TSim/InitOk.v prologue_ok (agree timg_B 0 at the head of the loop) and
   TSim/LoopOk.v op_ok (agree timg_B ops B at the start of each operation gives the operation's Some and
   agree timg_B (ops + 1) at its end), with the address stream A of the mallocs receive's X names (each
   recv_addr_ok, LoopOk.v heap_ok's condition; the callees' "forall a, recv_addr_ok a -> ... <> None" premises are
   op_ok at the stream that is a at the operation's index). At each callee call the walk derives, from
   agree timg_B ops B at the operation's start world B (TSim/Agree.v):
     (1) TW.M_fly_on <> 0 -> TW.M_fly_len <= SPEC_MAX_FRAME (io_send's, so wake's, close's, tick's, receive's and
         build_and_receive's): agree_fly b8_on01 and b8_frames (fly.on = 1 -> M_fly_len = frame_len (length body) with
         length body <= 1484, so at most 1514);
     (2) TW.S_queue_len i <= DIGINET_CMD_MAX_LEN for i < TW.S_queued (settle's, take's, so tick's, receive's and
         build_and_receive's): TSim/TickTakeQ.v tt_sq_ok (from agree_q: d1_entry over d2_cmd in tagged mode, D4 in
         raw mode; every session entry has 1 <= len <= 24), with its bound TW.S_queued <= QUEUE_MAX (asked beside (2)
         by receive, diginet_session_tick and build_and_receive; TSim/Deadline.v queued_le: agree_q d1_queued and
         d1_nq in tagged mode, d4_queued in raw mode);
     (4) every PENDING command g_cmd[s], s < g_ncmd, has Cmd_len <= SPEC_CMD_MAX (check_latest_sent's, so io_send's,
         so diginet_session_wake's, diginet_session_close's, diginet_session_tick's, receive's and
         build_and_receive's): agree_q d2_cmd (Cmd_st <> 0 -> 3 <= Cmd_len <= 24), with its bound
         TW.g_ncmd <= CMDS_MAX (asked beside (4) by receive, diginet_session_tick and build_and_receive; agree_q
         d3_ncmd, g_ncmd <= ops, and d3_ops, ops <= OPS_MAX = CMDS_MAX);
     (5) 1 <= TW.S_cfg_max_cmds and 1 <= TW.S_cfg_max_body (take's, so tick's, receive's, build_and_receive's):
         agree_cfg a1_max_cmds (1 <= Cfg_max_cmds) and a1_max_body (24 <= Cfg_max_body), with the session's copies
         equal to g_cfg's (TSim/TickTakeW.v tk_cfg_max_cmds, tk_cfg_max_body);
     (3) receive_cg.v recv_dn_each (receive's and build_and_receive's, at the bytes each hands receive): the OW.dn
         entry m_rx stores for a DATA frame points at tf_addr + 30 inside the frame's block with the frame's body
         length (TSim/RxData.v rx_data_g, with rxdata_mtail / rxdata_mtail_ok; reached through TSim/RxOpLib.v
         rxop_begin and TSim/RxOk.v rx_ok_g), for every address a with recv_addr_ok a; on op 8 (by_poll = 1)
         recv_dn_each is diginet_session_poll_cg.v poll_rx_each over every reception inside diginet_session_poll,
         carried through them by TSim/RxOpLib.v rxop_poll_ok, rxop_pre_g_poll and rxop_drain_step;
     and g_fail_next <= 1 (diginet_session_wake's, diginet_session_tick's, diginet_session_close's, receive's and
         build_and_receive's premise): agree_misc e1_fail_next.
   Each invariant holds at the call's world: before the calls of receive, build_and_receive, diginet_session_tick,
   diginet_session_wake and diginet_session_close the operation's steps (op_begin's two memsets, OW.desk_off and
   M.fail, the g_now store, m_tick, m_wake, m_close's own stores and its call of m_set) write no byte the invariants
   read but M.fly.on, which they set to 0 only (TCb.v m_lost_m, under m_tick, and m_close_m), so (1) stays true;
   settle is each operation's last step and TCb.v settle_m answers Some (B, tt) at the world B it is given (each of
   its checks answers that or None), so (2) at its call world is tt_sq_ok (in the per-index form TickTakeQ.v
   ttq_sq_d4) at agree timg_B (ops + 1), the operation's end world (LoopOk.v op_ok). For m_tick, m_wake and the call
   of m_set inside op 6 the keep is TModel/TRunInv.v m_tick_rk, m_wake_rk and m_set_rk (with rk_refl and rk_out,
   which give run_inv: (1), (2), (4), (5) and the two bounds; m_set stores only OW.t[OW.n], OW.n and M.state, which
   no invariant reads); no lemma of lib/TModel states it for op_begin, the g_now store or m_close's own stores as
   whole steps, so there the walk reads each invariant's fields (TWorld.v accessors) at the worlds the model names.
   The plain facts take the simulation's hypothesis links (TSim/LinksProof.v links_holds).

   The record facts (premises of the holds statement; each a closed fact the closing file decides on the record):
   DgnTransportBCg.v transport_cells (the GOT words, the flag word and the shadow base; the payload shadow rows of
   the read-only globals), diginet_session_config_default_cg.v trans_scfg_cells (g_cfg's shadow: the memcpys of HOST
   and DESK into g_cfg), receive_cg.v trans_recv_cells (OW's and GOT's zero shadow and their hulls' cells: op_begin's
   two memsets in ops 3 to 6), settle_cg.v trans_settle_cells (the zero shadow of GOT, OW, g_q and g_cmd: op 4's
   instrumented loads and stores into g_q and g_cmd, its memset and memcpy into g_cmd[serial]), trans_llvmf_cells
   below (M's zero shadow and its memset's hull cells; the 64-byte hulls of the read-only globals a callee reads:
   build_and_receive's dst and src, the memcpys' sources (io, HOST, DESK, OTHER) and the strlen wrapper's strings,
   their 0xf9 redzone cells; this is the hull fact DgnTransportBCg.v trans_src_ok's read-only disjunct needs through
   trans_sh_any for SPEC_BCAST and DESK, op_announce's arguments and op_frame's, and for HOST, OTHER, DESK2 and
   NOTDD, op_frame's; the globals this function reads only by its own checked loads, SCALE, op_frame.DST / SRC /
   CMD and op_announce.NAME, need one shadow byte each, transport_cells' payload rows), trans_g_unowned,
   trans_g_no_errno, trans_ro_rd_unowned, trans_rom_no_errno (G and the TRANS_RO_RD bytes across the stack malloc
   and each callee; trans_rom_view_rd and aro_unowned at each call from the slot's arodata_okS), the read-only
   range RLO <= TRANS_RLO and TRANS_RHI <= RHI (arodata_okS at [RLO, RHI) covers the TRANS_RO_RD bytes in RELRO: the
   struct constant __const.LLVMFuzzerTestOneInput.io, the op_frame / op_announce pointer tables, SPEC_C24, SPEC_PC
   and personalities), and the sink and meta facts in the G form (HSINK_KEPT /
   HMETA_KEPT over ajournal_gx G_HARNESS_B: the closing file opens the G journal at its start memory memS
   (W_journalG.v ajournal_g), which agrees with the true start memory outside G, carries asink_none / ameta_inv to
   memS by lib/Reusable/YE00.v asink_none_frame / ameta_ok_frame (the sink's and meta's cells lie outside G), and
   applies lib/Reusable/YE01.v asink_none_kept / ameta_inv_kept, which take that donor journal). The slot's shape is
   the core's lib/A/TransportShape.v transport_shape (lib/AgreeShape.v ag_shape of lib/FrameSlotK.v kept_shape),
   whose LIBK is the continuation at the leaf (return 0, the file system as given, no output); image B's driver takes
   the same shape (lib/B/TransportDriverB.v).
   The callees' own record facts (trans_tick_cells, trans_sinit_cells, trans_ssubmit_cells, trans_recv_uctx at
   CTX_receive, ...) are premises of their holds statements, not of this one; transport_llvmf_utraces names receive's
   trace facts at the contexts this function's run reaches.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 7516 code bytes, the 57 bytes of its frame
   description at 0x1766f (56 characters and the NUL), the 32 bytes of the jump table at 0x20f5c and the two 8-byte
   divisor constants at 0x10310 and 0x103a8 are equal in both files), 1879 words, all 4-byte; 105 calls (jal with
   link), one indirect jump (the op switch), one return:
     0x812a0 - 0x812e4 sp = sp - 320; 0x812a4 stores 8 zero bytes at sp; ra, s0 .. s11 at sp + 312 .. sp + 216 (loaded
                      back at 0x815a0 - 0x815d0); 0x812dc s0 = sp + 320 (the entry sp, the frame pointer: its record
                      [RA_LLVMF, the driver's s0] at s0 - 8 / s0 - 16, kept to 0x8159c); 0x812e0 sp = sp & -32 (at most
                      0x10 below entry - 320); s1 = the realigned sp; s5 = size (a1, 0x812e8), s6 = data (a0, 0x81304).
     0x812ec - 0x81300 the 8-byte loads of the GOT words 0xa3d48 (0xac680) and 0xa3cf0 (0xac678), the 4-byte flag word
                      at 0xac680, s10 = the shadow base at 0xac678: transport_cells rows 1, 2, 6, 7.
     0x81308 - 0x8133c the flag word = 0 skips the call (transport_cells row 6 gives 1); a0 = 256 and the call of
                      __asan_stack_malloc_2 (0x3d9f8 = transportb_sigma TB___asan_stack_malloc_2) at 0x81310, return
                      address 0x81314: a class-2 side-stack frame (256 bytes); its result 0 takes the real-stack arm
                      0x81324 - 0x8133c (a probe loop), which astack_malloc_realizes with frames S = [] (the slot's
                      pre) and stack_malloc_progressP rules out. Below, frame = the result (saved at s1 + 0x80; frame
                      at s1 + 0xd0 and s1 + 0x88).
     0x81348 - 0x81378 s4 = frame + 0xb0 (io, until 0x817d8); the header: 0x41b58ab3 at frame, the description 0x1766f
                      ("3 32 32 8 c.i:1070 96 34 11 body.i:1056 176 32 7 io:1127": op_submit's struct diginet_cmd c at
                      frame + 32 (32 bytes), op_announce's body[34] at frame + 96, the struct diginet_io io at
                      frame + 176 (32 bytes)) at frame + 8, the function's address 0x812a0 at frame + 16.
     0x81384 - 0x81408 the frame's 32 shadow bytes by plain stores (s2 = (frame >> 3) + the shadow base): 0..3 = 0xf1,
                      4..7 = 0xf8 (c out of scope), 8..11 = 0xf2, 12..16 = 0xf8 (body out of scope), 17..21 = 0xf2,
                      22..25 = 0 (io, for the whole call), 26..31 = 0xf3.
     0x8140c - 0x8141c the call of __asan_memcpy (0x523ec = transportb_sigma TB___asan_memcpy) at 0x8141c (return
                      0x81420): io = __const.LLVMFuzzerTestOneInput.io (0xa39c0, 32 bytes: 0, 0x82ffc, 0x83368,
                      0x83410 = timg_B's io_send, io_recv, io_now) (:1127).
     0x81420 - 0x81424 size >> 26 <> 0 goes to the epilogue (return 0, :1130-1131); the slot's 0 < n < 2 ^ 26 or n = 0.
     0x814e4 - 0x8150c size = 0 reads no byte (flags = 0, 0x815dc); else the UBSan test of the cursor at 0x814f0 and
                      the checked 1-byte load of flags at data (:1133).
     0x815e8 - 0x815f4 a0 = g_cfg (0x5ded00 = TWorldB.v TB_g_cfg); the call of diginet_session_config_default
                      (0x865f4) at 0x815f4 (return 0x815f8).
     0x815f8 - 0x8163c __asan_memcpy (g_cfg, HOST 0x20fe0, 6) at 0x81608 (return 0x8160c); plain 4-byte stores of the
                      three flag bits at g_cfg + 0xc, + 0x10, + 0x14; __asan_memcpy (g_cfg + 6, DESK 0x21000, 6) at
                      0x8163c (return 0x81640) (:1135-1139).
     0x81640 - 0x81738 the config bytes (:1140-1148): each a UBSan test of the cursor, a checked 1-byte load at the
                      cursor and a plain 4-byte store into g_cfg + 0x18 .. + 0x38 (max_cmds = 1 + byte % 255 at
                      0x82d48 - 0x82d60, max_body = 24 + u16 % 1461 at 0x81714 - 0x81738, both by magic multiply); a
                      short input reads each missing byte as 0 in its field's formula (the out-of-line pieces
                      0x82b08 - 0x82de0, which rejoin at 0x8169c, 0x816a4, 0x816ac, 0x816b8, 0x816c4, 0x816c8 and
                      0x816dc).
     0x81700 - 0x8174c plain stores: g_raw (4 bytes, 0x81700), g_now = 1000000 (8, 0x81710), g_fail_next = 0 (ONE
                      byte, 0x81744: the global is one byte, TWorld.v g_fail_next), g_last_counter = 0 (4, 0x8174c)
                      (:1150-1153).
     0x81750 - 0x81780 __asan_memset (M + 8, 0, 1640) (0x52888 = transportb_sigma TB___asan_memset) at 0x81764 (return
                      0x81768); the plain 4-byte store of desk_known at M + 0; __asan_memcpy (M + 4, DESK, 6) at
                      0x81780 (return 0x81784) (:1154-1156: M's 1648 bytes as the model's upd of zeros,
                      set_M_desk_known and set_M_desk).
     0x81784 - 0x817a0 plain stores g_nq = 0, g_ncmd = 0 (4 bytes each), g_rx = 0 (8) (:1157-1158).
     0x817a4 - 0x817c4 the call of diginet_session_init (0x8680c) at 0x817c4 (return 0x817c8): a0 = g_s 0x5df640,
                      a1 = g_cfg, a2 = io (frame + 176), a3 = notice 0x8341c (timg_B's ti_notice), a4 = 0 (:1165).
     0x817c8 - 0x817cc a0 <> 0 goes to 0x82de8: the no-return entry (0x5a500) at 0x82de8 and abort (0x93390) at
                      0x82dec (:1166); the model premise of the slot's run (diginet_session_init_m answers SPEC_OK,
                      TOps.v :394) rules it out.
     0x81828          in.n = 0 goes to the epilogue (:1168).
     the loop (0x81828 - 0x82928, :1168-1216): the UBSan test of the cursor at 0x81830 and the checked 1-byte load of
                      the op byte at 0x8184c; op = byte % 9 (0x81850 - 0x81868, a magic multiply); op > 7 goes to
                      0x81bac (op 8, the bltu at 0x81874); else the 4-byte load at TRANS_JT_LLVMF 0x20f5c + 4 * op (8
                      words, a plain load of a TRANS_RO_RD range) + 0x20f5c and the jump (jr a0) at 0x81890: op 0 ->
                      0x81894, 1 -> 0x81a54, 2 -> 0x81988, 3 -> 0x819f8, 4 -> 0x818d0, 5 -> 0x81a94, 6 -> 0x81b04,
                      7 -> 0x81a48. The tail 0x82910 - 0x82928: ops + 1; ops = 1024 goes to the epilogue, else the loop:
                      at most OPS_MAX = 1024 operations.
     op 0 (0x81894) and op 8 (0x81bac): the record's length (two checked loads; op 8 first reads pf, the checked load
                      at 0x81bcc, or 0 at 0x81cc8), then the ONE call of receive (0x836a8) at 0x81ea0, return address
                      0x81ea4: a0 = the record's start (in the input block), a1 = its length (at most 65535), a2 =
                      by_poll (0 at 0x81e98 for op 0, 1 at 0x81cf4 for op 8, which joins the call by the jump at
                      0x81cfc), a3 = poll_flags (0 at 0x81e9c, or the byte pf) (:1171-1174, :1209-1214).
     op 1 (0x81a54), op_frame: the checked byte loads of sel, send, ack, retry and w; ack = the plain 4-byte load of
                      g_last_counter when sel & 0x80; len = min (w mod 1485, in.n) (0x8260c - 0x82654); the checked
                      8-byte loads of op_frame.DST[sel >> 5 & 3] (0xa3a80) and op_frame.SRC[sel >> 3 & 3] (0xa3a40)
                      and the checked 1-byte load of op_frame.CMD[(sel & 7) mod 7] (0x210a0); the call of
                      build_and_receive (0x85998) at 0x82714, return address 0x82718: a0 = HOST / SPEC_BCAST / OTHER /
                      HOST, a1 = DESK / DESK2 / HOST / NOTDD, a2 = send (16 bits), a3 = ack (16 bits, or
                      g_last_counter's 32 bits), a4 = retry (0 .. 3), a5 = cmd, a6 = the cursor p (in the input block),
                      a7 = len (:1043-1049).
     op 2 (0x81988), op_announce: the checked byte loads of sel, mac, name (mac % 16 at 0x82018, name % 3 at
                      0x81ff8 - 0x82014 with the plain 8-byte load of the divisor constant at 0x10310,
                      TRANS_K_LLVMF); shadow bytes 12..15 = 0 and 16 = 2 (body in scope); __asan_memset (body, 0, 34)
                      at 0x81d3c or 0x82044; __asan_memcpy (body + mac, HOST, 6) or (body + mac - 10, OTHER, 6) at
                      0x82068 (HOST at body + mac when mac < 10, OTHER at body + mac - 10 when 10 <= mac <= 12, no
                      copy when mac > 12: the test at 0x82134); "1.37" by four plain 1-byte stores at
                      0x82074 - 0x82090 (body + 15 .. + 18); the checked 8-byte load of op_announce.NAME[name mod 3]
                      (0xa3ac0: 0x21060 "CNTRL|24", 0x21080 "MAINUNIT", 0x21120 "OTHER"); the call of the strlen
                      wrapper (0x42d20 = transportb_sigma TB___interceptor_trampoline_strlen) at 0x820cc, return
                      address 0x820d0, a0 = that string; its result (8, 8 or 5) the length of
                      __asan_memcpy (body + 24, the string, ..) at 0x820dc; the call of build_and_receive at 0x8210c,
                      return address 0x82110: a0 = SPEC_BCAST 0x21020, a1 = DESK 0x21000, a2 = a3 = a4 = 0,
                      a5 = 0xe0 + (sel & 1), a6 = body (frame + 96), a7 = 34; shadow bytes 12..16 = 0xf8
                      (:1055-1065).
     op 3 (0x819f8): the checked byte load; the checked 8-byte load of SCALE[byte & 3] (0x20fa0); op_begin
                      (__asan_memset (OW, 0, 304) at 0x81c2c, __asan_memset (GOT, 0, 224) at 0x81c40, the 1-byte load
                      of g_fail_next, plain stores OW.desk_off = -1 and M.fail); the u16;
                      g_now = g_now + SCALE * u16 (plain 8-byte load at 0x81f80 and store at 0x81f90); m_tick
                      (0x8383c) at 0x81f94 (return 0x81f98); diginet_session_tick (0x8909c) at 0x81fa4 (return
                      0x81fa8), a0 = g_s, a1 = the new g_now; settle (0x838c0) at 0x81fac (return 0x81fb0), a0 = 1
                      (:1181-1188).
     op 4 (0x818d0), op_submit: shadow bytes 4..7 = 0 (c in scope); before = the plain load of g_s.queued; op_begin
                      (memsets at 0x81904, 0x81918); __asan_memset (c, 0, 32) at 0x81940; key and display into c; the
                      plain load of g_raw. Raw (g_raw <> 0): the plain store of c.len at c + 0x18 (0x825b0);
                      __asan_memcpy (c, p, len) at 0x825bc; diginet_session_submit (0x89aec) at 0x825cc (return
                      0x825d0), a0 = g_s, a1 = c; check_refusal_submit (0x8640c) at 0x825dc (return 0x825e0), a0 = c,
                      a1 = rc, a2 = before. Tagged: serial = the plain load of g_ncmd;
                      __asan_memset (g_cmd + 40 serial, 0, 40) at 0x82280; the len byte (with the plain 8-byte load of
                      the divisor constant at 0x103a8, TRANS_K_LLVMF2); the tag and serial bytes into c;
                      __asan_memcpy (c + 3, p, n) at 0x8233c; spec_system_at over c (checked 1-byte loads of c,
                      0x82350 - 0x823f4); coalescable and the find loop over g_q (checked 4-byte loads of g_q[i] and
                      g_cmd[g_q[i]].key, 0x8248c - 0x82508); diginet_session_submit at 0x82744 (return 0x82748);
                      check_refusal_submit at 0x82758 (return 0x8275c); check_latest_submit (0x86568) at 0x82768
                      (return 0x8276c), a0 = rc, a1 = want, unless sys; when want = 0 the checked stores of
                      g_cmd[serial]'s st, key, display, len and __asan_memcpy (g_cmd[serial].bytes, c, len) at
                      0x827f8, then the replace (checked load of g_q[at] and store of g_cmd[g_q[at]].st, plain store
                      of g_q[at], 0x82804 - 0x82860) or the append (plain load of g_nq at 0x8288c, plain store of
                      g_nq + 1 at 0x82894, checked store of g_q[old g_nq] at 0x828cc); the plain g_ncmd + 1 at
                      0x828ec. Both: settle at 0x828f8 (return 0x828fc), a0 = 0; shadow bytes 4..7 = 0xf8
                      (:1068-1122).
     op 5 (0x81a94): op_begin (memsets at 0x81aa8, 0x81abc); m_wake (0x83914) at 0x81ad8 (return 0x81adc);
                      diginet_session_wake (0x86a38) at 0x81af0 (return 0x81af4), a0 = g_s, a1 = g_now;
                      check_state_wake_code (0x8399c) at 0x81afc (return 0x81b00), a0 = rc, a1 = want; settle at
                      0x81ba4 (return 0x81ba8), a0 = 0 (:1193-1198).
     op 6 (0x81b04): op_begin (memsets at 0x81b18, 0x81b2c); m_close inlined except its call of m_set (plain loads of
                      M.desk_known (0x81b3c), M.foreign (M + 0x18, 0x81b50), M.state (M + 0xc, 0x81b58) and OW.e3
                      (OW + 0xc8, 0x81b64); the plain store of OW.e3 + 1 (0x81b74) after the UBSan test at 0x81b6c,
                      and the plain stores M.fail = 0 (M + 0x58, 0x81b78) and M.fly.on = 0 (M + 0x60, 0x81b7c)); the
                      CALL of m_set (0x85224 = transportb_sigma TB_m_set) at 0x81b88, return address 0x81b8c, with
                      a0 = 3 (S_CLOSED) and a1 = 8 (R_CLOSED); diginet_session_close (0x87648) at 0x81b9c (return
                      0x81ba0), a0 = g_s, a1 = g_now; settle at 0x81ba4 (:1200-1205).
     op 7 (0x81a48): the plain 1-byte store g_fail_next = 1 at 0x81a4c (:1206-1208).
     the epilogue (0x81428 - 0x815d8, every exit): shadow bytes 22..25 = 0xf8; the header word 0x45e0360e at frame
                      (0x81448); shadow bytes 0..31 = 0xf5 and the inline release (the 8-byte load of the word at
                      frame + 248, then the zero byte store through it, 0x814d8 - 0x814dc; YG0d.v astack_free_law);
                      the real-stack arm 0x81518 - 0x81594 (shadow bytes 0..31 = 0; not taken); a0 = 0 (:1217);
                      sp = s0 - 320, the loads back, sp + 320, return (ret at 0x815d8).
   The model and the code: every test and store is TOps.v's (LLVMFuzzerTestOneInput_m, the prologue; _op_m, the op
   switch; op_frame_m, op_announce_m, op_submit_m; TCb.v op_begin_m, m_close_m, m_set_m), read through tw_at, garr8 of
   the input bytes and the registers; the model's None cases are ruled out by the model's Some (harness_model_ok
   above).
   Trap word (0x82de4, the word 0xc0001073: a write of the read-only CSR cycle, an illegal instruction that traps; the
   UBSan build traps, it calls no __ubsan_handle_* entry) with 74 branches, and the facts that rule each group out:
     41 pointer-overflow tests of the cursor, `in->p + 1` of fuzz_u8 (fuzz.h:45): each is taken when p + 1 <= 1
       unsigned, that is p = 0 or p = 2 ^ 64 - 1. The cursor is a byte address of the input block ((p, n) in
       ablocks, 4096 <= p and p + n <= alloc_ceiling by AR_laws' al_blocks) or, when n = 0, A_EMPTY = 0x5dece0, and
       no byte is read past the end (the model's in.n), so none is taken.
     6 pointer-overflow and null tests of `in->p + n` in fuzz_take (fuzz.h:67; 0x81ce4 op 8, 0x81e88 op 0, 0x825a0
       op 4 raw, 0x82654 op 1, 0x8232c / 0x82330 op 4 tagged): n <= in.n, so p + n stays inside the block and is
       not 0.
     9 pointer-overflow tests of a table or array index (0x81a30 SCALE + 8 * (byte & 3), 0x820ac NAME + 8 * name,
       0x82674 DST + 8 * i, 0x826a4 SRC + 8 * i, 0x826c8 CMD + i, 0x82814 g_q + 4 * at, 0x828b0 g_q + 4 * g_nq,
       0x824b8 and 0x82844 g_cmd + 40 * g_q[..]): each base is an image address below TRANS_RHI = 0xa49e8 or a byte of
       G (G_HARNESS_B's hull), and each offset is below 2 ^ 20, so no sum wraps.
     9 pointer-overflow and null tests of a frame address (0x82054 and 0x8213c body + mac, 0x82070 body + 15,
       0x82098 body + 24, 0x82148 and 0x82150 body + mac - 10, 0x82354 c + i (null), 0x82384 and 0x823ac c + i + 1
       and c + i + 3 of spec_system_at): body = frame + 96 and c = frame + 32 of the class-2 frame the stack malloc
       returned, and 4096 <= frame, frame + 256 <= alloc_ceiling (YCbq.v frames_bounds), so no sum wraps, no
       difference wraps and none is 0.
     1 pointer-overflow test of g_cmd + 40 * serial (0x82270): serial <= 1024 (below) and g_cmd = 0x5e5080.
     7 index tests (0x82254 g_ncmd <= 1024, the index of g_cmd[serial]; 0x8248c the find loop's i <> 1024 and
       0x8289c g_nq <= 1023, the indices of g_q[i] and g_q[g_nq]; 0x824a8 and 0x82834 g_q[..] <= 1023 and 0x8277c
       serial <> 1024, the indices of g_cmd[g_q[..]] and g_cmd[serial]; 0x82780 the g_cmd[serial] pointer <> 0; g_q
       and g_cmd each hold CMDS_MAX = 1024 entries, :159,161): the model's indices (agree_q d3_ncmd with
       g_ncmd <= ops and d3_ops with ops <= OPS_MAX = CMDS_MAX, d1_nq with g_nq <= QUEUE_MAX = 512, and d1_entry),
       and the model's Some, which excludes serial = CMDS_MAX.
     1 signed-overflow test of OW.e3 + 1 (0x81b6c): OW.e3 = 0 after op_begin's memset of OW (TCb.v op_begin_m), so
       the sum is 1.
   Error paths (59 calls; one abort pair, above) and the facts that rule them out:
     TB___asan_report_load1 (45): the input bytes at data + k and at the cursor (each read only while in.n > 0, so
       inside the input block (p, n) of ablocks, whose n bytes are addressable: AR_laws' al_blocks); op_frame.CMD at
       0x210a0 + i, i < 7 (its shadow byte 7, transport_cells); c + i, c + i + 1, c + i + 3 for i < len - 3 <= 21
       (inside c, shadow bytes 4..7 = 0 since 0x818d0).
     TB___asan_report_load8 (4): SCALE + 8i (i < 4), op_announce.NAME + 8i (i < 3), op_frame.DST / SRC + 8i (i < 4):
       inside their payloads, zero-shadow rows of transport_cells.
     TB___asan_report_load4 (3), _store4 (6), _store1 (1): g_q + 4i and g_cmd + 40 s + {0, 4, 8, 0x24} with
       i < g_nq <= QUEUE_MAX (for the append store at 0x828cc, i = the old g_nq, below g_nq raised at 0x82894 and
       below QUEUE_MAX by the want test at 0x82720 - 0x82734, on which 0x8276c branches) and s < CMDS_MAX (the
       model's indices: agree_q d1_entry / d1_nq / d3_ops, and the model's Some, which excludes serial = CMDS_MAX),
       inside the zero-shadow payloads of g_q and g_cmd (trans_settle_cells).
     The memsets' and memcpys' own checks (aintrin_realizes' pre, through TransportGCg.v gx_intrin_at): destinations
       in the own frame (io, body, c: their shadow 0 since the stores above), in g_cfg (trans_scfg_cells), M
       (trans_llvmf_cells), OW / GOT (trans_recv_cells) or g_cmd[serial] (trans_settle_cells, g_cmd's payload is
       64-byte aligned and a multiple of 64 bytes); sources in TRANS_RO_RD (trans_llvmf_cells' hulls with
       transport_cells' payload rows: trans_sh_any), in the input block, or c in the own frame (the memcpy at
       0x827f8; c's shadow bytes 4..7 = 0 since 0x818d0).
   Writes: g_cfg, g_raw, g_now, g_fail_next, g_last_counter, M, g_nq, g_ncmd, g_rx, OW, GOT, g_cmd, g_q (bytes of G,
   the G journal's), the own side-stack frame, its shadow and its flag byte, the own machine frame; and the callees'.

   Contexts. At every call s0 is the entry sp, so the frame-pointer chain the callees see is this function's record
   [RA_LLVMF, the driver's s0] and, since the slot's pre states the entry chain [] (afn_pre ... []), nothing more: the
   chain's return addresses are [RA_LLVMF], or [] when s0 lies within 16 bytes of ly_top (YCbq.v achain). So
   build_and_receive's call contexts are [[0x82110]; [0x82110; RA_LLVMF]; [0x82718]; [0x82718; RA_LLVMF]]
   (CTX_build_and_receive), and receive's are [[0x81ea4]; [0x81ea4; RA_LLVMF]] from its direct call followed by
   build_and_receive_cg.v bar_recv_ctx CTX_build_and_receive (CTX_receive).

   Callee texts assumed and what supplies each call's premises:
     __asan_stack_malloc_2 (0x81310): count_cid 2 [] = 0 < fs_frames 2.
     __asan_memcpy, __asan_memset: above.
     diginet_session_config_default (0x815f4): the world, the model step (TOps.v :357).
     diginet_session_init (0x817c4): iop = frame + 176 (8-aligned, nonzero), its 32 bytes sinit_io_bytes 0 0x82ffc
       0x83368 0x83410 (the memcpy at 0x8141c), trans_src_ok by decode_in_fake with decode_rd_ok (shadow 22..25 = 0),
       off the window, apart from g_s; the model step (:392-393, ti_* of timg_B).
     m_wake (0x81ad8), m_tick (0x81f94), m_set (0x81b88, a0 = 3, a1 = 8): the world and the model step (m_set's
       m_set_m Bw 3 8 = Some (Bw', tt), from m_close_m at the operation's world).
     diginet_session_wake (0x81af0), diginet_session_tick (0x81fa4), diginet_session_close (0x81b9c): TF = None
       (trans_tframe_at and the *_apart premises of None, and wake's and close's trans_tf_off_g of None; tick's
       contract has no trans_tf_off_g), now = g_now of the world (below 2 ^ 64),
       g_fail_next <= 1, trans_rom_view_rd, the model step (TOps.v :316, :307, :323; fuzz_transport.c :1196, :1186,
       :1203), the run invariants (above; tick's with the two bounds), the counts at the call state (the own class-2
       frame: count_cid 2 = 1, so 1 + 1 < fs_frames 2 for wake's and close's class-2 premise and 1 < fs_frames 2 for
       tick's class-2 premise; the class-1, class-5 and class-0 counts are 0).
     check_state_wake_code (0x81afc), check_refusal_submit (0x825dc, 0x82758), check_latest_submit (0x82768): leaves,
       DgnTransportBCg.v transport_leaf_at (c at frame + 32 for check_refusal_submit: 32 bytes, shadow 0).
     receive (0x81ea0) at CTX_receive: the record in the input block (decode_in_block), n <= 65535, by_poll and pf
       ranges, the chain (above), the run invariants with the two bounds and recv_dn_each, the five counts (class 5:
       0 + 1, class 1: 0 + 1, classes 3 and 0: 0, class 2: 1 + 2), st_nev + k + 2 <= EV_MAX (k <= 2 per earlier
       reception, at most 1023 of them: the slot's EV_LIB, transport_llvmf_events_ok), blocks_bytes + 65535 <=
       LIVE_MAX (LIVE_LIB), and the meter (the slot's mo_ok at XL n with the cost bound, through YC5d.v mok_station).
     settle (0x81ba4, 0x81fac, 0x828f8): ticked 1 / 0, (2), the model step; lifted by TransportGCg.v gx_call_cg.
     the strlen wrapper (0x820cc) as TransportRtCg.v astrlen_realizes: x = NAME[name] (a TRANS_RO_RD string), k = 8, 8
       or 5 (first_byte from the image bytes, trans_rom_view_rd), its shadow from transport_cells' rows and
       trans_llvmf_cells' hulls, the rest of the NUL's word visible (image bytes), aro_unowned from the slot's
       arodata_okS carried by acall_kept_g (an image byte outside G, the owned statics and errno is kept), 2 * ESTACK
       below sp present (the journal's window).
     build_and_receive (0x8210c, 0x82714) at CTX_build_and_receive: dst / src read-only globals (trans_src_ok's
       TRANS_RO_RD disjunct: trans_sh_any from transport_cells' payload row and trans_llvmf_cells' hull cells,
       decode_rd_ok, off the window: the image lies below the stack), body in the input block (op 1) or body[34] in
       the own frame (op 2, decode_in_fake, shadow 12..15 = 0 and 16 = 2), send < 2 ^ 16, ack < 2 ^ 32, retry < 2 ^ 8,
       cmd < 2 ^ 8, the run invariants with their bounds and recv_dn_each at bar_frame, the counts (class 5: 0 + 2;
       class 1: 0 + 1; class 2: 1 + 2; classes 3 and 0: 0), events, live bytes and meter as for receive.
     diginet_session_submit (0x825cc, 0x82744): cp = c (4-aligned), C = the 32 bytes of c (TOps.v cmd_struct),
       trans_src_ok by decode_in_fake with decode_rd_ok (c's shadow bytes 4..7 = 0), cp <> 0 (a frame address), off
       the window, not in G nor TRANS_RO_RD (a frame byte), count_cid 2 = 1 < fs_frames 2.
   Each callee's own record facts are premises of its holds statement.
   Stack: 320 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window, build_and_receive's BAR_STK (trans_llvmf_use_eq); it fits the slot's LLVMF_STK
   (trans_llvmf_use_fits).
   Meter: each reception charges at most recv_cost n <= mo_malloc MT 65535 + mo_free MT (YC5d.v mo_malloc_mono:
   n <= 65535), at most OPS_MAX receptions: transport_llvmf_cost.

   The differences from image A's form (lib/A/Prog/LLVMFuzzerTestOneInput_cg.v), each forced by image B's code:
   (1) m_set is a function on image B, not inlined: op 6's m_close ends in a CALL of m_set (0x81b88, a0 = 3, a1 = 8)
   where image A's code inlines m_set's checked stores of OW.t[OW.n].state / .old / .reason and the plain store of
   OW.n + 1 (image A 0x82200 - 0x8225c). So the holds statement takes m_set_cg.v's contract (a nineteenth callee
   text), and this function makes no instrumented store of OW.t: its _store4 / _store1 error paths are only op 4's.
   m_set's contract asks no record fact; its own holds statement asks trans_ow_cells (OW's zero shadow, a conjunct of
   trans_recv_cells and trans_settle_cells), so this statement takes no new premise for it.
   (2) The addresses, and the model, the world relation and the G journal at timg_B, TMAP_B and G_HARNESS_B: the
   entry 0x812a0 (size 7516, 1879 words; image A 0x81264, 6908, 1727), RA_LLVMF 0x8119c, the GOT words 0xa3d48 /
   0xa3cf0, the description string 0x1766f, the jump table 0x20f5c, the divisor constants 0x10310 (% 3) and 0x103a8
   (% 22) and the read-only globals at image B's bases (the TRANS_ names of DgnTransportBCg.v), so
   trans_llvmf_cells names image B's hulls of the read-only globals a callee reads: HOST alone in
   [0x20fc0, 0x21000), DESK with SPEC_BCAST in [0x21000, 0x21040), SPEC_OUI with "CNTRL|24" in [0x21040, 0x21080),
   "MAINUNIT" with op_frame.CMD in [0x21080, 0x210c0), DESK2 with NOTDD in [0x210c0, 0x21100), OTHER with "OTHER"
   in [0x21100, 0x21140), and the struct constant io's hull [0xa39c0, 0xa3a00) (image A: six hulls at 0x21040 ..
   0x211c0 and io's at 0xa3d40, there with 32 unregistered zero-shadow bytes, and the unregistered zero range after
   "OTHER"; image B's hulls hold no unregistered byte, so trans_llvmf_cells states no such range).
   (3) The UBSan tests: 74 branches to the trap word 0x82de4 (image A has none), each refuted by a fact the statement
   already has (the input block's bounds, the own frame's bounds, the model's indices, op_begin's memset of OW), so
   no premise is added; and image B's op byte, name, c.len and max_body use magic multiplies with two constant-pool
   words (TRANS_K_LLVMF, TRANS_K_LLVMF2), both TRANS_RO_RD ranges read by plain loads (image A reads one, at
   0x10398).
   (4) The counts the callees ask: image B's diginet_session_wake is of class 1 and asks count_cid 1 (frames Sc) <
   fs_frames 1 with count_cid 2 (frames Sc) + 1 < fs_frames 2 beside it (image A: its own class-2 frame,
   count_cid 2 (frames Sc) + 2 < fs_frames 2); image B's diginet_session_close takes no side-stack frame and asks
   count_cid 2 (frames Sc) + 1 < fs_frames 2 (CLOSE_CID = 2, its callees' class; image A: + 2); image B's receive
   asks count_cid 1 (frames Sc) + 1 < fs_frames 1 and the on_announce count of class 3 (image A: class 1 without
   + 1, class 4) — what this function supplies at its call state with its own class-2 frame live. Its own frame,
   its class (2, 256 bytes asked), its description's three variables, its 32 shadow bytes and its inline release by
   the flag store are image A's. *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportShape.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_config_default_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_init_cg m_wake_cg m_tick_cg m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg diginet_session_close_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg build_and_receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  check_state_wake_code_cg check_refusal_submit_cg check_latest_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TShape := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportShape.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module LCSWC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_code_cg.
Module LCRS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_refusal_submit_cg.
Module LCLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_submit_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The entry, as the listing names it; it is the core's YCfn.A_LLVMF. *)
Lemma transportb_text_llvmf : transportb_text = A_LLVMF.
Proof. reflexivity. Qed.

(* The run's event need (two allocator events, receive's malloc and free, for each of at most OPS_MAX receptions)
   within the slot's bound EV_LIB (lib/B/YCfn.v). *)
Definition transport_llvmf_events : Prop := TC.OPS_MAX * RECV_EV <= EV_LIB.
Lemma transport_llvmf_events_ok : transport_llvmf_events.
Proof. vm_compute. intros H. discriminate H. Qed.

(* ---- the code's constants ---- *)

(* The return addresses of this function's calls of receive (+0xc00, 0x81ea0), build_and_receive (+0xe6c, 0x8210c;
   +0x1474, 0x82714), as offsets from its entry (the jal is 4 bytes before). *)
Definition LLVMF_RA_RECV : list Z := map (fun o => transportb_text + o) [0xc04].
Definition LLVMF_RA_BAR : list Z := map (fun o => transportb_text + o) [0xe70; 0x1478].
Lemma llvmf_ras_at : LLVMF_RA_RECV = [0x81ea4] /\ LLVMF_RA_BAR = [0x82110; 0x82718].
Proof. split; reflexivity. Qed.

(* The call contexts (decode's `raZ :: spine ch` convention): the return address followed by [] or [RA_LLVMF]; for
   receive also the contexts it is called at from build_and_receive (build_and_receive_cg.v bar_recv_ctx). *)
Definition CTX_build_and_receive : list (list Z) := flat_map (fun r => [[r]; [r; RA_LLVMF]]) LLVMF_RA_BAR.
Definition CTX_receive : list (list Z) :=
  flat_map (fun r => [[r]; [r; RA_LLVMF]]) LLVMF_RA_RECV ++ bar_recv_ctx CTX_build_and_receive.
Lemma ctx_receive_bar : incl (bar_recv_ctx CTX_build_and_receive) CTX_receive.
Proof. intros c Hc. unfold CTX_receive. apply in_or_app. right. exact Hc. Qed.
Lemma ctx_receive_at : CTX_receive =
  [[0x81ea4]; [0x81ea4; 0x8119c]; [0x85d0c]; [0x85d0c; 0x82110]; [0x85d0c; 0x82110; 0x8119c];
   [0x85d0c; 0x82718]; [0x85d0c; 0x82718; 0x8119c]].
Proof. reflexivity. Qed.

(* This function's frame (`sp = sp - 320`), the at most 0x10 bytes of `sp = sp & -32` (0x812e0), and the largest stack
   a callee uses below the realigned sp: ESTACK for __asan_stack_malloc_2, __asan_memcpy, __asan_memset and the
   leaves (YG0d.v ecall_pre, LeafCgKit.v), 2 * ESTACK for the strlen wrapper (TransportRtCg.v astrlen_realizes), and
   each program callee's own constant (m_set's MSET_STK among them: image B calls m_set). *)
Definition TRANS_LLVMF_FRAME : Z := 320.
Definition TRANS_LLVMF_ALIGN : Z := 0x10.
Definition TRANS_LLVMF_USE : Z :=
  TRANS_LLVMF_FRAME + TRANS_LLVMF_ALIGN +
  Z.max (2 * ESTACK) (Z.max SCFG_STK (Z.max SINIT_STK (Z.max MWAKE_STK (Z.max WAKE_STK (Z.max RECV_STK
    (Z.max MTICK_STK (Z.max MSET_STK (Z.max TICK_STK (Z.max SETTLE_STK
      (Z.max BAR_STK (Z.max SSUBMIT_STK CLOSE_STK))))))))))).
Lemma trans_llvmf_use_eq : TRANS_LLVMF_USE = TRANS_LLVMF_FRAME + TRANS_LLVMF_ALIGN + BAR_STK.
Proof. reflexivity. Qed.
Lemma trans_llvmf_use_fits : TRANS_LLVMF_USE <= LLVMF_STK.
Proof. vm_compute. intros H. discriminate H. Qed.

(* The record facts this function's own code and the callees it hands read-only globals to need beyond
   transport_cells, trans_scfg_cells, trans_recv_cells and trans_settle_cells (each a row of the record:
   lib/B/YF0m.v Tfib_zero_shadow and Tfib_const_shadow): M's payload (1648 bytes) has zero shadow and the hull of its
   memset (M + 8, 1640 bytes) is visible: the shadow byte of g_last_counter's payload granule (4) and the three guard
   granules after it (0xf9), and M's first six guard granules (0xf9); the 64-byte hulls of the read-only globals a
   callee reads (build_and_receive's dst / src, the memcpys' sources, the strlen wrapper's strings) are visible: in
   each hull the payload granules are transport_cells' rows and the guard granules are 0xf9 (TRANS_LLVMF_F9).
   The hulls: [0x20fc0, 0x21000) HOST (its first four granules are SCALE's redzone); [0x21000, 0x21040) DESK,
   SPEC_BCAST; [0x21040, 0x21080) SPEC_OUI, "CNTRL|24"; [0x21080, 0x210c0) "MAINUNIT", op_frame.CMD;
   [0x210c0, 0x21100) DESK2, NOTDD; [0x21100, 0x21140) OTHER, "OTHER"; [0xa39c0, 0xa3a00) io.
   SCALE, op_frame.SRC / DST and op_announce.NAME are read only by this function's own checked 8-byte loads (and
   op_frame.CMD by its own checked 1-byte load), one shadow byte each, transport_cells' payload rows; no callee reads
   their hulls.
   Measured from the image's asan_globals descriptors (40 at 0xa85a0): payload granules 0 or the payload's byte
   count, redzone granules 0xf9. *)
Definition TRANS_LLVMF_F9 : list Z :=
  [TB_g_last_counter + 8; TB_g_last_counter + 16; TB_g_last_counter + 24] ++
  map (fun i => TB_M + TW.SZ_M + 8 * Z.of_nat i) (seq 0 6) ++
  [TRANS_HOST - 32; TRANS_HOST - 24; TRANS_HOST - 16; TRANS_HOST - 8;
   TRANS_HOST + 8; TRANS_HOST + 16; TRANS_HOST + 24] ++
  flat_map (fun b => [b + 8; b + 16; b + 24; b + 40; b + 48; b + 56]) [TRANS_DESK; TRANS_DESK2; TRANS_OTHER] ++
  [TRANS_SPEC_OUI + 8; TRANS_SPEC_OUI + 16; TRANS_SPEC_OUI + 24; TRANS_SPEC_OUI + 48; TRANS_SPEC_OUI + 56] ++
  [TRANS_STR_PC + 16; TRANS_STR_PC + 24; TRANS_STR_PC + 40; TRANS_STR_PC + 48; TRANS_STR_PC + 56] ++
  flat_map (fun b => [b + 32; b + 40; b + 48; b + 56]) [TRANS_IO].
Lemma trans_llvmf_f9_at : TRANS_LLVMF_F9 =
  [0x5dedc8; 0x5dedd0; 0x5dedd8; 0x5df450; 0x5df458; 0x5df460; 0x5df468; 0x5df470; 0x5df478;
   0x20fc0; 0x20fc8; 0x20fd0; 0x20fd8; 0x20fe8; 0x20ff0; 0x20ff8;
   0x21008; 0x21010; 0x21018; 0x21028; 0x21030; 0x21038;
   0x210c8; 0x210d0; 0x210d8; 0x210e8; 0x210f0; 0x210f8;
   0x21108; 0x21110; 0x21118; 0x21128; 0x21130; 0x21138;
   0x21048; 0x21050; 0x21058; 0x21070; 0x21078;
   0x21090; 0x21098; 0x210a8; 0x210b0; 0x210b8;
   0xa39e0; 0xa39e8; 0xa39f0; 0xa39f8].
Proof. reflexivity. Qed.
Definition trans_llvmf_cells (B : asyms) : Prop :=
  decode_zshadow_at B TB_M (TB_M + TW.SZ_M) /\
  forall ly,
    In (z1 (ANum (ACells.shadow_addr TB_g_last_counter)) 4) (as_const B ly) /\
    (forall a, In a TRANS_LLVMF_F9 -> In (z1 (ANum (ACells.shadow_addr a)) 0xf9) (as_const B ly)).

(* The trace facts of the receptions the run makes: receive_cg.v trans_recv_uctx at CTX_receive, the premise of
   receive's holds statement at these contexts, which the closing file decides on the record. *)
Definition transport_llvmf_utraces (B : asyms) : Prop := trans_recv_uctx B CTX_receive.

(* The statement the walk will prove (the slot at G_HARNESS_B, at the unit's shape lib/A/TransportShape.v
   transport_shape and with XL as both meter bounds). *)
Section h. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation tfib_K := YE2k.tfib_K.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* The meter of one call: at most OPS_MAX receptions, each a malloc of at most 65535 bytes and its free. *)
Definition transport_llvmf_cost (n : Z) : Z := TC.OPS_MAX * (mo_malloc MT 65535 + mo_free MT).

Definition transport_LLVMFuzzerTestOneInput_cg_holds_stmt : Prop :=
  (* the code address of the class-2 stack malloc (astack_malloc_realizes at pc_stack_malloc, YG0d.v); memset, memcpy
     and the strlen wrapper take the listing's address directly *)
  pc_stack_malloc (as_code B) 2 = transportb_sigma TB___asan_stack_malloc_2 ->
  transport_cells B -> trans_scfg_cells B -> trans_recv_cells B -> trans_settle_cells B ->
  trans_llvmf_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  RLO <= TRANS_RLO -> TRANS_RHI <= RHI ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  @asink_img_laws tfib_sink_head segs B tfib_K ->
  (* HSINK_KEPT / HMETA_KEPT: frame's premises of the same names (the core's lib/Reusable/YE01.v asink_none_kept /
     ameta_inv_kept specialised to one journal step) over the G journal: the slot's post states ajournal_gx *)
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
       ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W0 mem0) md0 -> asink_none segs tfib_K (rd W' mem') md') ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
       ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W0 mem0) M -> ameta_inv segs tfib_K ly' (rd W' mem') M) ->
  @ro_below_ofl segs RLO RHI tfib_sink_head ->
  (* the callee texts, pc order of their first call: 0x81310, 0x8141c, 0x815f4, 0x81764, 0x817c4, 0x81ad8, 0x81af0,
     0x81afc, 0x81b88, 0x81b9c, 0x81ba4, 0x81ea0, 0x81f94, 0x81fa4, 0x820cc, 0x8210c, 0x825cc, 0x825dc, 0x82768 *)
  (forall fx : YK11.FPState, @astack_malloc_realizes fx rc segs B 2) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_config_default_cg fx rc B MT (transportb_sigma TB_diginet_session_config_default)) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (transportb_sigma TB___asan_memset)) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_init_cg fx rc B MT (transportb_sigma TB_diginet_session_init)) ->
  (forall fx : YK11.FPState, @transport_m_wake_cg fx rc B MT (transportb_sigma TB_m_wake)) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_wake_cg fx rc B MT (transportb_sigma TB_diginet_session_wake)) ->
  (forall fx : YK11.FPState, @transport_leaf_at rc B (@LCSWC.transport_check_state_wake_code_cg) fx) ->
  (forall fx : YK11.FPState, @transport_m_set_cg fx rc B MT (transportb_sigma TB_m_set)) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_close_cg fx rc B MT (transportb_sigma TB_diginet_session_close)) ->
  (forall fx : YK11.FPState, @transport_settle_cg fx rc B MT (transportb_sigma TB_settle)) ->
  (forall fx : YK11.FPState, @transport_receive_cg fx rc B MT (transportb_sigma TB_receive) CTX_receive) ->
  (forall fx : YK11.FPState, @transport_m_tick_cg fx rc B MT (transportb_sigma TB_m_tick)) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_tick_cg fx rc B MT (transportb_sigma TB_diginet_session_tick)) ->
  (forall fx : YK11.FPState,
     @astrlen_realizes fx rc segs B (transportb_sigma TB___interceptor_trampoline_strlen)) ->
  (forall fx : YK11.FPState,
     @transport_build_and_receive_cg fx rc B MT (transportb_sigma TB_build_and_receive) CTX_build_and_receive) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_submit_cg fx rc B MT (transportb_sigma TB_diginet_session_submit)) ->
  (forall fx : YK11.FPState, @transport_leaf_at rc B (@LCRS.transport_check_refusal_submit_cg) fx) ->
  (forall fx : YK11.FPState, @transport_leaf_at rc B (@LCLS.transport_check_latest_submit_cg) fx) ->
  (forall n, 0 <= n -> transport_llvmf_cost n <= XL n) ->
  @tfib_lib_contract_x_all rc TShape.transport_shape TG.G_HARNESS_B B MT XL XL RLO RHI.
End h.
