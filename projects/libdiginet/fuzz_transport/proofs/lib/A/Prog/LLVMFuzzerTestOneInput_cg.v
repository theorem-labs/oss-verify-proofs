(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: Section h of proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_cg.v (origin/ossv/recipes 88154566652a; cgif_file_fuzzer lib/A/ACfn.v / lib/A/ACfj.v) for reac-repacer/fuzz_uci's image A: the slot is the relocated core's lib/A/ACfn.v tfib_lib_contract_x_all (so decode's own slot, Section a, is not copied) at the core's lib_shape checksum_shape, the core's sink names in place of Section Variables, and fuzz_uci's three callees; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/LLVMFuzzerTestOneInput_cg.v, with its module paths and module names changed; 112 of its 143 lines of code are new or changed and 32 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_cg: the statement of the walk of fuzz_transport.asan's (e89be137db17) LLVMFuzzerTestOneInput
   (fuzz/fuzz_transport.c:1124-1218, with op_frame (:1035-1050), op_announce (:1052-1066), op_submit (:1068-1122),
   op_begin, m_close, coalescable, spec_system_at and fuzz.h's cursor inlined; model lib/TModel/TOps.v
   LLVMFuzzerTestOneInput_m and LLVMFuzzerTestOneInput_op_m) at 0x81264 = transport_text = lib/A/ACfn.v A_LLVMF, size
   6908, as a STATEMENT only (no proof): the callee contracts and the facts about the record give the core's slot,
   lib/A/ACfn.v tfib_lib_contract_x_all at G = lib/A/TransportG.v G_HARNESS: from the slot's pre (input (p, n) in a
   driver block or the empty input, 0 < n < 2 ^ 26 or n = 0, no side-stack frame live) the call returns 0 to RA_LLVMF
   with the callee-saved registers kept, the G journal of the call (lib/A/W_journalG.v ajournal_gx over G_HARNESS, no
   out cell), at most EV_LIB allocator events, the driver's blocks up to permutation, the input bytes
   unchanged, the sink untouched and the meter charged at most XL n. It is libdiginet/fuzz_frame's entry statement
   (libdiginet/fuzz_frame lib/A/Prog/LLVMFuzzerTestOneInput_cg.v frame_llvmf_holds_stmt, file sha256 a1af309fa46d;
   donor not released) at the core's G-form slot: the harness keeps its whole model in writable globals that the call
   changes, so the slot's journal is ajournal_gx over the harness globals, G_HARNESS.

   The slot's event bound EV_LIB (ACfn.v; the pre's st_nev S + EV_LIB <= EV_MAX, the post's k <= EV_LIB) must cover
   the run: a run makes at most OPS_MAX = 1024 operations (the loop test, below), each receives at most once (TOps.v
   LLVMFuzzerTestOneInput_op_m: ops 0, 1, 2 and 8), and each reception is one call of receive, whose malloc and free
   are its two events (receive_cg.v RECV_EV = 2); no other call of this function's closure records an event. So
   OPS_MAX * RECV_EV = 2048 events are reachable, within the core's EV_LIB (transport_llvmf_events, a computation at
   the slot's EV_LIB by name: transport_llvmf_events_ok).

   The run invariants are DISCHARGED inside the walk, not stated: the statement has no premise on
   the world. The walk takes the world from the memory at entry (TWorldA.v tw_exists_A: the G payload bytes are
   image bytes, read through aview), and the model's run from the plain simulation: TSim/TopOk.v harness_model_ok's
   proof at timg_A (timg_ok timg_A by computation), that is TSim/InitOk.v prologue_ok (agree timg_A 0 at the head of
   the loop) and TSim/LoopOk.v op_ok (agree timg_A ops B at the start of each operation gives the operation's Some and
   agree timg_A (ops + 1) at its end), with the address stream A of the mallocs receive's X names (each recv_addr_ok,
   LoopOk.v heap_ok's condition; the callees' "forall a, recv_addr_ok a -> ... <> None" premises are op_ok at the
   stream that is a at the operation's index). At each callee call the walk derives, from agree timg_A ops B at the
   operation's start world B (TSim/Agree.v):
     (1) TW.M_fly_on <> 0 -> TW.M_fly_len <= SPEC_MAX_FRAME (io_send's, so wake's, close's, tick's, receive's and
         build_and_receive's): agree_fly b8_on01 and b8_frames (fly.on = 1 -> M_fly_len = frame_len (length body) with
         length body <= 1484, so at most 1514);
     (2) TW.S_queue_len i <= DIGINET_CMD_MAX_LEN for i < TW.S_queued (settle's, take's, so tick's, receive's and
         build_and_receive's): TSim/TickTakeQ.v tt_sq_ok (from agree_q: d1_entry over d2_cmd in tagged mode, D4 in
         raw mode; every session entry has 1 <= len <= 24), with its bound TW.S_queued <= QUEUE_MAX (asked beside (2)
         by receive, diginet_session_tick and build_and_receive; TSim/Deadline.v queued_le: agree_q d1_queued and
         d1_nq in tagged mode, d4_queued in raw mode);
     (4) every PENDING command g_cmd[s], s < g_ncmd, has Cmd_len <= SPEC_CMD_MAX (check_latest_sent's, so io_send's,
         so diginet_session_wake's, diginet_session_close's, diginet_session_tick's, receive's and build_and_receive's):
         agree_q d2_cmd (Cmd_st <> 0 -> 3 <= Cmd_len <= 24), with its bound TW.g_ncmd <= CMDS_MAX (asked beside (4) by
         receive, diginet_session_tick and build_and_receive; agree_q d3_ncmd, g_ncmd <= ops, and d3_ops,
         ops <= OPS_MAX = CMDS_MAX);
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
   diginet_session_wake and diginet_session_close the operation's steps (op_begin's two memsets, OW.desk_off and M.fail,
   the g_now store, m_tick, m_wake, m_close) write no byte the invariants read but M.fly.on, which they set to 0 only
   (TCb.v m_lost_m, under m_tick, and m_close_m), so (1) stays true; settle is each operation's last step and TCb.v
   settle_m answers Some (B, tt) at the world B it is given (each of its checks answers that or None), so (2) at its
   call world is tt_sq_ok (in the per-index form TickTakeQ.v ttq_sq_d4) at agree timg_A (ops + 1), the operation's
   end world (LoopOk.v op_ok). For m_tick and m_wake the keep is TModel/TRunInv.v m_tick_rk and m_wake_rk (with
   rk_refl and rk_out, which give run_inv: (1), (2), (4), (5) and the two bounds); no lemma of lib/TModel states it
   for op_begin, the g_now store or m_close as whole steps, so there the walk reads each invariant's fields (TWorld.v
   accessors) at the worlds the model names. The plain facts take the simulation's hypothesis links
   (TSim/LinksProof.v links_holds).

   The record facts (premises of the holds statement; each a closed fact the closing file decides on the record):
   transport_cells (the GOT words, the flag word and the shadow base; the payload shadow rows of the read-only globals),
   diginet_session_config_default_cg.v trans_scfg_cells (g_cfg's shadow: the memcpys of HOST and DESK into g_cfg),
   receive_cg.v trans_recv_cells (OW's and GOT's zero shadow and their hulls' cells: op_begin's two memsets in ops 3 to
   6), settle_cg.v trans_settle_cells (the zero shadow of GOT, OW, g_q and g_cmd: op 4's instrumented loads and stores
   into g_q and g_cmd, its memset and memcpy into g_cmd[serial], op 6's stores into OW.t[]), trans_llvmf_cells below
   (M's zero shadow and its memset's hull cells; the 64-byte hulls of the read-only globals the code hands
   build_and_receive, the memcpys and the strlen wrapper: their 0xf9 redzone cells and the two unregistered zero
   ranges; this is the hull fact DgnTransportCg.v trans_src_ok's read-only disjunct needs through trans_sh_any for
   SPEC_BCAST and DESK, op_announce's arguments and op_frame's, and for HOST, OTHER, DESK2 and NOTDD, op_frame's),
   trans_g_unowned, trans_g_no_errno, trans_ro_rd_unowned, trans_rom_no_errno (G and the TRANS_RO_RD bytes across the
   stack malloc and each callee; trans_rom_view_rd and aro_unowned at each call from the slot's arodata_okS), the
   read-only range RLO <= TRANS_RLO and TRANS_RHI <= RHI (arodata_okS at [RLO, RHI) covers the TRANS_RO_RD bytes of
   the RELRO tables: __const.LLVMFuzzerTestOneInput.io, the op_frame / op_announce pointer tables, SPEC_C24, SPEC_PC
   and personalities), and the sink and meta facts in the G form (HSINK_KEPT / HMETA_KEPT over ajournal_gx G_HARNESS:
   the closing file opens the G journal at its start memory memS (W_journalG.v ajournal_g), which agrees with the true
   start memory outside G, carries asink_none / ameta_inv to memS by lib/Reusable/YE00.v asink_none_frame /
   ameta_ok_frame (the sink's and meta's cells lie outside G), and applies lib/Reusable/YE01.v asink_none_kept /
   ameta_inv_kept, which take that donor journal). The slot's shape is the core's lib/A/TransportShape.v
   transport_shape (lib/AgreeShape.v ag_shape of lib/FrameSlotK.v kept_shape), whose LIBK is the continuation at the
   leaf (return 0, the file system as given, no output).
   The callees' own record facts (trans_tick_cells, trans_sinit_cells, trans_ssubmit_cells, trans_recv_uctx at
   CTX_receive, ...) are premises of their holds statements, not of this one; transport_llvmf_utraces names receive's
   trace facts at the contexts this function's run reaches.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   6908 code bytes are equal in both files), 1727 words, all 4-byte; 106 calls (jal with link), one indirect jump (the
   op switch), one return:
     0x81264 - 0x812c8 sp = sp - 320; 0x81268 stores 8 zero bytes at sp; ra, s0 .. s11 at sp + 312 .. sp + 216 (loaded
                      back at 0x828b4 - 0x828e4); 0x812a0 s0 = sp + 320 (the entry sp, the frame pointer: its record
                      [RA_LLVMF, the driver's s0] at s0 - 8 / s0 - 16, kept to 0x828b0); 0x812a4 sp = sp & -32 (at most
                      0x10 below entry - 320); s1 = the realigned sp; s5 = size (a1, 0x812ac), s3 = data (a0, 0x812c8).
     0x812b0 - 0x812c4 the 8-byte loads of the GOT words 0xa40e8 (0xaca00) and 0xa4090 (0xac9f8), the 4-byte flag word
                      at 0xaca00, s10 = the shadow base at 0xac9f8: transport_cells rows 1, 2, 6, 7.
     0x812cc - 0x81300 the flag word = 0 skips the call (transport_cells row 6 gives 1); a0 = 256 and the call of
                      __asan_stack_malloc_2 (0x3d99c = transport_sigma TS___asan_stack_malloc_2) at 0x812d4, return
                      address 0x812d8: a class-2 side-stack frame (256 bytes); its result 0 takes the real-stack arm
                      0x812e8 - 0x81300 (a probe loop), which astack_malloc_realizes with frames S = [] (the slot's pre)
                      and stack_malloc_progressP rules out. Below, frame = the result (saved at s1 + 0x80; frame at
                      s1 + 0x98 and s1 + 0xd0).
     0x8130c - 0x8133c the header: 0x41b58ab3 at frame, the description 0x17695 ("3 32 32 8 c.i:1070 96 34 11
                      body.i:1056 176 32 7 io:1127": op_submit's struct diginet_cmd c at frame + 32 (32 bytes),
                      op_announce's body[34] at frame + 96, the struct diginet_io io at frame + 176 (32 bytes)) at
                      frame + 8, the function's address 0x81264 at frame + 16.
     0x81344 - 0x813cc the frame's 32 shadow bytes by plain stores: 0..3 = 0xf1, 4..7 = 0xf8 (c out of scope),
                      8..11 = 0xf2, 12..16 = 0xf8 (body out of scope), 17..21 = 0xf2, 22..25 = 0 (io, for the whole call),
                      26..31 = 0xf3.
     0x813d0 - 0x813e0 the call of __asan_memcpy (0x523b0 = TS___asan_memcpy) at 0x813e0 (return 0x813e4): io =
                      __const.LLVMFuzzerTestOneInput.io (0xa3d60, 32 bytes: 0, 0x82d60, 0x834c4, 0x8356c = timg_A's
                      io_send, io_recv, io_now) (:1127).
     0x813e4          size >> 26 <> 0 goes to the epilogue (return 0, :1130-1131); the slot's 0 < n < 2 ^ 26 or n = 0.
     0x813f0 - 0x81410 size = 0 reads no byte (flags = 0); else the checked 1-byte load of flags at data (:1133).
     0x81420 - 0x8142c the call of diginet_session_config_default (0x862b8) at 0x8142c (return 0x81430), a0 = g_cfg.
     0x81430 - 0x81474 __asan_memcpy (g_cfg, HOST 0x21040, 6) at 0x81440 (return 0x81444); plain 4-byte stores of the
                      three flag bits at g_cfg + 0xc, + 0x10, + 0x14; __asan_memcpy (g_cfg + 6, DESK 0x21060, 6) at
                      0x81474 (return 0x81478) (:1135-1139).
     0x8147c - 0x81564 the config bytes (:1140-1148): each a checked 1-byte load at data + k (k = 1 .. 14) and a plain
                      4-byte store into g_cfg + 0x18 .. + 0x38 (the last, max_body, computed at 0x81508 - 0x81560 and
                      stored at 0x81564); a short input reads each missing byte as 0 in its field's formula (the tail
                      0x814b4 - 0x81504, out-of-line pieces 0x828f0 - 0x82b40).
     0x81528 - 0x81578 plain stores: g_raw (4 bytes, 0x81528), g_now = 1000000 (8, 0x81538), g_fail_next = 0 (ONE
                      byte, 0x81570: the global is one byte, TWorld.v g_fail_next), g_last_counter = 0 (4, 0x81578)
                      (:1150-1153).
     0x8157c - 0x815ac __asan_memset (M + 8, 0, 1640) at 0x81590 (return 0x81594); the plain 4-byte store of
                      desk_known at M + 0; __asan_memcpy (M + 4, DESK, 6) at 0x815ac (return 0x815b0) (:1154-1156:
                      M's 1648 bytes as the model's upd of zeros, set_M_desk_known and set_M_desk).
     0x815c0 - 0x815cc plain stores g_nq = 0, g_ncmd = 0 (4 bytes each), g_rx = 0 (8) (:1157-1158).
     0x815d0 - 0x815f0 the call of diginet_session_init (0x864ec) at 0x815f0 (return 0x815f4): a0 = g_s, a1 = g_cfg,
                      a2 = io (frame + 176), a3 = notice 0x83578 (timg_A's ti_notice), a4 = 0 (:1165).
     0x815f4 - 0x815f8 a0 <> 0 goes to 0x82b44: the no-return entry (0x5a4c4) at 0x82b44 and abort (0x93734) at
                      0x82b48 (:1166); the model premise of the slot's run (diginet_session_init_m answers SPEC_OK,
                      TOps.v :394) rules it out.
     0x81600          in.n = 0 goes to the epilogue (:1168).
     the loop (0x8166c - 0x82568, :1168-1216): the checked 1-byte load of the op byte at p; op = byte % 9; op = 8 goes to
                      0x8194c (bltu at 0x816a4); else the 4-byte load at 0x20fac + 4 * op (TRANS_JT_LLVMF, 8 words, a
                      plain load of a TRANS_RO_RD range) + 0x20fac and the jump (jr a0) at 0x816c0: op 0 -> 0x816c4,
                      1 -> 0x8184c, 2 -> 0x817c8, 3 -> 0x81818, 4 -> 0x816f0, 5 -> 0x8187c, 6 -> 0x818e8, 7 -> 0x81840.
                      The tail 0x8254c - 0x82568: ops > 1022 (unsigned) goes to the epilogue, else ops + 1 and
                      in.n <> 0 loops: at most OPS_MAX = 1024 operations.
     op 0 (0x816c4) and op 8 (0x8194c): the record's length (two checked loads), then (op 8 first reads pf) the ONE call
                      of receive (0x837d0) at 0x81b6c, return address 0x81b70: a0 = the record's start (in the input
                      block), a1 = its length (at most 65535), a2 = by_poll (0 for op 0, 1 for op 8), a3 = poll_flags
                      (0, or the byte pf) (:1171-1174, :1209-1214).
     op 1 (0x8184c), op_frame: the checked byte loads of sel, send, ack, retry and w; ack = the plain 4-byte load of
                      g_last_counter when sel & 0x80 (the sign-extending lw at 0x81f4c: its low 32 bits are ack);
                      len = min (w mod 1485, in.n); the checked 8-byte loads of
                      op_frame.DST[sel >> 5 & 3] (0xa3e20) and op_frame.SRC[sel >> 3 & 3] (0xa3de0) and the checked
                      1-byte load of op_frame.CMD[(sel & 7) mod 7] (0x21100); the call of build_and_receive (0x857e0) at
                      0x8237c, return address 0x82380: a0 = HOST / SPEC_BCAST / OTHER / HOST, a1 = DESK / DESK2 / HOST /
                      NOTDD, a2 = send (16 bits), a3 = ack (16 bits, or g_last_counter's 32 bits), a4 = retry (0 .. 3),
                      a5 = cmd, a6 = the cursor p (in the input block), a7 = len (:1043-1049).
     op 2 (0x817c8), op_announce: the checked byte loads of sel, mac, name; shadow bytes 12..15 = 0 and 16 = 2 (body in
                      scope); __asan_memset (body, 0, 34) at 0x81ae4 or 0x81c3c; __asan_memcpy (body + mac, HOST, 6) or
                      (body + mac - 10, OTHER, 6) at 0x81c58 (HOST at body + mac when mac < 10, OTHER at body + mac - 10
                      when 10 <= mac <= 12, no copy when mac > 12); "1.37" by plain stores at body + 15 .. + 18;
                      the checked 8-byte load of op_announce.NAME[name mod 3] (0xa3e60: 0x210c0 "CNTRL|24", 0x210e0
                      "MAINUNIT", 0x21180 "OTHER"); the call of the strlen wrapper (0x42ce4 = transport_sigma
                      TS___interceptor_trampoline_strlen) at 0x81cc0, return address 0x81cc4, a0 = that string; its
                      result (8, 8 or 5) the length of __asan_memcpy (body + 24, the string, ..) at 0x81cd0; the call of
                      build_and_receive at 0x81d00, return address 0x81d04: a0 = SPEC_BCAST 0x21080, a1 = DESK 0x21060,
                      a2 = a3 = a4 = 0, a5 = 0xe0 + (sel & 1), a6 = body (frame + 96), a7 = 34; shadow bytes 12..16 =
                      0xf8 (:1055-1065).
     op 3 (0x81818): the checked byte load; the checked 8-byte load of SCALE[byte & 3] (0x21000); op_begin
                      (__asan_memset (OW, 0, 304) at 0x819f0, __asan_memset (GOT, 0, 224) at 0x81a04, the 1-byte load of
                      g_fail_next, plain stores OW.desk_off = -1 and M.fail); the u16; g_now = g_now + SCALE * u16 (plain
                      8-byte load and store); m_tick (0x83c34) at 0x81bd4 (return 0x81bd8); diginet_session_tick
                      (0x892b8) at 0x81be4 (return 0x81be8), a0 = g_s, a1 = the new g_now; settle (0x83cac) at 0x81bec
                      (return 0x81bf0), a0 = 1 (:1181-1188).
     op 4 (0x816f0), op_submit: shadow bytes 4..7 = 0 (c in scope); before = the plain load of g_s.queued; op_begin
                      (memsets at 0x81724, 0x81738); __asan_memset (c, 0, 32) at 0x81760; key and display into c; the
                      plain load of g_raw. Raw (g_raw <> 0): the plain store of c.len at c + 0x18 (0x81e9c);
                      __asan_memcpy (c, p, len) at 0x81ea8; diginet_session_submit
                      (0x89ef0) at 0x81eb8 (return 0x81ebc), a0 = g_s, a1 = c; check_refusal_submit (0x86110) at 0x81ec8
                      (return 0x81ecc), a0 = c, a1 = rc, a2 = before. Tagged: serial = the plain load of g_ncmd;
                      __asan_memset (g_cmd + 40 serial, 0, 40) at 0x81dd4; the len byte (with the plain 8-byte load of
                      the divisor constant at 0x10398, TRANS_K_LLVMF); the tag and serial bytes into c;
                      __asan_memcpy (c + 3, p, n) at 0x82004; spec_system_at over c (checked 1-byte loads of c);
                      coalescable and the find loop over g_q (checked 4-byte loads of g_q[i] and g_cmd[g_q[i]].key);
                      diginet_session_submit at 0x823d4 (return 0x823d8); check_refusal_submit at 0x823ec (return
                      0x823f0); check_latest_submit (0x86230) at 0x823fc (return 0x82400), a0 = rc, a1 = want, unless
                      sys; when want = 0 the checked stores of g_cmd[serial]'s st, key, display, len and
                      __asan_memcpy (g_cmd[serial].bytes, c, len) at 0x8247c, then the replace (checked load of g_q[at]
                      and store of g_cmd[g_q[at]].st, plain store of g_q[at]) or the append (plain load of g_nq at
                      0x824dc, plain store of g_nq + 1 at 0x824e4, checked store of g_q[old g_nq] at 0x8250c); the plain
                      loads of c's len, key and display (0x82008, 0x820d0, 0x82434, 0x82450, 0x8246c) and of g_nq
                      (0x82120, 0x823b4); the plain g_ncmd + 1. Both: settle at 0x82530 (return 0x82534), a0 = 0;
                      shadow bytes 4..7 = 0xf8 (:1068-1122).
     op 5 (0x8187c): op_begin (memsets at 0x81890, 0x818a4); m_wake (0x83d00) at 0x818bc (return 0x818c0);
                      diginet_session_wake (0x866fc) at 0x818d4 (return 0x818d8), a0 = g_s, a1 = g_now;
                      check_state_wake_code (0x83e48) at 0x818e0 (return 0x818e4), a0 = rc, a1 = want; settle at 0x82280
                      (return 0x82284), a0 = 0 (:1193-1198).
     op 6 (0x818e8): op_begin (memsets at 0x818fc, 0x81910); m_close inlined (plain loads of M.desk_known, M.foreign,
                      M.state, OW.e3 (0x821cc) and OW.n (0x821ec); plain stores of OW.e3, M.fail, M.fly.on and M.state;
                      m_set's checked stores of OW.t[n].state / .old / .reason at OW + 12n + 4 .. + 12 when n <= 15,
                      and the plain store of OW.n + 1 at 0x8225c for every n);
                      diginet_session_close (0x8713c) at 0x82278 (return 0x8227c), a0 = g_s, a1 = g_now; settle at
                      0x82280 (:1200-1205).
     op 7 (0x81840): the plain 1-byte store g_fail_next = 1 (:1206-1208).
     the epilogue (0x82770 - 0x828ec, every exit): shadow bytes 22..25 = 0xf8; the header word 0x45e0360e at frame;
                      shadow bytes 0..31 = 0xf5 and the inline release (the 8-byte load of the word at frame + 248,
                      then the zero byte store through it, 0x82820 - 0x82824; astack_free_law); the real-stack arm
                      0x8282c - 0x828a8 (not taken); a0 = 0 (:1217); sp = s0 - 320, the loads back, sp + 320, return.
   The model and the code: every test and store is TOps.v's (LLVMFuzzerTestOneInput_m, the prologue; _op_m, the op
   switch; op_frame_m, op_announce_m, op_submit_m; TCb.v op_begin_m, m_close_m), read through tw_at, garr8 of the input
   bytes and the registers; the model's None cases are ruled out by the model's Some (harness_model_ok above).
   Error paths (61 calls; one abort pair, above) and the facts that rule them out:
     TS___asan_report_load1 (45): the input bytes at data + k and at the cursor (each read only while in.n > 0, so
       inside the input block (p, n) of ablocks, whose n bytes are addressable: AR_laws' al_blocks); op_frame.CMD at
       0x21100 + i, i < 7 (its shadow byte 7, transport_cells); c + i, c + i + 1, c + i + 3 for i < len - 3 <= 21
       (inside c, shadow bytes 4..7 = 0 since 0x816f0).
     TS___asan_report_load8 (4): SCALE + 8i (i < 4), op_announce.NAME + 8i (i < 3), op_frame.DST / SRC + 8i (i < 4):
       inside their payloads, zero-shadow rows of transport_cells.
     TS___asan_report_load4 (3), _store4 (8), _store1 (1): g_q + 4i and g_cmd + 40 s + {0, 4, 8, 0x24} with
       i < g_nq <= QUEUE_MAX (for the append store at 0x8250c, i = the old g_nq, below g_nq raised at 0x824e4 and
       below QUEUE_MAX by the want test at 0x823b4 - 0x823c4) and s < CMDS_MAX (the model's indices: agree_q d1_entry /
       d1_nq / d3_ops, and the model's Some, which excludes serial = CMDS_MAX), inside the zero-shadow payloads of g_q
       and g_cmd (trans_settle_cells); OW + 12n + 4 .. + 12 with n = OW.n = 0 after op_begin's memset of OW (inside OW,
       trans_settle_cells).
     The memsets' and memcpys' own checks (aintrin_realizes' pre, through TransportGCg.v gx_intrin_at): destinations
       in the own frame (io, body, c: their shadow 0 since the stores above), in g_cfg (trans_scfg_cells), M
       (trans_llvmf_cells), OW / GOT (trans_recv_cells) or g_cmd[serial] (trans_settle_cells, g_cmd's payload is
       64-byte aligned and a multiple of 64 bytes); sources in TRANS_RO_RD (trans_llvmf_cells' hulls with
       transport_cells' payload rows: trans_sh_any), in the input block, or c in the own frame (the memcpy at
       0x8247c; c's shadow bytes 4..7 = 0 since 0x816f0).
   Writes: g_cfg, g_raw, g_now, g_fail_next, g_last_counter, M, g_nq, g_ncmd, g_rx, OW, GOT, g_cmd, g_q (bytes of G, the
   G journal's), the own side-stack frame, its shadow and its flag byte, the own machine frame; and the callees'.

   Contexts. At every call s0 is the entry sp, so the frame-pointer chain the callees see is this function's record
   [RA_LLVMF, the driver's s0] and, since the slot's pre states the entry chain [] (afn_pre ... []), nothing more: the
   chain's return addresses are [RA_LLVMF], or [] when s0 lies within 16 bytes of ly_top (YCbq.v achain). So
   build_and_receive's call contexts are [[0x81d04]; [0x81d04; RA_LLVMF]; [0x82380]; [0x82380; RA_LLVMF]]
   (CTX_build_and_receive), and receive's are [[0x81b70]; [0x81b70; RA_LLVMF]] from its direct call followed by
   build_and_receive_cg.v bar_recv_ctx CTX_build_and_receive (CTX_receive).

   Callee texts assumed and what supplies each call's premises:
     __asan_stack_malloc_2 (0x812d4): count_cid 2 [] = 0 < fs_frames 2.
     __asan_memcpy, __asan_memset: above.
     diginet_session_config_default (0x8142c): the world, the model step (TOps.v :357).
     diginet_session_init (0x815f0): iop = frame + 176 (8-aligned, nonzero), its 32 bytes sinit_io_bytes 0 0x82d60 0x834c4
       0x8356c (the memcpy at 0x813e0), trans_src_ok by decode_in_fake with decode_rd_ok (shadow 22..25 = 0), off the
       window, apart from g_s; the model step (:392-393, ti_* of timg_A).
     m_wake (0x818bc), m_tick (0x81bd4): the world and the model step.
     diginet_session_wake (0x818d4), diginet_session_tick (0x81be4), diginet_session_close (0x82278): TF = None
       (trans_tframe_at, trans_tf_off_g and the *_apart premises of None), now = g_now of the world (below 2 ^ 64),
       g_fail_next <= 1, trans_rom_view_rd, the model step (TOps.v :316, :307, :323; fuzz_transport.c :1196, :1186,
       :1203), the run invariants (above; tick's with the two bounds), the counts at the call state (the own class-2
       frame: count_cid 2 = 1, so 1 + 2 < fs_frames 2; class 5 / 0 counts 0).
     check_state_wake_code (0x818e0), check_refusal_submit (0x81ec8, 0x823ec), check_latest_submit (0x823fc): leaves,
       DgnTransportCg.v transport_leaf_at (c at frame + 32 for check_refusal_submit: 32 bytes, shadow 0).
     receive (0x81b6c) at CTX_receive: the record in the input block (decode_in_block), n <= 65535, by_poll and pf
       ranges, the chain (above), the run invariants with the two bounds and recv_dn_each, the five counts (class 5:
       0 + 1, class 2: 1 + 2), st_nev + k + 2 <= EV_MAX (k <= 2 per earlier reception, at most 1023 of them: the
       slot's EV_LIB, transport_llvmf_events_ok), blocks_bytes + 65535 <= LIVE_MAX (LIVE_LIB), and the meter (the
       slot's mo_ok at XL n with the cost bound, through YC5d.v mok_station).
     settle (0x81bec, 0x82280, 0x82530): ticked 1 / 0, (2), the model step; lifted by TransportGCg.v gx_call_cg.
     the strlen wrapper (0x81cc0) as TransportRtCg.v astrlen_realizes: x = NAME[name] (a TRANS_RO_RD string), k = 8, 8
       or 5 (first_byte from the image bytes, trans_rom_view_rd), its shadow from transport_cells' rows and
       trans_llvmf_cells' hulls, the rest of the NUL's word visible (image bytes), aro_unowned from the slot's
       arodata_okS carried by acall_kept_g (an image byte outside G, the owned statics and errno is kept), 2 * ESTACK
       below sp present (the journal's window).
     build_and_receive (0x81d00, 0x8237c) at CTX_build_and_receive: dst / src read-only globals (trans_src_ok's
       TRANS_RO_RD disjunct: trans_sh_any from transport_cells' payload row and trans_llvmf_cells' hull cells,
       decode_rd_ok, off the window: the image lies below the stack), body in the input block (op 1) or body[34] in the
       own frame (op 2, decode_in_fake, shadow 12..15 = 0 and 16 = 2), send < 2 ^ 16, ack < 2 ^ 32, retry < 2 ^ 8,
       cmd < 2 ^ 8, the run invariants with their bounds and recv_dn_each at bar_frame, the counts (class 5: 0 + 2;
       class 2: 1 + 2; classes 1, 4 and 0: 0), events, live bytes and meter as for receive.
     diginet_session_submit (0x81eb8, 0x823d4): cp = c (4-aligned), C = the 32 bytes of c (TOps.v cmd_struct),
       trans_src_ok by decode_in_fake with decode_rd_ok (c's shadow bytes 4..7 = 0), cp <> 0 (a frame address), off
       the window, not in G nor TRANS_RO_RD (a frame byte), count_cid 2 = 1 < fs_frames 2.
   Each callee's own record facts are premises of its holds statement.
   Stack: 320 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window, build_and_receive's BAR_STK (trans_llvmf_use_eq); it fits the slot's LLVMF_STK
   (trans_llvmf_use_fits).
   Meter: each reception charges at most recv_cost n <= mo_malloc MT 65535 + mo_free MT (YC5d.v mo_malloc_mono:
   n <= 65535), at most OPS_MAX receptions: transport_llvmf_cost. *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG TransportShape.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_config_default_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_init_cg m_wake_cg m_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg diginet_session_close_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import receive_cg build_and_receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_state_wake_code_cg check_refusal_submit_cg check_latest_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TShape := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportShape.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module LCSWC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_code_cg.
Module LCRS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_refusal_submit_cg.
Module LCLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_submit_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The entry, as the listing names it; it is the core's ACfn.A_LLVMF. *)
Lemma transport_text_llvmf : transport_text = A_LLVMF.
Proof. reflexivity. Qed.

(* The run's event need (two allocator events, receive's malloc and free, for each of at most OPS_MAX receptions)
   within the slot's bound EV_LIB (lib/A/ACfn.v). *)
Definition transport_llvmf_events : Prop := TC.OPS_MAX * RECV_EV <= EV_LIB.
Lemma transport_llvmf_events_ok : transport_llvmf_events.
Proof. vm_compute. intros H. discriminate H. Qed.

(* ---- the code's constants ---- *)

(* The return addresses of this function's calls of receive (+0x908, 0x81b6c), build_and_receive (+0xa9c, 0x81d00;
   +0x1118, 0x8237c), as offsets from its entry (the jal is 4 bytes before). *)
Definition LLVMF_RA_RECV : list Z := map (fun o => transport_text + o) [0x90c].
Definition LLVMF_RA_BAR : list Z := map (fun o => transport_text + o) [0xaa0; 0x111c].
Lemma llvmf_ras_at : LLVMF_RA_RECV = [0x81b70] /\ LLVMF_RA_BAR = [0x81d04; 0x82380].
Proof. split; reflexivity. Qed.

(* The call contexts (decode's `raZ :: spine ch` convention): the return address followed by [] or [RA_LLVMF]; for
   receive also the contexts it is called at from build_and_receive (build_and_receive_cg.v bar_recv_ctx). *)
Definition CTX_build_and_receive : list (list Z) := flat_map (fun r => [[r]; [r; RA_LLVMF]]) LLVMF_RA_BAR.
Definition CTX_receive : list (list Z) :=
  flat_map (fun r => [[r]; [r; RA_LLVMF]]) LLVMF_RA_RECV ++ bar_recv_ctx CTX_build_and_receive.
Lemma ctx_receive_bar : incl (bar_recv_ctx CTX_build_and_receive) CTX_receive.
Proof. intros c Hc. unfold CTX_receive. apply in_or_app. right. exact Hc. Qed.
Lemma ctx_receive_at : CTX_receive =
  [[0x81b70]; [0x81b70; 0x81160]; [0x85a8c]; [0x85a8c; 0x81d04]; [0x85a8c; 0x81d04; 0x81160];
   [0x85a8c; 0x82380]; [0x85a8c; 0x82380; 0x81160]].
Proof. reflexivity. Qed.

(* This function's frame (`sp = sp - 320`), the at most 0x10 bytes of `sp = sp & -32` (0x812a4), and the largest stack a
   callee uses below the realigned sp: ESTACK for __asan_stack_malloc_2, __asan_memcpy, __asan_memset and the leaves
   (YG0d.v ecall_pre, LeafCgKit.v), 2 * ESTACK for the strlen wrapper (TransportRtCg.v astrlen_realizes), and each
   program callee's own constant. *)
Definition TRANS_LLVMF_FRAME : Z := 320.
Definition TRANS_LLVMF_ALIGN : Z := 0x10.
Definition TRANS_LLVMF_USE : Z :=
  TRANS_LLVMF_FRAME + TRANS_LLVMF_ALIGN +
  Z.max (2 * ESTACK) (Z.max SCFG_STK (Z.max SINIT_STK (Z.max MWAKE_STK (Z.max WAKE_STK (Z.max RECV_STK
    (Z.max MTICK_STK (Z.max TICK_STK (Z.max SETTLE_STK (Z.max BAR_STK (Z.max SSUBMIT_STK CLOSE_STK)))))))))).
Lemma trans_llvmf_use_eq : TRANS_LLVMF_USE = TRANS_LLVMF_FRAME + TRANS_LLVMF_ALIGN + BAR_STK.
Proof. reflexivity. Qed.
Lemma trans_llvmf_use_fits : TRANS_LLVMF_USE <= LLVMF_STK.
Proof. vm_compute. intros H. discriminate H. Qed.

(* The record facts this function's own code and its read-only arguments need beyond transport_cells,
   trans_scfg_cells, trans_recv_cells and trans_settle_cells (each a row of the record: lib/A/AF0m.v
   Tfib_zero_shadow and Tfib_const_shadow): M's payload has zero shadow and the hull of its memset (M + 8, 1640 bytes)
   is visible: the shadow byte of g_last_counter's payload granule (4) and the three guard granules after it (0xf9), and
   M's first six guard granules (0xf9); the 64-byte hulls of the read-only globals the code reads through a callee
   (build_and_receive's dst / src, the memcpys, the strlen wrapper) are visible: in each hull the payload granules are
   transport_cells' rows and the guard granules are 0xf9 (TRANS_LLVMF_F9), the unregistered bytes [0x211a0, 0x211c0)
   (after .str.4 "OTHER") have zero shadow, and io's hull [0xa3d40, 0xa3d80) (32 unregistered bytes, then
   __const.LLVMFuzzerTestOneInput.io's 32-byte payload) is one zero-shadow range.
   The hulls: [0x21040, 0x21080) HOST, DESK; [0x21080, 0x210c0) SPEC_BCAST, SPEC_OUI; [0x21100, 0x21140) op_frame.CMD,
   DESK2; [0x21140, 0x21180) NOTDD, OTHER; [0x210c0, 0x21100) "CNTRL|24", "MAINUNIT"; [0x21180, 0x211c0) "OTHER";
   [0xa3d40, 0xa3d80) io. Measured from the image's asan_globals descriptors (40 at 0xa8940): payload granules 0 or
   the payload's byte count, redzone granules 0xf9. *)
Definition TRANS_LLVMF_F9 : list Z :=
  [TA_g_last_counter + 8; TA_g_last_counter + 16; TA_g_last_counter + 24] ++
  map (fun i => TA_M + TW.SZ_M + 8 * Z.of_nat i) (seq 0 6) ++
  flat_map (fun b => [b + 8; b + 16; b + 24; b + 40; b + 48; b + 56])
    [TRANS_HOST; TRANS_SPEC_BCAST; TRANS_CMD; TRANS_NOTDD] ++
  [TRANS_STR_C24 + 16; TRANS_STR_C24 + 24; TRANS_STR_PC + 16; TRANS_STR_PC + 24] ++
  [TRANS_STR4 + 8; TRANS_STR4 + 16; TRANS_STR4 + 24].
Lemma trans_llvmf_f9_at : TRANS_LLVMF_F9 =
  [0x5df148; 0x5df150; 0x5df158; 0x5df7d0; 0x5df7d8; 0x5df7e0; 0x5df7e8; 0x5df7f0; 0x5df7f8;
   0x21048; 0x21050; 0x21058; 0x21068; 0x21070; 0x21078; 0x21088; 0x21090; 0x21098; 0x210a8; 0x210b0; 0x210b8;
   0x21108; 0x21110; 0x21118; 0x21128; 0x21130; 0x21138; 0x21148; 0x21150; 0x21158; 0x21168; 0x21170; 0x21178;
   0x210d0; 0x210d8; 0x210f0; 0x210f8; 0x21188; 0x21190; 0x21198].
Proof. reflexivity. Qed.
Definition trans_llvmf_cells (B : asyms) : Prop :=
  decode_zshadow_at B TA_M (TA_M + TW.SZ_M) /\
  decode_zshadow_at B (TRANS_STR4 + 32) (TRANS_STR4 + 64) /\
  decode_zshadow_at B (TRANS_IO - 32) (TRANS_IO + 32) /\
  forall ly,
    In (z1 (ANum (ACells.shadow_addr TA_g_last_counter)) 4) (as_const B ly) /\
    (forall a, In a TRANS_LLVMF_F9 -> In (z1 (ANum (ACells.shadow_addr a)) 0xf9) (as_const B ly)).

(* The trace facts of the receptions the run makes: receive_cg.v trans_recv_uctx at CTX_receive, the premise of
   receive's holds statement at these contexts, which the closing file decides on the record. *)
Definition transport_llvmf_utraces (B : asyms) : Prop := trans_recv_uctx B CTX_receive.

(* The statement the walk will prove (the slot at G_HARNESS, at the unit's shape lib/A/TransportShape.v
   transport_shape and with XL as both meter bounds). *)
Section h. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation tfib_K := AE2k.tfib_K.
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
  pc_stack_malloc (as_code B) 2 = transport_sigma TS___asan_stack_malloc_2 ->
  transport_cells B -> trans_scfg_cells B -> trans_recv_cells B -> trans_settle_cells B -> trans_llvmf_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  RLO <= TRANS_RLO -> TRANS_RHI <= RHI ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  @asink_img_laws tfib_sink_head segs B tfib_K ->
  (* HSINK_KEPT / HMETA_KEPT: frame's premises of the same names (the core's lib/Reusable/YE01.v asink_none_kept /
     ameta_inv_kept specialised to one journal step) over the G journal: the slot's post states ajournal_gx *)
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
       ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W0 mem0) md0 -> asink_none segs tfib_K (rd W' mem') md') ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
       ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W0 mem0) M -> ameta_inv segs tfib_K ly' (rd W' mem') M) ->
  @ro_below_ofl segs RLO RHI tfib_sink_head ->
  (* the callee texts, pc order of their first call: 0x812d4, 0x813e0, 0x8142c, 0x81590, 0x815f0, 0x818bc, 0x818d4,
     0x818e0, 0x81b6c, 0x81bd4, 0x81be4, 0x81bec, 0x81cc0, 0x81d00, 0x81eb8, 0x81ec8, 0x82278, 0x823fc *)
  (forall fx : YK11.FPState, @astack_malloc_realizes fx rc segs B 2) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_config_default_cg fx rc B MT (transport_sigma TS_diginet_session_config_default)) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_init_cg fx rc B MT (transport_sigma TS_diginet_session_init)) ->
  (forall fx : YK11.FPState, @transport_m_wake_cg fx rc B MT (transport_sigma TS_m_wake)) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_wake_cg fx rc B MT (transport_sigma TS_diginet_session_wake)) ->
  (forall fx : YK11.FPState, @transport_leaf_at rc B (@LCSWC.transport_check_state_wake_code_cg) fx) ->
  (forall fx : YK11.FPState, @transport_receive_cg fx rc B MT (transport_sigma TS_receive) CTX_receive) ->
  (forall fx : YK11.FPState, @transport_m_tick_cg fx rc B MT (transport_sigma TS_m_tick)) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_tick_cg fx rc B MT (transport_sigma TS_diginet_session_tick)) ->
  (forall fx : YK11.FPState, @transport_settle_cg fx rc B MT (transport_sigma TS_settle)) ->
  (forall fx : YK11.FPState,
     @astrlen_realizes fx rc segs B (transport_sigma TS___interceptor_trampoline_strlen)) ->
  (forall fx : YK11.FPState,
     @transport_build_and_receive_cg fx rc B MT (transport_sigma TS_build_and_receive) CTX_build_and_receive) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_submit_cg fx rc B MT (transport_sigma TS_diginet_session_submit)) ->
  (forall fx : YK11.FPState, @transport_leaf_at rc B (@LCRS.transport_check_refusal_submit_cg) fx) ->
  (forall fx : YK11.FPState,
     @transport_diginet_session_close_cg fx rc B MT (transport_sigma TS_diginet_session_close)) ->
  (forall fx : YK11.FPState, @transport_leaf_at rc B (@LCLS.transport_check_latest_submit_cg) fx) ->
  (forall n, 0 <= n -> transport_llvmf_cost n <= XL n) ->
  @tfib_lib_contract_x_all rc TShape.transport_shape TG.G_HARNESS B MT XL XL RLO RHI.
End h.
