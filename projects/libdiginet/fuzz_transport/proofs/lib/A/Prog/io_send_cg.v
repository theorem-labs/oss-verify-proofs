(* io_send_cg: the ASan walk contract of io_send (fuzz/fuzz_transport.c:823-899, with spec_read_frame and tagged_of
   inlined; model lib/TModel/TCb.v io_send_m) on fuzz_transport.asan (e89be137db17) at 0x82d60 = TImgA.v ti_io_send
   timg_A (the twin's symbol io_send, size 1892; transport_text + AF_io_send in DgnTransportList.v), as STATEMENTS
   only (no proof). It stores into g_fail_next, GOT, M and g_last_counter, four harness globals, and calls ten harness
   check functions, so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over
   G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v
   transport_cg_post (acall_kept_g over G_HARNESS).

   io_send is not a direct call target and has no TS_ symbol: the program reaches it only through the session's
   send pointer (struct diginet_session + 72, g_s.io.send, which diginet_session_init copies from the 32 bytes of
   __const.LLVMFuzzerTestOneInput.io at 0xa3d60 = TRANS_IO, whose second word is 0x82d60). The indirect call sites
   are send_control 0x86f70, diginet_session_tick 0x897f0, send_data 0x8a3a4. Each reads the
   pointer from the world (tw_read of S_io_send; the model's call of io_send compares it with ti_io_send timg_A) and
   applies this statement at that address.

   The contract. a1 = p, the len bytes frame at p (a2 = len = length frame; a0 = ctx is not read). The bytes at p are
   readable by a callee (DgnTransportCg.v trans_src_ok: send_control's buffer in its side-stack frame, or
   g_s.inflight_frame in G), outside this call's stack window (decode_off_win), and either wholly outside G or wholly
   inside g_s's payload (iosend_frame_at). The read-only bytes check_sent_frame compares (HOST) read as the image's
   (trans_rom_view_rd). The memory relates to the world Bw by image A's world relation (TWorldG.v tw_at at
   TWorldA.v TMAP_A, read through aview), and io_send_m timg_A Bw frame = Some (Bw', r). The function returns to ra
   with a0 = r (0, or -EIO = -5 sign-extended), the callee-saved registers kept, no allocator event and no meter
   charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at
   or above alloc_ceiling outside the call's stack window [sp - IOSEND_STK, sp), the image bytes outside G, the owned
   statics and errno, the caller's block and frame bytes outside iosend_wr len), and the world relation at Bw'.

   The translation from the plain contract (lib/Prog/T/io_send_c.v): a0 = r and wmem rsegs m' B' with B' the model's
   world; munch of the frame and the world -> acall_kept_g with E = iosend_wr; a1 = p, a2 = len, 0 < p and
   g_fail_next B <= 1 kept as they are; bytes_at rsegs m p frame -> garr8 of the view + trans_src_ok; off_window sp
   FRAME p len -> decode_off_win regs IOSEND_STK p len; io_send_frame_at (off the plain world, or
   inside g_s) -> iosend_frame_at (every byte outside G, or the whole range inside g_s's payload [0x5df9c0,
   0x5e4118)); wmem -> tw_at; timg_plain -> timg_A; the 16-aligned sp, stk, lo + FRAME <= sp and w_off_stack -> the
   journal's window premises; mem_inv is dropped. iosend_frame_at gives what the plain
   io_send_frame_at gave: no byte the call stores is a frame byte, though callees read the frame after stores
   (check_sent_frame and check_inflight_retry after the store of g_fail_next, check_latest_sent after the stores of
   M.host_counter and g_last_counter, __asan_memcpy after the stores of the M.fly fields). Each stored byte is in
   io_send's own stack window (its struct spec_frame, its int display, the saved registers, the callees' frames),
   which decode_off_win puts apart from the frame, or a byte of iosend_wr, a byte of the payload of M, GOT,
   g_fail_next, g_last_counter, g_cmd, g_q or g_nq: a byte of G (so not a frame byte in the first case) and outside
   [0x5df9c0, 0x5e4118) (so not a frame byte in the second).
   The premises the plain contract does not have:
   - trans_src_ok (the frame is readable where it lies; the ASan form of the plain bytes_at).
   - trans_rom_view_rd W memc: check_sent_frame's own premise (bcmp of f->src with HOST = 0x21040), taken at io_send's
     entry memory, as notice_cg.v takes it. It still holds at the call at 0x83084: before it, io_send stores only
     g_fail_next (.bss) and its own stack frame, and __asan_memset writes only [sp - 152, sp - 72) and its ESTACK
     below sp - 160; no byte of TRANS_RO_RD (read-only image and RELRO, below 0xa4d88) is among them.
   - TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME, check_inflight_retry_cg.v's run invariant (its
     second bcmp reads M.fly.len - 28 bytes from M + 148), under the guard of its plain source: lib/TSim/Agree.v
     b8_frames bounds M.fly.len only when M.fly.on = 1, and io_send is also called with no frame in flight
     (send_control's wake). io_send reaches check_inflight_retry on the e2 / DATA path with f.retry not 0
     (0x830fc), before any store of M.fly.*, so it cannot establish the bound; it carries it on its own Bw. The world
     the callee is handed is check_sent_frame_m's result B1 = B0 = set_g_fail_next Bw 0 (check_sent_frame's post:
     Bw' = Bw), which differs from Bw only at world offset 0xfdc8; M.fly.on is at 0x60 .. 0x63 and M.fly.len at
     0x668 .. 0x66f. check_inflight_retry_m B1 frame = Some _ gives truth (M_fly_on B1), so M_fly_on Bw <> 0 and
     the premise gives M_fly_len B1 = M_fly_len Bw <= 1514.
   - (forall s, 0 <= s < g_ncmd Bw -> Cmd_st Bw s = PENDING -> Cmd_len Bw s <= SPEC_CMD_MAX), check_latest_sent_cg.v's
     run invariant (its bcmp reads t->len bytes of g_cmd[s].bytes). io_send reaches check_latest_sent on the DATA path
     with g_raw = 0 and no keepalive (0x83314) and stores no g_cmd byte and no g_ncmd before it, so it carries it on
     its own Bw. The world the callee is handed is B5 = set_g_last_counter (set_M_host_counter B4 send) send, with
     B4 = B3 = B1 = B0 (check_inflight_new and check_latest_frame: Bw' = Bw), which differs from Bw only at world
     offsets 0xfdc8 (g_fail_next), 0x54 .. 0x57 (M.host_counter) and 0xfdd0 .. 0xfdd3 (g_last_counter). The invariant
     reads g_ncmd (0xfdd8 .. 0xfddb) and, for each s, the bytes A_Cmd_st s .. + 3 and A_Cmd_len s = 0x4dc8 + 40 s
     (+ 36); for no integer s is one of them a written offset (decided over every s with A_Cmd_st s < W_LEN), so the
     invariant at B5 is the invariant at Bw.
   io_send's own code needs no bound the model does not give: each frame byte it reads (the header bytes p + 12 ..
   p + 29, the body bytes p + 30 .. p + 30 + body_len - 1) lies in [p, p + len) (the code reads them only after
   len >= 30, and body_len = numbytes - 16 <= len - 30); g_cmd[s].len (the command count loop) is read only for
   s < g_ncmd, where the model is None unless s < CMDS_MAX, so it lies in g_cmd's payload; __asan_memcpy copies
   min (len, 1514) bytes to M + 120 .. M + 1634 < M + 1648, inside M's payload.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   1892 code bytes are equal in both files), 473 words:
     0x82d60 - 0x82d84 sp = sp - 160; ra, s0 .. s7 at sp + 152 .. sp + 88, loaded back at 0x83390 - 0x833b0
                      (sp = sp + 160 at 0x833b4, return at 0x833b8). No side-stack frame, no frame pointer. Own frame
                      cells: sp + 4 (int display, written by check_latest_sent), sp + 8 .. sp + 88 (struct spec_frame
                      f, SF_SIZE = 80); sp + 0 .. sp + 4 unused. s0 = len, s1 = p (0x82d88 - 0x82d8c).
     0x82d90 - 0x82d9c s4 = the 8-byte load at the GOT word 0xa4090, then at the cell 0xac9f8 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     0x82da0 - 0x82da4 s3 = the 1-byte load of g_fail_next (0x5df120, no instrumented check); the 1-byte store of 0
                      there (:826-829).
     0x82da8 - 0x82db4 a0 = sp + 8, a1 = 0, a2 = 80; call of checked_memset (__asan_memset, 0x5284c = transport_sigma
                      TS___asan_memset) at 0x82db4, return address 0x82db8: f cleared (spec_read_frame, spec.h).
     each instrumented check below: a 1-byte load at a, the shadow byte k at (a >> 3) + 0x7fff8000 (signed); k = 0
                      goes on; else (a & 7) < k (signed) goes on; else the error path. No check guards an access at a
                      constant address of G or at sp.
     0x82db8 - 0x82dc4 len < 30 (unsigned) goes to 0x83074 with a0 = -2.
     0x82dc8 - 0x82e0c checked loads of p[12], p[13]; ethertype = p[12] << 8 | p[13], the 2-byte store at sp + 32
                      (f + 24); <> 0x885f goes to 0x83070 (a0 = -3).
     0x82e10 - 0x82e5c checked loads of p[14], p[15]; numbytes, the 2-byte store at sp + 34 (f + 26); numbytes < 16 or
                      len - 14 < numbytes (unsigned) goes to 0x83074 with a0 = -4.
     0x82e60 - 0x82e6c the 8-byte stores of p at sp + 16 (f + 8, dst) and p + 6 at sp + 24 (f + 16, src).
     0x82e70 - 0x82fdc checked loads of p[16] .. p[27]: sum (2-byte store at sp + 36, f + 28), send (be32, 4-byte store
                      at sp + 40, f + 32), ack (4-byte store at sp + 44, f + 36), retry (2-byte store at sp + 38,
                      f + 30).
     0x82fe0 - 0x8301c checked loads of p[28], p[29]: cmd (1-byte store at sp + 48, f + 40), ncmds (sp + 49, f + 41).
     0x83010 - 0x83028 the 8-byte stores of p + 30 at sp + 56 (f + 48, body), numbytes - 16 at sp + 64 (f + 56,
                      body_len), len - 14 - numbytes at sp + 72 (f + 64, pad_len).
     0x8302c - 0x8306c body_len = 0 goes to 0x8328c; else the checked loads of p[30 + i], i < body_len, summed.
     0x8328c - 0x83294 a0 = 0; the 2-byte store of the sum at sp + 80 (f + 72, body_sum); to 0x83074.
     0x83070 - 0x83074 (a0 = -3 at 0x83070) the 4-byte store of a0 at sp + 8 (f + 0, code).
     0x83078 - 0x83084 a0 = s1 (p), a1 = s0 (len), a2 = sp + 8; call of check_sent_frame (0x83e68) at 0x83084, return
                      address 0x83088 (:831).
     0x83088 - 0x830c8 s5 = f.cmd (1-byte load at sp + 48); 0 or 0xe2 goes to 0x830e8; 0xa0 (SPEC_CMD_ACK) goes on at
                      0x830a0; 0xe3 at 0x830cc; any other value to 0x83384 (:895-896).
     0x830a0 - 0x830b8 ACK (:833-836): GOT.acks (0x5e53ac = GOT + 204) + 1 (32-bit), stored back (no instrumented
                      check); a0 = sp + 8; call of check_ack_frame (0x8415c) at 0x830b4, return address 0x830b8; to
                      0x830dc.
     0x830cc - 0x830d8 E3 (:891-893): GOT.e3 (0x5e53a8 = GOT + 200) + 1, stored back.
     0x830dc - 0x830e4 a0 = sp + 8; call of check_latest_control (0x8420c) at 0x830e0, return address 0x830e4; to
                      0x83384.
     0x830e8 - 0x830ec E2 / DATA (:838-840): f.retry (2-byte load at sp + 38) = 0 goes to 0x83124.
     0x830f0 - 0x83120 retry (:841-843): a0 = p, a1 = len, a2 = sp + 8; call of check_inflight_retry (0x84268) at
                      0x830fc, return address 0x83100; M.fly.retries (M + 108) + 1 stored back; the 8-byte store of
                      g_now (0x5df100) at M + 112 (M.fly.sent); to 0x83384.
     0x83124 - 0x8315c E2 (:846-852): s5 <> 0xe2 goes to 0x83160; call of check_state_wake (0x84370) at 0x8312c, return
                      address 0x83130 (no argument); a0 = sp + 8, call of check_latest_control at 0x83134, return
                      address 0x83138; GOT.e2 (0x5e53a4 = GOT + 196) + 1 stored back; the 4-byte store of f.send
                      (sp + 40) at g_last_counter (0x5df140); s3 & 1 = 0 goes to 0x83338 (the frame in flight); else
                      0x83384.
     0x83160 - 0x83188, 0x833bc - 0x833c8 DATA (:853-856): s2 = f.body_len (sp + 64); s6 = (body_len = 1, the checked
                      load of body[0] at f.body (sp + 56) = 0, and f.ncmds = 1), else 0.
     0x8318c          call of check_inflight_new (0x84398) at 0x8318c, return address 0x83190 (no argument).
     0x83190 - 0x831a4 g_raw (0x5df0e0, 4-byte load) <> 0 or s6 <> 0 goes to 0x83298 (a1 = f.ncmds, :863-865);
                      body_len = 0 goes to 0x8329c with a1 = 0.
     0x831a8 - 0x83258 the command count loop (:858-862, tagged_of :609-615): at = 0, cmds = 0; each round,
                      body_len - at < 3 (unsigned), body[at] <> 0xa0 (TAG) or serial = body[at + 1] | body[at + 2] << 7
                      >= g_ncmd (the 4-byte load at 0x5df980, unsigned compare) gives step = body_len - at; else step =
                      g_cmd[serial].len (the checked 1-byte load at g_cmd + 40 serial + 36, g_cmd = 0x5e5400); the
                      loads of body[at], body[at + 1], body[at + 2] are checked; at = at + step, cmds = cmds + 1
                      (32-bit, sign-extended); at < body_len (unsigned) goes round again; else to 0x8329c.
     0x83298 - 0x832a0 a0 = sp + 8; call of check_latest_frame (0x843e0) at 0x832a0 with a1 = cmds, return address
                      0x832a4 (:866).
     0x832a4 - 0x832c8 s4 = M (0x5df160); the 4-byte stores of f.send at M + 84 (M.host_counter) and at g_last_counter
                      (:867-868); g_raw (loaded again) = 0 and s6 <> 0 goes on (keepalive, :869-873); else 0x83304.
     0x832cc - 0x83300 call of check_keepalive_due (0x844b0) at 0x832cc, return address 0x832d0 (no argument);
                      a1 = g_cfg.keepalive_ms (4-byte unsigned load at g_cfg + 24 = 0x5df098) * 1000;
                      a2 = M.next_ka (M + 48) + a1, stored at M + 48; g_now < a2 (unsigned) goes to 0x83338; else
                      g_now + a1 stored at M + 48; to 0x83338.
     0x83304 - 0x83334 g_raw <> 0 goes to 0x83338; a0 = f.body (sp + 56), a1 = s2 (body_len), a2 = sp + 4; call of
                      check_latest_sent (0x84500) at 0x83314, return address 0x83318 (:875); the 4-byte load at
                      sp + 4 (display) = 0 goes to 0x83338; call of check_latest_display (0x84844) at 0x83320, return
                      address 0x83324 (no argument); the 8-byte store of g_now at M + 64 (M.last_display), the 4-byte
                      store of 1 at M + 72 (M.display_sent) (:876-879).
     0x83338 - 0x83380 the frame in flight (:883-889): the 4-byte store of 1 at M + 96 (M.fly.on), the 1-byte store
                      of s5 at M + 100 (M.fly.cmd), the 4-byte store of f.send at M + 104 (M.fly.counter), the 4-byte
                      store of 0 at M + 108 (M.fly.retries), the 8-byte store of g_now at M + 112 (M.fly.sent);
                      s0 = min (len, 1514), stored (8 bytes) at M + 1640 (M.fly.len); a0 = M + 120 (M.fly.frame,
                      0x5df1d8), a1 = p, a2 = s0; call of checked_memcpy (__asan_memcpy, 0x523b0 = transport_sigma
                      TS___asan_memcpy) at 0x83380, return address 0x83384.
     0x83384 - 0x833b8 a0 = -5 when s3 & 1 = 1, else 0 (`slli 63; srai 63; andi -5`, :898); ra, s0 .. s7 loaded back,
                      sp = sp + 160, return. a1 .. a7 at the return are not stated.
   No tail jump: every call is a jal with link, every j is inside the function, and the function ends with ret.
   The model and the code: the dispatch and every test is io_send_m's (the cmd byte, sf_retry, truth fail, ka,
   g_raw, the count loop's tagged_of_m and step, nk <=? g_now, truth disp), read through tw_at and the struct, whose
   fields are rf frame's after the inlined spec_read_frame; each store is the model's set_* (put of the low bytes);
   the code tests only bit 0 of g_fail_next (0x83150, 0x83384), which is truth fail under g_fail_next Bw <= 1. The
   model's None cases are the callees' aborts (their contracts' model premises, which io_send_m's branch supplies),
   GOT.acks / e2 / e3 at INT_MAX (the code wraps), a command of length 0 in the count loop (the code loops for ever),
   serial >= CMDS_MAX below g_ncmd (the code reads a byte outside g_cmd's payload: g_cmd's guard bytes, the error
   path, for serial < 1280; from serial 1280 on the byte can lie in g_q's payload, whose shadow is 0, and the load
   goes on), and a frame whose parse code is not 0 (check_sent_frame traps on it).
   The trap: none of its own (no call of __asan_handle_no_return or abort).
   Error paths (24 calls, all of errpath_load1 = TS___asan_report_load1 0x594c8) and the facts that rule them out:
     0x833d4, 0x833e0, 0x833ec, 0x833f8, 0x83404, 0x83410, 0x8341c, 0x83428, 0x83434, 0x83440, 0x8344c, 0x83458,
       0x83464, 0x83470, 0x8347c, 0x83488, 0x83494, 0x834a0 (p + 12 .. p + 29), 0x8306c (p + 30 + i, i < body_len),
       0x834ac (body[0] = p + 30), 0x834b0, 0x834b8, 0x834c0 (body[at], body[at + 1], body[at + 2], at + 3 <=
       body_len): each byte lies in [p, p + len), which trans_src_ok marks usable (a heap block: AR's block shadow;
       else decode_rd_ok's range_addressable); no store before them reaches a shadow byte.
     0x83288 (g_cmd + 40 serial + 36): serial < CMDS_MAX (the model), inside g_cmd's payload, whose shadow is 0
       (trans_iosend_cells).
   Callee texts assumed (pc order), and what supplies each premise of each:
     __asan_memset as aintrin_realizes .. OSet (transport_sigma TS___asan_memset), call at 0x82db4, through
       TransportGCg.v gx_intrin_at: d = sp + 8, n = 80, a byte of the journal's window (awr_byte; above the call's
       ESTACK window, transport_twr_ok_g_intro); range_addressable and shadow_hull_vis from CanKit.v
       can_stack_addressable / can_stack_hull (the machine stack's shadow is 0 at every AR state: YG0n.v
       zero_shadow_ranges' first row [ly_stk_lo, ly_stk_hi)); amem_range: a stack range.
     check_sent_frame as check_sent_frame_cg.v transport_check_sent_frame_cg at transport_sigma TS_check_sent_frame
       (call at 0x83084; donor form, through gx_call_cg: gx_ok, gx_noerrno): a0 = p (0 < p), a1 = len, a2 = sp + 8;
       its window CSF_STK below sp - 160 (IOSEND_STK); garr8 of the frame (entry, no store reaches it); trans_src_ok
       and decode_off_win of [p, p + len) (entry premises; Sc unchanged, no store reaches the frame or a shadow byte;
       IOSEND_STK >= 160 + CSF_STK); trans_sframe_at W memc (sp + 8) p (rf frame): the stores of the inlined
       spec_read_frame into the cleared struct (0x82e08 - 0x83290, with code 0 on the path the model allows);
       trans_src_ok of [sp + 8, sp + 88): the machine-stack case (ly_stk_lo lyc <= sp + 8, sp + 88 <= ly_stk_hi lyc:
       the journal's window lies in the stack) with decode_rd_ok (the window's bytes present by the journal,
       range_addressable / shadow_hull_vis by CanKit as for the memset, amem_range); decode_off_win of it:
       sp + 8 >= sp - 160; trans_rom_view_rd: the entry premise, kept (above); tw_at at B0 (the store at 0x82da4,
       tw_write); check_sent_frame_m B0 frame = Some (B1, tt): io_send_m.
     check_ack_frame as check_ack_frame_cg.v transport_check_ack_frame_cg (a leaf: transport_leaf_at, WR = []; call at
       0x830b4, through gx_call_leaf and the leaf bridge DgnTransportLeafb.v): fp = sp + 8 (0 < fp, fp mod 8 = 0);
       bytes_at of f + 36, f + 56, f + 30 (the struct's ack, body_len, retry: rf frame's); addressable of them (the
       stack's zero shadow, CanKit, decode_leafb_addressable); asan_cells (transport_cells, decode_leafb_asan_cells);
       app_mem of the stack (decode_leafb_app_stack); off_stk G (the stack lies above G); the RNG ranges (its window,
       the two cells, the fields and their shadow bytes, g_rx_send: visible G bytes); tw_at at csw_view (G's payloads
       are image bytes); check_ack_frame_m (set_GOT_acks B1 a) frame: io_send_m.
     check_latest_control as check_latest_control_cg.v (leaf; calls at 0x830e0 and 0x83134): fp = sp + 8, bytes_at /
       addressable / RNG of f + 32 (send), RNG of M.host_counter; check_latest_control_m at the world after
       check_ack_frame (ACK), after GOT.e3++ (E3), after check_state_wake (E2).
     check_inflight_retry as check_inflight_retry_cg.v transport_check_inflight_retry_cg at transport_sigma
       TS_check_inflight_retry (call at 0x830fc; donor form, gx_call_cg): the frame and struct facts as for
       check_sent_frame (CIR_STK <= IOSEND_STK - 160), tw_at at B1, check_inflight_retry_m B1 frame, and
       M_fly_len B1 <= 1514 from this statement's guarded run-invariant premise, whose guard that model call gives
       (above).
     check_state_wake as check_state_wake_cg.v (leaf; call at 0x8312c; no argument): tw_at at B1, check_state_wake_m
       B1, RNG of M.foreign. (Every leaf's RNG row of a world global is a G payload byte, visible at every memory:
       TransportGCg.v gx_rw_vis with TransportGRwA.v G_HARNESS_rw.)
     check_inflight_new as check_inflight_new_cg.v (leaf; call at 0x8318c; no argument): tw_at at B1,
       check_inflight_new_m B1, RNG of M.state, M.fly.on, g_now, M.backoff_until.
     check_latest_frame as check_latest_frame_cg.v (leaf; call at 0x832a0): fp = sp + 8, a1 = bv_swrap 32 cmds with
       0 <= cmds < 2 ^ 32 (u32 in cmds_loop; a zero-extended byte for f.ncmds), bytes_at / addressable / RNG of f + 32,
       f + 41, f + 56, RNG of g_cfg.max_body, g_cfg.max_cmds, g_raw, M.host_counter; check_latest_frame_m B3 frame
       cmds.
     check_keepalive_due as check_keepalive_due_cg.v (leaf; call at 0x832cc; no argument): tw_at at B5,
       check_keepalive_due_m B5, RNG of M.state, M.fly.on, g_now, M.backoff_until, M.next_ka.
     check_latest_sent as check_latest_sent_cg.v transport_check_latest_sent_cg at transport_sigma TS_check_latest_sent
       (call at 0x83314; G form, the same journal; its post, TransportGCg.v transport_cg_post_out [(dp, 4)], is
       used as written): bp = f.body = p + 30 (0 < bp), len = body_len, body = firstn body_len (skipn 30 frame)
       (length body_len); garr8, trans_src_ok, decode_off_win (CLS_STK = IOSEND_STK - 160) of the body: sub-ranges
       of the frame's; the body apart from cls_wr (sp + 4): the body is outside io_send's window and outside g_cmd,
       g_q, g_nq (iosend_frame_at); dp = sp + 4: dp mod 4 = 0, transport_twr_ok_g (a window byte above the call's
       ESTACK window), decode_rd_ok (CanKit), decode_off_win (dp >= sp - 160), not in G (the stack lies above G);
       tw_at at B5, check_latest_sent_m B5 body body_len = Some (Bs, disp): io_send_m; the command-length invariant at
       B5: this statement's premise (above).
     check_latest_display as check_latest_display_cg.v (leaf; call at 0x83320; no argument): tw_at at Bs,
       check_latest_display_m Bs, RNG of M.display_sent, M.last_display, g_now, g_cfg.display_gap_us.
     __asan_memcpy as aintrin_realizes .. OCpy (transport_sigma TS___asan_memcpy), call at 0x83380, through
       gx_intrin_at: d = M + 120, n = min (len, 1514) < 2 ^ 32, bytes of G (transport_twr_ok_g's G case);
       range_addressable of [M + 120, M + 120 + n): M's zero shadow; shadow_hull_vis: M's zero shadow, and for
       n = 1513 or 1514 the six guard shadow bytes 0x800b3efa .. 0x800b3eff (trans_iosend_cells); the source
       [p, p + n) inside the frame: src_ok, range_addressable and shadow_hull_vis from trans_src_ok, outside the
       call's ESTACK window (decode_off_win), apart from [M + 120, M + 120 + n) (iosend_frame_at).
   A donor callee keeps every byte of G (gx_call_cg: gx_ok and gx_noerrno) and a leaf every byte outside its ESTACK
   window, so the world relation after each is the one it was handed.
   Stack: 160 bytes of its own; every call runs from sp - 160: check_sent_frame CSF_STK, check_inflight_retry
   CIR_STK, check_latest_sent CLS_STK = 144 + 2 * ESTACK, the leaves and __asan_memset / __asan_memcpy ESTACK:
   IOSEND_STK = 160 + CLS_STK.

   The callers (each through g_s.io.send, the jalr's return address): send_control 0x86f70 (return 0x86f74): a0 =
   s->io.ctx (the 8-byte load at g_s + 64), a1 = s7 = its frame buffer (60 bytes at s9 + 32, inside its class-2
   side-stack frame), a2 = s5 = diginet_frame_build's result (the frame length); diginet_session_tick 0x897f0
   (return 0x897f4): a0 = s->io.ctx, a1 = g_s + 216 (g_s.inflight_frame), a2 = s->inflight_len (the 8-byte load at
   g_s + 1736); send_data 0x8a3a4 (return 0x8a3a8): a0 = s->io.ctx, a1 = s7 = g_s + 216 (g_s.inflight_frame), a2 =
   diginet_frame_build's result (0x8a2ac). Each supplies the G journal of its own walk, the world relation, the frame
   facts (send_control's buffer: decode_in_fake, outside G; g_s.inflight_frame: inG, inside g_s's payload) and the
   two run invariants. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require DgnTransportList.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  check_sent_frame_cg check_inflight_retry_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_ack_frame_cg check_latest_control_cg check_state_wake_cg check_inflight_new_cg check_latest_frame_cg
  check_keepalive_due_cg check_latest_display_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_frame_cg.
Module LLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_control_cg.
Module LSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_cg.
Module LIN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_new_cg.
Module LLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_frame_cg.
Module LKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_due_cg.
Module LLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_display_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* io_send's entry: the value the model's call of io_send tests the session's send pointer against, and the
   listing's offset of io_send from the entry function. *)
Lemma io_send_at :
  TI.ti_io_send timg_A = 0x82d60 /\ TI.ti_io_send timg_A = transport_text + DgnTransportList.AF_io_send.
Proof. split; reflexivity. Qed.

(* io_send's frame (`sp = sp - 160` at its entry; no realignment). Every call runs from sp - 160: check_sent_frame
   (CSF_STK), check_inflight_retry (CIR_STK), check_latest_sent (CLS_STK), the leaves and __asan_memset /
   __asan_memcpy (ESTACK). *)
Definition IOSEND_FRAME : Z := 160.
Definition IOSEND_STK : Z := IOSEND_FRAME + Z.max (Z.max ESTACK (Z.max CSF_STK CIR_STK)) CLS_STK.
Lemma iosend_stk_eq : IOSEND_STK = IOSEND_FRAME + CLS_STK.
Proof. reflexivity. Qed.
(* No allocator event: neither io_send nor a callee calls malloc or free or takes a side-stack frame. *)
Definition IOSEND_EV : Z := 0.

(* Where the frame lies: every byte outside G (send_control's buffer in its side-stack frame), or the whole range
   inside g_s's payload (g_s.inflight_frame). No byte the call stores lies in g_s. *)
Definition iosend_frame_at (p n : Z) : Prop :=
  (forall x, p <= x < p + n -> ~ inG TG.G_HARNESS x) \/ (TA_g_s <= p /\ p + n <= TA_g_s + TW.SZ_g_s).

(* The bytes some path of the call stores into G, field by field, for a frame of n bytes: g_fail_next; GOT.e2,
   GOT.e3, GOT.acks; g_last_counter; M.host_counter, M.next_ka, M.last_display, M.display_sent; M.fly.on, .cmd,
   .counter, .retries, .sent, .len and the first min (n, 1514) bytes of M.fly.frame; and check_latest_sent's: the st
   field of a command (g_cmd[s], s < CMDS_MAX), g_q's payload, g_nq. Each path stores a subset (io_send_m). No other
   callee stores outside its own window; check_latest_sent's int at sp + 4 lies in io_send's own window. *)
Definition iosend_wr (n a : Z) : Prop :=
  twa_fld TW.OFF_g_fail_next TA_g_fail_next TW.OFF_g_fail_next 1 a \/
  twa_fld TW.OFF_GOT TA_GOT TW.A_GOT_e2 4 a \/
  twa_fld TW.OFF_GOT TA_GOT TW.A_GOT_e3 4 a \/
  twa_fld TW.OFF_GOT TA_GOT TW.A_GOT_acks 4 a \/
  twa_fld TW.OFF_g_last_counter TA_g_last_counter TW.OFF_g_last_counter 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_host_counter 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_next_ka 8 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_last_display 8 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_display_sent 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_fly_on 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_fly_cmd 1 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_fly_counter 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_fly_retries 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_fly_sent 8 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_fly_len 8 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_fly_frame (Z.min n TC.SPEC_MAX_FRAME) a \/
  (exists s, 0 <= s < TC.CMDS_MAX /\ twa_fld TW.OFF_g_cmd TA_g_cmd (TW.A_Cmd_st s) 4 a) \/
  twa_fld TW.OFF_g_q TA_g_q TW.OFF_g_q TW.SZ_g_q a \/
  twa_fld TW.OFF_g_nq TA_g_nq TW.OFF_g_nq TW.SZ_g_nq a.

(* The shadow facts of the record (lib/A/AF0m.v Tfib_zero_shadow and Tfib_const_shadow rows) io_send's own code
   needs: g_cmd's payload (40960 bytes, whole granules) has shadow 0 (the instrumented check of g_cmd[serial].len in
   the command count loop); M's payload (1648 bytes, 206 whole granules) has shadow 0 (__asan_memcpy's destination
   check of [M + 120, M + 120 + n)), and the six guard granules after it, which share the aligned group of 8 shadow
   bytes of M's last payload bytes, are 0xf9 (that copy's shadow_hull_vis for n = 1513 or 1514). *)
Definition trans_iosend_cells (B : asyms) : Prop :=
  decode_zshadow_at B TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd) /\
  decode_zshadow_at B TA_M (TA_M + TW.SZ_M) /\
  forall ly,
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M + 32))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M + 40))) 0xf9) (as_const B ly).
Lemma trans_iosend_cells_rows :
  map (fun j => ACells.shadow_addr (TA_M + TW.SZ_M + 8 * j)) [0; 1; 2; 3; 4; 5] =
  [0x800b3efa; 0x800b3efb; 0x800b3efc; 0x800b3efd; 0x800b3efe; 0x800b3eff] /\
  ACells.shadow_addr TA_M = 0x800b3e2c /\ ACells.shadow_addr TA_g_cmd = 0x800b4a80.
Proof. split; [|split]; reflexivity. Qed.

Section iosend. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range
   iosend_wr (length frame), no meter charge, and X: a0 = r (sign-extended) and the world relation at the model's
   world Bw'. *)
Definition transport_io_send_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (n : Z) (Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    IOSEND_STK IOSEND_EV 0 (iosend_wr n)
    (fun regs2 W2 mem2 => YK11.getr regs2 10 = w64 r /\ tw_at TMAP_A (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_io_send_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p r : Z) (frame : list byte) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 11 = w64 p -> YK11.getr regs 12 = w64 (Z.of_nat (length frame)) ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - IOSEND_STK -> spZ regs <= sp0 ->
    0 < p ->
    garr8 segs (mrestrict (w_H W) memc) p (map DSpec.bz frame) ->
    trans_src_ok B lyc Sc W memc p (Z.of_nat (length frame)) ->
    decode_off_win regs IOSEND_STK p (Z.of_nat (length frame)) ->
    iosend_frame_at p (Z.of_nat (length frame)) ->
    TW.g_fail_next Bw <= 1 ->
    trans_rom_view_rd W memc ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TC.io_send_m timg_A Bw frame = Some (Bw', r) ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    st_nev S + k + IOSEND_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_io_send_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (Z.of_nat (length frame)) Bw' r).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of g_cmd
   and of M and M's guard granules, the allocator and meter laws, G inside the image, outside the allocator's statics
   and outside errno (a donor callee keeps G: gx_call_cg), and the contracts of the twelve callees (pc order of their
   first call) give the contract at io_send's entry. *)
Definition transport_io_send_cg_holds_stmt : Prop :=
  transport_cells B -> trans_iosend_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS -> gx_noerrno B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_check_sent_frame_cg fx' rc B MT (transport_sigma TS_check_sent_frame)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LAF.transport_check_ack_frame_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLC.transport_check_latest_control_cg) fx') ->
  (forall fx' : YK11.FPState,
     @transport_check_inflight_retry_cg fx' rc B MT (transport_sigma TS_check_inflight_retry)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSW.transport_check_state_wake_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIN.transport_check_inflight_new_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLF.transport_check_latest_frame_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LKD.transport_check_keepalive_due_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_check_latest_sent_cg fx' rc B MT (transport_sigma TS_check_latest_sent)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLD.transport_check_latest_display_cg) fx') ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  transport_io_send_cg (TI.ti_io_send timg_A).
End iosend.
