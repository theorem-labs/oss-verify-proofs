(* io_send_cg: image B's ASan walk contract of io_send (fuzz/fuzz_transport.c:823-899, spec_read_frame and tagged_of
   CALLED; model lib/TModel/TCb.v io_send_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x82ffc = TImgB.v
   ti_io_send timg_B (the twin's symbol io_send, size 876; transportb_text + AF_io_send in DgnTransportBList.v), as
   STATEMENTS only (no proof). It stores into g_fail_next, GOT, M and g_last_counter, four harness globals, and calls
   twelve harness functions, so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v
   ajournal_gx over G = lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post is
   lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS_B). Image B's twin of
   lib/A/Prog/io_send_cg.v; the differences image B's code forces are listed at the end of this comment.

   io_send is not a direct call target and has no TB_ symbol: the program reaches it only through the session's
   send pointer (struct diginet_session + 72, g_s.io.send, which diginet_session_init copies from the 32 bytes of
   __const.LLVMFuzzerTestOneInput.io at 0xa39c0 = TRANS_IO, whose second word is 0x82ffc). The indirect call sites:
   send_control 0x870fc, diginet_session_tick 0x894c0, send_data 0x89ff8. Each reads the pointer from the world
   (tw_read of S_io_send; the model's call of io_send compares it with ti_io_send timg_B) and applies this statement
   at that address.

   The contract. a1 = p, the len bytes frame at p (a2 = len = length frame; a0 = ctx is not read). The bytes at p are
   readable by a callee (DgnTransportBCg.v trans_src_ok: send_control's buffer in its side-stack frame, or
   g_s.inflight_frame in G), outside this call's stack window (decode_off_win), and either wholly outside G or wholly
   inside g_s's payload (iosend_frame_at). The read-only bytes check_sent_frame and check_latest_sent read (HOST, the
   constant-pool word TRANS_K_SENT) read as the image's (trans_rom_view_rd). The memory relates to the world Bw by
   image B's world relation (TWorldG.v tw_at at TWorldB.v TMAP_B, read through aview), and io_send_m timg_B Bw frame =
   Some (Bw', r). The function returns to ra with a0 = r (0, or -EIO = -5 sign-extended), the callee-saved registers
   kept, no allocator event and no meter charge, the caller's side-stack frames and blocks exactly, the bytes
   acall_kept_g G_HARNESS_B keeps (the bytes at or above alloc_ceiling outside the call's stack window
   [sp - IOSEND_STK, sp), the image bytes outside G, the owned statics and errno, the caller's block and frame bytes
   outside iosend_wr len), and the world relation at Bw'.

   The translation from the plain contract (lib/Prog/T/io_send_c.v): a0 = r and wmem rsegs m' B' with B' the model's
   world; munch of the frame and the world -> acall_kept_g with E = iosend_wr; a1 = p, a2 = len, 0 < p and
   g_fail_next B <= 1 kept as they are; bytes_at rsegs m p frame -> garr8 of the view + trans_src_ok; off_window sp
   FRAME p len -> decode_off_win regs IOSEND_STK p len; io_send_frame_at (off the plain world, or
   inside g_s) -> iosend_frame_at (every byte outside G, or the whole range inside g_s's payload [0x5df640,
   0x5e3d98)); wmem -> tw_at; timg_plain -> timg_B; the 16-aligned sp, stk, lo + FRAME <= sp and w_off_stack -> the
   journal's window premises; mem_inv is dropped. iosend_frame_at gives what the plain
   io_send_frame_at gave: no byte the call stores is a frame byte, though callees read the frame after stores
   (check_sent_frame and check_inflight_retry after the store of g_fail_next, check_latest_sent after the stores of
   M.host_counter and g_last_counter, __asan_memcpy after the stores of the M.fly fields). Each stored byte is in
   io_send's own stack window (its struct spec_frame, its int display, the saved registers, the callees' frames),
   which decode_off_win puts apart from the frame, or a byte of iosend_wr, a byte of the payload of M, GOT,
   g_fail_next, g_last_counter, g_cmd, g_q or g_nq: a byte of G (so not a frame byte in the first case) and outside
   [0x5df640, 0x5e3d98) (so not a frame byte in the second).
   The premises the plain contract does not have:
   - trans_src_ok (the frame is readable where it lies; the ASan form of the plain bytes_at).
   - trans_rom_view_rd W memc: check_sent_frame's own premise (bcmp of f->src with HOST = 0x20fe0) and, on image B,
     check_latest_sent's (its plain `ld` of the constant-pool word TRANS_K_SENT = 0x10338), taken at io_send's entry
     memory. It still holds at the calls at 0x83060 and 0x8329c: io_send's own stores before them are bytes of G
     (g_fail_next, GOT, M, g_last_counter) and of its own frame; the leaves keep every byte outside their ESTACK
     windows; spec_read_frame's post (acall_kept_g) and check_sent_frame's (acall_kept) keep an image byte outside G
     that is neither an owned static nor errno, which every TRANS_RO_RD byte is by DgnTransportBCg.v
     trans_ro_rd_scoped (trans_ro_rd_unowned, trans_rom_no_errno: premises of the holds statement).
   - TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME, check_inflight_retry_cg.v's run invariant (its
     second bcmp reads M.fly.len - 28 bytes from M + 148), under the guard of its plain source: lib/TSim/Agree.v
     b8_frames bounds M.fly.len only when M.fly.on = 1, and io_send is also called with no frame in flight
     (send_control's wake). io_send reaches check_inflight_retry on the e2 / DATA path with f.retry not 0
     (0x830e0), before any store of M.fly.*, so it cannot establish the bound; it carries it on its own Bw. The world
     the callee is handed is check_sent_frame_m's result B1 = B0 = set_g_fail_next Bw 0 (check_sent_frame's post:
     Bw' = Bw), which differs from Bw only at world offset 0xfdc8; M.fly.on is at 0x60 .. 0x63 and M.fly.len at
     0x668 .. 0x66f. check_inflight_retry_m B1 frame = Some _ gives truth (M_fly_on B1), so M_fly_on Bw <> 0 and
     the premise gives M_fly_len B1 = M_fly_len Bw <= 1514.
   - (forall s, 0 <= s < g_ncmd Bw -> Cmd_st Bw s = PENDING -> Cmd_len Bw s <= SPEC_CMD_MAX), check_latest_sent_cg.v's
     run invariant (its bcmp reads t->len bytes of g_cmd[s].bytes). io_send reaches check_latest_sent on the DATA path
     with g_raw = 0 and no keepalive (0x8329c) and stores no g_cmd byte and no g_ncmd before it, so it carries it on
     its own Bw. The world the callee is handed is B5 = set_g_last_counter (set_M_host_counter B4 send) send, with
     B4 = B3 = B1 = B0 (check_inflight_new and check_latest_frame: Bw' = Bw), which differs from Bw only at world
     offsets 0xfdc8 (g_fail_next), 0x54 .. 0x57 (M.host_counter) and 0xfdd0 .. 0xfdd3 (g_last_counter). The invariant
     reads g_ncmd (0xfdd8 .. 0xfddb) and, for each s, the bytes A_Cmd_st s .. + 3 and A_Cmd_len s = 0x4dc8 + 40 s
     (+ 36); for no integer s is one of them a written offset (decided over every s with A_Cmd_st s < W_LEN), so the
     invariant at B5 is the invariant at Bw.
   io_send's own code needs no bound the model does not give: the one frame byte it reads (body[0] = p + 30, when
   body_len = 1) lies in [p, p + len) (body_len = numbytes - 16 = 1 gives len >= numbytes + 14 = 31); g_cmd[s].len
   (the command count loop) is read only for t = tagged_of's result TB_g_cmd + 40 s, where the model is None unless
   s < CMDS_MAX, so it lies in g_cmd's payload; __asan_memcpy copies min (len, 1514) bytes to M + 120 .. M + 1634
   < M + 1648, inside M's payload.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 876 code bytes are equal in both files), 219
   words:
     0x82ffc - 0x83020 sp = sp - 160; ra, s0 .. s7 at sp + 152 .. sp + 88, loaded back at 0x8331c - 0x8333c
                      (sp = sp + 160 at 0x83340, return at 0x83344). No side-stack frame, no frame pointer. Own frame
                      cells: sp + 4 (int display: the 4-byte store of 0 at 0x83178, then check_latest_sent's),
                      sp + 8 .. sp + 88 (struct spec_frame f, 80 bytes, written by spec_read_frame); sp + 0 .. sp + 4
                      unused. s0 = len, s1 = p (0x83024 - 0x83028).
     0x8302c - 0x83038 s4 = the 8-byte load at the GOT word 0xa3cf0, then at the cell 0xac678 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     0x8303c - 0x83040 s3 = the 1-byte load of g_fail_next (0x5deda0 = TB_g_fail_next, no instrumented check); the
                      1-byte store of 0 there (:826-829).
     0x83044 - 0x83050 a0 = p, a1 = len, a2 = sp + 8; call of spec_read_frame (0x839c0 = transportb_sigma
                      TB_spec_read_frame) at 0x83050, return address 0x83054 (:830); its result is not read.
     0x83054 - 0x83060 a0 = p, a1 = len, a2 = sp + 8; call of check_sent_frame (0x84080) at 0x83060, return address
                      0x83064 (:831).
     0x83064 - 0x83078 a0 = f.cmd (the 1-byte load at sp + 48); above 0xe1 (signed) goes to 0x8309c; 0 goes to
                      0x830cc; not 0xa0 (SPEC_CMD_ACK) goes to 0x83310 (:895-896).
     0x8307c - 0x83098 ACK (:833-836): a2 = GOT.acks (the 4-byte load at 0x5e502c = GOT + 204, no instrumented check);
                      a1 = a2 + 1 (32-bit, sign-extended); a1 < a2 (signed: GOT.acks = INT_MAX) goes to the trap word
                      (0x83088); the store back; a0 = sp + 8; call of check_ack_frame (0x843d4) at 0x83094, return
                      address 0x83098; to 0x830c0.
     0x8309c - 0x830a8 0xe2 goes to 0x830cc; not 0xe3 goes to 0x83310.
     0x830ac - 0x830bc E3 (:891-893): GOT.e3 (0x5e5028 = GOT + 200) + 1, the same overflow branch to the trap word
                      (0x830b8), stored back.
     0x830c0 - 0x830c8 a0 = sp + 8; call of check_latest_control (0x84490) at 0x830c4, return address 0x830c8; to
                      0x83310.
     0x830cc - 0x830d0 E2 / DATA (:838-840): f.retry (the 2-byte load at sp + 38) = 0 goes to 0x83108.
     0x830d4 - 0x83104 retry (:841-843): a0 = p, a1 = len, a2 = sp + 8; call of check_inflight_retry (0x844fc) at
                      0x830e0, return address 0x830e4; M.fly.retries (M + 108, M = 0x5dede0 = TB_M) + 1 (the low 32
                      bits stored back); the 8-byte store of g_now (0x5ded80) at M + 112 (M.fly.sent); to 0x83310.
     0x83108 - 0x83144 E2 (:846-852): cmd <> 0xe2 goes to 0x83148; call of check_state_wake (0x84628) at 0x83110,
                      return address 0x83114 (no argument); a0 = sp + 8, call of check_latest_control at 0x83118,
                      return address 0x8311c; GOT.e2 (0x5e5024 = GOT + 196) + 1, the overflow branch to the trap word
                      (0x83128), stored back; the 4-byte store of f.send (sp + 40) at g_last_counter (0x5dedc0);
                      s3 & 1 = 0 goes to 0x832c0 (the frame in flight); else 0x83310.
     0x83148 - 0x83174, 0x83348 - 0x83354 DATA (:853-856): s5 = 0 when f.body_len (sp + 64) <> 1; else a0 = f.body
                      (sp + 56), 0 goes to the trap word (0x83158); the instrumented check of the 1-byte load at
                      f.body (the shadow byte k (signed) at (a >> 3) + 0x7fff8000; k = 0 goes on; else (a & 7) < k
                      goes on; else the error path); body[0] <> 0 gives s5 = 0; else s5 = (f.ncmds (sp + 49) = 1).
     0x83178 - 0x8317c the 4-byte store of 0 at sp + 4; call of check_inflight_new (0x84654) at 0x8317c, return
                      address 0x83180 (no argument).
     0x83180 - 0x83194 g_raw (0x5ded60, 4-byte load) <> 0 or s5 <> 0 goes to 0x83214 (s2 = f.ncmds, :863-865);
                      f.body_len = 0 goes to 0x8321c with s2 = 0.
     0x83198 - 0x83204 the command count loop (:858-862): at = s7 = 0, cmds = s2 = 0; each round: a0 = f.body + at
                      (f.body loaded again from sp + 56); a0 below f.body (unsigned: the sum wraps) goes to the trap
                      word (0x831a8), and so does (f.body <> 0) = (f.body + at = 0) (0x831b8); a1 = body_len - at;
                      call of tagged_of (0x846a0 = transportb_sigma TB_tagged_of) at 0x831c0, return address 0x831c4;
                      its result t = 0 gives step = body_len - at (0x831ec); else t & 3 <> 0 goes to the trap word
                      (0x831cc), the check of the 1-byte load at t + 36 (as above; slow path 0x83208), step = t->len
                      (the byte at t + 36); at = at + step, cmds = cmds + 1 (32-bit, sign-extended); at < body_len
                      (unsigned; body_len loaded again) goes round again; else to 0x83220.
     0x83220 - 0x83228 a0 = sp + 8, a1 = s2 (cmds); call of check_latest_frame (0x8478c) at 0x83228, return address
                      0x8322c (:866).
     0x8322c - 0x83250 s2 = M; the 4-byte stores of f.send at M + 84 (M.host_counter) and at g_last_counter
                      (:867-868); g_raw (loaded again) = 0 and s5 <> 0 goes on (keepalive, :869-873); else 0x8328c.
     0x83254 - 0x83288 call of check_keepalive_due (0x84868) at 0x83254, return address 0x83258 (no argument);
                      a1 = g_cfg.keepalive_ms (the 4-byte unsigned load at g_cfg + 24 = 0x5ded18) * 1000;
                      a2 = M.next_ka (M + 48) + a1, stored at M + 48; g_now < a2 (unsigned) goes to 0x832c0; else
                      g_now + a1 stored at M + 48; to 0x832c0.
     0x8328c - 0x832bc g_raw <> 0 goes to 0x832c0; a0 = f.body (sp + 56), a1 = f.body_len (sp + 64), a2 = sp + 4;
                      call of check_latest_sent (0x848bc) at 0x8329c, return address 0x832a0 (:875); the 4-byte load
                      at sp + 4 (display) = 0 goes to 0x832c0; call of check_latest_display (0x84bd0) at 0x832a8,
                      return address 0x832ac (no argument); the 8-byte store of g_now at M + 64 (M.last_display), the
                      4-byte store of 1 at M + 72 (M.display_sent) (:876-879).
     0x832c0 - 0x8330c the frame in flight (:883-889): the 8-byte store of g_now at M + 112 (M.fly.sent), the 4-byte
                      store of 1 at M + 96 (M.fly.on), the 1-byte store of f.cmd (sp + 48) at M + 100 (M.fly.cmd), the
                      4-byte store of f.send at M + 104 (M.fly.counter), the 4-byte store of 0 at M + 108
                      (M.fly.retries); s0 = min (len, 1514), stored (8 bytes) at M + 1640 (M.fly.len); a0 = M + 120
                      (M.fly.frame, 0x5dee58), a1 = p, a2 = s0; call of checked_memcpy (__asan_memcpy, 0x523ec =
                      transportb_sigma TB___asan_memcpy) at 0x8330c, return address 0x83310.
     0x83310 - 0x83344 a0 = -5 when s3 & 1 = 1, else 0 (`slli 63; srai 63; andi -5`, :898); ra, s0 .. s7 loaded back,
                      sp = sp + 160, return. a1 .. a7 at the return are not stated.
     0x83358          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path.
     0x8335c - 0x83364 the slow path of the check of body[0] and its error call.
   No tail jump: every call is a jal with link, every j is inside the function, and the function ends with ret.
   The model and the code: the dispatch and every test is io_send_m's (the cmd byte, sf_retry, truth fail, ka,
   g_raw, the count loop's tagged_of_m and step, nk <=? g_now, truth disp), read through tw_at and the struct, whose
   fields are rf frame's (spec_read_frame's post at len = length frame, spec_read_frame_cg.v srf_f_rf); each store is
   the model's set_* (put of the low bytes); the code tests only bit 0 of g_fail_next (0x83138, 0x83310), which is
   truth fail under g_fail_next Bw <= 1. The model's None cases are the callees' aborts (their contracts' model
   premises, which io_send_m's branch supplies), GOT.acks / e2 / e3 at INT_MAX (the code goes to the trap word), a
   command of length 0 in the count loop (the code loops for ever), tagged_of's (serial >= CMDS_MAX below g_ncmd),
   and a frame whose parse code is not 0 (check_sent_frame traps on it).
   Trap path (the unimp word at 0x83358, from 7 branches) and the fact that refutes each:
     0x83088, 0x830b8, 0x83128 (GOT.acks / GOT.e3 / GOT.e2 = INT_MAX): int_inc is None there, so the model premise
       rules them out.
     0x83158 (f.body = 0 on the DATA path with body_len = 1): check_sent_frame_m B0 frame = Some _ (io_send_m) gives
       sf_code (rf frame) = SPEC_OK, so the struct's body pointer is TContract.sf_ptr p (rf frame) (sf_body _) = p + 30
       (spec_read_frame's X, kept through check_sent_frame, whose written range is empty), and 0 < p.
     0x831a8 (f.body + at wraps): at < body_len and p + 30 + body_len <= p + len (rf: body_len = numbytes - 16 <=
       len - 30), and trans_src_ok places [p, p + len) below 2 ^ 64 (decode_rd_ok: p + len <= 2 ^ 63; a heap block
       below alloc_ceiling).
     0x831b8 ((f.body <> 0) = (f.body + at = 0)): f.body = p + 30 <> 0 and, by the bound above, f.body + at <> 0.
     0x831cc (t & 3 <> 0): t <> 0 is tagged_of's result TB_g_cmd + 40 s (tagged_of_cg.v tagged_of_res), and
       TB_g_cmd = 0x5e5080 is a multiple of 4.
   Error paths (2 calls of __asan_report_load1, 0x59504) and the facts that rule them out:
     0x83364 (body[0] = p + 30, body_len = 1): the byte lies in [p, p + len) (len >= 31), which trans_src_ok marks
       usable (a heap block: AR's block shadow; else decode_rd_ok's range_addressable), at the call state of each
       earlier call and after it (DgnTransportBCg.v trans_src_ok_kept; for a frame in g_s, spec_read_frame's gx_kept
       and the zero shadow of g_s, trans_src_ok's G case).
     0x83210 (t + 36 = g_cmd + 40 s + 36): s < CMDS_MAX (tagged_of_m), inside g_cmd's payload, whose shadow is 0
       (trans_iosend_cells).
   Callee texts assumed (pc order), and what supplies each premise of each:
     spec_read_frame as spec_read_frame_cg.v transport_spec_read_frame_cg at transportb_sigma TB_spec_read_frame (call
       at 0x83050; G form, the same journal; its post, TransportGCg.v transport_cg_post_out [(sp + 8, 80)], is used as
       written): b = p (0 < p), len = length frame (0 <= len <= length frame), garr8 of TW.zs frame (= map DSpec.bz
       frame); trans_src_ok and decode_off_win (SRF_STK <= IOSEND_STK - 160) of [p, p + len): entry premises; the
       frame apart from srf_wr (sp + 8): the frame lies outside io_send's window (decode_off_win at IOSEND_STK), the
       struct inside it; fp = sp + 8: fp mod 8 = 0 (sp mod 16 = 0), transport_twr_ok_g (window bytes above the call's
       ESTACK window, present by the journal), decode_rd_ok (CanKit.v can_stack_addressable / can_stack_hull: the
       machine stack's shadow is 0 at every AR state, YG0n.v zero_shadow_ranges' first row [ly_stk_lo, ly_stk_hi);
       amem_range: a stack range), decode_off_win (sp + 8 >= sp - 160), not in G (the stack lies above G). Its X:
       a0 = the code (not read), the 80 bytes at sp + 8 = TContract.sf_bytes p (rf frame), and gx_kept (G as it was,
       so the world relation at B0 = set_g_fail_next Bw 0 holds after it).
     check_sent_frame as check_sent_frame_cg.v transport_check_sent_frame_cg at transportb_sigma TB_check_sent_frame
       (call at 0x83060; donor form, through gx_call_cg: gx_ok, gx_noerrno): a0 = p (0 < p), a1 = len, a2 = sp + 8;
       its window CSF_STK below sp - 160 (IOSEND_STK); garr8 of the frame, trans_src_ok and decode_off_win of
       [p, p + len): kept through spec_read_frame's call (the frame outside srf_wr and outside its window;
       trans_src_ok_kept; a frame in g_s by its gx_kept); trans_sframe_at W memc (sp + 8) p (rf frame): spec_read_frame's
       X (sf_bytes' fields are trans_sframe_at's; 0 < sp + 8, sp + 8 mod 8 = 0); trans_src_ok of [sp + 8, sp + 88):
       the machine-stack case (ly_stk_lo lyc <= sp + 8, sp + 88 <= ly_stk_hi lyc: the journal's window lies in the
       stack) with decode_rd_ok as above; decode_off_win of it: sp + 8 >= sp - 160; trans_rom_view_rd: the entry
       premise, kept (above); tw_at at B0; check_sent_frame_m B0 frame = Some (B1, tt): io_send_m.
     check_ack_frame as check_ack_frame_cg.v transport_check_ack_frame_cg (a leaf: transport_leaf_at, WR = []; call at
       0x83094, through gx_call_leaf and the leaf bridge DgnTransportBLeafb.v): fp = sp + 8 (0 < fp, fp mod 8 = 0);
       bytes_at of f + 36, f + 56, f + 30 (the struct's ack, body_len, retry: rf frame's); addressable of them (the
       stack's zero shadow, CanKit, decode_leafb_addressable); asan_cells (transport_cells, decode_leafb_asan_cells);
       app_mem of the stack (decode_leafb_app_stack); off_stk G (the stack lies above G); the RNG ranges (its window,
       the two cells, the fields and their shadow bytes, g_rx_send: visible G bytes); tw_at at csw_view (G's payloads
       are image bytes); check_ack_frame_m (set_GOT_acks B1 a) frame: io_send_m.
     check_latest_control as check_latest_control_cg.v (leaf; calls at 0x830c4 and 0x83118): fp = sp + 8, bytes_at /
       addressable / RNG of f + 32 (send), RNG of M.host_counter; check_latest_control_m at the world after
       check_ack_frame (ACK), after GOT.e3++ (E3), after check_state_wake (E2).
     check_inflight_retry as check_inflight_retry_cg.v transport_check_inflight_retry_cg at transportb_sigma
       TB_check_inflight_retry (call at 0x830e0; donor form, gx_call_cg): the frame and struct facts as for
       check_sent_frame (CIR_STK <= IOSEND_STK - 160), tw_at at B1, check_inflight_retry_m B1 frame, and
       M_fly_len B1 <= 1514 from this statement's guarded run-invariant premise, whose guard that model call gives
       (above).
     check_state_wake as check_state_wake_cg.v (leaf; call at 0x83110; no argument): tw_at at B1, check_state_wake_m
       B1, RNG of M.foreign. (Every leaf's RNG row of a world global is a G payload byte, visible at every memory:
       TransportGCg.v gx_rw_vis with lib/B/Prog/TransportGRwB.v.)
     check_inflight_new as check_inflight_new_cg.v (leaf; call at 0x8317c; no argument): tw_at at B1,
       check_inflight_new_m B1, RNG of M.state, M.fly.on, g_now, M.backoff_until.
     tagged_of as tagged_of_cg.v transport_tagged_of_cg (leaf; call at 0x831c0, once per round of the count loop):
       a0 = p + 30 + at (0 < it), a1 = body_len - at (0 <= it < 2 ^ 64); bytes_at of skipn at body (body = the frame
       bytes from p + 30 on; the leaf bridge reads them from garr8 of the frame, which no store of the loop reaches);
       tw_at at csw_view of the call memory (the world B3 of the loop); tagged_of_m B3 (skipn at body)
       (body_len - at) = Some (B3, t): the round's let* in io_send_m's cmds_loop; asan_cells; when
       3 <= body_len - at, the 3 bytes at p + 30 + at addressable (trans_src_ok: a heap block, AR's shadow law; else
       decode_rd_ok) and off its frame (decode_off_win); the RNG rows (its window, the two cells, g_ncmd (a visible G
       byte), the 3 bytes and their shadow bytes). It returns t = 0 for None, TB_g_cmd + 40 s for Some s.
     check_latest_frame as check_latest_frame_cg.v (leaf; call at 0x83228): fp = sp + 8, a1 = bv_swrap 32 cmds with
       0 <= cmds < 2 ^ 32 (u32 in cmds_loop; a zero-extended byte for f.ncmds), bytes_at / addressable / RNG of f + 32,
       f + 41, f + 56, RNG of g_cfg.max_body, g_cfg.max_cmds, g_raw, M.host_counter; check_latest_frame_m B3 frame
       cmds.
     check_keepalive_due as check_keepalive_due_cg.v (leaf; call at 0x83254; no argument): tw_at at B5,
       check_keepalive_due_m B5, RNG of M.state, M.fly.on, g_now, M.backoff_until, M.next_ka.
     check_latest_sent as check_latest_sent_cg.v transport_check_latest_sent_cg at transportb_sigma
       TB_check_latest_sent (call at 0x8329c; G form, the same journal; its post, TransportGCg.v transport_cg_post_out
       [(dp, 4)], is used as written): bp = f.body = p + 30 (0 < bp), len = body_len, body = firstn body_len
       (skipn 30 frame) (length body_len); garr8, trans_src_ok (trans_src_ok_sub), decode_off_win
       (decode_off_win_sub; CLS_STK = IOSEND_STK - 160) of the body: sub-ranges of the frame's; the body apart from
       cls_wr (sp + 4): the body is outside io_send's window and outside g_cmd, g_q, g_nq (iosend_frame_at);
       dp = sp + 4: dp mod 4 = 0, transport_twr_ok_g (a window byte above the call's ESTACK window), decode_rd_ok
       (CanKit), decode_off_win (dp >= sp - 160), not in G (the stack lies above G); trans_rom_view_rd at the call
       memory (above); tw_at at B5, check_latest_sent_m B5 body body_len = Some (Bs, disp): io_send_m; the
       command-length invariant at B5: this statement's premise (above).
     check_latest_display as check_latest_display_cg.v (leaf; call at 0x832a8; no argument): tw_at at Bs,
       check_latest_display_m Bs, RNG of M.display_sent, M.last_display, g_now, g_cfg.display_gap_us.
     __asan_memcpy as aintrin_realizes .. OCpy (transportb_sigma TB___asan_memcpy), call at 0x8330c, through
       gx_intrin_at: d = M + 120, n = min (len, 1514) < 2 ^ 32, bytes of G (transport_twr_ok_g's G case);
       range_addressable of [M + 120, M + 120 + n): M's zero shadow; shadow_hull_vis: M's zero shadow, and for
       n = 1513 or 1514 the six guard shadow bytes 0x800b3e8a .. 0x800b3e8f (trans_iosend_cells); the source
       [p, p + n) inside the frame: src_ok, range_addressable and shadow_hull_vis from trans_src_ok, outside the
       call's ESTACK window (decode_off_win), apart from [M + 120, M + 120 + n) (iosend_frame_at).
   A donor callee keeps every byte of G (gx_call_cg: gx_ok and gx_noerrno), spec_read_frame keeps G (its X's
   gx_kept), and a leaf keeps every byte outside its ESTACK window, so the world relation after each is the one it was
   handed.
   Stack: 160 bytes of its own; every call runs from sp - 160: spec_read_frame SRF_STK, check_sent_frame CSF_STK,
   check_inflight_retry CIR_STK, check_latest_sent CLS_STK = 160 + 2 * ESTACK, the leaves and __asan_memcpy ESTACK:
   IOSEND_STK = 160 + CLS_STK.

   The callers (each through g_s.io.send, the jalr's return address): send_control 0x870fc (return 0x87100):
   a0 = s->io.ctx (the 8-byte load at g_s + 64), a1 = s7 = s9 + 32 (0x87064), its frame buffer inside the class-2
   side-stack frame it takes with __asan_stack_malloc_2 at 0x86f4c, a2 = s5 = diginet_frame_build's result (0x87084,
   the frame length); diginet_session_tick 0x894c0 (return 0x894c4): a0 = s->io.ctx, a1 = g_s + 216
   (g_s.inflight_frame, 0x893f4), a2 = s->inflight_len (the 8-byte load at g_s + 1736, 0x894b0); send_data 0x89ff8
   (return 0x89ffc): a0 = s->io.ctx, a1 = s7 = g_s + 216 (0x89edc), a2 = diginet_frame_build's result (0x89f00).
   Each supplies the G journal of its own walk, the world relation, the frame facts (send_control's buffer:
   decode_in_fake, outside G; g_s.inflight_frame: inG, inside g_s's payload) and the two run invariants.

   Against image A's statement (lib/A/Prog/io_send_cg.v): the same premises and post, at image B's names (TMAP_B,
   timg_B, TB_*, transportb_sigma, lib/B/Prog/DgnTransportBCg.v, lib/B/Prog/m_set_cg.v twb_fld). What image B's code
   forces: (1) spec_read_frame and tagged_of are called, not inlined: io_send's own code reads no frame byte but
   body[0], the struct is filled by spec_read_frame (whose callee __asan_memset is no longer io_send's), and the count
   loop reads only t->len itself; so the holds statement takes the contracts of spec_read_frame and of the leaf
   tagged_of in place of __asan_memset's. (2) Seven branches to the unimp word (the GOT.acks / e2 / e3 increments'
   overflow checks, where image A's code wraps; the body pointer checks; t's alignment check), each refuted by the
   model premise, the struct's fields or trans_src_ok, so no contract premise is added. (3) The holds statement takes
   trans_ro_rd_unowned B and trans_rom_no_errno B, which image A's does not: on image B the two callees that read
   TRANS_RO_RD bytes through trans_rom_view_rd, check_sent_frame (HOST) and check_latest_sent (the constant-pool word,
   which image A's check_latest_sent does not read), are entered after the call of spec_read_frame, whose post keeps an
   image byte outside G only when it is neither an owned static nor errno (TransportGCg.v acall_kept_g); on image A
   the one such callee, check_sent_frame, follows only the intrinsic __asan_memset, which keeps every byte outside its
   destination and its ESTACK window. (4) io_send stores 0 at its int display (sp + 4) before check_inflight_new on
   the DATA path (its own frame). *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBList.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  spec_read_frame_cg check_sent_frame_cg check_inflight_retry_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  check_ack_frame_cg check_latest_control_cg check_state_wake_cg check_inflight_new_cg tagged_of_cg
  check_latest_frame_cg check_keepalive_due_cg check_latest_display_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_ack_frame_cg.
Module LLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_control_cg.
Module LSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_cg.
Module LIN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_new_cg.
Module LTO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_cg.
Module LLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_frame_cg.
Module LKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_keepalive_due_cg.
Module LLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_display_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* io_send's entry: the value the model's call of io_send tests the session's send pointer against, and the
   listing's offset of io_send from the entry function. *)
Lemma io_send_at :
  TI.ti_io_send timg_B = 0x82ffc /\ TI.ti_io_send timg_B = transportb_text + DgnTransportBList.AF_io_send.
Proof. split; reflexivity. Qed.

(* io_send's frame (`sp = sp - 160` at its entry; no realignment). Every call runs from sp - 160: spec_read_frame
   (SRF_STK), check_sent_frame (CSF_STK), check_inflight_retry (CIR_STK), check_latest_sent (CLS_STK), the leaves and
   __asan_memcpy (ESTACK). *)
Definition IOSEND_FRAME : Z := 160.
Definition IOSEND_STK : Z :=
  IOSEND_FRAME + Z.max (Z.max (Z.max ESTACK SRF_STK) (Z.max CSF_STK CIR_STK)) CLS_STK.
Lemma iosend_stk_eq : IOSEND_STK = IOSEND_FRAME + CLS_STK.
Proof. reflexivity. Qed.
(* No allocator event: neither io_send nor a callee calls malloc or free or takes a side-stack frame. *)
Definition IOSEND_EV : Z := 0.

(* Where the frame lies: every byte outside G (send_control's buffer in its side-stack frame), or the whole range
   inside g_s's payload (g_s.inflight_frame). No byte the call stores lies in g_s. *)
Definition iosend_frame_at (p n : Z) : Prop :=
  (forall x, p <= x < p + n -> ~ inG TG.G_HARNESS_B x) \/ (TB_g_s <= p /\ p + n <= TB_g_s + TW.SZ_g_s).

(* The bytes some path of the call stores into G, field by field, for a frame of n bytes: g_fail_next; GOT.e2,
   GOT.e3, GOT.acks; g_last_counter; M.host_counter, M.next_ka, M.last_display, M.display_sent; M.fly.on, .cmd,
   .counter, .retries, .sent, .len and the first min (n, 1514) bytes of M.fly.frame; and check_latest_sent's: the st
   field of a command (g_cmd[s], s < CMDS_MAX), g_q's payload, g_nq. Each path stores a subset (io_send_m). No other
   callee stores outside its own window; spec_read_frame's struct at sp + 8 and check_latest_sent's int at sp + 4 lie
   in io_send's own window. *)
Definition iosend_wr (n a : Z) : Prop :=
  twb_fld TW.OFF_g_fail_next TB_g_fail_next TW.OFF_g_fail_next 1 a \/
  twb_fld TW.OFF_GOT TB_GOT TW.A_GOT_e2 4 a \/
  twb_fld TW.OFF_GOT TB_GOT TW.A_GOT_e3 4 a \/
  twb_fld TW.OFF_GOT TB_GOT TW.A_GOT_acks 4 a \/
  twb_fld TW.OFF_g_last_counter TB_g_last_counter TW.OFF_g_last_counter 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_host_counter 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_next_ka 8 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_last_display 8 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_display_sent 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_fly_on 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_fly_cmd 1 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_fly_counter 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_fly_retries 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_fly_sent 8 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_fly_len 8 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_fly_frame (Z.min n TC.SPEC_MAX_FRAME) a \/
  (exists s, 0 <= s < TC.CMDS_MAX /\ twb_fld TW.OFF_g_cmd TB_g_cmd (TW.A_Cmd_st s) 4 a) \/
  twb_fld TW.OFF_g_q TB_g_q TW.OFF_g_q TW.SZ_g_q a \/
  twb_fld TW.OFF_g_nq TB_g_nq TW.OFF_g_nq TW.SZ_g_nq a.

(* The shadow facts of the record (lib/B/YF0m.v Tfib_zero_shadow and Tfib_const_shadow rows) io_send's own code
   needs: g_cmd's payload (40960 bytes, whole granules) has shadow 0 (the instrumented check of g_cmd[serial].len in
   the command count loop); M's payload (1648 bytes, 206 whole granules) has shadow 0 (__asan_memcpy's destination
   check of [M + 120, M + 120 + n)), and the six guard granules after it, which share the aligned group of 8 shadow
   bytes of M's last payload bytes, are 0xf9 (that copy's shadow_hull_vis for n = 1513 or 1514). *)
Definition trans_iosend_cells (B : asyms) : Prop :=
  decode_zshadow_at B TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd) /\
  decode_zshadow_at B TB_M (TB_M + TW.SZ_M) /\
  forall ly,
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M + 32))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M + 40))) 0xf9) (as_const B ly).
Lemma trans_iosend_cells_rows :
  map (fun j => BCells.shadow_addr (TB_M + TW.SZ_M + 8 * j)) [0; 1; 2; 3; 4; 5] =
  [0x800b3e8a; 0x800b3e8b; 0x800b3e8c; 0x800b3e8d; 0x800b3e8e; 0x800b3e8f] /\
  BCells.shadow_addr TB_M = 0x800b3dbc /\ BCells.shadow_addr TB_g_cmd = 0x800b4a10.
Proof. split; [|split]; reflexivity. Qed.

Section iosend. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   iosend_wr (length frame), no meter charge, and X: a0 = r (sign-extended) and the world relation at the model's
   world Bw'. *)
Definition transport_io_send_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (n : Z) (Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs IOSEND_STK IOSEND_EV 0 (iosend_wr n)
    (fun regs2 W2 mem2 => YK11.getr regs2 10 = w64 r /\ tw_at TMAP_B (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_io_send_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p r : Z) (frame : list byte) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
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
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TC.io_send_m timg_B Bw frame = Some (Bw', r) ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    st_nev S + k + IOSEND_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_io_send_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (Z.of_nat (length frame)) Bw' r).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of g_cmd
   and of M and M's guard granules, the two read-only facts of the record (they keep the TRANS_RO_RD bytes visible
   through spec_read_frame's and check_sent_frame's posts), the allocator and meter laws, G inside the image, outside
   the allocator's statics and outside errno (a donor callee keeps G: gx_call_cg), and the contracts of the thirteen
   callees (pc order of their first call) give the contract at io_send's entry. *)
Definition transport_io_send_cg_holds_stmt : Prop :=
  transport_cells B -> trans_iosend_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS_B -> gx_noerrno B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_spec_read_frame_cg fx' rc B MT (transportb_sigma TB_spec_read_frame)) ->
  (forall fx' : YK11.FPState, @transport_check_sent_frame_cg fx' rc B MT (transportb_sigma TB_check_sent_frame)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LAF.transport_check_ack_frame_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLC.transport_check_latest_control_cg) fx') ->
  (forall fx' : YK11.FPState,
     @transport_check_inflight_retry_cg fx' rc B MT (transportb_sigma TB_check_inflight_retry)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSW.transport_check_state_wake_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIN.transport_check_inflight_new_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LTO.transport_tagged_of_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLF.transport_check_latest_frame_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LKD.transport_check_keepalive_due_cg) fx') ->
  (forall fx' : YK11.FPState,
     @transport_check_latest_sent_cg fx' rc B MT (transportb_sigma TB_check_latest_sent)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLD.transport_check_latest_display_cg) fx') ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  transport_io_send_cg (TI.ti_io_send timg_B).
End iosend.
