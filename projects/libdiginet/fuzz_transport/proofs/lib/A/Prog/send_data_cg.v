(* send_data_cg: the ASan walk contract of send_data (transport/src/diginet_session.c:388-401, with inflight_start
   (:111-117) and send_raw (:88-94) inlined; model lib/TModel/TSess.v send_data_m, lib/TModel/TSess0.v
   inflight_start_m) on fuzz_transport.asan (e89be137db17) at 0x8a12c = transport_sigma TS_send_data, size 988, as
   STATEMENTS only (no proof). It stores into g_s, a harness global (host_counter, the inflight fields, the stats
   counters, and, through diginet_frame_build, g_s.inflight_frame), takes a class-0 side-stack frame for its struct
   diginet_header h, calls __asan_memset, diginet_frame_build (a G-form callee) and io_send through the session's
   send pointer, so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over
   G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v
   transport_cg_post (acall_kept_g over G_HARNESS). The G form and the side-stack frame are session_lost_cg.v's; the
   input range is diginet_frame_build_cg.v's.

   The contract. a0 = s = &g_s = 0x5df9c0 (TWorldA.v TA_g_s), a1 = bodyp, a2 = the length of the bytes body at bodyp
   (diginet_session_tick's body[] after take, or its keepalive byte ka), a3 = ncmds (unsigned, sign-extended from
   bit 31), a4 = now (uint64_t). The body lies where DgnTransportCg.v trans_src_ok places it (in diginet_session_tick's
   class-5 side-stack frame for both calls), outside this call's stack window and outside G; bodyp itself is not a byte
   of G even when the body is empty, which keeps it apart from out = s + 216 for diginet_frame_build's separation
   premise at every length (at length 0 the range premises say nothing of bodyp). The memory relates to
   the world Bw by image A's world relation (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview),
   g_fail_next Bw <= 1, and send_data_m timg_A TF Bw body ncmds now = Some (Bw', r). The read-only bytes io_send's
   callees read are the image's (trans_rom_view_rd). Class 0 of the side stack has a free frame (its own) and class 2
   has one (diginet_body_check's inside diginet_frame_build). The function returns to ra with a0 = r (sign-extended),
   the callee-saved registers kept, no allocator event and no meter charge (its side-stack frame changes the state's
   st_fs only: ameter_fs_laws), its side-stack frame released (the caller's frames exactly), the caller's blocks
   exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or above alloc_ceiling outside the call's stack window
   [sp - SENDDATA_STK, sp), the image bytes outside G, the owned statics and errno, the caller's block and frame bytes
   outside senddata_wr), the world relation at Bw', and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/send_data_c.v): a0 = W_BASE_PLAIN + OFF_g_s
   -> a0 = TA_g_s; a1 = bodyp, a2 = length body, a3 = bv_swrap 32 ncmds, a4 = now, 0 <= ncmds < 2 ^ 32 and
   0 <= now < 2 ^ 64 kept; bytes_at m bodyp body -> garr8 of the view and trans_src_ok (diginet_frame_build reads
   the body through its own statement's trans_src_ok premise, which send_data passes on); arg_blk sp FRAME bodyp len ->
   0 < bodyp (kept), decode_off_win at SENDDATA_STK (off_window), the range apart from G (off_world), and p + n < 2 ^ 64
   from trans_src_ok (decode_rd_ok's q + n <= 2 ^ 63, or a heap block's amem_range); wmem -> tw_at; g_fail_next B <= 1
   kept (io_send's statement asks it; the code neither reads nor writes g_fail_next); send_data_m verbatim at timg_A,
   with TF free as in the plain contract (send_raw_m does not read it); stk, lo + FRAME <= sp, sp mod 16 and
   w_off_stack -> the journal's window premises; mem_inv is dropped. The post: munch -> acall_kept_g with the written
   range senddata_wr; wmono / stk / mem_inv -> the journal; wmem -> tw_at at Bw'; g_fail_next B' <= 1 kept in X (from
   the model, as lib/Prog/T/send_data.v gets it: the stores before the call leave g_fail_next alone (GF8),
   lib/TModel/TIoSendFail.v io_send_m_fail_next gives 0 after io_send, and the store of tx_frames leaves it alone; on
   the n < 0 path only host_counter changes).

   Premises the plain contract does not have:
   - count_cid 0 (frames Sc) < fs_frames 0 (its own class-0 frame) and count_cid 2 (frames Sc) < fs_frames 2
     (diginet_body_check's class-2 frame inside diginet_frame_build, whose statement asks it at its call state, where
     the frames are the own class-0 frame :: frames Sc, so the class-2 count is unchanged). With the first
     __asan_stack_malloc_0 returns a frame (astack_malloc_realizes), so the real-stack arm is not taken and h lies in
     the own side-stack frame, where diginet_frame_build's header premise decode_in_fake places it.
   - (not new, the translations above: trans_src_ok of the body and the body apart from G, from bytes_at and
     arg_blk's off_world; diginet_frame_build's out is g_s.inflight_frame, a range of G, and its statement asks the
     body apart from out.)
   - trans_rom_view_rd W memc: io_send's own premise (check_sent_frame's bcmp of f->src with HOST), taken at
     send_data's entry memory as session_lost_cg.v takes notice's. It still holds at the call at 0x8a3a4: before it,
     send_data stores only into its own machine frame, its side-stack frame, that frame's shadow bytes and g_s; the
     stack malloc's acall_kept keeps every TRANS_RO_RD byte (trans_ro_rd_scoped, from trans_ro_rd_unowned and
     trans_rom_no_errno), __asan_memset keeps every byte outside its destination and ESTACK window, and
     diginet_frame_build's acall_kept_g keeps the image bytes outside G that are not owned statics or errno.
   - in the holds statement: trans_senddata_cells (g_s's zero shadow), the side-stack laws, and trans_g_unowned,
     trans_g_no_errno, trans_ro_rd_unowned and trans_rom_no_errno: they carry the body's trans_src_ok across the
     stack malloc (DgnTransportCg.v trans_src_ok_inner with the body's bytes kept by its acall_kept and
     trans_rd_ok_sh, with these facts for a body in G or TRANS_RO_RD; the fresh frame is apart from the body's
     placement: trans_src_ok_disj_own), the TRANS_RO_RD bytes (above), and G (TransportGCg.v gx_kept_of_acall_kept
     with gx_ok and gx_noerrno, which DgnTransportCg.v G_HARNESS_gx_ok and G_HARNESS_gx_noerrno give from the first
     two).
   Run invariants carried (on its own Bw): (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME and (4)
   every PENDING command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX, both io_send_cg.v's premises. The world
   send_data hands io_send differs from Bw only inside g_s's payload (world offsets [0x670, 0x670 + 18264): the stores
   of host_counter, inflight_frame (diginet_frame_build's n bytes, n <= 1514), inflight_len, inflight,
   inflight_counter, inflight_retries, inflight_sent_us and stats.tx_data); the invariants read M.fly.on (0x60 ..
   0x63), M.fly.len (0x668 .. 0x66f), g_ncmd (0xfdd8 .. 0xfddb) and g_cmd's st and len fields (offsets at or above
   0x4dc8 for every s >= 0), none of them in g_s, so both carry verbatim. diginet_frame_build carries none; the others
   (check_latest_queue's, check_state_data's, take's cfg bound) are not reached from send_data. send_data's own
   accesses are at fixed offsets of g_s (s + 0 .. s + 125, s + 160, s + 212 .. s + 1759, s + 18192 .. s + 18207) and of
   its own frames, and the memset fills 15 bytes of h, so its code needs no bound the model does not give.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   988 code bytes are equal in both files), 247 words:
     0x8a12c - 0x8a168 sp = sp - 160; 0x8a130 stores 8 zero bytes at sp; ra at sp + 152, s0 .. s11 at sp + 144 ..
                      sp + 56, loaded back at 0x8a444 - 0x8a474; s0 = sp + 160 (the entry sp, kept to 0x8a440).
     0x8a16c - 0x8a180 sp = sp & -32 (at most 0x10 below entry - 160); s1 = the realigned sp; the 8-byte stores of now
                      at s1 + 16 and of body_len at s1 + 24 (its own machine frame); s7 = ncmds, s6 = bodyp.
     0x8a184 - 0x8a19c a2 = the 8-byte load of the GOT word 0xa40e8 (it holds 0xaca00), then the 4-byte load of the
                      flag word at 0xaca00; a1 = the 8-byte load of the GOT word 0xa4090 (it holds 0xac9f8), s4 = the
                      8-byte load at 0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s3 = s.
     0x8a1a0 - 0x8a1b0 the flag word = 0 goes to 0x8a1b4 (s2 = 0); transport_cells row 6 gives 1. a0 = 64 and the call
                      of __asan_stack_malloc_0 (frame_alloc_0, 0x3d698 = transport_sigma TS___asan_stack_malloc_0) at
                      0x8a1a8, return address 0x8a1ac: a class-0 side-stack frame (fs_frame_bytes 0 = 64 bytes);
                      s2 = the result.
     0x8a1b8 - 0x8a1d8 s10 = s2; s2 <> 0 goes to 0x8a1dc. The real-stack arm (s2 = 0): s10 = (sp - 64) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s10), then sp = s10. With
                      count_cid 0 (frames Sc) < fs_frames 0 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s10 = s2.
     0x8a1dc          the 8-byte store of frame at s1 + 48 (its own machine frame).
     0x8a1e0          s8 = hp = frame + 32 (struct diginet_header h).
     0x8a1e4 - 0x8a208 the frame header: 0x41b58ab3 at frame, the description string 0x1d87d ("1 32 16 5 h:390": one
                      variable, 16 bytes at frame + 32) at frame + 8, the function's address 0x8a12c at frame + 16.
     0x8a1f0, 0x8a20c - 0x8a234 s11 = (frame >> 3) + 0x7fff8000; the frame's shadow bytes 4..5 = 0 (h's 16 bytes
                      marked usable), 6..7 = 0xf3 (guard bytes), 0..3 = 0xf1 (guard bytes).
     0x8a238 - 0x8a244 a0 = hp, a1 = 0, a2 = 15; the call of __asan_memset (checked_memset, 0x5284c = transport_sigma
                      TS___asan_memset) at 0x8a244, return address 0x8a248: h's bytes 0 .. 14 set to 0 (:390, h =
                      { .cmd = DIGINET_CMD_DATA = 0, ... }).
     0x8a248          the 1-byte store of the low byte of ncmds at hp + 15 (num_commands = u8 ncmds).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on; for an 8-byte access any k <> 0 goes to the error path.
     0x8a24c - 0x8a25c, 0x8a480 - 0x8a48c s9 = s + 160, s5 = its shadow address; the check of the 4-byte load at
                      s + 160.
     0x8a260 - 0x8a270 a0 = the 4-byte signed load at s + 160 (S_host_counter Bw); s7 = a0 + ncmds; the 4-byte stores
                      of the low 32 bits of s7 at s + 160 (:391, set_S_host_counter Bw (u32 (S_host_counter Bw +
                      ncmds))) and at hp + 4 (send_counter: :392's send). The 12 bytes at hp + 4 are now
                      diginet_frame_build_cg.v frame_fb_hdr_bytes send 0 0 0 (u8 ncmds).
     0x8a268, 0x8a274 - 0x8a280, 0x8a494 - 0x8a49c the check of the 4-byte load at s + 20.
     0x8a284 - 0x8a2a4 a7 = the 4-byte signed load at s + 20 (S_cfg_sum_mode); s7 = out = s + 216
                      (g_s.inflight_frame); a0 = out, a1 = 1514, a2 = s + 120 (g_s.desk_mac), a3 = s
                      (g_s.cfg.host_mac), a4 = hp, a5 = bodyp, a6 = body_len (the 8-byte load at s1 + 24).
     0x8a2a8          the call of diginet_frame_build (0x8bcf8 = transport_sigma TS_diginet_frame_build), return
                      address 0x8a2ac (:393).
     0x8a2ac - 0x8a2b0 a2 = n (the result); n < 0 goes to 0x8a3d0 (:395-396).
     0x8a2b4 - 0x8a2c8, 0x8a4e8 the check of the 8-byte store at s + 1736, then the 8-byte store of n there
                      (S_inflight_len, :397).
     0x8a2cc - 0x8a2d0, 0x8a4a4 - 0x8a4b4 the check of the 4-byte load at s + 160 again (its shadow address in s5).
     0x8a2d4 - 0x8a2f4, 0x8a4b8 - 0x8a4c4 the check of the 4-byte store at s + 212; a1 = the 4-byte load at s + 160
                      (the new host_counter); the 4-byte store of 1 at s + 212 (S_inflight, inflight_start :113).
     0x8a2f0 - 0x8a308, 0x8a4c8 - 0x8a4d4 the check of the 4-byte store at s + 1744, then the store of a1 there
                      (S_inflight_counter, :114).
     0x8a30c - 0x8a320, 0x8a4d8 - 0x8a4e4 the check of the 4-byte store at s + 1748, then the store of 0 there
                      (S_inflight_retries, :115).
     0x8a324 - 0x8a348, 0x8a4ec the check of the 8-byte store at s + 1752; s5 = s + 18192; a0 = now (the 8-byte load
                      at s1 + 16); the 8-byte store at s + 1752 (S_inflight_sent_us, :116).
     0x8a34c - 0x8a368, 0x8a4f0 a0 = s + 18200 (g_s.stats.tx_data); the check of the 8-byte load; the 8-byte load,
                      + 1, the 8-byte store back (:399).
     0x8a36c - 0x8a390, 0x8a4f4 - 0x8a4fc the checks of the 8-byte loads at s + 72 and s + 64.
     0x8a394 - 0x8a3a0 a1 = the 8-byte load at s + 64 (S_io_ctx, which io_send does not read); a3 = the 8-byte load at
                      s + 72 (S_io_send: tw_read, and the model's call_send gives TI.ti_io_send timg_A = 0x82d60);
                      a0 = ctx, a1 = s + 216, a2 = n (kept since 0x8a2ac).
     0x8a3a4          the indirect call (jalr a3), return address 0x8a3a8 (:400, send_raw :90; struct
                      diginet_session + 72, io.send -> io_send).
     0x8a3a8 - 0x8a3ac a2 = r (io_send's result); r <> 0 goes to 0x8a3d0 (send_raw :93).
     0x8a3b0 - 0x8a3cc, 0x8a500 - 0x8a504 the check of the 8-byte load at s + 18192 (g_s.stats.tx_frames, s5); a2 = 0;
                      the 8-byte load, + 1, the 8-byte store back (send_raw :91-92).
     0x8a3d0 - 0x8a3d8 the frame's shadow bytes 4..5 = 0xf8 (h marked out of scope).
     0x8a3dc - 0x8a3e4 the header word 0x45e0360e stored at frame.
     0x8a3e8          s2 = 0 goes to 0x8a41c (the real-stack arm; not taken).
     0x8a3ec - 0x8a418 the release: the frame's 8 shadow bytes (64 bytes) = 0xf5 (released); a0 = the 8-byte load at
                      s2 + 56 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a0 (YG0d.v astack_free_law); to 0x8a43c.
     0x8a41c - 0x8a438 the real-stack arm's release: shadow bytes 0..7 = 0.
     0x8a43c - 0x8a47c a0 = a2 (n when n < 0, else r); sp = s0 - 160, ra and s0 .. s11 loaded back, sp = sp + 160,
                      return. a1 .. a7 at the return are not stated.
   No tail jump: every call is a jal or jalr with link, every j is inside the function, and it ends with ret.
   The model and the code: the store at s + 160 is send_data_m's set_S_host_counter (u32: the low 32 bits of the
   64-bit sum of two sign-extended values); n is diginet_frame_build's build_code_w body 1514 (S_cfg_sum_mode), the
   model's diginet_frame_build_code body DIGINET_MAX_FRAME_LEN mode (lib/Prog/T/send_data.v bcw_eq); the 1514 bytes
   at out after the build are build_out_w ... oj = lib_frame ... ++ the old tail of oj when n >= 0 (send_data.v
   bout_eq, :133), so the world is the model's set_S_inflight_frame of lib_frame (S_desk_mac) (S_cfg_host_mac) send
   0 0 DIGINET_CMD_DATA (u8 ncmds) body mode; the five stores after it are set_S_inflight_len and inflight_start_m's
   four stores, the read-modify-write at s + 18200 is set_S_stats_tx_data (u64 (... + 1)), the frame handed to
   io_send is inflight_bytes (n <= 1514, so Some (sub _ A_S_inflight_frame n)), and the read-modify-write at s + 18192
   is send_raw_m's set_S_stats_tx_frames when r = 0; each store a tw_write inside g_s's payload. The code has no trap
   of its own; the model's None cases are inflight_bytes' (inflight_len > 1514, which n <= 1514 rules out),
   call_send's (S_io_send <> ti_io_send timg_A) and io_send's, ruled out by the model premise.
   Error paths (12 calls; no abort) and the facts that rule them out:
     TS___asan_report_load4 0x59608 (errpath_load4) at 0x8a490 (s + 160), 0x8a4a0 (s + 20), 0x8a4b4 (s + 160);
     TS___asan_report_store4 0x59928 (errpath_store4) at 0x8a4c4 (s + 212), 0x8a4d4 (s + 1744), 0x8a4e4 (s + 1748);
     TS___asan_report_store8 0x599c8 (errpath_store8) at 0x8a4e8 (s + 1736), 0x8a4ec (s + 1752);
     TS___asan_report_load8 0x596a8 (errpath_load8) at 0x8a4f0 (s + 18200), 0x8a4f4 (s + 72), 0x8a4fc (s + 64),
       0x8a504 (s + 18192):
       each guards a naturally aligned access inside g_s's payload [0x5df9c0, 0x5e4118) (2283 whole granules), whose
       shadow bytes are 0 at every AR state (trans_senddata_cells, read by DgnTransportCg.v decode_zshadow_rd), so
       k = 0.
   Writes: g_s's host_counter, inflight_len, inflight, inflight_counter, inflight_retries, inflight_sent_us,
   stats.tx_data and stats.tx_frames (bytes of G); diginet_frame_build's stores (its E = [s + 216, s + 216 + 1514),
   g_s.inflight_frame, bytes of G); its own machine frame; its own side-stack frame (the header, h by the memset and
   the stores), that frame's shadow bytes and its flag byte; io_send's stores (io_send_cg.v iosend_wr, bytes of G).
   No byte of a caller's frame or block is written, so senddata_wr (all bytes of G) is the written range. The G kit
   for the own frame (TransportGCg.v): dk_kept_own_g with dkg_nf and dkg_nf_sep, dk_kept_trans_nf_g (the callees'
   acall_kept_g is stated at the call state, whose frames are the own frame :: frames Sc), dkg_frame_al64,
   gx_intrin_at (the memset) and dk_kept_frame_byte_g; the stack malloc's and the release's journal steps are
   CanKit.v can_stack_malloc_at and can_flag_store_pi, read inside the G journal through gx_lift.
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_0 as astack_malloc_realizes ... SENDDATA_CID (with pc_stack_malloc (as_code B) SENDDATA_CID
       = transport_sigma TS___asan_stack_malloc_0): count_cid 0 (frames Sc) < fs_frames 0 from the premise.
     __asan_memset as aintrin_realizes ... OSet (transport_sigma TS___asan_memset), call at 0x8a244, through
       TransportGCg.v gx_intrin_at: d = hp, n = 15; each destination byte a byte of the journal's own frame list after
       the stack malloc (YCbq.v awr_byte's in_frames: transport_twr_ok_g), not owned, below alloc_ceiling (outside the
       ESTACK window); range_addressable of [hp, hp + 15) and its shadow hull (shadow bytes 4..5 = 0 since 0x8a218,
       the hull visible by astack_malloc_realizes' zero_shadow); amem_range: a frame range.
     diginet_frame_build as diginet_frame_build_cg.v transport_diginet_frame_build_cg at transport_sigma
       TS_diginet_frame_build (call at 0x8a2a8; a G-form callee composed in the same G journal, no gx_call_cg): the
       journal at the call state (the own frame live); ra = 0x8a2ac; gp, tp kept; a0 = out = s + 216, a1 = 1514 =
       length oj with oj = S_inflight_frame of the world after the store at 0x8a26c (tw_at), a2 = dst = s + 120,
       a3 = src = s, a4 = hp, a5 = bodyp, a6 = length body, a7 = mode; the realigned sp is 32-aligned,
       sp0 - STK <= sp' - FRAME_FB_STK (sp' >= sp - 176, SENDDATA_STK = 176 + IOSEND_STK >= 176 + FRAME_FB_STK),
       sp' <= sp0; out, dst, src, hp <> 0; body <> 0 from 0 < bodyp; -2 ^ 31 <= mode < 2 ^ 31 (a signed 32-bit load);
       send = u32 (S_host_counter Bw + ncmds) < 2 ^ 32, ack = 0, retry = 0, cmd = 0, ncmds' = u8 ncmds < 2 ^ 8;
       trans_out_ok of [s + 216, s + 1730): the G case (inside g_s's payload) with trans_sh_any (trans_sh_any_zshadow
       over trans_senddata_cells: its 64-byte blocks [s + 192, s + 1792) lie in g_s, which starts on 64 bytes) and
       decode_rd_ok (G bytes visible by tw_at, their shadow 0); transport_twr_ok_g at sp' - 96 by its inG case;
       garr8 of oj at out (tw_at); dst = s + 120 and src = s: 6 bytes each inside g_s's payload, trans_src_ok by
       trans_src_ok_G_range with trans_sh_any (their 64-byte blocks [s + 64, s + 128) and [s, s + 64)) and
       decode_rd_ok, decode_off_win (G lies below the stack), garr8 of S_desk_mac and S_cfg_host_mac through tw_at
       (G kept through the stack malloc and the memset); the body: trans_src_ok at the call state from the entry
       premise, carried across the stack malloc (DgnTransportCg.v trans_src_ok_inner with the bytes kept and
       trans_rd_ok_sh; the fresh frame is apart from the body: trans_src_ok_disj_own) and the memset (destination
       inside the own frame, apart from the body), decode_off_win
       at FRAME_FB_STK from the premise at SENDDATA_STK (the callee's window lies inside this one: lia), garr8 of
       body (kept by the same steps and the stores into G and the own frames); the header:
       decode_in_fake of [hp + 4, hp + 16) in the own frame, decode_rd_ok (shadow bytes 4..5 = 0), decode_off_win
       (the frame lies below alloc_ceiling, the callee's window above), garr8 of frame_fb_hdr_bytes (the memset and
       the stores at 0x8a248 and 0x8a270); the four disjointness premises: dst + 6 = s + 126 <= out, src + 6 <= out,
       [hp + 4, hp + 16) apart from [out, out + 1514) (a frame byte is outside the image, out's bytes are image
       bytes: AR_laws' al_client_img), and the body apart from G (the premise) so apart from out; count_cid 2 at the
       call state = count_cid 2 (frames Sc) < fs_frames 2 (the premise; the own frame is of class 0); st_nev S + k
       + FRAME_FB_EV <= EV_MAX (SENDDATA_EV = FRAME_FB_EV + IOSEND_EV, the stack malloc records no event). Its X:
       a0 = n, the 1514 bytes at out, and gx_kept_ex G_HARNESS [out, out + 1514): every other byte of G is kept, so
       tw_at holds at the world with the new inflight_frame.
     io_send as io_send_cg.v transport_io_send_cg at TI.ti_io_send timg_A (= 0x82d60, io_send_cg.v io_send_at; call at
       0x8a3a4; a G-form callee in the same G journal): the journal at the call state; ra = 0x8a3a8; gp, tp kept;
       a1 = p = s + 216, a2 = n = length frame, frame = sub _ A_S_inflight_frame n (the model's inflight_bytes);
       sp' 32-aligned, sp0 - STK <= sp' - IOSEND_STK, sp' <= sp0; 0 < p; garr8 of frame through tw_at;
       trans_src_ok of [p, p + n) by trans_src_ok_G_range (inside g_s's payload, trans_sh_any as for out,
       decode_rd_ok); decode_off_win at IOSEND_STK (G lies below the stack); iosend_frame_at's second disjunct
       (TA_g_s <= p, p + n <= TA_g_s + SZ_g_s); g_fail_next of the handed world = g_fail_next Bw <= 1 (g_fail_next is
       not in g_s); trans_rom_view_rd at the call memory (above); tw_at at the handed world (the stores into g_s,
       tw_write; diginet_frame_build's X); io_send_m timg_A at that world and frame = Some (B1, r): send_data_m
       through send_raw_m and call_send; run invariants (1) and (4): the premises, carried (above); st_nev at the
       call: the event count after diginet_frame_build plus IOSEND_EV, inside SENDDATA_EV. Its X: a0 = r and tw_at
       at B1.
   Stack: 160 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, __asan_memset), diginet_frame_build's FRAME_FB_STK or io_send's
   IOSEND_STK: SENDDATA_STK = 176 + IOSEND_STK (senddata_stk_eq).

   The callers: diginet_session_tick, both calls with a0 = s4 (its first argument, &g_s) and a4 = now (the 8-byte load
   at its s1 + 56), the body in its class-5 side-stack frame (the frame of 2048 bytes __asan_stack_malloc_5 returns at
   0x89328, s11; its description string at 0x1f183 names ka at 368, 1 byte, and body80 at 384, 1484 bytes):
   - at 0x89c10 (return address 0x89c14), the keepalive (:450-455): a1 = s11 + 368 (ka, whose one byte it stores as 0
     at 0x89ba0 and marks usable by the shadow byte 1 at 0x89b9c), a2 = 1, a3 = 1;
   - at 0x89ca4 (return address 0x89ca8), the data frame (:471): a1 = s9 = s11 + 384 (body), a2 = body_len (the
     8-byte load at its s1 + 80, take's out cell), a3 = take's result (taken, 0x89c5c).
   It supplies its G journal, tw_at, g_fail_next, the model premise (that branch of diginet_session_tick_m), the
   body's trans_src_ok (decode_in_fake in its frame, with decode_rd_ok), decode_off_win and its placement apart from G,
   trans_rom_view_rd, the two run invariants, and the two frame counts (its own frame is of class 5). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_build_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* send_data's frame (`sp = sp - 160` at TS_send_data), the at most 0x10 bytes of `sp = sp & -32` (0x8a16c) below
   it, and the largest stack a callee uses below the realigned sp: ESTACK for __asan_stack_malloc_0 and
   __asan_memset (YG0d.v ecall_pre), diginet_frame_build's FRAME_FB_STK, io_send's IOSEND_STK. *)
Definition SENDDATA_FRAME : Z := 160.
Definition SENDDATA_ALIGN : Z := 0x10.
Definition SENDDATA_STK : Z := SENDDATA_FRAME + SENDDATA_ALIGN + Z.max ESTACK (Z.max FRAME_FB_STK IOSEND_STK).
Lemma senddata_stk_eq : SENDDATA_STK = SENDDATA_FRAME + SENDDATA_ALIGN + IOSEND_STK.
Proof. reflexivity. Qed.
(* No allocator event: diginet_frame_build and io_send record none, and the class-0 stack malloc and its release
   record none (YG00.v stack_malloc, stack_free). *)
Definition SENDDATA_EV : Z := FRAME_FB_EV + IOSEND_EV.
(* The side-stack class (a0 = 64 at 0x8a1a4, the call of __asan_stack_malloc_0 at 0x8a1a8). *)
Definition SENDDATA_CID : Z := 0.
(* Its first argument, g_s's base in image A, and the capacity it passes to diginet_frame_build (sizeof
   g_s.inflight_frame, DIGINET_MAX_FRAME_LEN). *)
Definition SENDDATA_S : Z := TA_g_s.
Definition SENDDATA_CAP : Z := 1514.
(* The addresses of the g_s fields the code reads or writes (s + 160, s + 20, s + 120, s + 0, s + 216, s + 1736,
   s + 212, s + 1744, s + 1748, s + 1752, s + 18200, s + 72, s + 64, s + 18192). *)
Lemma senddata_addrs :
  SENDDATA_S = 0x5df9c0 /\ SENDDATA_CAP = TS0.DIGINET_MAX_FRAME_LEN /\
  SENDDATA_S + (TW.A_S_host_counter - TW.OFF_g_s) = 0x5dfa60 /\
  SENDDATA_S + (TW.A_S_cfg_sum_mode - TW.OFF_g_s) = 0x5df9d4 /\
  SENDDATA_S + (TW.A_S_desk_mac - TW.OFF_g_s) = 0x5dfa38 /\
  SENDDATA_S + (TW.A_S_cfg_host_mac - TW.OFF_g_s) = 0x5df9c0 /\
  SENDDATA_S + (TW.A_S_inflight_frame - TW.OFF_g_s) = 0x5dfa98 /\
  SENDDATA_S + (TW.A_S_inflight_len - TW.OFF_g_s) = 0x5e0088 /\
  SENDDATA_S + (TW.A_S_inflight - TW.OFF_g_s) = 0x5dfa94 /\
  SENDDATA_S + (TW.A_S_inflight_counter - TW.OFF_g_s) = 0x5e0090 /\
  SENDDATA_S + (TW.A_S_inflight_retries - TW.OFF_g_s) = 0x5e0094 /\
  SENDDATA_S + (TW.A_S_inflight_sent_us - TW.OFF_g_s) = 0x5e0098 /\
  SENDDATA_S + (TW.A_S_stats_tx_data - TW.OFF_g_s) = 0x5e40d8 /\
  SENDDATA_S + (TW.A_S_io_send - TW.OFF_g_s) = 0x5dfa08 /\
  SENDDATA_S + (TW.A_S_io_ctx - TW.OFF_g_s) = 0x5dfa00 /\
  SENDDATA_S + (TW.A_S_stats_tx_frames - TW.OFF_g_s) = 0x5e40d0.
Proof. repeat split; reflexivity. Qed.

(* The bytes some path of the call stores outside its own frames, field by field (all bytes of G): g_s's
   host_counter, inflight_frame (diginet_frame_build's E, the whole array), inflight_len, inflight,
   inflight_counter, inflight_retries, inflight_sent_us, stats.tx_data and stats.tx_frames, and io_send's
   (io_send_cg.v iosend_wr for a frame of at most 1514 bytes). Each path stores a subset (send_data_m). *)
Definition senddata_wr (a : Z) : Prop :=
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_host_counter 4 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight_frame SENDDATA_CAP a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight_len 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight 4 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight_counter 4 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight_retries 4 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight_sent_us 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_tx_data 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_tx_frames 8 a \/
  iosend_wr SENDDATA_CAP a.

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented checks of the accesses at s + 160, s + 20, s + 212 .. s + 1759, s + 72, s + 64 and s + 18192 ..
   s + 18207 read it, and the trans_sh_any of diginet_frame_build's out (s + 216), dst (s + 120) and src (s) and of
   io_send's frame (s + 216) comes from it. *)
Definition trans_senddata_cells (B : asyms) : Prop := decode_zshadow_at B SENDDATA_S (SENDDATA_S + TW.SZ_g_s).

Section senddata. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range
   senddata_wr, no meter charge (the side-stack frame changes st_fs only), and X: a0 = r (sign-extended), the world
   relation at the model's world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the
   frame this function takes is released. *)
Definition transport_senddata_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    SENDDATA_STK SENDDATA_EV 0 senddata_wr
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 r /\
       tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_send_data_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (bodyp ncmds now r : Z) (body : list byte) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 SENDDATA_S -> YK11.getr regs 11 = w64 bodyp ->
    YK11.getr regs 12 = w64 (Z.of_nat (length body)) -> YK11.getr regs 13 = w64 (bv_swrap 32 ncmds) ->
    YK11.getr regs 14 = w64 now ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SENDDATA_STK -> spZ regs <= sp0 ->
    0 <= ncmds < 2 ^ 32 -> 0 <= now < 2 ^ 64 ->
    0 < bodyp ->
    garr8 segs (mrestrict (w_H W) memc) bodyp (TW.zs body) ->
    trans_src_ok B lyc Sc W memc bodyp (Z.of_nat (length body)) ->
    decode_off_win regs SENDDATA_STK bodyp (Z.of_nat (length body)) ->
    (forall x, bodyp <= x < bodyp + Z.of_nat (length body) -> ~ inG TG.G_HARNESS x) ->
    ~ inG TG.G_HARNESS bodyp ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.send_data_m timg_A TF Bw body ncmds now = Some (Bw', r) ->
    trans_rom_view_rd W memc ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID ->
    count_cid TRANS_BC_CID (frames Sc) < fs_frames TRANS_BC_CID ->
    st_nev S + k + SENDDATA_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_senddata_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' r).

(* The statement the walk will prove: the class-0 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the record facts that no byte of G and
   no TRANS_RO_RD byte is an owned static or errno (they carry the body's trans_src_ok, G and the TRANS_RO_RD bytes
   across the stack malloc's acall_kept; DgnTransportCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno give gx_ok and
   gx_noerrno from the first two), the allocator, meter and side-stack laws, and the contracts of
   __asan_stack_malloc_0, __asan_memset, diginet_frame_build and io_send (at the value the session's send pointer
   holds) give the contract at TS_send_data. *)
Definition transport_send_data_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) SENDDATA_CID = transport_sigma TS___asan_stack_malloc_0 ->
  transport_cells B -> trans_senddata_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B SENDDATA_CID) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_frame_build_cg fx' rc B MT (transport_sigma TS_diginet_frame_build)) ->
  (forall fx' : YK11.FPState, @transport_io_send_cg fx' rc B MT (TI.ti_io_send timg_A)) ->
  transport_send_data_cg (transport_sigma TS_send_data).
End senddata.
