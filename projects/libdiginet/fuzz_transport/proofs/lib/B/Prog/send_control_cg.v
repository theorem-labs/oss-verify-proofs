(* send_control_cg: image B's ASan walk contract of send_control (transport/src/diginet_session.c:97-109, with
   send_raw (:88-94) inlined; model lib/TModel/TSess.v send_control_m and send_raw_m) on fuzz_transport.asan-ubsan
   (41113a03c82f) at 0x86ed4 = transportb_sigma TB_send_control, size 1016, as STATEMENTS only (no proof). It stores
   into g_s (the stats counter tx_frames), a harness global, takes a class-2 side-stack frame for its locals f[60] and
   h, calls diginet_frame_build (a G-form callee) and calls io_send through the session's send pointer, so it is a
   G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/B/TransportGB.v
   G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post_out
   with the one out cell [(klp, 8)] when kp <> 0 (below; take_cg.v's form), transport_cg_post when kp = 0. Image B's
   twin of lib/A/Prog/send_control_cg.v; the differences image B's code forces are listed at the end of this comment.

   The contract. a0 = s = &g_s = 0x5df640 (TWorldB.v TB_g_s), a1 = cmd (a uint8_t), a2 = ack (a uint32_t,
   sign-extended from bit 31), a3 = kp and a4 = klp: both 0 (diginet_session_close, on_data), or
   diginet_session_wake's e2[60] (in its class-1 side-stack frame) and its size_t e2_len (in its machine frame). The
   memory relates to the world Bw by image B's world relation (TWorldG.v tw_at at TWorldB.v TMAP_B, read through
   aview), g_fail_next Bw <= 1, and send_control_m timg_B TF Bw cmd ack = Some (Bw', (r, f)) (f: the 60 built bytes,
   or [] when the build failed). The read-only bytes io_send's callees read are the image's (trans_rom_view_rd). Class
   2 of the side stack has two free frames (its own, and diginet_body_check's inside diginet_frame_build). The
   function returns to ra with a0 = r (sign-extended), the callee-saved registers kept, no allocator event and no
   meter charge (its side-stack frame changes the state's st_fs only: ameter_fs_laws), its side-stack frame released
   (the caller's frames exactly), the caller's blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (read, when
   kp <> 0, at the memory with the 8 bytes at klp put back; transport_cg_post when kp = 0, TransportGCg.v
   transport_cg_post_out_nil: the bytes at or above alloc_ceiling outside the call's stack window
   [sp - SENDCTL_STK, sp), the image bytes outside G, the owned statics and errno, the caller's block and frame bytes
   outside sendctl_wr kp klp), the world relation at Bw', g_fail_next Bw' <= 1, and, when kp <> 0, the 60 bytes at kp
   holding f and the 8 bytes at klp holding 60 when f <> [] (the old K and KL when f = []).

   The translation from the plain contract (lib/Prog/T/send_control_c.v) is image A's, but for
   0 < klp: a0 = W_BASE_PLAIN + OFF_g_s -> a0 = TB_g_s; a1 = cmd, a2 = bv_swrap 32 ack, 0 <= cmd < 2 ^ 8,
   0 <= ack < 2 ^ 32 kept; the keep disjunction kept, each part translated as take_cg.v translates its caller cells:
   rw_cells m kp [CB 60 K] and arg_blk sp FRAME kp 60 -> 0 < kp, decode_in_fake (e2 lies in a live side-stack frame
   of the caller), the write right transport_twr_ok_g, decode_rd_ok (__asan_memcpy's destination check),
   decode_off_win (off_window), the range apart from G (off_world) and garr8 of K; rw_cells / arg_blk of klp ->
   0 < klp KEPT (image A drops it; image B's code compares klp with 0, below), transport_twr_ok_g, decode_rd_ok (the
   instrumented check of the store at klp reads its shadow byte), decode_off_win, the range apart from G and garr8 of
   KL; klp mod 8 = 0 and blk_sep kp 60 klp 8 kept; wmem -> tw_at; g_fail_next B <= 1 kept (the code neither reads nor
   writes g_fail_next; io_send's statement asks it); send_control_m verbatim at timg_B, with TF free as in the plain
   contract (send_raw_m does not read it); stk, lo + FRAME <= sp, sp mod 16 and w_off_stack -> the journal's window
   premises; mem_inv is dropped. The post: munch -> acall_kept_g with the written range sendctl_wr kp klp, read at
   the memory with klp put back (transport_cg_post_out); wmono / stk / mem_inv -> the journal; wmem -> tw_at at Bw';
   g_fail_next B' <= 1 kept in X (from the model: lib/TModel/TIoSendFail.v io_send_m_fail_next gives 0 after
   io_send, and lib/Prog/T/send_control.v sc_gf_tx carries it past the store of tx_frames; on the n < 0 path
   Bw' = Bw); the rw_cells of kp and klp -> garr8 at mem2.

   Premises the plain contract does not have (image A's, for the same reasons):
   - count_cid 2 (frames Sc) + 1 < fs_frames 2: its own class-2
     frame, then diginet_body_check's class-2 frame inside diginet_frame_build (whose statement asks count_cid 2 <
     fs_frames 2 at its call state, where the frames are the own frame :: frames Sc). With it __asan_stack_malloc_2
     returns a frame (astack_malloc_realizes), so the real-stack arm is not taken and f lies in the own side-stack
     frame, where diginet_frame_build's out premise trans_out_ok places it.
   - trans_rom_view_rd W memc: io_send's own premise (check_sent_frame's bcmp of f->src with HOST and, on image B,
     check_latest_sent's load of the constant-pool word), taken at send_control's entry memory. It still holds at the
     call at 0x870fc: before it, send_control stores only into its own machine frame, its side-stack frame, that
     frame's shadow bytes, the 60 bytes at kp and the 8 bytes at klp; the stack malloc's acall_kept keeps every
     TRANS_RO_RD byte (trans_ro_rd_scoped, from trans_ro_rd_unowned and trans_rom_no_errno), diginet_frame_build's
     acall_kept_g keeps the image bytes outside G that are not owned statics or errno (the same two facts), and
     __asan_memcpy keeps every byte outside its destination and its ESTACK window.
   - in the holds statement: trans_sendctl_cells (g_s's zero shadow), the side-stack laws, gx_ok and gx_noerrno (G
     kept through the stack malloc's acall_kept: TransportGCg.v gx_kept_of_acall_kept), trans_ro_rd_unowned and
     trans_rom_no_errno (above).
   Run invariants carried (on its own Bw): (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME and (4)
   every PENDING command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX, both io_send_cg.v's premises. The world
   send_control hands io_send is Bw itself (send_raw_m calls call_send at the world send_control_m was given; the
   store of tx_frames is after the call), so both carry verbatim. diginet_frame_build carries none. The others
   (check_latest_queue's, check_state_data's, take's cfg bound) are not reached from send_control. send_control's own
   accesses are at fixed offsets of g_s (s + 0 .. s + 125, s + 160, s + 18192), of its own frames and at klp; the copy
   to kp moves n = 60 bytes inside f's 60, so its code needs no bound the model does not give.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 1016 code bytes are equal in both files), 254
   words:
     0x86ed4 - 0x86f0c sp = sp - 128; 0x86ed8 stores 8 zero bytes at sp; ra at sp + 120, s0 .. s10 at sp + 112 ..
                      sp + 32, loaded back at 0x87258 - 0x87284; s0 = sp + 128 (the entry sp, kept to 0x87254).
     0x86f10 - 0x86f24 sp = sp & -32 (at most 0x10 below entry - 128); s1 = the realigned sp; s4 = klp, s6 = kp,
                      s7 = a2 (ack), s5 = cmd.
     0x86f28 - 0x86f40 a2 = the 8-byte load of the GOT word 0xa3d48 (it holds 0xac680), then the 4-byte load of the
                      flag word at 0xac680; a1 = the 8-byte load of the GOT word 0xa3cf0 (it holds 0xac678), s10 = the
                      8-byte load at 0xac678 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s3 = s.
     0x86f44 - 0x86f58 the flag word = 0 goes to 0x86f58 (s2 = 0); transport_cells row 6 gives 1. a0 = 160 and the
                      call of __asan_stack_malloc_2 (frame_alloc_2, 0x3d9f8 = transportb_sigma
                      TB___asan_stack_malloc_2) at 0x86f4c, return address 0x86f50: a class-2 side-stack frame
                      (fs_frame_bytes 2 = 256 bytes); s2 = the result.
     0x86f5c - 0x86f7c s9 = s2; s2 <> 0 goes to 0x86f80. The real-stack arm (s2 = 0): s9 = (sp - 160) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s9), then sp = s9. With
                      count_cid 2 (frames Sc) < fs_frames 2 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s9 = s2.
     0x86f80          the 8-byte store of frame at s1 + 24 (its own machine frame).
     0x86f84 - 0x86fa8 the frame header: 0x41b58ab3 at frame, the description string 0x1d16b ("2 32 60 4 f:99 128 16
                      5 h:100": two variables, 60 bytes at frame + 32 and 16 bytes at frame + 128) at frame + 8, the
                      function's address 0x86ed4 at frame + 16.
     0x86f90, 0x86fac - 0x87010 s8 = (frame >> 3) + 0x7fff8000; the frame's shadow bytes 0..3 = 0xf1 (guard bytes),
                      12..15 = 0xf2 (guard bytes), 16..17 = 0 (h's 16 bytes at frame + 128 marked usable), 18..19 =
                      0xf3 (guard bytes), 8..10 = 0, 11 = 4 and 4..7 = 0 (f's 60 bytes at frame + 32 marked usable).
     0x87014          the 4-byte store of 0 at frame + 128 (h.numbytes, h.sum).
     0x87000, 0x87018 s & 7 <> 0 goes to the trap word at 0x87290.
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte load,
                      ((a & 7) + 3) < k (signed) goes on; for an 8-byte access any k <> 0 goes to the error path.
     0x8701c - 0x8702c, 0x87294 - 0x872a0 the check of the 4-byte load at s + 160.
     0x87030 - 0x87050 a4 = hp = frame + 128 (struct diginet_header h); a1 = the 4-byte signed load at s + 160
                      (S_host_counter Bw, :100; 0x87034); stores into h: one byte 0 at hp + 15 (num_commands,
                      0x8703c), the low 32 bits of a1 at hp + 4 (send_counter, 0x87044), the low 32 bits of s7 (the
                      entry a2) at hp + 8 (ack_counter = ack, 0x87048), two bytes 0 at hp + 12 (retry, 0x8704c), the
                      low byte of cmd at hp + 14 (cmd, 0x87050). The 12 bytes at hp + 4 are now
                      diginet_frame_build_cg.v frame_fb_hdr_bytes (S_host_counter Bw) ack 0 cmd 0.
     0x87038, 0x87040, 0x87054 - 0x8705c, 0x872a4 - 0x872b0 the check of the 4-byte load at s + 20.
     0x87060 - 0x8707c a7 = the 4-byte signed load at s + 20 (S_cfg_sum_mode Bw); s7 = f = frame + 32; a0 = f,
                      a1 = 60, a2 = s + 120 (g_s.desk_mac), a3 = s (g_s.cfg.host_mac), a4 = hp, a5 = 0, a6 = 0 (no
                      body).
     0x87080          the call of diginet_frame_build (0x8b818 = transportb_sigma TB_diginet_frame_build), return
                      address 0x87084 (:101).
     0x87084 - 0x87088 s5 = n (the result); n < 0 goes to 0x87134 (:102-103).
     0x8708c - 0x8709c kp = 0 goes to 0x870c0; else a0 = kp, a1 = f, a2 = n; the call of __asan_memcpy
                      (checked_memcpy, 0x523ec = transportb_sigma TB___asan_memcpy) at 0x8709c, return address
                      0x870a0 (:104-105, memcpy (keep, f, n)).
     0x870a0          klp = 0 goes to the trap word at 0x87290 (UBSan's null check of *keep_len).
     0x870a4 - 0x870a8 klp & 7 <> 0 goes to the trap word (UBSan's alignment check of the size_t store).
     0x870ac - 0x870bc, 0x872c0 - 0x872c4 the check of the 8-byte store at klp, then the 8-byte store of n at klp
                      (0x870bc; :106, *keep_len = n).
     0x870c0 - 0x870e4, 0x872b4 - 0x872bc the checks of the 8-byte loads at s + 72 and s + 64.
     0x870e8 - 0x870f8 a1 = the 8-byte load at s + 64 (S_io_ctx, which io_send does not read); a3 = the 8-byte load at
                      s + 72 (S_io_send Bw: tw_read, and the model's call_send gives TI.ti_io_send timg_B = 0x82ffc);
                      a0 = ctx, a1 = f, a2 = n.
     0x870fc          the indirect call (jalr a3), return address 0x87100 (:108, send_raw :90; struct
                      diginet_session + 72, io.send -> io_send).
     0x87100 - 0x87104 s5 = r (io_send's result); r <> 0 goes to 0x87134 (send_raw :93).
     0x87108 - 0x87130, 0x872c8 a0 = s + 18192 (g_s.stats.tx_frames); the check of the 8-byte load; s5 = 0; the
                      8-byte load, + 1, the 8-byte store back (send_raw :91-92). The world is now
                      set_S_stats_tx_frames B1 (u64 (S_stats_tx_frames B1 + 1)), B1 io_send's world.
     0x87134 - 0x8715c the frame's shadow bytes 16..17, 8..11 and 4..7 = 0xf8 (h and f marked out of scope).
     0x87160 - 0x87168 the header word 0x45e0360e stored at frame.
     0x8716c          s2 = 0 goes to 0x87200 (the real-stack arm; not taken).
     0x87170 - 0x871fc the release: the frame's 32 shadow bytes (256 bytes) = 0xf5 (released); a0 = the 8-byte load
                      at s2 + 248 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a0 (YG0d.v astack_free_law); to 0x87250.
     0x87200 - 0x8724c the real-stack arm's release: shadow bytes 0..19 = 0.
     0x87250 - 0x8728c a0 = s5 (n when n < 0, else r); sp = s0 - 128, ra and s0 .. s10 loaded back, sp = sp + 128,
                      return. a1 .. a7 at the return are not stated.
     0x87290          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path.
     0x87294 - 0x872c8 the slow paths of the 4-byte checks and the 6 error calls.
   No tail jump: every call is a jal or jalr with link, every j is inside the function, and it ends with ret.
   The model and the code: n is diginet_frame_build's build_code_w [] 60 (S_cfg_sum_mode Bw), which is the model's
   diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN mode (lib/Prog/T/send_data.v bcw_eq): -1 when the mode is not
   0 or 1, else 60; the 60 bytes at f after the build are build_out_w (S_desk_mac Bw) (S_cfg_host_mac Bw)
   (S_host_counter Bw) ack 0 cmd 0 [] mode oj = the model's lib_frame ... (lib/Prog/T/send_control.v sc_build_out);
   the memcpy and the store at klp are the plain contract's keep facts; the call is call_send at Bw with f; the store
   at s + 18192 is send_raw_m's set_S_stats_tx_frames (a tw_write inside g_s's payload) when r = 0. The model's None
   cases are call_send's (S_io_send <> ti_io_send timg_B) and io_send's, both ruled out by the model premise.
   Trap path (the unimp word at 0x87290, from 3 branches) and the fact that refutes each:
     0x87018 (s & 7 <> 0, a0 = s & 7 at 0x87000): s = 0x5df640, a multiple of 8;
     0x870a0 (klp = 0, reached when kp <> 0 and n >= 0): 0 < klp, the premise image B's code needs (below);
     0x870a8 (klp & 7 <> 0, reached on the same path): klp mod 8 = 0, image A's premise.
   Error paths (6 calls; no abort) and the facts that rule them out:
     __asan_report_load4 (0x59644) at 0x872a0 (s + 160) and 0x872b0 (s + 20);
     __asan_report_load8 (0x596e4) at 0x872b4 (s + 72), 0x872bc (s + 64) and 0x872c8 (s + 18192):
       each guards a naturally aligned access inside g_s's payload [0x5df640, 0x5e3d98) (2283 whole granules), whose
       shadow bytes are 0 at every AR state (trans_sendctl_cells, read by DgnTransportBCg.v decode_zshadow_rd), so
       k = 0;
     __asan_report_store8 (0x59a04) at 0x872c4 (klp): klp mod 8 = 0 (one granule) and decode_rd_ok's
       range_addressable of [klp, klp + 8) at entry, still true at 0x870ac: no store of send_control reaches a shadow
       byte outside its own frame's; for klp in the machine stack (diginet_session_wake's e2_len, the one caller that
       passes klp <> 0) the stack's shadow is 0 at every AR state (YG0n.v zero_shadow_ranges' first row [ly_stk_lo,
       ly_stk_hi); CanKit.v can_stack_addressable); for klp in a frame, the stack malloc and diginet_frame_build keep
       the frames' shadow bytes (acall_kept / acall_kept_g); in a block, the blocks' shadow by AR; and __asan_memcpy
       keeps every byte outside its destination and ESTACK window.
   Writes: g_s.stats.tx_frames (a byte of G); its own machine frame; its own side-stack frame, that frame's shadow
   bytes and its flag byte; diginet_frame_build's stores (its E = [f, f + 60), in the own frame); the 60 bytes at kp
   (__asan_memcpy) and the 8 bytes at klp; io_send's stores (io_send_cg.v iosend_wr 60: bytes of G). No other byte of
   a caller's frame or block is written, so sendctl_wr is the written range. The G kit for the own frame
   (TransportGCg.v): dk_kept_own_g with dkg_nf and dkg_nf_sep, dk_kept_trans_nf_g (the callees' acall_kept_g is
   stated at the call state, whose frames are the own frame :: frames Sc), dkg_frame_al64, gx_intrin_at (the
   memcpy) and dk_kept_frame_byte_g; the stack malloc's and the release's journal steps are image B's CanKit.v
   can_stack_malloc_at and can_flag_store_pi, read inside the G journal through gx_lift. The out cell klp (take_cg.v's
   form): the store at klp (0x870bc) is a write the journal allows (awr_ok_x: transport_twr_ok_g); klp lies in the
   caller's machine frame, above this call's stack window, where acall_kept_g's first clause keeps every byte at or
   above alloc_ceiling whatever the written range is, so the post reads acall_kept_g at the memory with klp's 8 bytes
   put back (W_journalG.v gover [(klp, 8)] mem2 memc), and X says what they hold.
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_2 as astack_malloc_realizes ... SENDCTL_CID (with pc_stack_malloc (as_code B) SENDCTL_CID =
       transportb_sigma TB___asan_stack_malloc_2): count_cid 2 (frames Sc) < fs_frames 2 from the count premise.
     diginet_frame_build as diginet_frame_build_cg.v transport_diginet_frame_build_cg at transportb_sigma
       TB_diginet_frame_build (call at 0x87080; a G-form callee composed in the same G journal, no gx_call_cg):
       the journal at the call state (the own frame live); ra = 0x87084; gp, tp kept; the eight argument registers
       above; the realigned sp is 32-aligned, sp0 - STK <= sp' - FRAME_FB_STK (sp' >= sp - 144, SENDCTL_STK =
       144 + IOSEND_STK >= 144 + FRAME_FB_STK), sp' <= sp0; out, dst, src, hp <> 0; body = 0 with length [] = 0 (the
       wide premise's right disjunct); hp mod 4 = 0 (image B's premise of diginet_frame_build: hp = frame + 128 and a
       side-stack frame is 32-aligned, AR's frames law frame_addr ly cid pos mod 32 = 0); -2 ^ 31 <= mode < 2 ^ 31
       (a signed 32-bit load); send = S_host_counter Bw < 2 ^ 32, ack < 2 ^ 32, retry = 0, cmd < 2 ^ 8, ncmds = 0;
       trans_out_ok of [f, f + 60) by decode_in_fake at the call state ([frame + 32, frame + 92) inside the 256 bytes
       of a frame of its frames) with decode_rd_ok (the bytes present by astack_malloc_realizes, shadow bytes 4..11 =
       0, 0, 0, 0, 0, 0, 0, 4 since 0x87010, their hull visible); transport_twr_ok_g at sp' - 96: each byte an
       awr_byte of the own frame list after the stack malloc (in_frames), not owned, below alloc_ceiling (so outside
       the ESTACK window); garr8 of the 60 bytes oj at f (present, by the stack malloc); dst = s + 120 and src = s:
       6 bytes each inside g_s's payload, trans_src_ok by DgnTransportBCg.v trans_src_ok_G_range with trans_sh_any
       (trans_sh_any_zshadow over trans_sendctl_cells: their 64-byte blocks [s + 64, s + 128) and [s, s + 64) lie in
       g_s, which starts on 64 bytes) and decode_rd_ok (G bytes visible by tw_at; their shadow 0), decode_off_win (G
       lies below the stack), garr8 of S_desk_mac Bw and S_cfg_host_mac Bw through tw_at (G kept through the stack
       malloc: gx_kept_of_acall_kept, gx_ok, gx_noerrno); the body: trans_src_ok_null, decode_off_win of [0, 0),
       garr8 of []; the header: decode_in_fake of [hp + 4, hp + 16) in the own frame, decode_rd_ok (shadow bytes
       16..17 = 0), decode_off_win (the frame lies below alloc_ceiling, the callee's window above), garr8 of
       frame_fb_hdr_bytes (the stores at 0x8703c - 0x87050); the four disjointness premises: [f, f + 60) apart from
       dst's and src's 6 bytes (a frame byte is outside the image, G's bytes are image bytes: AR_laws'
       al_client_img), [hp + 4, hp + 16) = [frame + 132, frame + 144) apart from [frame + 32, frame + 92), and
       body + 0 = 0 <= out; count_cid 2 at the call state = count_cid 2 (frames Sc) + 1 < fs_frames 2 (the count
       premise); st_nev S + k + FRAME_FB_EV <= EV_MAX (SENDCTL_EV = FRAME_FB_EV + IOSEND_EV, the stack malloc records
       no event). Its X: a0 = n, the 60 bytes at f, and gx_kept_ex G_HARNESS_B [f, f + 60): every byte of G is kept,
       so tw_at at Bw still holds.
     __asan_memcpy as aintrin_realizes ... OCpy (transportb_sigma TB___asan_memcpy), call at 0x8709c (kp <> 0 and
       n = 60), through TransportGCg.v gx_intrin_at: d = kp, x = f, n = 60 < 2 ^ 32; transport_twr_ok_g of [kp,
       kp + 60) at sp' (the premise's awr_byte, kept by the journal; kp below alloc_ceiling, outside the ESTACK
       window); amem_range, range_addressable and shadow_hull_vis of the destination from decode_rd_ok at entry, kept
       (kp lies in a frame of frames Sc: the frames' shadow bytes are kept by the stack malloc's acall_kept and
       diginet_frame_build's acall_kept_g); the source [f, f + 60): src_ok and its two shadow facts as for
       diginet_frame_build's out, apart from the destination (different frames: f's frame is the fresh one).
     io_send as io_send_cg.v transport_io_send_cg at TI.ti_io_send timg_B (= 0x82ffc, io_send_cg.v io_send_at; call
       at 0x870fc; a G-form callee in the same G journal): the journal at the call state; ra = 0x87100; gp, tp kept;
       a1 = p = f, a2 = 60 = length f; sp' 32-aligned, sp0 - STK <= sp' - IOSEND_STK, sp' <= sp0; 0 < f; garr8 of f
       (diginet_frame_build's X, kept by the memcpy: f lies outside [kp, kp + 60) and the ESTACK window, and by the
       store at klp, outside f's frame); trans_src_ok of [f, f + 60) by decode_in_fake at the call state with
       decode_rd_ok (shadow bytes kept by diginet_frame_build's and the memcpy's frame clauses); decode_off_win at
       IOSEND_STK (the frame lies below alloc_ceiling); iosend_frame_at's first disjunct (a frame byte is outside the
       image, so outside G); g_fail_next Bw <= 1 (the premise); trans_rom_view_rd at the call memory (above); tw_at
       at Bw (G kept by every step before the call: the stack malloc, diginet_frame_build's gx_kept_ex, the memcpy's
       destination outside G, the own stores and the store at klp outside G); io_send_m timg_B Bw f = Some (B1, r):
       send_control_m through send_raw_m and call_send; run invariants (1) and (4): the premises, at the same Bw;
       st_nev at the call: the event count after diginet_frame_build plus IOSEND_EV, inside SENDCTL_EV. Its X: a0 = r
       and tw_at at B1.
   Stack: 128 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, __asan_memcpy), diginet_frame_build's FRAME_FB_STK or io_send's
   IOSEND_STK: SENDCTL_STK = 144 + IOSEND_STK (sendctl_stk_eq).

   The callers (each with the return address after its jal):
   - diginet_session_wake at 0x86c54 (return 0x86c58): a0 = s4 (its a0, &g_s), a1 = 0xe2 (DIGINET_CMD_WAKE), a2 = 0,
     a3 = kp = s6 = s9 + 32 (0x86c14; e2[60] in its class-1 side-stack frame, which __asan_stack_malloc_1 returns at
     0x86aa4 for a0 = 0x80; its frame description "1 32 60 6 e2:134" at 0x15f6c; shadow bytes 4..11 of that frame set
     to 0, 0, 0, 0, 0, 0, 0, 4 at 0x86c20 - 0x86c3c before the call), a4 = klp = s1 + 24 (0x86c44; its realigned
     sp + 24: e2_len in its machine frame, so klp mod 8 = 0 and 0 < klp); after the call (n >= 0) it reads e2_len
     (the 8-byte load at s1 + 24, 0x86c5c) and copies that many bytes from e2 to g_s.inflight_frame (0x86c6c);
   - diginet_session_close at 0x87734 (return 0x87738): a0 = s0 (&g_s), a1 = 0xe3 (DIGINET_CMD_DISCONNECT), a2 = a3 =
     a4 = 0;
   - on_data at 0x88bb8 (return 0x88bbc): a0 = s3 (&g_s), a1 = 0xa0 (DIGINET_CMD_ACK), a2 = the frame's send counter
     (the 4-byte signed load at its a1 + 20, 0x88b98), a3 = a4 = 0.
   Each supplies its G journal, tw_at, g_fail_next, the model premise (its branch of the model), trans_rom_view_rd,
   the two run invariants, 0 < klp when kp <> 0, and count_cid 2 (frames Sc) + 1 < fs_frames 2 (on image B
   diginet_session_wake holds a class-1 frame of its own, diginet_session_close none and on_data a class-2 frame: each
   caller states the count for the class-2 frames below it).

   Against image A's statement (lib/A/Prog/send_control_cg.v): the same definitions, post and holds statement, at
   image B's names (TMAP_B, timg_B, TB_g_s, transportb_sigma, G_HARNESS_B, lib/B/Prog/DgnTransportBCg.v,
   lib/B/Prog/m_set_cg.v twb_fld, image B's diginet_frame_build_cg.v and io_send_cg.v), and what image B's code
   forces:
   - ONE premise more, `0 < klp` in the kp <> 0 disjunct: the UBSan null check `beqz s4` at 0x870a0 goes to the trap
     word when klp = 0, after the memcpy into kp, so a call with kp <> 0 and klp = 0 traps on image B; image A's code
     never compares klp with 0 and its statement drops the plain contract's 0 < klp (decode_rd_ok gives only
     0 <= klp). The one caller with kp <> 0, diginet_session_wake, passes its realigned sp + 24.
   - three UBSan branches to the trap word 0x87290 (the alignment check of s, the null and alignment checks of klp),
     refuted by the constant s, the new premise and image A's klp mod 8 = 0;
   - image B's diginet_frame_build asks hp mod 4 = 0, which hp = frame + 128 gives;
   - image B's own code: 1016 bytes (image A: 992), the store of the frame pointer at s1 + 24 (0x86f80) before the
     frame header, and io_send at 0x82ffc (image A: 0x82d60). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_build_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* send_control's frame (`sp = sp - 128` at TB_send_control), the at most 0x10 bytes of `sp = sp & -32` (0x86f10)
   below it, and the largest stack a callee uses below the realigned sp: ESTACK for __asan_stack_malloc_2 and
   __asan_memcpy (YG0d.v ecall_pre), diginet_frame_build's FRAME_FB_STK, io_send's IOSEND_STK. *)
Definition SENDCTL_FRAME : Z := 128.
Definition SENDCTL_ALIGN : Z := 0x10.
Definition SENDCTL_STK : Z := SENDCTL_FRAME + SENDCTL_ALIGN + Z.max ESTACK (Z.max FRAME_FB_STK IOSEND_STK).
Lemma sendctl_stk_eq : SENDCTL_STK = SENDCTL_FRAME + SENDCTL_ALIGN + IOSEND_STK.
Proof. reflexivity. Qed.
(* No allocator event: diginet_frame_build and io_send record none, and the class-2 stack malloc and its release
   record none (YG00.v stack_malloc, stack_free). *)
Definition SENDCTL_EV : Z := FRAME_FB_EV + IOSEND_EV.
(* The side-stack class (a0 = 160 at 0x86f48, the call of __asan_stack_malloc_2 at 0x86f4c): the class
   diginet_body_check takes inside diginet_frame_build, hence the + 1 of the count premise. *)
Definition SENDCTL_CID : Z := 2.
Lemma sendctl_cid_bc : SENDCTL_CID = TRANS_BC_CID.
Proof. reflexivity. Qed.
(* Its first argument, g_s's base in image B, and the size of f (DIGINET_MIN_FRAME_LEN), the bytes it builds, copies
   to keep and sends. *)
Definition SENDCTL_S : Z := TB_g_s.
Definition SENDCTL_F : Z := 60.
(* The addresses of the g_s fields the code reads or writes (s + 160, s + 20, s + 120, s + 0, s + 64, s + 72,
   s + 18192). *)
Lemma sendctl_addrs :
  SENDCTL_S = 0x5df640 /\ SENDCTL_F = TS0.DIGINET_MIN_FRAME_LEN /\
  SENDCTL_S + (TW.A_S_host_counter - TW.OFF_g_s) = 0x5df6e0 /\
  SENDCTL_S + (TW.A_S_cfg_sum_mode - TW.OFF_g_s) = 0x5df654 /\
  SENDCTL_S + (TW.A_S_desk_mac - TW.OFF_g_s) = 0x5df6b8 /\
  SENDCTL_S + (TW.A_S_cfg_host_mac - TW.OFF_g_s) = 0x5df640 /\
  SENDCTL_S + (TW.A_S_io_ctx - TW.OFF_g_s) = 0x5df680 /\
  SENDCTL_S + (TW.A_S_io_send - TW.OFF_g_s) = 0x5df688 /\
  SENDCTL_S + (TW.A_S_stats_tx_frames - TW.OFF_g_s) = 0x5e3d50.
Proof. repeat split; reflexivity. Qed.

(* The out cell: klp, in the caller's MACHINE frame (diginet_session_wake's e2_len), when kp <> 0. *)
Definition sendctl_outs (kp klp : Z) : list (Z * Z) := if kp =? 0 then [] else [(klp, 8)].

(* The bytes some path of the call stores outside its own frames: g_s.stats.tx_frames (8 bytes), io_send's
   (io_send_cg.v iosend_wr 60, bytes of G), and, when kp <> 0, the 60 bytes at kp and the 8 bytes at klp. *)
Definition sendctl_wr (kp klp a : Z) : Prop :=
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_tx_frames 8 a \/
  iosend_wr SENDCTL_F a \/
  (kp <> 0 /\ (kp <= a < kp + SENDCTL_F \/ klp <= a < klp + 8)).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow
   (lib/B/YF0m.v Tfib_zero_shadow row (0x5df640, 0x5e3d98 - 0x5df640)). The instrumented checks of the accesses at
   s + 160, s + 20, s + 72, s + 64 and s + 18192 read it, and the trans_sh_any of diginet_frame_build's dst (s + 120)
   and src (s) comes from it. *)
Definition trans_sendctl_cells (B : asyms) : Prop := decode_zshadow_at B SENDCTL_S (SENDCTL_S + TW.SZ_g_s).

Section sendctl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post_out over G_HARNESS_B with the out cells sendctl_outs kp klp,
   no event, the written range sendctl_wr kp klp, no meter charge (the side-stack frame changes st_fs only), and X:
   a0 = r (sign-extended), the world relation at the model's world Bw', g_fail_next Bw' <= 1, and when kp <> 0 the
   60 bytes at kp and the 8 bytes at klp (f and 60 when the build succeeded, else K and KL).
   transport_cg_post_out states frames S2 = frames Sc: the frame this function takes is released. *)
Definition transport_sendctl_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (kp klp : Z) (K KL f Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post_out fx rc tfib_sink_head segs B MT TG.G_HARNESS_B (sendctl_outs kp klp) STK sp0 FP ly S W0 mem0
    md0 own lyc Sc W memc k regs SENDCTL_STK SENDCTL_EV 0 (sendctl_wr kp klp)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 r /\
       tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1 /\
       (kp = 0 \/
        (garr8 segs (mrestrict (w_H W2) mem2) kp (TW.zs (match f with [] => K | _ => f end)) /\
         garr8 segs (mrestrict (w_H W2) mem2) klp
           (TW.zs (match f with [] => KL | _ => TW.put 8 (Z.of_nat (length f)) end))))).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_send_control_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (cmd ack kp klp r : Z) (K KL f : list byte) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 SENDCTL_S -> YK11.getr regs 11 = w64 cmd ->
    YK11.getr regs 12 = w64 (bv_swrap 32 ack) -> YK11.getr regs 13 = w64 kp -> YK11.getr regs 14 = w64 klp ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SENDCTL_STK -> spZ regs <= sp0 ->
    0 <= cmd < 2 ^ 8 -> 0 <= ack < 2 ^ 32 ->
    (kp = 0 \/
     (0 < kp /\
      decode_in_fake lyc Sc kp SENDCTL_F /\
      transport_twr_ok_g segs B TG.G_HARNESS_B STK sp0 FP ly S lyc Sc own W memc (spZ regs) kp SENDCTL_F /\
      decode_rd_ok W memc kp SENDCTL_F /\
      decode_off_win regs SENDCTL_STK kp SENDCTL_F /\
      (forall x, kp <= x < kp + SENDCTL_F -> ~ inG TG.G_HARNESS_B x) /\
      length K = Z.to_nat SENDCTL_F /\ garr8 segs (mrestrict (w_H W) memc) kp (TW.zs K) /\
      (* Image B's UBSan premise: 0x870a0 `beqz s4` (s4 = klp) goes to the trap word 0x87290 before the store
         *keep_len = n; image A's text lacks the test and its statement drops 0 < klp. *)
      0 < klp /\
      klp mod 8 = 0 /\
      transport_twr_ok_g segs B TG.G_HARNESS_B STK sp0 FP ly S lyc Sc own W memc (spZ regs) klp 8 /\
      decode_rd_ok W memc klp 8 /\
      decode_off_win regs SENDCTL_STK klp 8 /\
      (forall x, klp <= x < klp + 8 -> ~ inG TG.G_HARNESS_B x) /\
      length KL = 8%nat /\ garr8 segs (mrestrict (w_H W) memc) klp (TW.zs KL) /\
      (kp + SENDCTL_F <= klp \/ klp + 8 <= kp))) ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.send_control_m timg_B TF Bw cmd ack = Some (Bw', (r, f)) ->
    trans_rom_view_rd W memc ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    count_cid SENDCTL_CID (frames Sc) + 1 < fs_frames SENDCTL_CID ->
    st_nev S + k + SENDCTL_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_sendctl_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp K KL f Bw' r).

(* The statement the walk will prove: the class-2 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the TRANS_RO_RD bytes outside the owned
   statics and errno (DgnTransportBCg.v trans_ro_rd_scoped: they stay the image's through the stack malloc's
   acall_kept and diginet_frame_build's acall_kept_g), the allocator, meter and side-stack laws, G inside the image,
   outside the allocator's statics and outside errno (G kept through the stack malloc's acall_kept: TransportGCg.v
   gx_kept_of_acall_kept), and the contracts of __asan_stack_malloc_2, diginet_frame_build, __asan_memcpy and io_send
   (at the value the session's send pointer holds) give the contract at TB_send_control. *)
Definition transport_send_control_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) SENDCTL_CID = transportb_sigma TB___asan_stack_malloc_2 ->
  transport_cells B -> trans_sendctl_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  gx_ok segs B TG.G_HARNESS_B -> gx_noerrno B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B SENDCTL_CID) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_frame_build_cg fx' rc B MT (transportb_sigma TB_diginet_frame_build)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @transport_io_send_cg fx' rc B MT (TI.ti_io_send timg_B)) ->
  transport_send_control_cg (transportb_sigma TB_send_control).
End sendctl.
