(* diginet_session_wake_cg: the ASan walk contract of diginet_session_wake (transport/src/diginet_session.c:119-145,
   with inflight_start (:111-117) and set_state (:79-86) inlined; model lib/TModel/TSess.v diginet_session_wake_m,
   lib/TModel/TSess0.v inflight_start_m, TSess.v set_state_m) on fuzz_transport.asan (e89be137db17) at 0x866fc =
   transport_sigma TS_diginet_session_wake, size 1632, as STATEMENTS only (no proof). It stores into g_s, a harness
   global, takes a class-2 side-stack frame for set_state's struct diginet_notice and its local e2[60], calls
   send_control (a G-form callee) while that frame is live, and calls notice through the session's notify pointer,
   so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over G =
   lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v
   transport_cg_post (acall_kept_g over G_HARNESS). Its form is session_lost_cg.v's and maybe_online_cg.v's (a G walk
   with a side-stack frame of its own); it hands send_control the two out cells send_control_cg.v's caller paragraph
   names (e2 in its own side-stack frame, e2_len in its own machine frame).

   The contract. a0 = s = &g_s = 0x5df9c0 (TWorldA.v TA_g_s), a1 = now (a uint64_t). TF is the current heap frame
   (check_state_data_cg.v trans_tframe_at at this call's window); the read-only bytes the callees read are the
   image's (trans_rom_view_rd). The memory relates to the world Bw by image A's world relation (TWorldG.v tw_at at
   TWorldA.v TMAP_A, read through aview), g_fail_next Bw <= 1, and diginet_session_wake_m timg_A TF Bw now =
   Some (Bw', r). No byte the call stores is a byte of TF (wake_apart). Class 2 of the side stack has three free
   frames (its own, then send_control's and diginet_body_check's inside it while its own is live). The function
   returns to ra with a0 = r (sign-extended), the callee-saved registers kept, no allocator event and no meter
   charge (its side-stack frame changes the state's st_fs only: ameter_fs_laws), its side-stack frame released (the
   caller's frames exactly), the caller's blocks exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or
   above alloc_ceiling outside the call's stack window [sp - WAKE_STK, sp), the image bytes outside G, the owned
   statics and errno, the caller's block and frame bytes outside wake_wr Bw), the world relation at Bw', and
   g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/diginet_session_wake_c.v): a0 =
   W_BASE_PLAIN + OFF_g_s -> a0 = TA_g_s; a1 = now, 0 <= now < 2 ^ 64 kept; wmem -> tw_at; g_fail_next B <= 1 kept
   as a premise (the code neither reads nor writes g_fail_next; send_control's statement asks it, for io_send) and
   the post's g_fail_next B' <= 1 kept in X (on the -1 and -10 paths from the premise; else from send_control's X,
   and the stores after it and notice_m do not touch the byte); diginet_session_wake_m verbatim at timg_A;
   tframe_at -> trans_tframe_at at WAKE_STK, and its off_world clause -> two facts, since check_state_data_cg.v
   trans_tframe_at drops that clause: wake_apart, no byte the call stores is a byte of TF (maybe_online_cg.v
   maybeon_apart's form), and trans_tf_off_g (check_state_data_cg.v), no byte of TF is a byte of G. trans_tf_off_g
   carries TF across send_control (call at 0x86958), which writes G, to notice (call at 0x86adc), which reads it:
   send_control's acall_kept_g keeps the image bytes outside G only, and its X pins G only to the model world B1,
   so it carries no byte of a TF inside G (diginet_session_close_cg.v takes the same fact for the same callee);
   relro_img -> trans_rom_view_rd; stk, lo + FRAME <= sp, sp mod 16 and
   w_off_stack -> the journal's window premises; mem_inv is dropped. The post's munch, wmono, stk and mem_inv ->
   transport_cg_post (the journal at the return, acall_kept_g over wake_wr Bw); wmem -> X's tw_at; the result
   register -> X's a0 = r.
   Premises the plain contract does not have:
   - count_cid 2 (frames Sc) + 2 < fs_frames 2 (send_control_cg.v's count premise, one frame deeper): its own
     class-2 frame, then send_control's class-2 frame and diginet_body_check's inside it, taken while its own is live
     (send_control's statement asks count_cid 2 (frames Sc') + 1 < fs_frames 2 at its call state, whose frames Sc'
     are the own frame :: frames Sc). With it __asan_stack_malloc_2 returns a frame (astack_malloc_realizes), so the
     real-stack arm is not taken.
   - wake_apart and trans_tf_off_g (above).
   - in the holds statement: trans_wake_cells (g_s's zero shadow), the side-stack laws, and trans_g_unowned,
     trans_g_no_errno, trans_ro_rd_unowned and trans_rom_no_errno: they carry TF's trans_src_ok across the stack
     malloc (DgnTransportCg.v trans_src_ok_inner with TF's bytes kept by its acall_kept and trans_rd_ok_sh; the
     fresh frame is apart from TF's placement: trans_src_ok_disj_own) and
     across send_control's acall_kept_g (trans_src_ok_kept over its clauses, TF lying outside G by trans_tf_off_g;
     trans_src_ok_acall_g asks every byte of G to be kept, which send_control does not give), the TRANS_RO_RD bytes
     (trans_rom_view_rd for send_control and notice), and G (TransportGCg.v gx_kept_of_acall_kept with gx_ok and
     gx_noerrno, which DgnTransportCg.v G_HARNESS_gx_ok and G_HARNESS_gx_noerrno give from the first two), as
     send_data_cg.v takes them.
   Run invariants carried (on its own Bw): (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME and (4)
   every PENDING command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX, both send_control_cg.v's premises (for
   io_send). The world wake hands send_control is wake_w1 Bw now, which differs from Bw only in g_s's e1_named_us,
   wake_acked and wake_sent_us, so both carry verbatim. notice's premise for a data notice (check_state_data's run
   invariant) holds vacuously: wake's notice has kind N_STATE (the store of 2 at p by 0x86a8c; wake_ntc). The others
   (check_latest_queue's, take's cfg bound) are not reached from wake. wake's own accesses are at fixed offsets of
   g_s (s + 96 .. s + 163, s + 212 .. s + 275, s + 1736 .. s + 1759, s + 18224 .. s + 18231,
   s + 18256 .. s + 18263), at e2_len in its machine frame and in its own frames; its memcpy moves e2_len = 60 bytes
   inside g_s.inflight_frame (1514 bytes) and its memset fills 56 bytes of its own frame, so its code needs no bound
   that the model does not give.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   1632 code bytes are equal in both files), 408 words:
     0x866fc - 0x86738 sp = sp - 128; 0x86700 stores 8 zero bytes at sp; ra at sp + 120, s0 .. s11 at sp + 112 ..
                      sp + 24, loaded back at 0x86c54 - 0x86c84; s0 = sp + 128 (the entry sp, kept to 0x86c50).
     0x8673c - 0x86744 sp = sp & -32 (at most 0x10 below entry - 128); s1 = the realigned sp; s4 = now.
     0x86748 - 0x86760 a2 = the 8-byte load of the GOT word 0xa40e8 (it holds 0xaca00), then the 4-byte load of the
                      flag word at 0xaca00; a1 = the 8-byte load of the GOT word 0xa4090 (it holds 0xac9f8), s10 = the
                      8-byte load at 0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s3 = s.
     0x86764 - 0x86778 the flag word = 0 goes to 0x86778 (s2 = 0); transport_cells row 6 gives 1. a0 = 256 and the
                      call of __asan_stack_malloc_2 (frame_alloc_2, 0x3d99c = transport_sigma
                      TS___asan_stack_malloc_2) at 0x8676c, return address 0x86770: a class-2 side-stack frame
                      (fs_frame_bytes 2 = 256 bytes); s2 = the result.
     0x8677c - 0x8679c s9 = s2; s2 <> 0 goes to 0x867a0. The real-stack arm (s2 = 0): s9 = (sp - 256) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s9), then sp = s9. With
                      count_cid 2 (frames Sc) < fs_frames 2 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s9 = s2.
     0x867a0          the 8-byte store of frame at s1 + 8 (its own machine frame).
     0x867a4 - 0x867d0 the frame header: 0x41b58ab3 at frame, the description string 0x17f02 ("2 32 72 6 n.i:83 144 60
                      6 e2:134": two variables, 72 bytes at frame + 32 and 60 bytes at frame + 144) at frame + 8, the
                      function's address 0x866fc at frame + 16.
     0x867b0, 0x867d8 - 0x8685c s8 = (frame >> 3) + 0x7fff8000; the frame's shadow bytes 0..3 = 0xf1 (guard bytes),
                      4..12 = 0xf8 (the notice's 72 bytes at frame + 32, marked out of scope), 13..17 = 0xf2 (guard
                      bytes), 18..25 = 0xf8 (e2's 60 bytes at frame + 144, marked out of scope), 26..31 = 0xf3 (guard
                      bytes).
     0x86860 - 0x86864 a0 = -1 (DIGINET_E_ARG); s = 0 goes to 0x86b30 (:121-122); not taken: s = TA_g_s <> 0.
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on; for an 8-byte access any k <> 0 goes to the error path.
     0x86868 - 0x86878, 0x86c90 - 0x86ca0 the check of the 4-byte load at s + 116.
     0x8687c - 0x86880 a1 = the 4-byte signed load at s + 116 (S_desk_known Bw); = 0 goes to 0x86b30 with a0 = -1
                      (:123-124).
     0x86884 - 0x86894, 0x86ca4 - 0x86cb0 the check of the 4-byte load at s + 136.
     0x86898 - 0x868a8 a0 = the 4-byte signed load at s + 136 (S_foreign Bw); s5 = s + 18224 (g_s.stats.tx_wakes);
                      a0 = 0 goes to 0x868d4.
     0x868ac - 0x868d0, 0x86d3c the refused path (:125-128): a0 = s + 18256 (g_s.stats.refused); one check of the
                      8-byte access, then the 8-byte load, + 1, the 8-byte store back; a0 = -10 (DIGINET_E_REFUSED); to
                      0x86b30.
     0x868d4 - 0x868e8, 0x86cb4 - 0x86cc0 the check of the 4-byte store at s + 140, then the store of 0 (S_e1_named_us
                      = 0, :129).
     0x868ec - 0x86900, 0x86cc4 - 0x86cd0 the check of the 4-byte store at s + 144, then the store of 0
                      (S_wake_acked = 0, :130).
     0x86904 - 0x8691c, 0x86d40 the check of the 8-byte store at s + 152; s6 = e2 = frame + 144; the 8-byte store of
                      now at s + 152 (S_wake_sent_us = now, :131). The world is now wake_w1 Bw now.
     0x86920 - 0x86940 shadow bytes 18..24 = 0 and 25 = 4 (e2's 60 bytes marked usable).
     0x86944 - 0x86958 a1 = 0xe2 (DIGINET_CMD_WAKE), a4 = klp = s1 + 16 (e2_len, in its machine frame; klp mod 8 = 0),
                      a0 = s, a2 = 0 (ack), a3 = kp = e2; the call of send_control (0x86d5c = transport_sigma
                      TS_send_control) at 0x86958, return address 0x8695c (:134-136).
     0x8695c          a0 = r < 0 goes to 0x86b0c with a0 = r (:137-138).
     0x86960 - 0x86970 s7 = the 8-byte load at s1 + 16 (e2_len, which send_control stored: 60); a0 = s + 216
                      (g_s.inflight_frame), a1 = e2, a2 = s7; the call of __asan_memcpy (checked_memcpy, 0x523b0 =
                      transport_sigma TS___asan_memcpy) at 0x86970, return address 0x86974 (:139).
     0x86974 - 0x86988, 0x86d44 the check of the 8-byte store at s + 1736, then the store of s7 (S_inflight_len = 60,
                      :140).
     0x8698c - 0x869a4, 0x86d48 - 0x86d4c the check of the 8-byte access at s + 18224 (s5), then the 8-byte load,
                      + 1, the 8-byte store back (S_stats_tx_wakes, :141).
     0x869a8 - 0x869b8, 0x86cd4 - 0x86ce0 the check of the 4-byte load at s + 160.
     0x869bc - 0x869dc, 0x86ce4 - 0x86cf0 the check of the 4-byte store at s + 212; a1 = the 4-byte signed load at
                      s + 160 (S_host_counter, 0x869cc); the store of 1 at s + 212 (S_inflight = 1, :113).
     0x869d8 - 0x869f0, 0x86cf4 - 0x86d00 the check of the 4-byte store at s + 1744, then the store of the low 32 bits
                      of a1 (S_inflight_counter = the host counter, :114).
     0x869f4 - 0x86a08, 0x86d04 - 0x86d10 the check of the 4-byte store at s + 1748, then the store of 0
                      (S_inflight_retries = 0, :115).
     0x86a0c - 0x86a20, 0x86d50 the check of the 8-byte store at s + 1752, then the store of now
                      (S_inflight_sent_us = now, :116). The world is now wake_w3 B1 e2 now (B1 send_control's world).
     0x86a24 - 0x86a34, 0x86d14 - 0x86d24 s5 = s + 112, s6 = the address of its shadow byte; the check of the 4-byte
                      load at s + 112.
     0x86a38 - 0x86a48 s7 = the 4-byte signed load at s + 112 (S_state); s11 = 1; s7 = 1 (S_WAKING) goes to 0x86b0c
                      with a0 = 0 (set_state :81-82).
     0x86a4c - 0x86a70 s4 = p = frame + 32, the struct diginet_notice; shadow bytes 4..12 = 0 (the notice's 72 bytes
                      marked usable).
     0x86a74 - 0x86a80 a0 = p + 16, a1 = 0, a2 = 56; the call of __asan_memset (checked_memset, 0x5284c =
                      transport_sigma TS___asan_memset) at 0x86a80, return address 0x86a84: the notice's bytes
                      16 .. 71 set to 0 (:83).
     0x86a84 - 0x86a94 plain stores into the frame: the 8 bytes 0x0000000100000002 at p (kind = N_STATE = 2 at p,
                      state = S_WAKING = 1 at p + 4), the low 32 bits of s7 at p + 8 (old = S_state), 1 at p + 12
                      (reason = R_WAKE). The 72 bytes at p are then wake_ntc Bw as trans_ntc_at reads them: every field
                      from p + 16 on is 0 (the announce pointer 0, n_ann = None; the body pointer 0 and body_len 0,
                      n_body = []).
     0x86a98 - 0x86aa8, 0x86d28 - 0x86d38 the check of the 4-byte store at s + 112 (its shadow byte read again through
                      s6), then the store of 1 at s + 112 (S_state = S_WAKING, :84).
     0x86aa4 - 0x86acc, 0x86d54, 0x86d58 the checks of the 8-byte loads at s + 96 and at s + 104.
     0x86ad0 - 0x86adc a2 = the 8-byte load at s + 96 (S_notify: tw_read, and the model's call_notify gives
                      TI.ti_notice timg_A = 0x83578); a0 = the 8-byte load at s + 104 (notify_ctx, which notice does
                      not read); a1 = p; the indirect call (jalr a2) at 0x86adc, return address 0x86ae0 (:85;
                      struct diginet_session + 96, notify -> notice).
     0x86ae0 - 0x86b08 a0 = 0 (DIGINET_OK, :144); shadow bytes 4..12 = 0xf8 (the notice out of scope again).
     0x86b0c - 0x86b2c shadow bytes 18..25 = 0xf8 (e2 out of scope again).
     0x86b30 - 0x86b38 the header word 0x45e0360e stored at frame (every path).
     0x86b3c          s2 = 0 goes to 0x86bd0 (the real-stack arm; not taken).
     0x86b40 - 0x86bcc the release: the frame's 32 shadow bytes (256 bytes) = 0xf5 (released); a1 = the 8-byte load
                      at s2 + 248 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a1 (YG0d.v astack_free_law); to 0x86c50.
     0x86bd0 - 0x86c4c the real-stack arm's release: shadow bytes 0..31 = 0.
     0x86c50 - 0x86c8c sp = s0 - 128, ra and s0 .. s11 loaded back, sp = sp + 128, return. a0 = r (-1, -10,
                      send_control's negative result, or 0); a1 .. a7 at the return are not stated.
   No tail jump: the calls are jal with link (the stack malloc, send_control, the memcpy, the memset) and one jalr with
   link (notice); every j is inside the function, and the function ends with ret.
   The model and the code: the tests at 0x86880 and 0x868a8 are diginet_session_wake_m's (S_desk_known Bw and
   S_foreign Bw against 0, each a 32-bit signed read); the stores at s + 18256, s + 140, s + 144, s + 152 are
   set_S_stats_refused (u64 of the 64-bit sum), set_S_e1_named_us, set_S_wake_acked, set_S_wake_sent_us (wake_w1);
   the call at 0x86958 is send_control_m at wake_w1 Bw now with cmd DIGINET_CMD_WAKE and ack 0, whose result
   (B1, (r, e2)) gives a0 = r, and when r >= 0 e2 = the 60 bytes f it built (send_control_cg.v's X: the 60 bytes at
   kp and put 8 60 at klp); the memcpy and the stores at s + 1736, s + 18224 are set_S_inflight_frame B1 e2,
   set_S_inflight_len (length e2 = 60), set_S_stats_tx_wakes (wake_w2), the stores at s + 212 .. s + 1759 are
   inflight_start_m's with the counter S_host_counter (wake_w2 B1 e2) (wake_w3), each a tw_write (the memcpy a
   tw_fill) inside g_s's payload; the test at 0x86a40 is set_state_m's S_state =? S_WAKING at wake_w3 B1 e2 now, the
   store at s + 112 is its set_S_state, and the call at 0x86adc is call_notify at set_S_state (wake_w3 B1 e2 now)
   S_WAKING with set_state's notice, which is wake_ntc Bw (its old field is S_state (wake_w3 B1 e2 now) = S_state
   Bw: no store before it touches g_s.state, and io_send stores no byte of g_s) (wake_model). wake_wr and wake_ntc
   read S_state Bw and GOT_n Bw, so the walk needs the model fact that send_control_m keeps S_state and GOT.n
   (send_raw_m stores only stats.tx_frames, TSess.v; io_send_m stores no byte of g_s and not GOT.n, TCb.v, as
   io_send_cg.v iosend_wr says): acall_kept_g keeps no byte of G, so it comes from the model: lib/TModel/TOpsKeep.v
   send_control_m_keep (the world after send_control_m equals Bw outside tok_wr). The code has no trap of its own;
   the model's None cases are send_control's, call_notify's (S_notify
   <> ti_notice timg_A) and notice's, all ruled out by the model premise.
   Error paths (17 calls; no abort) and the facts that rule them out:
     TS___asan_report_load4 0x59608 (errpath_load4) at 0x86ca0 (s + 116), 0x86cb0 (s + 136), 0x86ce0 (s + 160),
       0x86d24 (s + 112);
     TS___asan_report_store4 0x59928 (errpath_store4) at 0x86cc0 (s + 140), 0x86cd0 (s + 144), 0x86cf0 (s + 212),
       0x86d00 (s + 1744), 0x86d10 (s + 1748), 0x86d38 (s + 112);
     TS___asan_report_load8 0x596a8 (errpath_load8) at 0x86d3c (s + 18256), 0x86d4c (s + 18224), 0x86d54 (s + 96),
       0x86d58 (s + 104);
     TS___asan_report_store8 0x599c8 (errpath_store8) at 0x86d40 (s + 152), 0x86d44 (s + 1736), 0x86d50 (s + 1752).
     Each guards a naturally aligned access inside g_s's payload [0x5df9c0, 0x5e4118) (2283 whole granules), whose
     shadow bytes are 0 (trans_wake_cells, read at each AR state by DgnTransportCg.v decode_zshadow_rd), so k = 0.
     The memcpy's own checks (aintrin_realizes' pre, through TransportGCg.v gx_intrin_at): the destination
     [s + 216, s + 276) lies in g_s's payload (bytes of G, writable through the G journal; shadow 0 by
     trans_wake_cells); the source [e2, e2 + 60) lies in the frame this function took, its shadow bytes 18..25 = 0,
     .., 0, 4 since 0x86940, kept by send_control's acall_kept_g (the frames' shadow clause) and visible; the two
     ranges are apart (a frame byte is outside the image: AR_laws' al_client_img). The memset's: the destination
     [p + 16, p + 72) lies in the frame this function took; its shadow bytes 6 .. 12 are 0 since 0x86a70; each byte
     is a byte of the journal's own frame list after the stack malloc (transport_twr_ok_g), not owned, not in the
     ESTACK bytes below sp.
   Writes: g_s's twelve fields (bytes of G); its own machine frame (the 8 zero bytes at sp at 0x86700, the saves at
   0x86704 - 0x86734, the frame word at s1 + 8; e2_len at s1 + 16, which send_control stores); its own side-stack
   frame, that frame's shadow bytes and its flag byte; send_control's stores outside wake's frames
   (g_s.stats.tx_frames and io_send's iosend_wr 60, bytes of G); notice's stores (notice_wr, bytes of GOT). No byte
   of a caller's frame or block is written, so wake_wr is the written range. The G kit for the own frame is
   send_control_cg.v's (TransportGCg.v dk_kept_own_g with dkg_nf and dkg_nf_sep, dk_kept_trans_nf_g (send_control's
   acall_kept_g is stated at the call state, whose frames are the own frame :: frames Sc), dkg_frame_al64,
   gx_intrin_at (the memcpy, the memset) and dk_kept_frame_byte_g; CanKit.v can_stack_malloc_at and
   can_flag_store_pi read inside the G journal through gx_lift). send_control's post is transport_cg_post_out with
   the out cell [(klp, 8)], so its acall_kept_g is read at gover [(klp, 8)] mem2 memc: the walk chains
   dk_kept_trans_out_g and transport_cg_post_out_fold (TransportGCg.v) with dk_kept_trans_nf_g, whose NF holds
   [klp, klp + 8) besides the own frame (sendctl_wr kp klp holds klp, which is in neither wake_wr nor the own frame).
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_2 as astack_malloc_realizes ... WAKE_CID (with pc_stack_malloc (as_code B) WAKE_CID =
       transport_sigma TS___asan_stack_malloc_2): count_cid 2 (frames Sc) < fs_frames 2 from the count premise.
     send_control as send_control_cg.v transport_send_control_cg at transport_sigma TS_send_control (call at 0x86958;
       a G-form callee composed in the same G journal, no gx_call_cg): the journal at the call state (the own frame
       live); ra = 0x8695c; gp, tp kept; a0 = SENDCTL_S, a1 = cmd = 0xe2 < 2 ^ 8, a2 = bv_swrap 32 0 = 0 (ack = 0),
       a3 = kp = e2, a4 = klp = s1 + 16; the realigned sp is 32-aligned, sp0 - STK <= sp' - SENDCTL_STK (sp' >=
       sp - 144, WAKE_STK = 144 + SENDCTL_STK), sp' <= sp0; the keep disjunction's right part: 0 < kp; decode_in_fake
       of [e2, e2 + 60) at the call state ([frame + 144, frame + 204) inside the 256 bytes of a frame of its frames);
       transport_twr_ok_g at sp': each byte an awr_byte of the own frame list after the stack malloc (in_frames),
       not owned, below alloc_ceiling (so outside the ESTACK window); decode_rd_ok (the bytes present by
       astack_malloc_realizes, shadow bytes 18..25 = 0, .., 0, 4, their hull visible); decode_off_win at SENDCTL_STK
       (the frame lies below alloc_ceiling, send_control's window above it); apart from G (a frame byte is outside
       the image); K = the 60 bytes there, garr8 (present, by the stack malloc); klp mod 8 = 0 (s1 is 32-aligned);
       transport_twr_ok_g of [klp, klp + 8) (inside the journal's stack window, at or above sp', so outside the ESTACK
       window); decode_rd_ok (the stack's shadow is 0 at every AR state: YG0n.v zero_shadow_ranges' first row
       [ly_stk_lo, ly_stk_hi); CanKit.v can_stack_addressable); decode_off_win at SENDCTL_STK (sp' <= klp); apart
       from G (G lies below the stack); KL = the 8 bytes there, garr8 (the stack window's bytes are present: the
       journal's stack clause); kp + 60 <= klp or klp + 8 <= kp (different regions: a frame byte lies below
       alloc_ceiling, the stack above it); tw_at at wake_w1 Bw now (G kept through the stack malloc:
       gx_kept_of_acall_kept with gx_ok, gx_noerrno; then the three tw_writes); g_fail_next (wake_w1 Bw now) <= 1
       (the stores do not touch it: g_fail_next Bw <= 1); send_control_m timg_A TF (wake_w1 Bw now) DIGINET_CMD_WAKE
       0 = Some (B1, (r, e2)) (the model premise through wake_model, on the path where S_desk_known Bw <> 0 and
       S_foreign Bw = 0); trans_rom_view_rd at the call memory (no store of wake reaches a read-only byte, and the
       stack malloc's acall_kept keeps every TRANS_RO_RD byte: trans_ro_rd_scoped, from trans_ro_rd_unowned and
       trans_rom_no_errno); run invariants (1) and (4) at wake_w1 Bw now: the premises at Bw (wake_w1 changes no byte
       of M, g_cmd or g_ncmd); count_cid 2 at the call state = count_cid 2 (frames Sc) + 1, and + 1 < fs_frames 2
       is the count premise; st_nev S + k + SENDCTL_EV <= EV_MAX (WAKE_EV = SENDCTL_EV + NOTICE_EV, the stack malloc
       records no event). Its X: a0 = r, tw_at at B1, g_fail_next B1 <= 1, and when r >= 0 (so e2 <> []) the 60 bytes
       at kp holding e2 and the 8 bytes at klp holding put 8 60, both read at the returned memory; its acall_kept_g is
       read at gover [(klp, 8)] mem2 memc, because klp lies at or above alloc_ceiling outside send_control's window,
       where acall_kept_g's first clause keeps every byte.
     __asan_memcpy as aintrin_realizes ... OCpy (transport_sigma TS___asan_memcpy), call at 0x86970 (r >= 0, n = 60
       < 2 ^ 32), through TransportGCg.v gx_intrin_at (above); after it the 60 bytes at s + 216 are e2, and tw_at
       holds at set_S_inflight_frame B1 e2 (tw_fill inside g_s's payload).
     __asan_memset as aintrin_realizes ... OSet (transport_sigma TS___asan_memset), call at 0x86a80 (above).
     notice as notice_cg.v transport_notice_cg at TI.ti_notice timg_A (= 0x83578, notice_cg.v notice_at; call at
       0x86adc; a G-form callee in the same G journal):
       the journal at the call state (the own frame live); ra = 0x86ae0 (ret_ok, 4096 <= ra); gp, tp kept; a1 = p;
       sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - NOTICE_STK: sp' >= sp - 144 and
       WAKE_STK >= 144 + NOTICE_STK; sp' <= sp0;
       trans_ntc_at p (wake_ntc Bw): 0 < p and p mod 8 = 0 (p = frame + 32, dkg_frame_al64); trans_src_ok by
       decode_in_fake at the call state ([frame + 32, frame + 104) inside the 256 bytes of a frame of its frames)
       with decode_rd_ok (the bytes present by astack_malloc_realizes, shadow bytes 4..12 = 0, their hull visible);
       decode_off_win (the frame lies below alloc_ceiling, notice's window above it); NB = the 72 bytes stored at
       0x86a80 - 0x86a94, whose fields are wake_ntc's; the body: pointer 0, length 0, garr8 of [], trans_src_ok of
       the empty range at 0 (DgnTransportCg.v trans_src_ok_null), decode_off_win of it (0 <= sp' - NOTICE_STK); the
       announce: n_ann = None with the pointer 0;
       trans_tframe_at TF at NOTICE_STK: wake's trans_tframe_at at WAKE_STK, carried: TF's bytes and their shadow
       are unchanged (wake_apart for the g_s stores; across send_control, trans_src_ok_kept over the clauses of its
       acall_kept_g, which reach TF because trans_tf_off_g puts it outside G and wake_apart outside send_control's
       stores outside wake's frames; the own frame is a fresh frame, apart from TF's placement, and e2_len lies in
       wake's window, which decode_off_win puts TF outside; the record facts of the holds statement for the stack
       malloc's acall_kept), and notice's window lies inside wake's;
       trans_rom_view_rd at the call memory (as for send_control, and across send_control's acall_kept_g, whose image
       clause keeps every TRANS_RO_RD byte outside G, the owned statics and errno; the memcpy and the memset keep every
       byte outside their destinations and ESTACK bytes);
       tw_at at set_S_state (wake_w3 B1 e2 now) S_WAKING: send_control's X, the memcpy's tw_fill, then the
       tw_writes;
       notice_m timg_A TF (set_S_state (wake_w3 B1 e2 now) S_WAKING) (wake_ntc Bw) = Some (Bw', tt): the model
       premise through wake_model and set_state_m (on this path S_state (wake_w3 B1 e2 now) = S_state Bw <>
       S_WAKING; call_notify's test is the indirect target's value);
       notice_apart: a byte of notice_wr is a byte of GOT (kind N_STATE: GOT.t[GOT.n] and GOT.n), a byte of G, so
       not a byte of p's frame (a frame byte is outside the image: AR_laws' al_client_img); the body range is empty
       and n_ann = None; TF's range: wake_apart, since notice_wr at notice's world is notice_wr Bw (wake_ntc Bw)
       (GOT.n is the same: neither wake nor send_control stores a byte of GOT.n), a part of wake_wr Bw;
       the N_DATA premise: vacuous (n_kind = N_STATE);
       st_nev: the event count after send_control plus NOTICE_EV, inside WAKE_EV. Its X: tw_at at Bw'.
   notice's and send_control's own record facts are premises of their holds statements.
   Stack: 128 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, __asan_memcpy, __asan_memset), send_control's SENDCTL_STK or notice's
   NOTICE_STK: WAKE_STK = 144 + SENDCTL_STK (wake_stk_eq).

   The callers (each with the return address after its jal):
   - LLVMFuzzerTestOneInput at 0x818d4 (return 0x818d8): a0 = 0x5df9c0 (&g_s, formed at 0x818cc - 0x818d0), a1 = the
     8-byte load at 0x818c4; it holds a class-2 frame of its own (256 bytes), so
     its count premise for class 2 leaves room for that frame and wake's three.
   - on_announce at 0x87fb4 (return 0x87fb8): a0 = s4 (its own a0, &g_s), a1 = the 8-byte load at 0(s1) (its a2,
     kept in s10 since 0x87abc and stored there at 0x87d10), on its path of :204-205 (S_state = S_IDLE and
     S_cfg_auto_wake <> 0); it holds a class-4 frame of its own.
   Each supplies its G journal, tw_at, g_fail_next, the model premise (its branch of the model), trans_tframe_at,
   wake_apart and trans_tf_off_g of its TF (the last two from its plain tframe_at's off_world clause),
   trans_rom_view_rd, the two run invariants, and count_cid 2 (frames Sc) + 2 < fs_frames 2.
   The image has 2 inlined copies of inflight_start (in diginet_session_wake and send_data) and 8 of set_state:
   wake's own copies are walked here. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
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
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_session_wake's frame (`sp = sp - 128` at TS_diginet_session_wake), the at most 0x10 bytes of
   `sp = sp & -32` (0x8673c) below it, and the largest stack a callee uses below the realigned sp: ESTACK for
   __asan_stack_malloc_2, __asan_memcpy and __asan_memset (YG0d.v ecall_pre), send_control's SENDCTL_STK, notice's
   NOTICE_STK. *)
Definition WAKE_FRAME : Z := 128.
Definition WAKE_ALIGN : Z := 0x10.
Definition WAKE_STK : Z := WAKE_FRAME + WAKE_ALIGN + Z.max ESTACK (Z.max SENDCTL_STK NOTICE_STK).
Lemma wake_stk_eq : WAKE_STK = WAKE_FRAME + WAKE_ALIGN + SENDCTL_STK.
Proof. reflexivity. Qed.
(* No allocator event: send_control and notice record none, and the class-2 stack malloc and its release record
   none (YG00.v stack_malloc, stack_free). *)
Definition WAKE_EV : Z := SENDCTL_EV + NOTICE_EV.
(* The side-stack class (a0 = 256 at 0x86768, the call of __asan_stack_malloc_2 at 0x8676c): send_control's class,
   and diginet_body_check's inside it, hence the + 2 of the count premise. *)
Definition WAKE_CID : Z := 2.
Lemma wake_cid_sendctl : WAKE_CID = SENDCTL_CID.
Proof. reflexivity. Qed.
(* Its first argument: g_s's base in image A. *)
Definition WAKE_S : Z := TA_g_s.
(* The addresses of the g_s fields the code reads or writes (s + 116, s + 136, s + 18256, s + 140, s + 144, s + 152,
   s + 216, s + 1736, s + 18224, s + 160, s + 212, s + 1744, s + 1748, s + 1752, s + 112, s + 96, s + 104). *)
Lemma wake_addrs :
  WAKE_S = 0x5df9c0 /\
  WAKE_S + (TW.A_S_desk_known - TW.OFF_g_s) = 0x5dfa34 /\
  WAKE_S + (TW.A_S_foreign - TW.OFF_g_s) = 0x5dfa48 /\
  WAKE_S + (TW.A_S_stats_refused - TW.OFF_g_s) = 0x5e4110 /\
  WAKE_S + (TW.A_S_e1_named_us - TW.OFF_g_s) = 0x5dfa4c /\
  WAKE_S + (TW.A_S_wake_acked - TW.OFF_g_s) = 0x5dfa50 /\
  WAKE_S + (TW.A_S_wake_sent_us - TW.OFF_g_s) = 0x5dfa58 /\
  WAKE_S + (TW.A_S_inflight_frame - TW.OFF_g_s) = 0x5dfa98 /\
  WAKE_S + (TW.A_S_inflight_len - TW.OFF_g_s) = 0x5e0088 /\
  WAKE_S + (TW.A_S_stats_tx_wakes - TW.OFF_g_s) = 0x5e40f0 /\
  WAKE_S + (TW.A_S_host_counter - TW.OFF_g_s) = 0x5dfa60 /\
  WAKE_S + (TW.A_S_inflight - TW.OFF_g_s) = 0x5dfa94 /\
  WAKE_S + (TW.A_S_inflight_counter - TW.OFF_g_s) = 0x5e0090 /\
  WAKE_S + (TW.A_S_inflight_retries - TW.OFF_g_s) = 0x5e0094 /\
  WAKE_S + (TW.A_S_inflight_sent_us - TW.OFF_g_s) = 0x5e0098 /\
  WAKE_S + (TW.A_S_state - TW.OFF_g_s) = 0x5dfa30 /\
  WAKE_S + (TW.A_S_notify - TW.OFF_g_s) = 0x5dfa20 /\
  WAKE_S + (TW.A_S_notify_ctx - TW.OFF_g_s) = 0x5dfa28.
Proof. repeat split; reflexivity. Qed.

(* The model's steps (TSess.v diginet_session_wake_m, TSess0.v inflight_start_m, TSess.v set_state_m): the world
   send_control is called with (:129-131), the world after the stores of :139-141 at send_control's world B1 and its
   bytes e2, the world after inflight_start (:142), and set_state's notice (:83) for S_WAKING / R_WAKE, whose old
   state is S_state Bw on the path that reaches it. *)
Definition wake_w1 (Bw : list byte) (now : Z) : list byte :=
  TW.set_S_wake_sent_us (TW.set_S_wake_acked (TW.set_S_e1_named_us Bw 0) 0) now.
Definition wake_w2 (B1 e2 : list byte) : list byte :=
  let B := TW.set_S_inflight_len (TW.set_S_inflight_frame B1 e2) (Z.of_nat (length e2)) in
  TW.set_S_stats_tx_wakes B (TS0.u64 (TW.S_stats_tx_wakes B + 1)).
Definition wake_w3 (B1 e2 : list byte) (now : Z) : list byte :=
  TW.set_S_inflight_sent_us
    (TW.set_S_inflight_retries
       (TW.set_S_inflight_counter (TW.set_S_inflight (wake_w2 B1 e2) 1) (TW.S_host_counter (wake_w2 B1 e2))) 0)
    now.
Definition wake_ntc (Bw : list byte) : TI.ntc :=
  TI.Ntc TS0.DIGINET_N_STATE TS0.DIGINET_S_WAKING (TW.S_state Bw) TS0.DIGINET_R_WAKE 0 0 0 0 None [] 0.
Lemma wake_model : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (now : Z),
  TSS.diginet_session_wake_m I F Bw now =
  if TW.S_desk_known Bw =? 0 then Some (Bw, TS0.DIGINET_E_ARG)
  else if negb (TW.S_foreign Bw =? 0) then
    Some (TW.set_S_stats_refused Bw (TS0.u64 (TW.S_stats_refused Bw + 1)), DLib.DIGINET_E_REFUSED)
  else
    match TSS.send_control_m I F (wake_w1 Bw now) TS0.DIGINET_CMD_WAKE 0 with
    | None => None
    | Some (B1, (r, e2)) =>
        if r <? 0 then Some (B1, r)
        else
          match TSS.set_state_m I F (wake_w3 B1 e2 now) TS0.DIGINET_S_WAKING TS0.DIGINET_R_WAKE with
          | None => None
          | Some (B2, _) => Some (B2, DLib.DIGINET_OK)
          end
    end.
Proof. intros I F Bw now. reflexivity. Qed.

(* The bytes some path of the call stores outside its own frames (each path stores a subset,
   diginet_session_wake_m): g_s's stats.refused, e1_named_us, wake_acked, wake_sent_us, inflight_frame (the 60 bytes
   of the memcpy), inflight_len, stats.tx_wakes, inflight, inflight_counter, inflight_retries, inflight_sent_us;
   send_control's stores outside wake's frames (send_control_cg.v sendctl_wr less kp and klp: stats.tx_frames and
   io_send_cg.v iosend_wr 60); and, when the state changes, g_s's state and notice's stores (notice_cg.v notice_wr:
   for an N_STATE notice, GOT.t[GOT.n] when 0 <= GOT.n < TRANS_MAX, and GOT.n; no store before notice touches
   GOT.n, so it is GOT_n Bw). *)
Definition wake_wr (Bw : list byte) (a : Z) : Prop :=
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_refused 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_e1_named_us 4 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_wake_acked 4 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_wake_sent_us 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight_frame SENDCTL_F a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight_len 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_tx_wakes 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight 4 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight_counter 4 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight_retries 4 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight_sent_us 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_tx_frames 8 a \/
  iosend_wr SENDCTL_F a \/
  (TW.S_state Bw <> TS0.DIGINET_S_WAKING /\
   (twa_fld TW.OFF_g_s TA_g_s TW.A_S_state 4 a \/ notice_wr Bw (wake_ntc Bw) a)).

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. notice reads TF after the g_s stores and after its own (notice_cg.v notice_apart). *)
Definition wake_apart (Fr : option TI.tframe) (Bw : list byte) : Prop :=
  forall x, wake_wr Bw x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented checks of the accesses at s + 96 .. s + 18263 read it, and the memcpy's destination s + 216 lies in
   it. *)
Definition trans_wake_cells (B : asyms) : Prop := decode_zshadow_at B WAKE_S (WAKE_S + TW.SZ_g_s).

Section wake. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range wake_wr Bw,
   no meter charge (the side-stack frame changes st_fs only), and X: a0 = r (sign-extended), the world relation at
   the model's world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this
   function takes is released. *)
Definition transport_wake_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    WAKE_STK WAKE_EV 0 (wake_wr Bw)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 r /\
       tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_diginet_session_wake_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 WAKE_S -> YK11.getr regs 11 = w64 now ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - WAKE_STK -> spZ regs <= sp0 ->
    0 <= now < 2 ^ 64 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.diginet_session_wake_m timg_A TF Bw now = Some (Bw', r) ->
    trans_tframe_at B lyc Sc W memc regs WAKE_STK TF ->
    trans_tf_off_g TF ->
    trans_rom_view_rd W memc ->
    wake_apart TF Bw ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    count_cid WAKE_CID (frames Sc) + 2 < fs_frames WAKE_CID ->
    st_nev S + k + WAKE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_wake_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The statement the walk will prove: the class-2 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the record facts that no byte of G and
   no TRANS_RO_RD byte is an owned static or errno (they carry TF's trans_src_ok, G and the TRANS_RO_RD bytes across
   the stack malloc's acall_kept and send_control's acall_kept_g; DgnTransportCg.v G_HARNESS_gx_ok /
   G_HARNESS_gx_noerrno give gx_ok and gx_noerrno from the first two), the allocator, meter and side-stack laws, and
   the contracts of __asan_stack_malloc_2, send_control, __asan_memcpy, __asan_memset and notice (at the value the
   session's notify pointer holds) give the contract at TS_diginet_session_wake. *)
Definition transport_diginet_session_wake_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) WAKE_CID = transport_sigma TS___asan_stack_malloc_2 ->
  transport_cells B -> trans_wake_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B WAKE_CID) ->
  (forall fx' : YK11.FPState, @transport_send_control_cg fx' rc B MT (transport_sigma TS_send_control)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  transport_diginet_session_wake_cg (transport_sigma TS_diginet_session_wake).
End wake.
