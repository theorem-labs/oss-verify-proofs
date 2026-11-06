(* on_data_cg: the ASan walk contract of on_data (transport/src/diginet_session.c:239-261, with ms (:77) inlined;
   model lib/TModel/TSess.v on_data_m) on fuzz_transport.asan (e89be137db17) at 0x888d0 = transport_sigma TS_on_data,
   size 1592, as STATEMENTS only (no proof). It stores into g_s, a harness global, takes a class-2 side-stack frame
   for its struct diginet_notice, calls send_control (a G-form callee) while that frame is live, calls the leaf
   diginet_frame_is_keepalive, and calls notice through the session's notify pointer, so it is a G-form
   caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v
   G_HARNESS with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post
   (acall_kept_g over G_HARNESS). Its form is session_lost_cg.v's and maybe_online_cg.v's: a G walk with a
   side-stack frame of its own. Its frame argument is on_ack_cg.v's trans_dframe_at.

   The contract. a0 = s = &g_s = 0x5df9c0 (TWorldA.v TA_g_s); a1 = fp, the struct diginet_frame f that
   diginet_session_rx's diginet_frame_parse filled from the frame bytes b at buf (on_ack_cg.v trans_dframe_at, the
   ASan form of lib/Prog/T/TSessC.v dframe_at); a2 = now (a uint64_t). TF is the current heap frame
   (check_state_data_cg.v trans_tframe_at at this call's window); the read-only bytes the callees read are the
   image's (trans_rom_view_rd). The memory relates to the world Bw by image A's world relation (TWorldG.v tw_at at
   TWorldA.v TMAP_A, read through aview), g_fail_next Bw <= 1, and on_data_m timg_A TF Bw b now = Some (Bw', tt). No
   byte the call stores is a byte of TF (ondata_apart). Class 2 of the side stack has three free frames (its own,
   then send_control's and diginet_body_check's inside it while its own is live). The function returns to ra with
   the callee-saved registers kept, no allocator event and no meter charge (its side-stack frame changes the state's
   st_fs only: ameter_fs_laws), its side-stack frame released (the caller's frames exactly), the caller's blocks
   exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or above alloc_ceiling outside the call's stack
   window [sp - ONDATA_STK, sp), the image bytes outside G, the owned statics and errno, the caller's block and frame
   bytes outside ondata_wr Bw b), the world relation at Bw', and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/on_data_c.v): a0 = W_BASE_PLAIN +
   OFF_g_s -> a0 = TA_g_s; a1 = fp kept; a2 = now, 0 <= now < 2 ^ 64 kept; dframe_at m sp FRAME fp buf b fj ->
   trans_dframe_at at ONDATA_STK (on_ack_cg.v gives the translation of each part); wmem -> tw_at; g_fail_next B <= 1
   kept as a premise (the code neither reads nor writes g_fail_next; send_control's statement asks it, for io_send)
   and the post's g_fail_next B' <= 1 kept in X (from send_control's X and the stores after it, which do not touch
   the byte); on_data_m verbatim at timg_A; tframe_at -> trans_tframe_at at ONDATA_STK, and its off_world clause ->
   two facts, since check_state_data_cg.v trans_tframe_at drops that clause: ondata_apart, no byte the call stores is
   a byte of TF (maybe_online_cg.v maybeon_apart's form), and trans_tf_off_g (check_state_data_cg.v), no byte of TF
   is a byte of G. trans_tf_off_g carries TF across send_control (call at 0x88a38), which writes G, to notice (call
   at 0x88c9c), which reads it: send_control's acall_kept_g keeps the image bytes outside G only, and its X pins G
   only to the model world B1, so it carries no byte of a TF inside G (diginet_session_close_cg.v takes the same
   fact for the same callee); relro_img ->
   trans_rom_view_rd; stk, lo + FRAME <= sp, sp mod 16 and w_off_stack -> the journal's window premises; mem_inv is
   dropped. The post's munch, wmono, stk and mem_inv -> transport_cg_post (the journal at the return, acall_kept_g
   over ondata_wr Bw b); wmem -> X's tw_at.
   Premises the plain contract does not have:
   - count_cid 2 (frames Sc) + 2 < fs_frames 2 (send_control_cg.v's count premise, one frame deeper): its own
     class-2 frame, then send_control's class-2 frame and diginet_body_check's inside it, taken while its own is live
     (send_control's statement asks count_cid 2 (frames Sc') + 1 < fs_frames 2 at its call state, whose frames Sc'
     are the own frame :: frames Sc). With it __asan_stack_malloc_2 returns a frame (astack_malloc_realizes), so the
     real-stack arm is not taken.
   - ondata_apart and trans_tf_off_g (above).
   - check_state_data's run invariant, carried for notice's data notice (below).
   - in the holds statement: trans_ondata_cells (g_s's zero shadow), the side-stack laws, and trans_g_unowned,
     trans_g_no_errno, trans_ro_rd_unowned and trans_rom_no_errno: they carry the trans_src_ok of TF, of the bytes
     at buf and of the OW.dn range across the stack malloc (DgnTransportCg.v trans_src_ok_inner with their bytes
     kept by its acall_kept and trans_rd_ok_sh; the fresh frame is apart from their placement:
     trans_src_ok_disj_own) and across send_control's acall_kept_g (trans_src_ok_kept over its
     clauses: the three ranges lie outside G, TF's by trans_tf_off_g, buf's by trans_dframe_at, the OW.dn range as a
     part of TF; trans_src_ok_acall_g asks every byte of G to be kept, which send_control does not give), the
     TRANS_RO_RD bytes (trans_rom_view_rd for send_control and notice), and G (TransportGCg.v
     gx_kept_of_acall_kept with gx_ok and gx_noerrno, which DgnTransportCg.v G_HARNESS_gx_ok and G_HARNESS_gx_noerrno
     give from the first two), as send_data_cg.v takes them.
   Run invariants carried (on its own Bw):
   - (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME and (4) every PENDING command g_cmd[s],
     s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX: send_control_cg.v's premises (for io_send). on_data calls
     send_control at Bw itself (on_data_m; the code stores nothing into G before 0x88a38), so both carry verbatim.
   - (3) check_state_data's: notice_cg.v asks, for a notice of kind N_DATA, trans_src_ok and decode_off_win of
     [OW_dn_body (GOT_ndata), + n_body_len n) and n_body_len n < 2 ^ 32, on notice's own world and window. on_data's
     notice has kind N_DATA exactly on the path where the frame is not a duplicate (ondata_dup) and not a keepalive
     (fr_keepalive b), with n_body_len = fr_body_len b (on_data_m, :257-259). No store before the notice touches OW
     or GOT.ndata (on_data stores fields of g_s; send_control stores g_s.stats.tx_frames and io_send's iosend_wr,
     none of them a byte of OW or GOT.ndata), and none touches g_s's desk_counter_valid or desk_counter before the
     duplicate test, so the premise is stated at Bw, guarded by ondata_dup Bw b = false and fr_keepalive b = false,
     with on_data's window (notice's window lies inside it). The bound n_body_len < 2 ^ 32 is not a premise: the
     walk has it from the frame, fr_body_len b = fr_numbytes b - 16 with fr_numbytes b = be16 b 14 < 2 ^ 16
     (DgnSpec.v), as notice_cg.v says of this caller.
   The others (check_latest_queue's, take's cfg bound) are not reached from on_data. on_data's own accesses are at
   fixed offsets of g_s (s + 36 .. s + 39, s + 96 .. s + 115, s + 164 .. s + 171, s + 192 .. s + 199, s + 18160 ..
   s + 18183, s + 18208 .. s + 18215), at fixed offsets of f (f + 20 .. f + 23, f + 28 .. f + 29, f + 32 .. f + 47) and
   in its own frames; its one memset fills 24 bytes of its own frame, so its code needs no bound that the model does
   not give.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   1592 code bytes are equal in both files), 398 words:
     0x888d0 - 0x8890c sp = sp - 160; 0x888d4 stores 8 zero bytes at sp; ra at sp + 152, s0 .. s11 at sp + 144 ..
                      sp + 56, loaded back at 0x88dc0 - 0x88df0; s0 = sp + 160 (the entry sp, kept to 0x88dbc).
     0x88910 - 0x8891c sp = sp & -32 (at most 0x10 below entry - 160); s1 = the realigned sp; s7 = now, s4 = fp.
     0x88920 - 0x88938 a2 = the 8-byte load of the GOT word 0xa40e8 (it holds 0xaca00), then the 4-byte load of the
                      flag word at 0xaca00; a1 = the 8-byte load of the GOT word 0xa4090 (it holds 0xac9f8), s11 = the
                      8-byte load at 0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s3 = s.
     0x8893c - 0x88950 the flag word = 0 goes to 0x88950 (s6 = 0); transport_cells row 6 gives 1. a0 = 160 and the
                      call of __asan_stack_malloc_2 (frame_alloc_2, 0x3d99c = transport_sigma
                      TS___asan_stack_malloc_2) at 0x88944, return address 0x88948: a class-2 side-stack frame
                      (fs_frame_bytes 2 = 256 bytes); s6 = the result.
     0x88954 - 0x88974 s10 = s6; s6 <> 0 goes to 0x88978. The real-stack arm (s6 = 0): s10 = (sp - 160) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s10), then sp = s10. With
                      count_cid 2 (frames Sc) < fs_frames 2 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s10 = s6.
     0x88978 - 0x889a8 the frame header: 0x41b58ab3 at frame, the description string 0x15fa3 ("1 32 72 5 n:257": one
                      variable, 72 bytes at frame + 32) at frame + 8, the function's address 0x888d0 at frame + 16.
     0x88984, 0x889b0 - 0x88a04 s9 = (frame >> 3) + 0x7fff8000; the frame's shadow bytes 0..3 = 0xf1, 4..12 = 0xf8
                      (the notice's 72 bytes at frame + 32, marked out of scope), 13..19 = 0xf3 (guard bytes).
     0x88a10          the 8-byte store of frame at s1 + 48 (its own machine frame).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on; for a 2-byte access, ((a & 7) + 1) < k; for an 8-byte
                      access any k <> 0 goes to the error path.
     0x889ac, 0x889c4, 0x88a08 - 0x88a14, 0x88dfc - 0x88e0c the check of the 4-byte load at f + 20 (s5 = f + 20, s2 =
                      its shadow byte's address).
     0x88a18          a2 = the 4-byte signed load at f + 20 (h.send_counter: fr_send b through frame_f_bytes, so
                      a2 = w64 (bv_swrap 32 (fr_send b))).
     0x88a1c - 0x88a38 s8 = s + 18160 (g_s.stats.rx_data); a1 = 0xa0 (DIGINET_CMD_ACK), a0 = s, a3 = 0 (kp), a4 = 0
                      (klp); the call of send_control (0x86d5c = transport_sigma TS_send_control) at 0x88a38, return
                      address 0x88a3c (:242).
     0x88a3c          a0 = r <> 0 goes to 0x88a60.
     0x88a40 - 0x88a5c, 0x88eec a0 = s + 18208 (g_s.stats.tx_acks); one check of the 8-byte access, then the 8-byte
                      load, + 1, the 8-byte store back (:242-243).
     0x88a60          the 8-byte store of s6 (the stack malloc's result) at s1 + 24.
     0x88a64 - 0x88a84, 0x88edc - 0x88ee0 one check of the 8-byte access at s + 18160, then the 8-byte load, + 1, the
                      8-byte store back (stats.rx_data, :244); s6 = f + 28 (0x88a78).
     0x88a7c, 0x88a88 - 0x88a90, 0x88e10 - 0x88e20 the check of the 2-byte load at f + 28 (a7 = its shadow byte's
                      address).
     0x88a94 - 0x88a98 a2 = the 2-byte unsigned load at f + 28 (h.retry: fr_retry b); = 0 goes to 0x88af8 (:245).
     0x88a9c - 0x88ab8, 0x88ee4 a0 = s + 18176 (g_s.stats.rx_desk_retries); one check of the 8-byte access, then the
                      8-byte load, + 1, the 8-byte store back (:246).
     0x88abc - 0x88acc, 0x88e6c - 0x88e78 the check of the 4-byte load at s + 36.
     0x88ad0 - 0x88ae0, 0x88ee8 the check of the 8-byte store at s + 192.
     0x88ae4 - 0x88af4 a1 = the 4-byte unsigned load at s + 36 (S_cfg_backoff_ms); a1 = a1 * 1000 + now (mod 2 ^ 64;
                      ms_m, u64); the 8-byte store of a1 at s + 192 (S_backoff_until_us, :247). The world is now
                      ondata_w2 B1 b r now (B1 send_control's world).
     0x88af8 - 0x88b08, 0x88e24 - 0x88e30 the check of the 4-byte load at s + 168 (a3 = its shadow byte's address).
     0x88b0c - 0x88b14 a4 = the 4-byte signed load at s + 168 (S_desk_counter_valid); a1 = s + 164; a4 = 0 goes to
                      0x88b64 (:249).
     0x88b18 - 0x88b1c, 0x88e7c - 0x88e8c the check of the 4-byte load at f + 20 (its shadow byte read through s2).
     0x88b20 - 0x88b30, 0x88e90 - 0x88ea0 the check of the 4-byte load at s + 164; a4 = the 4-byte load at f + 20
                      (0x88b2c).
     0x88b34          a2 (the retry) = 0 goes to 0x88b64 (:249).
     0x88b38 - 0x88b3c a2 = the 4-byte load at s + 164 (S_desk_counter); a2 <> a4 goes to 0x88b64 (:249). Past
                      0x88b3c, ondata_dup holds.
     0x88b40 - 0x88b60, 0x88ef0 the duplicate path (:250-251): a0 = s + 18168 (g_s.stats.rx_duplicates); one check of
                      the 8-byte access, then the 8-byte load, + 1, the 8-byte store back; to 0x88cc8.
     0x88b64 - 0x88b68, 0x88e34 - 0x88e44 the check of the 4-byte load at f + 20 (through s2).
     0x88b6c - 0x88b7c, 0x88e48 - 0x88e58 the check of the 4-byte store at s + 164; a2 = the 4-byte load at f + 20
                      (0x88b78).
     0x88b80          the 8-byte store of a7 (f + 28's shadow byte address) at s1 + 16 (its own machine frame).
     0x88b84          the store of the low 32 bits of a2 at s + 164 (S_desk_counter = fr_send b, :253).
     0x88b88 - 0x88b8c, 0x88e5c - 0x88e68 the check of the 4-byte store at s + 168 (its shadow byte read again
                      through a3).
     0x88b90 - 0x88b94 the store of 1 at s + 168 (S_desk_counter_valid = 1, :254). The world is now
                      ondata_w3 (ondata_w2 B1 b r now) b.
     0x88b98 - 0x88b9c a0 = fp; the call of diginet_frame_is_keepalive (0x8b63c = transport_sigma
                      TS_diginet_frame_is_keepalive) at 0x88b9c, return address 0x88ba0 (:255).
     0x88ba0          a0 <> 0 (a keepalive) goes to 0x88cc8 (:256).
     0x88ba4 - 0x88bc8 s7 = p = frame + 32, the struct diginet_notice; shadow bytes 4..12 = 0 (the notice's 72 bytes
                      marked usable).
     0x88bcc - 0x88bd4 the 4-byte store of 3 (N_DATA) at p (kind, :257).
     0x88bd0 - 0x88be4, 0x88ea4 - 0x88eb0 the check of the 4-byte load at s + 112.
     0x88be8 - 0x88bf8 a1 = the 4-byte signed load at s + 112 (S_state); stores into the frame: the low 32 bits of a1
                      at p + 4 (state), 8 zero bytes at p + 8 (old_state, reason), the 8 bytes of fp at p + 16
                      (n.frame, which notice does not read).
     0x88bec, 0x88bfc - 0x88c08 a0 = p + 24, a1 = 0, a2 = 24; s8 = f + 32; the call of __asan_memset
                      (checked_memset, 0x5284c = transport_sigma TS___asan_memset) at 0x88c08, return address
                      0x88c0c: the notice's bytes 24 .. 47 set to 0 (announce, personality, mac_offset).
     0x88c0c - 0x88c18, 0x88ef4 - 0x88ef8 the check of the 8-byte load at f + 32.
     0x88c1c - 0x88c24 a1 = the 8-byte load at f + 32 (f->body = buf + 30); its store at p + 48 (body, :258).
     0x88c20 - 0x88c38, 0x88efc the check of the 8-byte load at f + 40; a2 = the 8-byte load at s1 + 16 (0x88c34).
     0x88c3c - 0x88c40 a0 = the 8-byte load at f + 40 (f->body_len = fr_body_len b); its store at p + 56 (body_len,
                      :259).
     0x88c44 - 0x88c48, 0x88eb4 - 0x88ec4 the check of the 4-byte load at f + 20 (through s2).
     0x88c4c - 0x88c50 a0 = the 4-byte load at f + 20; the store of its low 32 bits at p + 64 (counter = fr_send b).
     0x88c54 - 0x88c58, 0x88ec8 - 0x88ed8 the check of the 2-byte load at f + 28 (its shadow byte read through a2).
     0x88c5c - 0x88c6c a1 = the 2-byte signed load at f + 28; the 2-byte store of a1 at p + 68 (retry = fr_retry b),
                      2 zero bytes at p + 70. The 72 bytes at p are then ondata_ntc of notice's world as trans_ntc_at
                      reads them (the announce pointer 0, n_ann = None; the body pointer buf + 30 and body_len
                      fr_body_len b, n_body = fr_body b).
     0x88c60 - 0x88c8c, 0x88f00, 0x88f04 the checks of the 8-byte loads at s + 96 and at s + 104.
     0x88c90 - 0x88c9c a2 = the 8-byte load at s + 96 (S_notify: tw_read, and the model's call_notify gives
                      TI.ti_notice timg_A = 0x83578); a0 = the 8-byte load at s + 104 (notify_ctx, which notice does
                      not read); a1 = p; the indirect call (jalr a2) at 0x88c9c, return address 0x88ca0 (:260;
                      struct diginet_session + 96, notify -> notice).
     0x88ca0 - 0x88cc4 shadow bytes 4..12 = 0xf8 (the notice out of scope again).
     0x88cc8 - 0x88cd0 the header word 0x45e0360e stored at frame (every path).
     0x88cd4 - 0x88cd8 a1 = the 8-byte load at s1 + 24 (the stack malloc's result); = 0 goes to 0x88d6c (the
                      real-stack arm; not taken).
     0x88cdc - 0x88d68 the release: the frame's 32 shadow bytes (256 bytes) = 0xf5 (released); a0 = the 8-byte load
                      at a1 + 248 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a0 (YG0d.v astack_free_law); to 0x88dbc.
     0x88d6c - 0x88db8 the real-stack arm's release: shadow bytes 0..19 = 0.
     0x88dbc - 0x88df8 sp = s0 - 160, ra and s0 .. s11 loaded back, sp = sp + 160, return. a0 .. a7 at the return are
                      not stated (void).
   No tail jump: the calls are jal with link (the stack malloc, send_control, diginet_frame_is_keepalive, the memset)
   and one jalr with link (notice); every j is inside the function, and the function ends with ret.
   The model and the code: the call at 0x88a38 is send_control_m at Bw with cmd DIGINET_CMD_ACK and ack fr_send b
   (fr_send b < 2 ^ 32: a2 holds its sign extension, as send_control's a2 = bv_swrap 32 ack); its result (B1, (r, _))
   gives a0 = r; the test at 0x88a3c and the stores at s + 18208, s + 18160, s + 18176, s + 192 are on_data_m's
   :242-247 (each 8-byte counter set to u64 of the 64-bit sum; the backoff with ms_m of a 4-byte unsigned read, so the
   product is below 2 ^ 42, plus now mod 2 ^ 64) (ondata_w2); the tests at 0x88b14, 0x88b34, 0x88b3c are on_data_m's
   duplicate test of :249 at ondata_w2 B1 b r now (ondata_dup, each a 32-bit compare: S_desk_counter_valid against 0,
   fr_retry b against 0, fr_send b against S_desk_counter), the store at s + 18168 is set_S_stats_rx_duplicates; the
   stores at s + 164 and s + 168 are set_S_desk_counter and set_S_desk_counter_valid (ondata_w3), each a tw_write
   inside g_s's payload; the call at 0x88b9c and the test at 0x88ba0 are fr_keepalive b (the leaf's result,
   keepalive_of (fr_cmd b) (fr_body_len b) (fr_body b)); the call at 0x88c9c is call_notify at ondata_w3 (ondata_w2 B1
   b r now) b with the data notice ondata_ntc of that world (ondata_model). The premise of (3) reads OW_dn_body,
   GOT_ndata, S_desk_counter_valid and S_desk_counter at Bw (its range and its guard ondata_dup Bw b), so the walk
   needs the model fact that send_control_m keeps them (send_raw_m stores only stats.tx_frames, TSess.v; io_send_m
   stores no byte of g_s, OW or GOT.ndata, TCb.v, as io_send_cg.v iosend_wr says): acall_kept_g keeps no byte of G,
   so it comes from the model: lib/TModel/TOpsKeep.v send_control_m_keep (the world after send_control_m equals Bw
   outside tok_wr). The code has no trap of its own; the model's None
   cases are send_control's, call_notify's (S_notify <> ti_notice timg_A) and notice's, all ruled out by the model
   premise.
   Error paths (21 calls; no abort) and the facts that rule them out:
     TS___asan_report_load4 0x59608 (errpath_load4) at 0x88e30 (s + 168), 0x88e78 (s + 36), 0x88ea0 (s + 164),
       0x88eb0 (s + 112);
     TS___asan_report_store4 0x59928 (errpath_store4) at 0x88e58 (s + 164), 0x88e68 (s + 168);
     TS___asan_report_load8 0x596a8 (errpath_load8) at 0x88ee0 (s + 18160), 0x88ee4 (s + 18176), 0x88eec
       (s + 18208), 0x88ef0 (s + 18168), 0x88f00 (s + 96), 0x88f04 (s + 104);
     TS___asan_report_store8 0x599c8 (errpath_store8) at 0x88ee8 (s + 192):
       each guards a naturally aligned access inside g_s's payload [0x5df9c0, 0x5e4118) (2283 whole granules),
       whose shadow bytes are 0 (trans_ondata_cells, read at each AR state by DgnTransportCg.v decode_zshadow_rd),
       so k = 0;
     TS___asan_report_load4 at 0x88e0c, 0x88e44, 0x88e8c, 0x88ec4 (f + 20); TS___asan_report_load2 0x59568
       (errpath_load2) at 0x88e20, 0x88ed8 (f + 28); TS___asan_report_load8 at 0x88ef8 (f + 32), 0x88efc (f + 40):
       fp mod 8 = 0, so each access lies in one granule of f's 64 bytes, and trans_dframe_at's decode_rd_ok gives
       range_addressable of them at entry, still true at each load: f lies in a frame of frames Sc, whose shadow
       bytes the stack malloc's acall_kept and send_control's acall_kept_g keep, the leaf keeps every byte outside
       its window, the memset keeps every byte outside [p + 24, p + 48) and its ESTACK window, and the code's own
       stores reach only g_s and its own frames and their shadow bytes.
     The memset's own check (aintrin_realizes' pre, from the G journal through TransportGCg.v gx_intrin_at): the
     destination [p + 24, p + 48) lies in the frame this function took; its shadow bytes 7 .. 9 are 0 since 0x88bc8
     and their hull is visible (astack_malloc_realizes' zero_shadow); each destination byte is a byte of the
     journal's own frame list after the stack malloc (YCbq.v awr_byte's in_frames: transport_twr_ok_g), not owned,
     not in the ESTACK bytes below sp.
   Writes: g_s's seven fields (bytes of G); its own machine frame (the 8 zero bytes at sp at 0x888d4, the saves at
   0x888d8 - 0x88908, s1 + 16, s1 + 24, s1 + 48); its own side-stack frame, that frame's shadow bytes and its flag
   byte; send_control's stores (send_control_cg.v sendctl_wr 0 0: g_s.stats.tx_frames and io_send's iosend_wr 60,
   bytes of G); notice's stores (notice_wr: GOT.ndata, a byte of G).
   No byte of a caller's frame or block is written (f and the bytes at buf are read only), so ondata_wr is the
   written range. The G kit for the own frame is session_lost_cg.v's (TransportGCg.v dk_kept_own_g with dkg_nf and
   dkg_nf_sep, dk_kept_trans_nf_g (send_control's acall_kept_g is stated at the call state, whose frames are the own
   frame :: frames Sc), dkg_frame_al64, gx_intrin_at, dk_kept_frame_byte_g; CanKit.v can_stack_malloc_at and
   can_flag_store_pi read inside the G journal through gx_lift).
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_2 as astack_malloc_realizes ... ONDATA_CID (with pc_stack_malloc (as_code B) ONDATA_CID =
       transport_sigma TS___asan_stack_malloc_2): count_cid 2 (frames Sc) < fs_frames 2 from the count premise.
     send_control as send_control_cg.v transport_send_control_cg at transport_sigma TS_send_control (call at 0x88a38;
       a G-form callee composed in the same G journal, no gx_call_cg): the journal at the call state (the own frame
       live); ra = 0x88a3c; gp, tp kept; a0 = SENDCTL_S, a1 = cmd = 0xa0 < 2 ^ 8, a2 = w64 (bv_swrap 32 (fr_send
       b)) with 0 <= fr_send b < 2 ^ 32 (be32), a3 = kp = 0, a4 = klp = 0 (the keep disjunction's left part); the
       realigned sp is 32-aligned, sp0 - STK <= sp' - SENDCTL_STK (sp' >= sp - 176, ONDATA_STK = 176 +
       SENDCTL_STK), sp' <= sp0; tw_at at Bw (G kept through the stack malloc: gx_kept_of_acall_kept with gx_ok,
       gx_noerrno); g_fail_next Bw <= 1; send_control_m timg_A TF Bw DIGINET_CMD_ACK (fr_send b) = Some (B1, (r, _))
       (the model premise through ondata_model); trans_rom_view_rd at the call memory (no store of on_data before it
       reaches a read-only byte, and the stack malloc's acall_kept keeps every TRANS_RO_RD byte: trans_ro_rd_scoped,
       from trans_ro_rd_unowned and trans_rom_no_errno); run invariants (1) and (4) at Bw: the premises; count_cid 2
       at the call state = count_cid 2 (frames Sc) + 1, and + 1 < fs_frames 2 is the count premise;
       st_nev S + k + SENDCTL_EV <= EV_MAX (ONDATA_EV = SENDCTL_EV + NOTICE_EV, the stack malloc records no event).
       Its X: a0 = r, tw_at at B1, g_fail_next B1 <= 1.
     diginet_frame_is_keepalive as its leaf statement (diginet_frame_is_keepalive_cg.v
       transport_diginet_frame_is_keepalive_cg, read at this unit's model by DgnTransportCg.v transport_leaf_at; call
       at 0x88b9c, through TransportGCg.v gx_call_leaf and the leaf bridge): a0 = f, 0 < f < 2 ^ 64; cmd = fr_cmd b
       < 2 ^ 8 and body = buf + 30 (0 <= body < 2 ^ 64); the bytes [b8 cmd] at f + 30 and le8 body ++ le8 (length
       bb) at f + 32, bb = fr_body b: the cells of frame_f_bytes buf b fj at 30, 32 and 40 (C1 (b8 (fr_cmd b)),
       C8 (buf + 30), C8 (fr_body_len b)), with length (fr_body b) = fr_body_len b (fr_code b = 0: 16 <= fr_numbytes
       b <= length b - 14); the bytes bb at body: b's bytes from 30 on (garr8 of b at buf); the leaf's addressable /
       off_stk / rng premises: f's 64 bytes marked usable (decode_rd_ok, kept as above), the body's shadow
       (trans_src_ok of buf's range: DgnTransportCg.v trans_src_ok_rd), each range outside the leaf's window [sp' -
       ESTACK, sp') (decode_off_win of f and buf at ONDATA_STK), the GOT word 0xa4090 and the cell 0xac9f8 (image
       bytes, outside every window; asan_cells: transport_cells rows 1-2). Its X: a0 = 1 when fr_keepalive b, else
       0; no byte outside its window changes (dleaf_post with WR = []).
     __asan_memset as aintrin_realizes ... OSet (transport_sigma TS___asan_memset), call at 0x88c08 (above).
     notice as notice_cg.v transport_notice_cg at TI.ti_notice timg_A (= 0x83578, notice_cg.v notice_at; call at
       0x88c9c; a G-form callee in the same G journal):
       the journal at the call state (the own frame live); ra = 0x88ca0 (ret_ok, 4096 <= ra); gp, tp kept; a1 = p;
       sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - NOTICE_STK: sp' >= sp - 176 and
       ONDATA_STK >= 176 + NOTICE_STK; sp' <= sp0;
       trans_ntc_at p (ondata_ntc of notice's world): 0 < p and p mod 8 = 0 (p = frame + 32, dkg_frame_al64);
       trans_src_ok by decode_in_fake at the call state ([frame + 32, frame + 104) inside the 256 bytes of a frame of
       its frames) with decode_rd_ok (the bytes present by astack_malloc_realizes, shadow bytes 4..12 = 0, their
       hull visible); decode_off_win (the frame lies below alloc_ceiling, notice's window above it); NB = the 72
       bytes stored at 0x88bd4 - 0x88c6c, whose fields are ondata_ntc's; the body: pointer buf + 30, n_body = fr_body
       b of length fr_body_len b, garr8 from b's at buf, trans_src_ok and decode_off_win of the sub-range [buf + 30,
       buf + 30 + fr_body_len b) of [buf, buf + length b) (DgnTransportCg.v trans_src_ok_sub, decode_off_win_sub),
       carried to the call state as below (an empty body, fr_body_len b = 0, is carried separately: the carrying
       lemmas trans_src_ok_sub, trans_src_ok_disj_own and trans_src_ok_kept take 0 < n); the announce: n_ann = None
       with the pointer 0;
       trans_tframe_at TF at NOTICE_STK: on_data's trans_tframe_at at ONDATA_STK, carried: TF's bytes and their
       shadow are unchanged (ondata_apart for the g_s stores; the own frame is a fresh frame, apart from TF's
       placement; across send_control, trans_src_ok_kept over the clauses of its acall_kept_g, which reach TF
       because trans_tf_off_g puts it outside G and ondata_apart outside sendctl_wr 0 0; the leaf keeps every byte
       outside its window; the memset keeps every byte outside [p + 24, p + 48) and its ESTACK window; the record
       facts of the holds statement for the stack malloc's acall_kept), and notice's window lies inside on_data's;
       trans_rom_view_rd at the call memory (as for send_control, and across send_control's acall_kept_g, whose image
       clause keeps every TRANS_RO_RD byte outside G, the owned statics and errno; the leaf keeps every byte outside
       its window; the memset keeps every byte outside its destination and ESTACK bytes);
       tw_at at ondata_w3 (ondata_w2 B1 b r now) b: send_control's X, then the tw_writes;
       notice_m timg_A TF (ondata_w3 (ondata_w2 B1 b r now) b) (its data notice) = Some (Bw', tt): the model premise
       through ondata_model (on this path the frame is not a duplicate and not a keepalive; call_notify's test is the
       indirect target's value);
       notice_apart: a byte of notice_wr is GOT.ndata (kind N_DATA), a byte of G, so not a byte of p's frame (a frame
       byte is outside the image: AR_laws' al_client_img) and not a byte of the body (trans_dframe_at: no byte of
       [buf, buf + length b) is a byte of G); n_ann = None; TF's range: ondata_apart, since notice_wr of the data
       notice is notice_wr Bw (ondata_ntc Bw b), a part of ondata_wr Bw b;
       the N_DATA premise: n_kind = N_DATA, and on this path ondata_dup Bw b = false (the duplicate test reads
       S_desk_counter_valid and S_desk_counter at ondata_w2 B1 b r now, where they are Bw's) and fr_keepalive b =
       false, so the run-invariant premise gives trans_src_ok and decode_off_win of [OW_dn_body Bw (GOT_ndata Bw),
       + fr_body_len b) at entry: OW_dn_body and GOT_ndata of notice's world are Bw's (no store before the notice
       touches OW or GOT.ndata), n_body_len = fr_body_len b; the range is carried across the stack malloc,
       send_control, the leaf and the memset by the same lemmas as TF's, and across send_control it is apart from
       sendctl_wr 0 0 and outside G for its own reason: when fr_body_len b > 0, check_state_data_m's frame_read
       (TCb.v) at notice's world puts it inside TF, which ondata_apart keeps apart from ondata_wr and trans_tf_off_g
       outside G; an empty range is carried separately (the lemmas take 0 < n); notice's window lies inside
       on_data's; n_body_len < 2 ^ 32 from the frame (above);
       st_nev: the event count after send_control plus NOTICE_EV, inside ONDATA_EV. Its X: tw_at at Bw'.
   notice's and send_control's own record facts are premises of their holds statements.
   Stack: 160 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the memset, the leaf), send_control's SENDCTL_STK or notice's
   NOTICE_STK: ONDATA_STK = 176 + SENDCTL_STK (ondata_stk_eq).

   The caller: diginet_session_rx at 0x879ec (return address 0x879f0), for a frame whose cmd byte (f + 30, the
   1-byte load at 0x87954) is 0 (DIGINET_CMD_DATA; 0x87984): a0 = s4 (its own a0, &g_s), a1 = s6 = its class-1
   side-stack frame + 32 (its struct diginet_frame f, filled by diginet_frame_parse at 0x876e0; the frame's shadow
   bytes 4..11, f's 64 bytes, set to 0 at 0x87698 - 0x876b4), a2 = s3 (its own a3, now). It supplies its G journal,
   tw_at, g_fail_next, the model premise (its branch of diginet_session_rx_m), trans_dframe_at of f and buf,
   trans_tframe_at, ondata_apart and trans_tf_off_g of its TF (the last two from its plain tframe_at's off_world
   clause), trans_rom_view_rd, the run invariants (1), (4) and (3), and
   count_cid 2 (frames Sc) + 2 < fs_frames 2 (its own frame is of class 1). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_frame_is_keepalive_cg.
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
Module LKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_frame_is_keepalive_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* on_data's frame (`sp = sp - 160` at TS_on_data), the at most 0x10 bytes of `sp = sp & -32` (0x88910) below it,
   and the largest stack a callee uses below the realigned sp: ESTACK for __asan_stack_malloc_2, __asan_memset (YG0d.v
   ecall_pre) and the leaf diginet_frame_is_keepalive (LeafCgKit.v ecall_pre), send_control's SENDCTL_STK, notice's
   NOTICE_STK. *)
Definition ONDATA_FRAME : Z := 160.
Definition ONDATA_ALIGN : Z := 0x10.
Definition ONDATA_STK : Z := ONDATA_FRAME + ONDATA_ALIGN + Z.max ESTACK (Z.max SENDCTL_STK NOTICE_STK).
Lemma ondata_stk_eq : ONDATA_STK = ONDATA_FRAME + ONDATA_ALIGN + SENDCTL_STK.
Proof. reflexivity. Qed.
(* No allocator event: send_control and notice record none, the leaf takes none, and the class-2 stack malloc and its
   release record none (YG00.v stack_malloc, stack_free). *)
Definition ONDATA_EV : Z := SENDCTL_EV + NOTICE_EV.
(* The side-stack class (a0 = 160 at 0x88940, the call of __asan_stack_malloc_2 at 0x88944): send_control's class,
   and diginet_body_check's inside it, hence the + 2 of the count premise. *)
Definition ONDATA_CID : Z := 2.
Lemma ondata_cid_sendctl : ONDATA_CID = SENDCTL_CID.
Proof. reflexivity. Qed.
(* Its first argument: g_s's base in image A. *)
Definition ONDATA_S : Z := TA_g_s.
(* The addresses of the g_s fields the code reads or writes (s + 18208, s + 18160, s + 18176, s + 36, s + 192,
   s + 168, s + 164, s + 18168, s + 112, s + 96, s + 104). *)
Lemma ondata_addrs :
  ONDATA_S = 0x5df9c0 /\
  ONDATA_S + (TW.A_S_stats_tx_acks - TW.OFF_g_s) = 0x5e40e0 /\
  ONDATA_S + (TW.A_S_stats_rx_data - TW.OFF_g_s) = 0x5e40b0 /\
  ONDATA_S + (TW.A_S_stats_rx_desk_retries - TW.OFF_g_s) = 0x5e40c0 /\
  ONDATA_S + (TW.A_S_cfg_backoff_ms - TW.OFF_g_s) = 0x5df9e4 /\
  ONDATA_S + (TW.A_S_backoff_until_us - TW.OFF_g_s) = 0x5dfa80 /\
  ONDATA_S + (TW.A_S_desk_counter_valid - TW.OFF_g_s) = 0x5dfa68 /\
  ONDATA_S + (TW.A_S_desk_counter - TW.OFF_g_s) = 0x5dfa64 /\
  ONDATA_S + (TW.A_S_stats_rx_duplicates - TW.OFF_g_s) = 0x5e40b8 /\
  ONDATA_S + (TW.A_S_state - TW.OFF_g_s) = 0x5dfa30 /\
  ONDATA_S + (TW.A_S_notify - TW.OFF_g_s) = 0x5dfa20 /\
  ONDATA_S + (TW.A_S_notify_ctx - TW.OFF_g_s) = 0x5dfa28.
Proof. repeat split; reflexivity. Qed.

(* The model's steps (TSess.v on_data_m): the world after the stores of :242-247 at send_control's world B1 and
   result r, the duplicate test of :249 at a world, the world after the stores of :253-254, and the data notice of
   :257-259 at a world (only its state field reads the world). *)
Definition ondata_w2 (B1 b : list byte) (r now : Z) : list byte :=
  let B := if r =? 0 then TW.set_S_stats_tx_acks B1 (TS0.u64 (TW.S_stats_tx_acks B1 + 1)) else B1 in
  let B := TW.set_S_stats_rx_data B (TS0.u64 (TW.S_stats_rx_data B + 1)) in
  if DSpec.fr_retry b =? 0 then B
  else
    let B := TW.set_S_stats_rx_desk_retries B (TS0.u64 (TW.S_stats_rx_desk_retries B + 1)) in
    TW.set_S_backoff_until_us B (TS0.u64 (now + TS0.ms_m (TW.S_cfg_backoff_ms B))).
Definition ondata_dup (Bx b : list byte) : bool :=
  negb (TW.S_desk_counter_valid Bx =? 0) && (DSpec.fr_send b =? TW.S_desk_counter Bx) &&
  negb (DSpec.fr_retry b =? 0).
Definition ondata_w3 (B2 b : list byte) : list byte :=
  TW.set_S_desk_counter_valid (TW.set_S_desk_counter B2 (DSpec.fr_send b)) 1.
Definition ondata_ntc (Bx b : list byte) : TI.ntc :=
  TI.Ntc TS0.DIGINET_N_DATA (TW.S_state Bx) 0 0 (DSpec.fr_send b) (DSpec.fr_retry b) 0 0 None
    (DSpec.fr_body b) (DSpec.fr_body_len b).
Lemma ondata_model : forall (I : TI.timg) (F : option TI.tframe) (Bw b : list byte) (now : Z),
  TSS.on_data_m I F Bw b now =
  match TSS.send_control_m I F Bw TS0.DIGINET_CMD_ACK (DSpec.fr_send b) with
  | None => None
  | Some (B1, (r, _)) =>
      if ondata_dup (ondata_w2 B1 b r now) b then
        Some (TW.set_S_stats_rx_duplicates (ondata_w2 B1 b r now)
                (TS0.u64 (TW.S_stats_rx_duplicates (ondata_w2 B1 b r now) + 1)), tt)
      else if DSpec.fr_keepalive b then Some (ondata_w3 (ondata_w2 B1 b r now) b, tt)
      else TSS.call_notify I F (ondata_w3 (ondata_w2 B1 b r now) b)
             (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b)
  end.
Proof. intros I F Bw b now. reflexivity. Qed.

(* The bytes some path of the call stores into G (each path stores a subset, on_data_m): send_control's
   (send_control_cg.v sendctl_wr 0 0: g_s.stats.tx_frames and io_send_cg.v iosend_wr 60), g_s's stats.tx_acks,
   stats.rx_data, stats.rx_desk_retries, backoff_until_us, stats.rx_duplicates (8 bytes each), desk_counter and
   desk_counter_valid (4 bytes each), and notice's stores for the data notice (notice_cg.v notice_wr: GOT.ndata, at
   any world). *)
Definition ondata_wr (Bw b : list byte) (a : Z) : Prop :=
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_tx_frames 8 a \/
  iosend_wr SENDCTL_F a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_tx_acks 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_rx_data 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_rx_desk_retries 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_backoff_until_us 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_rx_duplicates 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_desk_counter 4 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_desk_counter_valid 4 a \/
  notice_wr Bw (ondata_ntc Bw b) a.

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. notice reads TF after the g_s stores and after its own (notice_cg.v notice_apart). *)
Definition ondata_apart (Fr : option TI.tframe) (Bw b : list byte) : Prop :=
  forall x, ondata_wr Bw b x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented checks of the accesses at s + 36 .. s + 18215 read it. *)
Definition trans_ondata_cells (B : asyms) : Prop := decode_zshadow_at B ONDATA_S (ONDATA_S + TW.SZ_g_s).

Section ondata. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range
   ondata_wr Bw b, no meter charge (the side-stack frame changes st_fs only), and X: the world relation at the model's
   world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this function takes
   is released. *)
Definition transport_ondata_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' b : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    ONDATA_STK ONDATA_EV 0 (ondata_wr Bw b)
    (fun regs2 W2 mem2 => tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_on_data_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 ONDATA_S -> YK11.getr regs 11 = w64 fp -> YK11.getr regs 12 = w64 now ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - ONDATA_STK -> spZ regs <= sp0 ->
    0 <= now < 2 ^ 64 ->
    trans_dframe_at B lyc Sc W memc regs ONDATA_STK fp buf b fj ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.on_data_m timg_A TF Bw b now = Some (Bw', tt) ->
    trans_tframe_at B lyc Sc W memc regs ONDATA_STK TF ->
    trans_tf_off_g TF ->
    trans_rom_view_rd W memc ->
    ondata_apart TF Bw b ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    (ondata_dup Bw b = false -> DSpec.fr_keepalive b = false ->
       trans_src_ok B lyc Sc W memc (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (DSpec.fr_body_len b) /\
       decode_off_win regs ONDATA_STK (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (DSpec.fr_body_len b)) ->
    count_cid ONDATA_CID (frames Sc) + 2 < fs_frames ONDATA_CID ->
    st_nev S + k + ONDATA_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_ondata_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

(* The statement the walk will prove: the class-2 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the record facts that no byte of G and
   no TRANS_RO_RD byte is an owned static or errno (they carry the trans_src_ok of TF, of the bytes at buf and of the
   OW.dn range, G and the TRANS_RO_RD bytes across the stack malloc's acall_kept and send_control's acall_kept_g;
   DgnTransportCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno give gx_ok and gx_noerrno from the first two), the
   allocator, meter and side-stack laws, and the contracts of __asan_stack_malloc_2, send_control,
   diginet_frame_is_keepalive, __asan_memset and notice (at the value the session's notify pointer holds) give the
   contract at TS_on_data. *)
Definition transport_on_data_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) ONDATA_CID = transport_sigma TS___asan_stack_malloc_2 ->
  transport_cells B -> trans_ondata_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B ONDATA_CID) ->
  (forall fx' : YK11.FPState, @transport_send_control_cg fx' rc B MT (transport_sigma TS_send_control)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LKA.transport_diginet_frame_is_keepalive_cg) fx') ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  transport_on_data_cg (transport_sigma TS_on_data).
End ondata.
