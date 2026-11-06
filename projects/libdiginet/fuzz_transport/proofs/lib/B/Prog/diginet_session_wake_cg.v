(* diginet_session_wake_cg: image B's ASan walk contract of diginet_session_wake (transport/src/diginet_session.c:
   119-145, with inflight_start (:111-117) inlined; model lib/TModel/TSess.v diginet_session_wake_m,
   lib/TModel/TSess0.v inflight_start_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x86a38 = transportb_sigma
   TB_diginet_session_wake, size 1180, as STATEMENTS only (no proof). It stores into g_s, a harness global, takes a
   class-1 side-stack frame for its local e2[60], calls send_control (a G-form callee) while that frame is live, and
   calls set_state (a G-form callee: a function on image B, which image A inlines here), so it is a G-form
   caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx (image-free) over G =
   lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v
   transport_cg_post (image-free; acall_kept_g over G_HARNESS_B). Form: image A's
   lib/A/Prog/diginet_session_wake_cg.v at image B's names; the G walk with a side-stack frame of its own is image
   B's set_state_cg.v; it hands send_control the two out cells send_control_cg.v's caller paragraph names (e2 in its
   own side-stack frame, e2_len in its own machine frame).

   The contract. a0 = s = &g_s = 0x5df640 (TWorldB.v TB_g_s), a1 = now (a uint64_t). TF is the current heap frame
   (check_state_data_cg.v trans_tframe_at at this call's window); the read-only bytes the callees read are the
   image's (trans_rom_view_rd). The memory relates to the world Bw by image B's world relation (TWorldG.v tw_at at
   TWorldB.v TMAP_B, read through aview), g_fail_next Bw <= 1, and diginet_session_wake_m timg_B TF Bw now =
   Some (Bw', r). No byte the call stores is a byte of TF (wake_apart). Class 1 of the side stack has a free frame
   (its own), and class 2 has two (send_control's and diginet_body_check's inside it, taken while its own class-1
   frame is live; set_state's, taken after they are released). The function returns to ra with a0 = r
   (sign-extended), the callee-saved registers kept, no allocator event and no meter charge (its side-stack frame
   changes the state's st_fs only: ameter_fs_laws), its side-stack frame released (the caller's frames exactly), the
   caller's blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at or above alloc_ceiling outside the
   call's stack window [sp - WAKE_STK, sp), the image bytes outside G, the owned statics and errno, the caller's
   block and frame bytes outside wake_wr Bw), the world relation at Bw', and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/U/Prog/T/diginet_session_wake_c.v): a0 =
   W_BASE_UBSAN + OFF_g_s -> a0 = TB_g_s; a1 = now, 0 <= now < 2 ^ 64 kept; wmem -> tw_at; g_fail_next B <= 1 kept
   as a premise (the code neither reads nor writes g_fail_next; send_control's statement asks it, for io_send, and
   set_state's asks it) and the post's g_fail_next B' <= 1 kept in X (on the -1 and -10 paths from the premise; on
   send_control's negative result from send_control's X; else from set_state's X); diginet_session_wake_m verbatim
   at timg_B (timg_ubsan -> timg_B); tframe_at -> trans_tframe_at at WAKE_STK, and its off_world clause -> two facts,
   since check_state_data_cg.v trans_tframe_at drops that clause: wake_apart, no byte the call stores is a byte of TF
   (maybe_online_cg.v maybeon_apart's form), and trans_tf_off_g (check_state_data_cg.v), no byte of TF is a byte of
   G. trans_tf_off_g carries TF across send_control (call at 0x86c54), which writes G, to set_state (call at
   0x86d2c), which hands it to notice: send_control's acall_kept_g keeps the image bytes outside G only, and its X
   pins G only to the model world B1, so it carries no byte of a TF inside G (image A's
   lib/A/Prog/diginet_session_close_cg.v takes the same fact for the same callee); relro_img -> trans_rom_view_rd;
   stk, lo + FRAME <= sp, sp mod 16 and w_off_stack -> the journal's window premises; mem_inv is dropped. The post's
   munch, wmono, stk and mem_inv -> transport_cg_post (the journal at the return, acall_kept_g over wake_wr Bw); wmem
   -> X's tw_at; the result register -> X's a0 = r.
   Premises the plain contract does not have:
   - count_cid 1 (frames Sc) < fs_frames 1 and count_cid 2 (frames Sc) + 1 < fs_frames 2: its own class-1 frame;
     send_control's class-2 frame and diginet_body_check's inside it, taken while its own is live (send_control's
     statement asks count_cid 2 (frames Sc') + 1 < fs_frames 2 at its call state, whose frames Sc' are the own frame
     :: frames Sc, with count_cid 2 (frames Sc') = count_cid 2 (frames Sc): the own frame is of class 1); set_state's
     class-2 frame, taken after send_control's are released (set_state's statement asks count_cid 2 < fs_frames 2 at
     its call state). With the first, __asan_stack_malloc_1 returns a frame (astack_malloc_realizes), so the
     real-stack arm is not taken. Image A's form has count_cid 2 (frames Sc) + 2 < fs_frames 2 in their place: on
     image A the own frame is of class 2 (it holds set_state's struct diginet_notice and e2, 256 bytes); on image B
     the notice lies in set_state's own frame and the own frame holds e2 only (128 bytes, class 1), so image B's code
     needs the class-1 premise and the class-2 premise is one frame weaker.
   - wake_apart and trans_tf_off_g (above).
   - in the holds statement: trans_wake_cells (g_s's zero shadow), the side-stack laws, and trans_g_unowned,
     trans_g_no_errno, trans_ro_rd_unowned and trans_rom_no_errno: they carry TF's trans_src_ok across the stack
     malloc (DgnTransportBCg.v trans_src_ok_inner with TF's bytes kept by its acall_kept and trans_rd_ok_sh; the
     fresh frame is apart from TF's placement: trans_src_ok_disj_own) and
     across send_control's acall_kept_g (trans_src_ok_kept over its clauses, TF lying outside G by trans_tf_off_g;
     trans_src_ok_acall_g asks every byte of G to be kept, which send_control does not give), the TRANS_RO_RD bytes
     (trans_rom_view_rd for send_control and set_state), and G (TransportGCg.v gx_kept_of_acall_kept with gx_ok and
     gx_noerrno, which DgnTransportBCg.v G_HARNESS_gx_ok and G_HARNESS_gx_noerrno give from the first two), as image
     A's form takes them.
   Run invariants carried (on its own Bw): (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME and (4)
   every PENDING command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX, both send_control_cg.v's premises (for
   io_send). The world wake hands send_control is wake_w1 Bw now, which differs from Bw only in g_s's e1_named_us,
   wake_acked and wake_sent_us, so both carry verbatim. set_state carries none (its notice has kind N_STATE). The
   others (check_latest_queue's, take's cfg bound) are not reached from wake. wake's own accesses are at fixed
   offsets of g_s (s + 116 .. s + 163, s + 212 .. s + 275, s + 1736 .. s + 1759, s + 18224 .. s + 18231,
   s + 18256 .. s + 18263), at e2_len in its machine frame and in its own frame; its memcpy moves e2_len = 60 bytes
   inside g_s.inflight_frame (1514 bytes), so its code needs no bound that the model does not give.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 1180 code bytes and the 17 bytes of its frame
   description at 0x15f6c are equal in both files), 295 words:
     0x86a38 - 0x86a70 sp = sp - 128; 0x86a3c stores 8 zero bytes at sp; ra at sp + 120, s0 .. s10 at sp + 112 ..
                      sp + 32, loaded back at 0x86dfc - 0x86e28; s0 = sp + 128 (the entry sp, kept to 0x86df8).
     0x86a74 - 0x86a7c sp = sp & -32 (at most 0x10 below entry - 128); s1 = the realigned sp; s3 = now.
     0x86a80 - 0x86a94 a2 = the 8-byte load of the GOT word 0xa3d48 (it holds 0xac680), then the 4-byte load of the
                      flag word at 0xac680; a1 = the 8-byte load of the GOT word 0xa3cf0 (it holds 0xac678), s10 = the
                      8-byte load at 0xac678 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s4 = s.
     0x86a9c - 0x86ab0 the flag word = 0 goes to 0x86ab0 (s2 = 0); transport_cells row 6 gives 1. a0 = 128 and the
                      call of __asan_stack_malloc_1 (frame_alloc_1, 0x3d868 = transportb_sigma
                      TB___asan_stack_malloc_1) at 0x86aa4, return address 0x86aa8: a class-1 side-stack frame
                      (fs_frame_bytes 1 = 128 bytes); s2 = the result.
     0x86ab4 - 0x86ad4 s9 = s2; s2 <> 0 goes to 0x86ad8. The real-stack arm (s2 = 0): s9 = (sp - 128) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s9), then sp = s9. With
                      count_cid 1 (frames Sc) < fs_frames 1 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s9 = s2.
     0x86ad8          the 8-byte store of frame at s1 + 16 (its own machine frame).
     0x86adc - 0x86b04 the frame header: 0x41b58ab3 at frame, the description string 0x15f6c ("1 32 60 6 e2:134": one
                      variable, 60 bytes at frame + 32) at frame + 8, the function's address 0x86a38 at frame + 16.
     0x86ae8, 0x86b08 - 0x86b50 s8 = (frame >> 3) + 0x7fff8000; the frame's shadow bytes 0..3 = 0xf1 (guard bytes),
                      4..11 = 0xf8 (e2's 60 bytes at frame + 32, marked out of scope), 12..15 = 0xf3 (guard bytes).
     0x86b54 - 0x86b58 a0 = -1 (DIGINET_E_ARG); s = 0 goes to 0x86d58 (:121-122); not taken: s = TB_g_s <> 0.
     0x86b5c - 0x86b60 s & 7 <> 0 (the UBSan alignment check of struct diginet_session *s) goes to the trap word at
                      0x86e34.
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on; for an 8-byte access any k <> 0 goes to the error path.
     0x86b64 - 0x86b74, 0x86e38 - 0x86e48 the check of the 4-byte load at s + 116.
     0x86b78 - 0x86b7c a1 = the 4-byte signed load at s + 116 (S_desk_known Bw); = 0 goes to 0x86d58 with a0 = -1
                      (:123-124).
     0x86b80 - 0x86b90, 0x86e4c - 0x86e58 the check of the 4-byte load at s + 136.
     0x86b94 - 0x86ba4 a0 = the 4-byte signed load at s + 136 (S_foreign Bw); s5 = s + 18224 (g_s.stats.tx_wakes);
                      a0 = 0 goes to 0x86bd0.
     0x86ba8 - 0x86bcc, 0x86ebc the refused path (:125-128): a0 = s + 18256 (g_s.stats.refused); one check of the
                      8-byte access, then the 8-byte load, + 1, the 8-byte store back; a0 = -10 (DIGINET_E_REFUSED); to
                      0x86d58.
     0x86bd0 - 0x86be4, 0x86e5c - 0x86e68 the check of the 4-byte store at s + 140, then the store of 0 (S_e1_named_us
                      = 0, :129).
     0x86be8 - 0x86bfc, 0x86e6c - 0x86e78 the check of the 4-byte store at s + 144, then the store of 0
                      (S_wake_acked = 0, :130).
     0x86c00 - 0x86c18, 0x86ec0 the check of the 8-byte store at s + 152; s6 = e2 = frame + 32; the 8-byte store of
                      now at s + 152 (S_wake_sent_us = now, :131). The world is now wake_w1 Bw now.
     0x86c1c - 0x86c3c shadow bytes 4..10 = 0 and 11 = 4 (e2's 60 bytes marked usable).
     0x86c40 - 0x86c54 a1 = 0xe2 (DIGINET_CMD_WAKE), a4 = klp = s1 + 24 (e2_len, in its machine frame; klp mod 8 = 0),
                      a0 = s, a2 = 0 (ack), a3 = kp = e2; the call of send_control (0x86ed4 = transportb_sigma
                      TB_send_control) at 0x86c54, return address 0x86c58 (:134-136).
     0x86c58          a0 = r < 0 goes to 0x86d34 with a0 = r (:137-138).
     0x86c5c - 0x86c6c s7 = the 8-byte load at s1 + 24 (e2_len, which send_control stored: 60); a0 = s + 216
                      (g_s.inflight_frame), a1 = e2, a2 = s7; the call of __asan_memcpy (checked_memcpy, 0x523ec =
                      transportb_sigma TB___asan_memcpy) at 0x86c6c, return address 0x86c70 (:139).
     0x86c70 - 0x86c84, 0x86ec4 the check of the 8-byte store at s + 1736, then the store of s7 (S_inflight_len = 60,
                      :140).
     0x86c88 - 0x86ca0, 0x86ec8 - 0x86ecc the check of the 8-byte access at s + 18224 (s5), then the 8-byte load,
                      + 1, the 8-byte store back (S_stats_tx_wakes, :141).
     0x86ca4 - 0x86cb4, 0x86e7c - 0x86e88 the check of the 4-byte load at s + 160.
     0x86cb8 - 0x86cd8, 0x86e8c - 0x86e98 the check of the 4-byte store at s + 212; a1 = the 4-byte signed load at
                      s + 160 (S_host_counter, 0x86cc8); the store of 1 at s + 212 (S_inflight = 1, :113).
     0x86cd4 - 0x86cec, 0x86e9c - 0x86ea8 the check of the 4-byte store at s + 1744, then the store of the low 32 bits
                      of a1 (S_inflight_counter = the host counter, :114).
     0x86cf0 - 0x86d04, 0x86eac - 0x86eb8 the check of the 4-byte store at s + 1748, then the store of 0
                      (S_inflight_retries = 0, :115).
     0x86d08 - 0x86d1c, 0x86ed0 the check of the 8-byte store at s + 1752, then the store of now
                      (S_inflight_sent_us = now, :116). The world is now wake_w3 B1 e2 now (B1 send_control's world).
     0x86d20 - 0x86d2c a1 = 1 (S_WAKING), a2 = 1 (R_WAKE), a0 = s; the call of set_state (0x872cc = transportb_sigma
                      TB_set_state) at 0x86d2c, return address 0x86d30 (:142).
     0x86d30          a0 = 0 (DIGINET_OK, :144).
     0x86d34 - 0x86d54 shadow bytes 4..11 = 0xf8 (e2 out of scope again).
     0x86d58 - 0x86d60 the header word 0x45e0360e stored at frame (every path).
     0x86d64          s2 = 0 goes to 0x86db8 (the real-stack arm; not taken).
     0x86d68 - 0x86db4 the release: the frame's 16 shadow bytes (128 bytes) = 0xf5 (released); a1 = the 8-byte load
                      at s2 + 120 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a1 (YG0d.v astack_free_law); to 0x86df8.
     0x86db8 - 0x86df4 the real-stack arm's release: shadow bytes 0..15 = 0.
     0x86df8 - 0x86e30 sp = s0 - 128, ra and s0 .. s10 loaded back, sp = sp + 128, return. a0 = r (-1, -10,
                      send_control's negative result, or 0); a1 .. a7 at the return are not stated.
     0x86e34          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path.
     0x86e38 - 0x86ed0 the slow paths of the checks and the 13 error calls.
   No tail jump: the calls are jal with link (the stack malloc, send_control, the memcpy, set_state); every j is
   inside the function, and the function ends with ret.
   The model and the code: the tests at 0x86b7c and 0x86ba4 are diginet_session_wake_m's (S_desk_known Bw and
   S_foreign Bw against 0, each a 32-bit signed read); the stores at s + 18256, s + 140, s + 144, s + 152 are
   set_S_stats_refused (u64 of the 64-bit sum), set_S_e1_named_us, set_S_wake_acked, set_S_wake_sent_us (wake_w1);
   the call at 0x86c54 is send_control_m at wake_w1 Bw now with cmd DIGINET_CMD_WAKE and ack 0, whose result
   (B1, (r, e2)) gives a0 = r, and when r >= 0 e2 = the 60 bytes f it built (send_control_cg.v's X: the 60 bytes at
   kp and put 8 60 at klp); the memcpy and the stores at s + 1736, s + 18224 are set_S_inflight_frame B1 e2,
   set_S_inflight_len (length e2 = 60), set_S_stats_tx_wakes (wake_w2), the stores at s + 212 .. s + 1759 are
   inflight_start_m's with the counter S_host_counter (wake_w2 B1 e2) (wake_w3), each a tw_write (the memcpy a
   tw_fill) inside g_s's payload; the call at 0x86d2c is set_state_m at wake_w3 B1 e2 now with S_WAKING and R_WAKE
   (wake_model), whose notice is wake_ntc Bw (sstate_ntc (wake_w3 B1 e2 now) S_WAKING R_WAKE, whose old field is
   S_state (wake_w3 B1 e2 now) = S_state Bw: no store before it touches g_s.state, and io_send stores no byte of
   g_s). wake_wr and wake_ntc read S_state Bw and GOT_n Bw, so the walk needs the model fact that send_control_m keeps
   S_state and GOT.n (send_raw_m stores only stats.tx_frames, TSess.v; io_send_m stores no byte of g_s and not GOT.n,
   TCb.v, as io_send_cg.v iosend_wr says): acall_kept_g keeps no byte of G, so it comes from the model:
   lib/TModel/TOpsKeep.v send_control_m_keeps at wake_w1 Bw now (S_state and GOT_n of B1 are those of wake_w1 Bw
   now, which are Bw's; its premise length (wake_w1 Bw now) = W_LEN is tw_at's, TWorldG.v tw_len, because the three
   setters of wake_w1 keep the length). The model's None
   cases are send_control's and set_state's, ruled out by the model premise; the code's one trap word and its
   real-stack arm are ruled out by facts outside the model (the constant s, the side-stack premises).
   Trap path (the unimp word at 0x86e34, from 1 branch) and the fact that refutes it: 0x86b60 (s & 7 <> 0): s =
   0x5df640, a multiple of 8.
   Error paths (13 calls; no abort) and the facts that rule them out:
     __asan_report_load4 (0x59644) at 0x86e48 (s + 116), 0x86e58 (s + 136), 0x86e88 (s + 160);
     __asan_report_store4 (0x59964) at 0x86e68 (s + 140), 0x86e78 (s + 144), 0x86e98 (s + 212), 0x86ea8 (s + 1744),
       0x86eb8 (s + 1748);
     __asan_report_load8 (0x596e4) at 0x86ebc (s + 18256), 0x86ecc (s + 18224);
     __asan_report_store8 (0x59a04) at 0x86ec0 (s + 152), 0x86ec4 (s + 1736), 0x86ed0 (s + 1752).
     Each guards a naturally aligned access inside g_s's payload [0x5df640, 0x5e3d98) (2283 whole granules), whose
     shadow bytes are 0 (trans_wake_cells, read at each AR state by DgnTransportBCg.v decode_zshadow_rd), so k = 0.
     The memcpy's own checks (aintrin_realizes' pre, through TransportGCg.v gx_intrin_at): the destination
     [s + 216, s + 276) lies in g_s's payload (bytes of G, writable through the G journal; shadow 0 by
     trans_wake_cells); the source [e2, e2 + 60) lies in the frame this function took, its shadow bytes 4..11 = 0,
     .., 0, 4 since 0x86c3c, kept by send_control's acall_kept_g (the frames' shadow clause) and visible; the two
     ranges are apart (a frame byte is outside the image: AR_laws' al_client_img).
   Writes: g_s's eleven fields (bytes of G); its own machine frame (the 8 zero bytes at sp at 0x86a3c, the saves at
   0x86a40 - 0x86a6c, the frame word at s1 + 16; e2_len at s1 + 24, which send_control stores); its own side-stack
   frame, that frame's shadow bytes and its flag byte; send_control's stores outside wake's frames
   (g_s.stats.tx_frames and io_send's iosend_wr 60, bytes of G); set_state's stores (set_state_cg.v sstate_wr: g_s's
   state and notice's N_STATE stores, bytes of G). No byte of a caller's frame or block is written, so wake_wr is the
   written range. The G kit for the own frame is set_state_cg.v's (TransportGCg.v dk_kept_own_g with dkg_nf and
   dkg_nf_sep, dk_kept_trans_nf_g (send_control's and set_state's acall_kept_g are stated at their call states, whose
   frames are the own frame :: frames Sc), dkg_frame_al64, gx_intrin_at (the memcpy) and dk_kept_frame_byte_g; image
   B's CanKit.v can_stack_malloc_at and can_flag_store_pi read inside the G journal through gx_lift).
   send_control's post is transport_cg_post_out with the out cell [(klp, 8)], so its acall_kept_g is read at gover
   [(klp, 8)] mem2 memc: the walk chains dk_kept_trans_out_g and transport_cg_post_out_fold (TransportGCg.v) with
   dk_kept_trans_nf_g, whose NF holds [klp, klp + 8) besides the own frame (sendctl_wr kp klp holds klp, which is in
   neither wake_wr nor the own frame).
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_1 as astack_malloc_realizes ... WAKE_CID (with pc_stack_malloc (as_code B) WAKE_CID =
       transportb_sigma TB___asan_stack_malloc_1): count_cid 1 (frames Sc) < fs_frames 1 from the class-1 premise.
     send_control as send_control_cg.v transport_send_control_cg at transportb_sigma TB_send_control (call at
       0x86c54; a G-form callee composed in the same G journal, no gx_call_cg): the journal at the call state (the own
       frame live); ra = 0x86c58; gp, tp kept; a0 = SENDCTL_S, a1 = cmd = 0xe2 < 2 ^ 8, a2 = bv_swrap 32 0 = 0
       (ack = 0), a3 = kp = e2, a4 = klp = s1 + 24; the realigned sp is 32-aligned, sp0 - STK <= sp' - SENDCTL_STK
       (sp' >= sp - 144, WAKE_STK = 144 + SENDCTL_STK), sp' <= sp0; the keep disjunction's right part: 0 < kp;
       decode_in_fake of [e2, e2 + 60) at the call state ([frame + 32, frame + 92) inside the 128 bytes of a frame of
       its frames); transport_twr_ok_g at sp': each byte an awr_byte of the own frame list after the stack malloc
       (in_frames), not owned, below alloc_ceiling (so outside the ESTACK window); decode_rd_ok (the bytes present by
       astack_malloc_realizes, shadow bytes 4..11 = 0, .., 0, 4, their hull visible); decode_off_win at SENDCTL_STK
       (the frame lies below alloc_ceiling, send_control's window above it); apart from G (a frame byte is outside
       the image); K = the 60 bytes there, garr8 (present, by the stack malloc); 0 < klp (image B's send_control
       statement asks it: its UBSan null check of keep_len traps on klp = 0; klp lies in the machine stack) and
       klp mod 8 = 0 (s1 is 32-aligned); transport_twr_ok_g of [klp, klp + 8) (inside the journal's stack window, at
       or above sp', so outside the ESTACK window); decode_rd_ok (the stack's shadow is 0 at every AR state: YG0n.v
       zero_shadow_ranges' first row [ly_stk_lo, ly_stk_hi); CanKit.v can_stack_addressable); decode_off_win at
       SENDCTL_STK (sp' <= klp); apart from G (G lies below the stack); KL = the 8 bytes there, garr8 (the stack
       window's bytes are present: the journal's stack clause); kp + 60 <= klp or klp + 8 <= kp (different regions: a
       frame byte lies below alloc_ceiling, the stack above it); tw_at at wake_w1 Bw now (G kept through the stack
       malloc: gx_kept_of_acall_kept with gx_ok, gx_noerrno; then the three tw_writes); g_fail_next (wake_w1 Bw now)
       <= 1 (the stores do not touch it: g_fail_next Bw <= 1); send_control_m timg_B TF (wake_w1 Bw now)
       DIGINET_CMD_WAKE 0 = Some (B1, (r, e2)) (the model premise through wake_model, on the path where
       S_desk_known Bw <> 0 and S_foreign Bw = 0); trans_rom_view_rd at the call memory (no store of wake reaches a
       read-only byte, and the stack malloc's acall_kept keeps every TRANS_RO_RD byte: trans_ro_rd_scoped, from
       trans_ro_rd_unowned and trans_rom_no_errno); run invariants (1) and (4) at wake_w1 Bw now: the premises at Bw
       (wake_w1 changes no byte of M, g_cmd or g_ncmd); count_cid 2 at the call state = count_cid 2 (frames Sc) (the
       own frame is of class 1), and + 1 < fs_frames 2 is the class-2 premise; st_nev S + k + SENDCTL_EV <= EV_MAX
       (WAKE_EV = SENDCTL_EV + SSTATE_EV, the stack malloc records no event). Its X: a0 = r, tw_at at B1,
       g_fail_next B1 <= 1, and when r >= 0 (so e2 <> []) the 60 bytes at kp holding e2 and the 8 bytes at klp
       holding put 8 60, both read at the returned memory; its acall_kept_g is read at gover [(klp, 8)] mem2 memc,
       because klp lies at or above alloc_ceiling outside send_control's window, where acall_kept_g's first clause
       keeps every byte.
     __asan_memcpy as aintrin_realizes ... OCpy (transportb_sigma TB___asan_memcpy), call at 0x86c6c (r >= 0, n = 60
       < 2 ^ 32), through TransportGCg.v gx_intrin_at (above); after it the 60 bytes at s + 216 are e2, and tw_at
       holds at set_S_inflight_frame B1 e2 (tw_fill inside g_s's payload).
     set_state as set_state_cg.v transport_set_state_cg at transportb_sigma TB_set_state (call at 0x86d2c; a G-form
       callee composed in the same G journal, no gx_call_cg): the journal at the call state (the own frame live);
       ra = 0x86d30 (ret_ok, 4096 <= ra); gp, tp kept; a0 = SSTATE_S, a1 = st = 1 (S_WAKING), a2 = why = 1 (R_WAKE),
       0 <= st, why < 2 ^ 31; sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - SSTATE_STK: sp' >=
       sp - 144 and WAKE_STK >= 144 + SSTATE_STK; sp' <= sp0; tw_at at wake_w3 B1 e2 now (send_control's X, the
       memcpy's tw_fill, then the tw_writes); g_fail_next (wake_w3 B1 e2 now) <= 1 (send_control's X; the stores of
       :139-141 and :113-116 do not touch the byte); set_state_m timg_B TF (wake_w3 B1 e2 now) S_WAKING R_WAKE =
       Some (Bw', tt) (the model premise through wake_model, on the path where r >= 0); trans_tframe_at TF at
       SSTATE_STK: wake's trans_tframe_at at WAKE_STK, carried: TF's bytes and their shadow are unchanged (wake_apart
       for the g_s stores; across send_control, trans_src_ok_kept over the clauses of its acall_kept_g, which reach
       TF because trans_tf_off_g puts it outside G and wake_apart outside send_control's stores outside wake's
       frames; the own frame is a fresh frame, apart from TF's placement, and e2_len lies in wake's window, which
       decode_off_win puts TF outside; the memcpy keeps every byte outside its destination and ESTACK bytes; the
       record facts of the holds statement for the stack malloc's acall_kept), and set_state's window lies inside
       wake's; trans_rom_view_rd at the call memory (as for send_control, and across send_control's acall_kept_g,
       whose image clause keeps every TRANS_RO_RD byte outside G, the owned statics and errno; the memcpy keeps every
       byte outside its destination and ESTACK bytes); sstate_apart TF (wake_w3 B1 e2 now) S_WAKING R_WAKE:
       wake_apart, since sstate_wr (wake_w3 B1 e2 now) S_WAKING R_WAKE lies inside wake_wr Bw (S_state (wake_w3 B1 e2
       now) = S_state Bw, and notice_wr at set_state's notice world is notice_wr Bw (wake_ntc Bw): GOT.n is the same,
       as neither wake nor send_control stores a byte of GOT.n; the model fact above); count_cid 2 at the call state
       = count_cid 2 (frames Sc) < fs_frames 2 (the class-2 premise; send_control's frames are released); st_nev: the
       event count after send_control plus SSTATE_EV, inside WAKE_EV. Its X: tw_at at Bw' and g_fail_next Bw' <= 1.
   send_control's and set_state's own record facts are premises of their holds statements.
   Stack: 128 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, __asan_memcpy), send_control's SENDCTL_STK or set_state's SSTATE_STK:
   WAKE_STK = 144 + SENDCTL_STK (wake_stk_eq).
   The differences from image A's form (lib/A/Prog/diginet_session_wake_cg.v), each forced by image B's code: the
   addresses; the UBSan alignment check of s and its trap word are new (image A's code has no trap of its own), and
   the trap is refuted by the constant s, a fact image A's form already has; set_state is a function on image B
   (image A inlines it here), so set_state's notice, its memset, its state store and its notify call are set_state's
   (set_state_cg.v), and the holds statement takes set_state's contract in place of the contracts of
   __asan_memset and notice; the own side-stack frame holds e2 only and is of class 1 (__asan_stack_malloc_1), so
   the count premise is count_cid 1 (frames Sc) < fs_frames 1 and count_cid 2 (frames Sc) + 1 < fs_frames 2 in place
   of image A's count_cid 2 (frames Sc) + 2 < fs_frames 2 (above), WAKE_CID is 1 (image A's wake_cid_sendctl,
   WAKE_CID = SENDCTL_CID, does not hold) and WAKE_EV is SENDCTL_EV + SSTATE_EV; e2_len lies at s1 + 24 and the frame
   word at s1 + 16 (image A: s1 + 16 and s1 + 8); image B's send_control statement asks 0 < klp, which the machine
   stack gives. wake_wr names a field's bytes by lib/B/Prog/m_set_cg.v twb_fld (image A's m_lost_cg.v twa_fld) and
   io_send's by image B's io_send_cg.v iosend_wr; wake_wr and wake_ntc are image A's otherwise (wake_ntc Bw is
   set_state_cg.v's sstate_ntc Bw S_WAKING R_WAKE: wake_ntc_sstate).

   The callers (each with the return address after its jal):
   - LLVMFuzzerTestOneInput at 0x81af0 (return 0x81af4): a0 = 0x5df640 (&g_s, formed at 0x81ae8 - 0x81aec), a1 = the
     8-byte load at 0x81ae0; it holds a class-2 frame of its own (__asan_stack_malloc_2 at 0x81310, a0 = 256), so
     its class-2 count premise leaves room for that frame and send_control's two.
   - on_announce at 0x88160 (return 0x88164): a0 = s4 (its own a0, &g_s, 0x87d30), a1 = s5 (the 8-byte load at
     s1 + 24 at 0x880d4: its a2, stored there from s7 at 0x87f0c), on its path of :204-205 (S_state = S_IDLE and
     S_cfg_auto_wake <> 0); it holds a class-3 frame of its own (__asan_stack_malloc_3 at 0x87d3c).
   Each supplies its G journal, tw_at, g_fail_next, the model premise (its branch of the model), trans_tframe_at,
   wake_apart and trans_tf_off_g of its TF (the last two from its plain tframe_at's off_world clause),
   trans_rom_view_rd, the two run invariants, count_cid 1 (frames Sc) < fs_frames 1 and count_cid 2 (frames Sc) + 1
   < fs_frames 2.
   Image B inlines inflight_start into diginet_session_wake (walked here) and has set_state as a function
   (set_state_cg.v). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
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
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_session_wake's frame (`sp = sp - 128` at TB_diginet_session_wake), the at most 0x10 bytes of
   `sp = sp & -32` (0x86a74) below it, and the largest stack a callee uses below the realigned sp: ESTACK for
   __asan_stack_malloc_1 and __asan_memcpy (YG0d.v ecall_pre), send_control's SENDCTL_STK, set_state's
   SSTATE_STK. *)
Definition WAKE_FRAME : Z := 128.
Definition WAKE_ALIGN : Z := 0x10.
Definition WAKE_STK : Z := WAKE_FRAME + WAKE_ALIGN + Z.max ESTACK (Z.max SENDCTL_STK SSTATE_STK).
Lemma wake_stk_eq : WAKE_STK = WAKE_FRAME + WAKE_ALIGN + SENDCTL_STK.
Proof. reflexivity. Qed.
(* No allocator event: send_control and set_state record none, and the class-1 stack malloc and its release record
   none (YG00.v stack_malloc, stack_free). *)
Definition WAKE_EV : Z := SENDCTL_EV + SSTATE_EV.
(* The side-stack class (a0 = 128 at 0x86aa0, the call of __asan_stack_malloc_1 at 0x86aa4): class 1, not
   send_control's and set_state's class 2, hence the two count premises. *)
Definition WAKE_CID : Z := 1.
Lemma wake_cids : WAKE_CID = 1 /\ SENDCTL_CID = 2 /\ SSTATE_CID = SENDCTL_CID.
Proof. repeat split; reflexivity. Qed.
(* Its first argument: g_s's base in image B. *)
Definition WAKE_S : Z := TB_g_s.
(* The addresses of the g_s fields the code reads or writes (s + 116, s + 136, s + 18256, s + 140, s + 144, s + 152,
   s + 216, s + 1736, s + 18224, s + 160, s + 212, s + 1744, s + 1748, s + 1752). *)
Lemma wake_addrs :
  WAKE_S = 0x5df640 /\
  WAKE_S + (TW.A_S_desk_known - TW.OFF_g_s) = 0x5df6b4 /\
  WAKE_S + (TW.A_S_foreign - TW.OFF_g_s) = 0x5df6c8 /\
  WAKE_S + (TW.A_S_stats_refused - TW.OFF_g_s) = 0x5e3d90 /\
  WAKE_S + (TW.A_S_e1_named_us - TW.OFF_g_s) = 0x5df6cc /\
  WAKE_S + (TW.A_S_wake_acked - TW.OFF_g_s) = 0x5df6d0 /\
  WAKE_S + (TW.A_S_wake_sent_us - TW.OFF_g_s) = 0x5df6d8 /\
  WAKE_S + (TW.A_S_inflight_frame - TW.OFF_g_s) = 0x5df718 /\
  WAKE_S + (TW.A_S_inflight_len - TW.OFF_g_s) = 0x5dfd08 /\
  WAKE_S + (TW.A_S_stats_tx_wakes - TW.OFF_g_s) = 0x5e3d70 /\
  WAKE_S + (TW.A_S_host_counter - TW.OFF_g_s) = 0x5df6e0 /\
  WAKE_S + (TW.A_S_inflight - TW.OFF_g_s) = 0x5df714 /\
  WAKE_S + (TW.A_S_inflight_counter - TW.OFF_g_s) = 0x5dfd10 /\
  WAKE_S + (TW.A_S_inflight_retries - TW.OFF_g_s) = 0x5dfd14 /\
  WAKE_S + (TW.A_S_inflight_sent_us - TW.OFF_g_s) = 0x5dfd18.
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
(* set_state's notice for this call, at a world with wake's old state. *)
Lemma wake_ntc_sstate : forall Bw : list byte,
  wake_ntc Bw = sstate_ntc Bw TS0.DIGINET_S_WAKING TS0.DIGINET_R_WAKE.
Proof. intro Bw. reflexivity. Qed.
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
   io_send_cg.v iosend_wr 60); and, when the state changes, set_state's (set_state_cg.v sstate_wr: g_s's state and
   notice's stores, notice_cg.v notice_wr: for an N_STATE notice, GOT.t[GOT.n] when 0 <= GOT.n < TRANS_MAX, and
   GOT.n; no store before set_state touches GOT.n, so it is GOT_n Bw). *)
Definition wake_wr (Bw : list byte) (a : Z) : Prop :=
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_refused 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_e1_named_us 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_wake_acked 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_wake_sent_us 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight_frame SENDCTL_F a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight_len 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_tx_wakes 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight_counter 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight_retries 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight_sent_us 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_tx_frames 8 a \/
  iosend_wr SENDCTL_F a \/
  (TW.S_state Bw <> TS0.DIGINET_S_WAKING /\
   (twb_fld TW.OFF_g_s TB_g_s TW.A_S_state 4 a \/ notice_wr Bw (wake_ntc Bw) a)).

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. set_state reads TF (its notice's callees) after the g_s stores (set_state_cg.v sstate_apart). *)
Definition wake_apart (Fr : option TI.tframe) (Bw : list byte) : Prop :=
  forall x, wake_wr Bw x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow
   (lib/B/YF0m.v Tfib_zero_shadow row (0x5df640, 0x5e3d98 - 0x5df640)). The instrumented checks of the accesses at
   s + 116 .. s + 18263 read it, and the memcpy's destination s + 216 lies in it. *)
Definition trans_wake_cells (B : asyms) : Prop := decode_zshadow_at B WAKE_S (WAKE_S + TW.SZ_g_s).

Section wake. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range wake_wr Bw,
   no meter charge (the side-stack frame changes st_fs only), and X: a0 = r (sign-extended), the world relation at
   the model's world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this
   function takes is released. *)
Definition transport_wake_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs WAKE_STK WAKE_EV 0 (wake_wr Bw)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 r /\
       tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_diginet_session_wake_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 WAKE_S -> YK11.getr regs 11 = w64 now ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - WAKE_STK -> spZ regs <= sp0 ->
    0 <= now < 2 ^ 64 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.diginet_session_wake_m timg_B TF Bw now = Some (Bw', r) ->
    trans_tframe_at B lyc Sc W memc regs WAKE_STK TF ->
    trans_tf_off_g TF ->
    trans_rom_view_rd W memc ->
    wake_apart TF Bw ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    count_cid WAKE_CID (frames Sc) < fs_frames WAKE_CID ->
    count_cid SENDCTL_CID (frames Sc) + 1 < fs_frames SENDCTL_CID ->
    st_nev S + k + WAKE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_wake_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The statement the walk will prove: the class-1 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the record facts that no byte of G and
   no TRANS_RO_RD byte is an owned static or errno (they carry TF's trans_src_ok, G and the TRANS_RO_RD bytes across
   the stack malloc's acall_kept and send_control's acall_kept_g; DgnTransportBCg.v G_HARNESS_gx_ok /
   G_HARNESS_gx_noerrno give gx_ok and gx_noerrno from the first two), the allocator, meter and side-stack laws, and
   the contracts of __asan_stack_malloc_1, send_control, __asan_memcpy and set_state give the contract at
   TB_diginet_session_wake. *)
Definition transport_diginet_session_wake_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) WAKE_CID = transportb_sigma TB___asan_stack_malloc_1 ->
  transport_cells B -> trans_wake_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B WAKE_CID) ->
  (forall fx' : YK11.FPState, @transport_send_control_cg fx' rc B MT (transportb_sigma TB_send_control)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) ->
  transport_diginet_session_wake_cg (transportb_sigma TB_diginet_session_wake).
End wake.
