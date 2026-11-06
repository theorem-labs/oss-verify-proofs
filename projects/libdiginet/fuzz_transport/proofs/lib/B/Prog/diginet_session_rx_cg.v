(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module names changed; 358 of its 430 lines of code are new or changed and 371 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickCut.v, with its module paths and module names changed; 203 of its 254 lines of code are new or changed and 379 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_tick_cg.v, with its module names changed; 149 of its 219 lines of code are new or changed and 184 lines of the source are left out. *)
(* diginet_session_rx_cg: image B's ASan walk contract of diginet_session_rx (transport/src/diginet_session.c:263-318,
   with session_lost (:160-165) inlined and set_state (:79-86) CALLED; model lib/TModel/TSess.v diginet_session_rx_m)
   on fuzz_transport.asan-ubsan (41113a03c82f) at 0x87784 = transportb_sigma TB_diginet_session_rx, size 1348, as
   STATEMENTS only (no proof). It stores into g_s, a harness global, takes a class-1 side-stack frame for its local
   struct diginet_frame f, calls diginet_frame_parse (a donor-form callee) with f in that frame, the bcmp wrapper, the
   leaf diginet_mac_is_digidesign, __asan_memcpy, and on_announce, on_ack, set_state, on_data and
   diginet_session_tick (G-form callees) while that frame is live, so it is a G-form caller-journal walk: the
   caller's journal is lib/A/W_journalG.v ajournal_gx (image-free) over G = lib/B/TransportGB.v G_HARNESS_B with no
   out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post (image-free; acall_kept_g
   over G_HARNESS_B). Form: image A's lib/A/Prog/diginet_session_rx_cg.v at image B's names; the G walk with a
   side-stack frame of its own is image B's on_ack_cg.v and diginet_session_tick_cg.v.

   The contract. a0 = s = &g_s = 0x5df640 (TWorldB.v TB_g_s); a1 = buf, holding the bytes b; a2 = their length;
   a3 = now (a uint64_t). buf is receive's heap block (fuzz_transport.c:1021) or diginet_session_poll's local
   uint8_t[1514] in its class-5 side-stack frame, so it is placed by trans_src_ok, lies outside this call's stack
   window and holds no byte of G. TF is the current heap frame (check_state_data_cg.v trans_tframe_at at this call's
   window); the read-only bytes the callees read are the image's (trans_rom_view_rd). The memory relates to the world
   Bw by image B's world relation (TWorldG.v tw_at at TWorldB.v TMAP_B, read through aview), g_fail_next Bw <= 1, and
   diginet_session_rx_m timg_B TF Bw b now = Some (Bw', r). No byte the call stores is a byte of TF (srx_apart), and
   no byte of TF is a byte of G (check_state_data_cg.v trans_tf_off_g). Class 1 of the side stack has two free
   frames (its own, and diginet_session_wake's under on_announce, taken while its own is live); class 3 has one
   (on_announce's), class 5 one (diginet_session_tick's), class 0 one (send_data's under tick) and class 2 three (the
   deepest chain: under on_data its own, send_control's and diginet_body_check's. Under on_announce
   diginet_session_wake's send_control and diginet_body_check need two, and set_state one; on_ack needs two, its own
   and set_state's under maybe_online; set_state on the disconnect path one; diginet_session_tick one). The function
   returns to ra with a0 = r (sign-extended), the callee-saved registers kept, no allocator event and no meter
   charge (its side-stack frame changes the state's st_fs only: ameter_fs_laws), its side-stack frame released (the
   caller's frames exactly), the caller's blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at or
   above alloc_ceiling outside the call's stack window [sp - SRX_STK, sp), the image bytes outside G, the owned
   statics and errno, the caller's block and frame bytes outside srx_wr b), the world relation at Bw', and
   g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/U/Prog/T/diginet_session_rx_c.v): a0 = W_BASE_UBSAN + OFF_g_s ->
   a0 = TB_g_s; a1 = buf, a2 = the length of b kept; a3 = now, 0 <= now < 2 ^ 64 kept; bytes_at rsegs m bufp b ->
   garr8 of b at buf; arg_blk sp FRAME bufp (length b) -> 0 < buf (its buf + length b < 2 ^ 64 comes from
   trans_src_ok itself: a heap block lies below alloc_ceiling, and every other case carries decode_rd_ok's
   buf + length b <= 2 ^ 63), trans_src_ok and decode_off_win for its placement and the window part, and
   srx_buf_off_g, its off_world part (no byte of [buf, buf + length b) is a byte of G; the three session callees take
   it inside on_ack_cg.v trans_dframe_at); wmem -> tw_at; g_fail_next B <= 1 kept as a premise (the code neither
   reads nor writes g_fail_next; the callees' statements ask it) and the post's g_fail_next B' <= 1 kept in X (from
   the premise on the paths that call none of them, else from the X of the last one); diginet_session_rx_m verbatim
   at timg_B; timg_ubsan -> timg_B; tframe_at -> trans_tframe_at at SRX_STK, and its off_world clause -> two facts,
   since check_state_data_cg.v trans_tframe_at drops that clause: srx_apart, no byte the call stores is a byte of TF
   (maybe_online_cg.v maybeon_apart's form), and trans_tf_off_g (check_state_data_cg.v), no byte of TF is a byte of
   G. diginet_session_rx needs trans_tf_off_g for its own walk: it carries TF across the switch callee (on_announce
   at 0x87b78, on_ack at 0x87b94, set_state at 0x87c08 or on_data at 0x87c1c), a G-form callee that writes G, to
   diginet_session_tick (call at 0x87c4c), which takes TF: the switch callee's acall_kept_g keeps the image bytes
   outside G only, and its X pins G only to the model world, so it carries no byte of a TF inside G. The statements
   of on_announce, on_ack and on_data ask it too; relro_img -> trans_rom_view_rd; stk, lo + FRAME <= sp,
   sp mod 16 and w_off_stack -> the journal's window premises; mem_inv is dropped. The post's
   munch, wmono, stk and mem_inv -> transport_cg_post (the journal at the return, acall_kept_g over srx_wr b); wmem ->
   X's tw_at; the result register -> X's a0 = r.
   Premises the plain contract does not have:
   - the five frame counts: count_cid 1 (frames Sc) + 1 < fs_frames 1 (its own class-1 frame, and
     diginet_session_wake's under on_announce: on_announce's statement asks count_cid 1 (frames Sc') < fs_frames 1
     at its call state, whose frames Sc' are the own class-1 frame :: frames Sc; with it __asan_stack_malloc_1
     returns a frame, astack_malloc_realizes, so the real-stack arm is not taken), count_cid 3 (frames Sc) <
     fs_frames 3 (on_announce's), count_cid 5 (frames Sc) < fs_frames 5 (diginet_session_tick's), count_cid 0
     (frames Sc) < fs_frames 0 (send_data's under tick) and count_cid 2 (frames Sc) + 2 < fs_frames 2 (the deepest
     class-2 chain: under on_data its own frame, then send_control's, then diginet_body_check's). Each callee counts
     at the state whose frames are the own class-1 frame :: frames Sc, which has the same count at every class but 1
     (srx_cid_callees).
   - srx_apart and trans_tf_off_g (above).
   - the run invariants carried (below).
   - in the holds statement: trans_srx_cells (g_s's zero shadow and the rest of BROADCAST's shadow group), the
     side-stack laws, and trans_g_unowned, trans_g_no_errno, trans_ro_rd_unowned and trans_rom_no_errno: they carry
     the trans_src_ok of TF, of the bytes at buf and of the guarded OW.dn range across the stack malloc
     (DgnTransportBCg.v trans_src_ok_inner, the stack malloc adding the own frame and keeping the blocks, their bytes
     kept by its acall_kept and their decode_rd_ok by trans_rd_ok_sh, each range apart from the fresh frame and that
     frame's shadow: trans_src_ok_disj_own) and across diginet_frame_parse's acall_kept (through gx_call_cg;
     trans_src_ok_acall), and TF's across the switch callee's acall_kept_g to diginet_session_tick
     (trans_src_ok_kept over its clauses, TF lying outside G by trans_tf_off_g; trans_src_ok_acall_g asks every byte
     of G to be kept, which no session callee gives; the bytes at buf and the guarded OW.dn range are handed only to
     the switch callee, so neither crosses a G-form callee), the TRANS_RO_RD bytes (trans_rom_view_rd for every
     callee, and the bcmp range BROADCAST), and G (TransportGCg.v gx_kept_of_acall_kept and gx_call_cg with gx_ok and
     gx_noerrno, which DgnTransportBCg.v G_HARNESS_gx_ok and G_HARNESS_gx_noerrno give from the first two), as image
     B's diginet_session_tick_cg.v takes them.
   Run invariants carried (on its own Bw), each a premise of a callee it reaches, and each read at a world that
   differs from Bw only in g_s's desk_mac, desk_known, stats.rx_frames and last_rx_us (the two stores of :290-291 and
   the two of :296-297, the only stores the code makes before a switch callee; on the :313-315 path the call of
   diginet_session_tick also follows the store of g_s.stats.rx_ignored at 0x87c40, a field no invariant reads),
   none of which they read:
   - (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME (io_send's, through send_control and send_data:
     on_announce, on_data and diginet_session_tick ask it);
   - (2) TW.S_queue_len Bw i <= DIGINET_CMD_MAX_LEN for every i < S_queued Bw (take's, through
     diginet_session_tick);
   - (4) every PENDING command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX (check_latest_sent's, through
     io_send: on_announce, on_data and diginet_session_tick ask it);
   - (5) 1 <= TW.S_cfg_max_cmds Bw and 1 <= TW.S_cfg_max_body Bw (take's, through diginet_session_tick), in
     diginet_session_tick_cg.v's two-premise form;
   - with (2) and (4), their index bounds TW.S_queued Bw <= TC.QUEUE_MAX and TW.g_ncmd Bw <= TC.CMDS_MAX
     (diginet_session_tick's premises, and on_announce's for g_ncmd; diginet_session_tick_cg.v says why (2) and (4)
     cannot be carried across a callee's stores without them). Image B's disconnect arm calls set_state (0x87c08)
     before diginet_session_tick (0x87c4c), and set_state's N_STATE notice stores GOT.t[GOT.n] and GOT.n, GOT bytes
     that are g_cmd[s] bytes for s >= CMDS_MAX (GOT.t[5].old is A_Cmd_st 1131), as image A's session_lost's notice
     does; set_state itself carries no invariant and takes neither bound. The index is read by the callees, not by
     this function's code (take's queued and queue[i].len, check_latest_sent's g_cmd[s].len: diginet_session_tick_cg.v).
     No function this one calls writes g_ncmd, and take only lowers queued, so both hold at each call; the caller has
     them from the plain run (lib/TSim/Agree.v d3_ncmd and d3_ops, OPS_MAX = CMDS_MAX; lib/TSim/Deadline.v
     queued_le);
   - (3) check_state_data's, which notice asks for a notice of kind N_DATA: on_data_cg.v states it guarded by
     ondata_dup Bw b = false and fr_keepalive b = false, at its own world and window. Only on_data reaches an N_DATA
     notice, and diginet_session_rx_m reaches on_data exactly on the accept path of a data frame (srx_model): fr_code
     b = 0 (:268), srx_mac_bad Bw b = false (:273-277), S_desk_known Bw <> 0 with memeq 6 (fr_src b) (S_desk_mac Bw)
     = true (:278-282; with no desk known only an announce goes on, :284-285), S_state Bw <> S_CLOSED (:293-294) and
     fr_cmd b = DIGINET_CMD_DATA (:306). So this statement carries the same pair of facts guarded by exactly those
     tests as well, at Bw and at SRX_STK (on_data's window lies inside this one; each test reads Bw, since with a desk
     known the world srx_accept is handed is Bw; and the fields OW.dn, GOT.ndata, S_desk_counter_valid and
     S_desk_counter that the guard and the range read are untouched by the two stores of :296-297 before the call).
     A weaker guard would be false for reachable inputs: for a data frame the session drops (e.g. one addressed to
     neither the host nor BROADCAST) the harness's m_rx_m records no OW.dn entry either, op_begin_m leaves OW and GOT
     zero, and the range would be [0, fr_body_len b), which trans_src_ok does not admit when fr_body_len b > 0. A
     caller has the guarded pair from the plain sim's facts of the accepted data frame (lib/TSim/RxData.v: m_rx's
     OW.dn entry at the frame's tf_addr + 30 with the frame's body length). The bound n_body_len < 2 ^ 32 is not a
     premise: the walk has it from the frame, as on_data_cg.v says.
   on_announce, on_ack and set_state carry no other invariant. diginet_session_rx's own instrumented accesses are at
   fixed offsets of g_s (s + 112 .. s + 119, s + 168 .. s + 171, s + 176 .. s + 183, s + 212 .. s + 215,
   s + 18152 .. s + 18159, s + 18184 .. s + 18191); its bcmp ranges are [f, f + 6), [f + 6, f + 12), [s, s + 6),
   [s + 120, s + 126) and [0x21160, 0x21166); its memcpy moves 6 bytes from f + 6 into g_s.desk_mac; so its code
   needs no bound that the model does not give.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 1348 code bytes, the 16 bytes of its frame
   description at 0x113c8 and the 6 bytes of BROADCAST at 0x21160 are equal in both files), 337 words; s = s4,
   buf = s8 (to 0x87a68, where s8 becomes s + 116), len = s7 (to 0x87900, where s7 becomes f + 6), now = s3, the
   frame = s10 = s2, f = s6 = frame + 32, s11 = the shadow base, s9 = (frame >> 3) + s11 (the frame's first shadow
   byte), s5 = s + 18152 (g_s.stats):
     0x87784 - 0x877c0 sp = sp - 160; 0x87788 stores 8 zero bytes at sp; ra at sp + 152, s0 .. s11 at sp + 144 ..
                      sp + 56, loaded back at 0x87a2c - 0x87a5c; s0 = sp + 160 (the entry sp, kept to 0x87a28).
     0x877c4 - 0x877d4 sp = sp & -32 (at most 0x10 below entry - 160); s1 = the realigned sp; s3 = now, s7 = len,
                      s8 = buf.
     0x877d8 - 0x877f0 a2 = the 8-byte load of the GOT word 0xa3d48 (it holds 0xac680), then the 4-byte load of the
                      flag word at 0xac680; a1 = the 8-byte load of the GOT word 0xa3cf0 (it holds 0xac678), s11 = the
                      8-byte load at 0xac678 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s4 = s.
     0x877f4 - 0x87808 the flag word = 0 goes to 0x87808 (s2 = 0); transport_cells row 6 gives 1. a0 = 128 and the
                      call of __asan_stack_malloc_1 (frame_alloc_1, 0x3d868 = transportb_sigma
                      TB___asan_stack_malloc_1) at 0x877fc, return address 0x87800: a class-1 side-stack frame
                      (fs_frame_bytes 1 = 128 bytes); s2 = the result.
     0x8780c - 0x8782c s10 = s2; s2 <> 0 goes to 0x87830. The real-stack arm (s2 = 0): s10 = (sp - 128) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s10), then sp = s10. With
                      count_cid 1 (frames Sc) < fs_frames 1 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s10 = s2.
     0x87830          the 8-byte store of frame at s1 + 48 (its own machine frame).
     0x87834 - 0x87858 the frame header: 0x41b58ab3 at frame, the description string 0x113c8 ("1 32 64 5 f:265": one
                      variable, the 64 bytes of f at frame + 32) at frame + 8, the function's address 0x87784 at
                      frame + 16.
     0x87840, 0x8785c - 0x878a4 s9 = (frame >> 3) + 0x7fff8000; the frame's 16 shadow bytes (128 bytes): 0..3 =
                      0xf1, 12..15 = 0xf3 (guard bytes), 4..11 = 0 (f's 64 bytes, usable).
     each instrumented check below: the shadow byte k at (x >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access
                      ((x & 7) + 3) < k (signed) goes on; for an 8-byte access any k <> 0 goes to the error path.
     0x878a8 - 0x878b0 a0 = -1; s = 0 or buf = 0 goes to 0x87964 (returns -1; kept unreached: a0 = TB_g_s, and
                      0 < buf with buf + length b < 2 ^ 64 from trans_src_ok, so w64 buf <> 0).
     0x878b4 - 0x878c0 s5 = s + 18152 (g_s.stats); s6 = frame + 32 = f.
     0x878c4 - 0x878d0 a0 = buf, a1 = len, a2 = f; the call of diginet_frame_parse (0x8b1f8 = transportb_sigma
                      TB_diginet_frame_parse) at 0x878d0, return address 0x878d4 (:268). Its result a0 = fr_code b,
                      and the 64 bytes at f are DgnTransportBCg.v frame_f_bytes buf b fj.
     0x878d4 - 0x878f8 a1 = s & 7; a0 = 0 goes to 0x878fc. Else (:269-272) a1 <> 0 goes to the trap word; the check
                      of the 8-byte access at s + 18184 (g_s.stats.rx_ignored, a1 = s5 + 32), then 0x87958; a0 keeps
                      fr_code b, the result.
     0x878fc - 0x87914 a1 <> 0 (s & 7 <> 0) goes to the trap word; s7 = f + 6 (the source MAC); a0 = f + 6, a1 = s
                      (g_s.cfg.host_mac), a2 = 6; the call of the bcmp wrapper (0x42d34 = transportb_sigma
                      TB___interceptor_trampoline_bcmp) at 0x87910, return address 0x87914: a result 0 (the frame is the
                      host's own) goes to 0x87944 (:273-277).
     0x87918 - 0x87928 a0 = f (the destination MAC), a1 = s, a2 = 6; the bcmp call at 0x87924: a result 0 goes to
                      0x87a68 (:275).
     0x8792c - 0x87940 a0 = f, a1 = BROADCAST = 0x21160 (TRANS_BROADCAST, the 6 bytes of diginet_session.c:9),
                      a2 = 6; the bcmp call at 0x8793c: a result 0 goes to 0x87a68.
     0x87944 - 0x87960 the ignored path: a1 = s + 18184, the check of the 8-byte access, the 8-byte load, + 1, the
                      8-byte store back (set_S_stats_rx_ignored with u64 of the 64-bit sum). a0 = 0 (the shadow byte
                      the check loaded), the result DIGINET_OK.
     0x87964 - 0x87990 shadow bytes 4..11 = 0xf8 (f out of scope); the header word 0x45e0360e stored at frame (every
                      path).
     0x87994          s2 = 0 goes to 0x879e8 (the real-stack arm; not taken).
     0x87998 - 0x879e4 the release: the frame's 16 shadow bytes (128 bytes) = 0xf5 (released); a1 = the 8-byte load
                      at s2 + 120 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a1 (YG0d.v astack_free_law); to 0x87a28.
     0x879e8 - 0x87a24 the real-stack arm's release: shadow bytes 0..15 = 0.
     0x87a28 - 0x87a64 sp = s0 - 160, ra and s0 .. s11 loaded back, sp = sp + 160, return with a0 = the result.
     0x87a68 - 0x87a80 (the frame is for this host) s8 = s + 116 (g_s.desk_known); the check of the 4-byte load there
                      (its shadow byte's address a2, kept at s1 + 24 by 0x87ac4); a0 = the 4-byte load at s + 116;
                      = 0 goes to 0x87ab4 (:278).
     0x87a84 - 0x87ab0 a0 = f + 6, a1 = s + 120 (g_s.desk_mac), a2 = 6; the bcmp call at 0x87a90: a result 0 goes to
                      0x87af8 (:279-282); else the ignored path at 0x87a98 (the check of the 8-byte access at
                      s + 18184, which leaves a0 = 0, the result DIGINET_OK, then 0x87958).
     0x87ab4 - 0x87ac0 (no desk known) a0 = the 1-byte load at f + 30 (h.cmd; inside f, no instrumented check: the
                      compiler knows f's shadow); (a0 & 0xfe) <> 0xe0 goes to 0x87b18 (a0 = 0, :284-285).
     0x87ac4 - 0x87ad0 the 8-byte store of a2 at s1 + 24; a0 = f + 6; the call of diginet_mac_is_digidesign (0x8b068 =
                      transportb_sigma TB_diginet_mac_is_digidesign) at 0x87acc, return address 0x87ad0 (:286): a
                      result 0 goes to 0x87b9c (the ignored path, :287-289, which leaves a0 = 0 the same way).
     0x87ad4 - 0x87ae0 a0 = s + 120, a1 = f + 6, a2 = 6; the call of __asan_memcpy (checked_memcpy, 0x523ec =
                      transportb_sigma TB___asan_memcpy) at 0x87ae0, return address 0x87ae4: g_s.desk_mac = the source
                      MAC (:290).
     0x87ae4 - 0x87af4 a0 = the 8-byte load at s1 + 24 (the saved shadow-byte address of s + 116); the check of the
                      4-byte store there; the store of 1 at s + 116 (g_s.desk_known = 1, :291).
     0x87af8 - 0x87b14 a0 = s + 112 (g_s.state); the check of the 4-byte load there; a1 = the 4-byte load at s + 112;
                      = 3 (S_CLOSED) goes to 0x87b18 (:293-294).
     0x87b18 - 0x87b1c a0 = 0 (DIGINET_OK); to 0x87964.
     0x87b20 - 0x87b3c the check of the 8-byte access at s + 18152 (g_s.stats.rx_frames); the 8-byte load, + 1, the
                      8-byte store back (:296); a0 = s + 176 (g_s.last_rx_us).
     0x87b40 - 0x87b58 the check of the 8-byte store at s + 176; a2 = the 1-byte load at f + 30 (h.cmd); a3 = 0xdf;
                      the 8-byte store of now at s + 176 (:297).
     0x87b5c - 0x87b68 cmd <= 0xdf goes to 0x87b80; else (cmd - 0xe0) >= 2 (unsigned) goes to 0x87bb8.
     0x87b6c - 0x87b7c (cmd = 0xe0 or 0xe1) a0 = s, a1 = f, a2 = now; the call of on_announce (0x87cc8 =
                      transportb_sigma TB_on_announce) at 0x87b78, return address 0x87b7c (:299-302); to 0x87c44.
     0x87b80          cmd = 0 goes to 0x87c10 (DIGINET_CMD_DATA).
     0x87b84 - 0x87b98 cmd <> 0xa0 goes to 0x87c24; else (DIGINET_CMD_ACK) a0 = s, a1 = f; the call of on_ack
                      (0x8858c = transportb_sigma TB_on_ack) at 0x87b94, return address 0x87b98 (:303-305); to
                      0x87c44.
     0x87b9c - 0x87bb4 the ignored path of :287-289 (the check of the 8-byte access at s + 18184, then 0x87958).
     0x87bb8 - 0x87bbc cmd <> 0xe3 goes to 0x87c24 (DIGINET_CMD_DISCONNECT, :309).
     0x87bc0 - 0x87bc8 a1 = the state loaded at 0x87b0c, minus 1 (32-bit); 1 < a1 (unsigned) goes to 0x87c44 (the
                      state is neither S_WAKING nor S_ONLINE, :310).
     0x87bcc - 0x87c0c the inlined session_lost (:311, :162-164): the checks of the 4-byte stores at s + 212 and
                      s + 168 and the stores of 0 there (inflight, desk_counter_valid); a0 = s, a1 = 0 (S_IDLE), a2 = 7
                      (DIGINET_R_DESK_DISCONNECT); the call of set_state (0x872cc = transportb_sigma TB_set_state) at
                      0x87c08, return address 0x87c0c (:164); to 0x87c44.
     0x87c10 - 0x87c20 (cmd = 0) a0 = s, a1 = f, a2 = now; the call of on_data (0x88a48 = transportb_sigma
                      TB_on_data) at 0x87c1c, return address 0x87c20 (:306-308); to 0x87c44.
     0x87c24 - 0x87c40 the ignored path of :313-315 (the check of the 8-byte access at s + 18184, the 8-byte load,
                      + 1, the 8-byte store back).
     0x87c44 - 0x87c50 a0 = s, a1 = now; the call of diginet_session_tick (0x8909c = transportb_sigma
                      TB_diginet_session_tick) at 0x87c4c, return address 0x87c50 (:317); its result a0 is the
                      result; to 0x87964.
     0x87c54          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path.
     0x87c58 - 0x87cc4 the slow paths of the checks and the 12 error calls.
   No tail jump: the calls are jal with link; every j is inside the function, and the function ends with ret.
   The model and the code (srx_model): the test at 0x878d8 is diginet_session_rx_m's test of :268 on
   diginet_frame_parse's result fr_code b; the three bcmp calls at 0x87910, 0x87924 and 0x8793c are the memeq tests
   of :273-277 (abcmp_realizes: a result 0 exactly when the 6 bytes agree; the 6 bytes at s are S_cfg_host_mac and
   the 6 at 0x21160 are TSS.BROADCAST, through tw_read and trans_rom_view_rd; the bytes at f and f + 6 are fr_dst b
   and fr_src b, cells 0 and 6 of frame_f_bytes); the test at 0x87a80 is S_desk_known =? 0 and the bcmp at 0x87a90 is
   the memeq of :279 against S_desk_mac; the test at 0x87ac0 is the cmd test of :284 (cmd & 0xfe = 0xe0 is
   cmd = DIGINET_CMD_ANNOUNCE or DIGINET_CMD_ANNOUNCE_SESSION); the leaf at 0x87acc is oui_of (fr_src b) (:286); the
   memcpy and the store at s + 116 are set_S_desk_mac and set_S_desk_known (:290-291, srx_learn); the test at 0x87b14
   is S_state =? S_CLOSED (:293); the stores at s + 18152 and s + 176 are set_S_stats_rx_frames (u64 of the 64-bit
   sum) and set_S_last_rx_us (:296-297, srx_w1); the switch at 0x87b5c - 0x87c20 with its ignored arm at
   0x87c24 - 0x87c40 is :298-316 (srx_sw; the block at 0x87b9c - 0x87bb4 is the :287-289 ignored path, not an arm
   of the switch); the disconnect arm's inlined session_lost is session_lost_m at srx_w1 of its world: its two
   stores are slost_w1 (diginet_session_tick_cg.v), and its set_state_m step at slost_w1 of that world with S_IDLE
   and why is the call of set_state (diginet_session_tick_cg.v slost_model_sstate); the stores at s + 18184 are
   set_S_stats_rx_ignored; the call at 0x87c4c is diginet_session_tick_m (:317). Each store is a tw_write inside g_s's
   payload, and the memcpy a tw_fill there. The model's None cases are the session callees' and
   diginet_session_tick's, all ruled out by the model premise; the code's trap word and its real-stack arm are ruled
   out by facts outside the model (the constant s, the side-stack premises).
   Trap path (the unimp word at 0x87c54, from 2 branches) and the fact that refutes it: 0x878dc and 0x878fc
   (s & 7 <> 0, a1 = s & 7 at 0x878d4; the UBSan alignment check of struct diginet_session *s on each arm of the
   test of :268): s = 0x5df640, a multiple of 8.
   Error paths (12 calls; no abort) and the facts that rule them out:
     __asan_report_load8 (0x596e4) at 0x878f8, 0x87ab0, 0x87bb4, 0x87cb4, 0x87cc4 (s + 18184), 0x87cbc (s + 18152);
     __asan_report_load4 (0x59644) at 0x87c68 (s + 116), 0x87c78 (s + 112);
     __asan_report_store4 (0x59964) at 0x87c8c (s + 116), 0x87c9c (s + 212), 0x87cac (s + 168);
     __asan_report_store8 (0x59a04) at 0x87cc0 (s + 176).
     Each guards a naturally aligned access inside g_s's payload [0x5df640, 0x5e3d98) (2283 whole granules), whose
     shadow bytes are 0 (trans_srx_cells, read at each AR state by DgnTransportBCg.v decode_zshadow_rd), so k = 0.
     The 1-byte loads at f + 30 (0x87ab4, 0x87b50) have no instrumented check.
     The memcpy's own check (aintrin_realizes' pre, from the G journal through TransportGCg.v gx_intrin_at): the
     destination [s + 120, s + 126) lies in g_s's payload (bytes of G, writable through the G journal by
     TransportGRwB.v G_HARNESS_B_rw; shadow 0 by trans_srx_cells, and its aligned group of 8 shadow bytes, the shadow
     of [g_s + 64, g_s + 128), lies in g_s too); the source [f + 6, f + 12) lies in the frame this function took,
     its shadow bytes 4..11 are 0 since 0x878a4 and visible; the two are apart (a frame byte is outside the image:
     AR_laws' al_client_img).
   Writes: g_s's desk_mac, desk_known, stats.rx_frames, last_rx_us, stats.rx_ignored, inflight and desk_counter_valid
   (bytes of G); its own machine frame (the 8 zero bytes at sp at 0x87788, the saves at 0x8778c - 0x877bc, the words
   at s1 + 24 and s1 + 48); its own side-stack frame (the header and the 64 bytes of f, which diginet_frame_parse
   fills), that frame's shadow bytes and its flag byte; and each callee's stores (srx_wr's rows). No byte of a
   caller's frame or block is written (the bytes at buf are read only), so srx_wr is the written range. The G kit for
   the own frame is image B's set_state_cg.v's (TransportGCg.v dk_kept_own_g with dkg_nf and dkg_nf_sep,
   dk_kept_trans_nf_g, dkg_frame_al64, gx_intrin_at, dk_kept_frame_byte_g; image B's CanKit.v can_stack_malloc_at and
   can_flag_store_pi read inside the G journal through gx_lift).
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_1 as astack_malloc_realizes ... SRX_CID (with pc_stack_malloc (as_code B) SRX_CID =
       transportb_sigma TB___asan_stack_malloc_1): count_cid 1 (frames Sc) < fs_frames 1 from the count premise.
     diginet_frame_parse as diginet_frame_parse_cg.v transport_diginet_frame_parse_cg at transportb_sigma
       TB_diginet_frame_parse (call at 0x878d0; a donor-form callee lifted with TransportGCg.v gx_call_cg; it stores
       only into f, a byte range of this function's own frame, so the world relation after it is the one it was
       handed): the donor journal from the G journal; ra = 0x878d4 (ret_ok, 4096 <= ra); gp, tp kept; a0 = buf,
       a1 = the length of b, a2 = f; buf <> 0 (the premise) and f <> 0 (a frame address, 0 < frame_addr); f mod 8 = 0
       (the frame is 64-aligned: dkg_frame_al64); trans_src_ok and decode_off_win regs TRANS_FP_STK of
       [buf, buf + length b), for every b, the empty one included (diginet_frame_parse_cg.v states them so): this
       statement's premises, carried across the stack malloc by DgnTransportBCg.v trans_src_ok_inner with the bytes
       kept and trans_rd_ok_sh (the range apart from the fresh frame: trans_src_ok_disj_own; an empty b is carried
       separately, as that lemma takes 0 < n), with the window moved to the callee's by lia (the callee's
       window lies inside this one: TRANS_FP_STK + 176 <= SRX_STK); garr8 of b at buf; length fj = 64 and garr8 of fj
       at f, fj the 64 bytes the frame holds before the call (whatever they are: present by astack_malloc_realizes);
       decode_in_fake (32 + 64 <= 128, the own frame); decode_twr_ok (the frame is in this journal's own frame list,
       present and not owned: AR_frames_law); decode_rd_ok (the stores of 0x87888 - 0x878a4 mark f's 8 shadow bytes
       0; the frame's bytes and their shadow are present); decode_off_win of f (the frame lies below alloc_ceiling,
       the callee's window above it); the disjointness of f and the bytes at buf when b is not empty (a heap block and
       a side-stack frame lie below alloc_ceiling and are pairwise disjoint: AR_sep_law; a machine-stack buf lies at
       or above alloc_ceiling (trans_stk_bounds), the frame below it; a frame byte is outside the image, so a G or RO
       buf is apart too); st_nev S + k + TRANS_FP_EV <= EV_MAX. Its X: a0 = fr_code b and the 64 bytes at f are
       diginet_frame_parse_cg.v trans_fp_f_bytes buf b fj, the text DgnTransportBCg.v frame_f_bytes is convertible
       to (both are lib/Prog/diginet_frame_parse_c.v parse_cells at fr_code b = 0, else fj).
     the bcmp wrapper as abcmp_realizes (YG0d.v) at transportb_sigma TB___interceptor_trampoline_bcmp (calls at
       0x87910, 0x87924, 0x8793c, 0x87a90; through TransportGCg.v gx_call_leaf): x = f or f + 6, 6 bytes of this
       function's own frame (visible, shadow 0, hull visible, outside the wrapper's window [sp' - 2 * ESTACK, sp')
       since the frame lies below alloc_ceiling); y = s (g_s.cfg.host_mac), s + 120 (g_s.desk_mac) or 0x21160
       (BROADCAST). The two g_s ranges are bytes of G, visible through tw_at's view, outside every stack, shadow 0
       (trans_srx_cells), and their aligned groups of 8 shadow bytes are the shadow of [g_s, g_s + 64) and of
       [g_s + 64, g_s + 128), inside g_s's zero shadow (g_s is 64-aligned). BROADCAST is in TRANS_RO_RD, visible
       through the journal by trans_ro_rd_unowned and trans_rom_no_errno (trans_ro_rd_scoped); its shadow byte is 6
       (transport_cells) and the rest of its aligned group [0x7fffc228, 0x7fffc230) is the four shadow bytes of
       [0x21140, 0x21160), a range of the record's zero shadow, and three 0xf9 guard bytes (trans_srx_cells). Each
       result is 0 exactly when the 6 bytes agree; every byte outside the wrapper's window is kept.
     diginet_mac_is_digidesign as its leaf statement (diginet_mac_is_digidesign_cg.v
       transport_diginet_mac_is_digidesign_cg, read at this unit's model by DgnTransportBCg.v transport_leaf_at; call
       at 0x87acc, through gx_call_leaf and the leaf bridge): a0 = mac = f + 6, mac <> 0; l = the 6 bytes fr_src b
       there (3 <= length l), from frame_f_bytes' cell at 6; the leaf's stk / off_stk / addressable / rng premises:
       f's 64 bytes present and marked usable (decode_rd_ok, kept as above), [f + 6, f + 9) outside the leaf's window
       [sp' - ESTACK, sp') (decode_off_win of f at SRX_STK), the GOT word 0xa3cf0 and the cell 0xac678 (image bytes,
       outside every window; asan_cells: transport_cells rows 1-2). Its X: a0 = 1 when oui_of l, else 0; no byte
       outside its window changes (dleaf_post with WR = []).
     __asan_memcpy as aintrin_realizes ... OCpy (transportb_sigma TB___asan_memcpy), call at 0x87ae0 (above).
     on_announce as on_announce_cg.v transport_on_announce_cg at transportb_sigma TB_on_announce (call at 0x87b78; a
       G-form callee in the same G journal): the journal at the call state (the own frame live); ra = 0x87b7c
       (ret_ok, 4096 <= ra); gp, tp kept; a0 = s = ONANN_S, a1 = f, a2 = now, 0 <= now < 2 ^ 64; sp' 32-aligned,
       sp0 - STK <= sp' - ONANN_STK (SRX_STK = 176 + ONANN_STK), sp' <= sp0;
       trans_dframe_at at ONANN_STK of f and buf: fr_code b = 0 (this path), 0 < buf, garr8 of b at buf, trans_src_ok
       of [buf, buf + length b) (this statement's premise, carried across the stack malloc as for
       diginet_frame_parse's call (trans_src_ok_inner) and across diginet_frame_parse by DgnTransportBCg.v
       trans_src_ok_acall; across the own frame's header and shadow stores (0x87834 - 0x878a4,
       before diginet_frame_parse), its placement by trans_src_ok_inner and its decode_rd_ok by trans_rd_ok_sh, the
       range, its shadow bytes and its hull lying outside the fresh 64-aligned frame and that frame's shadow
       (trans_src_ok_disj_own); and across the bcmp wrapper, the leaf and the memcpy, which keep every byte outside
       their windows and destinations, and the g_s stores, bytes of G (srx_buf_off_g puts the range outside G), by
       trans_src_ok_view) and decode_off_win of it (this statement's premise at SRX_STK, moved to the callee's window
       by lia: ONANN_STK + 176 = SRX_STK), no byte of it in G (srx_buf_off_g), 0 < f, f mod 8 = 0 (the frame is
       64-aligned: dkg_frame_al64), length fj = 64, garr8 of frame_f_bytes buf b fj at f (diginet_frame_parse's X,
       carried: the bcmp wrapper, the leaf and the memcpy keep every byte outside their windows and destinations,
       and the destination [s + 120, s + 126) is a G byte, apart from the frame), decode_in_fake, decode_rd_ok and
       decode_off_win of f (as for diginet_frame_parse);
       tw_at at srx_w1 (srx_learn Bw b or Bw) now: the tw_fill of :290 and the tw_writes of :291, :296 and :297;
       g_fail_next of it <= 1 (the four stores do not touch the byte: g_fail_next Bw <= 1);
       on_announce_m timg_B TF at that world b now = Some (B2, tt) (the model premise through srx_model);
       trans_tframe_at TF at ONANN_STK: this walk's at SRX_STK, carried (TF's bytes and their shadow are unchanged:
       srx_apart for the g_s stores and the memcpy's destination [s + 120, s + 126), a row of srx_wr b; the own frame
       is a fresh frame apart from TF's placement; the bcmp wrapper, the leaf and the memcpy keep every byte outside
       their windows (which decode_off_win puts TF outside) and destinations; and the record facts of the holds
       statement carry it across the stack malloc's acall_kept (trans_src_ok_inner) and diginet_frame_parse's
       acall_kept (trans_src_ok_acall)), and on_announce's window lies inside this one;
       trans_rom_view_rd at the call memory (no store of diginet_session_rx reaches a read-only byte, and the stack
       malloc's acall_kept, diginet_frame_parse's acall_kept, the bcmp wrapper, the leaf and the memcpy keep every
       TRANS_RO_RD byte: trans_ro_rd_scoped);
       onann_apart TF at that world: srx_apart, since onann_wr of it is a row of srx_wr b; trans_tf_off_g TF: this
       statement's premise;
       the run invariants (1) and (4) and g_ncmd's bound at that world: Bw's (above); count_cid 3 at the call state
       = count_cid 3
       (frames Sc) < fs_frames 3, count_cid 1 at the call state = count_cid 1 (frames Sc) + 1 < fs_frames 1 (the own
       frame is of class 1), and count_cid 2 at the call state = count_cid 2 (frames Sc), with + 1 < fs_frames 2 from
       + 2 (the count premises; srx_cid_callees); st_nev S + k + ONANN_EV <= EV_MAX (SRX_EV is the largest switch
       callee's event plus TICK_EV, all 0). Its X: tw_at at B2, g_fail_next B2 <= 1.
     on_ack as on_ack_cg.v transport_on_ack_cg at transportb_sigma TB_on_ack (call at 0x87b94): as on_announce,
       without a2, the two run invariants and g_ncmd's bound, at ONACK_STK, with count_cid 2 (frames Sc) + 1 <
       fs_frames 2 (from + 2) and onack_apart. Its X: tw_at at B2, g_fail_next B2 <= 1.
     set_state as set_state_cg.v transport_set_state_cg at transportb_sigma TB_set_state (call at 0x87c08, after the
       inlined session_lost's two stores): the journal at the call state (the own frame live); ra = 0x87c0c; gp, tp
       kept; a0 = s = SSTATE_S, a1 = st = 0 (S_IDLE), a2 = why = 7 (DIGINET_R_DESK_DISCONNECT), 0 <= st, why < 2 ^ 31;
       sp' 32-aligned, sp0 - STK <= sp' - SSTATE_STK, sp' <= sp0; tw_at at slost_w1 B1, B1 = srx_w1 (srx_learn Bw b or
       Bw) now (the four stores, then the tw_writes of :162-163); g_fail_next of it <= 1 (as for on_announce);
       set_state_m timg_B TF (slost_w1 B1) S_IDLE why = Some (B2, tt): the model premise through srx_model and
       slost_model_sstate (on the path where S_state B1 is S_ONLINE or S_WAKING); trans_tframe_at TF at SSTATE_STK and
       trans_rom_view_rd (as for on_announce, and across the stores of :162-163, rows of srx_wr b); sstate_apart TF
       (slost_w1 B1) S_IDLE why: srx_apart, since sstate_wr (slost_w1 B1) S_IDLE why is a row of srx_wr b; count_cid 2
       at the call state = count_cid 2 (frames Sc) < fs_frames 2 (from + 2); st_nev: inside SRX_EV. It takes no frame
       argument, no trans_tf_off_g, no run invariant and neither index bound. Its X: tw_at at B2, g_fail_next B2 <= 1.
     on_data as on_data_cg.v transport_on_data_cg at transportb_sigma TB_on_data (call at 0x87c1c): as on_announce,
       at ONDATA_STK, with ondata_apart, the run invariants (1) and (4) but not g_ncmd's bound (on_data hands
       send_control its own Bw: on_data_cg.v), the guarded N_DATA pair (3) (this
       statement's premise, at Bw, whose accept-path guards hold here: the call at 0x87c1c is reached only past the
       branches at 0x878d8 (fr_code), 0x87914, 0x87928 and 0x87940 (after the three MAC compares), 0x87a80 (desk
       known), 0x87a94 (after the desk-MAC compare) and 0x87b14 (S_CLOSED), and on the switch's DATA arm (0x87b5c,
       0x87b80); the two stores before it (:296-297) touch no byte of OW, GOT.ndata, M or g_cmd, and
       ondata_dup reads S_desk_counter_valid and S_desk_counter, which they do not touch either; the range's
       trans_src_ok is carried to the call state as buf's is: trans_src_ok_inner with the bytes kept across the
       stack malloc, whose new frame (f's) is apart from its placement (trans_src_ok_disj_own), and
       trans_src_ok_acall across diginet_frame_parse; across the own frame's header and
       shadow stores, trans_src_ok_inner and trans_rd_ok_sh (trans_src_ok_disj_own), as for buf; and
       trans_src_ok_view across the bcmp wrapper, which keeps every byte outside its window (decode_off_win puts the
       range outside it), and the g_s stores of :296-297, bytes of G, which miss it:
       when fr_body_len b > 0, the model premise, through on_data_m and check_state_data_m's frame_read (TCb.v) at
       notice's world, whose OW.dn and GOT.ndata are Bw's, puts the range inside TF, which trans_tf_off_g puts outside
       G (on_data_cg.v gives the same reason); an empty range is carried separately, as the lemmas take 0 < n; its
       decode_off_win moves to ONDATA_STK by lia, on_data's window lying inside this one), and count_cid 2 (frames
       Sc) + 2 < fs_frames 2. Its X: tw_at at B2, g_fail_next B2 <= 1.
     diginet_session_tick as diginet_session_tick_cg.v transport_diginet_session_tick_cg at transportb_sigma
       TB_diginet_session_tick (call at 0x87c4c; a G-form callee in the same G journal): the journal at the call
       state (the own frame live); ra = 0x87c50; gp, tp kept; a0 = s = TICK_S, a1 = now, 0 <= now < 2 ^ 64; sp'
       32-aligned, sp0 - STK <= sp' - TICK_STK, sp' <= sp0; tw_at at B2, the world the switch callee left
       (srx_w1 .. now on the :309-312 path that calls none, and srx_ign (srx_w1 .. now) on the :313-315 path, whose
       store of g_s.stats.rx_ignored at 0x87c40 precedes the call);
       g_fail_next B2 <= 1 (that callee's X, or the premise with the stores, which leave the byte as it was);
       diginet_session_tick_m timg_B TF B2 now = Some (Bw', r) (the model premise through srx_model); trans_tframe_at
       TF at TICK_STK and trans_rom_view_rd at the call memory (carried as for the switch callee, and across its
       acall_kept_g: TF by trans_src_ok_kept over its clauses, which reach TF because trans_tf_off_g puts it outside G
       and srx_apart outside the callee's written range, a row of srx_wr b; the TRANS_RO_RD bytes by its image clause,
       since each lies outside G and is neither an owned static nor errno: trans_ro_rd_unowned, trans_rom_no_errno);
       tick_apart TF B2: srx_apart, since tick_wr B2 is a row of srx_wr b; the four run invariants at B2: this
       statement's at Bw, carried across the switch callee (its post names which G bytes it changed, and the walk
       reads the model's world B2 for the fields each invariant names: the only writer of M.fly among them is io_send,
       whose stored frame is at most SPEC_MAX_FRAME bytes and whose M.fly.len is that length (TCb.v io_send_m), so (1)
       holds at B2; io_send's check_latest_sent sets Cmd_st s to SENT and q_remove_m takes s out of g_q (TCb.v
       latest_sent_loop), so the PENDING set only shrinks, and no callee store (g_s outside queue, queued and cfg, M,
       GOT, g_q, g_nq, g_fail_next, g_last_counter, the Cmd_st fields of g_cmd[0 .. CMDS_MAX); set_state's g_s.state
       and its notice's GOT bytes among them) is a Cmd_len byte of g_cmd[0 .. CMDS_MAX) or a g_ncmd byte: with
       g_ncmd B2 = g_ncmd Bw <= CMDS_MAX, (4) holds at B2; none of the callees writes g_s.queue, g_s.queued or
       g_s.cfg, so with S_queued B2 = S_queued Bw <= QUEUE_MAX (2) and (5) hold at B2; the two index bounds hold at
       B2 for the same reason); count_cid 5, 0 and 2
       at the call state = this statement's counts (srx_cid_callees); st_nev: the event count after the switch callee
       plus TICK_EV, inside SRX_EV. Its X: a0 = r, tw_at at Bw', g_fail_next Bw' <= 1.
   The callees' own record facts are premises of their holds statements.
   Stack: 160 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the memcpy, the leaf), 2 * ESTACK (the bcmp wrapper),
   diginet_frame_parse's TRANS_FP_STK, on_announce's ONANN_STK, on_ack's ONACK_STK, on_data's ONDATA_STK,
   set_state's SSTATE_STK or diginet_session_tick's TICK_STK: SRX_STK = 176 + ONANN_STK (srx_stk_eq).
   The differences from image A's form (lib/A/Prog/diginet_session_rx_cg.v), each forced by image B's code: the
   addresses; image B has no session_lost function: the disconnect arm inlines it (its two checked stores at
   s + 212 and s + 168) and calls set_state (set_state_cg.v) where image A calls session_lost, so srx_wr's row for it
   is the two stores and set_state_cg.v sstate_wr at diginet_session_tick_cg.v slost_w1 (the content of image A's
   session_lost_cg.v slost_wr), SRX_STK and SRX_EV take SSTATE_STK and SSTATE_EV, and set_state's statement takes
   sstate_apart; on_announce's own frame is of class 3 on image B (image A: class 4) and diginet_session_wake's, under
   it, of class 1 (image A: class 2), so the count premises are count_cid 1 (frames Sc) + 1 < fs_frames 1 (image A:
   count_cid 1 (frames Sc) < fs_frames 1) and count_cid 3 (frames Sc) < fs_frames 3 (image A: class 4); the class-5,
   class-0 and class-2 premises are image A's; BROADCAST lies at 0x21160, 32 bytes past a 64-byte boundary (image A:
   0x211c0, on one), so the rest of its aligned group of shadow bytes is the zero shadow of [0x21140, 0x21160) before
   it and three 0xf9 guard bytes after it (trans_srx_cells; image A: three guard bytes and [0x211e0, 0x21200) after
   it); the two UBSan branches to the trap word are new (image A's code has no trap of its own), and each is refuted
   by the constant s, a fact image A's form already has, so no premise is added for them. srx_wr names a field's
   bytes by lib/B/Prog/m_set_cg.v twb_fld (image A's m_lost_cg.v twa_fld).

   The callers (each with the return address after its jal):
   - receive at 0x837fc (return 0x83800): a0 = 0x5df640 (&g_s, formed at 0x837ec - 0x837f0), a1 = s0, the heap block
     the malloc wrapper returned at 0x836dc for max (len, 1) bytes (so the block is never empty and a1 <> 0), a2 = s1
     (its own len), a3 = the 8-byte load of g_now at 0x837e4. Its buf is a heap block (decode_in_block).
   - diginet_session_poll at 0x8ad18 (return 0x8ad1c) and at 0x8ad90 (return 0x8ad94): a0 = s3 (its own a0, &g_s),
     a1 = s9 = its class-5 side-stack frame + 32 (its local uint8_t[1514], 0x8acc4; the frame from
     __asan_stack_malloc_5 at 0x8ab08), a2 = s10 (the count io_recv returned), a3 = the value io_now returned. Its buf
     is a range of a live side-stack frame (decode_in_fake with decode_rd_ok).
   Each supplies its G journal, tw_at, g_fail_next, the model premise (its branch of the model), the placement of
   buf and its bytes, srx_buf_off_g (a heap block and a side-stack frame are outside the image, so outside G),
   trans_tframe_at, srx_apart and trans_tf_off_g of its TF (the last two from its plain tframe_at's off_world clause),
   trans_rom_view_rd, the four run invariants with the two index bounds, and the guarded N_DATA pair, and the five
   frame counts (receive holds
   no side-stack frame; diginet_session_poll holds a class-5 frame of its own, so its own class-5 count must leave
   room for this call's chain). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_mac_is_digidesign_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
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
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_mac_is_digidesign_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_session_rx's frame (`sp = sp - 160` at TB_diginet_session_rx), the at most 0x10 bytes of `sp = sp & -32`
   (0x877c4) below it, and the largest stack a callee uses below the realigned sp: ESTACK for
   __asan_stack_malloc_1 and __asan_memcpy (YG0d.v ecall_pre) and for the leaf diginet_mac_is_digidesign
   (LeafCgKit.v ecall_pre), 2 * ESTACK for the bcmp wrapper (abcmp_realizes), diginet_frame_parse's TRANS_FP_STK,
   on_announce's ONANN_STK, on_ack's ONACK_STK, on_data's ONDATA_STK, set_state's SSTATE_STK and
   diginet_session_tick's TICK_STK. *)
Definition SRX_FRAME : Z := 160.
Definition SRX_ALIGN : Z := 0x10.
Definition SRX_STK : Z :=
  SRX_FRAME + SRX_ALIGN +
  Z.max (2 * ESTACK)
    (Z.max TRANS_FP_STK (Z.max ONANN_STK (Z.max ONACK_STK (Z.max ONDATA_STK (Z.max SSTATE_STK TICK_STK))))).
Lemma srx_stk_eq : SRX_STK = SRX_FRAME + SRX_ALIGN + ONANN_STK.
Proof. reflexivity. Qed.
(* No allocator event: every callee records none, and the class-1 stack malloc and its release record none (YG00.v
   stack_malloc, stack_free). At most one switch callee runs, and then diginet_session_tick. *)
Definition SRX_EV : Z := Z.max (Z.max ONANN_EV ONACK_EV) (Z.max ONDATA_EV SSTATE_EV) + TICK_EV.
Lemma srx_ev_zero : SRX_EV = 0.
Proof. reflexivity. Qed.
(* The side-stack class of its own frame (a0 = 128 at 0x877f8, the call of __asan_stack_malloc_1 at 0x877fc), and the
   classes its callees take: 3 (on_announce), 1 (diginet_session_wake under on_announce, hence the + 1 of the
   class-1 premise), 5 (diginet_session_tick), 0 (send_data under it) and 2 (the on_data / send_control chain). Its
   own frame is of class 1, so it changes no other class's count: count_cid c ((1, pos) :: frames Sc) =
   count_cid c (frames Sc) for c <> 1. *)
Definition SRX_CID : Z := 1.
Lemma srx_cid_callees :
  ONANN_CID = 3 /\ WAKE_CID = 1 /\ TICK_CID = 5 /\ SENDDATA_CID = 0 /\
  ONACK_CID = 2 /\ ONDATA_CID = 2 /\ SSTATE_CID = 2 /\ SENDCTL_CID = 2 /\ TRANS_BC_CID = 2 /\
  SRX_CID = WAKE_CID /\
  SRX_CID <> ONANN_CID /\ SRX_CID <> TICK_CID /\ SRX_CID <> SENDDATA_CID /\ SRX_CID <> ONDATA_CID.
Proof. repeat split; try reflexivity; cbv; congruence. Qed.
(* Its first argument: g_s's base in image B. *)
Definition SRX_S : Z := TB_g_s.
(* The addresses of the g_s fields the code reads or writes (s + 0, s + 18184, s + 116, s + 120, s + 112, s + 18152,
   s + 176, s + 212, s + 168) and of the read-only BROADCAST the third bcmp call reads. *)
Lemma srx_addrs :
  SRX_S = 0x5df640 /\
  SRX_S + (TW.A_S_cfg_host_mac - TW.OFF_g_s) = 0x5df640 /\
  SRX_S + (TW.A_S_stats_rx_ignored - TW.OFF_g_s) = 0x5e3d48 /\
  SRX_S + (TW.A_S_desk_known - TW.OFF_g_s) = 0x5df6b4 /\
  SRX_S + (TW.A_S_desk_mac - TW.OFF_g_s) = 0x5df6b8 /\
  SRX_S + (TW.A_S_state - TW.OFF_g_s) = 0x5df6b0 /\
  SRX_S + (TW.A_S_stats_rx_frames - TW.OFF_g_s) = 0x5e3d28 /\
  SRX_S + (TW.A_S_last_rx_us - TW.OFF_g_s) = 0x5df6f0 /\
  SRX_S + (TW.A_S_inflight - TW.OFF_g_s) = 0x5df714 /\
  SRX_S + (TW.A_S_desk_counter_valid - TW.OFF_g_s) = 0x5df6e8 /\
  TRANS_BROADCAST = 0x21160.
Proof. repeat split; reflexivity. Qed.
(* Its one local, the struct diginet_frame f, at offset 32 of its class-1 frame (the description string at 0x113c8),
   64 bytes inside the frame's 128. *)
Definition SRX_F : Z := 32.
Lemma srx_frame_fits : SRX_F + FRAME_F_SIZE = 96 /\ 96 <= fs_frame_bytes SRX_CID.
Proof. repeat split; cbv; congruence. Qed.

(* The model's steps (TSess.v diginet_session_rx_m): the ignored world, the two MAC tests of :273-277, the desk the
   function learns (:290-291), the world after the counters of :296-297, the switch of :298-316 and the accepted
   path of :293-317. Image-free: image A's text. *)
Definition srx_ign (Bx : list byte) : list byte :=
  TW.set_S_stats_rx_ignored Bx (TS0.u64 (TW.S_stats_rx_ignored Bx + 1)).
Definition srx_mac_bad (Bx b : list byte) : bool :=
  TS0.memeq 6 (DSpec.fr_src b) (TW.S_cfg_host_mac Bx) ||
  (negb (TS0.memeq 6 (DSpec.fr_dst b) (TW.S_cfg_host_mac Bx)) &&
   negb (TS0.memeq 6 (DSpec.fr_dst b) TSS.BROADCAST)).
Definition srx_learn (Bx b : list byte) : list byte :=
  TW.set_S_desk_known (TW.set_S_desk_mac Bx (DSpec.fr_src b)) 1.
Definition srx_w1 (Bx : list byte) (now : Z) : list byte :=
  TW.set_S_last_rx_us (TW.set_S_stats_rx_frames Bx (TS0.u64 (TW.S_stats_rx_frames Bx + 1))) now.
Definition srx_sw (I : TI.timg) (F : option TI.tframe) (Bx b : list byte) (now : Z) : option (list byte * unit) :=
  if (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) || (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)
  then TSS.on_announce_m I F Bx b now
  else if DSpec.fr_cmd b =? TS0.DIGINET_CMD_ACK then TSS.on_ack_m I F Bx b
  else if DSpec.fr_cmd b =? TS0.DIGINET_CMD_DATA then TSS.on_data_m I F Bx b now
  else if DSpec.fr_cmd b =? TS0.DIGINET_CMD_DISCONNECT then
    (if (TW.S_state Bx =? TS0.DIGINET_S_ONLINE) || (TW.S_state Bx =? TS0.DIGINET_S_WAKING)
     then TSS.session_lost_m I F Bx TS0.DIGINET_R_DESK_DISCONNECT else Some (Bx, tt))
  else Some (srx_ign Bx, tt).
Definition srx_accept (I : TI.timg) (F : option TI.tframe) (Bx b : list byte) (now : Z)
    : option (list byte * Z) :=
  if TW.S_state Bx =? TS0.DIGINET_S_CLOSED then Some (Bx, DLib.DIGINET_OK)
  else
    match srx_sw I F (srx_w1 Bx now) b now with
    | None => None
    | Some (B2, _) => TSS.diginet_session_tick_m I F B2 now
    end.
Lemma srx_model : forall (I : TI.timg) (F : option TI.tframe) (Bw b : list byte) (now : Z),
  TSS.diginet_session_rx_m I F Bw b now =
  if negb (DSpec.fr_code b =? DLib.DIGINET_OK) then Some (srx_ign Bw, DSpec.fr_code b)
  else if srx_mac_bad Bw b then Some (srx_ign Bw, DLib.DIGINET_OK)
  else if negb (TW.S_desk_known Bw =? 0) then
    (if negb (TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw)) then Some (srx_ign Bw, DLib.DIGINET_OK)
     else srx_accept I F Bw b now)
  else if negb ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) ||
                (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION))
  then Some (Bw, DLib.DIGINET_OK)
  else if negb (DSpec.oui_of (DSpec.fr_src b)) then Some (srx_ign Bw, DLib.DIGINET_OK)
  else srx_accept I F (srx_learn Bw b) b now.
Proof. intros I F Bw b now. reflexivity. Qed.

(* The off_world part of the plain contract's arg_blk for buf: no byte of the input bytes is a byte of G. A heap
   block and a side-stack frame both lie outside the image, so a caller has it from the placement of buf; the three
   session callees take it inside on_ack_cg.v trans_dframe_at. *)
Definition srx_buf_off_g (buf : Z) (b : list byte) : Prop :=
  forall x, buf <= x < buf + Z.of_nat (length b) -> ~ inG TG.G_HARNESS_B x.

(* The bytes some path of the call stores into G (each path stores a subset, diginet_session_rx_m): g_s's
   stats.rx_ignored, stats.rx_frames and last_rx_us (8 bytes each), desk_mac (6 bytes) and desk_known (4 bytes); the
   disconnect arm's inlined session_lost: inflight and desk_counter_valid (4 bytes each, the code's own) and
   set_state's (set_state_cg.v sstate_wr at diginet_session_tick_cg.v slost_w1 of the world it starts from); and each
   callee's written range at the world it is called with. The callees' worlds are the model's, which this statement
   does not name (on_announce, on_ack, on_data and the inlined session_lost run at srx_w1 of Bw or of srx_learn Bw b,
   diginet_session_tick at the world the switch callee left), so each row is that callee's range at any world: a
   caller needs of these rows only that they are bytes of G, which holds of every disjunct of each. *)
Definition srx_wr (b : list byte) (a : Z) : Prop :=
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_rx_ignored 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_desk_mac TS0.DIGINET_MAC_LEN a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_desk_known 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_rx_frames 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_last_rx_us 8 a \/
  (exists Bx : list byte, onann_wr Bx b a) \/
  (exists Bx : list byte, onack_wr Bx b a) \/
  (exists Bx : list byte, ondata_wr Bx b a) \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_desk_counter_valid 4 a \/
  (exists Bx : list byte, sstate_wr (slost_w1 Bx) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_DISCONNECT a) \/
  (exists Bx : list byte, tick_wr Bx a).

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. Each callee reads TF after the stores before it (notice_cg.v notice_apart and the callees' own *_apart). *)
Definition srx_apart (Fr : option TI.tframe) (b : list byte) : Prop :=
  forall x, srx_wr b x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow facts of the record (lib/B/YF0m.v Tfib_zero_shadow and Tfib_const_shadow rows) the code needs: g_s's
   payload (18264 bytes, 2283 whole granules) has shadow 0 (its instrumented accesses, the memcpy's destination and
   the bcmp ranges [s, s + 6) and [s + 120, s + 126), whose aligned groups of 8 shadow bytes are the shadow of
   [g_s, g_s + 64) and [g_s + 64, g_s + 128), inside it since g_s is 64-aligned); and the rest of BROADCAST's group
   of 8 shadow bytes (the shadow of [0x21140, 0x21180)), which transport_cells gives only for its payload: the four
   granules of [0x21140, 0x21160) before it, a range of the record's zero shadow (Tfib_zero_shadow row
   (0x21140, 0x20)), and the three guard granules after it (Tfib_const_shadow rows 0x7fffc22d .. 0x7fffc22f, 0xf9). *)
Definition trans_srx_cells (B : asyms) : Prop :=
  decode_zshadow_at B SRX_S (SRX_S + TW.SZ_g_s) /\
  decode_zshadow_at B (TRANS_BROADCAST - 32) TRANS_BROADCAST /\
  forall ly,
    In (z1 (ANum (ACells.shadow_addr (TRANS_BROADCAST + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_BROADCAST + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_BROADCAST + 24))) 0xf9) (as_const B ly).
Lemma trans_srx_cells_rows :
  map ACells.shadow_addr [TRANS_BROADCAST - 32; TRANS_BROADCAST; TRANS_BROADCAST + 8; TRANS_BROADCAST + 16;
                          TRANS_BROADCAST + 24; SRX_S; SRX_S + 64] =
  [0x7fffc228; 0x7fffc22c; 0x7fffc22d; 0x7fffc22e; 0x7fffc22f; 0x800b3ec8; 0x800b3ed0].
Proof. reflexivity. Qed.

Section srx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range srx_wr b,
   no meter charge (the side-stack frame changes st_fs only), and X: a0 = r (sign-extended), the world relation at
   the model's world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this
   function takes is released. *)
Definition transport_srx_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' b : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs SRX_STK SRX_EV 0 (srx_wr b)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 r /\
       tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_diginet_session_rx_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (buf now r : Z) (b : list byte) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 SRX_S -> YK11.getr regs 11 = w64 buf ->
    YK11.getr regs 12 = w64 (Z.of_nat (length b)) -> YK11.getr regs 13 = w64 now ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SRX_STK -> spZ regs <= sp0 ->
    0 <= now < 2 ^ 64 ->
    0 < buf ->
    garr8 segs (mrestrict (w_H W) memc) buf (TW.zs b) ->
    trans_src_ok B lyc Sc W memc buf (Z.of_nat (length b)) ->
    decode_off_win regs SRX_STK buf (Z.of_nat (length b)) ->
    srx_buf_off_g buf b ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.diginet_session_rx_m timg_B TF Bw b now = Some (Bw', r) ->
    trans_tframe_at B lyc Sc W memc regs SRX_STK TF ->
    trans_tf_off_g TF ->
    trans_rom_view_rd W memc ->
    srx_apart TF b ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN) ->
    TW.S_queued Bw <= TC.QUEUE_MAX ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    TW.g_ncmd Bw <= TC.CMDS_MAX ->
    1 <= TW.S_cfg_max_cmds Bw -> 1 <= TW.S_cfg_max_body Bw ->
    (DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false -> TW.S_desk_known Bw <> 0 ->
     TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw) = true -> TW.S_state Bw <> TS0.DIGINET_S_CLOSED ->
     DSpec.fr_cmd b = TS0.DIGINET_CMD_DATA -> ondata_dup Bw b = false -> DSpec.fr_keepalive b = false ->
       trans_src_ok B lyc Sc W memc (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (DSpec.fr_body_len b) /\
       decode_off_win regs SRX_STK (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (DSpec.fr_body_len b)) ->
    count_cid SRX_CID (frames Sc) + 1 < fs_frames SRX_CID ->
    count_cid ONANN_CID (frames Sc) < fs_frames ONANN_CID ->
    count_cid TICK_CID (frames Sc) < fs_frames TICK_CID ->
    count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID ->
    count_cid ONDATA_CID (frames Sc) + 2 < fs_frames ONDATA_CID ->
    st_nev S + k + SRX_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_srx_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The statement the walk will prove: the class-1 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words, the read-only globals' shadow), the shadow of g_s's payload and the
   rest of BROADCAST's shadow group, the record facts that no byte of G and no TRANS_RO_RD byte is an owned static or
   errno (they carry the trans_src_ok of TF, of the bytes at buf and of the guarded OW.dn range, G and the
   TRANS_RO_RD bytes across the stack malloc's acall_kept (trans_src_ok_inner) and diginet_frame_parse's acall_kept
   (trans_src_ok_acall), and TF's trans_src_ok, with trans_tf_off_g, and the TRANS_RO_RD bytes across the switch
   callee's acall_kept_g; DgnTransportBCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno give gx_ok and gx_noerrno from the
   first two), the allocator, meter and side-stack laws, and the contracts of __asan_stack_malloc_1,
   diginet_frame_parse, the bcmp wrapper, diginet_mac_is_digidesign, __asan_memcpy, on_announce, on_ack, set_state,
   on_data and diginet_session_tick give the contract at TB_diginet_session_rx. *)
Definition transport_diginet_session_rx_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) SRX_CID = transportb_sigma TB___asan_stack_malloc_1 ->
  transport_cells B -> trans_srx_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B SRX_CID) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_frame_parse_cg fx' rc B MT (transportb_sigma TB_diginet_frame_parse)) ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LMD.transport_diginet_mac_is_digidesign_cg) fx') ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @transport_on_announce_cg fx' rc B MT (transportb_sigma TB_on_announce)) ->
  (forall fx' : YK11.FPState, @transport_on_ack_cg fx' rc B MT (transportb_sigma TB_on_ack)) ->
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) ->
  (forall fx' : YK11.FPState, @transport_on_data_cg fx' rc B MT (transportb_sigma TB_on_data)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_session_tick_cg fx' rc B MT (transportb_sigma TB_diginet_session_tick)) ->
  transport_diginet_session_rx_cg (transportb_sigma TB_diginet_session_rx).
End srx.
