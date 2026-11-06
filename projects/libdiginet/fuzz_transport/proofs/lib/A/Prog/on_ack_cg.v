(* on_ack_cg: the ASan walk contract of on_ack (transport/src/diginet_session.c:223-237; model lib/TModel/TSess.v
   on_ack_m) on fuzz_transport.asan (e89be137db17) at 0x8842c = transport_sigma TS_on_ack, size 1188, as STATEMENTS
   only (no proof). It stores into g_s, a harness global, takes a class-2 side-stack frame for its struct
   diginet_notice, calls notice through the session's notify pointer and calls maybe_online (a G-form callee) while
   that frame is live, so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx
   over G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), and the post is
   lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS). Its form is session_lost_cg.v's and
   maybe_online_cg.v's: a G walk with a side-stack frame of its own.

   The contract. a0 = s = &g_s = 0x5df9c0 (TWorldA.v TA_g_s); a1 = fp, the struct diginet_frame f that
   diginet_session_rx's diginet_frame_parse filled from the frame bytes b at buf (trans_dframe_at, below: the ASan
   form of lib/Prog/T/TSessC.v dframe_at). TF is the current heap frame (check_state_data_cg.v trans_tframe_at at
   this call's window); the read-only bytes notice's callees read are the image's (trans_rom_view_rd). The memory
   relates to the world Bw by image A's world relation (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview),
   g_fail_next Bw <= 1, and on_ack_m timg_A TF Bw b = Some (Bw', tt). No byte the call stores is a byte of TF
   (onack_apart). Class 2 of the side stack has two free frames (its own, and maybe_online's while its own is
   live). The function returns to ra with the callee-saved registers kept, no allocator event and no meter charge
   (its side-stack frame changes the state's st_fs only: ameter_fs_laws), its side-stack frame released (the
   caller's frames exactly), the caller's blocks exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or
   above alloc_ceiling outside the call's stack window [sp - ONACK_STK, sp), the image bytes outside G, the owned
   statics and errno, the caller's block and frame bytes outside onack_wr Bw b), the world relation at Bw', and
   g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/on_ack_c.v): a0 = W_BASE_PLAIN + OFF_g_s -> a0 = TA_g_s;
   a1 = fp kept; dframe_at m sp FRAME fp buf b fj -> trans_dframe_at at ONACK_STK (the translation of
   dframe_at: fr_code b = 0 kept; bytes_at of b at buf -> garr8, with trans_src_ok and decode_off_win for its
   placement and the window part of arg_blk, its off_world part -> no byte of [buf, buf + length b) is a byte of G,
   its 0 < buf kept and its buf + length b < 2 ^ 64 from trans_src_ok (trans_src_ok_place); rw_cells of
   dframe_cells at fp -> garr8 of DgnTransportCg.v frame_f_bytes buf b fj (which is lib/Prog/diginet_frame_parse_c.v
   parse_cells at fr_code b = 0, the cells of dframe_cells one for one) with length fj = 64 (rw_cells' cells_wf of
   the CB cells of fj, which diginet_frame_parse_cg.v's premise length fj = 64 gives the caller), decode_in_fake (f
   lies in a live side-stack frame of the caller: diginet_session_rx's class-1 frame), decode_rd_ok (the bytes
   visible, the 64 bytes marked usable: the instrumented check of the load at f + 24 reads their shadow; its
   fp + 64 <= 2 ^ 63 gives arg_blk's fp + 64 < 2 ^ 64) and decode_off_win for the window part of arg_blk (its
   off_world part holds of every frame byte: a frame byte is outside the image), 0 < fp and fp mod 8 = 0 kept);
   wmem -> tw_at; g_fail_next B <= 1 kept as a premise, and the post's g_fail_next B' <= 1 kept in X (the code
   neither reads nor writes g_fail_next; maybe_online's statement asks it and gives it back, as session_lost_cg.v
   takes it); timg_plain -> timg_A; tframe_at -> trans_tframe_at at ONACK_STK, and its off_world clause -> two
   facts, since check_state_data_cg.v trans_tframe_at drops that clause: onack_apart, no byte the call stores is a
   byte of TF (maybe_online_cg.v maybeon_apart's form), and trans_tf_off_g (check_state_data_cg.v), no byte of TF is
   a byte of G. trans_tf_off_g carries TF across notice (call at 0x88674), which writes G (GOT.acked), to
   maybe_online (call at 0x886ac), which takes TF: notice's acall_kept_g keeps the image bytes outside G only, and
   its X pins G only to the model world, so it carries no byte of a TF inside G; relro_img ->
   trans_rom_view_rd; stk, lo + FRAME <= sp, sp mod 16 and w_off_stack -> the journal's window premises; mem_inv is
   dropped. The post's munch, wmono, stk and mem_inv -> transport_cg_post (the journal at the
   return, acall_kept_g over onack_wr Bw b); wmem -> X's tw_at.
   Premises the plain contract does not have:
   - count_cid 2 (frames Sc) + 1 < fs_frames 2: its own class-2 frame, then maybe_online's class-2 frame, taken
     while its own is live (maybe_online's statement asks count_cid 2 < fs_frames 2 at its call state, whose frames
     are the own frame :: frames Sc). With it __asan_stack_malloc_2 returns a frame (astack_malloc_realizes), so the
     real-stack arm is not taken.
   - onack_apart and trans_tf_off_g (above).
   - in the holds statement: trans_onack_cells (g_s's zero shadow), the side-stack laws, and trans_g_unowned,
     trans_g_no_errno, trans_ro_rd_unowned and trans_rom_no_errno: they carry TF's trans_src_ok across the stack
     malloc (DgnTransportCg.v trans_src_ok_inner with TF's bytes kept by its acall_kept and trans_rd_ok_sh; the
     fresh frame is apart from TF's placement: trans_src_ok_disj_own) and
     across notice's acall_kept_g (trans_src_ok_kept over its clauses, TF lying outside G by trans_tf_off_g;
     trans_src_ok_acall_g asks every byte of G to be kept, which notice does not give), and f's bytes across the
     stack malloc's acall_kept (f is read only at 0x8859c, before notice), the TRANS_RO_RD bytes (trans_rom_view_rd
     for notice and maybe_online), and G (TransportGCg.v gx_kept_of_acall_kept with gx_ok and gx_noerrno, which
     DgnTransportCg.v G_HARNESS_gx_ok and G_HARNESS_gx_noerrno give from the first two), as send_data_cg.v takes
     them.
   Run invariants: none is carried. notice carries check_state_data's run invariant (the OW.dn[GOT.ndata].body range
   window-safe, with n_body_len < 2 ^ 32) only for a notice of kind N_DATA; on_ack's notice has kind N_ACKED (the
   store of 4 at p by 0x885e8; onack_ntc), so that premise of notice holds vacuously. maybe_online carries none.
   on_ack's own accesses are at fixed offsets of g_s (s + 96 .. s + 215, s + 1744 .. s + 1749, s + 18184 ..
   s + 18191), at f + 24 and in its own frames; its one memset fills 40 bytes of its own frame, so its code needs no
   bound that the model does not give.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   1188 code bytes are equal in both files), 297 words:
     0x8842c - 0x88468 sp = sp - 128; 0x88430 stores 8 zero bytes at sp; ra at sp + 120, s0 .. s11 at sp + 112 ..
                      sp + 24, loaded back at 0x887f8 - 0x88828; s0 = sp + 128 (the entry sp, kept to 0x887f4).
     0x8846c - 0x88474 sp = sp & -32 (at most 0x10 below entry - 128); s1 = the realigned sp; s4 = fp.
     0x88478 - 0x88490 a2 = the 8-byte load of the GOT word 0xa40e8 (it holds 0xaca00), then the 4-byte load of the
                      flag word at 0xaca00; a1 = the 8-byte load of the GOT word 0xa4090 (it holds 0xac9f8), s9 = the
                      8-byte load at 0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s3 = s.
     0x88494 - 0x884a8 the flag word = 0 goes to 0x884a8 (s2 = 0); transport_cells row 6 gives 1. a0 = 160 and the
                      call of __asan_stack_malloc_2 (frame_alloc_2, 0x3d99c = transport_sigma
                      TS___asan_stack_malloc_2) at 0x8849c, return address 0x884a0: a class-2 side-stack frame
                      (fs_frame_bytes 2 = 256 bytes); s2 = the result.
     0x884ac - 0x884cc s8 = s2; s2 <> 0 goes to 0x884d0. The real-stack arm (s2 = 0): s8 = (sp - 160) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s8), then sp = s8. With
                      count_cid 2 (frames Sc) < fs_frames 2 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s8 = s2.
     0x884d0 - 0x88500 the frame header: 0x41b58ab3 at frame, the description string 0x13d76 ("1 32 72 5 n:230": one
                      variable, 72 bytes at frame + 32) at frame + 8, the function's address 0x8842c at frame + 16.
     0x884dc, 0x88508 - 0x8855c s7 = (frame >> 3) + 0x7fff8000; the frame's shadow bytes 0..3 = 0xf1, 4..12 = 0xf8
                      (the notice's 72 bytes at frame + 32, marked out of scope), 13..19 = 0xf3 (guard bytes).
     0x88568          the 8-byte store of frame at s1 + 16 (its own machine frame).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access
                      (and the 2-byte load at s + 1748, whose check has the 4-byte form), ((a & 7) + 3) < k (signed)
                      goes on; for an 8-byte access any k <> 0 goes to the error path.
     0x88504, 0x8851c, 0x88560 - 0x8856c, 0x88834 - 0x88840 the check of the 4-byte load at s + 212 (a3 = its shadow
                      byte's address).
     0x88570 - 0x88574 a1 = the 4-byte signed load at s + 212 (S_inflight Bw); = 0 goes to 0x886dc (:225).
     0x88578 - 0x88588, 0x88844 - 0x88854 the check of the 4-byte load at f + 24 (h.ack_counter).
     0x8858c - 0x885a0, 0x88858 - 0x88868 the check of the 4-byte load at s + 1744; s10 = the 4-byte load at f + 24
                      (fr_ack b, through frame_f_bytes; at 0x8859c).
     0x885a4 - 0x885a8 a1 = the 4-byte load at s + 1744 (S_inflight_counter Bw); a1 <> s10 goes to 0x886dc (:225).
                      Past 0x885a8, onack_ign Bw b = false.
     0x885ac - 0x885b0, 0x8886c - 0x88878 the check of the 4-byte store at s + 212 (its shadow byte read again
                      through a3).
     0x885b4 - 0x885b8 s5 = p = frame + 32, the struct diginet_notice; the store of 0 at s + 212 (S_inflight = 0,
                      :229). The world is now onack_w1 Bw.
     0x885bc - 0x885dc shadow bytes 4..12 = 0 (the notice's 72 bytes marked usable).
     0x885e0 - 0x885e8 the 4-byte store of 4 (N_ACKED) at p (kind, :230).
     0x885e4 - 0x885f8, 0x8887c - 0x8888c s6 = s + 112, s11 = the address of its shadow byte; the check of the
                      4-byte load at s + 112.
     0x885fc - 0x88608 a0 = the 4-byte signed load at s + 112 (S_state (onack_w1 Bw)); stores into the frame: 8 zero
                      bytes at p + 8 (old_state, reason), the low 32 bits of a0 at p + 4 (state), the 8 bytes of fp
                      at p + 16 (n.frame, which notice does not read).
     0x8860c - 0x88618 a0 = p + 24, a1 = 0, a2 = 40; the call of __asan_memset (checked_memset, 0x5284c =
                      transport_sigma TS___asan_memset) at 0x88618, return address 0x8861c: the notice's bytes
                      24 .. 63 set to 0 (announce, personality, mac_offset, body, body_len).
     0x8861c          the 4-byte store of s10 at p + 64 (counter = fr_ack b, :231).
     0x88620 - 0x88630, 0x88890 - 0x8889c the check at s + 1748.
     0x88634 - 0x88644 a1 = the 2-byte signed load at s + 1748 (the low 16 bits of S_inflight_retries (onack_w1 Bw));
                      the 2-byte store of a1 at p + 68 (retry = u16 of it, :231), 2 zero bytes at p + 70. The 72
                      bytes at p are then onack_ntc Bw b as trans_ntc_at reads them (the announce pointer 0, n_ann =
                      None; the body pointer 0 and body_len 0, n_body = []).
     0x88638 - 0x88664, 0x888c8, 0x888cc the checks of the 8-byte loads at s + 96 and at s + 104.
     0x88668 - 0x88674 a2 = the 8-byte load at s + 96 (S_notify (onack_w1 Bw): tw_read, and the model's call_notify
                      gives TI.ti_notice timg_A = 0x83578); a0 = the 8-byte load at s + 104 (notify_ctx, which notice
                      does not read); a1 = p; the indirect call (jalr a2) at 0x88674, return address 0x88678 (:232;
                      struct diginet_session + 96, notify -> notice).
     0x88678 - 0x8867c, 0x888a0 - 0x888b0 the check of the 4-byte load at s + 112 (its shadow byte read through s11).
     0x88680 - 0x88688 a0 = the 4-byte signed load at s + 112 (S_state of notice's world B2); <> 1 (S_WAKING) goes
                      to 0x886b0 (:233).
     0x8868c - 0x8869c, 0x888b4 - 0x888c0 the check of the 4-byte store at s + 144.
     0x886a0 - 0x886a4 the store of 1 at s + 144 (S_wake_acked = 1, :234). The world is now set_S_wake_acked B2 1.
     0x886a8 - 0x886ac a0 = s3; the call of maybe_online (0x8b170 = transport_sigma TS_maybe_online) at 0x886ac,
                      return address 0x886b0 (:235).
     0x886b0 - 0x886d8 shadow bytes 4..12 = 0xf8 (the notice out of scope again); to 0x88704.
     0x886dc - 0x88700, 0x888c4 the ignored path (:226-227): a0 = s + 18184 (g_s.stats.rx_ignored); one check of
                      the 8-byte access (its shadow byte), then the 8-byte load, + 1, the 8-byte store back. The world
                      is now set_S_stats_rx_ignored Bw (u64 (S_stats_rx_ignored Bw + 1)).
     0x88704 - 0x8870c the header word 0x45e0360e stored at frame (every path).
     0x88710          s2 = 0 goes to 0x887a4 (the real-stack arm; not taken).
     0x88714 - 0x887a0 the release: the frame's 32 shadow bytes (256 bytes) = 0xf5 (released); a0 = the 8-byte load
                      at s2 + 248 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a0 (YG0d.v astack_free_law); to 0x887f4.
     0x887a4 - 0x887f0 the real-stack arm's release: shadow bytes 0..19 = 0.
     0x887f4 - 0x88830 sp = s0 - 128, ra and s0 .. s11 loaded back, sp = sp + 128, return. a0 .. a7 at the return are
                      not stated (void).
   No tail jump: the calls are jal with link (the stack malloc, the memset, maybe_online) and one jalr with link
   (notice); every j is inside the function, and the function ends with ret.
   The model and the code: the two tests at 0x88574 and 0x885a8 are on_ack_m's test of :225 (onack_ign: S_inflight
   Bw against 0 and fr_ack b against S_inflight_counter Bw, each a 32-bit compare), the store at s + 212 is
   set_S_inflight, the stores at s + 144 and s + 18184 are set_S_wake_acked and set_S_stats_rx_ignored (with u64 of
   the 64-bit sum), each a tw_write inside g_s's payload; the call at 0x88674 is call_notify at onack_w1 Bw with
   onack_ntc Bw b; the test at 0x88688 is on_ack_m's S_state B2 =? S_WAKING on notice's world B2; the call at
   0x886ac is maybe_online_m at set_S_wake_acked B2 1 (onack_model). B2 is set_GOT_acked (onack_w1 Bw) (GOT_acked
   Bw + 1) (notice_m's N_ACKED branch: int_inc, then check_inflight_acked_m, which returns its world, TCb.v), so B2
   and onack_w1 Bw agree in every field maybeon_wr reads (S_state, S_wake_acked, S_e1_named_us, S_last_rx_us,
   S_cfg_keepalive_ms, GOT.n); acall_kept_g keeps no byte of G, so the walk has this from the model. The code has no
   trap of its own; the model's None cases are call_notify's (S_notify <> ti_notice timg_A), notice's and
   maybe_online's, all ruled out by the model premise.
   Error paths (11 calls; no abort) and the facts that rule them out:
     TS___asan_report_load4 0x59608 (errpath_load4) at 0x88840 (s + 212), 0x88868 (s + 1744), 0x8888c (s + 112),
       0x8889c (s + 1748), 0x888b0 (s + 112);
     TS___asan_report_store4 0x59928 (errpath_store4) at 0x88878 (s + 212), 0x888c0 (s + 144);
     TS___asan_report_load8 0x596a8 (errpath_load8) at 0x888c4 (s + 18184), 0x888c8 (s + 96), 0x888cc (s + 104).
     Each guards a naturally aligned access inside g_s's payload [0x5df9c0, 0x5e4118) (2283 whole granules), whose
     shadow bytes are 0 (trans_onack_cells, read at each AR state by DgnTransportCg.v decode_zshadow_rd), so k = 0.
     TS___asan_report_load4 at 0x88854 (f + 24): fp mod 8 = 0, so [f + 24, f + 28) lies in one granule, and
     trans_dframe_at's decode_rd_ok gives range_addressable of the 64 bytes at fp at entry, still true at the
     shadow load of the check (0x88584): f lies in a frame of frames Sc, whose shadow bytes the stack malloc's
     acall_kept keeps, and the code's own stores before it reach only its own frames and their shadow bytes.
     The memset's own check (aintrin_realizes' pre, from the G journal through TransportGCg.v gx_intrin_at): the
     destination [p + 24, p + 64) lies in the frame this function took; its shadow bytes 7 .. 11 are 0 since 0x885dc
     and their hull is visible (astack_malloc_realizes' zero_shadow); each destination byte is a byte of the
     journal's own frame list after the stack malloc (YCbq.v awr_byte's in_frames: transport_twr_ok_g), not owned,
     not in the ESTACK bytes below sp.
   Writes: g_s's three fields (bytes of G); its own machine frame (the 8 zero bytes at sp at 0x88430, the saves at
   0x88434 - 0x88464, the frame word at s1 + 16); its own side-stack frame, that frame's shadow bytes and its flag
   byte; notice's stores (notice_wr, bytes of GOT); maybe_online's stores (maybeon_wr, bytes of G). No byte of a
   caller's frame or block is written (f and the bytes at buf are read only), so onack_wr is the written range. The
   G kit for the own frame is session_lost_cg.v's (TransportGCg.v dk_kept_own_g with dkg_nf and dkg_nf_sep,
   dk_kept_trans_nf_g, dkg_frame_al64, gx_intrin_at, dk_kept_frame_byte_g; CanKit.v can_stack_malloc_at and
   can_flag_store_pi read inside the G journal through gx_lift).
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_2 as astack_malloc_realizes ... ONACK_CID (with pc_stack_malloc (as_code B) ONACK_CID =
       transport_sigma TS___asan_stack_malloc_2): count_cid 2 (frames Sc) < fs_frames 2 from the count premise.
     __asan_memset as aintrin_realizes ... OSet (transport_sigma TS___asan_memset), call at 0x88618 (above).
     notice as notice_cg.v transport_notice_cg at TI.ti_notice timg_A (= 0x83578, notice_cg.v notice_at; call at
       0x88674; a G-form callee composed in the same G journal, no gx_call_cg):
       the journal: on_ack's G journal at the call state (the own frame live); ra = 0x88678 (ret_ok, 4096 <= ra);
       gp, tp kept; a1 = p;
       sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - NOTICE_STK: sp' >= sp - 144 and
       ONACK_STK >= 144 + NOTICE_STK; sp' <= sp0;
       trans_ntc_at p (onack_ntc Bw b): 0 < p and p mod 8 = 0 (p = frame + 32, dkg_frame_al64); trans_src_ok by
       decode_in_fake at the call state ([frame + 32, frame + 104) inside the 256 bytes of a frame of its frames)
       with decode_rd_ok (the bytes present by astack_malloc_realizes, shadow bytes 4..12 = 0, their hull visible);
       decode_off_win (the frame lies below alloc_ceiling, notice's window above it); NB = the 72 bytes stored at
       0x885e8 - 0x88644, whose fields are onack_ntc's; the body: pointer 0, length 0, garr8 of [], trans_src_ok of
       the empty range at 0 (DgnTransportCg.v trans_src_ok_null), decode_off_win of it (0 <= sp' - NOTICE_STK); the
       announce: n_ann = None with the pointer 0;
       trans_tframe_at TF at NOTICE_STK: on_ack's trans_tframe_at at ONACK_STK, carried: TF's bytes and their
       shadow are unchanged (onack_apart for the store at s + 212; the own frame is a fresh frame, apart from TF's
       placement; the record facts of the holds statement for the stack malloc's acall_kept), and notice's window
       lies inside on_ack's;
       trans_rom_view_rd at the call memory: no store of on_ack reaches a read-only byte, the memset keeps every
       byte outside its destination and ESTACK bytes (gx_intrin_at), and the stack malloc's acall_kept keeps every
       TRANS_RO_RD byte (trans_ro_rd_scoped, from trans_ro_rd_unowned and trans_rom_no_errno);
       tw_at at onack_w1 Bw: G kept through the stack malloc (gx_kept_of_acall_kept: gx_ok, gx_noerrno), then the
       tw_write of :229;
       notice_m timg_A TF (onack_w1 Bw) (onack_ntc Bw b) = Some (B2, tt): the model premise through onack_model (on
       this path onack_ign Bw b = false; call_notify's test is the indirect target's value);
       notice_apart: a byte of notice_wr is a byte of GOT (kind N_ACKED: GOT.acked), a byte of G, so not a byte of
       p's frame (a frame byte is outside the image: AR_laws' al_client_img); the body range is empty and n_ann =
       None; TF's range: onack_apart, since notice_wr (onack_w1 Bw) (onack_ntc Bw b) lies inside onack_wr Bw b;
       the N_DATA premise: vacuous (n_kind = N_ACKED);
       st_nev S + k + NOTICE_EV <= EV_MAX: ONACK_EV = NOTICE_EV + MAYBEON_EV, and the stack malloc records no event.
       Its X: tw_at at B2.
     maybe_online as maybe_online_cg.v transport_maybe_online_cg at transport_sigma TS_maybe_online (call at
       0x886ac; a G-form callee in the same G journal): the journal at the call state (the own frame live); ra =
       0x886b0; gp, tp kept; a0 = s = MAYBEON_S; sp' 32-aligned, sp0 - STK <= sp' - MAYBEON_STK (ONACK_STK = 144 +
       MAYBEON_STK), sp' <= sp0; tw_at at set_S_wake_acked B2 1 (notice's X, then the tw_write of :234);
       g_fail_next (set_S_wake_acked B2 1) <= 1 (notice and the stores of :229 and :234 leave the byte as it was:
       g_fail_next Bw <= 1); maybe_online_m timg_A TF (set_S_wake_acked B2 1) = Some (Bw', tt) (the model premise
       through onack_model, on the path where S_state B2 = S_WAKING); trans_tframe_at TF at MAYBEON_STK (carried as
       for notice, then across notice's acall_kept_g by trans_src_ok_kept over its clauses, which reach TF because
       trans_tf_off_g puts it outside G and onack_apart outside notice_wr (onack_w1 Bw) (onack_ntc Bw b), and across
       the store of :234 (onack_apart); maybe_online's window lies inside on_ack's); trans_rom_view_rd at the call
       memory (as for notice, and across notice's acall_kept_g: its image clause keeps every TRANS_RO_RD byte outside
       G, the owned statics and errno); maybeon_apart TF
       (set_S_wake_acked B2 1): onack_apart, since maybeon_wr of that world is maybeon_wr (set_S_wake_acked
       (onack_w1 Bw) 1) (maybeon_wr reads S_state, S_wake_acked, S_e1_named_us, S_last_rx_us,
       S_cfg_keepalive_ms and GOT.n, none of which notice's N_ACKED store GOT.acked changes), a part of onack_wr
       Bw b; count_cid 2 at the call state = count_cid 2 (frames Sc) + 1 < fs_frames 2 (the count premise);
       st_nev: the event count after notice plus MAYBEON_EV, inside ONACK_EV. Its X: tw_at at Bw' and
       g_fail_next Bw' <= 1.
   notice's and maybe_online's own record facts are premises of their holds statements.
   Stack: 128 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the memset), notice's NOTICE_STK or maybe_online's MAYBEON_STK:
   ONACK_STK = 144 + MAYBEON_STK (onack_stk_eq).

   The caller: diginet_session_rx at 0x87998 (return address 0x8799c), for a frame whose cmd byte (f + 30, the
   1-byte load at 0x87954) is 0xa0 (DIGINET_CMD_ACK): a0 = s4 (its own a0, &g_s), a1 = s6 = its class-1 side-stack
   frame + 32 (its struct diginet_frame f, filled by diginet_frame_parse at 0x876e0 from its a1 / a2 = buf and the
   length; the frame's shadow bytes 4..11, f's 64 bytes, set to 0 at 0x87698 - 0x876b4). It supplies its G
   journal, tw_at, g_fail_next, the model premise (its branch of diginet_session_rx_m), trans_dframe_at of f and
   buf, trans_tframe_at, onack_apart and trans_tf_off_g of its TF (the last two from its plain tframe_at's
   off_world clause), trans_rom_view_rd, and count_cid 2 (frames Sc) + 1 <
   fs_frames 2 (its own frame is of class 1).

   Also defined here (on_data and on_announce take the same frame): trans_dframe_at, the ASan form of
   lib/Prog/T/TSessC.v dframe_at. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* on_ack's frame (`sp = sp - 128` at TS_on_ack), the at most 0x10 bytes of `sp = sp & -32` (0x8846c) below it, and
   the largest stack a callee uses below the realigned sp: ESTACK for __asan_stack_malloc_2 and __asan_memset
   (YG0d.v ecall_pre), notice's NOTICE_STK, maybe_online's MAYBEON_STK. *)
Definition ONACK_FRAME : Z := 128.
Definition ONACK_ALIGN : Z := 0x10.
Definition ONACK_STK : Z := ONACK_FRAME + ONACK_ALIGN + Z.max ESTACK (Z.max NOTICE_STK MAYBEON_STK).
Lemma onack_stk_eq : ONACK_STK = ONACK_FRAME + ONACK_ALIGN + MAYBEON_STK.
Proof. reflexivity. Qed.
(* No allocator event: notice and maybe_online record none, and the class-2 stack malloc and its release record none
   (YG00.v stack_malloc, stack_free). *)
Definition ONACK_EV : Z := NOTICE_EV + MAYBEON_EV.
(* The side-stack class (a0 = 160 at 0x88498, the call of __asan_stack_malloc_2 at 0x8849c): maybe_online's class,
   hence the + 1 of the count premise. *)
Definition ONACK_CID : Z := 2.
Lemma onack_cid_maybeon : ONACK_CID = MAYBEON_CID.
Proof. reflexivity. Qed.
(* Its first argument: g_s's base in image A. *)
Definition ONACK_S : Z := TA_g_s.
(* The addresses of the g_s fields the code reads or writes (s + 212, s + 1744, s + 112, s + 1748, s + 96, s + 104,
   s + 144, s + 18184). *)
Lemma onack_addrs :
  ONACK_S = 0x5df9c0 /\
  ONACK_S + (TW.A_S_inflight - TW.OFF_g_s) = 0x5dfa94 /\
  ONACK_S + (TW.A_S_inflight_counter - TW.OFF_g_s) = 0x5e0090 /\
  ONACK_S + (TW.A_S_state - TW.OFF_g_s) = 0x5dfa30 /\
  ONACK_S + (TW.A_S_inflight_retries - TW.OFF_g_s) = 0x5e0094 /\
  ONACK_S + (TW.A_S_notify - TW.OFF_g_s) = 0x5dfa20 /\
  ONACK_S + (TW.A_S_notify_ctx - TW.OFF_g_s) = 0x5dfa28 /\
  ONACK_S + (TW.A_S_wake_acked - TW.OFF_g_s) = 0x5dfa50 /\
  ONACK_S + (TW.A_S_stats_rx_ignored - TW.OFF_g_s) = 0x5e40c8.
Proof. repeat split; reflexivity. Qed.

(* The model's steps (TSess.v on_ack_m): the test of :225, the world after the store of :229, and the notice of
   :230-231. *)
Definition onack_ign (Bw b : list byte) : bool :=
  (TW.S_inflight Bw =? 0) || negb (DSpec.fr_ack b =? TW.S_inflight_counter Bw).
Definition onack_w1 (Bw : list byte) : list byte := TW.set_S_inflight Bw 0.
Definition onack_ntc (Bw b : list byte) : TI.ntc :=
  TI.Ntc TS0.DIGINET_N_ACKED (TW.S_state (onack_w1 Bw)) 0 0 (DSpec.fr_ack b)
    (DSpec.u16 (TW.S_inflight_retries (onack_w1 Bw))) 0 0 None [] 0.
Lemma onack_model : forall (I : TI.timg) (F : option TI.tframe) (Bw b : list byte),
  TSS.on_ack_m I F Bw b =
  if onack_ign Bw b then Some (TW.set_S_stats_rx_ignored Bw (TS0.u64 (TW.S_stats_rx_ignored Bw + 1)), tt)
  else
    match TSS.call_notify I F (onack_w1 Bw) (onack_ntc Bw b) with
    | None => None
    | Some (B2, _) =>
        if TW.S_state B2 =? TS0.DIGINET_S_WAKING then TSS.maybe_online_m I F (TW.set_S_wake_acked B2 1)
        else Some (B2, tt)
    end.
Proof. intros I F Bw b. reflexivity. Qed.

(* The bytes some path of the call stores into G (each path stores a subset, on_ack_m): g_s's stats.rx_ignored
   (8 bytes), inflight and wake_acked (4 bytes each), notice's stores for the N_ACKED notice (notice_cg.v notice_wr:
   GOT.acked) and maybe_online's (maybe_online_cg.v maybeon_wr at the world it is called with, whose reads
   maybeon_wr (set_S_wake_acked (onack_w1 Bw) 1) gives: notice's store of GOT.acked changes none of them). *)
Definition onack_wr (Bw b : list byte) (a : Z) : Prop :=
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_rx_ignored 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight 4 a \/
  notice_wr (onack_w1 Bw) (onack_ntc Bw b) a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_wake_acked 4 a \/
  maybeon_wr (TW.set_S_wake_acked (onack_w1 Bw) 1) a.

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. notice and maybe_online read TF after the store at s + 212 (notice_cg.v notice_apart, maybe_online_cg.v
   maybeon_apart). *)
Definition onack_apart (Fr : option TI.tframe) (Bw b : list byte) : Prop :=
  forall x, onack_wr Bw b x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented checks of the accesses at s + 96 .. s + 215, s + 1744 .. s + 1749 and s + 18184 read it. *)
Definition trans_onack_cells (B : asyms) : Prop := decode_zshadow_at B ONACK_S (ONACK_S + TW.SZ_g_s).

Section onack. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The struct diginet_frame f a session function receives from diginet_session_rx (lib/Prog/T/TSessC.v dframe_at),
   read through the walk's image view: the frame bytes b at buf, parsed with code 0, placed by trans_src_ok, outside
   the callee's stack window [sp - K, sp) and apart from G (dframe_at's arg_blk); the 64 bytes at fp as the parse
   left them (DgnTransportCg.v frame_f_bytes buf b fj: lib/Prog/diginet_frame_parse_c.v parse_cells at fr_code b =
   0, TSessC.v dframe_cells one cell for one), in one of the caller's live side-stack frames (diginet_session_rx's
   class-1 frame), visible and marked usable (decode_rd_ok), outside the callee's window, fp 8-aligned. *)
Definition trans_dframe_at (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
    (regs : bvmap 5 word) (K fp buf : Z) (b fj : list byte) : Prop :=
  DSpec.fr_code b = 0 /\
  0 < buf /\ garr8 segs (mrestrict (w_H W) memc) buf (TW.zs b) /\
  trans_src_ok B lyc Sc W memc buf (Z.of_nat (length b)) /\
  decode_off_win regs K buf (Z.of_nat (length b)) /\
  (forall x, buf <= x < buf + Z.of_nat (length b) -> ~ inG TG.G_HARNESS x) /\
  0 < fp /\ fp mod 8 = 0 /\ length fj = 64%nat /\
  garr8 segs (mrestrict (w_H W) memc) fp (frame_f_bytes buf b fj) /\
  decode_in_fake lyc Sc fp FRAME_F_SIZE /\
  decode_rd_ok W memc fp FRAME_F_SIZE /\
  decode_off_win regs K fp FRAME_F_SIZE.

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range onack_wr Bw b,
   no meter charge (the side-stack frame changes st_fs only), and X: the world relation at the model's world Bw' and
   g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this function takes is
   released. *)
Definition transport_onack_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' b : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    ONACK_STK ONACK_EV 0 (onack_wr Bw b)
    (fun regs2 W2 mem2 => tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_on_ack_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 ONACK_S -> YK11.getr regs 11 = w64 fp ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - ONACK_STK -> spZ regs <= sp0 ->
    trans_dframe_at lyc Sc W memc regs ONACK_STK fp buf b fj ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.on_ack_m timg_A TF Bw b = Some (Bw', tt) ->
    trans_tframe_at B lyc Sc W memc regs ONACK_STK TF ->
    trans_tf_off_g TF ->
    trans_rom_view_rd W memc ->
    onack_apart TF Bw b ->
    count_cid ONACK_CID (frames Sc) + 1 < fs_frames ONACK_CID ->
    st_nev S + k + ONACK_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_onack_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

(* The statement the walk will prove: the class-2 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the record facts that no byte of G and
   no TRANS_RO_RD byte is an owned static or errno (they carry TF's trans_src_ok, f's bytes, G and the TRANS_RO_RD
   bytes across the stack malloc's acall_kept and notice's acall_kept_g; DgnTransportCg.v G_HARNESS_gx_ok /
   G_HARNESS_gx_noerrno give gx_ok and gx_noerrno from the first two), the allocator, meter and side-stack laws, and
   the contracts of __asan_stack_malloc_2, __asan_memset, notice (at the value the session's notify pointer holds) and
   maybe_online give the contract at TS_on_ack. *)
Definition transport_on_ack_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) ONACK_CID = transport_sigma TS___asan_stack_malloc_2 ->
  transport_cells B -> trans_onack_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B ONACK_CID) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  (forall fx' : YK11.FPState, @transport_maybe_online_cg fx' rc B MT (transport_sigma TS_maybe_online)) ->
  transport_on_ack_cg (transport_sigma TS_on_ack).
End onack.
