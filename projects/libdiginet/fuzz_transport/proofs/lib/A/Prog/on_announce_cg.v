(* on_announce_cg: the ASan walk contract of on_announce (transport/src/diginet_session.c:184-221, with find_mac
   (:168-174) and two copies of session_lost (:160-165), each with its set_state (:79-86), inlined; model
   lib/TModel/TSess.v on_announce_m) on fuzz_transport.asan (e89be137db17) at 0x87a74 = transport_sigma TS_on_announce,
   size 2488, as STATEMENTS only (no proof). It stores into g_s, a harness global, takes a class-4 side-stack frame
   for its local struct diginet_announce a and four struct diginet_notice, calls diginet_announce_parse (a leaf that
   writes a), diginet_personality_from_name (a donor-form callee), the bcmp wrapper, __asan_memset, notice through the
   session's notify pointer, diginet_session_wake and maybe_online (G-form callees) while that frame is live, so it is
   a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v
   G_HARNESS with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post
   (acall_kept_g over G_HARNESS). Its form is on_ack_cg.v's and on_data_cg.v's: a G walk with a side-stack frame of
   its own; its frame argument is on_ack_cg.v's trans_dframe_at.

   The contract. a0 = s = &g_s = 0x5df9c0 (TWorldA.v TA_g_s); a1 = fp, the struct diginet_frame f that
   diginet_session_rx's diginet_frame_parse filled from the frame bytes b at buf (on_ack_cg.v trans_dframe_at, the
   ASan form of lib/Prog/T/TSessC.v dframe_at); a2 = now (a uint64_t). TF is the current heap frame
   (check_state_data_cg.v trans_tframe_at at this call's window); the read-only bytes the callees read are the
   image's (trans_rom_view_rd). The memory relates to the world Bw by image A's world relation (TWorldG.v tw_at at
   TWorldA.v TMAP_A, read through aview), g_fail_next Bw <= 1, and on_announce_m timg_A TF Bw b now = Some (Bw', tt).
   No byte the call stores is a byte of TF (onann_apart), and no byte of TF is a byte of G (check_state_data_cg.v
   trans_tf_off_g). Class 4 of the side stack has a free frame (its own), and class 2 has three
   (diginet_session_wake's, then send_control's and diginet_body_check's inside it, while its own frame is live). The
   function returns to ra with the callee-saved registers kept, no allocator event and no meter
   charge (its side-stack frame changes the state's st_fs only: ameter_fs_laws), its side-stack frame released (the
   caller's frames exactly), the caller's blocks exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or
   above alloc_ceiling outside the call's stack window [sp - ONANN_STK, sp), the image bytes outside G, the owned
   statics and errno, the caller's block and frame bytes outside onann_wr Bw b), the world relation at Bw', and
   g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/on_announce_c.v): a0 = W_BASE_PLAIN +
   OFF_g_s -> a0 = TA_g_s; a1 = fp kept; a2 = now, 0 <= now < 2 ^ 64 kept; dframe_at m sp FRAME fp buf b fj ->
   trans_dframe_at at ONANN_STK (on_ack_cg.v gives the translation of each part); wmem -> tw_at; g_fail_next B <= 1
   kept as a premise (the code neither reads nor writes g_fail_next; diginet_session_wake's and maybe_online's
   statements ask it) and the post's g_fail_next B' <= 1 kept in X (from the premise on the paths that call neither,
   else from the X of the last of them; notice and the stores after them do not touch the byte); on_announce_m
   verbatim at timg_A; tframe_at -> trans_tframe_at at ONANN_STK, and its off_world clause -> two facts, since
   check_state_data_cg.v trans_tframe_at drops that clause: onann_apart, no byte the call stores is a byte of TF
   (maybe_online_cg.v maybeon_apart's form), and trans_tf_off_g (check_state_data_cg.v), no byte of TF is a byte of
   G. on_announce needs trans_tf_off_g for its own walk: it carries TF across notice (calls at 0x87e48, 0x87f50 and
   0x880b0), which writes G (GOT.desk, GOT.foreign, or GOT.t[GOT.n] and GOT.n), to a later call that takes TF
   (notice at 0x87f50, 0x880b0 or 0x88184, diginet_session_wake at 0x87fb4, maybe_online at 0x87ff8): notice's
   acall_kept_g keeps the image bytes outside G only, and its X pins G only to the model world, so it carries no byte
   of a TF inside G. diginet_session_wake's statement asks it too (send_control, then notice, inside wake); relro_img
   -> trans_rom_view_rd; stk, lo + FRAME <= sp, sp mod 16 and w_off_stack -> the journal's window premises; mem_inv is
   dropped. The post's munch, wmono, stk and mem_inv -> transport_cg_post (the journal at the return, acall_kept_g
   over onann_wr Bw b); wmem -> X's tw_at.
   Premises the plain contract does not have:
   - count_cid 4 (frames Sc) < fs_frames 4: its own class-4 frame. With it __asan_stack_malloc_4 returns a frame
     (astack_malloc_realizes), so the real-stack arm is not taken.
   - count_cid 2 (frames Sc) + 2 < fs_frames 2:
     diginet_session_wake's statement asks count_cid 2 (frames Sc') + 2 < fs_frames 2 at its call state, whose
     frames Sc' are the own class-4 frame :: frames Sc (the same class-2 count); maybe_online's count_cid 2 <
     fs_frames 2 follows. personality_from_name, notice, the leaf and the intrinsics take no side-stack frame.
   - onann_apart and trans_tf_off_g (above).
   - the run invariants (1) and (4) of diginet_session_wake, and (4)'s index bound g_ncmd Bw <= CMDS_MAX (below).
   - in the holds statement: trans_onann_cells (g_s's zero shadow), the side-stack laws, and trans_g_unowned,
     trans_g_no_errno, trans_ro_rd_unowned and trans_rom_no_errno: they carry the trans_src_ok of TF and of the bytes
     at buf across the stack malloc (DgnTransportCg.v trans_src_ok_inner with their bytes kept by its acall_kept
     and trans_rd_ok_sh; the fresh frame is apart from their placement: trans_src_ok_disj_own) and
     personality_from_name's acall_kept (through gx_call_cg; trans_src_ok_acall), and TF's across notice's
     acall_kept_g (trans_src_ok_kept over its clauses, TF lying outside G by trans_tf_off_g; trans_src_ok_acall_g
     asks every byte of G to be kept, which notice does not give; the bytes at buf are read only by the leaf and the
     bcmp wrapper, before the first notice), the TRANS_RO_RD bytes (trans_rom_view_rd for personality_from_name,
     notice, diginet_session_wake and maybe_online), and G (TransportGCg.v gx_kept_of_acall_kept and gx_call_cg
     with gx_ok and gx_noerrno, which DgnTransportCg.v G_HARNESS_gx_ok and G_HARNESS_gx_noerrno give from the first
     two), as send_data_cg.v takes them. The bytes of f (f + 30's shadow byte is loaded at 0x87e50 and f + 30 at
     0x87e58, after the first notice) and their shadow lie in a frame of frames Sc, outside every callee's written
     range and window: the frame clause of acall_kept and acall_kept_g keeps them, and the leaf, the bcmp wrapper and
     the intrinsics keep every byte outside their windows and destinations.
   Run invariants carried (on its own Bw): (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME and (4)
   every PENDING command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX, both diginet_session_wake_cg.v's
   premises (for io_send, through send_control). The world on_announce hands diginet_session_wake differs from Bw only
   in g_s's personality, foreign, inflight, desk_counter_valid and state and in notice's stores (GOT.desk for the desk
   notice, GOT.t[GOT.n] and GOT.n for the inlined session_lost's notice): no byte of M, of g_cmd[0 .. CMDS_MAX) or of
   g_ncmd, so with the index bound TW.g_ncmd Bw <= TC.CMDS_MAX, a premise beside (4), both carry verbatim. Without it
   (4) would not carry: for s >= CMDS_MAX g_cmd[s]'s fields are other world bytes, and a notice's store into GOT.t
   can be one of them (GOT.t[5].old is A_Cmd_st 1131). diginet_session_wake does not take the bound (the world it
   hands send_control differs from its own only inside g_s, below g_cmd); no function on_announce calls writes
   g_ncmd, and the caller has the bound from the plain run (lib/TSim/Agree.v d3_ncmd and d3_ops, OPS_MAX =
   CMDS_MAX). notice's premise for a data notice (check_state_data's run invariant) holds vacuously at each of its
   four calls: their kinds are N_DESK (the store of 1 at n by 0x87da8), N_STATE (the stores of 2 at 0x87f10 and
   0x88140)
   and N_FOREIGN (the store of 6 at 0x8803c). maybe_online, personality_from_name and the leaf carry none; the others
   (check_latest_queue's, take's cfg bounds) are not reached from on_announce. on_announce's own instrumented accesses
   are at fixed offsets of g_s (s + 16 .. s + 19, s + 96 .. s + 115, s + 128 .. s + 143, s + 168 .. s + 171, s + 212 ..
   s + 215, s + 18184 .. s + 18191), at f + 30 and in its own frame; its bcmp ranges are [buf + 30 + i, + 6) (i <= 9,
   inside b: the model's ann_code 0 gives fr_body_len b >= 33) and [s, s + 6); its memsets fill 28, 56, 40 and 56
   bytes of its own frame, so its code needs no bound that the model does not give.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   2488 code bytes are equal in both files), 622 words; s = s4 (until 0x880fc), f = s6, now = s10 (kept at s1 + 0
   from 0x87d10), the frame = s2, its first shadow byte s3 = (frame >> 3) + 0x7fff8000:
     0x87a74 - 0x87ab0 sp = sp - 192; 0x87a78 stores 8 zero bytes at sp; ra at sp + 184, s0 .. s11 at sp + 176 ..
                      sp + 88, loaded back at 0x88250 - 0x88280; s0 = sp + 192 (the entry sp, kept to 0x8824c).
     0x87ab4 - 0x87ac0 sp = sp & -32 (at most 0x10 below entry - 192); s1 = the realigned sp; s10 = now, s6 = fp.
     0x87ac4 - 0x87adc a2 = the 8-byte load of the GOT word 0xa40e8 (it holds 0xaca00), then the 4-byte load of the
                      flag word at 0xaca00; a1 = the 8-byte load of the GOT word 0xa4090 (it holds 0xac9f8), s8 = the
                      8-byte load at 0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s4 = s.
     0x87ae0 - 0x87af4 the flag word = 0 goes to 0x87af4 (s7 = 0); transport_cells row 6 gives 1. a0 = 576 and the
                      call of __asan_stack_malloc_4 (frame_alloc_4, 0x3db38 = transport_sigma
                      TS___asan_stack_malloc_4) at 0x87ae8, return address 0x87aec: a class-4 side-stack frame
                      (fs_frame_bytes 4 = 1024 bytes); s7 = the result.
     0x87af8 - 0x87b18 s2 = s7; s7 <> 0 goes to 0x87b1c. The real-stack arm (s7 = 0): s2 = (sp - 576) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s2), then sp = s2. With
                      count_cid 4 (frames Sc) < fs_frames 4 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s2 = s7.
     0x87b1c - 0x87b20 the 8-byte store of frame at s1 + 80 (its own machine frame); s5 = a = frame + 256.
     0x87b24 - 0x87b58 the frame header: 0x41b58ab3 at frame, the description string 0x123a6 ("5 32 72 10 n.i.i90:83
                      144 72 8 n.i.i:83 256 40 5 a:186 336 72 5 n:196 448 72 6 fn:217": five variables, the inlined
                      set_state notices n3 at frame + 32 and n2 at frame + 144, a at frame + 256 (40 bytes), the
                      desk notice n at frame + 336 and the foreign notice fn at frame + 448, each notice 72 bytes)
                      at frame + 8, the function's address 0x87a74 at frame + 16.
     0x87b5c - 0x87c7c the frame's 72 shadow bytes (576 bytes): 0..3 = 0xf1; 4..12 = 0xf8 (n3, out of scope);
                      13..17 = 0xf2; 18..26 = 0xf8 (n2); 27..31 = 0xf2; 32..36 = 0 (a, usable); 37..41 = 0xf2;
                      42..50 = 0xf8 (n); 51..55 = 0xf2; 56..64 = 0xf8 (fn); 65..71 = 0xf3.
     each instrumented check below: the shadow byte k at (x >> 3) + 0x7fff8000; k = 0 goes on; for a 1-byte access
                      (x & 7) < k (signed), for a 4-byte access ((x & 7) + 3) < k (signed) goes on; for an 8-byte
                      access any k <> 0 goes to the error path.
     0x87c80 - 0x87c88 a0 = fp, a1 = a; the call of diginet_announce_parse (0x8c238 = transport_sigma
                      TS_diginet_announce_parse) at 0x87c88, return address 0x87c8c (:187).
     0x87c8c - 0x87cb8 a0 = 0 goes to 0x87cbc. Else (:188-189): a0 = s + 18184 (g_s.stats.rx_ignored), the check of
                      the 8-byte access, the 8-byte load, + 1, the 8-byte store back; to 0x88200.
     0x87cbc - 0x87cc4 a0 = a + 10 (a.name); the call of diginet_personality_from_name (0x8c484 = transport_sigma
                      TS_diginet_personality_from_name) at 0x87cc0, return address 0x87cc4 (:191); s9 = p, the result.
     0x87cc8 - 0x87ce0 p = 0 goes to 0x87ce4; else the check of the 8-byte store at s + 128 and the store of p there
                      (g_s.personality, :192-193).
     0x87ce4 - 0x87cfc the 8-byte store of a at s1 + 56; s11 = fp + 30; the check of the 1-byte load at f + 30 (its
                      shadow byte's address a2, kept at s1 + 32 by 0x87d14); a0 = cmd = the 1-byte load at f + 30.
     0x87d00 - 0x87d18 s5 = n = frame + 336; a1 = 0xe1, a3 = off = -1; the stores of s7 at s1 + 40, of now at s1 + 0,
                      of a2 at s1 + 32; cmd <> 0xe1 (DIGINET_CMD_ANNOUNCE_SESSION) goes to 0x87d7c (:194).
     0x87d1c - 0x87d78 find_mac (:168-174): fp kept at s1 + 48; s6 = the 8-byte load at a + 32 (unknown_len, 15:
                      the leaf's X), s10 = 6; s6 < 6 (unsigned) goes to 0x87d78; s8 kept at s1 + 24; s7 = the 8-byte
                      load at a + 24
                      (unknown = buf + 30, the leaf's X), s8 = i = 0; the loop: a0 = s7 + s10 - 6 = unknown + i, a1 = s,
                      a2 = 6, the call of the bcmp wrapper (0x42cf8 = transport_sigma TS___interceptor_trampoline_bcmp)
                      at 0x87d4c, return address 0x87d50; a result 0 goes to 0x87d70 (a3 = i); else s10 = s10 + 1,
                      s8 = s8 + 1 (32-bit), s10 <= s6 (unsigned) goes round again, and after the ten turns
                      i = 0 .. 9 a3 = -1. s8
                      and s6 = fp are loaded back from s1 + 24 and s1 + 48. The loads at a + 24 and a + 32 have no
                      instrumented check.
     0x87d7c - 0x87d9c shadow bytes 42..50 = 0 (n usable).
     0x87da0 - 0x87dbc the 4-byte store of 1 (N_DESK) at n (kind, :196); a0 = s + 112, s10 = its shadow byte's address;
                      the check of the 4-byte load at s + 112.
     0x87dc0 - 0x87de4 s + 112 kept at s1 + 48; a1 = the 4-byte load at s + 112 (S_state); stores into n: a1's low 32
                      bits at n + 4 (state), 8 zero bytes at n + 8 (old_state, reason), the 8 bytes of fp at n + 16
                      (n.frame, which notice does not read); the check of the 8-byte store at n + 24 (frame + 360).
     0x87de8 - 0x87e08 the 8-byte stores of a at n + 24 (n.announce) and of p at n + 32 (n.personality); s7 = off and
                      its 4-byte store at n + 40 (n.mac_offset, :197); a0 = n + 44, a1 = 0 (the shadow byte loaded at
                      0x87de0), a2 = 28; the call of __asan_memset (checked_memset, 0x5284c = transport_sigma
                      TS___asan_memset) at 0x87e08, return address 0x87e0c: n's bytes 44 .. 71 set to 0 (padding, body,
                      body_len, counter, retry, padding).
     0x87e00, 0x87e0c - 0x87e38 s9 = s + 96, kept at s1 + 24, its shadow byte's address at s1 + 8; the check of the
                      8-byte load at s + 96; s9 = s + 104, its shadow byte's address at s1 + 16; the check of the 8-byte
                      load at s + 104.
     0x87e3c - 0x87e48 a2 = the 8-byte load at s + 96 (S_notify: tw_read, and the model's call_notify gives
                      TI.ti_notice timg_A = 0x83578); a0 = the 8-byte load at s + 104 (notify_ctx, which notice does
                      not read); a1 = n; the indirect call (jalr a2) at 0x87e48, return address 0x87e4c (:198;
                      struct diginet_session + 96, notify -> notice).
     0x87e4c - 0x87e64 the check of the 1-byte load at f + 30 (its shadow byte's address from s1 + 32); a1 = cmd = the
                      1-byte load at f + 30; a0 = s + 136; cmd <> 0xe0 (DIGINET_CMD_ANNOUNCE) goes to 0x87fbc (:200).
     0x87e68 - 0x87e7c the check of the 4-byte store at s + 136 (s7 loaded back from s1 + 40); the store of 0 at s + 136
                      (g_s.foreign = 0, :201).
     0x87e80 - 0x87e94 the check of the 4-byte load at s + 112 (its shadow byte read through s10); a0 = the 4-byte load
                      at s + 112 (address from s1 + 48); <> 2 (S_ONLINE) goes to 0x87f8c (:202).
     0x87e98 - 0x87f50 the inlined session_lost (:203, :162-164, set_state :83-85): the checks of the 4-byte stores at
                      s + 212 and s + 168 and the stores of 0 there (inflight, desk_counter_valid); s5 = n2 = frame +
                      144; shadow bytes 18..26 = 0 (n2 usable); a0 = n2 + 16, a1 = 0, a2 = 56, the call of
                      __asan_memset at 0x87efc, return address 0x87f00 (n2's bytes 16 .. 71 = 0: frame, announce,
                      personality, mac_offset, padding, body, body_len, counter, retry, padding); the 8-byte store of 2
                      at n2 (kind N_STATE = 2, state S_IDLE = 0) and of (3 << 32) + 2 at n2 + 8 (old_state 2 =
                      S_ONLINE, reason 3 = DIGINET_R_DESK_OFFLINE); the check of the 4-byte store at s + 112 (s10) and
                      the store of 0 there (state = S_IDLE); the checks of the 8-byte loads at s + 96 and s + 104 (their
                      shadow bytes' addresses from s1 + 8 and s1 + 16); a2 = notify (address from s1 + 24), a0 =
                      notify_ctx, a1 = n2; the indirect call (jalr a2) at 0x87f50, return address 0x87f54.
     0x87f54 - 0x87f78 shadow bytes 18..26 = 0xf8 (n2 out of scope).
     0x87f7c - 0x87f88 the check of the 4-byte load at s + 112; a0 = the 4-byte load at s + 112.
     0x87f8c - 0x87fa8 a0 <> 0 (not S_IDLE) goes to 0x881d8; the check of the 4-byte load at s + 16 (cfg.auto_wake);
                      its value 0 goes to 0x881d8 (:204).
     0x87fac - 0x87fb8 a0 = s, a1 = now (the 8-byte load at s1 + 0); the call of diginet_session_wake (0x866fc =
                      transport_sigma TS_diginet_session_wake) at 0x87fb4, return address 0x87fb8 (:205; its result is
                      not used); to 0x881d8.
     0x87fbc - 0x87fc4 (cmd = 0xe1) a1 = the shadow byte's address of s + 136; off < 0 (s7) goes to 0x88000 (:209).
     0x87fc8 - 0x87ff0 the check of the 4-byte store at s + 136 and the store of 0 (g_s.foreign = 0, :211); the check of
                      the 4-byte store at s + 140 (s7 loaded back from s1 + 40) and the store of 1 (g_s.e1_named_us =
                      1, :212).
     0x87ff4 - 0x87ffc a0 = s; the call of maybe_online (0x8b170 = transport_sigma TS_maybe_online) at 0x87ff8, return
                      address 0x87ffc (:213); to 0x881d8.
     0x88000 - 0x88048 (off < 0) the check of the 4-byte store at s + 136; s5 = fn = frame + 448; the store of 1 at
                      s + 136 (g_s.foreign = 1, :216); shadow bytes 56..64 = 0 (fn usable); the 4-byte store of 6
                      (N_FOREIGN) at fn (kind, :217); the check of the 4-byte load at s + 112 (s10).
     0x8804c - 0x88080 a1 = the 4-byte load at s + 112; stores into fn: a1's low 32 bits at fn + 4, 8 zero bytes at
                      fn + 8, the 8 bytes of fp at fn + 16; the check of the 8-byte store at fn + 24 (frame + 472); a at
                      fn + 24 (fn.announce); a0 = fn + 32, a1 = 0 (the shadow byte loaded at 0x88068), a2 = 40; the call
                      of __asan_memset at 0x88080, return address 0x88084: fn's bytes 32 .. 71 = 0 (personality,
                      mac_offset, padding, body, body_len, counter, retry, padding).
     0x88084 - 0x880b0 the checks of the 8-byte loads at s + 96 and s + 104 (s7 loaded back from s1 + 40); a2 = notify,
                      a0 = notify_ctx, a1 = fn; the indirect call (jalr a2) at 0x880b0, return address 0x880b4 (:218).
     0x880b4 - 0x880cc the check of the 4-byte load at s + 112; s5 = the 4-byte load at s + 112; (s5 - 1) (32-bit) > 1
                      (unsigned) goes to 0x881b0 (neither S_WAKING nor S_ONLINE, :219).
     0x880d0 - 0x88184 the inlined session_lost (:220, :162-164, set_state :83-85): the checks of the 4-byte stores at
                      s + 212 and s + 168 and the stores of 0 there; s4 = n3 = frame + 32; shadow bytes 4..12 = 0 (n3
                      usable); a0 = n3 + 16, a1 = 0, a2 = 56, the call of __asan_memset at 0x88134, return address
                      0x88138 (n3's bytes 16 .. 71 = 0); the 8-byte store of 2 at n3 (kind N_STATE, state S_IDLE), the
                      4-byte stores of s5 at n3 + 8 (old_state) and of 5 at n3 + 12 (reason DIGINET_R_FOREIGN); the
                      check of the 4-byte store at s + 112 and the store of 0 there (address from s1 + 48); the checks
                      of the 8-byte loads at s + 96 and s + 104; a2 = notify (address from s1 + 24), a0 = notify_ctx
                      (address s9), a1 = n3; the indirect call (jalr a2) at 0x88184, return address 0x88188.
     0x88188 - 0x881ac shadow bytes 4..12 = 0xf8 (n3 out of scope).
     0x881b0 - 0x881d4 shadow bytes 56..64 = 0xf8 (fn out of scope).
     0x881d8 - 0x881fc shadow bytes 42..50 = 0xf8 (n out of scope).
     0x88200 - 0x88214 shadow bytes 32..36 = 0xf8 (a out of scope; every path).
     0x88218 - 0x88220 the header word 0x45e0360e stored at frame (every path).
     0x88224          s7 = 0 goes to 0x88240 (the real-stack arm; not taken).
     0x88228 - 0x8823c the release: a0 = s3 (the frame's first shadow byte), a1 = 128; the call of __asan_set_shadow_f5
                      (meta_fill_f5, 0x55378 = transport_sigma TS___asan_set_shadow_f5) at 0x88230, return address
                      0x88234: the frame's 128 shadow bytes (1024 bytes) = 0xf5 (released); a0 = the 8-byte load at
                      s7 + 1016 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a0 (YG0d.v astack_free_law); to 0x8824c.
     0x88240 - 0x88248 the real-stack arm's release: a0 = s3, a1 = 72, the call of __asan_set_shadow_00 (meta_fill_00,
                      0x55270 = transport_sigma TS___asan_set_shadow_00) at 0x88248 (shadow bytes 0..71 = 0). Not
                      reached (above), so its contract is not a premise.
     0x8824c - 0x88288 sp = s0 - 192, ra and s0 .. s11 loaded back, sp = sp + 192, return. a0 .. a7 at the return are
                      not stated (void).
   No tail jump: the calls are jal with link (the stack malloc, the leaf, personality_from_name, bcmp, the memsets,
   diginet_session_wake, maybe_online, the set_shadow entries) and four jalr with link (notice); every j is inside the
   function, and the function ends with ret.
   The model and the code (onann_model): the test at 0x87c8c is on_announce_m's ann_code test of :187 (the leaf's X: a0
   = ann_code (fr_cmd b) (length (fr_body b)), length (fr_body b) = fr_body_len b at fr_code b = 0); the store at
   s + 18184 is set_S_stats_rx_ignored with u64 of the 64-bit sum; personality_from_name's X is the personality
   pointer the model computes from a.name (onann_pv timg_A b: the walk relates codec_cells.v from_name_res, the
   result of that statement, to TNeed.v diginet_personality_from_name at timg_A's personalities), and the store at
   s + 128 is set_S_personality when it is not 0 (onann_w1); the loop is find_mac_m (ann_unknown (fr_body b)) 15
   (S_cfg_host_mac (onann_w1 ..)) (abcmp_realizes: a result 0 exactly when the 6 bytes agree; the 6 bytes at s are
   S_cfg_host_mac through tw_read; unknown_len is 15 and unknown = buf + 30 from the leaf's X), and off = -1 for cmd
   0xe0; the call at 0x87e48 is call_notify at onann_w1 timg_A Bw b with onann_dntc; the stores at s + 136 and s + 140
   are set_S_foreign and set_S_e1_named_us; each inlined session_lost is session_lost_m (session_lost_cg.v
   slost_model) on its path, where S_state <> S_IDLE, so its set_state stores and calls notice with slost_ntc; the
   tests at 0x87e94, 0x87f8c / 0x87fa8 and 0x880cc are the model's state tests at the world they read; the calls at
   0x87fb4, 0x87ff8 and 0x880b0 are diginet_session_wake_m, maybe_online_m and call_notify with onann_fntc. The code
   has no trap of its own; the model's None cases are the callees' (call_notify with S_notify <> ti_notice timg_A,
   notice_m, session_lost_m's, diginet_session_wake_m's, maybe_online_m's), all ruled out by the model premise.
   Error paths (30 calls; no abort) and the facts that rule them out:
     TS___asan_report_load1 0x594c8 (errpath_load1) at 0x88298, 0x882b8 (f + 30);
     TS___asan_report_load4 0x59608 (errpath_load4) at 0x882a8, 0x882e0, 0x88350, 0x88388, 0x883a0 (s + 112),
       0x88360 (s + 16);
     TS___asan_report_store4 0x59928 (errpath_store4) at 0x882c8, 0x882f0, 0x88370 (s + 136), 0x88300 (s + 140),
       0x88310, 0x883b0 (s + 212), 0x88320, 0x883c0 (s + 168), 0x88338, 0x883d8 (s + 112);
     TS___asan_report_load8 0x596a8 (errpath_load8) at 0x883dc (s + 18184), 0x883e8, 0x883fc, 0x88410, 0x88420
       (s + 96), 0x883f0, 0x88404, 0x88418, 0x88428 (s + 104);
     TS___asan_report_store8 0x599c8 (errpath_store8) at 0x883f4 (s + 128), 0x883e0 (n + 24), 0x88408 (fn + 24).
     The g_s ones guard naturally aligned accesses inside g_s's payload [0x5df9c0, 0x5e4118) (2283 whole granules),
     whose shadow bytes are 0 (trans_onann_cells, read at each AR state by DgnTransportCg.v decode_zshadow_rd), so
     k = 0. The two at f + 30: trans_dframe_at's decode_rd_ok gives range_addressable of the 64 bytes at fp at entry,
     still true at each shadow load (0x87cf4, 0x87e50): f lies in a frame of frames Sc, whose shadow bytes the stack
     malloc's acall_kept, the leaf, personality_from_name's and notice's posts keep, and the code's own stores reach
     only its own frames and their shadow bytes. The two in the frame: n + 24 and fn + 24 lie in granules whose shadow
     bytes (45 and 59) are 0 since 0x87d7c and 0x88018.
     Each memset's own check (aintrin_realizes' pre, from the G journal through TransportGCg.v gx_intrin_at): the
     destination ([n + 44, n + 72), [n2 + 16, n2 + 72), [fn + 32, fn + 72), [n3 + 16, n3 + 72)) lies in the frame this
     function took; its shadow bytes (47..50, 20..26, 60..64, 6..12) are 0 since 0x87d7c, 0x87ecc, 0x88018 and 0x88104
     and their hull is visible (astack_malloc_realizes' zero_shadow); each destination byte is a byte of the journal's
     own frame list after the stack malloc (YCbq.v awr_byte's in_frames: transport_twr_ok_g), not owned, not in the
     ESTACK bytes below sp.
   Writes: g_s's fields (bytes of G); its own machine frame (the 8 zero bytes at sp at 0x87a78, the saves at 0x87a7c -
   0x87aac, the words at s1 + 0 .. s1 + 87); its own side-stack frame (the header, a through the leaf, the four
   notices), that frame's shadow bytes and its flag byte; notice's stores (notice_wr, bytes of GOT);
   diginet_session_wake's (wake_wr, bytes of G) and maybe_online's (maybeon_wr, bytes of G). No byte of a caller's
   frame or block is written (f and the bytes at buf are read only), so onann_wr is the written range. The G kit for
   the own frame is session_lost_cg.v's (TransportGCg.v dk_kept_own_g with dkg_nf and dkg_nf_sep, dk_kept_trans_nf_g,
   dkg_frame_al64, gx_intrin_at, dk_kept_frame_byte_g; CanKit.v can_stack_malloc_at and can_flag_store_pi read inside
   the G journal through gx_lift).
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_4 as astack_malloc_realizes ... ONANN_CID (with pc_stack_malloc (as_code B) ONANN_CID =
       transport_sigma TS___asan_stack_malloc_4): count_cid 4 (frames Sc) < fs_frames 4 from the count premise.
     diginet_announce_parse as its leaf statement (diginet_announce_parse_cg.v
       transport_diginet_announce_parse_cg, read at this unit's model by DgnTransportCg.v transport_leaf_wr_at, since
       it writes a range of its caller; call at 0x87c88, through TransportGCg.v gx_call_leaf and the leaf bridge): a0 =
       f, 0 < f < 2 ^ 64; a1 = ap = a, 0 < ap < 2 ^ 64; cmd = fr_cmd b < 2 ^ 8 and body = buf + 30 (0 < body < 2 ^ 64);
       the bytes [b8 cmd] at f + 30 and le8 body ++ le8 (length bb) at f + 32, bb = fr_body b: the cells of
       frame_f_bytes buf b fj at 30, 32 and 40 (C1 (b8 (fr_cmd b)), C8 (buf + 30), C8 (fr_body_len b)), with
       length (fr_body b) = fr_body_len b (fr_code b = 0: 16 <= fr_numbytes b <= length b - 14); the bytes bb at body:
       b's bytes from 30 on (garr8 of b at buf); off_stk of [f + 30, f + 48) and of [body + 15, body + 33) (decode_off_win
       of f and of buf at ONANN_STK); when ann_ok: the 40 bytes aj at ap (the frame's bytes there, present by
       astack_malloc_realizes), apart from [f + 30, f + 48) and from [body + 15, body + 33) (ap lies in the fresh frame,
       f in diginet_session_rx's frame and body in buf's range: a fresh frame is apart from both placements), outside
       the leaf's frame; asan_cells (transport_cells rows 1-2); addressable f + 30 and [f + 32, f + 48) (decode_rd_ok of
       f, kept as above), [body + 15, body + 33) (trans_src_ok of buf's range, DgnTransportCg.v trans_src_ok_rd: ann_ok
       gives fr_body_len b >= 33, so body + 33 <= buf + length b), ap's 40 bytes (shadow bytes 32..36 = 0 since
       0x87c7c); the footprint premises (each byte and shadow byte named is visible); WR = [(ap, ap + 40)] not aowned
       and not in the image (a byte of a live frame: transport_leaf_wr_at). Its X: a0 = ann_code cmd (length bb) and,
       when ann_ok, the 40 bytes at ap are PAnn.ann_cells body bb aj (version = copy_strz of the body bytes from 15,
       name = copy_strz of the body bytes from 24, unknown = body at ap + 24, unknown_len = 15 at ap + 32).
     diginet_personality_from_name as diginet_personality_from_name_cg.v transport_diginet_personality_from_name_cg at
       transport_sigma TS_diginet_personality_from_name (call at 0x87cc0; a donor-form callee lifted with
       TransportGCg.v gx_call_cg; it keeps G, so the world relation after it is the one it was handed): the donor
       journal from the G journal; ra = 0x87cc4; gp, tp kept; a0 = x = a + 10, x <> 0; tb = TSS.ann_field (skipn 24
       (fr_body b)), the name's bytes and its 0, which the leaf stored at a + 10 (ann_cells' name field, copy_strz),
       In (b8 0) tb; trans_src_ok of [x, x + length tb) by decode_in_fake ([a + 10, a + 20) inside the 1024 bytes of a
       frame of its frames) with decode_rd_ok (the bytes stored by the leaf, shadow bytes 32..36 = 0, their hull
       visible); decode_off_win (the frame lies below alloc_ceiling, the callee's window above it); trans_rom_view_rd
       at the call memory (no store of on_announce reaches a read-only byte, and the stack malloc's acall_kept and the
       leaf's post keep every TRANS_RO_RD byte: trans_ro_rd_scoped); st_nev S + k + PFROM_EV <= EV_MAX. Its X: a0 =
       trans_pfrom_res tb.
     the bcmp wrapper as abcmp_realizes (YG0d.v) at transport_sigma TS___interceptor_trampoline_bcmp (calls at 0x87d4c,
       i = 0 .. 9; through gx_call_leaf): x = buf + 30 + i, y = s, n = 6; [buf + 30 + i, + 6) lies in [buf + 30,
       buf + 45), inside buf's range (fr_body_len b >= 33), so trans_src_ok_rd gives its visibility, amem_range,
       range_addressable and shadow_hull_vis, and decode_off_win at ONANN_STK puts it outside the wrapper's window
       [sp' - 2 * ESTACK, sp') (sp' >= sp - 208); [s, s + 6) is g_s.cfg.host_mac, bytes of G (visible by tw_at's view,
       outside every stack), shadow 0 (trans_onann_cells), and its aligned group of 8 shadow bytes, the shadow of
       [g_s, g_s + 64) (g_s is 64-aligned), is inside g_s's zero shadow. Its X: a0 = 0 exactly when the 6 bytes agree;
       every byte outside its window is kept.
     __asan_memset as aintrin_realizes ... OSet (transport_sigma TS___asan_memset), calls at 0x87e08, 0x87efc, 0x88080,
       0x88134 (above).
     notice as notice_cg.v transport_notice_cg at TI.ti_notice timg_A (= 0x83578, notice_cg.v notice_at; calls at
       0x87e48, 0x87f50, 0x880b0 and 0x88184; a G-form callee composed in the same G journal, no gx_call_cg). At each:
       the journal at the call state (the own frame live); ra = the address after the jalr (ret_ok, 4096 <= ra); gp, tp
       kept; a1 = p (n, n2, fn, n3); sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - NOTICE_STK:
       sp' >= sp - 208 and ONANN_STK >= 208 + NOTICE_STK; sp' <= sp0;
       trans_ntc_at p: 0 < p and p mod 8 = 0 (p = frame + 32, + 144, + 336 or + 448, dkg_frame_al64); trans_src_ok by
       decode_in_fake at the call state ([p, p + 72) inside the 1024 bytes of a frame of its frames) with decode_rd_ok
       (the bytes present by astack_malloc_realizes, p's 9 shadow bytes 0, their hull visible); decode_off_win (the
       frame lies below alloc_ceiling, notice's window above it); NB = the 72 bytes stored at p, whose fields are the
       notice's: for n (0x87da8 - 0x87e08) onann_dntc timg_A (onann_w1 timg_A Bw b) b (state S_state of that world,
       old_state 0, reason 0, counter 0, retry 0, mac_offset off, personality p, the announce Some (onann_ann b) with
       the pointer a, 8-aligned, the version bytes TSS.ann_field (skipn 15 (fr_body b)) at a and the name bytes at
       a + 10 as the leaf stored them, trans_src_ok of [a, a + 20) by decode_in_fake, decode_off_win of it); for fn
       (0x8803c - 0x88080) onann_fntc at notice's world (state, 0, 0, counter 0, retry 0, mac_offset 0, personality 0,
       the same announce); for n2 and n3 (0x87efc - 0x87f14, 0x88134 - 0x88148) session_lost_cg.v slost_ntc at that
       world with why = DIGINET_R_DESK_OFFLINE or DIGINET_R_FOREIGN (state S_IDLE, old_state the state read, the
       announce None with the pointer 0); each body: pointer 0, length 0, garr8 of [], trans_src_ok of the empty range
       at 0 (DgnTransportCg.v trans_src_ok_null), decode_off_win of it (0 <= sp' - NOTICE_STK);
       trans_tframe_at TF at NOTICE_STK: on_announce's trans_tframe_at at ONANN_STK, carried: TF's bytes and their
       shadow are unchanged (onann_apart for the g_s stores; the own frame is a fresh frame, apart from TF's
       placement; the leaf, the bcmp wrapper and the memsets keep every byte outside their windows and destinations;
       the record facts of the holds statement for the stack malloc's acall_kept and personality_from_name's
       acall_kept; for the calls at 0x87f50, 0x880b0 and 0x88184, across the earlier notice's acall_kept_g by
       trans_src_ok_kept over its clauses, which reach TF because trans_tf_off_g puts it outside G and onann_apart
       outside that notice's notice_wr, a row of onann_wr), and notice's window lies inside on_announce's;
       trans_rom_view_rd at the call memory (as for personality_from_name, and across notice's acall_kept_g, whose
       image clause keeps every TRANS_RO_RD byte outside G, the owned statics and errno);
       tw_at at notice's world: G kept through the stack malloc (gx_kept_of_acall_kept: gx_ok, gx_noerrno), the
       leaf, personality_from_name (gx_call_cg) and bcmp, then the tw_writes before it;
       notice_m timg_A TF at that world with that notice = Some (B', tt): the model premise through onann_model (and
       slost_model for n2 and n3; call_notify's test is the indirect target's value);
       notice_apart: a byte of notice_wr is a byte of GOT (GOT.desk, GOT.foreign, or GOT.t[GOT.n] and GOT.n), a byte of
       G, so not a byte of p's frame and not a byte of [a, a + 20) (a frame byte is outside the image: AR_laws'
       al_client_img); the body range is empty; TF's range: onann_apart, since notice_wr at that world with that
       notice lies inside onann_wr Bw b (notice_wr names no world for N_DESK and N_FOREIGN; for N_STATE it reads
       GOT.n, which no store before the inlined session_lost changes: the desk and foreign notices store GOT.desk and
       GOT.foreign, so the slost_wr Bw rows cover it);
       the N_DATA premise: vacuous (the kinds above);
       st_nev S + k + NOTICE_EV <= EV_MAX: the event count after the earlier callees plus NOTICE_EV, inside ONANN_EV
       (it counts each of the at most three notice calls of a path; all the callees' events are 0), and the stack
       malloc records no event. Its X: tw_at at notice's world after it.
     diginet_session_wake as diginet_session_wake_cg.v transport_diginet_session_wake_cg at transport_sigma
       TS_diginet_session_wake (call at 0x87fb4; a G-form callee in the same G journal): the journal at the call
       state (the own frame live); ra = 0x87fb8; gp, tp kept; a0 = s = WAKE_S; a1 = now, 0 <= now < 2 ^ 64; sp'
       32-aligned, sp0 - STK <= sp' - WAKE_STK (ONANN_STK = 208 + WAKE_STK), sp' <= sp0; tw_at at its world B4 (the
       world after the desk notice and the store of :201, or session_lost's X: the inlined copy's stores and notice's
       X); g_fail_next B4 <= 1 (notice and on_announce's stores leave the byte as it was: g_fail_next Bw <= 1);
       diginet_session_wake_m timg_A TF B4 now = Some (B5, r') (the model premise through onann_model, on the path
       where S_state B4 = S_IDLE and S_cfg_auto_wake B4 <> 0); trans_tframe_at TF at WAKE_STK (carried as for notice,
       then across the desk notice's acall_kept_g and, when the inlined session_lost runs, its notice's (0x87f50), by
       trans_src_ok_kept over their clauses, which reach TF because trans_tf_off_g puts it outside G and onann_apart
       outside each notice_wr; wake's window lies inside on_announce's); trans_tf_off_g TF: this statement's premise;
       trans_rom_view_rd at the call memory (as for notice); wake_apart TF B4: onann_apart, since wake_wr B4 lies in
       the row `exists Bx, wake_wr Bx` of onann_wr (wake_wr reads its world only through S_state and GOT.n, and the
       inlined session_lost's notice may have advanced GOT.n); the run invariants (1) and (4) at B4: Bw's (above,
       with the index bound);
       count_cid 2 at the call state = count_cid 2 (frames Sc), and + 2 < fs_frames 2 is the count premise; st_nev:
       the event count after the earlier callees plus WAKE_EV, inside ONANN_EV. Its X: a0 = r' (not used), tw_at at
       B5, g_fail_next B5 <= 1.
     maybe_online as maybe_online_cg.v transport_maybe_online_cg at transport_sigma TS_maybe_online (call at 0x87ff8;
       a G-form callee in the same G journal): the journal at the call state (the own frame live); ra = 0x87ffc; gp,
       tp kept; a0 = s = MAYBEON_S; sp' 32-aligned, sp0 - STK <= sp' - MAYBEON_STK, sp' <= sp0; tw_at at
       set_S_e1_named_us (set_S_foreign B2 0) 1, B2 the desk notice's world after it (notice's X, then the tw_writes of
       :211 and :212); g_fail_next of it <= 1 (as for diginet_session_wake); maybe_online_m timg_A TF at it = Some (Bw',
       tt) (the model premise through onann_model, on the path where off >= 0); trans_tframe_at TF at MAYBEON_STK and
       trans_rom_view_rd (as for diginet_session_wake, across the desk notice only; maybe_online's statement does not
       take trans_tf_off_g); maybeon_apart TF at it: onann_apart, since maybeon_wr of that world is maybeon_wr
       (set_S_e1_named_us (set_S_foreign (onann_w1 timg_A Bw b) 0) 1) (maybeon_wr reads S_state, S_wake_acked,
       S_e1_named_us, S_last_rx_us, S_cfg_keepalive_ms and GOT.n, none of which the desk notice's store GOT.desk
       changes), a row of onann_wr; count_cid 2 at the call state = count_cid 2 (frames Sc) < fs_frames 2
       (the count premise); st_nev: inside ONANN_EV. Its X: tw_at at Bw' and g_fail_next Bw' <= 1.
     __asan_set_shadow_f5 as TransportRtCg.v aset_shadow_realizes at transport_sigma TS___asan_set_shadow_f5 with
       v = 0xf5 (call at 0x88230; through gx_call_leaf): ecall_pre at the call state (the G journal's AR, ret_ok of
       0x88234, the realigned sp, the ESTACK bytes below it present); In (4, pos) (frames S) (the own frame, live until
       the flag store that follows); a0 = q = shadow_addr frame, a1 = n = 128 = fs_frame_bytes 4 / 8, 0 < n, [q, q + n)
       the frame's shadow. Its X: those 128 bytes are 0xf5, every other byte kept, AR at the same state; the flag store
       after it then releases the frame (astack_free_law).
   notice's, diginet_session_wake's, maybe_online's and personality_from_name's own record facts are premises of
   their holds statements.
   Stack: 192 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the memsets, the leaf, the set_shadow entry), 2 * ESTACK (the bcmp wrapper),
   personality_from_name's PFROM_STK, notice's NOTICE_STK, diginet_session_wake's WAKE_STK or maybe_online's
   MAYBEON_STK: ONANN_STK = 208 + WAKE_STK (onann_stk_eq).

   The caller: diginet_session_rx at 0x8797c (return address 0x87980), for a frame whose cmd byte (f + 30, the 1-byte
   load at 0x87954) is 0xe0 or 0xe1 (0x87960 - 0x8796c): a0 = s4 (its own a0, &g_s), a1 = s6 = its class-1 side-stack
   frame + 32 (its struct diginet_frame f, filled by diginet_frame_parse at 0x876e0; the frame's shadow bytes 4..11,
   f's 64 bytes, set to 0 at 0x87698 - 0x876b4), a2 = s3 (its own a3, now). It supplies its G journal, tw_at,
   g_fail_next, the model premise (its branch of diginet_session_rx_m), trans_dframe_at of f and buf,
   trans_tframe_at, onann_apart and trans_tf_off_g of its TF (trans_tf_off_g is its own premise), trans_rom_view_rd,
   the run invariants (1) and (4) with (4)'s index bound, count_cid 4 (frames Sc) < fs_frames 4 and count_cid 2
   (frames Sc) + 2 < fs_frames 2 (its own frame is of class 1).
   The image has 1 inlined copy of find_mac (in on_announce), 4 of session_lost (in diginet_session_tick and
   on_announce) and 8 of set_state: on_announce's own copies are walked here. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TNeed TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LAP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_announce_parse_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* on_announce's frame (`sp = sp - 192` at TS_on_announce), the at most 0x10 bytes of `sp = sp & -32` (0x87ab4) below
   it, and the largest stack a callee uses below the realigned sp: ESTACK for __asan_stack_malloc_4, __asan_memset,
   __asan_set_shadow_f5 (YG0d.v ecall_pre) and the leaf diginet_announce_parse (LeafCgKit.v ecall_pre), 2 * ESTACK for
   the bcmp wrapper (abcmp_realizes), personality_from_name's PFROM_STK, notice's NOTICE_STK, diginet_session_wake's
   WAKE_STK and maybe_online's MAYBEON_STK. *)
Definition ONANN_FRAME : Z := 192.
Definition ONANN_ALIGN : Z := 0x10.
Definition ONANN_STK : Z :=
  ONANN_FRAME + ONANN_ALIGN +
  Z.max ESTACK (Z.max (2 * ESTACK) (Z.max PFROM_STK (Z.max NOTICE_STK (Z.max WAKE_STK MAYBEON_STK)))).
Lemma onann_stk_eq : ONANN_STK = ONANN_FRAME + ONANN_ALIGN + WAKE_STK.
Proof. reflexivity. Qed.
(* No allocator event: personality_from_name, notice, diginet_session_wake and maybe_online record none, the leaf takes
   none, and the class-4 stack malloc and its release record none (YG00.v stack_malloc, stack_free). A path calls
   notice at most three times (the desk notice, then the foreign notice and the second inlined session_lost's on the
   cmd 0xe1, off < 0 path), so the bound counts NOTICE_EV three times. *)
Definition ONANN_EV : Z := PFROM_EV + 3 * NOTICE_EV + WAKE_EV + MAYBEON_EV.
(* The side-stack class of its own frame (a0 = 576 at 0x87ae4, the call of __asan_stack_malloc_4 at 0x87ae8). The
   callees that take a side-stack frame take class 2 (diginet_session_wake, maybe_online), hence the second count
   premise at WAKE_CID. *)
Definition ONANN_CID : Z := 4.
Lemma onann_cid_callees : WAKE_CID = 2 /\ MAYBEON_CID = 2.
Proof. split; reflexivity. Qed.
(* Its first argument: g_s's base in image A. *)
Definition ONANN_S : Z := TA_g_s.
(* The addresses of the g_s fields the code reads or writes (s + 18184, s + 128, s + 112, s + 96, s + 104, s + 136,
   s + 212, s + 168, s + 16, s + 140) and of cfg.host_mac (s + 0), which the bcmp calls read. *)
Lemma onann_addrs :
  ONANN_S = 0x5df9c0 /\
  ONANN_S + (TW.A_S_stats_rx_ignored - TW.OFF_g_s) = 0x5e40c8 /\
  ONANN_S + (TW.A_S_personality - TW.OFF_g_s) = 0x5dfa40 /\
  ONANN_S + (TW.A_S_state - TW.OFF_g_s) = 0x5dfa30 /\
  ONANN_S + (TW.A_S_notify - TW.OFF_g_s) = 0x5dfa20 /\
  ONANN_S + (TW.A_S_notify_ctx - TW.OFF_g_s) = 0x5dfa28 /\
  ONANN_S + (TW.A_S_foreign - TW.OFF_g_s) = 0x5dfa48 /\
  ONANN_S + (TW.A_S_inflight - TW.OFF_g_s) = 0x5dfa94 /\
  ONANN_S + (TW.A_S_desk_counter_valid - TW.OFF_g_s) = 0x5dfa68 /\
  ONANN_S + (TW.A_S_cfg_auto_wake - TW.OFF_g_s) = 0x5df9d0 /\
  ONANN_S + (TW.A_S_e1_named_us - TW.OFF_g_s) = 0x5dfa4c /\
  ONANN_S + (TW.A_S_cfg_host_mac - TW.OFF_g_s) = 0x5df9c0.
Proof. repeat split; reflexivity. Qed.
(* The variables in its class-4 frame (the description string at 0x123a6): n3 at 32, n2 at 144, a at 256 (40 bytes),
   n at 336, fn at 448 (72 bytes each); 576 bytes in all, inside the 1024 bytes of a class-4 frame. *)
Definition ONANN_N3 : Z := 32.
Definition ONANN_N2 : Z := 144.
Definition ONANN_A : Z := 256.
Definition ONANN_N : Z := 336.
Definition ONANN_FN : Z := 448.
Lemma onann_frame_fits : ONANN_FN + NTC_SIZE = 520 /\ 520 <= 576 /\ 576 <= fs_frame_bytes ONANN_CID.
Proof. repeat split; cbv; congruence. Qed.

(* The model's steps (TSess.v on_announce_m): the ann_code test of :187, the announce notice() reads (:190), a.name
   (:191) and the personality pointer the model computes from it, the world after :192-193, find_mac's result (:194)
   at a world, the desk notice of :196-197 and the foreign notice of :217 at a world. *)
Definition onann_ign (b : list byte) : bool :=
  negb (DSpec.ann_code (DSpec.fr_cmd b) (DSpec.fr_body_len b) =? DLib.DIGINET_OK).
Definition onann_ann (b : list byte) : TI.tann :=
  TI.TAnn (TSS.ann_field (skipn 15 (DSpec.fr_body b))) (TSS.ann_field (skipn 24 (DSpec.fr_body b))).
Definition onann_name (b : list byte) : list byte :=
  firstn (DSpec.copy_len 10 9 (skipn 24 (DSpec.fr_body b))) (skipn 24 (DSpec.fr_body b)).
Definition onann_pv (I : TI.timg) (b : list byte) : Z :=
  match TN.diginet_personality_from_name (onann_name b) with
  | Some i => TI.ti_personalities I + 24 * i
  | None => 0
  end.
Definition onann_w1 (I : TI.timg) (Bw b : list byte) : list byte :=
  match TN.diginet_personality_from_name (onann_name b) with
  | Some _ => TW.set_S_personality Bw (onann_pv I b)
  | None => Bw
  end.
Definition onann_off (Bx b : list byte) : Z :=
  if DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION
  then TSS.find_mac_m (DSpec.ann_unknown (DSpec.fr_body b)) 15 (TW.S_cfg_host_mac Bx) else -1.
Definition onann_dntc (I : TI.timg) (Bx b : list byte) : TI.ntc :=
  TI.Ntc TS0.DIGINET_N_DESK (TW.S_state Bx) 0 0 0 0 (onann_off Bx b) (onann_pv I b) (Some (onann_ann b)) [] 0.
Definition onann_fntc (Bx b : list byte) : TI.ntc :=
  TI.Ntc TS0.DIGINET_N_FOREIGN (TW.S_state Bx) 0 0 0 0 0 0 (Some (onann_ann b)) [] 0.
Lemma onann_model : forall (I : TI.timg) (F : option TI.tframe) (Bw b : list byte) (now : Z),
  TSS.on_announce_m I F Bw b now =
  if onann_ign b then Some (TW.set_S_stats_rx_ignored Bw (TS0.u64 (TW.S_stats_rx_ignored Bw + 1)), tt)
  else
    match TSS.call_notify I F (onann_w1 I Bw b) (onann_dntc I (onann_w1 I Bw b) b) with
    | None => None
    | Some (B2, _) =>
        if DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE then
          match (if TW.S_state (TW.set_S_foreign B2 0) =? TS0.DIGINET_S_ONLINE
                 then TSS.session_lost_m I F (TW.set_S_foreign B2 0) TS0.DIGINET_R_DESK_OFFLINE
                 else Some (TW.set_S_foreign B2 0, tt)) with
          | None => None
          | Some (B4, _) =>
              if (TW.S_state B4 =? TS0.DIGINET_S_IDLE) && negb (TW.S_cfg_auto_wake B4 =? 0) then
                match TSS.diginet_session_wake_m I F B4 now with
                | None => None
                | Some (B5, _) => Some (B5, tt)
                end
              else Some (B4, tt)
          end
        else if 0 <=? onann_off (onann_w1 I Bw b) b then
          TSS.maybe_online_m I F (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1)
        else
          match TSS.call_notify I F (TW.set_S_foreign B2 1) (onann_fntc (TW.set_S_foreign B2 1) b) with
          | None => None
          | Some (B3, _) =>
              if (TW.S_state B3 =? TS0.DIGINET_S_ONLINE) || (TW.S_state B3 =? TS0.DIGINET_S_WAKING)
              then TSS.session_lost_m I F B3 TS0.DIGINET_R_FOREIGN else Some (B3, tt)
          end
    end.
Proof. intros I F Bw b now. reflexivity. Qed.

(* The bytes some path of the call stores into G (each path stores a subset, on_announce_m): g_s's stats.rx_ignored
   and personality (8 bytes each), foreign and e1_named_us (4 bytes each); the desk and foreign notices' stores
   (notice_cg.v notice_wr: GOT.desk, GOT.foreign; for these kinds it names no world); the two inlined session_lost
   copies' stores (session_lost_cg.v slost_wr at Bw: inflight, desk_counter_valid, and, the state not being S_IDLE
   on their paths, state and the N_STATE notice's GOT.t[GOT.n] and GOT.n, GOT.n being Bw's since the desk and foreign
   notices do not store it); diginet_session_wake's (diginet_session_wake_cg.v wake_wr at the world it is called
   with, which may follow the inlined session_lost's notice: the row names no world, wake_wr reading it only through
   S_state and GOT.n); and maybe_online's (maybe_online_cg.v maybeon_wr at the world it is called with, whose reads
   maybeon_wr (set_S_e1_named_us (set_S_foreign (onann_w1 timg_A Bw b) 0) 1) gives: the desk notice's store of
   GOT.desk changes none of them). *)
Definition onann_wr (Bw b : list byte) (a : Z) : Prop :=
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_stats_rx_ignored 8 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_personality 8 a \/
  notice_wr (onann_w1 timg_A Bw b) (onann_dntc timg_A (onann_w1 timg_A Bw b) b) a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_foreign 4 a \/
  slost_wr Bw TS0.DIGINET_R_DESK_OFFLINE a \/
  (exists Bx : list byte, wake_wr Bx a) \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_e1_named_us 4 a \/
  maybeon_wr (TW.set_S_e1_named_us (TW.set_S_foreign (onann_w1 timg_A Bw b) 0) 1) a \/
  notice_wr (onann_w1 timg_A Bw b) (onann_fntc (onann_w1 timg_A Bw b) b) a \/
  slost_wr Bw TS0.DIGINET_R_FOREIGN a.

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. notice, diginet_session_wake and maybe_online read TF after the g_s stores and the earlier callees' stores
   (notice_cg.v notice_apart, diginet_session_wake_cg.v wake_apart, maybe_online_cg.v maybeon_apart). *)
Definition onann_apart (Fr : option TI.tframe) (Bw b : list byte) : Prop :=
  forall x, onann_wr Bw b x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented checks of the accesses at s + 16 .. s + 18191 read it, and the bcmp range [s, s + 6) and its aligned
   group of 8 shadow bytes ([g_s, g_s + 64): g_s is 64-aligned) lie in it. *)
Definition trans_onann_cells (B : asyms) : Prop := decode_zshadow_at B ONANN_S (ONANN_S + TW.SZ_g_s).

Section onann. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range onann_wr Bw b,
   no meter charge (the side-stack frame changes st_fs only), and X: the world relation at the model's world Bw' and
   g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this function takes is
   released. *)
Definition transport_onann_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' b : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    ONANN_STK ONANN_EV 0 (onann_wr Bw b)
    (fun regs2 W2 mem2 => tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_on_announce_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 ONANN_S -> YK11.getr regs 11 = w64 fp -> YK11.getr regs 12 = w64 now ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - ONANN_STK -> spZ regs <= sp0 ->
    0 <= now < 2 ^ 64 ->
    trans_dframe_at B lyc Sc W memc regs ONANN_STK fp buf b fj ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.on_announce_m timg_A TF Bw b now = Some (Bw', tt) ->
    trans_tframe_at B lyc Sc W memc regs ONANN_STK TF ->
    trans_tf_off_g TF ->
    trans_rom_view_rd W memc ->
    onann_apart TF Bw b ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    TW.g_ncmd Bw <= TC.CMDS_MAX ->
    count_cid ONANN_CID (frames Sc) < fs_frames ONANN_CID ->
    count_cid WAKE_CID (frames Sc) + 2 < fs_frames WAKE_CID ->
    st_nev S + k + ONANN_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_onann_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

(* The statement the walk will prove: the class-4 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the record facts that no byte of G and
   no TRANS_RO_RD byte is an owned static or errno (they carry the trans_src_ok of TF and of the bytes at buf, G and
   the TRANS_RO_RD bytes across the stack malloc's acall_kept and personality_from_name's acall_kept, and TF's
   trans_src_ok, with trans_tf_off_g, and the TRANS_RO_RD bytes across notice's acall_kept_g; DgnTransportCg.v
   G_HARNESS_gx_ok / G_HARNESS_gx_noerrno give gx_ok and gx_noerrno from the first two), the allocator, meter and
   side-stack laws, and the contracts of __asan_stack_malloc_4, diginet_announce_parse, diginet_personality_from_name,
   the bcmp wrapper, __asan_memset, notice (at the value the session's notify pointer holds), diginet_session_wake,
   maybe_online and __asan_set_shadow_f5 give the contract at TS_on_announce. *)
Definition transport_on_announce_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) ONANN_CID = transport_sigma TS___asan_stack_malloc_4 ->
  transport_cells B -> trans_onann_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B ONANN_CID) ->
  (forall fx' : YK11.FPState, @transport_leaf_wr_at rc B (@LAP.transport_diginet_announce_parse_cg) fx') ->
  (forall fx' : YK11.FPState,
     @transport_diginet_personality_from_name_cg fx' rc B MT (transport_sigma TS_diginet_personality_from_name)) ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transport_sigma TS___interceptor_trampoline_bcmp)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_session_wake_cg fx' rc B MT (transport_sigma TS_diginet_session_wake)) ->
  (forall fx' : YK11.FPState, @transport_maybe_online_cg fx' rc B MT (transport_sigma TS_maybe_online)) ->
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transport_sigma TS___asan_set_shadow_f5) 0xf5) ->
  transport_on_announce_cg (transport_sigma TS_on_announce).
End onann.
