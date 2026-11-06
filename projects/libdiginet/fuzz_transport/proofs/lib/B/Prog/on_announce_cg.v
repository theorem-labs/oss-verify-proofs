(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module names changed; 358 of its 430 lines of code are new or changed and 371 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickCut.v, with its module paths and module names changed; 203 of its 254 lines of code are new or changed and 379 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_tick_cg.v, with its module names changed; 137 of its 204 lines of code are new or changed and 187 lines of the source are left out. *)
(* on_announce_cg: image B's ASan walk contract of on_announce (transport/src/diginet_session.c:184-221, with find_mac
   (:168-174) and two copies of session_lost (:160-165) inlined, and set_state (:79-86) CALLED; model
   lib/TModel/TSess.v on_announce_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x87cc8 = transportb_sigma
   TB_on_announce, size 2244, as STATEMENTS only (no proof). It stores into g_s, a harness global, takes a class-3
   side-stack frame for its local struct diginet_announce a and two struct diginet_notice, calls
   diginet_announce_parse and diginet_personality_from_name (donor-form callees), the bcmp wrapper, __asan_memset,
   notice through the session's notify pointer, set_state, diginet_session_wake and maybe_online (G-form callees)
   while that frame is live, so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v
   ajournal_gx (image-free) over G = lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post
   is lib/A/Prog/TransportGCg.v transport_cg_post (image-free; acall_kept_g over G_HARNESS_B). Form: image A's
   lib/A/Prog/on_announce_cg.v at image B's names; the G walk with a side-stack frame of its own is image B's
   on_ack_cg.v and on_data_cg.v; its frame argument is image B's on_ack_cg.v trans_dframe_at.

   The contract. a0 = s = &g_s = 0x5df640 (TWorldB.v TB_g_s); a1 = fp, the struct diginet_frame f that
   diginet_session_rx's diginet_frame_parse filled from the frame bytes b at buf (on_ack_cg.v trans_dframe_at, the
   ASan form of lib/U/Prog/T/TSessC.v dframe_at); a2 = now (a uint64_t). TF is the current heap frame
   (check_state_data_cg.v trans_tframe_at at this call's window); the read-only bytes the callees read are the
   image's (trans_rom_view_rd). The memory relates to the world Bw by image B's world relation (TWorldG.v tw_at at
   TWorldB.v TMAP_B, read through aview), g_fail_next Bw <= 1, and on_announce_m timg_B TF Bw b now = Some (Bw', tt).
   No byte the call stores is a byte of TF (onann_apart), and no byte of TF is a byte of G (check_state_data_cg.v
   trans_tf_off_g). Class 3 of the side stack has a free frame (its own), class 1 one (diginet_session_wake's) and
   class 2 two (send_control's and diginet_body_check's inside it, under diginet_session_wake, while its own frame is
   live; set_state's and maybe_online's set_state's need one). The function returns to ra with the callee-saved
   registers kept, no allocator event and no meter charge (its side-stack frame changes the state's st_fs only:
   ameter_fs_laws), its side-stack frame released (the caller's frames exactly), the caller's blocks exactly, the
   bytes acall_kept_g G_HARNESS_B keeps (the bytes at or above alloc_ceiling outside the call's stack window
   [sp - ONANN_STK, sp), the image bytes outside G, the owned statics and errno, the caller's block and frame bytes
   outside onann_wr Bw b), the world relation at Bw', and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/U/Prog/T/on_announce_c.v): a0 = W_BASE_UBSAN + OFF_g_s -> a0 =
   TB_g_s; a1 = fp kept; a2 = now, 0 <= now < 2 ^ 64 kept; dframe_at m sp FRAME fp buf b fj -> trans_dframe_at at
   ONANN_STK (on_ack_cg.v gives the translation of each part); wmem -> tw_at; g_fail_next B <= 1 kept as a premise
   (the code neither reads nor writes g_fail_next; set_state's, diginet_session_wake's and maybe_online's statements
   ask it) and the post's g_fail_next B' <= 1 kept in X (from the premise on the paths that call none of them, else
   from the X of the last of them; notice and the stores after them do not touch the byte); on_announce_m verbatim at
   timg_B; timg_ubsan -> timg_B; tframe_at -> trans_tframe_at at ONANN_STK, and its off_world clause -> two facts,
   since check_state_data_cg.v trans_tframe_at drops that clause: onann_apart, no byte the call stores is a byte of
   TF (maybe_online_cg.v maybeon_apart's form), and trans_tf_off_g (check_state_data_cg.v), no byte of TF is a byte
   of G. on_announce needs trans_tf_off_g for its own walk: it carries TF across notice (calls at 0x88094 and
   0x88258), which writes G (GOT.desk or GOT.foreign), and across set_state (call at 0x88128), which writes G (g_s's
   state, and GOT.t[GOT.n] and GOT.n through its notice), to a later call that takes TF (notice at 0x88258,
   set_state at 0x88128 or 0x882b8, diginet_session_wake at 0x88160, maybe_online at 0x881a4): the acall_kept_g of
   a G-form callee keeps the image bytes outside G only, and its X pins G only to the model world, so it carries no
   byte of a TF inside G. diginet_session_wake's statement asks it too (send_control, then set_state, inside wake);
   relro_img -> trans_rom_view_rd; stk, lo + FRAME <= sp, sp mod 16 and w_off_stack -> the journal's window
   premises; mem_inv is dropped. The post's munch, wmono, stk and mem_inv -> transport_cg_post
   (the journal at the return, acall_kept_g over onann_wr Bw b); wmem -> X's tw_at.
   Premises the plain contract does not have:
   - count_cid 3 (frames Sc) < fs_frames 3: its own class-3 frame. With it __asan_stack_malloc_3 returns a frame
     (astack_malloc_realizes), so the real-stack arm is not taken.
   - count_cid 1 (frames Sc) < fs_frames 1 and count_cid 2 (frames Sc) + 1 < fs_frames 2: diginet_session_wake's
     statement asks count_cid 1 (frames Sc') < fs_frames 1 and count_cid 2 (frames Sc') + 1 < fs_frames 2 at its
     call state, whose frames Sc' are the own class-3 frame :: frames Sc (the same class-1 and class-2 counts:
     onann_cid_callees); set_state's and maybe_online's count_cid 2 < fs_frames 2 follows. diginet_announce_parse,
     personality_from_name, notice, the bcmp wrapper and the intrinsics take no side-stack frame.
   - onann_apart and trans_tf_off_g (above).
   - the run invariants (1) and (4) of diginet_session_wake, and (4)'s index bound g_ncmd Bw <= CMDS_MAX (below).
   - in the holds statement: trans_onann_cells (g_s's zero shadow), the side-stack laws, and trans_g_unowned,
     trans_g_no_errno, trans_ro_rd_unowned and trans_rom_no_errno: they carry the trans_src_ok of TF and of the bytes
     at buf across the stack malloc (DgnTransportBCg.v trans_src_ok_inner with their bytes kept by its acall_kept
     and trans_rd_ok_sh; the fresh frame is apart from their placement: trans_src_ok_disj_own) and
     diginet_announce_parse's and personality_from_name's acall_kept (through gx_call_cg; trans_src_ok_acall), and
     TF's across notice's and set_state's acall_kept_g (trans_src_ok_kept over its clauses, TF lying outside G by
     trans_tf_off_g; trans_src_ok_acall_g asks every byte of G to be kept, which neither gives; the bytes at buf are
     read only by diginet_announce_parse and the bcmp wrapper, before the first notice), the TRANS_RO_RD bytes
     (trans_rom_view_rd for personality_from_name, notice, set_state, diginet_session_wake and maybe_online), and G
     (TransportGCg.v gx_kept_of_acall_kept and gx_call_cg with gx_ok and gx_noerrno, which DgnTransportBCg.v
     G_HARNESS_gx_ok and G_HARNESS_gx_noerrno give from the first two), as image B's on_data_cg.v takes them. The
     bytes of f (f + 30's shadow byte is loaded at 0x8809c and f + 30 at 0x880a8, after the first notice) and their
     shadow lie in a frame of frames Sc, outside every callee's written range and window: the frame clause of
     acall_kept and acall_kept_g keeps them, and the bcmp wrapper and the intrinsics keep every byte outside their
     windows and destinations.
   Run invariants carried (on its own Bw): (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME and (4)
   every PENDING command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX, both diginet_session_wake_cg.v's
   premises (for io_send, through send_control). The world on_announce hands diginet_session_wake differs from Bw only
   in g_s's personality, foreign, inflight, desk_counter_valid and state and in notice's stores (GOT.desk for the desk
   notice, GOT.t[GOT.n] and GOT.n for set_state's notice, set_state being called at 0x88128 before
   diginet_session_wake at 0x88160): no byte of M, of g_cmd[0 .. CMDS_MAX) or of g_ncmd, so with the index bound
   TW.g_ncmd Bw <= TC.CMDS_MAX, a premise beside (4), both carry verbatim. Without it (4) would not carry: for
   s >= CMDS_MAX g_cmd[s]'s fields are other world bytes, and a notice's store into GOT.t can be one of them
   (GOT.t[5].old is A_Cmd_st 1131: TWorld.v's offsets, the same world for both images). diginet_session_wake does not
   take the bound (the world it hands send_control, wake_w1 Bw now, differs from its own only inside g_s, below g_cmd,
   and its set_state call at 0x86d2c comes after send_control: diginet_session_wake_cg.v); no function on_announce
   calls writes g_ncmd, and the caller has the bound from the plain run (lib/TSim/Agree.v d3_ncmd and d3_ops,
   OPS_MAX = CMDS_MAX). on_announce carries (2) to no callee, so it takes no bound on S_queued.
   notice's premise for a data notice (check_state_data's run invariant) holds vacuously at its two calls: their
   kinds are N_DESK (the store of 1 at n by 0x87ff4) and N_FOREIGN (the store of 6 at fn by 0x881e8); set_state,
   maybe_online, personality_from_name and diginet_announce_parse carry none; the others (check_latest_queue's,
   take's cfg bounds) are not reached from on_announce. on_announce's own instrumented accesses are at fixed offsets
   of g_s (s + 16 .. s + 19, s + 96 .. s + 115, s + 128 .. s + 143, s + 168 .. s + 171, s + 212 .. s + 215,
   s + 18184 .. s + 18191), at f + 30 and in its own frame; its bcmp ranges are [buf + 30 + i, + 6) (i <= 9, inside
   b: the model's ann_code 0 gives fr_body_len b >= 33) and [s, s + 6); its memsets fill 28 and 40 bytes of its own
   frame, so its code needs no bound that the model does not give.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 2244 code bytes and the 48 bytes of its frame
   description at 0x1d874 are equal in both files), 561 words; s = s4, f = s6 (to 0x880d8 on the cmd 0xe0 path; kept
   at s1 + 40 over find_mac), now = s7 (kept at s1 + 24 from 0x87f0c), a = s10 (to 0x88050; kept at s1 + 16 from
   0x87f10), p = a6 (kept at s1 + 32 over find_mac), the frame = s3, the stack malloc's result s9, the frame's first
   shadow byte s2 = (frame >> 3) + 0x7fff8000, the shadow base s8 (kept at s1 + 0 over find_mac):
     0x87cc8 - 0x87d04 sp = sp - 192; 0x87ccc stores 8 zero bytes at sp; ra at sp + 184, s0 .. s11 at sp + 176 ..
                      sp + 88, loaded back at 0x88400 - 0x88430; s0 = sp + 192 (the entry sp, kept to 0x883fc).
     0x87d08 - 0x87d14 sp = sp & -32 (at most 0x10 below entry - 192); s1 = the realigned sp; s7 = now, s6 = fp.
     0x87d18 - 0x87d30 a2 = the 8-byte load of the GOT word 0xa3d48 (it holds 0xac680), then the 4-byte load of the
                      flag word at 0xac680; a1 = the 8-byte load of the GOT word 0xa3cf0 (it holds 0xac678), s8 = the
                      8-byte load at 0xac678 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s4 = s.
     0x87d34 - 0x87d48 the flag word = 0 goes to 0x87d48 (s9 = 0); transport_cells row 6 gives 1. a0 = 352 and the
                      call of __asan_stack_malloc_3 (frame_alloc_3, 0x3db94 = transportb_sigma
                      TB___asan_stack_malloc_3) at 0x87d3c, return address 0x87d40: a class-3 side-stack frame
                      (fs_frame_bytes 3 = 512 bytes); s9 = the result.
     0x87d4c - 0x87d6c s3 = s9; s9 <> 0 goes to 0x87d70. The real-stack arm (s9 = 0): s3 = (sp - 352) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s3), then sp = s3. With
                      count_cid 3 (frames Sc) < fs_frames 3 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s3 = s9.
     0x87d70 - 0x87d74 the 8-byte store of frame at s1 + 80 (its own machine frame); s10 = a = frame + 32.
     0x87d78 - 0x87da4 the frame header: 0x41b58ab3 at frame, the description string 0x1d874 ("3 32 40 5 a:186 112 72
                      5 n:196 224 72 6 fn:217": three variables, a at frame + 32 (40 bytes), the desk notice n at
                      frame + 112 and the foreign notice fn at frame + 224, each notice 72 bytes) at frame + 8, the
                      function's address 0x87cc8 at frame + 16.
     0x87d84, 0x87dac - 0x87e60 s2 = (frame >> 3) + 0x7fff8000; the frame's 44 shadow bytes (352 bytes): 0..3 = 0xf1;
                      4..8 = 0 (a, usable); 9..13 = 0xf2; 14..22 = 0xf8 (n, out of scope); 23..27 = 0xf2; 28..36 =
                      0xf8 (fn); 37..43 = 0xf3.
     each instrumented check below: the shadow byte k at (x >> 3) + 0x7fff8000; k = 0 goes on; for a 1-byte access
                      (x & 7) < k (signed), for a 4-byte access ((x & 7) + 3) < k (signed) goes on; for an 8-byte
                      access any k <> 0 goes to the error path.
     0x87e64 - 0x87e6c a0 = fp, a1 = a; the call of diginet_announce_parse (0x8bdec = transportb_sigma
                      TB_diginet_announce_parse) at 0x87e6c, return address 0x87e70 (:187).
     0x87e70 - 0x87ea4 a0 = 0 goes to 0x87ea8. Else (:188-189): s & 7 <> 0 goes to the trap word; a0 = s + 18184
                      (g_s.stats.rx_ignored), the check of the 8-byte access, the 8-byte load, + 1, the 8-byte store
                      back; to 0x8830c.
     0x87ea8 - 0x87eb0 a0 = a + 10 (a.name); the call of diginet_personality_from_name (0x8c050 = transportb_sigma
                      TB_diginet_personality_from_name) at 0x87eac, return address 0x87eb0 (:191); a6 = p, the result.
     0x87eb4 - 0x87ed4 p = 0 goes to 0x87ed8; else s & 7 <> 0 goes to the trap word, the check of the 8-byte store at
                      s + 128 and the store of p there (g_s.personality, :192-193).
     0x87ed8 - 0x87efc fp & 7 <> 0 goes to the trap word (the UBSan alignment check of struct diginet_frame *f);
                      the check of the 1-byte load at f + 30 (its shadow byte's address a3, kept at s1 + 48, and
                      f + 30 kept at s1 + 56); a1 = cmd = the 1-byte load at f + 30.
     0x87f00 - 0x87f14 a0 = s & 7, a2 = 0xe1, a5 = off = -1; the stores of now at s1 + 24 and of a at s1 + 16; cmd <>
                      0xe1 (DIGINET_CMD_ANNOUNCE_SESSION) goes to 0x87f38 (a1 = (s & 7 = 0), then 0x87fc8) (:194).
     0x87f18 - 0x87fbc find_mac (:168-174): s & 7 <> 0 goes to the trap word; p kept at s1 + 32, fp at s1 + 40;
                      s11 = the 8-byte load at a + 32 (unknown_len, 15: diginet_announce_parse's X), s6 = 6;
                      s11 < 6 (unsigned) goes to 0x87f30 (fp loaded back, then 0x87fc0); s8 and s9 kept at s1 + 0 and
                      s1 + 8; s9 = i = 0; s8 = the 8-byte load at a + 24 (unknown = buf + 30, diginet_announce_parse's
                      X), s7 = (unknown <> 0), s5 = s10 = unknown; the loop at 0x87f5c: s10 < unknown (unsigned: the
                      UBSan pointer-overflow check of unknown + i) goes to the trap word, and so does (s7 xor
                      (s10 = 0)) = 0 (unknown + i is 0 exactly when unknown is not); a0 = s5 = unknown + i, a1 = s,
                      a2 = 6, the call of the bcmp wrapper (0x42d34 = transportb_sigma
                      TB___interceptor_trampoline_bcmp) at 0x87f78, return address 0x87f7c; a result 0 goes to
                      0x87fac (a5 = i); else s9 = s9 + 1 (32-bit), s10, s6 and s5 + 1, s11 >= s6 (unsigned) goes
                      round again, and after the ten turns i = 0 .. 9 a5 = -1. s9, s8, s6 = fp and s10 = a are
                      loaded back from s1 + 8, s1 + 0, s1 + 40 and s1 + 16; a6 = p from s1 + 32 (0x87fc0); a1 = 1
                      (0x87fc4). The loads at a + 24 and a + 32 have no instrumented check.
     0x87fc8 - 0x87ff4 s5 = n = frame + 112; shadow bytes 14..22 = 0 (n usable); the 4-byte store of 1 (N_DESK) at
                      n (kind, :196).
     0x87ff8 - 0x88010 a1 = 0 (s & 7 <> 0) goes to the trap word; a3 = s + 112, a4 = its shadow byte's address; the
                      check of the 4-byte load at s + 112; a1 = the 4-byte load at s + 112 (S_state).
     0x88014 - 0x88030 stores into n: a1's low 32 bits at n + 4 (state), 8 zero bytes at n + 8 (old_state, reason),
                      the 8 bytes of fp at n + 16 (n.frame, which notice does not read); the check of the 8-byte store
                      at n + 24 (frame + 136).
     0x88034 - 0x88058 a4 kept at s1 + 32 and a3 = s + 112 at s1 + 40; the 8-byte stores of a at n + 24 (n.announce)
                      and of p at n + 32 (n.personality); s7 = off and its 4-byte store at n + 40 (n.mac_offset, :197);
                      a0 = n + 44, a1 = 0 (the shadow byte loaded at 0x8802c), a2 = 28, s10 = s + 96; the call of
                      __asan_memset (checked_memset, 0x52888 = transportb_sigma TB___asan_memset) at 0x88058, return
                      address 0x8805c: n's bytes 44 .. 71 set to 0 (padding, body, body_len, counter, retry, padding).
     0x8805c - 0x88084 the check of the 8-byte load at s + 96 (its shadow byte's address kept at s1 + 8); s11 = s +
                      104, its shadow byte's address kept at s1 + 0; the check of the 8-byte load at s + 104.
     0x88088 - 0x88094 a2 = the 8-byte load at s + 96 (S_notify: tw_read, and the model's call_notify gives
                      TI.ti_notice timg_B = 0x8341c); a0 = the 8-byte load at s + 104 (notify_ctx, which notice does
                      not read); a1 = n; the indirect call (jalr a2) at 0x88094, return address 0x88098 (:198;
                      struct diginet_session + 96, notify -> notice: notice_cg.v's list of indirect call sites).
     0x88098 - 0x880b0 the check of the 1-byte load at f + 30 (its shadow byte's address from s1 + 48); a0 = cmd = the
                      1-byte load at f + 30 (address from s1 + 56); cmd <> 0xe0 (DIGINET_CMD_ANNOUNCE) goes to 0x88168
                      (:200).
     0x880b4 - 0x880c8 the check of the 4-byte store at s + 136; the store of 0 at s + 136 (g_s.foreign = 0, :201).
     0x880cc - 0x880e8 s10 = the shadow byte's address of s + 112 (from s1 + 32), s5 = now (from s1 + 24), s6 =
                      s + 112 (from s1 + 40); the check of the 4-byte load at s + 112; a0 = the 4-byte load at s + 112;
                      <> 2 (S_ONLINE) goes to 0x88138 (:202).
     0x880ec - 0x88128 the inlined session_lost (:203, :162-164): the checks of the 4-byte stores at s + 212 and
                      s + 168 and the stores of 0 there (inflight, desk_counter_valid); a0 = s, a1 = 0 (S_IDLE), a2 = 3
                      (DIGINET_R_DESK_OFFLINE); the call of set_state (0x872cc = transportb_sigma TB_set_state) at
                      0x88128, return address 0x8812c (:164).
     0x8812c - 0x88134 the check of the 4-byte load at s + 112; a0 = the 4-byte load at s + 112.
     0x88138 - 0x88154 a0 <> 0 (not S_IDLE) goes to 0x882e4; the check of the 4-byte load at s + 16 (cfg.auto_wake);
                      its value 0 goes to 0x882e4 (:204).
     0x88158 - 0x88164 a0 = s, a1 = now (s5); the call of diginet_session_wake (0x86a38 = transportb_sigma
                      TB_diginet_session_wake) at 0x88160, return address 0x88164 (:205; its result is not used); to
                      0x882e4.
     0x88168 - 0x88174 (cmd = 0xe1) a0 = s + 136, a1 = its shadow byte's address; off < 0 (s7) goes to 0x881ac (:209).
     0x88178 - 0x881a8 the check of the 4-byte store at s + 136 and the store of 0 (g_s.foreign = 0, :211); the check of
                      the 4-byte store at s + 140 and the store of 1 (g_s.e1_named_us = 1, :212); a0 = s; the call of
                      maybe_online (0x8ae8c = transportb_sigma TB_maybe_online) at 0x881a4, return address 0x881a8
                      (:213); to 0x882e4.
     0x881ac - 0x881e8 (off < 0) the check of the 4-byte store at s + 136; s5 = fn = frame + 224; the store of 1 at
                      s + 136 (g_s.foreign = 1, :216); shadow bytes 28..36 = 0 (fn usable); the 4-byte store of 6
                      (N_FOREIGN) at fn (kind, :217).
     0x881ec - 0x8821c the check of the 4-byte load at s + 112 (its shadow byte's address from s1 + 32, the address
                      from s1 + 40); a1 = the 4-byte load at s + 112; stores into fn: a1's low 32 bits at fn + 4,
                      8 zero bytes at fn + 8, the 8 bytes of fp at fn + 16; the check of the 8-byte store at fn + 24
                      (frame + 248).
     0x88220 - 0x88230 a (from s1 + 16) at fn + 24 (fn.announce); a0 = fn + 32, a1 = 0 (the shadow byte loaded at
                      0x88218), a2 = 40; the call of __asan_memset at 0x88230, return address 0x88234: fn's bytes
                      32 .. 71 = 0 (personality, mac_offset, padding, body, body_len, counter, retry, padding).
     0x88234 - 0x88258 the checks of the 8-byte loads at s + 96 and s + 104 (their shadow bytes' addresses from s1 + 8
                      and s1 + 0); a2 = notify (s10 = s + 96), a0 = notify_ctx (s11 = s + 104), a1 = fn; the indirect
                      call (jalr a2) at 0x88258, return address 0x8825c (:218).
     0x8825c - 0x88278 the check of the 4-byte load at s + 112; a0 = the 4-byte load at s + 112; (a0 - 1) (32-bit) > 1
                      (unsigned) goes to 0x882bc (neither S_WAKING nor S_ONLINE, :219).
     0x8827c - 0x882b8 the inlined session_lost (:220, :162-164): the checks of the 4-byte stores at s + 212 and
                      s + 168 and the stores of 0 there; a0 = s, a1 = 0, a2 = 5 (DIGINET_R_FOREIGN); the call of
                      set_state at 0x882b8, return address 0x882bc.
     0x882bc - 0x882e0 shadow bytes 28..36 = 0xf8 (fn out of scope).
     0x882e4 - 0x88308 shadow bytes 14..22 = 0xf8 (n out of scope).
     0x8830c - 0x88320 shadow bytes 4..8 = 0xf8 (a out of scope; every path).
     0x88324 - 0x8832c the header word 0x45e0360e stored at frame (every path).
     0x88330          s9 = 0 goes to 0x8834c (the real-stack arm; not taken).
     0x88334 - 0x88348 the release: a0 = s2 (the frame's first shadow byte), a1 = 64; the call of
                      __asan_set_shadow_f5 (meta_fill_f5, 0x553b4 = transportb_sigma TB___asan_set_shadow_f5) at
                      0x8833c, return address 0x88340: the frame's 64 shadow bytes (512 bytes) = 0xf5 (released);
                      a0 = the 8-byte load at s9 + 504 (the frame's last word, which holds the flag byte's address:
                      astack_malloc_realizes' rdword), then the store of one zero byte at a0 (YG0d.v
                      astack_free_law); to 0x883fc.
     0x8834c - 0x883f8 the real-stack arm's release: shadow bytes 0..43 = 0 (inline stores, no call). Not reached.
     0x883fc - 0x88438 sp = s0 - 192, ra and s0 .. s11 loaded back, sp = sp + 192, return. a0 .. a7 at the return are
                      not stated (void).
     0x8843c          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path.
     0x88440 - 0x88588 the slow paths of the checks and the 24 error calls.
   No tail jump: the calls are jal with link (the stack malloc, diginet_announce_parse, personality_from_name, bcmp,
   the memsets, set_state, diginet_session_wake, maybe_online, the set_shadow entry) and two jalr with link (notice);
   every j is inside the function, and the function ends with ret.
   The model and the code (onann_model): the test at 0x87e70 is on_announce_m's ann_code test of :187
   (diginet_announce_parse's X: a0 = ann_code (fr_cmd b) (length (fr_body b)), length (fr_body b) = fr_body_len b at
   fr_code b = 0); the store at s + 18184 is set_S_stats_rx_ignored with u64 of the 64-bit sum;
   personality_from_name's X is the personality pointer the model computes from a.name (onann_pv timg_B b: the walk
   relates diginet_personality_from_name_cg.v trans_pfrom_res, the result of that statement, to TNeed.v
   diginet_personality_from_name at timg_B's personalities, trans_pfrom_pers), and the store at s + 128 is
   set_S_personality when it is not 0 (onann_w1); the loop is find_mac_m (ann_unknown (fr_body b)) 15
   (S_cfg_host_mac (onann_w1 ..)) (abcmp_realizes: a result 0 exactly when the 6 bytes agree; the 6 bytes at s are
   S_cfg_host_mac through tw_read; unknown_len is 15 and unknown = buf + 30 from diginet_announce_parse's X), and
   off = -1 for cmd 0xe0; the call at 0x88094 is call_notify at onann_w1 timg_B Bw b with onann_dntc; the stores at
   s + 136 and s + 140 are set_S_foreign and set_S_e1_named_us; each inlined session_lost is session_lost_m on its
   path: its two stores are slost_w1 (diginet_session_tick_cg.v), and its set_state_m step at slost_w1 of that world
   with S_IDLE and why is the call of set_state (diginet_session_tick_cg.v slost_model_sstate; set_state's test of
   S_state against S_IDLE is its own); the tests at 0x880e8, 0x88138 / 0x88154 and 0x88278 are the model's state
   tests at the world they read; the calls at 0x88160, 0x881a4 and 0x88258 are diginet_session_wake_m,
   maybe_online_m and call_notify with onann_fntc. The model's None cases are the callees' (call_notify with S_notify
   <> ti_notice timg_B, notice_m, set_state_m's, diginet_session_wake_m's, maybe_online_m's), all ruled out by the
   model premise; the code's trap word and its real-stack arm are ruled out by facts outside the model (the constant
   s, trans_dframe_at, the side-stack premises).
   Trap path (the unimp word at 0x8843c, from 7 branches) and the facts that refute it: 0x87e78, 0x87ebc, 0x87f18 and
   0x87ff8 (s & 7 <> 0; at 0x87ff8 through a1 = (s & 7 = 0) or 1): s = 0x5df640, a multiple of 8; 0x87edc
   (fp & 7 <> 0): trans_dframe_at's fp mod 8 = 0; 0x87f5c and 0x87f68 (unknown + i wraps, or is 0): unknown =
   buf + 30 (diginet_announce_parse's X), 0 < buf and [buf, buf + length b) below 2 ^ 64 (trans_src_ok of buf's
   range: DgnTransportBCg.v trans_src_ok_place), and i <= 9 < length b - 30 (ann_code 0 gives fr_body_len b >= 33),
   so 0 < unknown <= unknown + i < 2 ^ 64.
   Error paths (24 calls; no abort) and the facts that rule them out:
     __asan_report_load1 (0x59504) at 0x88448, 0x88470 (f + 30);
     __asan_report_load4 (0x59644) at 0x8845c, 0x88494, 0x884e8, 0x88520, 0x88538 (s + 112), 0x884f8 (s + 16);
     __asan_report_store4 (0x59964) at 0x88480, 0x884a4, 0x88508 (s + 136), 0x884b4 (s + 140), 0x884c4, 0x88548
       (s + 212), 0x884d4, 0x88558 (s + 168);
     __asan_report_load8 (0x596e4) at 0x8855c (s + 18184), 0x88568, 0x88580 (s + 96), 0x88570, 0x88588 (s + 104);
     __asan_report_store8 (0x59a04) at 0x88574 (s + 128), 0x88560 (n + 24), 0x88578 (fn + 24).
     The g_s ones guard naturally aligned accesses inside g_s's payload [0x5df640, 0x5e3d98) (2283 whole granules),
     whose shadow bytes are 0 (trans_onann_cells, read at each AR state by DgnTransportBCg.v decode_zshadow_rd), so
     k = 0. The two at f + 30: trans_dframe_at's decode_rd_ok gives range_addressable of the 64 bytes at fp at entry,
     still true at each shadow load (0x87eec, 0x880a0): f lies in a frame of frames Sc, whose shadow bytes the stack
     malloc's acall_kept, diginet_announce_parse's and personality_from_name's acall_kept and notice's acall_kept_g
     keep, and the code's own stores reach only its own frames and their shadow bytes. The two in the frame: n + 24
     and fn + 24 lie in granules whose shadow bytes (17 and 31) are 0 since 0x87fec and 0x881e4.
     Each memset's own check (aintrin_realizes' pre, from the G journal through TransportGCg.v gx_intrin_at): the
     destination ([n + 44, n + 72), [fn + 32, fn + 72)) lies in the frame this function took; its shadow bytes (19..22,
     32..36) are 0 since 0x87fec and 0x881e4 and their hull is visible (astack_malloc_realizes' zero_shadow); each
     destination byte is a byte of the journal's own frame list after the stack malloc (YCbq.v awr_byte's in_frames:
     transport_twr_ok_g), not owned, not in the ESTACK bytes below sp.
   Writes: g_s's fields (bytes of G); its own machine frame (the 8 zero bytes at sp at 0x87ccc, the saves at 0x87cd0 -
   0x87d00, the words at s1 + 0 .. s1 + 63 and s1 + 80); its own side-stack frame (the header, a through
   diginet_announce_parse, the two notices), that frame's shadow bytes and its flag byte; notice's stores (notice_wr,
   bytes of GOT); set_state's (set_state_cg.v sstate_wr, bytes of G), diginet_session_wake's (wake_wr, bytes of G)
   and maybe_online's (maybeon_wr, bytes of G). No byte of a caller's frame or block is written (f and the bytes at
   buf are read only), so onann_wr is the written range. The G kit for the own frame is image B's set_state_cg.v's
   (TransportGCg.v dk_kept_own_g with dkg_nf and dkg_nf_sep, dk_kept_trans_nf_g, dkg_frame_al64, gx_intrin_at,
   dk_kept_frame_byte_g; image B's CanKit.v can_stack_malloc_at and can_flag_store_pi read inside the G journal
   through gx_lift).
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_3 as astack_malloc_realizes ... ONANN_CID (with pc_stack_malloc (as_code B) ONANN_CID =
       transportb_sigma TB___asan_stack_malloc_3): count_cid 3 (frames Sc) < fs_frames 3 from the count premise.
     diginet_announce_parse as diginet_announce_parse_cg.v transport_diginet_announce_parse_cg at transportb_sigma
       TB_diginet_announce_parse (call at 0x87e6c; a donor-form callee lifted with TransportGCg.v gx_call_cg; it
       writes only [a, a + 20) and [a + 24, a + 40) (trans_anp_wr), bytes of this function's own frame, so the world
       relation after it is the one it was handed): the donor journal from the G journal; ra = 0x87e70 (ret_ok,
       4096 <= ra); gp, tp kept; a0 = f, a1 = ap = a; f <> 0 and ap <> 0; f mod 8 = 0 (trans_dframe_at) and
       ap mod 8 = 0 (frame + 32, dkg_frame_al64); 0 < body = buf + 30 (0 < buf); cmd = fr_cmd b < 2 ^ 8 and the
       bytes [cmd] at f + 30 and trans_anp_f32_bytes body bb at f + 32, bb = fr_body b: the cells of
       frame_f_bytes buf b fj at 30, 32 and 40 (C1 (b8 (fr_cmd b)), C8 (buf + 30), C8 (fr_body_len b)), with
       length (fr_body b) = fr_body_len b (fr_code b = 0: 16 <= fr_numbytes b <= length b - 14); decode_rd_ok and
       decode_off_win of f (trans_dframe_at's, kept as below, the window moved to TRANS_ANP_STK by lia); when bb is
       not empty, trans_src_ok and decode_off_win of [body, body + length bb), a range inside [buf, buf + length b)
       (DgnTransportBCg.v trans_src_ok_sub), garr8 of bb at body (b's bytes from 30 on, garr8 of b at buf); length aj =
       40, aj the 40 bytes at ap (present by astack_malloc_realizes; on_announce does not fill them); decode_in_fake
       (32 + 40 <= 512, the own frame); decode_twr_ok (the frame is in this journal's own frame list, present and not
       owned: AR_frames_law); decode_rd_ok (the stores of 0x87dc4 and 0x87e54 - 0x87e60 mark a's 5 shadow bytes 0);
       decode_off_win of ap (the frame lies below alloc_ceiling, the callee's window above it); ap apart from
       [f, f + 64) and from bb (a fresh frame is apart from diginet_session_rx's frame and from buf's placement);
       st_nev S + k + TRANS_ANP_EV <= EV_MAX. Its X: a0 = ann_code cmd (length bb) and the 40 bytes at ap are
       trans_anp_bytes, which are, when ann_ok, PAnn.ann_cells body bb aj (version = copy_strz of the body bytes from
       15, name = copy_strz of the body bytes from 24, unknown = body at ap + 24, unknown_len = 15 at ap + 32).
     diginet_personality_from_name as diginet_personality_from_name_cg.v transport_diginet_personality_from_name_cg at
       transportb_sigma TB_diginet_personality_from_name (call at 0x87eac; a donor-form callee lifted with
       TransportGCg.v gx_call_cg; it keeps G, so the world relation after it is the one it was handed): the donor
       journal from the G journal; ra = 0x87eb0; gp, tp kept; a0 = x = a + 10, x <> 0; tb = TSS.ann_field (skipn 24
       (fr_body b)), the name's bytes and its 0, which diginet_announce_parse stored at a + 10 (ann_cells' name field,
       copy_strz), In (b8 0) tb; trans_src_ok of [x, x + length tb) by decode_in_fake ([a + 10, a + 20) inside the
       512 bytes of a frame of its frames) with decode_rd_ok (the bytes stored by diginet_announce_parse, shadow bytes
       4..8 = 0, their hull visible); decode_off_win (the frame lies below alloc_ceiling, the callee's window above
       it); trans_rom_view_rd at the call memory (no store of on_announce reaches a read-only byte, and the stack
       malloc's acall_kept and diginet_announce_parse's acall_kept keep every TRANS_RO_RD byte: trans_ro_rd_scoped);
       st_nev S + k + PFROM_EV <= EV_MAX. Its X: a0 = trans_pfrom_res tb.
     the bcmp wrapper as abcmp_realizes (YG0d.v) at transportb_sigma TB___interceptor_trampoline_bcmp (calls at
       0x87f78, i = 0 .. 9; through gx_call_leaf): x = buf + 30 + i, y = s, n = 6; [buf + 30 + i, + 6) lies in
       [buf + 30, buf + 45), inside buf's range (fr_body_len b >= 33), so trans_src_ok_rd gives its visibility,
       amem_range, range_addressable and shadow_hull_vis, and decode_off_win at ONANN_STK puts it outside the wrapper's
       window [sp' - 2 * ESTACK, sp') (sp' >= sp - 208); [s, s + 6) is g_s.cfg.host_mac, bytes of G (visible by
       tw_at's view, outside every stack), shadow 0 (trans_onann_cells), and its aligned group of 8 shadow bytes, the
       shadow of [g_s, g_s + 64) (g_s is 64-aligned), is inside g_s's zero shadow. Its X: a0 = 0 exactly when the 6
       bytes agree; every byte outside its window is kept.
     __asan_memset as aintrin_realizes ... OSet (transportb_sigma TB___asan_memset), calls at 0x88058 and 0x88230
       (above).
     notice as notice_cg.v transport_notice_cg at TI.ti_notice timg_B (= 0x8341c, notice_cg.v notice_at; calls at
       0x88094 and 0x88258; a G-form callee composed in the same G journal, no gx_call_cg). At each:
       the journal at the call state (the own frame live); ra = the address after the jalr (ret_ok, 4096 <= ra); gp,
       tp kept; a1 = p (n, fn); sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - NOTICE_STK:
       sp' >= sp - 208 and ONANN_STK >= 208 + NOTICE_STK; sp' <= sp0;
       trans_ntc_at p: 0 < p and p mod 8 = 0 (p = frame + 112 or + 224, dkg_frame_al64); trans_src_ok by
       decode_in_fake at the call state ([p, p + 72) inside the 512 bytes of a frame of its frames) with decode_rd_ok
       (the bytes present by astack_malloc_realizes, p's 9 shadow bytes 0, their hull visible); decode_off_win (the
       frame lies below alloc_ceiling, notice's window above it); NB = the 72 bytes stored at p, whose fields are the
       notice's: for n (0x87ff4 - 0x88058) onann_dntc timg_B (onann_w1 timg_B Bw b) b (state S_state of that world,
       old_state 0, reason 0, counter 0, retry 0, mac_offset off, personality p, the announce Some (onann_ann b) with
       the pointer a, 8-aligned, the version bytes TSS.ann_field (skipn 15 (fr_body b)) at a and the name bytes at
       a + 10 as diginet_announce_parse stored them, trans_src_ok of [a, a + 20) by decode_in_fake, decode_off_win of
       it); for fn (0x881e8 - 0x88230) onann_fntc at notice's world (state, 0, 0, counter 0, retry 0, mac_offset 0,
       personality 0, the same announce); each body: pointer 0, length 0, garr8 of [], trans_src_ok of the empty
       range at 0 (DgnTransportBCg.v trans_src_ok_null), decode_off_win of it (0 <= sp' - NOTICE_STK);
       trans_tframe_at TF at NOTICE_STK: on_announce's trans_tframe_at at ONANN_STK, carried: TF's bytes and their
       shadow are unchanged (onann_apart for the g_s stores; the own frame is a fresh frame, apart from TF's
       placement; the bcmp wrapper and the memsets keep every byte outside their windows and destinations; the record
       facts of the holds statement for the stack malloc's acall_kept and diginet_announce_parse's and
       personality_from_name's acall_kept; for the call at 0x88258, across the desk notice's acall_kept_g by
       trans_src_ok_kept over its clauses, which reach TF because trans_tf_off_g puts it outside G and onann_apart
       outside that notice's notice_wr, a row of onann_wr), and notice's window lies inside on_announce's;
       trans_rom_view_rd at the call memory (as for personality_from_name, and across the desk notice's
       acall_kept_g, whose image clause keeps every TRANS_RO_RD byte outside G, the owned statics and errno);
       tw_at at notice's world: G kept through the stack malloc (gx_kept_of_acall_kept: gx_ok, gx_noerrno),
       diginet_announce_parse and personality_from_name (gx_call_cg) and bcmp, then the tw_writes before it;
       notice_m timg_B TF at that world with that notice = Some (B', tt): the model premise through onann_model
       (call_notify's test is the indirect target's value);
       notice_apart: a byte of notice_wr is a byte of GOT (GOT.desk or GOT.foreign), a byte of G, so not a byte of
       p's frame and not a byte of [a, a + 20) (a frame byte is outside the image: AR_laws' al_client_img); the body
       range is empty; TF's range: onann_apart, since notice_wr at that world with that notice lies inside onann_wr
       Bw b (notice_wr names no world for N_DESK and N_FOREIGN);
       the N_DATA premise: vacuous (the kinds above);
       st_nev S + k + NOTICE_EV <= EV_MAX: the event count after the earlier callees plus NOTICE_EV, inside ONANN_EV
       (it counts each of the at most two notice calls of a path; all the callees' events are 0), and the stack
       malloc records no event. Its X: tw_at at notice's world after it.
     set_state as set_state_cg.v transport_set_state_cg at transportb_sigma TB_set_state (calls at 0x88128 and
       0x882b8; a G-form callee in the same G journal): the journal at the call state (the own frame live); ra =
       0x8812c / 0x882bc; gp, tp kept; a0 = s = SSTATE_S, a1 = st = 0 (S_IDLE), a2 = why = 3 (DIGINET_R_DESK_OFFLINE)
       / 5 (DIGINET_R_FOREIGN), 0 <= st, why < 2 ^ 31; sp' 32-aligned, sp0 - STK <= sp' - SSTATE_STK (ONANN_STK >= 208 +
       SSTATE_STK), sp' <= sp0; tw_at at slost_w1 B3, B3 the world the inlined session_lost starts from
       (set_S_foreign B2 0, B2 the desk notice's world after it, at 0x88128; the foreign notice's world after it at
       0x882b8), then the tw_writes of :162-163; g_fail_next of it <= 1 (notice and on_announce's stores leave the
       byte as it was: g_fail_next Bw <= 1); set_state_m timg_B TF (slost_w1 B3) S_IDLE why = Some (B4, tt): the
       model premise through onann_model and slost_model_sstate (on the path where S_state B3 = S_ONLINE, at 0x88128,
       or S_state B3 is S_ONLINE or S_WAKING, at 0x882b8); trans_tframe_at TF at SSTATE_STK (carried as for notice,
       then across the notice before it by trans_src_ok_kept over its clauses, which reach TF because trans_tf_off_g
       puts it outside G and onann_apart outside its notice_wr, and across the stores of :162-163 (onann_apart);
       set_state's window lies inside on_announce's); trans_rom_view_rd at the call memory (as for notice);
       sstate_apart TF (slost_w1 B3) S_IDLE why: onann_apart, since sstate_wr (slost_w1 B3) S_IDLE why is sstate_wr
       (slost_w1 Bw) S_IDLE why (sstate_wr reads its world only through S_state and GOT.n, and neither the desk or
       foreign notice nor the stores before it change them), a row of onann_wr; count_cid 2 at the call state =
       count_cid 2 (frames Sc) < fs_frames 2 (from the count premise: the own frame is of class 3); st_nev: the event
       count after the earlier callees plus SSTATE_EV, inside ONANN_EV. Its X: tw_at at B4, g_fail_next B4 <= 1.
     diginet_session_wake as diginet_session_wake_cg.v transport_diginet_session_wake_cg at transportb_sigma
       TB_diginet_session_wake (call at 0x88160; a G-form callee in the same G journal): the journal at the call
       state (the own frame live); ra = 0x88164; gp, tp kept; a0 = s = WAKE_S; a1 = now, 0 <= now < 2 ^ 64; sp'
       32-aligned, sp0 - STK <= sp' - WAKE_STK (ONANN_STK = 208 + WAKE_STK), sp' <= sp0; tw_at at its world B4 (the
       world after the desk notice and the store of :201, or set_state's X after the inlined session_lost's stores);
       g_fail_next B4 <= 1 (set_state's X, or notice and on_announce's stores, which leave the byte as it was:
       g_fail_next Bw <= 1); diginet_session_wake_m timg_B TF B4 now = Some (B5, r') (the model premise through
       onann_model, on the path where S_state B4 = S_IDLE and S_cfg_auto_wake B4 <> 0); trans_tframe_at TF at
       WAKE_STK (carried as for notice, then across the desk notice's acall_kept_g and, when the inlined session_lost
       runs, set_state's (0x88128), by trans_src_ok_kept over their clauses, which reach TF because trans_tf_off_g puts
       it outside G and onann_apart outside each written range; wake's window lies inside on_announce's);
       trans_tf_off_g TF: this statement's premise; trans_rom_view_rd at the call memory (as for notice); wake_apart TF
       B4: onann_apart, since wake_wr B4 lies in the row `exists Bx, wake_wr Bx` of onann_wr (wake_wr reads its world
       only through S_state and GOT.n, and set_state's notice may have advanced GOT.n); the run invariants (1) and (4)
       at B4: Bw's (above, with the index bound); count_cid 1 and count_cid 2 at the call state = count_cid 1
       (frames Sc) < fs_frames 1 and count_cid 2 (frames Sc) + 1 < fs_frames 2 (the count premises); st_nev: the
       event count after the earlier callees plus WAKE_EV, inside ONANN_EV. Its X: a0 = r' (not used), tw_at at B5,
       g_fail_next B5 <= 1.
     maybe_online as maybe_online_cg.v transport_maybe_online_cg at transportb_sigma TB_maybe_online (call at 0x881a4;
       a G-form callee in the same G journal): the journal at the call state (the own frame live); ra = 0x881a8; gp,
       tp kept; a0 = s = MAYBEON_S; sp' 32-aligned, sp0 - STK <= sp' - MAYBEON_STK, sp' <= sp0; tw_at at
       set_S_e1_named_us (set_S_foreign B2 0) 1, B2 the desk notice's world after it (notice's X, then the tw_writes
       of :211 and :212); g_fail_next of it <= 1 (as for set_state); maybe_online_m timg_B TF at it = Some (Bw', tt)
       (the model premise through onann_model, on the path where off >= 0); trans_tframe_at TF at MAYBEON_STK and
       trans_rom_view_rd (as for set_state, across the desk notice only; maybe_online's statement does not take
       trans_tf_off_g); maybeon_apart TF at it: onann_apart, since maybeon_wr of that world is maybeon_wr
       (set_S_e1_named_us (set_S_foreign (onann_w1 timg_B Bw b) 0) 1) (maybeon_wr reads S_state, S_wake_acked,
       S_e1_named_us, S_last_rx_us, S_cfg_keepalive_ms and GOT.n, none of which the desk notice's store GOT.desk
       changes), a row of onann_wr; count_cid 2 at the call state = count_cid 2 (frames Sc) < fs_frames 2 (from the
       count premise); st_nev: inside ONANN_EV. Its X: tw_at at Bw' and g_fail_next Bw' <= 1.
     __asan_set_shadow_f5 as TransportRtCg.v aset_shadow_realizes at transportb_sigma TB___asan_set_shadow_f5 with
       v = 0xf5 (call at 0x8833c; through gx_call_leaf): ecall_pre at the call state (the G journal's AR, ret_ok of
       0x88340, the realigned sp, the ESTACK bytes below it present); In (3, pos) (frames S) (the own frame, live until
       the flag store that follows); a0 = q = shadow_addr frame, a1 = n = 64 = fs_frame_bytes 3 / 8, 0 < n, [q, q + n)
       the frame's shadow. Its X: those 64 bytes are 0xf5, every other byte kept, AR at the same state; the flag store
       after it then releases the frame (astack_free_law).
   notice's, set_state's, diginet_session_wake's, maybe_online's, diginet_announce_parse's and personality_from_name's
   own record facts are premises of their holds statements.
   Stack: 192 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the memsets, the set_shadow entry), 2 * ESTACK (the bcmp wrapper),
   diginet_announce_parse's TRANS_ANP_STK, personality_from_name's PFROM_STK, notice's NOTICE_STK, set_state's
   SSTATE_STK, diginet_session_wake's WAKE_STK or maybe_online's MAYBEON_STK: ONANN_STK = 208 + WAKE_STK
   (onann_stk_eq).
   The differences from image A's form (lib/A/Prog/on_announce_cg.v), each forced by image B's code: the addresses;
   image B calls set_state (a function on image B, set_state_cg.v) from its two inlined session_lost copies, where
   image A inlines set_state and holds set_state's two notices n3 and n2 in on_announce's own frame; so the own frame
   holds a, n and fn only (352 bytes at 32, 112 and 224, class 3: __asan_stack_malloc_3, released by
   __asan_set_shadow_f5 over 64 shadow bytes; image A: 576 bytes, class 4), set_state is a callee with its own class-2
   frame, and the inlined session_lost's written range is its two stores and set_state_cg.v sstate_wr at
   slost_w1 Bw (the content of image A's session_lost_cg.v slost_wr Bw, which image B has no file for: image B's
   slost_w1 and slost_model_sstate are diginet_session_tick_cg.v's); diginet_session_wake's own frame is of class 1 on
   image B (image A: class 2), so the count premises are count_cid 3 (frames Sc) < fs_frames 3, count_cid 1
   (frames Sc) < fs_frames 1 and count_cid 2 (frames Sc) + 1 < fs_frames 2 in place of image A's count_cid 4
   (frames Sc) < fs_frames 4 and count_cid 2 (frames Sc) + 2 < fs_frames 2; diginet_announce_parse is a donor-form
   callee on image B (it calls copy_strz: diginet_announce_parse_cg.v), lifted with gx_call_cg, where image A reads
   a leaf statement through transport_leaf_wr_at, and its event count TRANS_ANP_EV joins ONANN_EV; ONANN_EV counts
   two notice calls and one set_state call per path (image A: three notice calls); the seven UBSan branches to the
   trap word are new (image A's code has no trap of its own), and each is refuted by a fact image A's form already
   has (the constant s, trans_dframe_at's fp mod 8 = 0, and buf's placement for unknown + i), so no premise is added
   for them; the real-stack release stores its zero shadow inline (image A calls __asan_set_shadow_00, not
   reached). onann_wr names a field's bytes by lib/B/Prog/m_set_cg.v twb_fld (image A's m_lost_cg.v twa_fld).

   The caller: diginet_session_rx at 0x87b78 (return address 0x87b7c), for a frame whose cmd byte (f + 30, the 1-byte
   load at 0x87b50) is 0xe0 or 0xe1 (0x87b5c - 0x87b68): a0 = s4 (its own a0, &g_s), a1 = s6 = its class-1
   side-stack frame + 32 (0x878c0; its struct diginet_frame f, filled by diginet_frame_parse at 0x878d0; the frame's
   shadow bytes 4..11, f's 64 bytes, set to 0 at 0x87888 - 0x878a4), a2 = s3 (its own a3, now). It supplies its G
   journal, tw_at, g_fail_next, the model premise (its branch of diginet_session_rx_m), trans_dframe_at of f and buf,
   trans_tframe_at, onann_apart and trans_tf_off_g of its TF (trans_tf_off_g is its own premise),
   trans_rom_view_rd, the run invariants (1) and (4) with (4)'s index bound, count_cid 3 (frames Sc) < fs_frames 3,
   count_cid 1 (frames Sc) + 1 < fs_frames 1 (its own frame is of class 1, so at this call the class-1 count is one
   more) and count_cid 2 (frames Sc) + 1 < fs_frames 2.
   The image has 1 inlined copy of find_mac (in on_announce) and 5 of session_lost (in diginet_session_rx,
   diginet_session_tick and on_announce; set_state_cg.v's list of callers): on_announce's own copies are walked
   here. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TNeed TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* on_announce's frame (`sp = sp - 192` at TB_on_announce), the at most 0x10 bytes of `sp = sp & -32` (0x87d08)
   below it, and the largest stack a callee uses below the realigned sp: ESTACK for __asan_stack_malloc_3,
   __asan_memset and __asan_set_shadow_f5 (YG0d.v ecall_pre), 2 * ESTACK for the bcmp wrapper (abcmp_realizes),
   diginet_announce_parse's TRANS_ANP_STK, personality_from_name's PFROM_STK, notice's NOTICE_STK, set_state's
   SSTATE_STK, diginet_session_wake's WAKE_STK and maybe_online's MAYBEON_STK. *)
Definition ONANN_FRAME : Z := 192.
Definition ONANN_ALIGN : Z := 0x10.
Definition ONANN_STK : Z :=
  ONANN_FRAME + ONANN_ALIGN +
  Z.max ESTACK (Z.max (2 * ESTACK) (Z.max TRANS_ANP_STK (Z.max PFROM_STK (Z.max NOTICE_STK
    (Z.max SSTATE_STK (Z.max WAKE_STK MAYBEON_STK)))))).
Lemma onann_stk_eq : ONANN_STK = ONANN_FRAME + ONANN_ALIGN + WAKE_STK.
Proof. reflexivity. Qed.
(* No allocator event: diginet_announce_parse, personality_from_name, notice, set_state, diginet_session_wake and
   maybe_online record none, and the class-3 stack malloc and its release record none (YG00.v stack_malloc,
   stack_free). A path calls notice at most twice (the desk notice, then the foreign notice on the cmd 0xe1,
   off < 0 path) and set_state at most once (one inlined session_lost per path), so the bound counts NOTICE_EV twice
   and SSTATE_EV once. *)
Definition ONANN_EV : Z :=
  TRANS_ANP_EV + PFROM_EV + 2 * NOTICE_EV + SSTATE_EV + WAKE_EV + MAYBEON_EV.
(* The side-stack class of its own frame (a0 = 352 at 0x87d38, the call of __asan_stack_malloc_3 at 0x87d3c). The
   callees that take a side-stack frame take class 1 (diginet_session_wake) and class 2 (set_state, maybe_online's
   set_state, and send_control and diginet_body_check under diginet_session_wake), hence the count premises at
   WAKE_CID and SENDCTL_CID; its own class is neither, so it changes neither count. *)
Definition ONANN_CID : Z := 3.
Lemma onann_cid_callees :
  WAKE_CID = 1 /\ SENDCTL_CID = 2 /\ SSTATE_CID = SENDCTL_CID /\ MAYBEON_CID = SENDCTL_CID /\
  ONANN_CID <> WAKE_CID /\ ONANN_CID <> SENDCTL_CID.
Proof. repeat split; try reflexivity; discriminate. Qed.
(* Its first argument: g_s's base in image B. *)
Definition ONANN_S : Z := TB_g_s.
Lemma onann_s_eq : ONANN_S = SSTATE_S /\ ONANN_S = WAKE_S /\ ONANN_S = MAYBEON_S.
Proof. repeat split; reflexivity. Qed.
(* The addresses of the g_s fields the code reads or writes (s + 18184, s + 128, s + 112, s + 96, s + 104, s + 136,
   s + 212, s + 168, s + 16, s + 140) and of cfg.host_mac (s + 0), which the bcmp calls read. *)
Lemma onann_addrs :
  ONANN_S = 0x5df640 /\
  ONANN_S + (TW.A_S_stats_rx_ignored - TW.OFF_g_s) = 0x5e3d48 /\
  ONANN_S + (TW.A_S_personality - TW.OFF_g_s) = 0x5df6c0 /\
  ONANN_S + (TW.A_S_state - TW.OFF_g_s) = 0x5df6b0 /\
  ONANN_S + (TW.A_S_notify - TW.OFF_g_s) = 0x5df6a0 /\
  ONANN_S + (TW.A_S_notify_ctx - TW.OFF_g_s) = 0x5df6a8 /\
  ONANN_S + (TW.A_S_foreign - TW.OFF_g_s) = 0x5df6c8 /\
  ONANN_S + (TW.A_S_inflight - TW.OFF_g_s) = 0x5df714 /\
  ONANN_S + (TW.A_S_desk_counter_valid - TW.OFF_g_s) = 0x5df6e8 /\
  ONANN_S + (TW.A_S_cfg_auto_wake - TW.OFF_g_s) = 0x5df650 /\
  ONANN_S + (TW.A_S_e1_named_us - TW.OFF_g_s) = 0x5df6cc /\
  ONANN_S + (TW.A_S_cfg_host_mac - TW.OFF_g_s) = 0x5df640.
Proof. repeat split; reflexivity. Qed.
(* The variables in its class-3 frame (the description string at 0x1d874): a at 32 (40 bytes), n at 112, fn at 224
   (72 bytes each); 352 bytes in all, inside the 512 bytes of a class-3 frame. *)
Definition ONANN_A : Z := 32.
Definition ONANN_N : Z := 112.
Definition ONANN_FN : Z := 224.
Lemma onann_frame_fits : ONANN_FN + NTC_SIZE = 296 /\ 296 <= 352 /\ 352 <= fs_frame_bytes ONANN_CID.
Proof. repeat split; cbv; congruence. Qed.

(* The model's steps (TSess.v on_announce_m): the ann_code test of :187, the announce notice() reads (:190), a.name
   (:191) and the personality pointer the model computes from it, the world after :192-193, find_mac's result (:194)
   at a world, the desk notice of :196-197 and the foreign notice of :217 at a world. Image-free: image A's text. *)
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
   copies' stores: inflight and desk_counter_valid (4 bytes each, the code's own) and set_state's (set_state_cg.v
   sstate_wr at slost_w1 Bw with S_IDLE and the copy's why: when the state is not S_IDLE, state and the N_STATE
   notice's GOT.t[GOT.n] and GOT.n; it reads its world only through S_state and GOT.n, which are Bw's at either call,
   since the desk and foreign notices store neither); diginet_session_wake's (diginet_session_wake_cg.v wake_wr at
   the world it is called with, which may follow set_state's notice: the row names no world, wake_wr reading it only
   through S_state and GOT.n); and maybe_online's (maybe_online_cg.v maybeon_wr at the world it is called with, whose
   reads maybeon_wr (set_S_e1_named_us (set_S_foreign (onann_w1 timg_B Bw b) 0) 1) gives: the desk notice's store of
   GOT.desk changes none of them). *)
Definition onann_wr (Bw b : list byte) (a : Z) : Prop :=
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_rx_ignored 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_personality 8 a \/
  notice_wr (onann_w1 timg_B Bw b) (onann_dntc timg_B (onann_w1 timg_B Bw b) b) a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_foreign 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_desk_counter_valid 4 a \/
  sstate_wr (slost_w1 Bw) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_OFFLINE a \/
  (exists Bx : list byte, wake_wr Bx a) \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_e1_named_us 4 a \/
  maybeon_wr (TW.set_S_e1_named_us (TW.set_S_foreign (onann_w1 timg_B Bw b) 0) 1) a \/
  notice_wr (onann_w1 timg_B Bw b) (onann_fntc (onann_w1 timg_B Bw b) b) a \/
  sstate_wr (slost_w1 Bw) TS0.DIGINET_S_IDLE TS0.DIGINET_R_FOREIGN a.

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. notice, set_state, diginet_session_wake and maybe_online read TF after the g_s stores and the earlier
   callees' stores (notice_cg.v notice_apart, set_state_cg.v sstate_apart, diginet_session_wake_cg.v wake_apart,
   maybe_online_cg.v maybeon_apart). *)
Definition onann_apart (Fr : option TI.tframe) (Bw b : list byte) : Prop :=
  forall x, onann_wr Bw b x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow
   (lib/B/YF0m.v Tfib_zero_shadow row (0x5df640, 0x5e3d98 - 0x5df640)). The instrumented checks of the accesses at
   s + 16 .. s + 18191 read it, and the bcmp range [s, s + 6) and its aligned group of 8 shadow bytes
   ([g_s, g_s + 64): g_s is 64-aligned) lie in it. *)
Definition trans_onann_cells (B : asyms) : Prop := decode_zshadow_at B ONANN_S (ONANN_S + TW.SZ_g_s).

Section onann. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   onann_wr Bw b, no meter charge (the side-stack frame changes st_fs only), and X: the world relation at the model's
   world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this function takes
   is released. *)
Definition transport_onann_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' b : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs ONANN_STK ONANN_EV 0 (onann_wr Bw b)
    (fun regs2 W2 mem2 => tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_on_announce_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 ONANN_S -> YK11.getr regs 11 = w64 fp -> YK11.getr regs 12 = w64 now ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - ONANN_STK -> spZ regs <= sp0 ->
    0 <= now < 2 ^ 64 ->
    trans_dframe_at B lyc Sc W memc regs ONANN_STK fp buf b fj ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.on_announce_m timg_B TF Bw b now = Some (Bw', tt) ->
    trans_tframe_at B lyc Sc W memc regs ONANN_STK TF ->
    trans_tf_off_g TF ->
    trans_rom_view_rd W memc ->
    onann_apart TF Bw b ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    TW.g_ncmd Bw <= TC.CMDS_MAX ->
    count_cid ONANN_CID (frames Sc) < fs_frames ONANN_CID ->
    count_cid WAKE_CID (frames Sc) < fs_frames WAKE_CID ->
    count_cid SENDCTL_CID (frames Sc) + 1 < fs_frames SENDCTL_CID ->
    st_nev S + k + ONANN_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_onann_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

(* The statement the walk will prove: the class-3 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the record facts that no byte of G and
   no TRANS_RO_RD byte is an owned static or errno (they carry the trans_src_ok of TF and of the bytes at buf, G and
   the TRANS_RO_RD bytes across the stack malloc's acall_kept and diginet_announce_parse's and
   personality_from_name's acall_kept, and TF's trans_src_ok, with trans_tf_off_g, and the TRANS_RO_RD bytes across
   notice's and set_state's acall_kept_g; DgnTransportBCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno give gx_ok and
   gx_noerrno from the first two), the allocator, meter and side-stack laws, and the contracts of
   __asan_stack_malloc_3, diginet_announce_parse, diginet_personality_from_name, the bcmp wrapper, __asan_memset,
   notice (at the value the session's notify pointer holds), set_state, diginet_session_wake, maybe_online and
   __asan_set_shadow_f5 give the contract at TB_on_announce. *)
Definition transport_on_announce_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) ONANN_CID = transportb_sigma TB___asan_stack_malloc_3 ->
  transport_cells B -> trans_onann_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B ONANN_CID) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_announce_parse_cg fx' rc B MT (transportb_sigma TB_diginet_announce_parse)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_personality_from_name_cg fx' rc B MT (transportb_sigma TB_diginet_personality_from_name)) ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_B)) ->
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_session_wake_cg fx' rc B MT (transportb_sigma TB_diginet_session_wake)) ->
  (forall fx' : YK11.FPState, @transport_maybe_online_cg fx' rc B MT (transportb_sigma TB_maybe_online)) ->
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transportb_sigma TB___asan_set_shadow_f5) 0xf5) ->
  transport_on_announce_cg (transportb_sigma TB_on_announce).
End onann.
