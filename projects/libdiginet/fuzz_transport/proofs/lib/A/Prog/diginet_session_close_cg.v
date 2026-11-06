(* diginet_session_close_cg: the ASan walk contract of diginet_session_close (transport/src/diginet_session.c:147-158,
   with set_state (:79-86) inlined; model lib/TModel/TSess.v diginet_session_close_m, send_control_m and set_state_m)
   on fuzz_transport.asan (e89be137db17) at 0x8713c = transport_sigma TS_diginet_session_close, size 1112, as
   STATEMENTS only (no proof). It stores into g_s, a harness global, takes a class-2 side-stack frame for set_state's
   struct diginet_notice, calls send_control (a G-form callee) and calls notice through the session's notify pointer,
   so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over G =
   lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v
   transport_cg_post (acall_kept_g over G_HARNESS). The G form and the side-stack frame are session_lost_cg.v's (its
   inlined set_state is the same code); the call of send_control with kp = klp = 0 is send_control_cg.v's second
   caller.

   The contract. a0 = s = &g_s = 0x5df9c0 (TWorldA.v TA_g_s), a1 = now (uint64_t, which the code does not read). TF is
   the current heap frame (check_state_data_cg.v trans_tframe_at at this call's window); the read-only bytes the
   callees' callees read are the image's (trans_rom_view_rd). The memory relates to the world Bw by image A's world
   relation (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview), g_fail_next Bw <= 1, and
   diginet_session_close_m timg_A TF Bw now = Some (Bw', r). No byte the call stores is a byte of TF (close_apart).
   Class 2 of the side stack has three free frames (its own, send_control's, and diginet_body_check's inside
   diginet_frame_build inside send_control). The function returns to ra with a0 = r (sign-extended), the
   callee-saved registers kept, no allocator event and no meter charge (its side-stack frame changes the state's st_fs
   only: ameter_fs_laws), its side-stack frame released (the caller's frames exactly), the caller's blocks exactly,
   the bytes acall_kept_g G_HARNESS keeps (the bytes at or above alloc_ceiling outside the call's stack window
   [sp - CLOSE_STK, sp), the image bytes outside G, the owned statics and errno, the caller's block and frame bytes
   outside close_wr TF Bw), the world relation at Bw', and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/diginet_session_close_c.v): a0 =
   W_BASE_PLAIN + OFF_g_s -> a0 = TA_g_s; a1 = now with 0 <= now < 2 ^ 64, kept; wmem -> tw_at; g_fail_next B <= 1 kept
   as a premise (send_control's statement asks it), and the post's g_fail_next B' <= 1 kept in X (send_control's X
   gives it after the send; the code neither reads nor writes g_fail_next; notice's N_STATE path does not write it:
   lib/TModel/TCb.v notice_m); diginet_session_close_m verbatim at timg_A (timg_plain -> timg_A); tframe_at ->
   trans_tframe_at at CLOSE_STK, and its off_world clause (TF lies outside the plain world
   [W_BASE_PLAIN, W_BASE_PLAIN + W_LEN), which on image A is G, lib/Prog/T/TContract.v tframe_at) -> two facts, since
   check_state_data_cg.v trans_tframe_at drops that clause: close_apart, no byte the call stores is a byte of TF
   (session_lost_cg.v slost_apart's form), and trans_tf_off_g (check_state_data_cg.v), no byte of TF is a byte of G.
   trans_tf_off_g is what carries TF across send_control, which writes G (tx_frames and io_send's fields):
   acall_kept_g keeps the image bytes OUTSIDE G, the caller's block, frame and stack bytes outside the written range,
   and says nothing of a byte of G, while send_control's X pins G only to the model world B1. With trans_tf_off_g, TF
   is block, frame or stack memory, or read-only data, outside sendctl_wr 0 0 (close_apart), so the block, frame,
   stack and image clauses of acall_kept_g keep its bytes and its frames' shadow (the read-only case through
   trans_ro_rd_scoped), and its placement follows clause by clause (DgnTransportCg.v trans_src_ok_kept;
   trans_src_ok_acall_g itself asks every byte of G to be kept, which send_control does not give); relro_img -> trans_rom_view_rd; stk, lo + FRAME <= sp, sp mod 16 and w_off_stack
   -> the journal's window premises; mem_inv is dropped. The post's munch, wmono, stk and mem_inv ->
   transport_cg_post (the journal at the return, acall_kept_g over close_wr TF Bw); wmem -> X's tw_at.

   Premises the plain contract does not have:
   - count_cid 2 (frames Sc) + 2 < fs_frames 2: its own class-2 frame is live at the call of send_control (0x87514),
     whose statement asks count_cid 2 + 1 < fs_frames 2 at its call state, where the frames are the own frame ::
     frames Sc (send_control's own class-2 frame, then diginet_body_check's inside diginet_frame_build). With it
     __asan_stack_malloc_2 returns a frame (astack_malloc_realizes), so the real-stack arm is not taken.
   - close_apart and trans_tf_off_g (above; both translate the plain tframe_at's off_world clause).
   (The plain contract's relro_img is translated above as trans_rom_view_rd W memc: send_control's and notice's
     premise, taken at entry as session_lost_cg.v takes it.)
   - in the holds statement: trans_close_cells (g_s's zero shadow), the side-stack laws, and trans_g_unowned,
     trans_g_no_errno, trans_ro_rd_unowned and trans_rom_no_errno: they carry TF's trans_src_ok (inside
     trans_tframe_at) across the stack malloc (DgnTransportCg.v trans_src_ok_inner, the stack malloc adding the own
     frame and keeping the blocks, TF's bytes kept by its acall_kept with the four facts and its decode_rd_ok by
     trans_rd_ok_sh, the fresh frame apart from TF's placement: trans_src_ok_disj_own) and across send_control's
     acall_kept_g (trans_src_ok_kept over its
     clauses), the
     TRANS_RO_RD bytes (trans_ro_rd_scoped), and G (TransportGCg.v gx_kept_of_acall_kept with gx_ok and gx_noerrno,
     which DgnTransportCg.v G_HARNESS_gx_ok and G_HARNESS_gx_noerrno give from the first two; send_data_cg.v's form).
   Run invariants carried (on its own Bw): (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME and (4)
   every PENDING command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX, both send_control_cg.v's premises.
   diginet_session_close_m calls send_control_m at Bw itself (the loads at s + 116, s + 136 and s + 112 before it
   store nothing), so both carry verbatim. notice carries check_state_data's body-range premise only for a notice of
   kind N_DATA; this notice has kind N_STATE (close_ntc; the store of 2 at p by 0x87344), so that premise holds
   vacuously. The others (check_latest_queue's, take's cfg bound) are not reached from diginet_session_close. Its own
   accesses are at fixed offsets of g_s (s + 96 .. s + 215) and its one memset fills 56 bytes of its own frame, so its
   code needs no bound that the model does not give.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   1112 code bytes are equal in both files), 278 words:
     0x8713c - 0x87178 sp = sp - 160; 0x87140 stores 8 zero bytes at sp; ra at sp + 152, s0 .. s11 at sp + 144 ..
                      sp + 56, loaded back at 0x874c4 - 0x874f4; s0 = sp + 160 (the entry sp, kept to 0x874c0).
     0x8717c - 0x87180 sp = sp & -32 (at most 0x10 below entry - 160); s1 = the realigned sp.
     0x87184 - 0x8719c a2 = the 8-byte load of the GOT word 0xa40e8 (it holds 0xaca00), then the 4-byte load of the
                      flag word at 0xaca00; a1 = the 8-byte load of the GOT word 0xa4090 (it holds 0xac9f8), s9 = the
                      8-byte load at 0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s3 = s.
     0x871a0 - 0x871b4 the flag word = 0 goes to 0x871b4 (s2 = 0); transport_cells row 6 gives 1. a0 = 160 and the
                      call of __asan_stack_malloc_2 (frame_alloc_2, 0x3d99c = transport_sigma
                      TS___asan_stack_malloc_2) at 0x871a8, return address 0x871ac: a class-2 side-stack frame
                      (fs_frame_bytes 2 = 256 bytes); s2 = the result.
     0x871b8 - 0x871d8 s8 = s2; s2 <> 0 goes to 0x871dc. The real-stack arm (s2 = 0): s8 = (sp - 160) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s8), then sp = s8. With
                      count_cid 2 (frames Sc) < fs_frames 2 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s8 = s2.
     0x871dc          the 8-byte store of frame at s1 + 48 (its own machine frame).
     0x871e0 - 0x87208 the frame header: 0x41b58ab3 at frame, the description string 0x1fa69 ("1 32 72 6 n.i:83": one
                      variable, 72 bytes at frame + 32; session_lost's and maybe_online's frames name the same string)
                      at frame + 8, the function's address 0x8713c at frame + 16.
     0x871ec, 0x87210 - 0x87264 s7 = (frame >> 3) + 0x7fff8000; the frame's shadow bytes 0..3 = 0xf1, 4..12 = 0xf8
                      (the notice's 72 bytes at frame + 32, marked out of scope), 13..19 = 0xf3 (guard bytes).
     0x87268          s = 0 goes to 0x873c8 (a3 = -1, :150-151); s = 0x5df9c0, so not taken.
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on; for an 8-byte access any k <> 0 goes to the error path.
     0x8726c - 0x87288 the check of the 4-byte load at s + 116; the 4-byte signed load (S_desk_known Bw) = 0 goes to
                      0x872c4 (:153); s5 = s + 112.
     0x8728c - 0x872a4 the check of the 4-byte load at s + 136; the load (S_foreign Bw) <> 0 goes to 0x872c4.
     0x872a8 - 0x872c0 the check of the 4-byte load at s + 112; the load (S_state Bw) <> 3 (S_CLOSED) goes to 0x87500;
                      = 3 falls to 0x872c4. Past these tests, close_go Bw holds exactly on the path to 0x87500.
     0x87500 - 0x8751c a1 = 0xe3 (DIGINET_CMD_DISCONNECT), a0 = s, a2 = a3 = a4 = 0; the call of send_control
                      (0x86d5c = transport_sigma TS_send_control) at 0x87514, return address 0x87518 (:154); a3 = its
                      a0 (r); to 0x872c8.
     0x872c4          a3 = 0 (r = 0, :152, when close_go Bw is false).
     0x872c8 - 0x872dc the check of the 4-byte store at s + 212, then the store of 0 there (S_inflight, :155). The world
                      is now close_w1 B1, B1 = send_control's world, or Bw when close_go Bw is false.
     0x872e0 - 0x872f8 s10 = the address of the shadow byte of s + 112; the check of the 4-byte load; s11 = the 4-byte
                      signed load at s + 112 (S_state (close_w1 B1)); s4 = 3; s11 = 3 goes to 0x873cc: set_state's
                      :81-82, no notice and no state store.
     0x872fc          the 8-byte store of a3 (r) at s1 + 24 (its own machine frame), loaded back at 0x873c0.
     0x87300 - 0x87324 s6 = frame + 32 = p, the struct diginet_notice; shadow bytes 4..12 = 0 (its 72 bytes marked
                      usable).
     0x87328 - 0x87334 a0 = p + 16, a1 = 0, a2 = 56; the call of __asan_memset (checked_memset, 0x5284c =
                      transport_sigma TS___asan_memset) at 0x87334, return address 0x87338: the notice's bytes
                      16 .. 71 set to 0 (:83).
     0x87338 - 0x8734c plain stores into the frame: the 8 bytes 0x0000000300000002 at p (kind = N_STATE = 2 at p,
                      state = S_CLOSED = 3 at p + 4), the low 32 bits of s11 at p + 8 (old), 8 at p + 12 (reason =
                      R_CLOSED). The 72 bytes at p are then close_ntc B1 as trans_ntc_at reads them: every field from
                      p + 16 on is 0 (the announce pointer 0, n_ann = None; the body pointer 0 and body_len 0, n_body =
                      []).
     0x87350 - 0x87360 the check of the 4-byte store at s + 112 (its shadow byte read again through s10), then the
                      store of 3 at s + 112 (S_state = S_CLOSED, :84). The world is now close_w2 B1.
     0x8735c - 0x87384 the checks of the 8-byte loads at s + 96 and at s + 104.
     0x87388 - 0x87394 a2 = the 8-byte load at s + 96 (S_notify (close_w2 B1): tw_read, and the model's call_notify
                      gives TI.ti_notice timg_A = 0x83578); a0 = the 8-byte load at s + 104 (notify_ctx, which notice
                      does not read); a1 = p; the indirect call (jalr a2) at 0x87394, return address 0x87398 (:85;
                      struct diginet_session + 96, notify -> notice).
     0x87398 - 0x873c4 shadow bytes 4..12 = 0xf8 (the notice out of scope again); a3 = the 8-byte load at s1 + 24
                      (r); to 0x873cc.
     0x873cc - 0x873d4 the header word 0x45e0360e stored at frame (every path).
     0x873d8          s2 = 0 goes to 0x8746c (the real-stack arm; not taken).
     0x873dc - 0x87468 the release: the frame's 32 shadow bytes (256 bytes) = 0xf5 (released); a0 = the 8-byte load at
                      s2 + 248 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a0 (YG0d.v astack_free_law); to 0x874bc.
     0x8746c - 0x874b8 the real-stack arm's release: shadow bytes 0..19 = 0.
     0x874bc - 0x874fc a0 = a3 (r); sp = s0 - 160, ra and s0 .. s11 loaded back, sp = sp + 160, return. a1 .. a7 at the
                      return are not stated.
   No tail jump: the calls are jal with link (the stack malloc, the memset, send_control, and the 8 error-path
   calls) and one jalr with link (notice at 0x87394); every j is inside the function, and the function's own return
   is the ret at 0x874fc.
   The model and the code: the three tests at 0x87288, 0x872a4 and 0x872c0 are close_go (S_desk_known Bw against 0,
   S_foreign Bw against 0, S_state Bw against S_CLOSED, each a 32-bit signed read); the call of send_control is
   send_control_m at Bw with cmd 0xe3 and ack 0, and its a0 is r (close_sent); the store at s + 212 is set_S_inflight
   (put 4 of 0) at B1; the test at 0x872f8 is set_state_m's S_state B =? S_CLOSED at close_w1 B1; the store at
   s + 112 is set_state_m's set_S_state (put 4 of 3); each a tw_write inside g_s's payload; the call is call_notify at
   close_w2 B1 with close_ntc B1 (close_model, close_setstate). The code has no trap of its own; the model's None cases
   are send_control_m's (send_control_cg.v), call_notify's (S_notify <> ti_notice timg_A) and notice's, all ruled out
   by the model premise.
   Error paths (8 calls; no abort) and the facts that rule them out:
     TS___asan_report_load4 0x59608 (errpath_load4) at 0x8752c (s + 116), 0x87550 (s + 112, the load at 0x872f0),
       0x87560 (s + 136), 0x87588 (s + 112, the load at 0x872b8);
     TS___asan_report_store4 0x59928 (errpath_store4) at 0x8753c (s + 212), 0x87574 (s + 112);
     TS___asan_report_load8 0x596a8 (errpath_load8) at 0x8758c (s + 96) and 0x87590 (s + 104).
     Each guards a naturally aligned access inside g_s's payload [0x5df9c0, 0x5e4118) (2283 whole granules), whose
     shadow bytes are 0 (trans_close_cells, read at each AR state by DgnTransportCg.v decode_zshadow_rd), so k = 0.
     The memset's own check (aintrin_realizes' pre, from the G journal through TransportGCg.v gx_intrin_at): the
     destination [p + 16, p + 72) lies in the frame this function took; its shadow bytes 6 .. 12 are 0 since
     0x87324 and their hull is visible (astack_malloc_realizes' zero_shadow); each destination byte is a byte of the
     journal's own frame list after the stack malloc (YCbq.v awr_byte's in_frames: transport_twr_ok_g), not owned,
     not in the ESTACK bytes below sp.
   Writes: g_s's inflight and state (bytes of G); its own machine frame (s1 + 24, s1 + 48); its own side-stack frame,
   that frame's shadow bytes and its flag byte; send_control's stores (send_control_cg.v sendctl_wr 0 0: tx_frames and
   io_send's iosend_wr 60, bytes of G); notice's stores (notice_wr, bytes of GOT). No byte of a caller's frame or block
   is written, so close_wr is the written range. The G kit for the own frame is session_lost_cg.v's (TransportGCg.v
   dk_kept_own_g with dkg_nf and dkg_nf_sep, dk_kept_trans_nf_g for both callees, whose acall_kept_g is stated at the
   call state with the own frame live, dkg_frame_al64, gx_intrin_at, dk_kept_frame_byte_g; CanKit.v
   can_stack_malloc_at and can_flag_store_pi read inside the G journal through gx_lift).
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_2 as astack_malloc_realizes ... CLOSE_CID (with pc_stack_malloc (as_code B) CLOSE_CID =
       transport_sigma TS___asan_stack_malloc_2): count_cid 2 (frames Sc) < fs_frames 2 from the count premise.
     __asan_memset as aintrin_realizes ... OSet (transport_sigma TS___asan_memset), call at 0x87334 (above).
     notice as notice_cg.v transport_notice_cg at TI.ti_notice timg_A (= 0x83578 = transport_obj 10, notice_cg.v
       notice_at; call at 0x87394; a G-form callee composed in the same G journal, no gx_call_cg):
       the journal: the G journal at the call state (the own frame live); ra = 0x87398 (ret_ok, 4096 <= ra); gp, tp
         kept; a1 = p;
       sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - NOTICE_STK: sp' >= sp - 176 and
         CLOSE_STK = 176 + SENDCTL_STK >= 176 + NOTICE_STK; sp' <= sp0;
       trans_ntc_at p (close_ntc B1): 0 < p and p mod 8 = 0 (p = frame + 32, dkg_frame_al64); trans_src_ok by
         decode_in_fake at the call state ([frame + 32, frame + 104) inside the 256 bytes of a frame of its frames)
         with decode_rd_ok (the bytes present by astack_malloc_realizes, shadow bytes 4..12 = 0, their hull visible);
         decode_off_win (the frame lies below alloc_ceiling, notice's window above it); NB = the 72 bytes stored at
         0x87334 - 0x8734c, whose fields are close_ntc's; the body: pointer 0, length 0, garr8 of [], trans_src_ok of
         the empty range at 0 (DgnTransportCg.v trans_src_ok_null), decode_off_win of it; the announce: n_ann = None
         with the pointer 0;
       trans_tframe_at TF at NOTICE_STK: the entry's trans_tframe_at at CLOSE_STK, carried: across the stack malloc
         (trans_src_ok_inner with TF's bytes kept, trans_rd_ok_sh and trans_src_ok_disj_own; the four record facts),
         across send_control (trans_src_ok_kept over the clauses of its
         acall_kept_g, which reach TF because trans_tf_off_g puts it outside G and close_apart outside
         sendctl_wr 0 0), across
         the g_s stores (close_apart) and the memset (the own frame); notice's window lies inside this call's;
       trans_rom_view_rd at the call memory: the stack malloc's acall_kept and send_control's acall_kept_g keep every
         TRANS_RO_RD byte (trans_ro_rd_scoped, from trans_ro_rd_unowned and trans_rom_no_errno), the memset keeps every
         byte outside its destination and ESTACK bytes, and no store of this function reaches a read-only byte;
       tw_at at close_w2 B1: tw_at at B1 (send_control's X, or Bw kept through the stack malloc by
         gx_kept_of_acall_kept when close_go Bw is false), then the two tw_writes;
       notice_m timg_A TF (close_w2 B1) (close_ntc B1) = Some (Bw', tt): the model premise through close_model and
         close_setstate (on this path S_state (close_w1 B1) is not S_CLOSED; call_notify's test is the indirect
         target's value);
       notice_apart: a byte of notice_wr is a byte of GOT (kind N_STATE), a byte of G, so not a byte of p's frame (a
         frame byte is outside the image: AR_laws' al_client_img); the body range is empty and n_ann = None; TF's range:
         close_apart, since on this path notice_wr (close_w2 B1) (close_ntc B1) lies inside close_wr TF Bw;
       the N_DATA premise: vacuous (n_kind = N_STATE);
       st_nev S + k + NOTICE_EV <= EV_MAX: the count after send_control (SENDCTL_EV) plus NOTICE_EV, inside CLOSE_EV.
     send_control as send_control_cg.v transport_send_control_cg at transport_sigma TS_send_control (call at 0x87514,
       when close_go Bw holds; a G-form callee composed in the same G journal, no gx_call_cg):
       the journal at the call state (the own frame live); ra = 0x87518; gp, tp kept; a0 = SENDCTL_S = s, a1 = cmd =
         0xe3 (0 <= cmd < 2 ^ 8), a2 = bv_swrap 32 0 = 0 (ack = 0), a3 = kp = 0, a4 = klp = 0 (the keep disjunction's
         left side);
       sp' 32-aligned; sp0 - STK <= sp' - SENDCTL_STK: sp' >= sp - 176 and CLOSE_STK = 176 + SENDCTL_STK
         (close_stk_eq); sp' <= sp0;
       tw_at at Bw (G kept through the stack malloc: gx_kept_of_acall_kept with gx_ok and gx_noerrno; the stores
         before the call are into the own frames and their shadow); g_fail_next Bw <= 1 (the premise);
       send_control_m timg_A TF Bw 0xe3 0 = Some (B1, (r, f)): close_sent's first branch (close_model);
       trans_rom_view_rd at the call memory (kept through the stack malloc: trans_ro_rd_scoped);
       run invariants (1) and (4): the premises, at the same Bw;
       count_cid 2 at the call state = count_cid 2 (frames Sc) + 1, and + 1 < fs_frames 2 is the count premise;
       st_nev S + k + SENDCTL_EV <= EV_MAX (the stack malloc records no event; CLOSE_EV = SENDCTL_EV + NOTICE_EV).
       Its post is transport_cg_post_out with sendctl_outs 0 0 = [] (TransportGCg.v transport_cg_post_out_nil), and its
       X gives a0 = r, tw_at at B1 and g_fail_next B1 <= 1.
   notice's and send_control's own record facts are premises of their holds statements.
   Stack: 160 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the memset), notice's NOTICE_STK or send_control's SENDCTL_STK:
   CLOSE_STK = 176 + SENDCTL_STK (close_stk_eq).

   The caller: LLVMFuzzerTestOneInput at 0x82278 (return address 0x8227c), the operation that closes the session.
   Its inlined copy of the harness's m_close runs first: the three tests at 0x8191c - 0x81940 (M.desk_known,
   M.foreign, and M.state against 3), then either the S_CLOSED path at 0x81944 - 0x81948 (M.fly.on = 0, then the
   jump to 0x82268, which skips the stores) or the stores at 0x821cc - 0x82264 (OW.e3 + 1 and M.fail = 0, both only on the 0x821cc
   entry; M.fly.on = 0; m_set's OW.t[OW.n] and OW.n; M.state = 3). Then a0 = 0x5df9c0 (&g_s, formed at 0x82270 - 0x82274) and a1 =
   the 8-byte load at 0x8226c (g_now). It supplies its G journal, tw_at, g_fail_next, the model premise (its call of
   diginet_session_close_m), trans_tframe_at, close_apart and trans_tf_off_g of its TF (all three vacuous there),
   trans_rom_view_rd, the two run invariants, and the class-2 count: it holds a class-2 side-stack frame of its own while it calls, so its statement must leave room
   for three more class-2 frames below it. *)
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

(* diginet_session_close's frame (`sp = sp - 160` at TS_diginet_session_close), the at most 0x10 bytes of
   `sp = sp & -32` (0x8717c) below it, and the largest stack a callee uses below the realigned sp: ESTACK for
   __asan_stack_malloc_2 and __asan_memset (YG0d.v ecall_pre), notice's NOTICE_STK, send_control's SENDCTL_STK. *)
Definition CLOSE_FRAME : Z := 160.
Definition CLOSE_ALIGN : Z := 0x10.
Definition CLOSE_STK : Z := CLOSE_FRAME + CLOSE_ALIGN + Z.max ESTACK (Z.max NOTICE_STK SENDCTL_STK).
Lemma close_stk_eq : CLOSE_STK = CLOSE_FRAME + CLOSE_ALIGN + SENDCTL_STK.
Proof. reflexivity. Qed.
(* No allocator event: send_control and notice record none, and the class-2 stack malloc and its release record none
   (YG00.v stack_malloc, stack_free). *)
Definition CLOSE_EV : Z := SENDCTL_EV + NOTICE_EV.
(* The side-stack class (a0 = 160 at 0x871a4, the call of __asan_stack_malloc_2 at 0x871a8): the class send_control's
   frame and diginet_body_check's frame (inside diginet_frame_build inside send_control) take, hence the + 2 of the
   count premise. *)
Definition CLOSE_CID : Z := 2.
Lemma close_cid_sendctl : CLOSE_CID = SENDCTL_CID.
Proof. reflexivity. Qed.
(* Its first argument: g_s's base in image A. *)
Definition CLOSE_S : Z := TA_g_s.
(* The addresses of the six g_s fields the code reads or writes (s + 116, s + 136, s + 112, s + 212, s + 96,
   s + 104). *)
Lemma close_addrs :
  CLOSE_S = 0x5df9c0 /\ CLOSE_S = SENDCTL_S /\
  CLOSE_S + (TW.A_S_desk_known - TW.OFF_g_s) = 0x5dfa34 /\
  CLOSE_S + (TW.A_S_foreign - TW.OFF_g_s) = 0x5dfa48 /\
  CLOSE_S + (TW.A_S_state - TW.OFF_g_s) = 0x5dfa30 /\
  CLOSE_S + (TW.A_S_inflight - TW.OFF_g_s) = 0x5dfa94 /\
  CLOSE_S + (TW.A_S_notify - TW.OFF_g_s) = 0x5dfa20 /\
  CLOSE_S + (TW.A_S_notify_ctx - TW.OFF_g_s) = 0x5dfa28.
Proof. repeat split; reflexivity. Qed.

(* The model's steps (TSess.v diginet_session_close_m, set_state_m): the test of :153; the send of :154 (send_control's
   world and result, or Bw and 0); the world after the store of :155; the world after set_state's store of the state
   (:84); and set_state's notice (:83). *)
Definition close_go (Bw : list byte) : bool :=
  negb (TW.S_desk_known Bw =? 0) && (TW.S_foreign Bw =? 0) && negb (TW.S_state Bw =? TS0.DIGINET_S_CLOSED).
Definition close_sent (I : TI.timg) (F : option TI.tframe) (Bw : list byte) : option (list byte * Z) :=
  if close_go Bw then
    match TSS.send_control_m I F Bw TS0.DIGINET_CMD_DISCONNECT 0 with
    | None => None
    | Some (B1, (r, _)) => Some (B1, r)
    end
  else Some (Bw, 0).
Definition close_w1 (B1 : list byte) : list byte := TW.set_S_inflight B1 0.
Definition close_w2 (B1 : list byte) : list byte := TW.set_S_state (close_w1 B1) TS0.DIGINET_S_CLOSED.
Definition close_ntc (B1 : list byte) : TI.ntc :=
  TI.Ntc TS0.DIGINET_N_STATE TS0.DIGINET_S_CLOSED (TW.S_state (close_w1 B1)) TS0.DIGINET_R_CLOSED 0 0 0 0 None [] 0.
Lemma close_model : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (now : Z),
  TSS.diginet_session_close_m I F Bw now =
  match close_sent I F Bw with
  | None => None
  | Some (B1, r) =>
      match TSS.set_state_m I F (close_w1 B1) TS0.DIGINET_S_CLOSED TS0.DIGINET_R_CLOSED with
      | None => None
      | Some (B2, _) => Some (B2, r)
      end
  end.
Proof. intros I F Bw now. reflexivity. Qed.
Lemma close_setstate : forall (I : TI.timg) (F : option TI.tframe) (B1 : list byte),
  TSS.set_state_m I F (close_w1 B1) TS0.DIGINET_S_CLOSED TS0.DIGINET_R_CLOSED =
  if TW.S_state (close_w1 B1) =? TS0.DIGINET_S_CLOSED then Some (close_w1 B1, tt)
  else TSS.call_notify I F (close_w2 B1) (close_ntc B1).
Proof. intros I F B1. reflexivity. Qed.

(* The bytes the code stores outside its own frames, exactly, by path: send_control's (send_control_cg.v sendctl_wr
   with kp = klp = 0: g_s.stats.tx_frames and io_send's iosend_wr 60) when close_go Bw holds; g_s's inflight (4
   bytes); and, when the state of close_w1 B1 is not S_CLOSED, g_s's state (4 bytes) and notice's stores at the world
   close_w2 B1 (notice_cg.v notice_wr: for an N_STATE notice, GOT.t[GOT.n] when 0 <= GOT.n < TRANS_MAX, and GOT.n). *)
Definition close_wr (F : option TI.tframe) (Bw : list byte) (a : Z) : Prop :=
  (close_go Bw = true /\ sendctl_wr 0 0 a) \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight 4 a \/
  (exists B1 r, close_sent timg_A F Bw = Some (B1, r) /\ TW.S_state (close_w1 B1) <> TS0.DIGINET_S_CLOSED /\
     (twa_fld TW.OFF_g_s TA_g_s TW.A_S_state 4 a \/ notice_wr (close_w2 B1) (close_ntc B1) a)).

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. notice reads TF after send_control's stores, the g_s stores and its own (notice_cg.v notice_apart). *)
Definition close_apart (Fr : option TI.tframe) (Bw : list byte) : Prop :=
  forall x, close_wr Fr Bw x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented checks of the accesses at s + 96 .. s + 215 read it. *)
Definition trans_close_cells (B : asyms) : Prop := decode_zshadow_at B CLOSE_S (CLOSE_S + TW.SZ_g_s).

Section close. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range close_wr TF Bw,
   no meter charge (the side-stack frame changes st_fs only), and X: a0 = r (sign-extended), the world relation at the
   model's world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this
   function takes is released. *)
Definition transport_close_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (TF : option TI.tframe) (Bw Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    CLOSE_STK CLOSE_EV 0 (close_wr TF Bw)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 r /\
       tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_diginet_session_close_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 CLOSE_S -> YK11.getr regs 11 = w64 now ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CLOSE_STK -> spZ regs <= sp0 ->
    0 <= now < 2 ^ 64 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.diginet_session_close_m timg_A TF Bw now = Some (Bw', r) ->
    trans_tframe_at B lyc Sc W memc regs CLOSE_STK TF ->
    trans_rom_view_rd W memc ->
    close_apart TF Bw ->
    trans_tf_off_g TF ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    count_cid CLOSE_CID (frames Sc) + 2 < fs_frames CLOSE_CID ->
    st_nev S + k + CLOSE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_close_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw Bw' r).

(* The statement the walk will prove: the class-2 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the record facts that no byte of G and
   no TRANS_RO_RD byte is an owned static or errno (they carry TF's trans_src_ok, G and the TRANS_RO_RD bytes across
   the stack malloc's acall_kept and send_control's acall_kept_g; DgnTransportCg.v G_HARNESS_gx_ok /
   G_HARNESS_gx_noerrno give gx_ok and gx_noerrno from the first two), the allocator, meter and side-stack laws, and
   the contracts of __asan_stack_malloc_2, __asan_memset, notice (at the value the session's notify pointer holds) and
   send_control (pc order of their first call) give the contract at TS_diginet_session_close. *)
Definition transport_diginet_session_close_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) CLOSE_CID = transport_sigma TS___asan_stack_malloc_2 ->
  transport_cells B -> trans_close_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B CLOSE_CID) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  (forall fx' : YK11.FPState, @transport_send_control_cg fx' rc B MT (transport_sigma TS_send_control)) ->
  transport_diginet_session_close_cg (transport_sigma TS_diginet_session_close).
End close.
