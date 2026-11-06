(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module names changed; 358 of its 430 lines of code are new or changed and 371 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickCut.v, with its module paths and module names changed; 203 of its 254 lines of code are new or changed and 379 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_tick_cg.v; 81 of its 139 lines of code are new or changed and 196 lines of the source are left out. *)
(* diginet_session_close_cg: image B's ASan walk contract of diginet_session_close (transport/src/diginet_session.c:
   147-158, with set_state (:79-86) CALLED; model lib/TModel/TSess.v diginet_session_close_m, send_control_m and
   set_state_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x87648 = transportb_sigma TB_diginet_session_close,
   size 316, as STATEMENTS only (no proof). It stores into g_s, a harness global, takes no side-stack frame, calls
   send_control (a G-form callee) and calls set_state (a G-form callee: a function on image B, which image A inlines
   here; set_state_cg.v takes the class-2 frame for the struct diginet_notice and calls notice), so it is a G-form
   caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx (image-free) over G =
   lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v
   transport_cg_post (image-free; acall_kept_g over G_HARNESS_B). Form: image A's lib/A/Prog/diginet_session_close_cg.v
   at image B's names; the G walk with no side-stack frame of its own that calls set_state is image B's
   maybe_online_cg.v; the call of send_control with kp = klp = 0 is send_control_cg.v's second caller. The
   differences are listed at the end of this comment.

   The contract. a0 = s = &g_s = 0x5df640 (TWorldB.v TB_g_s), a1 = now (uint64_t, which the code does not read). TF is
   the current heap frame (check_state_data_cg.v trans_tframe_at at this call's window); the read-only bytes the
   callees' callees read are the image's (trans_rom_view_rd). The memory relates to the world Bw by image B's world
   relation (TWorldG.v tw_at at TWorldB.v TMAP_B, read through aview), g_fail_next Bw <= 1, and
   diginet_session_close_m timg_B TF Bw now = Some (Bw', r). No byte the call stores is a byte of TF (close_apart),
   and no byte of TF is a byte of G (trans_tf_off_g). Class 2 of the side stack has two free frames (send_control's
   and diginet_body_check's inside diginet_frame_build inside send_control; set_state's is taken after they are
   released). The function returns to ra with a0 = r (sign-extended), the callee-saved registers kept, no allocator
   event and no meter charge (the callees' side-stack frames change the state's st_fs only), the callees' side-stack
   frames released (the caller's frames exactly), the caller's blocks exactly, the bytes acall_kept_g G_HARNESS_B
   keeps (the bytes at or above alloc_ceiling outside the call's stack window [sp - CLOSE_STK, sp), the image bytes
   outside G, the owned statics and errno, the caller's block and frame bytes outside close_wr TF Bw), the world
   relation at Bw', and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/U/Prog/T/diginet_session_close_c.v): a0 =
   W_BASE_UBSAN + OFF_g_s -> a0 = TB_g_s; a1 = now with 0 <= now < 2 ^ 64, kept; wmem -> tw_at; g_fail_next B <= 1
   kept as a premise (send_control's and set_state's statements ask it), and the post's g_fail_next B' <= 1 kept in X
   (set_state's X gives it; the code neither reads nor writes g_fail_next); diginet_session_close_m verbatim at
   timg_B (timg_ubsan -> timg_B); tframe_at -> trans_tframe_at at CLOSE_STK, and its off_world clause (TF lies
   outside the plain world [W_BASE_UBSAN, W_BASE_UBSAN + W_LEN), which on image B is G, lib/U/Prog/T/TContract.v
   tframe_at) -> two facts, since check_state_data_cg.v trans_tframe_at drops that clause: close_apart, no byte the
   call stores is a byte of TF (set_state_cg.v sstate_apart's form), and trans_tf_off_g (check_state_data_cg.v), no
   byte of TF is a byte of G. trans_tf_off_g is what carries TF across send_control, which writes G (tx_frames and
   io_send's fields), to set_state, which reads it (its notice's callees): acall_kept_g keeps the image bytes OUTSIDE
   G, the caller's block, frame and stack bytes outside the written range, and says nothing of a byte of G, while
   send_control's X pins G only to the model world B1. With trans_tf_off_g, TF is block, frame or stack memory, or
   read-only data, outside sendctl_wr 0 0 (close_apart), so the block, frame, stack and image clauses of acall_kept_g
   keep its bytes and its frames' shadow (the read-only case through trans_ro_rd_scoped), and its placement follows
   clause by clause (DgnTransportBCg.v trans_src_ok_kept; trans_src_ok_acall_g itself asks every byte of G to be
   kept, which send_control does not give); relro_img -> trans_rom_view_rd; stk, lo + FRAME <= sp, sp mod 16 and
   w_off_stack -> the journal's window premises; mem_inv is dropped. The post's munch, wmono, stk and mem_inv ->
   transport_cg_post (the journal at the return, acall_kept_g over close_wr TF Bw); wmem -> X's tw_at.

   Premises the plain contract does not have:
   - count_cid 2 (frames Sc) + 1 < fs_frames 2: send_control's statement asks count_cid 2 + 1 < fs_frames 2 at its
     call state (its own class-2 frame, then diginet_body_check's inside diginet_frame_build), whose frames are
     frames Sc (close takes no side-stack frame); set_state's statement asks count_cid 2 < fs_frames 2 at its call
     state, whose frames are again frames Sc (send_control's post releases its frames).
   - close_apart and trans_tf_off_g (above; both translate the plain tframe_at's off_world clause).
   (The plain contract's relro_img is translated above as trans_rom_view_rd W memc: send_control's and set_state's
     premise.)
   - in the holds statement: trans_close_cells (g_s's zero shadow), gx_ok (the store at s + 212, a byte of G, in the
     G journal), and trans_ro_rd_unowned and trans_rom_no_errno: they carry TF's trans_src_ok (inside
     trans_tframe_at) across send_control's acall_kept_g when TF is read-only data (trans_ro_rd_scoped; the image
     clause keeps no owned-static or errno byte), and the TRANS_RO_RD bytes across it (trans_rom_view_rd for
     set_state); maybe_online_cg.v's form for a walk with no side-stack frame of its own.
   Run invariants carried (on its own Bw): (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME and (4)
   every PENDING command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX, both send_control_cg.v's premises.
   diginet_session_close_m calls send_control_m at Bw itself (the loads at s + 116, s + 136 and s + 112 before it
   store nothing), so both carry verbatim. set_state carries none (its notice has kind N_STATE, so notice's N_DATA
   premise holds vacuously: set_state_cg.v). The others (check_latest_queue's, take's cfg bound) are not reached from
   diginet_session_close. Its own accesses are at fixed offsets of g_s (s + 112 .. s + 139, s + 212 .. s + 215), so
   its code needs no bound that the model does not give.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 316 code bytes are equal in both files), 79 words:
     0x87648 - 0x87658 sp = sp - 32; ra at sp + 24, s0 at sp + 16, s1 at sp + 8, s2 at sp + 0, loaded back at
                      0x87708 - 0x87714. No side-stack frame, no realignment, no frame pointer.
     0x8765c          s = 0 goes to 0x87700 (s1 = -1, DIGINET_E_ARG, :150-151); not taken: s = TB_g_s <> 0.
     0x87660 - 0x87668 s0 = s; s & 7 <> 0 (the UBSan alignment check of struct diginet_session *s) goes to the trap
                      word at 0x87740.
     0x8766c - 0x87674 a0 = the 8-byte load of the GOT word 0xa3cf0 (it holds 0xac678), s2 = the 8-byte load at
                      0xac678 (0x7fff8000, the shadow base): transport_cells rows 1-2.
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on.
     0x87678 - 0x87688, 0x87744 - 0x87750 the check of the 4-byte load at s + 116.
     0x8768c - 0x87690 the 4-byte signed load at s + 116 (S_desk_known Bw) = 0 goes to 0x876d0 (:153).
     0x87694 - 0x876a4, 0x87764 - 0x87770 the check of the 4-byte load at s + 136.
     0x876a8 - 0x876ac the load (S_foreign Bw) <> 0 goes to 0x876d0.
     0x876b0 - 0x876c0, 0x87774 - 0x87780 the check of the 4-byte load at s + 112.
     0x876c4 - 0x876cc the load (S_state Bw) <> 3 (S_CLOSED) goes to 0x87720; = 3 falls to 0x876d0. Past these tests,
                      close_go Bw holds exactly on the path to 0x87720.
     0x87720 - 0x8773c a1 = 0xe3 (DIGINET_CMD_DISCONNECT), a0 = s, a2 = a3 = a4 = 0; the call of send_control
                      (0x86ed4 = transportb_sigma TB_send_control) at 0x87734, return address 0x87738 (:154); s1 = its
                      a0 (r); to 0x876d4.
     0x876d0          s1 = 0 (r = 0, :152, when close_go Bw is false).
     0x876d4 - 0x876e8, 0x87754 - 0x87760 the check of the 4-byte store at s + 212, then the store of 0 there
                      (S_inflight, :155) at 0x876e8. The world is now close_w1 B1, B1 = send_control's world, or Bw
                      when close_go Bw is false.
     0x876ec - 0x876f8 a1 = 3 (S_CLOSED), a2 = 8 (R_CLOSED), a0 = s; the call of set_state (0x872cc = transportb_sigma
                      TB_set_state) at 0x876f8, return address 0x876fc (:156); to 0x87704.
     0x87700          s1 = -1 (the s = 0 path; not taken).
     0x87704 - 0x8771c a0 = s1 (r); ra, s0, s1, s2 loaded back, sp = sp + 32, return. a1 .. a7 at the return are not
                      stated.
     0x87740          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path.
     0x87744 - 0x87780 the slow paths of the checks and the 4 error calls.
   No tail jump: the calls are jal with link (send_control, set_state, and the 4 error-path calls); every j is inside
   the function, and the function's own return is the ret at 0x8771c.
   The model and the code: the three tests at 0x87690, 0x876ac and 0x876cc are close_go (S_desk_known Bw against 0,
   S_foreign Bw against 0, S_state Bw against S_CLOSED, each a 32-bit signed read); the call of send_control is
   send_control_m at Bw with cmd 0xe3 and ack 0, and its a0 is r (close_sent), kept in the callee-saved s1 across
   set_state; the store at s + 212 is set_S_inflight (put 4 of 0) at B1, a tw_write inside g_s's payload; the call of
   set_state is set_state_m at close_w1 B1 with S_CLOSED and R_CLOSED (close_model), whose steps are close_w2 and
   close_ntc (close_sstate) and whose test of S_state (close_w1 B1) against S_CLOSED is set_state's own (its
   0x8741c). The model's None cases are send_control_m's (send_control_cg.v) and set_state_m's (call_notify's and
   notice's, inside set_state_cg.v), all ruled out by the model premise; the code's one trap branch is ruled out by
   the constant s, a fact outside the model.
   Trap path (the unimp word at 0x87740, from 1 branch) and the fact that refutes it: 0x87668 (s & 7 <> 0): s =
   0x5df640, a multiple of 8.
   Error paths (4 calls; no abort) and the facts that rule them out:
     __asan_report_load4 (0x59644) at 0x87750 (s + 116), 0x87770 (s + 136), 0x87780 (s + 112);
     __asan_report_store4 (0x59964) at 0x87760 (s + 212).
     Each guards a naturally aligned access inside g_s's payload [0x5df640, 0x5e3d98) (2283 whole granules), whose
     shadow bytes are 0 (trans_close_cells, read at each AR state by DgnTransportBCg.v decode_zshadow_rd), so k = 0.
   Writes: g_s's inflight (bytes of G); its own machine frame (the four saves at sp - 32 .. sp - 1); send_control's
   stores (send_control_cg.v sendctl_wr 0 0: tx_frames and io_send's iosend_wr 60, bytes of G); set_state's stores
   (set_state_cg.v sstate_wr (close_w1 B1) S_CLOSED R_CLOSED: g_s's state and notice's N_STATE stores, bytes of G,
   when the state changes; its own frames). No byte of a caller's frame or block is written, so close_wr (A's text;
   close_wr_sstate reads its last row as set_state's range) is the written range. The G kit: the store at s + 212 a G
   byte (transport_twr_ok_g's inG case, gx_ok), the four saves window bytes, and send_control's and set_state's
   acall_kept_g at their call states, whose frames are frames Sc (TransportGCg.v dk_kept_trans_nf_g).
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     set_state as set_state_cg.v transport_set_state_cg at transportb_sigma TB_set_state (call at 0x876f8; a G-form
       callee composed in the same G journal, no gx_call_cg):
       the journal at the call state; ra = 0x876fc (ret_ok, 4096 <= ra); gp, tp kept; a0 = SSTATE_S = s, a1 = st = 3
         (S_CLOSED), a2 = why = 8 (R_CLOSED), 0 <= st, why < 2 ^ 31;
       sp' = sp - 32, 16-aligned; sp0 - STK <= sp' - SSTATE_STK: CLOSE_STK = 32 + SENDCTL_STK >= 32 + SSTATE_STK
         (close_stk_eq); sp' <= sp0;
       tw_at at close_w1 B1: tw_at at B1 (send_control's X, or the entry's tw_at at Bw when close_go Bw is false: the
         loads change no byte), then the tw_write of the store at s + 212; g_fail_next (close_w1 B1) <= 1
         (send_control's X, or the premise; the store does not touch the byte);
       set_state_m timg_B TF (close_w1 B1) S_CLOSED R_CLOSED = Some (Bw', tt): the model premise through close_model
         (close_sent's branch on this path);
       trans_tframe_at TF at SSTATE_STK: the entry's trans_tframe_at at CLOSE_STK, carried: across send_control
         (trans_src_ok_kept over the clauses of its acall_kept_g, which reach TF because trans_tf_off_g puts it outside
         G and close_apart outside sendctl_wr 0 0), across the store at s + 212 (close_apart); set_state's window lies
         inside this call's;
       trans_rom_view_rd at the call memory: send_control's acall_kept_g keeps every TRANS_RO_RD byte
         (trans_ro_rd_scoped, from trans_ro_rd_unowned and trans_rom_no_errno: its image clause keeps the image bytes
         outside G, the owned statics and errno), and the store at s + 212 is a byte of G, not a read-only byte;
       sstate_apart TF (close_w1 B1) S_CLOSED R_CLOSED: close_apart, since sstate_wr (close_w1 B1) S_CLOSED R_CLOSED
         is close_wr TF Bw's last row at B1 (close_wr_sstate);
       count_cid SSTATE_CID at the call state = count_cid 2 (frames Sc) < fs_frames 2 (the count premise;
         send_control's post states frames S2 = frames Sc);
       st_nev S + k + SSTATE_EV <= EV_MAX: the event count after send_control plus SSTATE_EV, inside CLOSE_EV.
       Its X: tw_at at Bw' and g_fail_next Bw' <= 1.
     send_control as send_control_cg.v transport_send_control_cg at transportb_sigma TB_send_control (call at
       0x87734, when close_go Bw holds; a G-form callee composed in the same G journal, no gx_call_cg):
       the journal at the call state; ra = 0x87738; gp, tp kept; a0 = SENDCTL_S = s, a1 = cmd = 0xe3
         (0 <= cmd < 2 ^ 8), a2 = bv_swrap 32 0 = 0 (ack = 0, 0 <= ack < 2 ^ 32), a3 = kp = 0, a4 = klp = 0 (the keep
         disjunction's left side);
       sp' = sp - 32, 16-aligned; sp0 - STK <= sp' - SENDCTL_STK (CLOSE_STK = 32 + SENDCTL_STK, close_stk_eq);
         sp' <= sp0;
       tw_at at Bw (no store before the call); g_fail_next Bw <= 1 (the premise);
       send_control_m timg_B TF Bw 0xe3 0 = Some (B1, (r, f)): close_sent's first branch (close_model);
       trans_rom_view_rd at the call memory (the entry's: no store before the call);
       run invariants (1) and (4): the premises, at the same Bw;
       count_cid 2 at the call state = count_cid 2 (frames Sc), and + 1 < fs_frames 2 is the count premise;
       st_nev S + k + SENDCTL_EV <= EV_MAX (CLOSE_EV = SENDCTL_EV + SSTATE_EV).
       Its post is transport_cg_post_out with sendctl_outs 0 0 = [] (TransportGCg.v transport_cg_post_out_nil), and its
       X gives a0 = r, tw_at at B1 and g_fail_next B1 <= 1.
   send_control's and set_state's own record facts (the stack-malloc entries, the side-stack laws, their cells,
   gx_noerrno) are premises of their holds statements, not of this one.
   Stack: 32 bytes of its own, no realignment; every call runs from sp - 32, and the largest callee window is
   send_control's SENDCTL_STK (set_state's SSTATE_STK is smaller): CLOSE_STK = 32 + SENDCTL_STK (close_stk_eq).

   The caller: LLVMFuzzerTestOneInput at 0x81b9c (return address 0x81ba0), the operation that closes the session. Its
   inlined copy of the harness's m_close runs first: the three tests at 0x81b4c - 0x81b60 (M.desk_known, M.foreign,
   and M.state against 3); on their path the stores of OW.e3 + 1 and M.fail = 0 (0x81b64 - 0x81b78); M.fly.on = 0
   (0x81b7c); then the call of m_set at 0x81b88 (a0 = 3, a1 = 8). Then a0 = 0x5df640 (&g_s, formed at
   0x81b94 - 0x81b98) and a1 = the 8-byte load at 0x81b90 (g_now, at 0x5de6f4 + 0x68c, the base held at its s1 + 0x98).
   It supplies its G journal, tw_at, g_fail_next, the model premise (its call of diginet_session_close_m),
   trans_tframe_at, close_apart and trans_tf_off_g of its TF (all three vacuous there), trans_rom_view_rd, the two
   run invariants, and the class-2 count: it holds a class-2 side-stack frame of its own while it calls
   (__asan_stack_malloc_2 at 0x81310, a0 = 256), so its statement must leave room for two more class-2 frames below
   it.

   Against image A's statement (lib/A/Prog/diginet_session_close_cg.v): the same definitions (close_go, close_sent,
   close_w1, close_w2, close_ntc, close_model, close_setstate, close_wr, close_apart), premises (but the count, below)
   and post, at image B's names (TMAP_B, timg_B, TB_g_s, transportb_sigma, G_HARNESS_B, lib/B/Prog/DgnTransportBCg.v,
   lib/B/Prog/m_set_cg.v twb_fld, lib/B/Prog/check_state_data_cg.v trans_tf_off_g). What image B's code forces:
   (1) set_state is a function, called at 0x876f8, where image A's diginet_session_close inlines it (its own 160-byte
   frame, realignment, class-2 stack malloc, memset, notice call and release): close takes no side-stack frame and
   has a 32-byte frame with no realignment, so the holds statement takes set_state's contract in place of the
   contracts of __asan_stack_malloc_2, __asan_memset and notice, and of the side-stack laws (pc_stack_malloc,
   ameter_fs_laws, stack_malloc_progressP, astack_free_law, frame_flag_lawP) and of the record facts only the stack
   malloc's acall_kept needs (trans_g_unowned and trans_g_no_errno, which gave gx_ok and gx_noerrno; gx_ok is now a
   premise of its own, as in maybe_online_cg.v); CLOSE_STK = 32 + Z.max SENDCTL_STK SSTATE_STK (image A: 176 +
   Z.max ESTACK (Z.max NOTICE_STK SENDCTL_STK)), CLOSE_EV = SENDCTL_EV + SSTATE_EV (image A: SENDCTL_EV + NOTICE_EV),
   CLOSE_CID is the class send_control's and set_state's frames take (image A: its own frame's class, the same 2);
   the count premise is count_cid 2 (frames Sc) + 1 < fs_frames 2, one frame weaker than image A's + 2, which counts
   close's own class-2 frame; close_addrs names four fields (s + 96 and s + 104, the notify loads, are set_state's on
   image B); two lemmas read A's definitions as set_state's (close_sstate, close_wr_sstate). (2) One UBSan branch to
   the trap word 0x87740 (the alignment check of s), refuted by the constant s, a fact image A's form already has.
   (3) 4 error calls of its own (image A's 8 include the notify loads' and the state store's checks and set_state's
   reload of the state, which on image B are set_state's). No premise of the contract is added; the holds statement's
   callee contracts and laws change as (1) says. *)
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

(* diginet_session_close's frame (`sp = sp - 32` at TB_diginet_session_close; no realignment), and the largest stack a
   callee uses below sp - 32: send_control's SENDCTL_STK, set_state's SSTATE_STK. *)
Definition CLOSE_FRAME : Z := 32.
Definition CLOSE_STK : Z := CLOSE_FRAME + Z.max SENDCTL_STK SSTATE_STK.
Lemma close_stk_eq : CLOSE_STK = CLOSE_FRAME + SENDCTL_STK.
Proof. reflexivity. Qed.
(* No allocator event: send_control and set_state record none, and close takes no side-stack frame. *)
Definition CLOSE_EV : Z := SENDCTL_EV + SSTATE_EV.
(* The side-stack class of the frames the callees take (send_control's a0 = 160 at 0x86f48 and set_state's a0 = 160
   at 0x8733c, each a call of __asan_stack_malloc_2) and of diginet_body_check's frame inside diginet_frame_build
   inside send_control, hence the + 1 of the count premise. *)
Definition CLOSE_CID : Z := SENDCTL_CID.
Lemma close_cid_sendctl : CLOSE_CID = SENDCTL_CID /\ CLOSE_CID = SSTATE_CID /\ CLOSE_CID = 2.
Proof. repeat split; reflexivity. Qed.
(* Its first argument: g_s's base in image B. *)
Definition CLOSE_S : Z := TB_g_s.
(* The addresses of the four g_s fields the code reads or writes (s + 116, s + 136, s + 112, s + 212); s + 96 and
   s + 104 (notify) are set_state's. *)
Lemma close_addrs :
  CLOSE_S = 0x5df640 /\ CLOSE_S = SENDCTL_S /\ CLOSE_S = SSTATE_S /\
  CLOSE_S + (TW.A_S_desk_known - TW.OFF_g_s) = 0x5df6b4 /\
  CLOSE_S + (TW.A_S_foreign - TW.OFF_g_s) = 0x5df6c8 /\
  CLOSE_S + (TW.A_S_state - TW.OFF_g_s) = 0x5df6b0 /\
  CLOSE_S + (TW.A_S_inflight - TW.OFF_g_s) = 0x5df714.
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
(* Image B's code makes the set_state_m step a call of set_state at close_w1 B1 (st = S_CLOSED, why = R_CLOSED),
   whose steps are close_w2 and close_ntc. *)
Lemma close_sstate : forall (B1 : list byte),
  close_w2 B1 = sstate_w (close_w1 B1) TS0.DIGINET_S_CLOSED /\
  close_ntc B1 = sstate_ntc (close_w1 B1) TS0.DIGINET_S_CLOSED TS0.DIGINET_R_CLOSED.
Proof. intros B1. split; reflexivity. Qed.

(* The bytes the code stores outside its own frames, exactly, by path: send_control's (send_control_cg.v sendctl_wr
   with kp = klp = 0: g_s.stats.tx_frames and io_send's iosend_wr 60) when close_go Bw holds; g_s's inflight (4
   bytes); and, when the state of close_w1 B1 is not S_CLOSED, g_s's state (4 bytes) and notice's stores at the world
   close_w2 B1 (notice_cg.v notice_wr: for an N_STATE notice, GOT.t[GOT.n] when 0 <= GOT.n < TRANS_MAX, and GOT.n). *)
Definition close_wr (F : option TI.tframe) (Bw : list byte) (a : Z) : Prop :=
  (close_go Bw = true /\ sendctl_wr 0 0 a) \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight 4 a \/
  (exists B1 r, close_sent timg_B F Bw = Some (B1, r) /\ TW.S_state (close_w1 B1) <> TS0.DIGINET_S_CLOSED /\
     (twb_fld TW.OFF_g_s TB_g_s TW.A_S_state 4 a \/ notice_wr (close_w2 B1) (close_ntc B1) a)).
(* The same range as image B's code makes it: send_control's, the store at s + 212, then set_state's written range at
   the world of its call. *)
Lemma close_wr_sstate : forall (F : option TI.tframe) (Bw : list byte) (a : Z),
  close_wr F Bw a <->
  (close_go Bw = true /\ sendctl_wr 0 0 a) \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight 4 a \/
  (exists B1 r, close_sent timg_B F Bw = Some (B1, r) /\
     sstate_wr (close_w1 B1) TS0.DIGINET_S_CLOSED TS0.DIGINET_R_CLOSED a).
Proof. intros F Bw a. split; intros H; exact H. Qed.

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. set_state reads TF (its notice's callees) after send_control's stores and the store at s + 212
   (set_state_cg.v sstate_apart). *)
Definition close_apart (Fr : option TI.tframe) (Bw : list byte) : Prop :=
  forall x, close_wr Fr Bw x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow
   (lib/B/YF0m.v Tfib_zero_shadow row (0x5df640, 0x5e3d98 - 0x5df640)). The instrumented checks of the accesses at
   s + 112 .. s + 139 and s + 212 .. s + 215 read it. *)
Definition trans_close_cells (B : asyms) : Prop := decode_zshadow_at B CLOSE_S (CLOSE_S + TW.SZ_g_s).

Section close. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   close_wr TF Bw, no meter charge (the callees' side-stack frames change st_fs only), and X: a0 = r (sign-extended),
   the world relation at the model's world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 =
   frames Sc: the frames the callees take are released. *)
Definition transport_close_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (TF : option TI.tframe) (Bw Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs CLOSE_STK CLOSE_EV 0 (close_wr TF Bw)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 r /\
       tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_diginet_session_close_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 CLOSE_S -> YK11.getr regs 11 = w64 now ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CLOSE_STK -> spZ regs <= sp0 ->
    0 <= now < 2 ^ 64 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.diginet_session_close_m timg_B TF Bw now = Some (Bw', r) ->
    trans_tframe_at B lyc Sc W memc regs CLOSE_STK TF ->
    trans_rom_view_rd W memc ->
    close_apart TF Bw ->
    trans_tf_off_g TF ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    count_cid CLOSE_CID (frames Sc) + 1 < fs_frames CLOSE_CID ->
    st_nev S + k + CLOSE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_close_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw Bw' r).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of g_s's
   payload, the record facts that no TRANS_RO_RD byte is an owned static or errno (they carry TF's trans_src_ok and
   the TRANS_RO_RD bytes across send_control's acall_kept_g: DgnTransportBCg.v trans_ro_rd_scoped), the allocator and
   meter laws, G inside the image and outside the allocator's statics, and the contracts of set_state and send_control
   (pc order of their first call) give the contract at TB_diginet_session_close. *)
Definition transport_diginet_session_close_cg_holds_stmt : Prop :=
  transport_cells B -> trans_close_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) ->
  (forall fx' : YK11.FPState, @transport_send_control_cg fx' rc B MT (transportb_sigma TB_send_control)) ->
  transport_diginet_session_close_cg (transportb_sigma TB_diginet_session_close).
End close.
