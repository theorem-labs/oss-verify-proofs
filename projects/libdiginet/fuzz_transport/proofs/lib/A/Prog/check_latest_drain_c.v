(* check_latest_drain_contract: check_latest_drain (fuzz/fuzz_transport.c:785-802; model lib/TModel/TCb.v
   check_latest_drain_m) on fuzz_transport.asan (e89be137db17), a leaf that scans g_q[0 .. g_nq) for a command that may
   go now (g_cmd[g_q[i]].display = 0, or the display gap passed) and checks it against M's state, in-flight and
   back-off members, and returns nothing. It stores into no harness global, so it takes the leaf form.
   Arguments: none.
   Premises:
   - as the plain contract (lib/Prog/T/check_latest_drain_c.v): the world relation of image A (lib/A/Prog/TWorldG.v
     tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between the memory m, read through csw_view (check_state_wake_c.v),
     and the world Bw; check_latest_drain_m Bw = Some (Bw', tt) (TCb.v:612-631): drain_loop reads g_q[i] only for
     i < CMDS_MAX = 1024 and g_cmd[q].display only for q < CMDS_MAX (else None), and the result is None exactly when
     M.state = S_ONLINE (2), M.fly.on = 0, M.backoff_until <= g_now and a ready command exists; the caller's stack
     below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp) outside the hull [G_HARNESS_LO,
     G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so the frame store does not touch the world;
   - for the instrumented checks of the loads of g_q[i] and g_cmd[q].display (lib/A/AsanCells.v): asan_cells m
     (among others, the 8 bytes at GOT_CELL_K = 0xa4090 hold CELL_K = 0xac9f8 and the 8 bytes at CELL_K hold
     0x7fff8000); both ends of the frame are in application memory (app_mem), so the frame is not a shadow byte;
     GOT_CELL_K 8 and CELL_K 8 are outside the frame (off_stk); the payloads of g_q [0x5f1c00, + 4096) and g_cmd
     [0x5e5400, + 40960) are marked usable in the shadow map (addressable).
   Result: the run returns to ra with every register but a0 .. a7 and t0 .. t3 unchanged (they are not specified:
   the function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack
   below sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world.
   These are the plain contract's post facts (B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 308 code bytes of
   this function are equal in both files): symbol check_latest_drain, value 0x85fdc, size 308 (77 words).
     0x85fdc          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x85fe0          the 8-byte store of ra at sp - 8 (own frame); 0x860f8 loads it back.
     0x85fe4-0x85fe8  a2 = 0x5df160: M (payload 0x5df160, 1648 bytes).
     0x85fec          a0 = the 4-byte load at 0x5df1a8, sign-extended: M.display_sent (A_M_display_sent =
                      OFF_M + 72). No instrumented check precedes the loads of M, g_now, g_cfg and g_nq.
     0x85ff0          a0 = 0 goes to 0x86014: a3 = 0.
     0x85ff8          a1 = the 8-byte load at 0x5df1a0: M.last_display (A_M_last_display = OFF_M + 64).
     0x85ff4, 0x85ffc a0 = the 8-byte load at 0x5df100: g_now (payload 0x5df100, 8 bytes).
     0x86000-0x86004  a3 = the 4-byte load at 0x5df0b0, zero-extended: g_cfg.display_gap_us (g_cfg payload 0x5df080;
                      A_Cfg_display_gap_us = OFF_g_cfg + 48).
     0x86008-0x86010  a0 = a0 - a1 (mod 2^64); a3 = 1 when a0 < a3 (unsigned), else 0; on to 0x86018. So a3 = 1
                      exactly when M.display_sent <> 0 and u64 (g_now - M.last_display) < display_gap_us: a3 is
                      negb allow of the model.
     0x86018-0x8601c  a4 = the 4-byte load at 0x5df960, zero-extended: g_nq (payload 0x5df960, 4 bytes).
     0x86020          a4 = 0 goes to 0x860c4: a1 = 1.
     0x86024-0x86028  a0 = the 8-byte load at GOT_CELL_K = 0xa4090 (.got): CELL_K.
     0x8602c-0x86030  a5 = 0x5f1c00: g_q (payload 0x5f1c00, 4096 bytes).
     0x86034          a6 = the 8-byte load at CELL_K = 0xac9f8: 0x7fff8000.
     0x86038-0x86048  a7 = 1; t0 = 40; t1 = 0x5e5400: g_cmd (payload 0x5e5400, 40960 bytes); a0 = a5.
     0x8604c          the loop, for i = 0, 1, ... with a0 = a5 = 0x5f1c00 + 4 i and a7 = i + 1:
     0x8604c-0x86058    the instrumented check of the 4-byte load at a = 0x5f1c00 + 4 i: a1 = the signed shadow byte
                        k at (a >> 3) + 0x7fff8000; k <> 0 goes to 0x860a0: t2 = (a & 7) + 3; t2 >= k goes to
                        0x8610c, a call of __asan_report_load4 (0x59608, TS___asan_report_load4) with a0 = a (the
                        error path), else back to 0x8605c;
     0x8605c            a1 = the 4-byte load at a, zero-extended: q = g_q[i] (TWorld.v Q_at, OFF_g_q + 4 i);
     0x86060-0x86068    a1 = 0x5e5400 + 40 q + 8: the address of g_cmd[q].display (A_Cmd_display q =
                        OFF_g_cmd + 40 q + 8);
     0x8606c-0x86078    the instrumented check of the 4-byte load at that address b: t2 = the signed shadow byte k at
                        (b >> 3) + 0x7fff8000; k <> 0 goes to 0x860b0: t3 = (b & 7) + 3; t3 < k goes back to
                        0x8607c, else 0x860bc-0x860c0: a0 = b, call of __asan_report_load4;
     0x8607c            a1 = the 4-byte load at b, sign-extended: g_cmd[q].display;
     0x86080-0x86084    a1 = 1 when a1 <> 0, else 0; a1 = a1 & a3: a1 = 1 exactly when the command is not ready
                        (negb (negb (truth display) || allow));
     0x86088            i + 1 >= g_nq (unsigned) goes to 0x860c8;
     0x8608c-0x86094    a0 = a0 + 4, a5 = a5 + 4, a7 = a7 + 1;
     0x86098-0x8609c    a1 = 0 (ready) goes to 0x860c8, else back to 0x8604c.
                      So at 0x860c8 a1 = 0 exactly when drain_loop's ready is true.
     0x860c8          a0 = the 4-byte load at 0x5df16c, sign-extended: M.state (A_M_state = OFF_M + 12).
     0x860cc-0x860d0  a3 = 2; a0 <> 2 goes to 0x860f8 (the return).
     0x860d4-0x860d8  a0 = the 4-byte load at 0x5df1c0, sign-extended: M.fly.on (A_M_fly_on = OFF_M + 96); a0 <> 0
                      goes to 0x860f8.
     0x860dc-0x860e0  a0 = the 8-byte load at 0x5df100: g_now.
     0x860e4          a2 = the 8-byte load at 0x5df198: M.backoff_until (A_M_backoff_until = OFF_M + 56).
     0x860e8-0x860f0  a0 = 1 when g_now < backoff_until (unsigned), else 0; a0 = (a0 | a1) & 1.
     0x860f4          a0 = 0 goes to 0x86104; else 0x860f8-0x86100: ra reloaded, sp = sp + 16, return. This is the
                      one return; on it every register but a0 .. a7, t0 .. t3 is as at entry.
     0x86104          call of __asan_handle_no_return (0x5a4c4, TS___asan_handle_no_return), then 0x86108 call of
                      abort (0x93734): the trap path.
   Error paths and the premise that rules each out:
     - the two calls of __asan_report_load4 (0x8610c for g_q[i], 0x860c0 for g_cmd[q].display) are reached only when
       the signed shadow byte k of the load's address a is not 0 and (a & 7) + 3 >= k. check_latest_drain_m Bw =
       Some _ gives i < 1024 at each load of g_q[i] and q < 1024 at each load of g_cmd[q].display, so the 4 bytes
       lie in the payload of g_q (4 i + 4 <= 4096) or of g_cmd (40 q + 12 <= 40960); both addresses are 4-aligned,
       so the load's last byte a + 3 is in a's granule, and addressable gives k = 0 or (a & 7) + 3 < k <= 7: the
       check passes;
     - the trap path (0x86104 / 0x86108) is reached only when M.state = 2, M.fly.on = 0, g_now >= M.backoff_until
       (unsigned) and a1 = 0 at 0x860c8 (a ready command). By tw_at each loaded value is the world's (TWorldG.v
       tw_read_val, tw_lw, tw_lwu: M_display_sent, M_last_display, g_now, Cfg_display_gap_us, g_nq, Q_at, Cmd_display,
       M_state, M_fly_on, M_backoff_until of Bw), the loop runs drain_loop's iterations (the same exit tests, i < g_nq
       and not ready), and check_latest_drain_m Bw = Some _ rules the trap condition out.
   Callee texts assumed: none (the only callees, __asan_report_load4, __asan_handle_no_return and abort, are on the
   error and trap paths).
   The caller: settle reaches it by a tail jump (0x83cfc, after settle reloads ra and s0 and restores its sp), so ra
   is settle's return address.
   Form: check_state_wake_c.v (the image-A leaf form of the exemplar) with the instrumented-load premises of fuzz_frame's
   image-A diginet_frame_is_keepalive_c.v (asan_cells, app_mem of the frame ends, off_stk and addressable per loaded
   range; here the two payloads the loop reads), and the plain contract's world and model premises, B' = B and the
   world after. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.

Definition CHECK_LATEST_DRAIN : Z := 0x85fdc.
Definition CHECK_LATEST_DRAIN_FRAME : Z := 16.
(* The members of the world the code loads outside the loop, at their global's image-A base plus the member's
   offset in it; the loop reads the payloads of g_q (TA_g_q, TW.SZ_g_q) and g_cmd (TA_g_cmd, TW.SZ_g_cmd). *)
Definition CHECK_LATEST_DRAIN_SENT : Z := TA_M + (TW.A_M_display_sent - TW.OFF_M).
Definition CHECK_LATEST_DRAIN_LAST : Z := TA_M + (TW.A_M_last_display - TW.OFF_M).
Definition CHECK_LATEST_DRAIN_GAP : Z := TA_g_cfg + (TW.A_Cfg_display_gap_us - TW.OFF_g_cfg).
Definition CHECK_LATEST_DRAIN_STATE : Z := TA_M + (TW.A_M_state - TW.OFF_M).
Definition CHECK_LATEST_DRAIN_FLY : Z := TA_M + (TW.A_M_fly_on - TW.OFF_M).
Definition CHECK_LATEST_DRAIN_BACKOFF : Z := TA_M + (TW.A_M_backoff_until - TW.OFF_M).
Lemma check_latest_drain_sent_at : CHECK_LATEST_DRAIN_SENT = 0x5df1a8.
Proof. reflexivity. Qed.
Lemma check_latest_drain_last_at : CHECK_LATEST_DRAIN_LAST = 0x5df1a0.
Proof. reflexivity. Qed.
Lemma check_latest_drain_gap_at : CHECK_LATEST_DRAIN_GAP = 0x5df0b0.
Proof. reflexivity. Qed.
Lemma check_latest_drain_state_at : CHECK_LATEST_DRAIN_STATE = 0x5df16c.
Proof. reflexivity. Qed.
Lemma check_latest_drain_fly_at : CHECK_LATEST_DRAIN_FLY = 0x5df1c0.
Proof. reflexivity. Qed.
Lemma check_latest_drain_backoff_at : CHECK_LATEST_DRAIN_BACKOFF = 0x5df198.
Proof. reflexivity. Qed.
Lemma check_latest_drain_globals_at :
  TA_g_now = 0x5df100 /\ TA_g_nq = 0x5df960 /\ TA_g_q = 0x5f1c00 /\ TW.SZ_g_q = 4096 /\
  TA_g_cmd = 0x5e5400 /\ TW.SZ_g_cmd = 40960.
Proof. repeat split; reflexivity. Qed.

Definition check_latest_drain_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_latest_drain_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_DRAIN_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_DRAIN_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_LATEST_DRAIN_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_LATEST_DRAIN_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_LATEST_DRAIN_FRAME CELL_K 8 ->
    addressable m TA_g_q TW.SZ_g_q ->
    addressable m TA_g_cmd TW.SZ_g_cmd ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_DRAIN_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_DRAIN) fc None m (seg_rom rsegs)).
