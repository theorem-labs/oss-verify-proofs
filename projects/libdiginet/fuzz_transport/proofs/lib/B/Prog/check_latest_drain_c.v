(* check_latest_drain_contract: check_latest_drain (fuzz/fuzz_transport.c:785-802; model lib/TModel/TCb.v
   check_latest_drain_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that scans g_q[0 .. g_nq) for a command
   that may go now (g_cmd[g_q[i]].display = 0, or the display gap passed) and checks it against M's state, in-flight
   and back-off members, and returns nothing. It stores into no harness global, so it takes the leaf form.
   Arguments: none.
   Premises:
   - as the plain contract (lib/Prog/T/check_latest_drain_c.v): the world relation of image B (lib/A/Prog/TWorldG.v
     tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between the memory m, read through csw_view (check_state_wake_c.v),
     and the world Bw; check_latest_drain_m Bw = Some (Bw', tt) (TCb.v:612-631): drain_loop reads g_q[i] only for
     i < CMDS_MAX = 1024 and g_cmd[q].display only for q < CMDS_MAX (else None), and the result is None exactly when
     M.state = S_ONLINE (2), M.fly.on = 0, M.backoff_until <= g_now and a ready command exists; the caller's stack
     below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp) outside the hull [G_HARNESS_B_LO,
     G_HARNESS_B_HI) of the 18 harness globals (lib/B/TransportGB.v), so the frame store does not touch the world;
   - for the instrumented checks of the loads of g_q[i] and g_cmd[q].display (lib/B/AsanCells.v): asan_cells m
     (among others, the 8 bytes at GOT_CELL_K = 0xa3cf0 hold CELL_K = 0xac678 and the 8 bytes at CELL_K hold
     0x7fff8000); both ends of the frame are in application memory (app_mem), so the frame is not a shadow byte;
     GOT_CELL_K 8 and CELL_K 8 are outside the frame (off_stk); the payloads of g_q [0x5f1880, + 4096) and g_cmd
     [0x5e5080, + 40960) are marked usable in the shadow map (addressable).
   Result: the run returns to ra with every register but a0 .. a7 and t0 .. t6 unchanged (they are not specified:
   the function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack
   below sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world.
   These are the plain contract's post facts (B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 340 code bytes of this function are equal in both files):
   symbol check_latest_drain, value 0x862b8, size 340 (85 words).
     0x862b8          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x862bc          the 8-byte store of ra at sp - 8 (own frame); 0x863ec loads it back.
     0x862c0-0x862c4  a2 = 0x5dede0: M (payload 0x5dede0 = TB_M, 1648 bytes).
     0x862c8          a0 = the 4-byte load at 0x5dee28, sign-extended: M.display_sent (A_M_display_sent =
                      OFF_M + 72). No instrumented check precedes the loads of M, g_now, g_cfg and g_nq.
     0x862cc          a0 = 0 goes to 0x862f0: a3 = 0.
     0x862d4          a1 = the 8-byte load at 0x5dee20: M.last_display (A_M_last_display = OFF_M + 64).
     0x862d0, 0x862d8 a0 = the 8-byte load at 0x5ded80: g_now (payload 0x5ded80 = TB_g_now, 8 bytes).
     0x862dc-0x862e0  a3 = the 4-byte load at 0x5ded30, zero-extended: g_cfg.display_gap_us (g_cfg payload 0x5ded00
                      = TB_g_cfg; A_Cfg_display_gap_us = OFF_g_cfg + 48).
     0x862e4-0x862ec  a0 = a0 - a1 (mod 2^64); a3 = 1 when a0 < a3 (unsigned), else 0; on to 0x862f4. So a3 = 1
                      exactly when M.display_sent <> 0 and u64 (g_now - M.last_display) < display_gap_us: a3 is
                      negb allow of the model.
     0x862f4-0x862f8  a4 = the 4-byte load at 0x5df5e0, zero-extended: g_nq (payload 0x5df5e0 = TB_g_nq, 4 bytes).
     0x862fc          a4 = 0 goes to 0x863b8: a1 = 1.
     0x86300-0x8630c  a0 = the 8-byte load at GOT_CELL_K = 0xa3cf0 (.got): CELL_K; a5 = 1; a1 = 0x5f1308.
     0x86310-0x86318  a6 = 1025; a7 = 1023; t0 = 0x5f1880: g_q (payload 0x5f1880 = TB_g_q, 4096 bytes).
     0x8631c          t1 = the 8-byte load at CELL_K = 0xac678: 0x7fff8000.
     0x86320-0x86330  t2 = 40; t3 = 0x5e5080: g_cmd (payload 0x5e5080 = TB_g_cmd, 40960 bytes); t4 = not t3 =
                      2^64 - 1 - 0x5e5080; a0 = t0.
     0x86334          the loop, for i = 0, 1, ... with a0 = t0 = 0x5f1880 + 4 i and a5 = i + 1:
     0x86334            a5 = 1025 (i = 1024) goes to 0x863f8 (the UBSan trap: the bounds check of g_q[i]);
     0x86338-0x86344    the instrumented check of the 4-byte load at a = 0x5f1880 + 4 i: a1 = the signed shadow
                        byte k at (a >> 3) + 0x7fff8000; k <> 0 goes to 0x86394: t5 = (a & 7) + 3; t5 >= k goes to
                        0x86408, a call of __asan_report_load4 (0x59644, TB___asan_report_load4) with a0 = a (the
                        error path), else 0x863a0 goes back to 0x86348;
     0x86348            a1 = the 4-byte load at a, sign-extended: q = g_q[i] (TWorld.v Q_at, OFF_g_q + 4 i);
     0x8634c            a1 > 1023 (unsigned) goes to 0x863f8 (the UBSan trap: the bounds check of g_cmd[q]);
     0x86350-0x86354    a1 = 40 q; a1 > t4 (unsigned), so 0x5e5080 + 40 q >= 2^64, goes to 0x863f8 (the UBSan
                        trap: the pointer-overflow check);
     0x86358-0x8635c    a1 = 0x5e5080 + 40 q + 8: the address of g_cmd[q].display (A_Cmd_display q =
                        OFF_g_cmd + 40 q + 8);
     0x86360-0x8636c    the instrumented check of the 4-byte load at that address b: t5 = the signed shadow byte k at
                        (b >> 3) + 0x7fff8000; k <> 0 goes to 0x863a4: t6 = (b & 7) + 3; t6 < k goes back to
                        0x86370, else 0x863b0-0x863b4: a0 = b, call of __asan_report_load4;
     0x86370            a1 = the 4-byte load at b, sign-extended: g_cmd[q].display;
     0x86374-0x86378    a1 = 1 when a1 <> 0, else 0; a1 = a1 & a3: a1 = 1 exactly when the command is not ready
                        (negb (negb (truth display) || allow));
     0x8637c            i + 1 >= g_nq (unsigned) goes to 0x863bc;
     0x86380-0x86388    a5 = a5 + 1, a0 = a0 + 4, t0 = t0 + 4;
     0x8638c-0x86390    a1 <> 0 (not ready) goes back to 0x86334, else to 0x863bc.
                      So at 0x863bc a1 = 0 exactly when drain_loop's ready is true.
     0x863bc          a0 = the 4-byte load at 0x5dedec, sign-extended: M.state (A_M_state = OFF_M + 12).
     0x863c0-0x863c4  a3 = 2; a0 <> 2 goes to 0x863ec (the return).
     0x863c8-0x863cc  a0 = the 4-byte load at 0x5dee40, sign-extended: M.fly.on (A_M_fly_on = OFF_M + 96); a0 <> 0
                      goes to 0x863ec.
     0x863d0-0x863d4  a0 = the 8-byte load at 0x5ded80: g_now.
     0x863d8          a2 = the 8-byte load at 0x5dee18: M.backoff_until (A_M_backoff_until = OFF_M + 56).
     0x863dc-0x863e4  a0 = 1 when g_now < backoff_until (unsigned), else 0; a0 = (a0 | a1) & 1.
     0x863e8          a0 = 0 goes to 0x863fc; else 0x863ec-0x863f4: ra reloaded, sp = sp + 16, return. This is the
                      one return; on it every register but a0 .. a7, t0 .. t6 is as at entry.
     0x863f8          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the UBSan trap path of the three checks (UBSan in trapping mode: no __ubsan_handle_*
                      call).
     0x863fc          call of __asan_handle_no_return (0x5a500, TB___asan_handle_no_return), then 0x86400 call of
                      abort (0x93390), then 0x86404 the word 0xc0001073 (unimp), reached only if abort returns: the
                      trap path.
   Against image A's code (lib/A/Prog/check_latest_drain_c.v, 77 words): the code before the loop and after it
   (0x862b8-0x862fc and 0x863b8-0x863f4, 0x863fc-0x86400) is image A's, instruction for instruction, with image B's
   auipc / load / branch / jal immediates. The loop and its set-up differ: image B keeps i + 1 in a5 and the address
   of g_q[i] in a0 and t0 (image A: a7, and a0 and a5), the shadow offset in t1, 40 in t2 and g_cmd in t3 (image A:
   a6, t0, t1); it adds three UBSan checks (0x86334, 0x8634c, 0x86354, each to the unimp word at 0x863f8) with their
   bounds in a6 = 1025, a7 = 1023 and t4 = not g_cmd (0x8632c); its shadow checks use t5 and t6 where image A's use
   t2 and t3; it loads g_q[i] sign-extended (lw at 0x86348; image A: lwu). Image B's code has the two unimp words
   0x863f8 and 0x86404 that image A's code does not have. The post therefore leaves t4, t5 and t6 unspecified too
   (image A's post: a0 .. a7, t0 .. t3).
   Error paths and the premise that rules each out:
     - the two calls of __asan_report_load4 (0x86408 for g_q[i], 0x863b4 for g_cmd[q].display) are reached only when
       the signed shadow byte k of the load's address a is not 0 and (a & 7) + 3 >= k. check_latest_drain_m Bw =
       Some _ gives i < 1024 at each load of g_q[i] and q < 1024 at each load of g_cmd[q].display, so the 4 bytes
       lie in the payload of g_q (4 i + 4 <= 4096) or of g_cmd (40 q + 12 <= 40960); both addresses are 4-aligned,
       so the load's last byte a + 3 is in a's granule, and addressable gives k = 0 or (a & 7) + 3 < k <= 7: the
       check passes;
     - the UBSan trap at 0x863f8 is reached only from 0x86334 (i = 1024 at the loop's head), 0x8634c (q > 1023) or
       0x86354 (0x5e5080 + 40 q >= 2^64). The loop's head runs only when i < g_nq and the command before was not
       ready (drain_loop's test), and there check_latest_drain_m Bw = Some _ gives i < 1024 (drain_loop: CMDS_MAX
       <= i gives None). The loaded q is Q_at Bw i < 2^32 by tw_at, so the sign-extended register is q or
       q - 2^32 (as 64 bits: >= 2^64 - 2^31, above 1023); Some _ gives q < 1024 (drain_loop: CMDS_MAX <= q gives
       None), so the register is q <= 1023 and the branch at 0x8634c falls through. Then 40 q <= 40920 <
       2^64 - 1 - 0x5e5080 and the branch at 0x86354 falls through;
     - the trap path (0x863fc / 0x86400 / 0x86404) is reached only when M.state = 2, M.fly.on = 0, g_now >=
       M.backoff_until (unsigned) and a1 = 0 at 0x863bc (a ready command). By tw_at each loaded value is the world's
       (TWorldG.v tw_read_val, tw_lw, tw_lwu: M_display_sent, M_last_display, g_now, Cfg_display_gap_us, g_nq,
       Q_at, Cmd_display, M_state, M_fly_on, M_backoff_until of Bw), the loop runs drain_loop's iterations (the
       same exit tests, i < g_nq and not ready), and check_latest_drain_m Bw = Some _ rules the trap condition out.
       The unimp word at 0x86404 follows the call of abort on this path, so the same premise rules it out.
   Callee texts assumed: none (the only callees, __asan_report_load4, __asan_handle_no_return and abort, are on the
   error and trap paths).
   The caller: settle reaches it by a tail jump (0x83910, after settle reloads ra at 0x83904 and s0 at 0x83908 and
   restores its sp at 0x8390c; DgnTransportBList.v PTail TB_check_latest_drain), so ra is settle's return address.
   Form: lib/A/Prog/check_latest_drain_c.v (image A's contract of this function), at image B's entry, load
   addresses, runtime cells (lib/B/AsanCells.v), world table TMAP_B and harness hull; its premises also refute the
   three UBSan checks, so the premise list is image A's; the post leaves t4, t5, t6 unspecified as well. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.

Definition CHECK_LATEST_DRAIN : Z := 0x862b8.
Definition CHECK_LATEST_DRAIN_FRAME : Z := 16.
(* The members of the world the code loads outside the loop, at their global's image-B base plus the member's
   offset in it; the loop reads the payloads of g_q (TB_g_q, TW.SZ_g_q) and g_cmd (TB_g_cmd, TW.SZ_g_cmd). *)
Definition CHECK_LATEST_DRAIN_SENT : Z := TB_M + (TW.A_M_display_sent - TW.OFF_M).
Definition CHECK_LATEST_DRAIN_LAST : Z := TB_M + (TW.A_M_last_display - TW.OFF_M).
Definition CHECK_LATEST_DRAIN_GAP : Z := TB_g_cfg + (TW.A_Cfg_display_gap_us - TW.OFF_g_cfg).
Definition CHECK_LATEST_DRAIN_STATE : Z := TB_M + (TW.A_M_state - TW.OFF_M).
Definition CHECK_LATEST_DRAIN_FLY : Z := TB_M + (TW.A_M_fly_on - TW.OFF_M).
Definition CHECK_LATEST_DRAIN_BACKOFF : Z := TB_M + (TW.A_M_backoff_until - TW.OFF_M).
Lemma check_latest_drain_sent_at : CHECK_LATEST_DRAIN_SENT = 0x5dee28.
Proof. reflexivity. Qed.
Lemma check_latest_drain_last_at : CHECK_LATEST_DRAIN_LAST = 0x5dee20.
Proof. reflexivity. Qed.
Lemma check_latest_drain_gap_at : CHECK_LATEST_DRAIN_GAP = 0x5ded30.
Proof. reflexivity. Qed.
Lemma check_latest_drain_state_at : CHECK_LATEST_DRAIN_STATE = 0x5dedec.
Proof. reflexivity. Qed.
Lemma check_latest_drain_fly_at : CHECK_LATEST_DRAIN_FLY = 0x5dee40.
Proof. reflexivity. Qed.
Lemma check_latest_drain_backoff_at : CHECK_LATEST_DRAIN_BACKOFF = 0x5dee18.
Proof. reflexivity. Qed.
Lemma check_latest_drain_globals_at :
  TB_g_now = 0x5ded80 /\ TB_g_nq = 0x5df5e0 /\ TB_g_q = 0x5f1880 /\ TW.SZ_g_q = 4096 /\
  TB_g_cmd = 0x5e5080 /\ TW.SZ_g_cmd = 40960.
Proof. repeat split; reflexivity. Qed.

Definition check_latest_drain_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_latest_drain_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_DRAIN_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_DRAIN_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_LATEST_DRAIN_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_LATEST_DRAIN_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_LATEST_DRAIN_FRAME CELL_K 8 ->
    addressable m TB_g_q TW.SZ_g_q ->
    addressable m TB_g_cmd TW.SZ_g_cmd ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_DRAIN_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_DRAIN) fc None m (seg_rom rsegs)).
