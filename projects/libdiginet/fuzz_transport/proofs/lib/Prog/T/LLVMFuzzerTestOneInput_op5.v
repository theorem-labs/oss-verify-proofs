(* Case 5 of the op loop, 0x13a10-0x13a60 and the shared tail 0x13b20-0x13b24, 0x13c4c-0x13c50
   (fuzz_transport.c:1193-1199 `case 5: { op_begin(); int want = m_wake();
   check_state_wake_code(diginet_session_wake(&g_s, g_now), want); settle(0); break; }`; the model is the
   `op =? 5` branch of TModel/TOps.v LLVMFuzzerTestOneInput_op_m): the two memsets of op_begin and its two
   inline stores, then four calls. m_wake's result `want` is kept in s4 (0x13a48) across diginet_session_wake;
   check_state_wake_code takes diginet_session_wake's result rc in a0 and want in a1 (0x13a58). The case reads
   no input byte: the cursor after it is fuzz_u8_m's c1, in s3 / s6 since the switch. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  m_wake_c m_wake diginet_session_wake_c check_state_wake_code_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.

(* A put-write that misses g_fail_next (TWorld.v: OFF_g_fail_next = 0xfdc8 = 64968, one byte; W_LEN = 0x10050 =
   65616) leaves it. *)
Lemma op5_fn_put : forall (u : list byte) k n v, Z.of_nat (length u) = 65616 -> 0 <= k ->
  k + Z.of_nat n <= 65616 -> (k + Z.of_nat n <= 64968 \/ 64969 <= k) ->
  g_fail_next (upd u k (put n v)) = g_fail_next u.
Proof.
  intros u k n v Hu Hk Hn Hd. unfold g_fail_next, OFF_g_fail_next.
  rewrite u_at_upd_out; [reflexivity | lia | lia | rewrite length_put; lia | rewrite length_put; lia].
Qed.

(* g_fail_next through a chain of put-writes that all miss it; the lengths by m_wake.v's wlen *)
Ltac op5_fn := repeat (rewrite op5_fn_put by (first [wlen | lia])); reflexivity.

(* m_wake (fuzz_transport.c:218-233) writes only M and OW, never g_fail_next, and its result is one of -1, -10,
   -5, 0 (Prog/T/m_wake.v m_wake_m_eq), so a C int. *)
Lemma op5_wake_facts : forall Bx By w, Z.of_nat (length Bx) = 65616 ->
  m_wake_m Bx = Some (By, w) -> g_fail_next By = g_fail_next Bx /\ -2 ^ 31 <= w < 2 ^ 31.
Proof.
  intros Bx By w HL HW.
  rewrite (m_wake_m_eq Bx) in HW. rewrite (mw_on Bx HL) in HW.
  destruct (M_desk_known Bx =? 0); [injection HW as <- <-; split; [reflexivity | lia]|].
  destruct (negb (M_foreign Bx =? 0)); [injection HW as <- <-; split; [reflexivity | lia]|].
  destruct (OW_e2 (mw_B2 Bx) =? 2 ^ 31 - 1); [discriminate HW|].
  destruct (negb (M_fail (mw_B3 Bx) =? 0)).
  { injection HW as <- <-. split; [|lia]. rewrite (mw_W_m Bx HL). unfold mwm_W. op5_fn. }
  destruct (M_state (mw_W Bx) =? 1).
  { injection HW as <- <-. split; [|lia]. rewrite (mw_W_m Bx HL). unfold mwm_W. op5_fn. }
  destruct (s32_at Bx 65312 <? 0) eqn:EN; [discriminate HW|].
  destruct (s32_at Bx 65312 =? 2 ^ 31 - 1); [discriminate HW|].
  apply Z.ltb_ge in EN.
  destruct (15 <? s32_at Bx 65312) eqn:E5; injection HW as <- <-; (split; [|lia]).
  - rewrite (mw_fin_m Bx HL). unfold mwm_W. op5_fn.
  - apply Z.ltb_ge in E5. rewrite (mw_fin_rec_m Bx HL). unfold mwm_W. op5_fn.
Qed.

(* op_begin (fuzz_transport.c:388-394) as case 5 runs it: the two memsets (OFF_OW = 0xff20 = 65312, SZ_OW = 304;
   OFF_GOT = 0xfe3c = 65084, SZ_GOT = 224), then OW.desk_off = -1 (0x13a38; A_OW_desk_off = OFF_OW + 232 = 65544),
   then M.fail = g_fail_next (0x13a3c; A_M_fail = 88) with the byte loaded at 0x13a30. The machine writes in the
   model's order, and OW.desk_off's write does not move g_fail_next. *)
Lemma op5_begin_world : forall (Bx Bz : list byte), Z.of_nat (length Bx) = W_LEN ->
  Bz = upd (upd Bx 65312 (repeat (Z_to_bv 8 0) 304)) 65084 (repeat (Z_to_bv 8 0) 224) ->
  op_begin_m Bx = Some (upd (upd Bz 65544 (put 4 (-1))) 88 (put 4 (u_at Bz OFF_g_fail_next 1)), tt).
Proof.
  intros Bx Bz HL EZ.
  assert (EWL : W_LEN = 65616) by reflexivity.
  assert (R304 : Z.of_nat (length (repeat (Z_to_bv 8 0) 304)) = 304) by (rewrite repeat_length; lia).
  assert (R224 : Z.of_nat (length (repeat (Z_to_bv 8 0) 224)) = 224) by (rewrite repeat_length; lia).
  assert (L1 : Z.of_nat (length (upd Bx 65312 (repeat (Z_to_bv 8 0) 304))) = W_LEN)
    by (rewrite length_upd; [exact HL | lia | rewrite R304; lia]).
  assert (LZ : Z.of_nat (length Bz) = 65616)
    by (rewrite EZ, length_upd; [rewrite L1; exact EWL | lia | rewrite R224, L1; lia]).
  unfold op_begin_m, set_M_fail, set_OW_desk_off, A_M_fail, A_OW_desk_off, OFF_M, OFF_OW, OFF_GOT.
  cbv zeta.
  change (Z.to_nat SZ_OW) with 304%nat. change (Z.to_nat SZ_GOT) with 224%nat.
  change (b8 0) with (Z_to_bv 8 0).
  rewrite <- EZ.
  replace (65312 + 232) with 65544 by lia. replace (0 + 88) with 88 by lia.
  assert (EFN : g_fail_next (upd Bz 65544 (put 4 (-1))) = u_at Bz OFF_g_fail_next 1).
  { change (u_at Bz OFF_g_fail_next 1) with (g_fail_next Bz).
    apply op5_fn_put; [exact LZ | lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia]. }
  rewrite EFN. reflexivity.
Qed.

(* check_state_wake_code (fuzz_transport.c:517-525) returns only when rc = want *)
Lemma op5_code_eq : forall Bx By rc want, check_state_wake_code_m Bx rc want = Some (By, tt) -> rc = want.
Proof.
  intros Bx By rc want H. unfold check_state_wake_code_m in H.
  destruct (Z.eqb_spec rc want) as [E|_]; [exact E | cbn [negb] in H; discriminate H].
Qed.

Section OP5.
Context (data : Z) (D : list byte).

(* 0x13b20-0x13b24 and the shared tail 0x13c4c-0x13c50: settle(0), then the latch. Only the saved registers,
   s3 / s6 (the cursor after the op) and the world are live. *)
Lemma llvm_op5_settle : forall Sp lo ops c1 B4 B5
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q m0 m j10 j28
    gp tp q0 q1 q2 q3 q4 q5 q6 q7 r8 r20 r23 e0 e1 e2 e3 e4 e5 e6 rz,
  settle_contract ->
  llvm_mem data D Sp lo B4 m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  llvm_cursor D c1 -> 0 <= ops < OPS_MAX ->
  settle_m B4 0 = Some (B5, tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops c1 B5
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp e0 e1 e2 r8 (Z_to_bv 64 7) q0 q1 q2 q3 q4 q5 q6 q7
             (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c1)) r20
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (fi_n c1)) r23
             (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
        F (Z_to_bv 64 0x13b20) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c1 B4 B5 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q m0 m j10 j28
    gp tp q0 q1 q2 q3 q4 q5 q6 q7 r8 r20 r23 e0 e1 e2 e3 e4 e5 e6 rz STC HM HC1 HOPS HB5 HK.
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  unfold LLVM_LOOP_K in HLO. unfold LLVM_FRAME in HSP2.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_s.
  (* 0x13b20 mv a0, zero; 0x13b24 j 0x13c4c; 0x13c4c jal settle *)
  do 3 zstep.
  eapply evt_cut.
  { eapply STC with (B := B4) (ticked := 0) (lo := lo).
    - reflexivity.
    - lia.
    - exact HWM.
    - exact HB5.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold settle_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold settle_FRAME. lia.
    - exact HMI. }
  intros ms' Hpost.
  destruct Hpost as (g0 & g1 & g2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & i3 & i4 & i5 & i6 & m5 &
                     -> & MU5 & WMO5 & MI5 & ST5 & EB & WM5).
  rewrite unsigned_lit in MU5, ST5 by lia.
  subst B5.
  assert (HM5 : llvm_mem data D Sp lo B4 m0 m5 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_call data D Sp lo settle_FRAME B4 B4 m0 m m5);
      [ exact HM0 | unfold settle_FRAME, LLVM_LOOP_K; lia | apply munch_add_world; exact MU5
      | exact WMO5 | exact MI5 | exact ST5 | exact WM5 | exact HFN ]. }
  (* 0x13c50 j 0x1428c *)
  rewrite (ret_pc_even 0x13c50) by (first [lia | reflexivity]).
  zstep.
  apply HK. unfold llvm_latch. do 22 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HC1|]. exact HM5.
Qed.

(* 0x13a40-0x13a60: m_wake(), diginet_session_wake(&g_s, g_now), check_state_wake_code(rc, want), then the jump to
   0x13b20. The world is op_begin's result B1. *)
Lemma llvm_op5_calls : forall Sp lo ops c1 B1 B2 B3 B4 B5 want rc
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q m0 m j10 j28
    gp tp q0 q1 q2 q3 q4 q5 q6 q7 r8 r20 r23 e0 e1 e2 e3 e4 e5 e6 rz,
  m_wake_contract -> diginet_session_wake_contract -> check_state_wake_code_contract -> settle_contract ->
  llvm_mem data D Sp lo B1 m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  llvm_cursor D c1 -> 0 <= ops < OPS_MAX ->
  m_wake_m B1 = Some (B2, want) ->
  diginet_session_wake_m timg_plain None B2 (g_now B2) = Some (B3, rc) ->
  check_state_wake_code_m B3 rc want = Some (B4, tt) ->
  settle_m B4 0 = Some (B5, tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops c1 B5
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp e0 e1 e2 r8 (Z_to_bv 64 7) q0 q1 q2 q3 q4 q5 q6 q7
             (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c1)) r20
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (fi_n c1)) r23
             (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
        F (Z_to_bv 64 0x13a40) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c1 B1 B2 B3 B4 B5 want rc ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q m0 m j10 j28
    gp tp q0 q1 q2 q3 q4 q5 q6 q7 r8 r20 r23 e0 e1 e2 e3 e4 e5 e6 rz WKC DWC CWC STC HM HC1 HOPS HB2 HB3 HB4 HB5 HK.
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LB1 : Z.of_nat (length B1) = 65616)
    by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  destruct (op5_wake_facts B1 B2 want LB1 HB2) as (FN2 & RW).
  pose proof (op5_code_eq B3 B4 rc want HB4) as ERC.
  unfold LLVM_LOOP_K in HLO. unfold LLVM_FRAME in HSP2.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_now. wk_eq_fact OFF_g_s.
  (* ---- 0x13a40 jal m_wake ---- *)
  zstep.
  eapply evt_cut.
  { eapply WKC with (B := B1) (lo := lo).
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold m_wake_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold m_wake_FRAME. lia.
    - exact HMI.
    - exact HWM.
    - exact HB2. }
  intros ms' Hpost.
  destruct Hpost as (c0 & cc1 & c2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & f3 & f4 & f5 & f6 & m2 &
                     -> & MU2 & WMO2 & MI2 & ST2 & WM2).
  rewrite unsigned_lit in MU2, ST2 by lia.
  assert (HM2 : llvm_mem data D Sp lo B2 m0 m2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_call data D Sp lo m_wake_FRAME B1 B2 m0 m m2);
      [ exact HM0 | unfold m_wake_FRAME, LLVM_LOOP_K; lia | exact MU2 | exact WMO2
      | exact MI2 | exact ST2 | exact WM2 | rewrite FN2; exact HFN ]. }
  clear HD HSTK HMI HRO HWM HRW HFN MU2 WMO2 MI2 ST2 WM2 HM0.
  pose proof HM2 as HM2c. unfold llvm_mem in HM2c.
  destruct HM2c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  assert (HNOW : 0 <= g_now B2 < 2 ^ 64).
  { unfold g_now. pose proof (u_at_range B2 OFF_g_now 8) as R. cbn in R. lia. }
  (* ---- 0x13a44 ld a1, g_now (s9 + 0x20 = OFF_g_now 0xfde8); 0x13a48 mv s4, a0 (want);
     0x13a4c-0x13a50 a0 = 0x32e00 = W_BASE_PLAIN + OFF_g_s; 0x13a54 jal diginet_session_wake ---- *)
  rewrite (ret_pc_even 0x13a44) by (first [lia | reflexivity]).
  do 5 zstep.
  eapply evt_cut.
  { eapply DWC with (B := B2) (TF := None) (lo := lo).
    - reflexivity.
    - reflexivity.
    - exact HNOW.
    - exact HWM.
    - exact HFN.
    - exact HB3.
    - exact I.
    - exact HRO.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold diginet_session_wake_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold diginet_session_wake_FRAME. lia.
    - exact HMI. }
  intros ms' Hpost.
  destruct Hpost as (k0 & k1 & k2 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & n3 & n4 & n5 & n6 & m3 &
                     -> & MU3 & WMO3 & MI3 & ST3 & WM3 & FN3).
  rewrite unsigned_lit in MU3, ST3 by lia.
  assert (HM3 : llvm_mem data D Sp lo B3 m0 m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_call data D Sp lo diginet_session_wake_FRAME B2 B3 m0 m2 m3);
      [ exact HM2 | unfold diginet_session_wake_FRAME, LLVM_LOOP_K; lia | exact MU3 | exact WMO3
      | exact MI3 | exact ST3 | exact WM3 | exact FN3 ]. }
  clear HD HSTK HMI HRO HWM HRW HFN MU3 WMO3 MI3 ST3 WM3 HM2.
  pose proof HM3 as HM3c. unfold llvm_mem in HM3c.
  destruct HM3c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  (* ---- 0x13a58 mv a1, s4 (want); 0x13a5c jal check_state_wake_code (a0 = rc) ---- *)
  rewrite (ret_pc_even 0x13a58) by (first [lia | reflexivity]).
  do 2 zstep.
  eapply evt_cut.
  { eapply CWC with (B := B3) (lo := lo) (rc := rc) (want := want).
    - reflexivity.
    - reflexivity.
    - rewrite ERC. exact RW.
    - exact RW.
    - exact HWM.
    - exact HB4.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold check_state_wake_code_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold check_state_wake_code_FRAME. lia.
    - exact HMI. }
  intros ms' Hpost.
  destruct Hpost as (o0 & o1 & o2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & u3 & u4 & u5 & u6 & m4 &
                     -> & MU4 & WMO4 & MI4 & ST4 & EB4 & WM4).
  rewrite unsigned_lit in MU4, ST4 by lia.
  subst B4.
  assert (HM4 : llvm_mem data D Sp lo B3 m0 m4 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_call data D Sp lo check_state_wake_code_FRAME B3 B3 m0 m3 m4);
      [ exact HM3 | unfold check_state_wake_code_FRAME, LLVM_LOOP_K; lia | apply munch_add_world; exact MU4
      | exact WMO4 | exact MI4 | exact ST4 | exact WM4 | exact HFN ]. }
  clear HD HSTK HMI HRO HWM HRW HFN MU4 WMO4 MI4 ST4 WM4 HM3.
  (* ---- 0x13a60 j 0x13b20 ---- *)
  rewrite (ret_pc_even 0x13a60) by (first [lia | reflexivity]).
  zstep.
  eapply llvm_op5_settle; [exact STC | exact HM4 | exact HC1 | exact HOPS | exact HB5 | exact HK].
Qed.

Lemma llvm_op5 : forall Sp lo ops c c1 B B1 B2 B3 B4 B5 want rc
    m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  memset_contract -> m_wake_contract -> diginet_session_wake_contract -> check_state_wake_code_contract ->
  settle_contract ->
  llvm_case data D m0 gp tp 5 Sp lo ops c c1 B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  op_begin_m B = Some (B1, tt) ->
  m_wake_m B1 = Some (B2, want) ->
  diginet_session_wake_m timg_plain None B2 (g_now B2) = Some (B3, rc) ->
  check_state_wake_code_m B3 rc want = Some (B4, tt) ->
  settle_m B4 0 = Some (B5, tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops c1 B5
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros Sp lo ops c c1 B B1 B2 B3 B4 B5 want rc m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q
    MSC WKC DWC CWC STC H HB1 HB2 HB3 HB4 HB5 HK.
  destruct H as (rz & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 &
                 t3 & t4 & t5 & t6 & m & j10 & j28 & -> & HOPS & HN & HC & HC1 & HM).
  pose proof HM as HM0.
  unfold llvm_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length B) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  unfold LLVM_CASE. cbn [Z.eqb Pos.eqb].
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_OW. wk_eq_fact OFF_GOT.
  wk_eq_fact OFF_M. wk_eq_fact A_M_fail. wk_eq_fact A_OW_desk_off. wk_eq_fact SZ_OW. wk_eq_fact SZ_GOT.
  (* ---- 0x13a10-0x13a1c: memset(&OW, 0, 0x130); a0 = s9 + 0x158 = W_BASE_PLAIN + OFF_OW ---- *)
  do 4 zstep.
  assert (CW1 : rw_cells rsegs m (W_BASE_PLAIN + OFF_OW) [CB (Z.to_nat 304) (sub B OFF_OW 304)]).
  { pose proof (wm_cell rsegs W_BASE_PLAIN m B OFF_OW 304 (W_BASE_PLAIN + OFF_OW) HWM eq_refl
                  ltac:(lia) ltac:(lia)) as P.
    rewrite length_sub in P by lia. exact P. }
  eapply evt_cut.
  { eapply MSC with (junk := sub B OFF_OW 304).
    - rewrite !unsigned_lit by lia.
      replace (W_BASE_PLAIN + OFF_g_fail_next + 344) with (W_BASE_PLAIN + OFF_OW) by lia. exact CW1.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m1 &
                     -> & MU1 & WMO1 & MI1 & CZ1).
  rewrite !unsigned_lit in MU1, CZ1 by lia.
  replace (W_BASE_PLAIN + OFF_g_fail_next + 344) with (W_BASE_PLAIN + OFF_OW) in MU1, CZ1 by lia.
  cbn [Z.to_nat] in CZ1.
  assert (HM1 : llvm_mem data D Sp lo (upd B OFF_OW (repeat (Z_to_bv 8 0) 304)) m0 m1
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_fill data D Sp lo B m0 m m1);
      [ exact HM0 | exact MU1 | exact WMO1 | exact MI1 | exact CZ1 | lia | lia | lia | ].
    unfold g_fail_next.
    rewrite u_at_upd_out by (rewrite ?repeat_length; unfold OFF_g_fail_next, OFF_OW in *; lia).
    exact HFN. }
  clear HM0 HD HSTK HMI HRO HWM HRW HFN CW1 CZ1 MU1 WMO1 MI1.
  (* ---- 0x13a20-0x13a2c: memset(&GOT, 0, 0xe0); a0 = s9 + 0x74 = W_BASE_PLAIN + OFF_GOT ---- *)
  pose proof HM1 as HM1c. unfold llvm_mem in HM1c.
  destruct HM1c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  set (Ba := upd B OFF_OW (repeat (Z_to_bv 8 0) 304)) in *.
  assert (LBa : Z.of_nat (length Ba) = W_LEN)
    by (unfold Ba; rewrite length_upd; [exact LBz | lia | rewrite repeat_length; lia]).
  rewrite (ret_pc_even 0x13a20) by (first [lia | reflexivity]).
  do 4 zstep.
  assert (CW2 : rw_cells rsegs m1 (W_BASE_PLAIN + OFF_GOT) [CB (Z.to_nat 224) (sub Ba OFF_GOT 224)]).
  { pose proof (wm_cell rsegs W_BASE_PLAIN m1 Ba OFF_GOT 224 (W_BASE_PLAIN + OFF_GOT) HWM eq_refl
                  ltac:(lia) ltac:(lia)) as P.
    rewrite length_sub in P by lia. exact P. }
  eapply evt_cut.
  { eapply MSC with (junk := sub Ba OFF_GOT 224).
    - rewrite !unsigned_lit by lia.
      replace (W_BASE_PLAIN + OFF_g_fail_next + 116) with (W_BASE_PLAIN + OFF_GOT) by lia. exact CW2.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 &
                     -> & MU2 & WMO2 & MI2 & CZ2).
  rewrite !unsigned_lit in MU2, CZ2 by lia.
  replace (W_BASE_PLAIN + OFF_g_fail_next + 116) with (W_BASE_PLAIN + OFF_GOT) in MU2, CZ2 by lia.
  cbn [Z.to_nat] in CZ2.
  assert (HM2 : llvm_mem data D Sp lo (upd Ba OFF_GOT (repeat (Z_to_bv 8 0) 224)) m0 m2
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_fill data D Sp lo Ba m0 m1 m2);
      [ exact HM1 | exact MU2 | exact WMO2 | exact MI2 | exact CZ2 | lia | lia | lia | ].
    unfold g_fail_next.
    rewrite u_at_upd_out by (rewrite ?repeat_length; unfold OFF_g_fail_next, OFF_GOT in *; lia).
    exact HFN. }
  clear HD HSTK HMI HRO HWM HRW HFN CW2 CZ2 MU2 WMO2 MI2 HM1.
  pose proof HM2 as HM2c. unfold llvm_mem in HM2c.
  destruct HM2c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  set (Bb := upd Ba OFF_GOT (repeat (Z_to_bv 8 0) 224)) in *.
  assert (LBb : Z.of_nat (length Bb) = 65616)
    by (unfold Bb; rewrite length_upd; [rewrite LBa; reflexivity | lia | rewrite repeat_length; lia]).
  rewrite (ret_pc_even 0x13a30) by (first [lia | reflexivity]).
  (* ---- 0x13a30-0x13a3c: lbu a0, g_fail_next; li a1, -1; OW.desk_off = -1 (s9 + 0x240);
     M.fail = g_fail_next (s10 + 0x58): op_begin's last two writes ---- *)
  unfold off_world in HOW. unfold off_window in HOWIN.
  unfold LLVM_LOOP_K, LLVM_FRAME in *.
  unfold llvm_frame_consts, llvm_saved in HRW.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m2) as MU6.
  pose proof (wmono_refl rsegs m2) as WMO6.
  do 4 zstep.
  (* the world is now op_begin's result, the model's B1 *)
  assert (EB1 : upd (upd Bb 65544 (put 4 (-1))) 88 (put 4 (u_at Bb OFF_g_fail_next 1)) = B1).
  { rewrite (op5_begin_world B Bb LBz eq_refl) in HB1. congruence. }
  lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN _ |- _ => rewrite EB1 in H end.
  assert (FN1 : g_fail_next B1 = g_fail_next Bb) by (rewrite <- EB1; op5_fn).
  lazymatch goal with H : rw_cells rsegs ?m6 W_BASE_PLAIN [CB _ B1] |- _ =>
    assert (HM6 : llvm_mem data D Sp lo B1 m0 m6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28) end.
  { eapply (llvm_mem_after_call data D Sp lo 0 Bb B1 m0 m2);
      [ exact HM2 | unfold LLVM_LOOP_K; lia | exact MU6 | exact WMO6 | assumption | assumption
      | assumption | rewrite FN1; exact HFN ]. }
  assert (HCc1 : llvm_cursor D c1).
  { rewrite HC1. unfold llvm_cursor, fuzz_u8_m in *.
    destruct (Z.eqb_spec (fi_n c) 0); [lia|]. cbn. lia. }
  (* ---- 0x13a40: the calls ---- *)
  eapply llvm_op5_calls;
    [ exact WKC | exact DWC | exact CWC | exact STC | exact HM6 | exact HCc1 | exact HOPS
    | exact HB2 | exact HB3 | exact HB4 | exact HB5 | exact HK ].
Qed.

End OP5.
