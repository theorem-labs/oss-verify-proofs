(* The tagged path of case 4 of the ubsan LLVMFuzzerTestOneInput, 0x14384 .. 0x143f0 (fuzz/fuzz_transport.c:1102-1107):
     0x14384  want in s7: -10 if sys, else -5 if at < 0 and g_nq = QUEUE_MAX, else 0 (&M kept in s1)      t4_E1
     0x143b4  rc = diginet_session_submit(&g_s, &c); check_refusal_submit(&c, rc, before);
              if !sys check_latest_submit(rc, want); s8 = &M, s1 = 1 again                              t4_E2
   It ends at 0x143f0 in LLVMFuzzerTestOneInput_op4_tag_rec.v's t4r_at. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells
  Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid
  LLVMFuzzerTestOneInput_op4_lib LLVMFuzzerTestOneInput_op4_tag_lib LLVMFuzzerTestOneInput_op4_tag_m
  LLVMFuzzerTestOneInput_op4_tag_s LLVMFuzzerTestOneInput_op4_tag_rec.
Import ListNotations.
Open Scope Z_scope.

(* 0x143b4: want in s7, &M in s1 *)
Definition t4_SW (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte)
    (Sp lo ops before : Z) (c3 : fuzz_in) (B1 : list byte) (display key : Z) (F : bvmap 5 word) (fc : bv 32)
    (at_ : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (jio jhi : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x143b4) fc None m (seg_rom rsegs) /\
    s0 = Z_to_bv 64 (g_ncmd B1) /\ s1 = Z_to_bv 64 (W_BASE_UBSAN + OFF_M) /\
    s2 = Z_to_bv 64 (229576 + g_ncmd B1 * 40) /\ s3 = Z_to_bv 64 (data + fi_off (t4_c5 D c3)) /\
    s4 = Z_to_bv 64 (at_ mod 2 ^ 32) /\ s5 = Z_to_bv 64 229576 /\ s6 = Z_to_bv 64 (t4_n D c3) /\
    s7 = Z_to_bv 64 (t4_want B1 D c3 at_) /\ s9 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next) /\
    s10 = Z_to_bv 64 (Z.b2z (t4_sys B1 D c3)) /\ s11 = Z_to_bv 64 ops /\
    t4_ok D ops before c3 B1 display key /\ length jhi = 8%nat /\ (at_ = -1 \/ 0 <= at_ < CMDS_MAX) /\
    llvm_mem data D regs0 m0 Sp lo (t4_B2 B1) m (t4_j10 D c3 before) jio (t4_cs B1 D c3 display key ++ jhi).

Lemma t4_lxor63' : forall x, 0 <= x < 9223372036854775808 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof. intros x H. change 9223372036854775808 with (2 ^ 63). apply zb_lxor_pow2_small; lia. Qed.

(* the machine's want against the model's, the comparisons decided by the context *)
Ltac t4_want_eq :=
  apply wk_bv_eqm;
  repeat match goal with
  | |- context [bv_swrap 32 ?x] =>
      first [ rewrite (swrap32_small x) by lia
            | (let v0 := wk_zval x in let v := eval vm_compute in (bv_swrap 32 v0) in
               change (bv_swrap 32 x) with v) ]
  end;
  rewrite ?unsigned_lit_wrap; rewrite ?t4_lxor63' by lia;
  decide_tests;
  first [ reflexivity | (Z.div_mod_to_equations; lia) | (idtac "WANTFAIL"; t4_goal; fail 1) ].

Lemma t4_want_rng : forall B1 D c3 at_, -10 <= t4_want B1 D c3 at_ <= 0.
Proof.
  intros B1 D c3 at_. unfold t4_want, SPEC_E_REFUSED, SPEC_E_SPACE, SPEC_OK.
  destruct (t4_sys B1 D c3); [lia|]. destruct ((at_ <? 0) && (g_nq (t4_B2 B1) =? QUEUE_MAX)); lia.
Qed.

Lemma t4_j10_hi : forall D c3 before, sub (t4_j10 D c3 before) 8 8 = le8 (Z_to_bv 64 (bv_swrap 32 before)).
Proof.
  intros. unfold sub, t4_j10. change (Z.to_nat 8) with 8%nat.
  rewrite skipn_app, length_le8. rewrite (skipn_all2 (le8 _)) by (rewrite length_le8; lia). rewrite app_nil_l.
  replace (8 - 8)%nat with 0%nat by lia.
  change (skipn 0 (le8 (Z_to_bv 64 (bv_swrap 32 before)))) with (le8 (Z_to_bv 64 (bv_swrap 32 before))).
  apply firstn_all2. rewrite length_le8. lia.
Qed.

Lemma t4_E1 : forall data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms at_ (Q : machine_state -> Prop),
  t4_SD data D regs0 m0 Sp lo ops before c3 B1 display key F fc at_ ms ->
  t4_atopt B1 key = Some at_ ->
  (forall ms', t4_SW data D regs0 m0 Sp lo ops before c3 B1 display key F fc at_ ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms at_ Q H HAT HK.
  destruct H as (ra & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 &
                 s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & jio & jhi & -> &
                 E0 & E2 & E3 & E4 & E5 & E6 & E8 & E9 & E10 & E11 & HOK & LJHI & HM).
  subst s0 s2 s3 s4 s5 s6 s8 s9 s10 s11.
  pose proof HOK as (HOPS & HCUR & HBEF & HDSP & HKEY & HSER).
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & HMI & _ & _ & _ & HWM & _ & LB & _).
  assert (HAR : at_ = -1 \/ 0 <= at_ < CMDS_MAX).
  { unfold t4_atopt in HAT. destruct (negb (h_coalescable_m key =? 0)).
    - destruct (t4_findat_rng _ _ _ 0 at_ ltac:(lia) HAT) as [R|R]; [right; lia | left; exact R].
    - injection HAT as <-. left; reflexivity. }
  pose proof (s32_range (t4_B2 B1) 64980) as HS32.
  (* ---- 0x14384 mv s1, s8; 0x14388 beqz s10 ---- *)
  zstep. zstep.
  destruct (t4_sys B1 D c3) eqn:HSYS.
  - (* sys: 0x1438c li s7, -10; 0x14390 j 0x143b4 *)
    t4_br. zstep. zstep.
    apply HK. unfold t4_SW, t4_want. rewrite HSYS.
    do 28 eexists. exists m, jio, jhi.
    split; [reflexivity|].
    do 11 (split; [t4_weq|]).
    split; [exact HOK|]. split; [exact LJHI|]. split; [exact HAR|]. exact HM.
  - (* 0x14394 lw a0, 0xc(s9) (g_nq, signed); 0x14398 sext.w a1, s4; 0x1439c slti a1, a1, 0;
       0x143a0 addi a0, a0, -0x200; 0x143a4 seqz a0, a0; 0x143a8 and a0, a1, a0; 0x143ac neg a0, a0;
       0x143b0 andi s7, a0, -5 *)
    t4_br.
    assert (S512 : s32_at (t4_B2 B1) 64980 = 512 <-> g_nq (t4_B2 B1) = QUEUE_MAX)
      by (unfold QUEUE_MAX; apply (t4_s32_iff (t4_B2 B1) 64980 512); lia).
    destruct HAR as [EA|EA].
    + subst at_.
      do 8 zstep.
      apply HK. unfold t4_SW. rewrite HSYS.
      do 28 eexists. exists m, jio, jhi.
      split; [reflexivity|].
      do 7 (split; [t4_weq|]).
      split.
      { unfold t4_want. rewrite HSYS. cbv iota.
        destruct (Z.eq_dec (g_nq (t4_B2 B1)) QUEUE_MAX) as [N|N].
        - pose proof (proj2 S512 N) as N'. rewrite (proj2 (Z.eqb_eq _ _) N). t4_want_eq.
        - assert (N' : s32_at (t4_B2 B1) 64980 <> 512) by (intros X; apply N; apply (proj1 S512); exact X).
          rewrite (proj2 (Z.eqb_neq _ _) N). t4_want_eq. }
      do 3 (split; [t4_weq|]).
      split; [exact HOK|]. split; [exact LJHI|]. split; [left; reflexivity|]. exact HM.
    + do 8 zstep.
      apply HK. unfold t4_SW. rewrite HSYS.
      do 28 eexists. exists m, jio, jhi.
      split; [reflexivity|].
      do 7 (split; [t4_weq|]).
      split.
      { unfold t4_want. rewrite HSYS. cbv iota.
        rewrite (proj2 (Z.ltb_ge at_ 0) ltac:(lia)). cbn [andb].
        unfold CMDS_MAX in EA. t4_want_eq. }
      do 3 (split; [t4_weq|]).
      split; [exact HOK|]. split; [exact LJHI|]. split; [right; exact EA|]. exact HM.
Qed.

Lemma t4_E2 : diginet_session_submit_contract -> check_refusal_submit_contract -> check_latest_submit_contract ->
  forall data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms at_ rc B3 B4 B5 (Q : machine_state -> Prop),
  t4_SW data D regs0 m0 Sp lo ops before c3 B1 display key F fc at_ ms ->
  diginet_session_submit_m (t4_B2 B1) (t4_cs B1 D c3 display key) = Some (B3, rc) ->
  check_refusal_submit_m B3 (t4_cs B1 D c3 display key) rc before = Some (B4, tt) ->
  (if t4_sys B1 D c3 then Some (B4, tt) else check_latest_submit_m B4 rc (t4_want B1 D c3 at_)) = Some (B5, tt) ->
  (forall ms', (exists jhi, length jhi = 8%nat /\
                 t4r_at data D regs0 m0 Sp lo ops before c3 B1 display key jhi at_ B5 F fc ms') ->
               evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros SUB CRS CLS data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms at_ rc B3 B4 B5 Q H ES ER EL HK.
  destruct H as (ra & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 &
                 s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & jio & jhi & -> &
                 E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E9 & E10 & E11 & HOK & LJHI & HAR & HM).
  subst s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11.
  pose proof HOK as (HOPS & HCUR & HBEF & HDSP & HKEY & HSER).
  pose proof (t4_cbD D c3 HCUR) as (HCB1 & HCB2 & HCB3).
  pose proof (t4_cs_len B1 D c3 display key HCB1 HCB2 HCB3) as LCS.
  pose proof (t4_want_rng B1 D c3 at_) as HWR.
  pose proof HM as HMc. unfold llvm_mem in HMc.
  destruct HMc as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                   HJ1 & HJ2 & HJ3 & HRW).
  unfold LH_K, LH_FRAME in *.
  clear HD HRO HMU HWMO HRW.
  pose proof (wm_len _ _ _ _ HWM) as LB.
  pose proof (t4_mem_j60 _ _ _ _ _ _ _ _ _ _ _ HM) as HJ.
  pose proof (proj1 (proj1 (bytes_at_app rsegs m (Sp + 96) _ _) HJ)) as HB.
  (* ---- 0x143b4 auipc a0; 0x143b8 addi a0 (&g_s); 0x143bc addi a1, sp, 0x60; 0x143c0 jal submit ---- *)
  do 4 zstep.
  eapply evt_cut.
  { eapply (SUB _ (Z_to_bv 64 Sp) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
              (Sp + 96) rc (t4_cs B1 D c3 display key) (t4_B2 B1) B3).
    - t4_weq.
    - t4_weq.
    - exact HB.
    - exact LCS.
    - unfold arg_blk, off_world, off_window; rewrite unsigned_lit by lia;
      split; [lia|]; split; [lia|]; split; [right; lia | right; lia].
    - lia.
    - exact HWM.
    - exact ES.
    - rewrite unsigned_lit by lia; exact HSP.
    - rewrite unsigned_lit by lia; exact HSTK.
    - rewrite unsigned_lit by lia; unfold diginet_session_submit_FRAME; lia.
    - unfold w_off_stack; rewrite unsigned_lit by lia; unfold diginet_session_submit_FRAME; lia.
    - exact HMI. }
  intros ms' Hpost.
  destruct Hpost as (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & p8 & p9 & p10 & p11 & p12 & p13 & m2 &
                     -> & MU2 & WMO2 & MI2 & ST2 & WM2).
  rewrite unsigned_lit in MU2, ST2 by lia.
  pose proof (submit_rc _ _ _ _ ES) as HRC.
  assert (HFN3 : g_fail_next B3 <= 1)
    by (rewrite (submit_gfn (t4_B2 B1) _ B3 rc LB LCS ES); exact HFN).
  assert (HM2 : llvm_mem data D regs0 m0 Sp lo B3 m2 (t4_j10 D c3 before) jio
                  (t4_cs B1 D c3 display key ++ jhi)).
  { eapply (llvm_mem_after_call data D regs0 m0 Sp lo diginet_session_submit_FRAME (t4_B2 B1) B3 _ m2);
      [ exact HM | unfold diginet_session_submit_FRAME, LH_K; lia | exact MU2 | exact WMO2
      | exact MI2 | exact ST2 | exact WM2 | exact HFN3 ]. }
  clear HM HJ HB HSTK HMI HWM HFN MU2 WMO2 MI2 ST2 WM2.
  t4_ret.
  (* ---- 0x143c4 mv s8, a0; 0x143c8 addi a0, sp, 0x60; 0x143cc mv a1, s8; 0x143d0 ld a2, 0x18(sp);
     0x143d4 jal check_refusal_submit ---- *)
  pose proof (t4_mem_rd10 _ _ _ _ _ _ _ _ _ _ _ 8 8%nat (Sp + 24) HM2 ltac:(lia) ltac:(lia) ltac:(lia)) as HR18.
  rewrite (t4_j10_hi D c3 before) in HR18.
  pose proof HM2 as HM2c. unfold llvm_mem in HM2c.
  destruct HM2c as (_ & _ & _ & _ & _ & HSTK2 & _ & _ & _ & HMI2 & _ & HWM2 & _ & _ & _ & _ & _ & _ & _).
  pose proof (t4_mem_j60 _ _ _ _ _ _ _ _ _ _ _ HM2) as HJ2'.
  pose proof (proj1 (proj1 (bytes_at_app rsegs m2 (Sp + 96) _ _) HJ2')) as HB2.
  do 5 zstep.
  eapply evt_cut.
  { eapply (CRS _ (Z_to_bv 64 Sp) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
              B3 B4 (Sp + 96) (t4_cs B1 D c3 display key) rc before).
    - t4_weq.
    - t4_weq.
    - t4_weq.
    - lia.
    - exact HBEF.
    - lia.
    - lia.
    - exact HB2.
    - exact LCS.
    - unfold off_window; rewrite unsigned_lit by lia; unfold check_refusal_submit_FRAME; right; lia.
    - exact HWM2.
    - exact ER.
    - rewrite unsigned_lit by lia; exact HSP.
    - rewrite unsigned_lit by lia; exact HSTK2.
    - rewrite unsigned_lit by lia; unfold check_refusal_submit_FRAME; lia.
    - unfold w_off_stack; rewrite unsigned_lit by lia; unfold check_refusal_submit_FRAME; lia.
    - exact HMI2. }
  intros ms' Hpost.
  destruct Hpost as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & m3 &
                     -> & MU3 & WMO3 & MI3 & ST3 & EB3 & WM3).
  rewrite unsigned_lit in MU3, ST3 by lia.
  subst B4.
  assert (HM3 : llvm_mem data D regs0 m0 Sp lo B3 m3 (t4_j10 D c3 before) jio
                  (t4_cs B1 D c3 display key ++ jhi)).
  { eapply (llvm_mem_after_call data D regs0 m0 Sp lo check_refusal_submit_FRAME B3 B3 m2 m3);
      [ exact HM2 | unfold check_refusal_submit_FRAME, LH_K; lia
      | apply lh_munch_add_world; exact MU3 | exact WMO3 | exact MI3 | exact ST3 | exact WM3 | exact HFN3 ]. }
  clear HM2 HJ2' HB2 HSTK2 HMI2 HWM2 HR18 MU3 WMO3 MI3 ST3 WM3.
  t4_ret.
  (* ---- 0x143d8 bnez s10 ---- *)
  zstep.
  destruct (t4_sys B1 D c3) eqn:HSYS.
  - (* sys: no check_latest_submit; 0x143e8 mv s8, s1; 0x143ec li s1, 1 *)
    t4_br.
    try rewrite HSYS in EL. cbv iota in EL. apply opt_pair_inv in EL. destruct EL as [EB5 _]. subst B5.
    zstep. zstep.
    apply HK. exists jhi. split; [exact LJHI|]. unfold t4r_at.
    do 17 eexists. eexists. exists jio.
    split; [reflexivity | exact HM3].
  - (* 0x143dc mv a0, s8; 0x143e0 mv a1, s7; 0x143e4 jal check_latest_submit *)
    t4_br.
    try rewrite HSYS in EL. cbv iota in EL.
    pose proof HM3 as HM3c. unfold llvm_mem in HM3c.
    destruct HM3c as (_ & _ & _ & _ & _ & HSTK3 & _ & _ & _ & HMI3 & _ & HWM3 & _ & _ & _ & _ & _ & _ & _).
    do 3 zstep.
    eapply evt_cut.
    { eapply (CLS _ (Z_to_bv 64 Sp) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
                B3 B5 rc (t4_want B1 D c3 at_)).
      - t4_weq.
      - t4_weq.
      - lia.
      - lia.
      - exact HWM3.
      - exact EL.
      - rewrite unsigned_lit by lia; exact HSP.
      - rewrite unsigned_lit by lia; exact HSTK3.
      - rewrite unsigned_lit by lia; unfold check_latest_submit_FRAME; lia.
      - unfold w_off_stack; rewrite unsigned_lit by lia; unfold check_latest_submit_FRAME; lia.
      - exact HMI3. }
    intros ms' Hpost.
    destruct Hpost as (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & m4 &
                       -> & MU4 & WMO4 & MI4 & ST4 & EB4 & WM4).
    rewrite unsigned_lit in MU4, ST4 by lia.
    subst B5.
    assert (HM4 : llvm_mem data D regs0 m0 Sp lo B3 m4 (t4_j10 D c3 before) jio
                    (t4_cs B1 D c3 display key ++ jhi)).
    { eapply (llvm_mem_after_call data D regs0 m0 Sp lo check_latest_submit_FRAME B3 B3 m3 m4);
        [ exact HM3 | unfold check_latest_submit_FRAME, LH_K; lia
        | apply lh_munch_add_world; exact MU4 | exact WMO4 | exact MI4 | exact ST4 | exact WM4 | exact HFN3 ]. }
    t4_ret.
    zstep. zstep.
    apply HK. exists jhi. split; [exact LJHI|]. unfold t4r_at.
    do 17 eexists. eexists. exists jio.
    split; [reflexivity | exact HM4].
Qed.
