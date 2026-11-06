From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg CheckFacts memchr_c bcmp_c check_c.
Import ListNotations.
Open Scope Z_scope.

Lemma zero_ro : ro_bytes rsegs 0x10392 zero6.
Proof. vm_compute. repeat split; reflexivity. Qed.

Ltac curmem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Theorem check_holds : memchr_contract -> bcmp_contract -> check_contract.
Proof.
  intros MEMCHR BCMP. unfold check_contract, CHECK, CHECK_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo r fabric bs -> -> HB [HL [B1 [B2 [B3 [B4 [B5 B6]]]]]] HF HI ST LO DJ.
  unfold boxreg_B1, boxreg_B2 in *.
  pose proof (bytes_at_bound rsegs m r bs HB) as TB. rewrite HL in TB.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  carve_frame 112%nat ST.
  do 15 step.
  let mm := curmem in pose proof (rd4_read mm r bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)) as RN.
  step.
  rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_n bs).
  step. step. step.
  rewrite ltu_lit by lia.
  if_false.
  step.
  let mm := curmem in pose proof (rd4_read mm r bs 284 HB ltac:(lia) ltac:(rewrite HL; lia)) as RF.
  step.
  rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_fabric bs). rewrite HF.
  step.
  rewrite eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb].
  step.
  let mm := curmem in rename mm into M1.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  assert (EPI : forall m' (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                          x28 x29 x30 x31 : word),
    munch [] M1 m' -> wmono rsegs M1 m' -> mem_inv rsegs m' ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
                          x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x1358c) fc None m' (seg_rom rsegs))).
  { intros m' x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      MU1 WM1 HI1.
    eapply rw_cells_transport in FR; [| exact MU1 | exact WM1 | exact I].
    eapply stk_transport in ST; [| exact MU1 | exact WM1 | intros; left; exact I].
    do 14 zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU1]]; intros x _; exact I|].
    split; [eapply wmono_trans; [exact WM | exact WM1]|].
    split; [exact ST | exact HI1]. }
  step.
  rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (bx_n bs) 0) as [N0|N0].
  { apply EPI; [apply munch_refl | apply wmono_refl | exact HI]. }
  do 8 step.
  assert (OL : forall k i m' (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x24 x26 x27 x28 x29 x30 x31 : word),
    Z.of_nat k = bx_n bs - i -> 0 <= i < bx_n bs -> munch [] M1 m' -> wmono rsegs M1 m' -> mem_inv rsegs m' ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 r) (Z_to_bv 64 fabric)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0x10392) x19 x20 (Z_to_bv 64 (bx_n bs))
                          (Z_to_bv 64 i) (Z_to_bv 64 (r + 56 * (i + 1))) x24 (Z_to_bv 64 (bx_n bs - 1 - i)) x26 x27
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x134d4) fc None m' (seg_rom rsegs))).
  { induction k as [|k IH];
      intros i m' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x24 x26 x27 x28 x29 x30 x31 Hk Hi MU1 WM1 HI1;
      [lia|].
    pose proof (bytes_at_transport rsegs [] M1 m' r bs HB MU1 I) as HBm.
    pose proof (rw_cells_transport rsegs [] M1 m' _ _ FR MU1 WM1 I) as FR1.
    assert (TAIL : forall m' (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x24 x26 x27 x28 x29 x30 x31 : word),
      munch [] M1 m' -> wmono rsegs M1 m' -> mem_inv rsegs m' ->
      evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 r) (Z_to_bv 64 fabric)
                            x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0x10392) x19 x20 (Z_to_bv 64 (bx_n bs))
                            (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (r + 56 * (i + 1))) x24 (Z_to_bv 64 (bx_n bs - 1 - i))
                            x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x13580) fc None m' (seg_rom rsegs))).
    { clear m' HI1 MU1 WM1 HBm FR1.
      intros m' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z19 z20 z24 z26 z27 z28 z29 z30 z31 MU1 WM1 HI1.
      step. step. step.
      rewrite eqb_lit by lia.
      destruct (Z.eqb_spec (i + 1) (bx_n bs)) as [Eq|Ne]; cbn [negb].
      - apply EPI; assumption.
      - replace (r + 56 * (i + 1) + 56) with (r + 56 * (i + 1 + 1)) by lia.
        replace (bx_n bs - 1 - i + -1) with (bx_n bs - 1 - (i + 1)) by lia.
        apply (IH (i + 1)); try assumption; lia. }
    destruct (B3_bounds bs i ltac:(unfold boxreg_B2; lia) B3 Hi) as (Bb & Bn & Be).
    destruct (B3 i Hi) as (Bev & Bn2 & Bnf & Bb0 & Bbf).
    do 4 step.
    rewrite box_addr by lia.
    pose proof (rd4_read m' r bs (56 * i + 12) HBm ltac:(lia) ltac:(rewrite HL; lia)) as RNi.
    pose proof (rd4_read m' r bs (56 * i + 8) HBm ltac:(lia) ltac:(rewrite HL; lia)) as RBi.
    step.
    rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_nch bs i).
    step. rewrite lts_lit by lia. if_false.
    step. step. step.
    rewrite swrap_addi by lia.
    rewrite (Z_to_bv_neg_wrap (bx_nch bs i + -41)) by lia. rewrite (Z_to_bv_neg_wrap (-39)) by lia.
    rewrite ltu_lit by lia. if_false.
    step. step.
    rewrite (unsigned_lit (bx_nch bs i)) by lia. rewrite (land1_even (bx_nch bs i) ltac:(lia) Bev). if_false.
    step.
    rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_base bs i).
    step. rewrite lts_lit by lia. if_false.
    step. rewrite swrap_add by lia.
    step. rewrite lts_lit by lia. if_false.
    step. rewrite ?addi_lit. step. step.
    destruct (memchr_name (r + 56 * i + 24) (bx_name bs i) (bsub_length32 bs i HL ltac:(lia)) (B6 i Hi))
      as [MOK [jm [Hjm MRES]]].
    pose proof (bytes_at_bsub m' r bs (56 * i + 24) 32 HBm ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)) as HNm.
    replace (r + (56 * i + 24)) with (r + 56 * i + 24) in HNm by lia. fold (bx_name bs i) in HNm.
    step.
    eapply evt_cut.
    { eapply MEMCHR.
      - rewrite unsigned_lit by lia. exact HNm.
      - rewrite unsigned_lit by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
        change (bv_unsigned (Z_to_bv 64 32)) with 32. exact MOK.
      - exact HI1. }
    intros ms' Hp. unfold memchr_post in Hp.
    destruct Hp as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & HI2 & _).
    replace (ret_pc (Z_to_bv 64 0x13520)) with (Z_to_bv 64 0x13520) by (apply bv_eq; vm_compute; reflexivity).
    rewrite (unsigned_lit (r + 56 * i + 24)) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    change (bv_unsigned (Z_to_bv 64 32)) with 32. rewrite MRES.
    pose proof (munch_trans [] M1 m' m2 MU1 MU2) as MU3. pose proof (wmono_trans rsegs M1 m' m2 WM1 WM2) as WM3.
    step. rewrite eqb_lit by lia. if_false.
    pose proof (rw_cells_transport rsegs [] M1 m2 _ _ FR MU3 WM3 I) as FR2.
    step. step. step.
    rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (i + 1) (bx_n bs)) as [Lt|Ge]; cbn [negb].
    2:{ apply TAIL; assumption. }
    assert (IL : forall kj j m' (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word),
      Z.of_nat kj = bx_n bs - j -> i + 1 <= j < bx_n bs -> munch [] M1 m' -> wmono rsegs M1 m' -> mem_inv rsegs m' ->
      evt rsegs QQ (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp z5 z6 z7 (Z_to_bv 64 r) (Z_to_bv 64 fabric)
                            z10 z11 z12 z13 z14 z15 z16 z17 (Z_to_bv 64 0x10392) (Z_to_bv 64 (r + 56 * i))
                            (Z_to_bv 64 (r + 56 * j)) (Z_to_bv 64 (bx_n bs)) (Z_to_bv 64 (i + 1))
                            (Z_to_bv 64 (r + 56 * (i + 1))) (Z_to_bv 64 (bx_base bs i + bx_nch bs i))
                            (Z_to_bv 64 (bx_n bs - (i + 1))) (Z_to_bv 64 (bx_n bs - j)) (Z_to_bv 64 (bx_base bs i))
                            z28 z29 z30 z31)
                       F (Z_to_bv 64 0x13538) fc None m' (seg_rom rsegs))).
    { clear y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU2 WM2 MU3 WM3 FR2 HI2.
      induction kj as [|kj IHj];
        intros j m3 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 Hkj Hj3 MU4 WM4 HI4; [lia|].
      pose proof (bytes_at_transport rsegs [] M1 m3 r bs HB MU4 I) as HB3.
      destruct (B3_bounds bs j ltac:(unfold boxreg_B2; lia) B3 ltac:(lia)) as (Cb & Cn & Ce).
      pose proof (B4 i j ltac:(lia) ltac:(lia) ltac:(lia)) as B4ij. unfold meets in B4ij.
      pose proof (rd4_read m3 r bs (56 * j + 8) HB3 ltac:(lia) ltac:(rewrite HL; lia)) as RBj.
      pose proof (rd4_read m3 r bs (56 * j + 12) HB3 ltac:(lia) ltac:(rewrite HL; lia)) as RNj.
      assert (JT : forall m4 (w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 : word),
        munch [] M1 m4 -> wmono rsegs M1 m4 -> mem_inv rsegs m4 ->
        evt rsegs QQ (MS (mkR w1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp w5 w6 w7 (Z_to_bv 64 r) (Z_to_bv 64 fabric)
                              w10 w11 w12 w13 w14 w15 w16 w17 (Z_to_bv 64 0x10392) (Z_to_bv 64 (r + 56 * i))
                              (Z_to_bv 64 (r + 56 * j)) (Z_to_bv 64 (bx_n bs)) (Z_to_bv 64 (i + 1))
                              (Z_to_bv 64 (r + 56 * (i + 1))) (Z_to_bv 64 (bx_base bs i + bx_nch bs i))
                              (Z_to_bv 64 (bx_n bs - (i + 1))) (Z_to_bv 64 (bx_n bs - j)) (Z_to_bv 64 (bx_base bs i))
                              w28 w29 w30 w31)
                         F (Z_to_bv 64 0x13574) fc None m4 (seg_rom rsegs))).
      { intros m4 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 MU5 WM5 HI5.
        step. step. step.
        rewrite eqb_lit by lia.
        destruct (Z.eqb_spec (bx_n bs - j + -1) 0) as [Z0|Z1]; cbn [negb].
        - replace (bx_n bs - (i + 1)) with (bx_n bs - 1 - i) by lia. apply TAIL; assumption.
        - replace (r + 56 * j + 56) with (r + 56 * (j + 1)) by lia.
          replace (bx_n bs - j + -1) with (bx_n bs - (j + 1)) by lia.
          apply (IHj (j + 1)); try assumption; lia. }
      assert (BCALLS : forall m4 (w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 : word),
        munch [] M1 m4 -> wmono rsegs M1 m4 -> mem_inv rsegs m4 ->
        evt rsegs QQ (MS (mkR w1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp w5 w6 w7 (Z_to_bv 64 r) (Z_to_bv 64 fabric)
                              w10 w11 w12 w13 w14 w15 w16 w17 (Z_to_bv 64 0x10392) (Z_to_bv 64 (r + 56 * i))
                              (Z_to_bv 64 (r + 56 * j)) (Z_to_bv 64 (bx_n bs)) (Z_to_bv 64 (i + 1))
                              (Z_to_bv 64 (r + 56 * (i + 1))) (Z_to_bv 64 (bx_base bs i + bx_nch bs i))
                              (Z_to_bv 64 (bx_n bs - (i + 1))) (Z_to_bv 64 (bx_n bs - j)) (Z_to_bv 64 (bx_base bs i))
                              w28 w29 w30 w31)
                         F (Z_to_bv 64 0x1354c) fc None m4 (seg_rom rsegs))).
      { intros m4 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 MU5 WM5 HI5.
        pose proof (bytes_at_transport rsegs [] M1 m4 r bs HB MU5 I) as HB4.
        pose proof (bytes_at_bsub m4 r bs (56 * i) 6 HB4 ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)) as HMi.
        fold (bx_mac bs i) in HMi.
        pose proof (ro_bytes_at rsegs m4 0x10392 zero6 HI5 ltac:(lia) ltac:(cbn; lia) zero_ro) as HZ4.
        destruct (memcmp_model_total (bx_mac bs i) zero6 6) as [v1 V1];
          [rewrite (bsub_length6 bs i HL ltac:(lia)); lia | cbn; lia |].
        destruct (memcmp_eq _ _ 6 v1 (bsub_length6 bs i HL ltac:(lia)) zero6_length V1) as [V1iff V1r].
        step. step. step. step.
        eapply evt_cut.
        { eapply BCMP.
          - rewrite unsigned_lit by lia. exact HMi.
          - change (bv_unsigned (Z_to_bv 64 66450)) with 0x10392. exact HZ4.
          - change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat. exact V1.
          - exact HI5. }
        intros ms' Hp. unfold memcmp_post in Hp.
        destruct Hp as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m5 & -> & MU6 & WM6 & HI6 & _).
        replace (ret_pc (Z_to_bv 64 0x1355c)) with (Z_to_bv 64 0x1355c) by (apply bv_eq; vm_compute; reflexivity).
        pose proof (munch_trans [] M1 m4 m5 MU5 MU6) as MU7. pose proof (wmono_trans rsegs M1 m4 m5 WM5 WM6) as WM7.
        step. rewrite bv_v_zero by lia.
        destruct (Z.eqb_spec v1 0) as [V10|V1n]; cbv beta iota.
        - apply JT; assumption.
        - pose proof (bytes_at_transport rsegs [] M1 m5 r bs HB MU7 I) as HB5.
          pose proof (bytes_at_bsub m5 r bs (56 * i) 6 HB5 ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)) as HMi5.
          fold (bx_mac bs i) in HMi5.
          pose proof (bytes_at_bsub m5 r bs (56 * j) 6 HB5 ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)) as HMj5.
          fold (bx_mac bs j) in HMj5.
          destruct (memcmp_model_total (bx_mac bs i) (bx_mac bs j) 6) as [v2 V2];
            [rewrite (bsub_length6 bs i HL ltac:(lia)); lia | rewrite (bsub_length6 bs j HL ltac:(lia)); lia |].
          destruct (memcmp_eq _ _ 6 v2 (bsub_length6 bs i HL ltac:(lia)) (bsub_length6 bs j HL ltac:(lia)) V2)
            as [V2iff V2r].
          assert (V2n : v2 <> 0).
          { intros E. apply V2iff in E. destruct (B5 i j ltac:(lia) ltac:(lia) ltac:(lia)) as [Z6|NE].
            - apply V1n. apply V1iff. exact Z6.
            - exact (NE E). }
          step. step. step. step.
          eapply evt_cut.
          { eapply BCMP.
            - rewrite unsigned_lit by lia. exact HMi5.
            - rewrite unsigned_lit by lia. exact HMj5.
            - change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat. exact V2.
            - exact HI6. }
          intros ms' Hp. unfold memcmp_post in Hp.
          destruct Hp as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m6 & -> & MU8 & WM8 & HI8 & _).
          replace (ret_pc (Z_to_bv 64 0x13570)) with (Z_to_bv 64 0x13570) by (apply bv_eq; vm_compute; reflexivity).
          pose proof (munch_trans [] M1 m5 m6 MU7 MU8) as MU9. pose proof (wmono_trans rsegs M1 m5 m6 WM7 WM8) as WM9.
          step. rewrite bv_v_zero by lia.
          destruct (Z.eqb_spec v2 0) as [V20|_]; [exfalso; exact (V2n V20)|]. cbv beta iota.
          apply JT; assumption. }
      step.
      rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_base bs j).
      step. rewrite lts_lit by lia.
      destruct (Z.ltb_spec (bx_base bs j) (bx_base bs i + bx_nch bs i)) as [Lt2|Ge2]; cbn [negb].
      - step.
        rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_nch bs j).
        step. rewrite swrap_add by lia.
        step. rewrite lts_lit by lia. if_false.
        apply BCALLS; assumption.
      - apply BCALLS; assumption. }
    step. step.
    replace (bx_n bs - 1 - i) with (bx_n bs - (i + 1)) by lia.
    apply (IL (Z.to_nat (bx_n bs - (i + 1))) (i + 1)); try assumption; lia. }
  rewrite shl_shr32 by lia.
  replace (bx_n bs + -1) with (bx_n bs - 1 - 0) by lia.
  replace (r + 56) with (r + 56 * (0 + 1)) by lia.
  apply (OL (Z.to_nat (bx_n bs)) 0); [lia | lia | apply munch_refl | apply wmono_refl | exact HI].
Qed.
