From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import CheckFactsU memchr_c bcmp_c check_c.
Import ListNotations.
Open Scope Z_scope.

Ltac curmem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Ltac merge5 H :=
  lazymatch type of H with
  | rw_cells ?sg ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?sv) =>
      apply (rw_cells_merge sg mm A [] [c0; c1; c2; c3; c4] sv) in H;
      cbn [app cells_size cells_bytes csize Nat.add] in H
  end.

Theorem check_holds : memchr_contract -> bcmp_contract -> check_contract.
Proof.
  intros MEMCHR BCMP. unfold check_contract, CHECK, CHECK_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo r fabric bs -> -> R4 HB [HL [B1 [B2 [B3 [B4 [B5 B6]]]]]] HF HI ST LO DJ.
  unfold boxreg_B1, boxreg_B2 in *.
  pose proof (bytes_at_bound rsegs m r bs HB) as TB. rewrite HL in TB.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  carve_frame 144%nat ST.
  do 16 step.
  rewrite (unsigned_lit r) by lia. rewrite (land3_mod4 r) by lia.
  step. step. if_false.
  let mm := curmem in pose proof (rd4_read_u mm r bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)) as RN.
  step.
  rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_n bs).
  step. step. step.
  rewrite ltu_lit by lia. if_false.
  let mm := curmem in pose proof (rd4_read_u mm r bs 284 HB ltac:(lia) ltac:(rewrite HL; lia)) as RF.
  step.
  rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_fabric bs). rewrite HF.
  step. step.
  rewrite eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb].
  step. step.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: ?sv) =>
  assert (EPI : forall m' (w40 : list byte)
                       (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                        x28 x29 x30 x31 : word),
    munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m' (bv_unsigned sp + -144) (CB 40 w40 :: sv) ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
                          x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x1371c) fc None m' (seg_rom rsegs)))
  end.
  { intros m' w40 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
      x27 x28 x29 x30 x31 MU1 WM1 HI1 ST1 FR1.
    clear FR ST.
    do 14 zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact ST1 | exact HI1]. }
  rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (bx_n bs) 0) as [N0|N0].
  { merge5 FR. eapply EPI; eassumption. }
  do 15 step.
  rewrite shl_shr32 in * by lia. rewrite (mul56 (bx_n bs)) by lia. rewrite not_lit by lia.
  let mm := curmem in rename mm into M3.
  lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: ?sv) => set (SV := sv) in * end.
  assert (OL : forall k i m' (w16 : list byte)
                      (x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x20 x24 x25 x26 x28 x29 x30 x31 : word),
    Z.of_nat k = bx_n bs - i -> 0 <= i < bx_n bs ->
    munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    bytes_at rsegs m' r bs -> stk rsegs m' lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m' (bv_unsigned sp + -144)
      (C8 (Z_to_bv 64 (bx_n bs)) :: C8 (Z_to_bv 64 (bx_n bs)) :: CB 8 w16 :: C8 (Z_to_bv 64 fabric) ::
       C8 (Z_to_bv 64 (i + 1)) :: SV) ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 r) x9 x10 x11
                          (Z_to_bv 64 i) x13 x14 x15 x16 x17 (Z_to_bv 64 0x10392) x19 x20
                          (Z_to_bv 64 (56 * bx_n bs)) (Z_to_bv 64 (56 * (i + 1))) (Z_to_bv 64 (2 ^ 64 - 1 - r))
                          x24 x25 x26 (Z_to_bv 64 5) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x13620) fc None m' (seg_rom rsegs))).
  { induction k as [|k IH];
      intros i m' w16 x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x20 x24 x25 x26 x28 x29 x30 x31
        Hk Hi MU1 WM1 HI1 HB1 ST1 FR1; [lia|].
    clear MU WM HI HB ST FR.
    destruct (B3_bounds bs i ltac:(unfold boxreg_B2; lia) B3 Hi) as (Bb & Bn & Be).
    destruct (B3 i Hi) as (Bev & Bn2 & Bnf & Bb0 & Bbf).
    assert (TAIL : forall m4 (z1 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z19 z20 z24 z25 z26 z28 z29 z30 z31 : word),
      munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m4 -> wmono rsegs m m4 -> mem_inv rsegs m4 ->
      bytes_at rsegs m4 r bs -> stk rsegs m4 lo (bv_unsigned sp + -144) ->
      rw_cells rsegs m4 (bv_unsigned sp + -144) (C8 (Z_to_bv 64 (bx_n bs)) :: C8 (Z_to_bv 64 (bx_n bs)) :: C8 (Z_to_bv 64 (i + 1)) :: C8 (Z_to_bv 64 fabric) :: C8 (Z_to_bv 64 (i + 1)) :: SV) ->
      evt rsegs QQ (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp z5 z6 z7 (Z_to_bv 64 r) z9 z10 z11 z12 z13
                            z14 z15 z16 z17 (Z_to_bv 64 0x10392) z19 z20 (Z_to_bv 64 (56 * bx_n bs))
                            (Z_to_bv 64 (56 * (i + 1))) (Z_to_bv 64 (2 ^ 64 - 1 - r)) z24 z25 z26 (Z_to_bv 64 5)
                            z28 z29 z30 z31)
                       F (Z_to_bv 64 0x13700) fc None m4 (seg_rom rsegs))).
    { clear m' MU1 WM1 HI1 HB1 ST1 FR1.
      intros m4 z1 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z19 z20 z24 z25 z26 z28 z29 z30 z31 MU4 WM4 HI4 HB4 ST4 FR4.
      do 7 step.
      rewrite eqb_lit by lia.
      destruct (Z.eqb_spec (i + 1) (bx_n bs)) as [Eq|Ne]; cbn [negb].
      - merge5 FR4. eapply EPI; eassumption.
      - apply cell3_merge in FR4.
        replace (56 * (i + 1) + 56) with (56 * (i + 1 + 1)) by lia.
        replace (i + 2) with (i + 1 + 1) in FR4 by lia.
        eapply (IH (i + 1)); try eassumption; lia. }
    assert (IL : forall kj j m4 (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z20 z28 z29 z30 z31 : word),
      Z.of_nat kj = bx_n bs - j -> i + 1 <= j < bx_n bs ->
      munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m4 -> wmono rsegs m m4 -> mem_inv rsegs m4 ->
      bytes_at rsegs m4 r bs -> stk rsegs m4 lo (bv_unsigned sp + -144) ->
      rw_cells rsegs m4 (bv_unsigned sp + -144) (C8 (Z_to_bv 64 (bx_n bs)) :: C8 (Z_to_bv 64 (bx_n bs)) :: C8 (Z_to_bv 64 (i + 1)) :: C8 (Z_to_bv 64 fabric) :: C8 (Z_to_bv 64 (i + 1)) :: SV) ->
      evt rsegs QQ (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp z5 z6 z7 (Z_to_bv 64 r)
                            (Z_to_bv 64 (bx_base bs i + bx_nch bs i)) z10 z11 z12 z13 z14 z15 z16 z17
                            (Z_to_bv 64 0x10392) (Z_to_bv 64 (r + 56 * i)) z20 (Z_to_bv 64 (56 * bx_n bs))
                            (Z_to_bv 64 (56 * (i + 1))) (Z_to_bv 64 (2 ^ 64 - 1 - r)) (Z_to_bv 64 j)
                            (Z_to_bv 64 (56 * j)) (Z_to_bv 64 (bx_base bs i)) (Z_to_bv 64 5) z28 z29 z30 z31)
                       F (Z_to_bv 64 0x136a0) fc None m4 (seg_rom rsegs))).
    { clear m' MU1 WM1 HI1 HB1 ST1 FR1.
      induction kj as [|kj IHj];
        intros j m4 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z20 z28 z29 z30 z31 Hkj Hj4 MU4 WM4 HI4 HB4 ST4 FR4;
        [lia|].
      destruct (B3_bounds bs j ltac:(unfold boxreg_B2; lia) B3 ltac:(lia)) as (Cb & Cn & Ce).
      pose proof (B4 i j ltac:(lia) ltac:(lia) ltac:(lia)) as B4ij. unfold meets in B4ij.
      assert (JT : forall m5 (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 : word),
        munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m5 -> wmono rsegs m m5 -> mem_inv rsegs m5 ->
        bytes_at rsegs m5 r bs -> stk rsegs m5 lo (bv_unsigned sp + -144) ->
        rw_cells rsegs m5 (bv_unsigned sp + -144) (C8 (Z_to_bv 64 (bx_n bs)) :: C8 (Z_to_bv 64 (bx_n bs)) :: C8 (Z_to_bv 64 (i + 1)) :: C8 (Z_to_bv 64 fabric) :: C8 (Z_to_bv 64 (i + 1)) :: SV) ->
        evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp y5 y6 y7 (Z_to_bv 64 r)
                              (Z_to_bv 64 (bx_base bs i + bx_nch bs i)) y10 y11 y12 y13 y14 y15 y16 y17
                              (Z_to_bv 64 0x10392) (Z_to_bv 64 (r + 56 * i)) y20 (Z_to_bv 64 (56 * bx_n bs))
                              (Z_to_bv 64 (56 * (i + 1))) (Z_to_bv 64 (2 ^ 64 - 1 - r)) (Z_to_bv 64 j)
                              (Z_to_bv 64 (56 * j)) (Z_to_bv 64 (bx_base bs i)) (Z_to_bv 64 5) y28 y29 y30 y31)
                         F (Z_to_bv 64 0x136f4) fc None m5 (seg_rom rsegs))).
      { intros m5 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 MU5 WM5 HI5 HB5 ST5 FR5.
        step. step. step.
        rewrite eqb_lit by lia.
        destruct (Z.eqb_spec (56 * bx_n bs) (56 * j + 56)) as [Eq|Ne]; cbn [negb].
        - eapply TAIL; eassumption.
        - replace (56 * j + 56) with (56 * (j + 1)) by lia.
          eapply (IHj (j + 1)); try eassumption; lia. }
      assert (BCALLS : forall m5 (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 : word),
        munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m5 -> wmono rsegs m m5 -> mem_inv rsegs m5 ->
        bytes_at rsegs m5 r bs -> stk rsegs m5 lo (bv_unsigned sp + -144) ->
        rw_cells rsegs m5 (bv_unsigned sp + -144) (C8 (Z_to_bv 64 (bx_n bs)) :: C8 (Z_to_bv 64 (bx_n bs)) :: C8 (Z_to_bv 64 (i + 1)) :: C8 (Z_to_bv 64 fabric) :: C8 (Z_to_bv 64 (i + 1)) :: SV) ->
        evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp y5 y6 y7 (Z_to_bv 64 r)
                              (Z_to_bv 64 (bx_base bs i + bx_nch bs i)) y10 y11 y12 y13 y14 y15 y16 y17
                              (Z_to_bv 64 0x10392) (Z_to_bv 64 (r + 56 * i)) (Z_to_bv 64 (r + 56 * j))
                              (Z_to_bv 64 (56 * bx_n bs))
                              (Z_to_bv 64 (56 * (i + 1))) (Z_to_bv 64 (2 ^ 64 - 1 - r)) (Z_to_bv 64 j)
                              (Z_to_bv 64 (56 * j)) (Z_to_bv 64 (bx_base bs i)) (Z_to_bv 64 5) y28 y29 y30 y31)
                         F (Z_to_bv 64 0x136cc) fc None m5 (seg_rom rsegs))).
      { intros m5 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 MU5 WM5 HI5 HB5 ST5 FR5.
        pose proof (bytes_at_bsub_u m5 r bs (56 * i) 6 HB5 ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)) as HMi.
        fold (bx_mac bs i) in HMi.
        pose proof (ro_bytes_at rsegs m5 0x10392 zero6 HI5 ltac:(lia) ltac:(cbn; lia) zero_ro_u) as HZ5.
        destruct (memcmp_model_total (bx_mac bs i) zero6 6) as [v1 V1];
          [rewrite (bsub_length6 bs i HL ltac:(lia)); lia | cbn; lia |].
        destruct (memcmp_eq _ _ 6 v1 (bsub_length6 bs i HL ltac:(lia)) zero6_length V1) as [V1iff V1r].
        step. step. step. step.
        eapply evt_cut.
        { eapply BCMP.
          - rewrite unsigned_lit by lia. exact HMi.
          - change (bv_unsigned (Z_to_bv 64 66450)) with 0x10392. exact HZ5.
          - change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat. exact V1.
          - exact HI5. }
        intros ms' Hp. unfold memcmp_post in Hp.
        destruct Hp as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m6 & -> & MU6 & WM6 & HI6 & _).
        replace (ret_pc (Z_to_bv 64 0x136dc)) with (Z_to_bv 64 0x136dc) by (apply bv_eq; vm_compute; reflexivity).
        pose proof (munch_trans _ m m5 m6 MU5 (munch_weaken [] _ m5 m6 (fun x _ => I) MU6)) as MU7.
        pose proof (wmono_trans rsegs m m5 m6 WM5 WM6) as WM7.
        pose proof (bytes_at_transport rsegs [] m5 m6 r bs HB5 MU6 I) as HB7.
        pose proof (rw_cells_transport rsegs [] m5 m6 _ _ FR5 MU6 WM6 I) as FR7.
        pose proof (stk_transport rsegs [] m5 m6 lo _ ST5 MU6 WM6 (fun x _ => or_introl I)) as ST7.
        step. rewrite bv_v_zero by lia.
        destruct (Z.eqb_spec v1 0) as [V10|V1n]; cbv beta iota.
        - eapply JT; eassumption.
        - pose proof (bytes_at_bsub_u m6 r bs (56 * i) 6 HB7 ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)) as HMi6.
          fold (bx_mac bs i) in HMi6.
          pose proof (bytes_at_bsub_u m6 r bs (56 * j) 6 HB7 ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)) as HMj6.
          fold (bx_mac bs j) in HMj6.
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
            - rewrite unsigned_lit by lia. exact HMi6.
            - rewrite unsigned_lit by lia. exact HMj6.
            - change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat. exact V2.
            - exact HI6. }
          intros ms' Hp. unfold memcmp_post in Hp.
          destruct Hp as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m7 & -> & MU8 & WM8 & HI8 & _).
          replace (ret_pc (Z_to_bv 64 0x136f0)) with (Z_to_bv 64 0x136f0) by (apply bv_eq; vm_compute; reflexivity).
          pose proof (munch_trans _ m m6 m7 MU7 (munch_weaken [] _ m6 m7 (fun x _ => I) MU8)) as MU9.
          pose proof (wmono_trans rsegs m m6 m7 WM7 WM8) as WM9.
          pose proof (bytes_at_transport rsegs [] m6 m7 r bs HB7 MU8 I) as HB9.
          pose proof (rw_cells_transport rsegs [] m6 m7 _ _ FR7 MU8 WM8 I) as FR9.
          pose proof (stk_transport rsegs [] m6 m7 lo _ ST7 MU8 WM8 (fun x _ => or_introl I)) as ST9.
          step. rewrite bv_v_zero by lia.
          destruct (Z.eqb_spec v2 0) as [V20|_]; [exfalso; exact (V2n V20)|]. cbv beta iota.
          eapply JT; eassumption. }
      pose proof (rd4_read_u m4 r bs (56 * j + 8) HB4 ltac:(lia) ltac:(rewrite HL; lia)) as RBj.
      pose proof (rd4_read_u m4 r bs (56 * j + 12) HB4 ltac:(lia) ltac:(rewrite HL; lia)) as RNj.
      step. rewrite ltu_lit by lia. if_false.
      step. rewrite ltu_lit by lia. if_false.
      step. step.
      rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_base bs j).
      step.
      rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_nch bs j).
      step. step. rewrite swrap_add by lia.
      step. rewrite eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb].
      step. rewrite lts_lit by lia.
      destruct (Z.ltb_spec (bx_base bs j) (bx_base bs i + bx_nch bs i)) as [Lt2|Ge2]; cbn [negb].
      - step. rewrite swrap_addi by lia.
        step. rewrite lts_lit by lia. if_false.
        eapply BCALLS; eassumption.
      - eapply BCALLS; eassumption. }
    step. step. step.
    rewrite (mul56 i) by lia.
    step. rewrite ltu_lit by lia. if_false.
    step.
    pose proof (rd4_read_u m' r bs (56 * i + 12) HB1 ltac:(lia) ltac:(rewrite HL; lia)) as RNi.
    pose proof (rd4_read_u m' r bs (56 * i + 8) HB1 ltac:(lia) ltac:(rewrite HL; lia)) as RBi.
    step.
    rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_nch bs i).
    step. step. rewrite lts_lit by lia. if_false.
    step. step. step. step.
    rewrite swrap_addi by lia.
    rewrite (Z_to_bv_neg_wrap (bx_nch bs i + -41)) by lia. rewrite (Z_to_bv_neg_wrap (-39)) by lia.
    rewrite ltu_lit by lia. if_false.
    step. step.
    rewrite (unsigned_lit (bx_nch bs i)) by lia. rewrite (land1_even (bx_nch bs i) ltac:(lia) Bev). if_false.
    step.
    rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_base bs i).
    step. rewrite lts_lit by lia. if_false.
    step. rewrite swrap_add by lia.
    step.
    step. rewrite eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb].
    step. step. rewrite lts_lit by lia. if_false.
    destruct (memchr_name (r + 56 * i + 24) (bx_name bs i) (bsub_length32 bs i HL ltac:(lia)) (B6 i Hi))
      as [MOK [jm [Hjm MRES]]].
    pose proof (bytes_at_bsub_u m' r bs (56 * i + 24) 32 HB1 ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)) as HNm.
    replace (r + (56 * i + 24)) with (r + 56 * i + 24) in HNm by lia. fold (bx_name bs i) in HNm.
    step. step. step. step.
    eapply evt_cut.
    { eapply MEMCHR.
      - rewrite unsigned_lit by lia. exact HNm.
      - rewrite unsigned_lit by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
        change (bv_unsigned (Z_to_bv 64 32)) with 32. exact MOK.
      - exact HI1. }
    intros ms' Hp. unfold memchr_post in Hp.
    destruct Hp as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & HI2 & _).
    replace (ret_pc (Z_to_bv 64 0x13684)) with (Z_to_bv 64 0x13684) by (apply bv_eq; vm_compute; reflexivity).
    rewrite (unsigned_lit (r + 56 * i + 24)) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    change (bv_unsigned (Z_to_bv 64 32)) with 32. rewrite MRES.
    pose proof (munch_trans _ m m' m2 MU1 (munch_weaken [] _ m' m2 (fun x _ => I) MU2)) as MU3.
    pose proof (wmono_trans rsegs m m' m2 WM1 WM2) as WM3.
    pose proof (bytes_at_transport rsegs [] m' m2 r bs HB1 MU2 I) as HB3.
    pose proof (rw_cells_transport rsegs [] m' m2 _ _ FR1 MU2 WM2 I) as FR3.
    pose proof (stk_transport rsegs [] m' m2 lo _ ST1 MU2 WM2 (fun x _ => or_introl I)) as ST3.
    clear MU1 WM1 HB1 FR1 ST1 MU2 WM2.
    step. rewrite eqb_lit by lia. if_false.
    step. step. step. step.
    rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (i + 1) (bx_n bs)) as [Lt|Ge]; cbn [negb].
    2:{ eapply TAIL; eassumption. }
    step. step.
    eapply (IL (Z.to_nat (bx_n bs - (i + 1))) (i + 1)); try eassumption; lia. }
  eapply (OL (Z.to_nat (bx_n bs)) 0); try eassumption; lia.
Qed.