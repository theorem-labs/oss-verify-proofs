From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcLib RcFin RcFinLib RcRec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import
  reac_ctrl_record_cksum_stamp_c reac_ctrl_block_cksum_stamp_c ctrl_finish_c.
Import ListNotations.
Open Scope Z_scope.

Lemma rcf_stampck : forall B o n, 0 <= o -> 1 <= n -> o + n <= 32 -> length B = 32%nat ->
  stampck (firstn (Z.to_nat (n - 1)) (skipn (Z.to_nat o) B)) = (- rsum B o (n - 1)) mod 128.
Proof.
  intros B o n Ho Hn Hon Hl. unfold stampck, rsum.
  rewrite length_firstn, length_skipn.
  replace (Nat.min (Z.to_nat (n - 1)) (length B - Z.to_nat o)) with (Z.to_nat (n - 1)) by lia.
  rewrite rcf_psum_firstn by lia. reflexivity.
Qed.

Section U.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (p : Z).
  Hypothesis HBS : reac_ctrl_block_cksum_stamp_contract.
  Hypothesis Hp : 0 < p.
  Hypothesis Hp50 : p + 50 <= 2^64.

  Definition Qt (mm : word -> option byte) (bs : list byte) : machine_state -> Prop :=
    fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(p + 18 + 31, p + 18 + 32)] mm m' /\ wmono rsegs mm m' /\ (mem_inv rsegs mm -> mem_inv rsegs m')
      /\ rw_cells rsegs m' (p + 18) [CB 32 (stamp32 bs)].

  Lemma tail : forall mm bs yra y0 y1 y2 y3 y4 y5 y6 y7,
    length bs = 32%nat -> bytes_at rsegs mm (p + 18) bs -> wr_at rsegs mm (p + 18) 32 ->
    bytes_at rsegs mm (bv_unsigned sp + -8) (le8 ra) -> bytes_at rsegs mm (bv_unsigned sp + -16) (le8 s0) ->
    evt rsegs (Qt mm bs)
      (MS (mkR yra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 p) s1 y0 y1 y2 y3 y4 y5 y6 y7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1496c) fc None mm (seg_rom rsegs)).
  Proof.
    intros mm bs yra y0 y1 y2 y3 y4 y5 y6 y7 Hl HB HW Ha Hs.
    assert (RDa : ov_read_bytes rsegs mm (wa (bv_unsigned sp + -8)) 8 = Some (le8 ra)).
    { replace (bv_unsigned sp + -8) with (bv_unsigned sp + -8 + 0) by lia.
      rewrite (bytes_at_read rsegs mm _ (le8 ra) 0 8 Ha) by (try rewrite length_le8; lia). reflexivity. }
    assert (RDs : ov_read_bytes rsegs mm (wa (bv_unsigned sp + -16)) 8 = Some (le8 s0)).
    { replace (bv_unsigned sp + -16) with (bv_unsigned sp + -16 + 0) by lia.
      rewrite (bytes_at_read rsegs mm _ (le8 s0) 0 8 Hs) by (try rewrite length_le8; lia). reflexivity. }
    step.
    rewrite (rcf_eqb p 0) by lia. replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step. step.
    rewrite (rcf_ltu_neg_l p (-19)) by lia.
    replace (2^64 + -19 <? p) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step. step. step. step.
    step.
    eapply evt_mono; [eapply HBS with (q := p + 18) (B := bs);
                      [lia | lia | reflexivity | apply rcf_rw32; assumption] |].
    intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & a6' & m' & -> & MU & WM & MI & RW & _).
    unfold Qt. do 9 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact RW.
  Qed.
End U.

Theorem ctrl_finish_holds : reac_ctrl_record_cksum_stamp_contract -> reac_ctrl_block_cksum_stamp_contract ->
  ctrl_finish_contract.
Proof.
  intros HRS HBS. unfold ctrl_finish_contract, CTRL_FINISH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p f c o n row B -> -> ST DJf DJp Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  pose proof ST as (ST1 & ST2 & _).
  assert (SP16 : 16 <= bv_unsigned sp) by lia.
  assert (HS1 : store_ok rsegs m (wa (bv_unsigned sp + -8)) 8 = true)
    by (apply (rcf_stk_store_ok rsegs m (bv_unsigned sp - 16) (bv_unsigned sp)); [exact ST | lia | cbn; lia]).
  pose proof (stk_write rsegs m (bv_unsigned sp - 16) (bv_unsigned sp) (bv_unsigned sp + -8) (le8 ra) ST
                ltac:(lia) ltac:(rewrite length_le8; lia)) as ST'.
  assert (HS2 : store_ok rsegs (write_to_mem m (Z_to_bv 64 (bv_unsigned sp + -8)) (le8 ra))
                  (wa (bv_unsigned sp + -16)) 8 = true)
    by (apply (rcf_stk_store_ok rsegs _ (bv_unsigned sp - 16) (bv_unsigned sp)); [exact ST' | lia | cbn; lia]).
  step. step. step. clear HS1 HS2 ST'.
  destruct (rcf_frame16 rsegs m (bv_unsigned sp) (fin_w c o n p) ra s0 ST)
    as (MU1 & WM1 & MI1 & STm1 & FRa & FRs & TB1 & TW1).
  pose proof (TB1 f row HR ltac:(rewrite Hrl; lia)) as HR1.
  remember (write_to_mem (write_to_mem m (Z_to_bv 64 (bv_unsigned sp + -8)) (le8 ra))
              (Z_to_bv 64 (bv_unsigned sp + -16)) (le8 s0)) as m1 eqn:Em1.
  pose proof (bytes_at_bound rsegs m f row HR) as HRB.
  pose proof (rd_byte rsegs m1 f row 20 HR1 ltac:(lia)) as RD20. change (Z.of_nat 20) with 20 in RD20.
  pose proof (rd_byte rsegs m1 f row 18 HR1 ltac:(lia)) as RD18. change (Z.of_nat 18) with 18 in RD18.
  pose proof (rd_byte rsegs m1 f row 19 HR1 ltac:(lia)) as RD19. change (Z.of_nat 19) with 19 in RD19.
  assert (Z20 : zxb (nth 20 row (Z_to_bv 8 0)) = Z_to_bv 64 c) by (unfold zxb; rewrite <- Hc; reflexivity).
  assert (Z18 : zxb (nth 18 row (Z_to_bv 8 0)) = Z_to_bv 64 o) by (unfold zxb; rewrite <- Ho; reflexivity).
  assert (Z19 : zxb (nth 19 row (Z_to_bv 8 0)) = Z_to_bv 64 n) by (unfold zxb; rewrite <- Hn; reflexivity).
  pose proof (byte_range (nth 20 row (Z_to_bv 8 0))) as BRc.
  pose proof (byte_range (nth 18 row (Z_to_bv 8 0))) as BRo.
  pose proof (byte_range (nth 19 row (Z_to_bv 8 0))) as BRn.
  unfold ubat in Hc, Ho, Hn.
  assert (Hcases : c = 0 \/ c = 1 \/ c = 2) by lia.
  assert (L7 : Z.land f 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact Hf8).
  step. step.
  rewrite (unsigned_lit f) by lia. rewrite L7. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  step. step. rewrite Z20. step. step.
  rewrite (rcf_eqb c 1) by lia.
  destruct Hcases as [C | [C | C]].
  - replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step. step.
    rewrite (rcf_eqb c 2) by lia. replace (c =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. cbv iota.
    assert (RDa : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + -8)) 8 = Some (le8 ra)).
    { replace (bv_unsigned sp + -8) with (bv_unsigned sp + -8 + 0) by lia.
      rewrite (bytes_at_read rsegs m1 _ (le8 ra) 0 8 FRa) by (try rewrite length_le8; lia). reflexivity. }
    assert (RDs : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + -16)) 8 = Some (le8 s0)).
    { replace (bv_unsigned sp + -16) with (bv_unsigned sp + -16 + 0) by lia.
      rewrite (bytes_at_read rsegs m1 _ (le8 s0) 0 8 FRs) by (try rewrite length_le8; lia). reflexivity. }
    step. step. step. step.
    apply evt_done. cbv beta. do 9 eexists. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact STm1|].
    intros [H | H]; exfalso; lia.
  - replace (c =? 1) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
    destruct (rcf_rw32_inv rsegs m (p + 18) B (HRW ltac:(lia))) as (Hl & HB & HW).
    pose proof (TB1 (p + 18) B HB ltac:(rewrite Hl; lia)) as HB1.
    pose proof (TW1 (p + 18) 32 HW) as HW1.
    eapply evt_mono; [apply (tail ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p
                               HBS Hp Hp50 m1 B _ _ _ _ _ _ _ _ _ Hl HB1 HW1 FRa FRs)|].
    intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MU & WM & MI & RW). cbv beta.
    rewrite C. change (fin_w 1 o n p) with [(p + 49, p + 50)].
    rewrite C in MU1. change (fin_w 1 o n p) with [(p + 49, p + 50)] in MU1.
    do 9 eexists. split; [reflexivity|].
    split.
    { apply (munch_trans _ m m1 m' MU1). apply rcf_munch_in with (1 := MU).
      intros x Hx. cbn [outside] in Hx. lia. }
    split; [exact (wmono_trans rsegs m m1 m' WM1 WM)|].
    split; [intros HI; exact (MI (MI1 HI))|].
    split.
    { apply (stk_transport_disjoint rsegs [(p + 18 + 31, p + 18 + 32)] m1 m' _ _ STm1 MU WM).
      cbn [disjoint_from]. lia. }
    intros _.
    split; [rewrite rcf_fin1; exact RW|].
    split; [apply rcf_closes_fin; [exact Hl | left; reflexivity | intros H; discriminate H]|].
    intros HC. apply rcf_fin_same; [exact Hl | left; reflexivity | intros H; discriminate H | exact HC].
  - replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step. step.
    rewrite (rcf_eqb c 2) by lia. replace (c =? 2) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. cbv iota.
    destruct (Hrec C) as [Hn2 Hon].
    destruct (rcf_rw32_inv rsegs m (p + 18) B (HRW ltac:(lia))) as (Hl & HB & HW).
    pose proof (TB1 (p + 18) B HB ltac:(rewrite Hl; lia)) as HB1.
    pose proof (TW1 (p + 18) 32 HW) as HW1.
    step.
    rewrite (rcf_eqb p 0) by lia. replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step. step.
    rewrite (rcf_ltu_neg p (-18)) by lia.
    replace (p <? 2^64 + -18) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
    step. rewrite Z18. step. step. step.
    rewrite (unsigned_lit (p + 18)) by lia. rewrite (zb_lxor_ones (p + 18)) by lia.
    rewrite (rcf_ltu (18446744073709551615 - (p + 18)) o) by lia.
    replace (18446744073709551615 - (p + 18) <? o) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step. rewrite Z19. step. step.
    assert (Hbsr : bytes_at rsegs m1 (p + 18 + o) (firstn (Z.to_nat (n - 1)) (skipn (Z.to_nat o) B))).
    { pose proof (rcf_bytes_sub rsegs m1 (p + 18) B (Z.to_nat o) (Z.to_nat (n - 1)) ltac:(lia) HB1) as H.
      replace (p + 18 + Z.of_nat (Z.to_nat o)) with (p + 18 + o) in H by lia. exact H. }
    assert (Hwr : wr_at rsegs m1 (p + 18 + o + n - 1) 1).
    { replace (p + 18 + o + n - 1) with (p + 18 + (o + n - 1)) by lia.
      apply (rcf_wr_sub rsegs m1 (p + 18) 32 1 HW1); lia. }
    eapply evt_cut;
      [eapply HRS with (bs := firstn (Z.to_nat (n - 1)) (skipn (Z.to_nat o) B));
       rewrite ?(unsigned_lit (p + 18 + o)) by lia; rewrite ?(unsigned_lit n) by lia;
       [lia | lia | lia | rewrite length_firstn, length_skipn; lia | exact Hbsr | exact Hwr] |].
    intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & -> & HBr & _ & _ & MU2 & WM2 & MI2).
    rewrite (unsigned_lit (p + 18 + o)), (unsigned_lit n) in HBr, MU2 by lia.
    replace (ret_pc (Z_to_bv 64 84332)) with (Z_to_bv 64 84332) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    replace (p + 18 + o + n - 1) with (p + 18 + Z.of_nat (Z.to_nat (o + n - 1))) in HBr, MU2 by lia.
    replace (p + 18 + o + n) with (p + 18 + Z.of_nat (Z.to_nat (o + n - 1)) + 1) in MU2 by lia.
    pose proof (rcf_bytes_munch1 rsegs m1 m2 (p + 18) B (Z.to_nat (o + n - 1)) _ HB1 ltac:(lia) MU2 HBr) as HB2.
    rewrite (rcf_stampck B o n) in HB2 by lia.
    assert (HlR : length (rstamp B o n) = 32%nat) by (apply rcf_rstamp_len; lia).
    pose proof (wr_at_transport rsegs m1 m2 (p + 18) 32 HW1 WM2) as HW2.
    pose proof (bytes_at_transport rsegs _ m1 m2 _ _ FRa MU2
                  ltac:(cbn [disjoint_from]; rewrite length_le8; split; [lia | exact I])) as FRa2.
    pose proof (bytes_at_transport rsegs _ m1 m2 _ _ FRs MU2
                  ltac:(cbn [disjoint_from]; rewrite length_le8; split; [lia | exact I])) as FRs2.
    pose proof (stk_transport_disjoint rsegs _ m1 m2 _ _ STm1 MU2 WM2
                  ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STm2.
    eapply evt_mono; [apply (tail ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p
                               HBS Hp Hp50 m2 (rstamp B o n) _ _ _ _ _ _ _ _ _ HlR HB2 HW2 FRa2 FRs2)|].
    intros ms' (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m3 & -> & MU3 & WM3 & MI3 & RW3). cbv beta.
    rewrite C in MU1 |- *.
    change (fin_w 2 o n p) with [(p + 18 + o + n - 1, p + 18 + o + n); (p + 49, p + 50)] in MU1 |- *.
    do 9 eexists. split; [reflexivity|].
    split.
    { apply (munch_trans _ m m2 m3); [apply (munch_trans _ m m1 m2 MU1)|].
      - apply rcf_munch_in with (1 := MU2). intros x Hx. cbn [outside] in Hx. lia.
      - apply rcf_munch_in with (1 := MU3). intros x Hx. cbn [outside] in Hx. lia. }
    split; [exact (wmono_trans rsegs m m2 m3 (wmono_trans rsegs m m1 m2 WM1 WM2) WM3)|].
    split; [intros HI; exact (MI3 (MI2 (MI1 HI)))|].
    split.
    { apply (stk_transport_disjoint rsegs [(p + 18 + 31, p + 18 + 32)] m2 m3 _ _ STm2 MU3 WM3).
      cbn [disjoint_from]. split; [lia | exact I]. }
    intros _.
    split; [rewrite rcf_fin2; exact RW3|].
    split; [apply rcf_closes_fin; [exact Hl | right; reflexivity | intros _; split; [lia | split; lia]]|].
    intros HC. apply rcf_fin_same; [exact Hl | right; reflexivity | intros _; split; [lia | split; lia] | exact HC].
Qed.