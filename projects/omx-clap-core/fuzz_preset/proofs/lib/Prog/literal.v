From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjIn strlen_c bcmp_c literal_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Lemma memcmp_model_range : forall n l r v, memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v H.
  - cbn in H. injection H as <-. lia.
  - destruct l as [|a l], r as [|b r]; cbn in H; try discriminate.
    destruct (bv_unsigned a =? bv_unsigned b) eqn:E.
    + exact (IH l r v H).
    + injection H as <-. pose proof (byte_range a). pose proof (byte_range b). lia.
Qed.

Lemma memcmp_model_zero : forall n l r v, memcmp_model l r n = Some v ->
  (v = 0 <-> firstn n l = firstn n r).
Proof.
  induction n as [|n IH]; intros l r v H.
  - cbn in H. injection H as <-. cbn. split; intros; reflexivity.
  - destruct l as [|a l], r as [|b r]; cbn in H; try discriminate.
    cbn [firstn].
    destruct (bv_unsigned a =? bv_unsigned b) eqn:E.
    + apply Z.eqb_eq in E. assert (a = b) by (apply bv_eq; exact E). subst b.
      rewrite (IH l r v H). split; [intros ->; reflexivity | intros Hc; injection Hc; auto].
    + apply Z.eqb_neq in E. injection H as <-. split.
      * intros Hv. exfalso. lia.
      * intros Hc. injection Hc as Ha _. subst b. exfalso. apply E. reflexivity.
Qed.

Lemma bytes_at_skipn : forall m a bs k, bytes_at rsegs m a bs -> (k <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia. exact H.
Qed.

Lemma eqb0_small : forall z, -256 < z < 256 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = (z =? 0).
Proof.
  intros z Hz. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec z 0) as [E|E]; [subst z; reflexivity|].
  apply Z.eqb_neq. intro E2. apply E. Z.div_mod_to_equations. lia.
Qed.

Theorem literal_holds : strlen_contract -> bcmp_contract -> literal_contract.
Proof.
  intros HSL HBC.
  unfold literal_contract, LITERAL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    q text len p d txt w cw slack ty v lo E0 E1 E2 E3 PJ W0 W1 RO NZ SL TY V0 V8 VW VD ST LO SD MI.
  subst a0 a1 a2 a3.
  pose proof (pj_in_ok_bounds rsegs m q text len p d txt PJ) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  cbn [disjoint_from] in VD, SD.
  pose proof VW as (VB1 & VB2 & _).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 64%nat ST.
  do 14 step.
  let mm := cur_mem in
  assert (RW : bytes_at rsegs mm (bv_unsigned (Z_to_bv 64 w)) (cw ++ Z_to_bv 8 0 :: slack))
    by (rewrite unsigned_lit by lia; apply ro_bytes_at; [exact MI | lia | rewrite length_app; cbn [length]; lia | exact RO]).
  assert (SL' : (- (bv_unsigned (Z_to_bv 64 w) + Z.of_nat (length cw) + 1)) mod 8 <= Z.of_nat (length slack))
    by (rewrite unsigned_lit by lia; exact SL).
  step.
  call (HSL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cw slack RW NZ SL' MI).
  try (lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end).
  let mm := cur_mem in
  assert (PJx : pj_in_ok rsegs mm q text len p d txt)
    by (eapply pj_in_ok_transport; [exact PJ | exact MU | exact WM | cbn [disjoint_from]; lia | cbn [disjoint_from]; lia]).
  pose proof (pj_in_ok_rd_p rsegs _ _ _ _ _ _ _ PJx) as RQ.
  pose proof (pj_in_ok_rd_end rsegs _ _ _ _ _ _ _ PJx) as RE.
  step. step. step. step. step. step.
  assert (LC : Z.of_nat (length cw) < 2 ^ 64) by lia.
  if_cases HC; rewrite bv_ltu_Z, (unsigned_lit (text + len)), (unsigned_lit p) in HC by lia;
    rewrite (unsigned_lit (text + len - p)), (unsigned_lit (Z.of_nat (length cw))) in HC by lia.
  - apply Z.ltb_lt in HC.
    do 11 step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [|exact MU]; intros z Hz; cbn [outside] in Hz |- *; tauto|].
    split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    right. split; [intros [Hl _]; lia|]. split; [reflexivity|]. split; [exact MU|exact PJx].
  - apply Z.ltb_ge in HC.
    set (k := Z.to_nat (p - text)).
    assert (Kp : text + Z.of_nat k = p) by (unfold k; lia).
    pose proof PJx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PT & _ & _).
    pose proof (bytes_at_skipn _ _ _ k PT ltac:(unfold k; lia)) as PS. rewrite Kp in PS.
    assert (L1 : (length cw <= length (skipn k txt))%nat) by (rewrite length_skipn; unfold k; lia).
    assert (L2 : (length cw <= length (cw ++ Z_to_bv 8 0 :: slack))%nat) by (rewrite length_app; cbn [length]; lia).
    destruct (memcmp_model_total _ _ _ L1 L2) as [vr VR].
    pose proof (memcmp_model_range _ _ _ _ VR) as VRR.
    pose proof (memcmp_model_zero _ _ _ _ VR) as VRZ.
    let mm := cur_mem in
    assert (P1 : bytes_at rsegs mm (bv_unsigned (Z_to_bv 64 p)) (skipn k txt)) by (rewrite unsigned_lit by lia; exact PS);
    assert (P2 : bytes_at rsegs mm (bv_unsigned (Z_to_bv 64 w)) (cw ++ Z_to_bv 8 0 :: slack))
      by (rewrite unsigned_lit by lia; apply ro_bytes_at; [exact MI | lia | rewrite length_app; cbn [length]; lia | exact RO]).
    assert (P3 : memcmp_model (skipn k txt) (cw ++ Z_to_bv 8 0 :: slack) (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (length cw))))) = Some vr)
      by (rewrite unsigned_lit by lia; rewrite Nat2Z.id; exact VR).
    do 4 step.
    call (HBC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ vr P1 P2 P3 MI).
    try (lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end).
    step.
    rewrite firstn_app_len in VRZ by reflexivity.
    let mm := cur_mem in
    assert (PJy : pj_in_ok rsegs mm q text len p d txt)
      by (eapply pj_in_ok_transport; [exact PJ | exact MU | exact WM | cbn [disjoint_from]; lia | cbn [disjoint_from]; lia]).
    if_cases HZ; rewrite eqb0_small in HZ by lia.
    + apply negb_true_iff, Z.eqb_neq in HZ.
      do 11 step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity|].
      split; [eapply munch_weaken; [|exact MU]; intros z Hz; cbn [outside] in Hz |- *; tauto|].
      split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      right. split; [intros [_ Hf]; apply HZ, VRZ; exact Hf|]. split; [reflexivity|]. split; [exact MU|exact PJy].
    + apply negb_false_iff, Z.eqb_eq in HZ. apply VRZ in HZ.
      pose proof (pj_in_ok_store_p rsegs _ _ _ _ _ _ _ PJy) as HSq.
      let mm := cur_mem in
      assert (MUf : munch [(bv_unsigned sp + -64, bv_unsigned sp); (q, q + 8); (v, v + 4)] m mm)
        by (eapply munch_weaken; [|exact MU]; intros z Hz; cbn [outside] in Hz |- *; tauto).
      step. step. step.
      let mm := cur_mem in remember mm as m2 eqn:Hm2.
      assert (PJ2 : pj_in_ok rsegs m2 q text len (p + Z.of_nat (length cw)) d txt)
        by (subst m2; eapply pj_in_ok_set_p; [exact PJy | lia]).
      assert (MI2 : mem_inv rsegs m2) by (subst m2; apply mem_inv_store; [exact MI | rewrite length_le8; exact HSq]).
      assert (MU2 : munch [(bv_unsigned sp + -64, bv_unsigned sp); (q, q + 8); (v, v + 4)] m m2)
        by (subst m2; apply munch_write; [exact MUf | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]).
      assert (WM2 : wmono rsegs m m2) by (subst m2; apply wmono_write; exact WM).
      assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -64)) by (subst m2; apply stk_write; [exact ST | lia | rewrite length_le8; lia]).
      assert (HSv : store_ok rsegs m2 (wa v) 4 = true).
      { subst m2. rewrite <- (Z.add_0_r v) at 1. apply (wr_at_store_ok rsegs _ v 4 0 4); [apply wr_at_write; exact VW | lia | cbn; lia]. }
      lazymatch type of FR with rw_cells _ _ ?A ?cs =>
        assert (FR2 : rw_cells rsegs m2 A cs)
          by (subst m2; apply rw_cells_frame; [exact FR | lia | rewrite length_le8; lia | rewrite length_le8; cbn [cells_size csize Nat.add]; lia])
      end.
      clear FR ST MU MUf WM MI PJy HSq Hm2 VW.
      step.
      let mm := cur_mem in remember mm as m3 eqn:Hm3.
      assert (PJ3 : pj_in_ok rsegs m3 q text len (p + Z.of_nat (length cw)) d txt)
        by (subst m3; apply pj_in_ok_write_other; [exact PJ2 | lia | rewrite length_le4; lia | rewrite length_le4; cbn [disjoint_from]; lia]).
      assert (BV : bytes_at rsegs m3 v (le4 (Z_to_bv 64 ty))) by (subst m3; apply bytes_at_write_same; rewrite ?length_le4; lia).
      assert (MI3 : mem_inv rsegs m3) by (subst m3; apply mem_inv_store; [exact MI2 | rewrite length_le4; exact HSv]).
      assert (MU3 : munch [(bv_unsigned sp + -64, bv_unsigned sp); (q, q + 8); (v, v + 4)] m m3)
        by (subst m3; apply munch_write; [exact MU2 | lia | rewrite length_le4; lia | cbn [inside]; rewrite length_le4; lia]).
      assert (WM3 : wmono rsegs m m3) by (subst m3; apply wmono_write; exact WM2).
      assert (ST : stk rsegs m3 lo (bv_unsigned sp + -64)) by (subst m3; apply stk_write; [exact ST2 | lia | rewrite length_le4; lia]).
      lazymatch type of FR2 with rw_cells _ _ ?A ?cs =>
        assert (FR : rw_cells rsegs m3 A cs)
          by (subst m3; apply rw_cells_frame; [exact FR2 | lia | rewrite length_le4; lia | rewrite length_le4; cbn [cells_size csize Nat.add]; lia])
      end.
      clear FR2 ST2 MU2 WM2 MI2 PJ2 HSv Hm3.
      do 11 step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity|].
      split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST|].
      left. split; [split; [lia | exact HZ]|]. split; [reflexivity|]. split; [exact PJ3 | exact BV].
Qed.
