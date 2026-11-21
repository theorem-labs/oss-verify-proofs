(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Zh_kit Z_infl_iface Z_infl_pure2 Z_itab_kit Z_itab_defs Z_itab_ldefs Z_ukit Z_itab_exit Z_itab_head Z_itab_next Z_itab_sub Z_itab_init Z_itab_sort Z_itab_offs Z_itab_kraft.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_itab_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees ItableModel ItableModel2 ItableModel3 RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].
Lemma mx_next : forall (M : Z) cnt n k k', M = find_max_rec cnt (S n) k -> 1 <= k -> k' = k - 1 -> arr_get cnt k = 0 -> M = find_max_rec cnt n k'.
Proof.
  intros M cnt n k k' H Hk -> Hz. rewrite H. cbn [find_max_rec]. rewrite Hz, Z.eqb_refl.
  replace (1 <=? k) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
Lemma mx_stop : forall (M : Z) cnt n k, M = find_max_rec cnt (S n) k -> 1 <= k -> arr_get cnt k <> 0 -> M = k.
Proof.
  intros M cnt n k H Hk Hz. rewrite H. cbn [find_max_rec]. replace (arr_get cnt k =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz).
  rewrite andb_false_r. reflexivity.
Qed.
Lemma mx_zero : forall (M : Z) cnt n, M = find_max_rec cnt n 0 -> M = 0.
Proof. intros M cnt [|n] H; rewrite H; reflexivity. Qed.
Lemma fm_next : forall (M : Z) cnt max n mn mn', M = find_min_rec cnt max (S n) mn -> mn < max -> mn' = mn + 1 -> arr_get cnt mn = 0 -> M = find_min_rec cnt max n mn'.
Proof.
  intros M cnt max n mn mn' H Hm -> Hz. rewrite H. cbn [find_min_rec]. rewrite Hz, Z.eqb_refl.
  replace (mn <? max) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma fm_stop : forall (M : Z) cnt max n mn, M = find_min_rec cnt max (S n) mn -> arr_get cnt mn <> 0 -> M = mn.
Proof.
  intros M cnt max n mn H Hz. rewrite H. cbn [find_min_rec]. replace (arr_get cnt mn =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz).
  rewrite andb_false_r. reflexivity.
Qed.
Lemma fm_end : forall (M : Z) cnt max n, M = find_min_rec cnt max n max -> M = max.
Proof. intros M cnt max [|n] H; rewrite H; cbn [find_min_rec]; [reflexivity|]. rewrite Z.ltb_irrefl. reflexivity. Qed.
Lemma itab_ldbits : forall X m Q (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  isA m (tx_L X) (tx_s X) -> 0 <= tx_bits X <= 15 ->
  evt usegs Q (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 (wz (tx_bits X))
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz (0x21ddc + 4)) (tx_fc X) None m (seg_rom usegs)) ->
  evt usegs Q (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz 0x21ddc) (tx_fc X) None m (seg_rom usegs)).
Proof.
  intros until x31; intros GA Rb H. unfold isA, isA_cells in GA.
  assert (E14 : wz (tx_bitsA X) = wz (il_As (tx_L X) + (if tx_dsel X then 140 else 136))) by reflexivity.
  assert (E17 : tx_bits X = (if tx_dsel X then is_distbits (tx_s X) else is_lenbits (tx_s X))) by reflexivity.
  rewrite E17 in H, Rb. revert H. rewrite E14. destruct (tx_dsel X); intros H; zs; exact H.
Qed.
Section MaxMin.
Variables (X : itx) (cnt : arr) (m : mem).
Definition kraft_K : Prop :=
  forall (max min root : Z) (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word),
  itm_max cnt = max -> itm_min cnt max = min -> itm_root (tx_bits X) max min = root -> 1 <= max <= 15 -> 1 <= min <= 15 -> 1 <= root <= 15 ->
  evt usegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) (wz max) (wz min) (wz (arr_get cnt 15)) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) (wz (-1)) (wz root)
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz (arr_get cnt 1)) (wz (if max =? 1 then 0 else 1)) (wz 2) x31)
        (tx_F X) (wz PC_IT_KRAFT) (tx_fc X) None m (seg_rom usegs)).
Definition nosym_K : Prop :=
  forall (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  itm_max cnt = 0 ->
  evt usegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_NOSYM) (tx_fc X) None m (seg_rom usegs)).
Hypothesis CNT : u8arr usegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16)).
Hypothesis XO : itx_ok X.
Hypothesis TYC : ty16 cnt.
Hypothesis LC : arr_len cnt = 16.
Hypothesis Rb : 0 <= tx_bits X <= 15.
Hypothesis KR : kraft_K.
Hypothesis KN : nosym_K.
Lemma itab_minj : forall (max min root0 : Z) (x1 x8 x9 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  itm_max cnt = max -> itm_min cnt max = min -> 2 <= max <= 15 -> 1 <= min <= max -> root0 = (if max <? tx_bits X then max else tx_bits X) ->
  evt usegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) (wz max) (wz min) (wz (arr_get cnt 15)) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 (wz root0)
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_MINJ) (tx_fc X) None m (seg_rom usegs)).
Proof.
  intros until x31; intros EM EMIN Rmax Rmin ER0.
  pose proof XO as XO'. destruct XO' as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (cnt_cells_of_arr _ _ _ CNT) as CC. unfold cnt_cells in CC. pose proof (TYC 1) as R1.
  assert (Rr0 : 0 <= root0 <= 15) by (rewrite ER0; destruct (Z.ltb_spec max (tx_bits X)); lia).
  unfold PC_IT_MINJ. zs. rewrite zx16_small by lia. zs. zs. br_cases K.
  - zs. zs. replace (wz 1) with (wz (if max =? 1 then 0 else 1)) by (replace (max =? 1) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    apply (KR max min root0); try assumption; try lia. unfold itm_root. rewrite <- ER0.
    replace (root0 <? min) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - zs. zs. zs. replace (wz 1) with (wz (if max =? 1 then 0 else 1)) by (replace (max =? 1) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    apply (KR max min min); try assumption; try lia. unfold itm_root. rewrite <- ER0.
    destruct (Z.ltb_spec root0 min); lia.
Qed.
Lemma itab_minloop : forall n (max mn root0 : Z) (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word),
  itm_max cnt = max -> 2 <= max <= 15 -> 1 <= mn < max -> max - mn <= Z.of_nat n ->
  itm_min cnt max = find_min_rec cnt max n mn -> root0 = (if max <? tx_bits X then max else tx_bits X) ->
  evt usegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) (wz max) (wz mn) (wz (arr_get cnt 15)) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808))
             (wz (bv_unsigned (tx_sp X) + -136 + 2 * mn)) (wz root0)
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz (max - mn)) x29 x30 x31)
        (tx_F X) (wz PC_IT_MINL) (tx_fc X) None m (seg_rom usegs)).
Proof.
  induction n as [|n IH]; intros until x31; intros EM Rmax Rmn Rn FM ER0; [lia|].
  pose proof XO as XO'. destruct XO' as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (av16_zlength cnt 16 ltac:(lia)) as L16c. pose proof (TYC mn) as Rc.
  unfold PC_IT_MINL.
  pose proof (u16arr_read usegs _ (bv_unsigned (tx_sp X) + -136) (av16 cnt 16) mn _ (wa (bv_unsigned (tx_sp X) + -136 + 2 * mn)) CNT
                (av16_nth cnt 16 mn ltac:(lia)) ltac:(lia) eq_refl) as RD.
  zs. rewrite zx16_small by lia. clear RD. zs. br_cases K.
  -
    eapply (itab_minj max mn root0); [exact EM| exact (fm_stop _ cnt max n mn FM K)| lia| lia| exact ER0].
  - pose proof (fm_next _ cnt max n mn (mn + 1) FM ltac:(lia) eq_refl K) as FM'. clear FM.
    zs. zs. zs. zs. br_cases Kb2.
    +
      replace (bv_unsigned (tx_sp X) + -136 + 2 * mn + 2) with (bv_unsigned (tx_sp X) + -136 + 2 * (mn + 1)) by lia.
      replace (max - mn + -1) with (max - (mn + 1)) by lia.
      eapply (IH max (mn + 1) root0); [exact EM| lia| lia| lia| exact FM'| exact ER0].
    +
      zs. replace (mn + 1) with max in FM' by lia. eapply (itab_minj max max root0); [exact EM| exact (fm_end _ cnt max n FM')| lia| lia| exact ER0].
Qed.
Lemma itab_maxj : forall (max : Z) (x1 x6 x7 x8 x9 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  itm_max cnt = max -> 2 <= max <= 15 -> x7 = wz (arr_get cnt 15) ->
  evt usegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) (wz max) x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 (wz (tx_bits X))
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_MAXJ) (tx_fc X) None m (seg_rom usegs)).
Proof.
  intros until x31; intros EM Rmax ->.
  pose proof XO as XO'. destruct XO' as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (itm_min_rec cnt max ltac:(lia)) as FM.
  unfold PC_IT_MAXJ. zs. br_cases K.
  - zs. zs. zs.
    replace (wz (bv_unsigned (tx_sp X) + -134)) with (wz (bv_unsigned (tx_sp X) + -136 + 2 * 1)) by (f_equal; lia).
    replace (max + -1) with (max - 1) by lia.
    eapply (itab_minloop 16 max 1 (tx_bits X)); [exact EM| lia| lia| lia| exact FM|].
    replace (max <? tx_bits X) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - zs. zs. zs. zs.
    replace (wz (bv_unsigned (tx_sp X) + -134)) with (wz (bv_unsigned (tx_sp X) + -136 + 2 * 1)) by (f_equal; lia).
    replace (max + -1) with (max - 1) by lia.
    eapply (itab_minloop 16 max 1 max); [exact EM| lia| lia| lia| exact FM|].
    destruct (Z.ltb_spec max (tx_bits X)); lia.
Qed.
Ltac mxblk MX Z15 cnt k k' :=
  zs; rewrite zx16_small by lia; zs; let K := fresh "K" in br_cases K;
  [ let M := fresh "MX" in pose proof (mx_next _ cnt _ k k' MX ltac:(lia) ltac:(lia) K) as M; clear MX; rename M into MX
  | zs; zs; apply (itab_maxj k); [exact (mx_stop _ cnt _ k MX ltac:(lia) K)| lia| exact Z15] ].
Definition PC_IT_MAX14 : Z := 0x21dec.
Lemma itab_cascade : forall (x1 x5 x6 x8 x9 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  itm_max cnt = find_max_rec cnt 15 14 -> arr_get cnt 15 = 0 ->
  evt usegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 (wz (arr_get cnt 15)) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 (wz (tx_bits X))
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_MAX14) (tx_fc X) None m (seg_rom usegs)).
Proof.
  intros until x31; intros MX Z15.
  pose proof XO as XO'. destruct XO' as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (cnt_cells_of_arr _ _ _ CNT) as CC. unfold cnt_cells in CC.
  pose proof (TYC 1) as R1. pose proof (TYC 2) as R2. pose proof (TYC 3) as R3. pose proof (TYC 4) as R4. pose proof (TYC 5) as R5.
  pose proof (TYC 6) as R6. pose proof (TYC 7) as R7. pose proof (TYC 8) as R8. pose proof (TYC 9) as R9. pose proof (TYC 10) as R10.
  pose proof (TYC 11) as R11. pose proof (TYC 12) as R12. pose proof (TYC 13) as R13. pose proof (TYC 14) as R14. pose proof (TYC 15) as R15.
  assert (Z15w : wz (arr_get cnt 15) = wz (arr_get cnt 15)) by reflexivity.
  unfold PC_IT_MAX14.
  mxblk MX Z15w cnt 14 13. mxblk MX Z15w cnt 13 12. mxblk MX Z15w cnt 12 11. mxblk MX Z15w cnt 11 10. mxblk MX Z15w cnt 10 9.
  mxblk MX Z15w cnt 9 8. mxblk MX Z15w cnt 8 7. mxblk MX Z15w cnt 7 6. mxblk MX Z15w cnt 6 5. mxblk MX Z15w cnt 5 4.
  mxblk MX Z15w cnt 4 3. mxblk MX Z15w cnt 3 2.
  zs. rewrite zx16_small by lia. zs. br_cases Kb2.
  2:{ zs. apply (itab_maxj 2); [exact (mx_stop _ cnt _ 2 MX ltac:(lia) Kb2)| lia| exact Z15w]. }
  pose proof (mx_next _ cnt _ 2 1 MX ltac:(lia) ltac:(lia) Kb2) as MX1. clear MX.
  zs. rewrite zx16_small by lia. zs. br_cases Kb1.
  {   apply KN. exact (mx_zero _ cnt _ (mx_next _ cnt _ 1 0 MX1 ltac:(lia) ltac:(lia) Kb1)). }
  pose proof (mx_stop _ cnt _ 1 MX1 ltac:(lia) Kb1) as EM. clear MX1.
  zs. zs. zs. zs. zs. br_cases Kb3.
  2:{ exfalso. destruct (0 <? tx_bits X); cbn in Kb3; lia. }
  zs. zs. zs.
  eapply evt_eq; [| eapply (KR 1 1 1); [exact EM| | | lia| lia| lia]].
  - unfold PC_IT_KRAFT. rewrite Z15. reflexivity.
  - rewrite itm_min_rec by lia. cbn [find_min_rec]. rewrite Z.ltb_irrefl. reflexivity.
  - unfold itm_root. destruct (Z.ltb_spec 1 (tx_bits X)); [reflexivity|]. destruct (Z.ltb_spec (tx_bits X) 1); lia.
Qed.
Lemma itab_cntx : forall (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  isA m (tx_L X) (tx_s X) ->
  evt usegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_CNTX) (tx_fc X) None m (seg_rom usegs)).
Proof.
  intros until x31; intros GA.
  pose proof XO as XO'. destruct XO' as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (cnt_cells_of_arr _ _ _ CNT) as CC. unfold cnt_cells in CC. pose proof (TYC 15) as R15.
  pose proof (itm_max_rec cnt) as MX.
  assert (RBA : 0 < tx_bitsA X /\ tx_bitsA X + 4 < 2 ^ 62 /\ tx_bitsA X mod 4 = 0) by (unfold tx_bitsA; destruct (tx_dsel X); lia).
  unfold PC_IT_CNTX. ustep PC_IT_TRAP. zs. al4 (tx_bitsA X). ustep PC_IT_TRAP. zs. rewrite zx16_small by lia.
  apply (itab_ldbits X m); [exact GA| exact Rb|]. zs. br_cases K.
  - apply itab_cascade; [| exact K]. exact (mx_next _ cnt _ 15 14 MX ltac:(lia) ltac:(lia) K).
  - zs. zs. apply (itab_maxj 15); [exact (mx_stop _ cnt _ 15 MX ltac:(lia) K)| lia| reflexivity].
Qed.
End MaxMin.
