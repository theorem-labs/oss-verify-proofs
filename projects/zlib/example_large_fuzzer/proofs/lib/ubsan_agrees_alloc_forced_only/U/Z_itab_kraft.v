(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Zh_kit Z_infl_iface Z_infl_pure2 Z_itab_kit Z_itab_defs Z_itab_ldefs Z_ukit Z_itab_exit Z_itab_head Z_itab_next Z_itab_sub Z_itab_init Z_itab_sort Z_itab_offs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_itab_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees ItableModel ItableModel2 ItableModel3 RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].
Lemma sltz_small : forall v, - 2 ^ 62 <= v < 2 ^ 62 -> bv_lts (wz v) (wz 0) = (v <? 0).
Proof.
  intros v Hv. rewrite bv_lts_zero_r. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (2^63) with 9223372036854775808. change (2^62) with 4611686018427387904 in Hv.
  destruct (Z.ltb_spec v 0); destruct (Z.leb_spec 9223372036854775808 (v mod 18446744073709551616)); try reflexivity; exfalso; Z.div_mod_to_equations; lia.
Qed.
Lemma kraft_flag : forall ty (max : Z),
  Z.lor (Z.b2z (ity_code ty <? 1)) (if max =? 1 then 0 else 1) = Z.b2z (codetype_eqb ty CODES || negb (max =? 1)).
Proof. intros [| |] max; destruct (max =? 1); reflexivity. Qed.
Lemma ity_code_range : forall ty, 0 <= ity_code ty <= 2.
Proof. intros [| |]; cbn; lia. Qed.
Lemma bne_b2z : forall b, negb (bv_eqb (wz (Z.b2z b)) (wz 0)) = b.
Proof. intros [|]; reflexivity. Qed.
Lemma reject_none : forall ty max, itm_reject ty max None = true.
Proof. reflexivity. Qed.
Lemma lc_next : forall (lc : option Z) cnt n len len' lft e,
  lc = left_rec cnt (S n) len lft -> len <= 15 -> len' = len + 1 -> e = 2 * lft - arr_get cnt len -> 0 <= e ->
  lc = left_rec cnt n len' e.
Proof.
  intros lc cnt n len len' lft e H Hl -> He Hnn. rewrite H, left_rec_S' by (unfold MAXBITS; lia). unfold lstep. rewrite <- He.
  replace (e <? 0) with false by (symmetry; apply Z.ltb_ge; exact Hnn). reflexivity.
Qed.
Lemma lc_stop : forall (lc : option Z) cnt n len lft e,
  lc = left_rec cnt (S n) len lft -> len <= 15 -> e = 2 * lft - arr_get cnt len -> e < 0 -> lc = None.
Proof.
  intros lc cnt n len lft e H Hl He Hn. rewrite H, left_rec_S' by (unfold MAXBITS; lia). unfold lstep. rewrite <- He.
  replace (e <? 0) with true by (symmetry; apply Z.ltb_lt; exact Hn). reflexivity.
Qed.
Ltac kst LCK FAIL cnt k k' :=
  lazymatch type of LCK with _ = left_rec _ _ _ ?Ep =>
    zs; rewrite zx16_small by lia; zs; rewrite shl1; zstep; try rewrite (bv_swrap32_id (2 * Ep - arr_get cnt k)) by lia;
    zs; lazymatch goal with |- context [bv_lts (wz ?e) (wz 0)] =>
      rewrite (sltz_small e) by lia; let K := fresh "K" in destruct (Z.ltb_spec e 0) as [K|K];
      [ apply FAIL; rewrite (lc_stop _ cnt _ k Ep e LCK ltac:(lia) ltac:(lia) K); apply reject_none
      | let L := fresh "LCK" in pose proof (lc_next _ cnt _ k k' Ep e LCK ltac:(lia) ltac:(lia) ltac:(lia) K) as L; clear LCK; rename L into LCK ] end end.
Lemma itab_kraft : forall X low cnt wk tb m o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 (max min root : Z)
    (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word),
  rw_cells usegs m (bv_unsigned (tx_sp X) + -208) low -> Z.of_nat (cells_size low) = 42 ->
  rw_cells usegs m (bv_unsigned (tx_sp X) + -166) (ofs_junk o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15) ->
  u8arr usegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16)) ->
  rw_cells usegs m (bv_unsigned (tx_sp X) + -104) (it_saved X) -> stk usegs m (tx_lo X) (bv_unsigned (tx_sp X) + -208) ->
  u8arr usegs m (il_As (tx_L X) + 808) (u16s (av16 wk 288)) -> u32arr usegs m (il_As (tx_L X) + 1384) (av32 tb 1444) ->
  u8arr usegs m (il_As (tx_L X) + 168) (u16s (av16 (tx_lens X) 320)) ->
  mem_inv usegs m -> munch (tx_W1 X) (tx_m0 X) m -> wmono usegs (tx_m0 X) m ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ty16 cnt -> arr_len cnt = 16 -> arr_len wk = 288 -> arr_len tb = 1444 ->
  (itm_reject (tx_ty X) max (it_left_check cnt) = true -> tx_call X = (-1, tb, tx_table X, tx_bits X, wk)) ->
  (itm_reject (tx_ty X) max (it_left_check cnt) = false -> forall x7' x16' x27' x29' : word,
     evt usegs (itab_post X)
       (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) (wz max) (wz min) x7' (wz (arr_get cnt 4)) (wz (arr_get cnt 5)) (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16' (wz root)
             (wz (arr_get cnt 6)) (wz (arr_get cnt 7)) (wz (arr_get cnt 8)) (wz (arr_get cnt 9)) (wz (arr_get cnt 10)) (wz (arr_get cnt 11))
             (wz (arr_get cnt 12)) (wz (arr_get cnt 13)) (wz (arr_get cnt 14)) x27' (wz (arr_get cnt 1)) x29' (wz (arr_get cnt 2)) (wz (arr_get cnt 3)))
        (tx_F X) (wz PC_IT_OFFS) (tx_fc X) None m (seg_rom usegs))) ->
  evt usegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) (wz max) (wz min) (wz (arr_get cnt 15)) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) (wz (-1)) (wz root)
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz (arr_get cnt 1)) (wz (if max =? 1 then 0 else 1)) (wz 2) x31)
        (tx_F X) (wz PC_IT_KRAFT) (tx_fc X) None m (seg_rom usegs)).
Proof.
  intros until x31; intros LOW SZ OFSC CNT SAV ST Gw Gc Gl MI MU WM XO IST0 TYC LC LW LT REJ K.
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (it_saved_bound _ m SAV) as BSP.
  pose proof (cnt_cells_of_arr _ _ _ CNT) as CC. unfold cnt_cells in CC.
  pose proof (TYC 1) as R1. pose proof (TYC 2) as R2. pose proof (TYC 3) as R3. pose proof (TYC 4) as R4. pose proof (TYC 5) as R5.
  pose proof (TYC 6) as R6. pose proof (TYC 7) as R7. pose proof (TYC 8) as R8. pose proof (TYC 9) as R9. pose proof (TYC 10) as R10.
  pose proof (TYC 11) as R11. pose proof (TYC 12) as R12. pose proof (TYC 13) as R13. pose proof (TYC 14) as R14. pose proof (TYC 15) as R15.
  pose proof (it_left_check_rec cnt) as LCK. pose proof (ity_code_range (tx_ty X)) as Rity.
  assert (FAIL : forall (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    itm_reject (tx_ty X) max (it_left_check cnt) = true ->
    evt usegs (itab_post X) (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (wz (-1)) x17
                                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz 0x2257c) (tx_fc X) None m (seg_rom usegs))).
  { intros; eapply itab_ret_exit'; [exact LOW| exact SZ| exact OFSC| reflexivity| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact MI| exact MU| exact WM
      | exact XO'| exact IST0| exact LW| exact LT| apply REJ; assumption]. }
  unfold PC_IT_KRAFT. zs. br_cases K1.
  {
    apply FAIL. rewrite (lc_stop _ cnt _ 1 1 (2 - arr_get cnt 1) LCK ltac:(lia) ltac:(lia) ltac:(lia)). apply reject_none. }
  pose proof (lc_next _ cnt _ 1 2 1 (2 - arr_get cnt 1) LCK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as LCK1. clear LCK; rename LCK1 into LCK.
  zs. zs. rewrite srliw_small, shr30_small by lia. zs. br_false.
  zs. rewrite zx16_small by lia. zs. rewrite shl1. zs.
  zs. lazymatch goal with |- context [bv_lts (wz ?e) (wz 0)] =>
      rewrite (sltz_small e) by lia; destruct (Z.ltb_spec e 0) as [K2|K2];
      [ apply FAIL; rewrite (lc_stop _ cnt _ 2 (2 - arr_get cnt 1) e LCK ltac:(lia) ltac:(lia) K2); apply reject_none
      | pose proof (lc_next _ cnt _ 2 3 (2 - arr_get cnt 1) e LCK ltac:(lia) ltac:(lia) ltac:(lia) K2) as LCK1; clear LCK; rename LCK1 into LCK ] end.
  kst LCK FAIL cnt 3 4. kst LCK FAIL cnt 4 5. kst LCK FAIL cnt 5 6. kst LCK FAIL cnt 6 7. kst LCK FAIL cnt 7 8. kst LCK FAIL cnt 8 9.
  kst LCK FAIL cnt 9 10. kst LCK FAIL cnt 10 11. kst LCK FAIL cnt 11 12. kst LCK FAIL cnt 12 13. kst LCK FAIL cnt 13 14. kst LCK FAIL cnt 14 15.
  lazymatch type of LCK with _ = left_rec _ _ _ ?Ep =>
    zs; rewrite shl1, bv_swrap32_id by lia; zs; br_cases K15;
    [ apply FAIL; rewrite (lc_stop _ cnt _ 15 Ep (2 * Ep - arr_get cnt 15) LCK ltac:(lia) ltac:(lia) ltac:(lia)); apply reject_none
    | pose proof (lc_next _ cnt _ 15 16 Ep (2 * Ep - arr_get cnt 15) LCK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as LCK1; clear LCK;
      lazymatch type of LCK1 with _ = left_rec cnt 1 16 ?e => assert (LCK : it_left_check cnt = Some e) by (rewrite LCK1; reflexivity); clear LCK1 end ] end.
  zs. br_cases K16.
  {   apply K. rewrite LCK. unfold itm_reject.
    lazymatch goal with |- context [0 <? ?e] => replace (0 <? e) with false by (symmetry; apply Z.ltb_ge; lia) end. reflexivity. }
  zs. zs. rewrite kraft_flag. zs. if_cases K17; rewrite bne_b2z in K17.
  { apply FAIL. rewrite LCK. unfold itm_reject. rewrite K17. lazymatch goal with |- context [0 <? ?e] => replace (0 <? e) with true by (symmetry; apply Z.ltb_lt; lia) end. reflexivity. }
  apply K. rewrite LCK. unfold itm_reject. rewrite K17. lazymatch goal with |- context [0 <? ?e] => replace (0 <? e) with true by (symmetry; apply Z.ltb_lt; lia) end. reflexivity.
Qed.
