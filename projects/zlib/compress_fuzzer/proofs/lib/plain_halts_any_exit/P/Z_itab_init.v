(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Zh_kit Z_infl_iface Z_itab_kit Z_itab_defs Z_itab_pure Z_itab_ldefs Z_itab_trip Z_itab_exit Z_itab_loop.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_itab_lx.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees ItableModel ItableModel2 RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].


Lemma enough_root : forall root, 1 <= root <= 15 -> (852 <? 2 ^ root) = (9 <? root) /\ (592 <? 2 ^ root) = (9 <? root).
Proof.
  intros root Hr. destruct (Z.ltb_spec 9 root).
  - assert (2 ^ 10 <= 2 ^ root) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in *.
    split; apply Z.ltb_lt; lia.
  - assert (2 ^ root <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in *.
    split; apply Z.ltb_ge; lia.
Qed.

Lemma itab_init : forall X root max min cnt ofs wk tb m jf jg
    (x1 x8 x9 x12 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word),
  ITM X (it_flags X jf jg) cnt ofs wk tb m ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> 1 <= root <= 15 -> 1 <= max <= 15 -> 1 <= min <= 15 -> 0 <= tx_table X ->
  ty16 cnt -> arr_len cnt = 16 -> ty32 tb -> arr_len tb = 1444 -> ty16 wk -> arr_len wk = 288 ->
  it_loop_ok (Z.to_nat (tx_codes X + 1)) (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) 288 320 1444
             (itm_st0 min (tx_table X) root cnt tb wk) = true ->
  it_lx (Z.to_nat (tx_codes X + 1)) (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) (itm_st0 min (tx_table X) root cnt tb wk) ->
  tx_call X = it_fin (tx_table X) root (tx_bits X)
                (it_loop_n (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) (tx_codes X + 1) (itm_st0 min (tx_table X) root cnt tb wk)) ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) (wz max) (wz min) (wz (tx_baseA X)) x8 x9 (wz (tx_match X))
             (wz (tx_lensA X)) x12 (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 (wz root)
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz (tx_extraA X)) x29 x30 x31)
        (tx_F X) (wz PC_IT_INIT) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros TM XO IST0 Rroot Rmax Rmin Rtab TYC LC TYT LT TYW LW OK LX CALL. pose proof XO as XO'.
  destruct TM as [LOW OFS CNT SAV ST Gw Gc MI MU WM]. unfold it_flags in LOW. unfold tx_W1 in MU. pose proof (it_saved_bound _ m SAV) as BSP.
  pose proof (av16s_zlength ofs 1 15 ltac:(lia)) as L16o.
  destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (isA_munch (tx_m0 X) m _ _ _ (ist_A _ _ _ IST0) MU WM ltac:(cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as GA.
  unfold isA, isA_cells in GA. change (is_next (tx_s X)) with (tx_table X) in GA.
  pose proof (pow2_root_bounds root Rroot) as Pr.
  unfold PC_IT_INIT. zs. zs. zs. zs. zs. zs. zs. rewrite sllw_1 by lia. zs. zs. zs. zs. zs. rewrite sllw_1 by lia. zs.
  eapply (itab_loop (Z.to_nat (tx_codes X + 1)) X root max (itm_st0 min (tx_table X) root cnt tb wk) (mkLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _));
    [ | | | exact XO'| exact IST0| exact Rroot| exact Rmax| exact OK| exact LX| rewrite Z2Nat.id by lia; exact CALL].
  - unfold itm_st0. cbn [t_count t_work t_tbl]. unfold PC_IT_TRIP. itl_close.
  - unfold TREGS, itm_st0. cbn [t_len t_curr t_next t_huff t_drop t_low t_used t_sym l6 l7 l8 l9 l16 l23 l30 l31].
    rewrite itm_used_pow2 by lia. unfold lowx. rewrite Z.eqb_refl. splits; try reflexivity; f_equal; lia.
  - unfold LINV, itm_st0. cbn [t_drop t_low t_next t_count t_tbl t_work]. rewrite Z.eqb_refl. splits; try assumption; try lia.
Qed.

Lemma ity_code_cases : forall ty, (ity_code ty = 0 /\ ty = CODES) \/ (ity_code ty = 1 /\ ty = LENS) \/ (ity_code ty = 2 /\ ty = DISTS).
Proof. intros [| |]; cbn; tauto. Qed.

Lemma itab_type : forall X root max min cnt ofs wk tb m j1 ja jb j2
    (x1 x7 x8 x9 x12 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  ITM X [CB 8 j1; CB 8 ja; CB 8 jb; CB 2 j2] cnt ofs wk tb m ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> 1 <= root <= 15 -> 1 <= max <= 15 -> 1 <= min <= 15 -> 0 <= tx_table X ->
  ty16 cnt -> arr_len cnt = 16 -> ty32 tb -> arr_len tb = 1444 -> ty16 wk -> arr_len wk = 288 ->
  (it_not_enough (tx_ty X) (itm_used root) = true -> tx_call X = (1, tb, tx_table X, tx_bits X, wk)) ->
  (it_not_enough (tx_ty X) (itm_used root) = false ->
   it_loop_ok (Z.to_nat (tx_codes X + 1)) (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) 288 320 1444
             (itm_st0 min (tx_table X) root cnt tb wk) = true /\
   it_lx (Z.to_nat (tx_codes X + 1)) (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) (itm_st0 min (tx_table X) root cnt tb wk) /\
   tx_call X = it_fin (tx_table X) root (tx_bits X)
                (it_loop_n (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) (tx_codes X + 1) (itm_st0 min (tx_table X) root cnt tb wk))) ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) (wz max) (wz min) x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) x12 (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 (wz root)
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_TYPE) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros TM XO IST0 Rroot Rmax Rmin Rtab TYC LC TYT LT TYW LW NOSP LP. pose proof XO as XO'.
  pose proof TM as TM0. destruct TM as [LOW OFS CNT SAV ST Gw Gc MI MU WM]. unfold tx_W1 in MU. pose proof (it_saved_bound _ m SAV) as BSP.
  pose proof (av16s_zlength ofs 1 15 ltac:(lia)) as L16o.
  destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof LOW as [[WF _] _]. cbn in WF. destruct WF as (L1 & La & Lb & L2 & _).
  pose proof (av16_zlength cnt 16 ltac:(lia)) as L16c. unfold u16arr in Gw. pose proof (av16_zlength wk 288 ltac:(lia)) as L16w.
  pose proof (av32_zlength tb 1444 ltac:(lia)) as L32.
  rewrite itm_used_pow2 in NOSP, LP by lia. pose proof (enough_root root Rroot) as [ER1 ER2].
  unfold PC_IT_TYPE. destruct (ity_code_cases (tx_ty X)) as [[EC TY]|[[EC TY]|[EC TY]]]; rewrite EC.
  -
    assert (EN : it_not_enough (tx_ty X) (2 ^ root) = false) by (rewrite TY; reflexivity). rewrite EN in NOSP, LP.
    assert (ELOW : forall m', rw_cells psegs m' (bv_unsigned (tx_sp X) + -192) [CB 8 j1; C8 (wz 0); C8 (wz 0); CB 2 j2] ->
                   rw_cells psegs m' (bv_unsigned (tx_sp X) + -192) (it_flags X j1 j2)) by (intros m' H; unfold it_flags, tx_fD, tx_fL; rewrite TY; exact H).
    destruct (LP eq_refl) as (OK & LX & CALL).
    (* 1.4: the switch tests DISTS, then LENS, then default, and CODES sets base = extra = 0 *)
    zs. zs. if_false. zs. zs. if_false. zs. if_false. zs. zs. zs. zs. zs. zs.
    eapply evt_eq; [| eapply itab_init; [split; [apply ELOW; exact LOW| exact OFS| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact MI| exact MU| exact WM]
      | exact XO'| exact IST0| exact Rroot| exact Rmax| exact Rmin| exact Rtab| exact TYC| exact LC| exact TYT| exact LT| exact TYW| exact LW| exact OK| exact LX| exact CALL]].
    unfold tx_match, tx_extraA, tx_baseA, tx_fD, tx_fL, PC_IT_INIT. rewrite TY. reflexivity.
  -
    assert (EN : it_not_enough (tx_ty X) (2 ^ root) = (9 <? root)) by (rewrite TY; unfold it_not_enough, ENOUGH_LENS; exact ER1). rewrite EN in NOSP, LP.
    assert (ELOW : forall m', rw_cells psegs m' (bv_unsigned (tx_sp X) + -192) [CB 8 j1; C8 (wz 0); C8 (wz 1); CB 2 j2] ->
                   rw_cells psegs m' (bv_unsigned (tx_sp X) + -192) (it_flags X j1 j2)) by (intros m' H; unfold it_flags, tx_fD, tx_fL; rewrite TY; exact H).
    zs. zs. if_false. zs. zs. if_true. zs. zs. br_cases K.
    {
      specialize (NOSP ltac:(apply Z.ltb_lt; lia)).
      eapply itab_ret_exit; [split; [exact LOW| exact OFS| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact MI| exact MU| exact WM]| reflexivity
        | exact XO'| exact IST0| exact LW| exact LT| exact NOSP]. }
    destruct (LP ltac:(apply Z.ltb_ge; lia)) as (OK & LX & CALL).
    zs. zs. zs. zs. zs. zs. zs. zs. zs.
    eapply evt_eq; [| eapply itab_init; [split; [apply ELOW; exact LOW| exact OFS| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact MI| exact MU| exact WM]
      | exact XO'| exact IST0| exact Rroot| exact Rmax| exact Rmin| exact Rtab| exact TYC| exact LC| exact TYT| exact LT| exact TYW| exact LW| exact OK| exact LX| exact CALL]].
    unfold tx_match, tx_extraA, tx_baseA, tx_fD, tx_fL, PC_IT_INIT, Z_LEXT, Z_LBASE. rewrite TY. reflexivity.
  -
    assert (EN : it_not_enough (tx_ty X) (2 ^ root) = (9 <? root)) by (rewrite TY; unfold it_not_enough, ENOUGH_DISTS; exact ER2). rewrite EN in NOSP, LP.
    assert (ELOW : forall m', rw_cells psegs m' (bv_unsigned (tx_sp X) + -192) [CB 8 j1; C8 (wz 1); C8 (wz 0); CB 2 j2] ->
                   rw_cells psegs m' (bv_unsigned (tx_sp X) + -192) (it_flags X j1 j2)) by (intros m' H; unfold it_flags, tx_fD, tx_fL; rewrite TY; exact H).
    (* 1.4: the root > 9 test comes before the table setup, as for LENS *)
    zs. zs. if_true. zs. zs. zs. br_cases K.
    + specialize (NOSP ltac:(apply Z.ltb_lt; lia)).
      eapply itab_ret_exit; [split; [exact LOW| exact OFS| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact MI| exact MU| exact WM]| reflexivity
        | exact XO'| exact IST0| exact LW| exact LT| exact NOSP].
    + destruct (LP ltac:(apply Z.ltb_ge; lia)) as (OK & LX & CALL).
      zs. zs. zs. zs. zs. zs. zs. zs. zs.
      eapply evt_eq; [| eapply itab_init; [split; [apply ELOW; exact LOW| exact OFS| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact MI| exact MU| exact WM]
        | exact XO'| exact IST0| exact Rroot| exact Rmax| exact Rmin| exact Rtab| exact TYC| exact LC| exact TYT| exact LT| exact TYW| exact LW| exact OK| exact LX| exact CALL]].
      unfold tx_match, tx_extraA, tx_baseA, tx_fD, tx_fL, PC_IT_INIT, Z_DEXT, Z_DBASE. rewrite TY. reflexivity.
Qed.
