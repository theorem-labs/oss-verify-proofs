(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Zh_kit Z_infl_iface Z_itab_kit Z_itab_defs Z_itab_pure Z_itab_ldefs.
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


Lemma rw_cells_app' : forall m A cs1 cs2,
  rw_cells psegs m A (cs1 ++ cs2) <-> rw_cells psegs m A cs1 /\ rw_cells psegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)). rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma itab_frame_merge' : forall X m low ofsc cnt,
  rw_cells psegs m (bv_unsigned (tx_sp X) + -192) low -> Z.of_nat (cells_size low) = 26 ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -166) ofsc -> Z.of_nat (cells_size ofsc) = 30 ->
  u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16)) ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -104) (it_saved X) ->
  exists j, rw_cells psegs m (bv_unsigned (tx_sp X) + -192) (CB 88 j :: it_saved X).
Proof.
  intros X m low ofsc cnt LOW SZ OFS SZO CNT SAV.
  pose proof LOW as [[WF _] _]. pose proof OFS as [[WFO _] _].
  apply rw_cells_of_u8arr in CNT. rewrite u16s_length, av16_length in CNT. change (2 * Z.to_nat 16)%nat with 32%nat in CNT.
  exists (cells_bytes low ++ cells_bytes ofsc ++ u16s (av16 cnt 16)).
  apply (rw_cells_recast m _ (((low ++ ofsc) ++ [CB 32 (u16s (av16 cnt 16))]) ++ it_saved X)).
  - apply (proj2 (rw_cells_app' m _ _ _)). split.
    + apply (proj2 (rw_cells_app' m _ _ _)). split.
      * apply (proj2 (rw_cells_app' m _ _ _)). split; [exact LOW|]. eapply rw_cells_addr_eq; [exact OFS| lia].
      * rewrite cells_size_app. eapply rw_cells_addr_eq; [exact CNT| lia].
    + rewrite !cells_size_app. cbn [cells_size csize Nat.add]. eapply rw_cells_addr_eq; [exact SAV| lia].
  - pose proof SAV as [[WFS _] _]. cbn [cells_wf app]. split; [| exact WFS]. cbn [cell_wf].
    do 2 rewrite length_app. rewrite (cells_bytes_length low WF), (cells_bytes_length ofsc WFO), u16s_length, av16_length. lia.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma itab_frame_merge : forall X m low ofs cnt,
  rw_cells psegs m (bv_unsigned (tx_sp X) + -192) low -> Z.of_nat (cells_size low) = 26 ->
  u8arr psegs m (bv_unsigned (tx_sp X) + -166) (u16s (av16s ofs 1 15)) ->
  u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16)) ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -104) (it_saved X) ->
  exists j, rw_cells psegs m (bv_unsigned (tx_sp X) + -192) (CB 88 j :: it_saved X).
Proof.
  intros X m low ofs cnt LOW SZ OFS CNT SAV. apply rw_cells_of_u8arr in OFS.
  eapply itab_frame_merge'; [exact LOW| exact SZ| exact OFS| | exact CNT| exact SAV].
  cbn [cells_size csize Nat.add]. rewrite u16s_length, av16s_length. reflexivity.
Qed.

Lemma itab_ret_exit' : forall X low ofsc cnt wk tb ret m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  rw_cells psegs m (bv_unsigned (tx_sp X) + -192) low -> Z.of_nat (cells_size low) = 26 ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -166) ofsc -> Z.of_nat (cells_size ofsc) = 30 ->
  u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16)) ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -104) (it_saved X) -> stk psegs m (tx_lo X) (bv_unsigned (tx_sp X) + -192) ->
  u16arr psegs m (il_As (tx_L X) + 808) (av16 wk 288) -> u32arr psegs m (il_As (tx_L X) + 1384) (av32 tb 1444) ->
  mem_inv psegs m -> munch (tx_W1 X) (tx_m0 X) m -> wmono psegs (tx_m0 X) m ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> arr_len wk = 288 -> arr_len tb = 1444 ->
  tx_call X = (ret, tb, tx_table X, tx_bits X, wk) ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (wz ret) x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_EPI) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros LOW SZ OFS SZO CNT SAV ST Gw Gc MI MU WM XO IST0 LW LT CALL. pose proof XO as XO'.
  pose proof (xo_As X XO) as HA.
  pose proof (isA_munch (tx_m0 X) m _ _ _ (ist_A _ _ _ IST0) MU WM ltac:(unfold tx_W1; cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as GA.
  pose proof (isT_munch (tx_m0 X) m _ _ _ (ist_T _ _ _ IST0) MU WM ltac:(unfold tx_W1; cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as GT.
  pose proof (ilens_munch (tx_m0 X) m _ _ _ (ist_lens _ _ _ IST0) MU WM ltac:(unfold tx_W1; cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as Gl.
  assert (Gwin : iwin m (tx_L X) (tx_s X)).
  { apply (iwin_munch (tx_m0 X) m _ _ _ (ist_win _ _ _ IST0) MU WM). intros NE. pose proof (xo_win X XO NE). destruct (ist_lay _ _ _ IST0) as [_ LW']. destruct (LW' NE) as [_ AP].
    unfold apart in AP. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]]. }
  destruct (itab_frame_merge' X m _ _ _ LOW SZ OFS SZO CNT SAV) as (j & FR).
  unfold PC_IT_EPI.
  eapply (itab_epilogue X ret (it_res_state (tx_s X) (tx_dsel X) tb (tx_table X) (tx_bits X) wk));
    [exact XO'| exact FR| exact ST| | exact MI| eapply munch_weaken; [apply tx_W1_sub| exact MU]| exact WM| apply it_result_eq; exact CALL].
  apply IST_result; [exact XO'| apply isA_result_same; exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact LW| exact LT].
Qed.

Lemma itab_ret_exit : forall X low cnt ofs wk tb ret m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  ITM X low cnt ofs wk tb m -> Z.of_nat (cells_size low) = 26 ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> arr_len wk = 288 -> arr_len tb = 1444 ->
  tx_call X = (ret, tb, tx_table X, tx_bits X, wk) ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (wz ret) x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_EPI) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros TM SZ XO IST0 LW LT CALL. destruct TM as [LOW OFS CNT SAV ST Gw Gc MI MU WM].
  apply rw_cells_of_u8arr in OFS.
  eapply itab_ret_exit'; [exact LOW| exact SZ| exact OFS| | exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact MI| exact MU| exact WM
    | exact XO| exact IST0| exact LW| exact LT| exact CALL].
  cbn [cells_size csize Nat.add]. rewrite u16s_length, av16s_length. reflexivity.
Qed.

Lemma itab_fail_exit : forall X root max q cnt wk tb ms,
  ITL X root max PC_IT_EPI q cnt wk tb ms -> l16 q = wz 1 ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> arr_len wk = 288 -> arr_len tb = 1444 ->
  tx_call X = (1, tb, tx_table X, tx_bits X, wk) ->
  evt psegs (itab_post X) ms.
Proof.
  intros X root max q cnt wk tb ms HL E16 XO IST0 LW LT CALL.
  destruct q as [x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31].
  destruct HL as (m & j1 & j2 & ofs & -> & TM). cbn [l16] in E16. subst x16.
  eapply itab_ret_exit; [exact TM| reflexivity| exact XO| exact IST0| exact LW| exact LT| exact CALL].
Qed.

Definition PC_IT_DONE2 : Z := 0x1f7d8.

Lemma itab_done_tail : forall X root max cnt wk tb ms used a0v x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITLg X root max PC_IT_DONE2 (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) a0v cnt wk tb ms -> x30 = wz used ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> 1 <= root <= 15 -> 0 <= used < 65536 -> 0 <= tx_table X <= 1444 ->
  arr_len wk = 288 -> arr_len tb = 1444 ->
  tx_call X = (0, tb, tx_table X + used, root, wk) ->
  evt psegs (itab_post X) ms.
Proof.
  intros until x31; intros HL E30 XO IST0 Rroot Rused Rtab LW LT CALL. pose proof XO as XO'.
  itl_open HL; subst x30; destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (isA_munch (tx_m0 X) m _ _ _ (ist_A _ _ _ IST0) MU WM ltac:(cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as GA.
  pose proof (isT_munch (tx_m0 X) m _ _ _ (ist_T _ _ _ IST0) MU WM ltac:(cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as GT.
  pose proof (ilens_munch (tx_m0 X) m _ _ _ (ist_lens _ _ _ IST0) MU WM ltac:(cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as Gl.
  assert (Gwin : iwin m (tx_L X) (tx_s X)).
  { apply (iwin_munch (tx_m0 X) m _ _ _ (ist_win _ _ _ IST0) MU WM). intros NE. pose proof (XWIN NE). destruct LAY as [_ LW']. destruct (LW' NE) as [_ AP].
    unfold apart in AP. cbn [disjoint_from]. split; [lia| split; [lia| exact I]]. }
  pose proof (munch_refl [(il_As (tx_L X) + 136, il_As (tx_L X) + 144); (il_As (tx_L X) + 160, il_As (tx_L X) + 168)] m) as MUa.
  pose proof (wmono_refl psegs m) as WMa.
  apply (munch_weaken _ _ _ _ (tx_W1_sub X)) in MU. unfold tx_W1, tx_W in MU.
  unfold isA, isA_cells in GA. change (is_next (tx_s X)) with (tx_table X) in GA.
  pose proof (av32_zlength tb 1444 ltac:(lia)) as L32.
  unfold PC_IT_DONE2 at 1. zs. zs. zs. rewrite zext32_x4' by lia. zs. zs.
  zs. unfold tx_bitsA. destruct (tx_dsel X) eqn:ED; zs.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    pose proof (isT_munch m mf _ _ _ GT MUa WMa ltac:(cbn [disjoint_from]; lia)) as GT';
    pose proof (ilens_munch m mf _ _ _ Gl MUa WMa ltac:(cbn [disjoint_from]; lia)) as Gl';
    assert (Gwin' : iwin mf (tx_L X) (tx_s X)) by (apply (iwin_munch m mf _ _ _ Gwin MUa WMa); intros NE; cbn [disjoint_from]; destruct LAY as [[_ _] LW']; destruct (LW' NE) as [_ AP]; unfold apart in AP; lia) end.
  all: destruct (itab_frame_merge X _ _ _ _ LOW ltac:(reflexivity) OFS CNT SAV) as (j & FR).
  all: eapply (itab_epilogue X 0 (it_res_state (tx_s X) (tx_dsel X) tb (tx_table X + used) root wk));
    [exact XO'| exact FR| exact ST| | exact MI| exact MU| exact WM| apply it_result_eq; exact CALL].
  all: apply IST_result; [exact XO'| | exact GT'| exact Gl'| split; [exact (proj1 Gw)| exact (proj2 Gw)]| exact Gc| exact Gwin'| exact LW| exact LT].
  all: unfold isA, it_res_state, it_bits_set; rewrite ED; unfold isA_cells; ired; close_cells GA.
Qed.

Lemma itab_done : forall X root max cnt wk tb ms (huff next bits used : Z) x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITL X root max PC_IT_DONE (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) cnt wk tb ms ->
  x8 = wz (il_As (tx_L X) + 1384 + 4 * next) -> x9 = wz huff -> x24 = wz bits -> x30 = wz used ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> 1 <= root <= 15 -> 0 <= used < 65536 -> 0 <= tx_table X <= 1444 ->
  0 <= huff < 65536 -> 0 <= bits <= 15 -> 0 <= next -> (huff <> 0 -> next + huff < 1444) ->
  arr_len wk = 288 -> arr_len tb = 1444 -> ty32 tb ->
  tx_call X = (0, (if negb (huff =? 0) then arr_set tb (next + huff) (code_pack 64 bits 0) else tb), tx_table X + used, root, wk) ->
  evt psegs (itab_post X) ms.
Proof.
  intros until x31; intros HL E8 E9 E24 E30 XO IST0 Rroot Rused Rtab Rhuff Rbits Rnext Rroom LW LT TYT CALL. pose proof XO as XO'.
  itl_open HL; subst x8 x9 x24 x30; destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  unfold PC_IT_DONE at 1. zs. br_cases K.
  -
    replace (huff =? 0) with true in CALL by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in CALL.
    eapply itab_done_tail; [unfold PC_IT_DONE2; itlg_close| reflexivity| exact XO'| exact IST0| exact Rroot| exact Rused| exact Rtab| exact LW| exact LT| exact CALL].
  - replace (huff =? 0) with false in CALL by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in CALL. specialize (Rroom ltac:(lia)).
    zs. zs. rewrite zext32_x4' by lia. zs. zs.
    set (idx := next + huff). set (A := il_As (tx_L X) + 1384) in *.
    pose proof (TYT idx) as Rc0. pose proof (av32_zlength tb 1444 ltac:(lia)) as L32.
    pose proof (u32arr_store_ok_part m A (av32 tb 1444) idx 0 1 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le1 ?w)) _) =>
        let E := addr_expr a0 in
        pose proof (av32_put_b0 m0 A tb 1444 idx w 64 Gc ltac:(lia) ltac:(lia) Rc0 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
        replace (A + 4 * idx) with E in Gc' by lia end.
    clear Gc L32. store_done. rename Gc' into Gc.
    pose proof (av32_zlength (arr_set tb idx (put_b0 (arr_get tb idx) 64)) 1444 ltac:(lia)) as L32.
    pose proof (put_b0_range (arr_get tb idx) 64 Rc0) as Rc1.
    pose proof (u32arr_store_ok_part _ A _ idx 1 1 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le1 ?w)) _) =>
        let E := addr_expr a0 in
        pose proof (av32_put_b1 m0 A tb 1444 idx _ w bits Gc ltac:(lia) ltac:(lia) Rc1 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
        replace (A + 4 * idx + 1) with E in Gc' by lia end.
    clear Gc L32. store_done. rename Gc' into Gc.
    pose proof (av32_zlength (arr_set tb idx (put_b1 (put_b0 (arr_get tb idx) 64) bits)) 1444 ltac:(lia)) as L32.
    pose proof (put_b1_range _ bits Rc1) as Rc2.
    pose proof (u32arr_store_ok_part _ A _ idx 2 2 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
        let E := addr_expr a0 in
        pose proof (av32_put_h1 m0 A tb 1444 idx _ w 0 Gc ltac:(lia) ltac:(lia) Rc2 ltac:(reflexivity)) as Gc';
        replace (A + 4 * idx + 2) with E in Gc' by lia end.
    clear Gc L32. store_done. rename Gc' into Gc.
    rewrite put3_pack in Gc. clear Rc0 Rc1 Rc2.
    eapply itab_done_tail; [unfold PC_IT_DONE2; itlg_close| reflexivity| exact XO'| exact IST0| exact Rroot| exact Rused| exact Rtab| exact LW| | exact CALL].
    subst idx. rewrite arr_len_set. exact LT.
Qed.
