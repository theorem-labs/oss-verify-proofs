(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.

Module Z_itab_exit.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
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

Definition PC_IT_DONE2 : Z := 0x1f4d8.

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
End Z_itab_exit.


Module Z_itab_sort.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].


Lemma le2_wz_wrap16 : forall v, le2 (wz v) = le2 (wz (wrap16 v)).
Proof.
  intros v. apply le2_wz_mod. rewrite unsigned_lit_wrap, wrap16_mod, Z.mod_mod by lia. apply Z.mod_mod_divide. exists (2 ^ 48). reflexivity.
Qed.

Record ITSM (X : itx) (low : list cell) (cnt o w tb : arr) (m : mem) : Prop := mkITSM {
  sm_low : rw_cells psegs m (bv_unsigned (tx_sp X) + -192) low;
  sm_ofs : u8arr psegs m (bv_unsigned (tx_sp X) + -166) (u16s (av16s o 1 15));
  sm_cnt : u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16));
  sm_sav : rw_cells psegs m (bv_unsigned (tx_sp X) + -104) (it_saved X);
  sm_stk : stk psegs m (tx_lo X) (bv_unsigned (tx_sp X) + -192);
  sm_work : u8arr psegs m (il_As (tx_L X) + 808) (u16s (av16 w 288));
  sm_codes : u32arr psegs m (il_As (tx_L X) + 1384) (av32 tb 1444);
  sm_lens : u8arr psegs m (il_As (tx_L X) + 168) (u16s (av16 (tx_lens X) 320));
  sm_mi : mem_inv psegs m;
  sm_mu : munch (tx_W1 X) (tx_m0 X) m;
  sm_wm : wmono psegs (tx_m0 X) m }.

Lemma ITSM_ITM : forall X low cnt o w tb m, ITSM X low cnt o w tb m -> ITM X low cnt o w tb m.
Proof. intros X low cnt o w tb m [A B C D E F G H I J K]. split; try assumption. Qed.

Definition sort_post (X : itx) (low : list cell) (cnt o w tb : arr) (x5 x6 x17 : word) : machine_state -> Prop :=
  fun ms' => exists x1 x7 x8 x9 x12 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
    ms' = MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
                 (wz (tx_lensA X)) x12 (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_TYPE) (tx_fc X) None m' (seg_rom psegs)
    /\ ITSM X low cnt o w tb m'.

Lemma itm_sort_k_offs_ty : forall lens lens_ofs k o0 work,
  (forall i, 0 <= arr_get o0 i < 65536) -> forall i, 0 <= arr_get (fst (itm_sort_k lens lens_ofs k o0 work)) i < 65536.
Proof.
  intros lens lens_ofs k o0 work B. unfold itm_sort_k.
  destruct (Z_lt_le_dec k 0).
  - rewrite forZ_nil by lia. exact B.
  - apply (ModelRel.forZ_ind (fun _ ow => forall i, 0 <= arr_get (fst ow) i < 65536)); [| exact B | lia].
    intros j [o w] _ H i. cbn [sort_body fst] in *.
    destruct (negb _); cbn [fst]; [|apply H]. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply H].
Qed.

Lemma itab_sort_loop : forall n X low cnt o0 w0 tb m (sym : Z)
    (x1 x5 x6 x8 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word),
  let o := fst (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0) in
  let w := snd (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0) in
  ITSM X low cnt o w tb m -> Z.of_nat (cells_size low) = 26 ->
  itx_ok X -> 0 <= sym < tx_codes X -> tx_codes X - sym <= Z.of_nat n ->
  (forall i, 0 <= arr_get o0 i < 65536) -> arr_len o0 = 16 -> ty16 w0 -> arr_len w0 = 288 -> ty16 (tx_lens X) ->
  (forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15) ->
  snd (itm_sort_ok_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 288) = true ->
  evt psegs (sort_post X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) tb x5 x6 x17)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 (wz (bv_unsigned (tx_sp X) + -168)) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) (wz sym) x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz (tx_lensA X + 2 * sym)) x29 x30 x31) (tx_F X) (wz PC_IT_SORT) (tx_fc X) None m (seg_rom psegs)).
Proof.
  induction n as [|n IH]; intros until x31; intros o w SM SZ XO Rsym Rn TYO0 LO0 TYW0 LW0 TYL L15 SOK; [lia|].
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  destruct SM as [LOW OFS CNT SAV ST Gw Gc Gl MI MU WM]. unfold tx_W1 in MU. pose proof (it_saved_bound _ m SAV) as BSP.
  pose proof (av16s_zlength o 1 15 ltac:(lia)) as L16o. pose proof (av16_zlength cnt 16 ltac:(lia)) as L16c.
  pose proof (av16_zlength w 288 ltac:(lia)) as L16w. pose proof (av32_zlength tb 1444 ltac:(lia)) as L32. pose proof (av16_zlength (tx_lens X) 320 ltac:(lia)) as L16l.
  pose proof (itm_sort_k_len (tx_lens X) (tx_lofs X) sym o0 w0) as [LO LW]. fold o in LO. fold w in LW.
  pose proof (itm_sort_k_offs_ty (tx_lens X) (tx_lofs X) sym o0 w0 TYO0) as TYO. fold o in TYO.
  pose proof (itm_sort_k_work_range (tx_lens X) (tx_lofs X) sym o0 w0 TYW0) as TYW. fold w in TYW.
  set (l := arr_get (tx_lens X) (tx_lofs X + sym)). pose proof (TYL (tx_lofs X + sym)) as Rl. pose proof (L15 sym ltac:(lia)) as Rl15. fold l in Rl, Rl15.
  assert (TAIL : forall m1 (y29 y30 y31 : word),
    ITSM X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (sym + 1) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (sym + 1) o0 w0)) tb m1 ->
    evt psegs (sort_post X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) tb x5 x6 x17)
      (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 (wz (bv_unsigned (tx_sp X) + -168)) x8 x9 (wz (ity_code (tx_ty X)))
               (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) (wz sym) x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz (tx_lensA X + 2 * sym)) y29 y30 y31) (tx_F X) (wz PC_IT_SORTN) (tx_fc X) None m1 (seg_rom psegs))).
  { intros m1 y29 y30 y31 SM1. pose proof SM1 as [LOW1 OFS1 CNT1 SAV1 ST1 Gw1 Gc1 Gl1 MI1 MU1 WM1].
    unfold PC_IT_SORTN. zs. zs. zs. br_cases KE.
    -
      replace (sym + 1) with (tx_codes X) in SM1 by lia.
      apply evt_done. unfold sort_post, PC_IT_TYPE. do 21 eexists. split; [reflexivity| exact SM1].
    - replace (tx_lensA X + 2 * sym + 2) with (tx_lensA X + 2 * (sym + 1)) by lia.
      eapply (IH X low cnt o0 w0 tb m1 (sym + 1)); [exact SM1| exact SZ| exact XO'| lia| lia| exact TYO0| exact LO0| exact TYW0| exact LW0| exact TYL| exact L15| exact SOK]. }
  rewrite itm_sort_k_step in TAIL by lia. unfold sort_body in TAIL.
  change (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0) with (fst (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0), snd (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0)) in TAIL || idtac.
  rewrite (surjective_pairing (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0)) in TAIL. fold o w l in TAIL.
  unfold PC_IT_SORT.
  pose proof (u16arr_read psegs _ (il_As (tx_L X) + 168) (av16 (tx_lens X) 320) (tx_lofs X + sym) _ (wa (tx_lensA X + 2 * sym)) Gl
                (av16_nth (tx_lens X) 320 (tx_lofs X + sym) ltac:(lia)) ltac:(lia) ltac:(unfold tx_lensA; f_equal; lia)) as RD.
  zs. rewrite zx16_small by lia. clear RD. fold l. zs. br_cases K.
  -
    replace (l =? 0) with true in TAIL by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in TAIL.
    apply TAIL. split; assumption.
  - replace (l =? 0) with false in TAIL by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in TAIL.
    pose proof (TYO l) as Rol. set (ol := arr_get o l) in *.
    assert (Rol2 : ol < 288).
    { pose proof (itm_sort_ok_k_inv (tx_lens X) (tx_lofs X) o0 w0 288 sym ltac:(lia)
                    (itm_sort_ok_k_le (tx_lens X) (tx_lofs X) o0 288 (tx_codes X) (sym + 1) ltac:(lia) SOK)) as [_ B].
      fold o l in B. specialize (B ltac:(lia)). lia. }
    zs. zs.
    pose proof (u16arr_read psegs _ (bv_unsigned (tx_sp X) + -166) (av16s o 1 15) (l - 1) _ (wa (bv_unsigned (tx_sp X) + -168 + (l ≪ 1))) OFS
                  (av16s_nth o 1 15 (l - 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
    replace (1 + (l - 1)) with l in RD by lia. fold ol in RD.
    zs. rewrite zx16_small by lia. clear RD. zs. zs.
    replace (l ≪ 1) with (2 * l) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (u16arr_store_ok psegs _ (bv_unsigned (tx_sp X) + -166) (av16s o 1 15) (l - 1) (wa (bv_unsigned (tx_sp X) + -166 + 2 * (l - 1))) OFS
                  ltac:(rewrite av16s_length; lia) eq_refl) as SOK0.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?wv)) _) =>
      let E := addr_expr a0 in
      pose proof (av16s_write m0 (bv_unsigned (tx_sp X) + -166) o 1 15 (l - 1) wv (wrap16 (ol + 1)) OFS ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(apply le2_wz_wrap16)) as OFS';
      unfold u16arr in OFS'; replace (bv_unsigned (tx_sp X) + -166 + 2 * (l - 1)) with E in OFS' by lia end.
    replace (1 + (l - 1)) with l in OFS' by lia.
    pose proof (av16s_zlength (arr_set o l (wrap16 (ol + 1))) 1 15 ltac:(lia)) as L16o'.
    clear OFS L16o. store_done. rename OFS' into OFS. try clear SOK0.
    zs. replace (ol ≪ 1) with (2 * ol) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    st16 Gw w 288 (il_As (tx_L X) + 808) ol (wrap16 sym) ltac:(apply le2_wz_wrap16).
    zs. apply TAIL. split; try assumption.
Qed.

Lemma land_ones32 : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x H. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^32) with 4294967296. lia. Qed.

Definition PC_IT_SORT0 : Z := 0x1f1cc.

Lemma itab_sort : forall X low cnt o0 w0 tb m
    (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  ITSM X low cnt o0 w0 tb m -> Z.of_nat (cells_size low) = 26 ->
  itx_ok X -> (forall i, 0 <= arr_get o0 i < 65536) -> arr_len o0 = 16 -> ty16 w0 -> arr_len w0 = 288 -> ty16 (tx_lens X) ->
  (forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15) ->
  snd (itm_sort_ok_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 288) = true ->
  evt psegs (sort_post X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) tb x5 x6 x17)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_SORT0) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros SM SZ XO TYO0 LO0 TYW0 LW0 TYL L15 SOK.
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof SM as [LOW OFS CNT SAV ST Gw Gc Gl MI MU WM]. pose proof (it_saved_bound _ m SAV) as BSP.
  unfold PC_IT_SORT0. zs. br_cases K.
  -
    rewrite !itm_sort_k_0 by lia. cbn [fst snd].
    apply evt_done. unfold sort_post, PC_IT_TYPE. do 21 eexists. split; [reflexivity| exact SM].
  - zs. zs. zs. rewrite land_ones32 by lia. zs. zs. zs.
    replace (wz (tx_lensA X)) with (wz (tx_lensA X + 2 * 0)) at 2 by (f_equal; lia).
    eapply (itab_sort_loop (Z.to_nat (tx_codes X)) X low cnt o0 w0 tb m 0);
      [cbv zeta; rewrite !itm_sort_k_0 by lia; cbn [fst snd]; exact SM| exact SZ| exact XO'| lia| lia| exact TYO0| exact LO0| exact TYW0| exact LW0| exact TYL| exact L15| exact SOK].
Qed.
End Z_itab_sort.

Module Z_itab_offs.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_sort.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3 RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].


Ltac norm_psum :=
  repeat match goal with |- context [Z.to_nat ?e] => let v := eval vm_compute in (Z.to_nat e) in change (Z.to_nat e) with v end;
  cbn [psum];
  repeat match goal with |- context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v end.

Definition ofs_junk (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 : list byte) : list cell :=
  [CB 2 o1; CB 2 o2; CB 2 o3; CB 2 o4; CB 2 o5; CB 2 o6; CB 2 o7; CB 2 o8; CB 2 o9; CB 2 o10; CB 2 o11; CB 2 o12; CB 2 o13; CB 2 o14; CB 2 o15].

Definition offs_post (X : itx) (low : list cell) (cnt wk tb : arr) (x5 x6 x17 : word) : machine_state -> Prop :=
  fun ms' => exists x1 x7 x8 x9 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
    ms' = MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
                 (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_SORT0) (tx_fc X) None m' (seg_rom psegs)
    /\ ITSM X low cnt (itm_offs cnt) wk tb m'.

Lemma itab_offs : forall X low cnt wk tb m o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 (x1 x5 x6 x7 x16 x17 x27 x28 : word),
  rw_cells psegs m (bv_unsigned (tx_sp X) + -192) low -> Z.of_nat (cells_size low) = 26 ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -166) (ofs_junk o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15) ->
  u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16)) ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -104) (it_saved X) -> stk psegs m (tx_lo X) (bv_unsigned (tx_sp X) + -192) ->
  u8arr psegs m (il_As (tx_L X) + 808) (u16s (av16 wk 288)) -> u32arr psegs m (il_As (tx_L X) + 1384) (av32 tb 1444) ->
  u8arr psegs m (il_As (tx_L X) + 168) (u16s (av16 (tx_lens X) 320)) ->
  mem_inv psegs m -> munch (tx_W1 X) (tx_m0 X) m -> wmono psegs (tx_m0 X) m ->
  itx_ok X -> ty16 cnt -> arr_len cnt = 16 -> arr_len wk = 288 -> arr_len tb = 1444 ->
  evt psegs (offs_post X low cnt wk tb x5 x6 x17)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 (wz (arr_get cnt 4)) (wz (arr_get cnt 5)) (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             (wz (arr_get cnt 6)) (wz (arr_get cnt 7)) (wz (arr_get cnt 8)) (wz (arr_get cnt 9)) (wz (arr_get cnt 10)) (wz (arr_get cnt 11))
             (wz (arr_get cnt 12)) (wz (arr_get cnt 13)) (wz (arr_get cnt 14)) x27 x28 (wz (arr_get cnt 1)) (wz (arr_get cnt 2)) (wz (arr_get cnt 3)))
        (tx_F X) (wz PC_IT_OFFS) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x28; intros LOW SZ OFSC CNT SAV ST Gw Gc Gl MI MU WM XO TYC LC LW LT.
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO. unfold tx_W1 in MU.
  pose proof (it_saved_bound _ m SAV) as BSP. unfold ofs_junk in OFSC.
  pose proof (av16_zlength cnt 16 ltac:(lia)) as L16c. pose proof (av16_zlength wk 288 ltac:(lia)) as L16w.
  pose proof (av32_zlength tb 1444 ltac:(lia)) as L32. pose proof (av16_zlength (tx_lens X) 320 ltac:(lia)) as L16l.
  pose proof (TYC 1) as R1. pose proof (TYC 2) as R2. pose proof (TYC 3) as R3. pose proof (TYC 4) as R4. pose proof (TYC 5) as R5.
  pose proof (TYC 6) as R6. pose proof (TYC 7) as R7. pose proof (TYC 8) as R8. pose proof (TYC 9) as R9. pose proof (TYC 10) as R10.
  pose proof (TYC 11) as R11. pose proof (TYC 12) as R12. pose proof (TYC 13) as R13. pose proof (TYC 14) as R14.
  unfold PC_IT_OFFS. do 28 zs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    assert (OFS : u8arr psegs mf (bv_unsigned (tx_sp X) + -166) (u16s (av16s (itm_offs cnt) 1 15))) end.
  { lazymatch goal with |- u8arr _ ?mf _ _ => apply (ofs_arr_of_cells mf) end.
    eapply rw_cells_recast; [exact OFSC| cbn; tauto|].
    unfold ofs_cells. rewrite !itm_offs_psum by lia. cbn [cells_bytes cbytes app].
    repeat (apply (f_equal2 (@app byte)); [rewrite <- le2_wz_wrap16; f_equal; f_equal; norm_psum; lia|]). reflexivity. }
  clear OFSC. apply evt_done. unfold offs_post, PC_IT_SORT0. do 20 eexists. split; [reflexivity|]. split; assumption.
Qed.
End Z_itab_offs.


Module Z_itab_fill.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].

Lemma itab_fill : forall j X root max cnt wk tb ms (opv bits val hs next incr : Z)
    x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITL X root max PC_IT_FILL (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) cnt wk tb ms ->
  x26 = wz opv -> x24 = wz bits -> x25 = wz val -> x27 = wz (- incr) -> x1 = wz (hs - incr) -> x22 = wz (Z.of_nat j * incr) ->
  x8 = wz (il_As (tx_L X) + 1384 + 4 * next) ->
  itx_ok X -> (1 <= j)%nat -> incr = 2 ^ bits -> 0 <= bits <= 15 -> 0 <= hs -> 0 <= next -> Z.of_nat j * incr <= 32768 ->
  next + hs + Z.of_nat j * incr < 1444 + incr -> arr_len tb = 1444 -> ty32 tb -> 0 <= opv < 256 -> 0 <= val < 65536 ->
  evt psegs (ITL X root max PC_IT_INCR0 (mkLS x1 x6 x7 x8 x9 (wz 0) x16 (wz 0) x23 x24 x25 x26 x27 x30 x31) cnt wk
              (fill_iter (code_pack opv bits val) hs next incr j tb)) ms.
Proof.
  induction j as [|j IH]; [intros; lia|].
  intros until x31. intros HL E26 E24 E25 E27 E1 E22 E8 XO Hj Hincr Rbits Rhs Rnext Rfill Rroom LT TYT Ropv Rval.
  itl_open HL. subst x26 x24 x25 x27 x1 x22 x8.
  destruct XO as [XLO XAS XWIN XCO ARRS LAY]. unfold Z_ITABLE_STACK in XLO.
  assert (Hi1 : 1 <= incr <= 32768).
  { rewrite Hincr. split; [change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia| change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia]. }
  assert (Hji : 0 <= Z.of_nat j * incr) by nia.
  unfold PC_IT_FILL at 1. zs. rewrite addw_neg by lia.
  replace (Z.of_nat (S j) * incr - incr) with (Z.of_nat j * incr) by lia.
  zs. zs. zs. rewrite zext32_x4' by lia. zs.
  set (idx := next + (hs + Z.of_nat j * incr)).
  pose proof (TYT idx) as Rc. set (A := il_As (tx_L X) + 1384) in *.
  pose proof (av32_zlength tb 1444 ltac:(lia)) as L32.
  pose proof (u32arr_store_ok_part m A (av32 tb 1444) idx 0 1 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le1 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_b0 m0 A tb 1444 idx w opv Gc ltac:(lia) ltac:(lia) Rc ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * idx) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  pose proof (av32_zlength (arr_set tb idx (put_b0 (arr_get tb idx) opv)) 1444 ltac:(lia)) as L32.
  pose proof (put_b0_range (arr_get tb idx) opv Rc) as Rc1.
  pose proof (u32arr_store_ok_part _ A _ idx 1 1 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le1 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_b1 m0 A tb 1444 idx _ w bits Gc ltac:(lia) ltac:(lia) Rc1 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * idx + 1) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  pose proof (av32_zlength (arr_set tb idx (put_b1 (put_b0 (arr_get tb idx) opv) bits)) 1444 ltac:(lia)) as L32.
  pose proof (put_b1_range _ bits Rc1) as Rc2.
  pose proof (u32arr_store_ok_part _ A _ idx 2 2 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_h1 m0 A tb 1444 idx _ w val Gc ltac:(lia) ltac:(lia) Rc2 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * idx + 2) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  rewrite put3_pack in Gc. clear Rc Rc1 Rc2.
  pose proof (av32_zlength (arr_set tb idx (code_pack opv bits val)) 1444 ltac:(lia)) as L32.
  zs. zs. rewrite fill_iter_S. fold idx. br_cases K.
  -
    eapply IH; [itl_close| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
               | split; assumption| lia| exact Hincr| lia| lia| lia| lia| lia| | | lia| lia].
    + subst idx. rewrite arr_len_set. exact LT.
    + intros i. subst idx. rewrite arr_get_set. destruct (_ && _); [apply code_pack_ty| apply TYT].
  -
    assert (j = 0%nat) by nia. subst j. cbn [fill_iter]. apply evt_done. unfold PC_IT_INCR0. itl_close.
Qed.
End Z_itab_fill.

Module Z_itab_head.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].


Lemma itab_head : forall X root max cnt wk tb ms (huff sym len curr drop : Z)
    x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITL X root max PC_IT_TRIP (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) cnt wk tb ms ->
  x6 = wz len -> x7 = wz (2 ^ curr) -> x9 = wz huff -> x16 = wz drop -> x31 = wz sym ->
  itx_ok X -> 0 <= sym < 288 -> 1 <= len <= 15 -> 0 <= drop <= len -> 0 <= huff < 65536 -> ty16 wk ->
  (let w := arr_get wk sym in it_match (tx_ty X) <= w -> w - it_match (tx_ty X) < it_ext_len (tx_ty X) 288) ->
  (tx_ty X = LENS -> arr_get wk sym < 286) -> (tx_ty X = CODES -> arr_get wk sym < 19) ->
  evt psegs (ITL X root max PC_IT_FILL
               (mkLS (wz (huff ≫ drop - 2 ^ (len - drop))) x6 x7 x8 x9 x10 x16 x7 x23 (wz (len - drop))
                     (wz (it_here_val (tx_ty X) wk (arr_get wk sym))) (wz (it_here_op (tx_ty X) wk (arr_get wk sym)))
                     (wz (- 2 ^ (len - drop))) x30 x31) cnt wk tb) ms.
Proof.
  intros until x31. intros HL E6 E7 E9 E16 E31 XO Rsym Rlen Rdrop Rhuff TYW Rext RLX RLC.
  itl_open HL. subst x6 x7 x9 x16 x31.
  destruct XO as [XLO XAS XWIN XCO ARRS LAY]. unfold Z_ITABLE_STACK in XLO.
  pose proof (TYW sym) as Rw. cbv zeta in Rext.
  assert (Rmt : 0 <= tx_match X <= 257) by (unfold tx_match; destruct (tx_ty X); cbn; lia).
  assert (Emt : tx_match X = it_match (tx_ty X)) by reflexivity.
  pose proof (pow2_le15 (len - drop) ltac:(lia)) as Hp2.
  unfold PC_IT_TRIP. zs. zs. rewrite zext32_x2 by lia. zs.
  ld16 Gw wk 288 (il_As (tx_L X) + 808) sym ltac:(lia).
  set (w := arr_get wk sym) in *.
  zs. zs. br_cases K.
  - zs. br_cases K2.
    +
      zs. zs. zs. rewrite zext32_x2 by lia. zs. zs.
      assert (HNC : tx_ty X <> CODES).
      { intros HC. specialize (RLC HC). assert (tx_match X = 20) by (rewrite Emt, HC; reflexivity). lia. }
      pose proof (extra_read X m wk (w - tx_match X) MI Gw ltac:(lia)
                    ltac:(intros HT; specialize (RLX HT); rewrite Emt, HT; cbn [it_match]; lia) HNC) as RD1.
      pose proof (base_read X m wk (w - tx_match X) MI Gw ltac:(lia) HNC) as RD2.
      zs. cbv beta. rewrite bv8_unsigned_wrap. clear RD1.
      zs. rewrite (zx16_small (it_base (tx_ty X) wk (w - tx_match X))) by (apply it_base_range; [exact TYW| lia]). clear RD2.
      zs. zs. rewrite sllw_m1 by lia. zs. rewrite srlw_small' by lia. zs. zs.
      apply evt_done. unfold PC_IT_FILL. unfold it_here_val, it_here_op. fold w. unfold tx_match in K, K2.
      replace (w + 1 <? it_match (tx_ty X)) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (it_match (tx_ty X) <=? w) with true by (symmetry; apply Z.leb_le; lia).
      rewrite wrap8_mod. change (2 ^ 8) with 256. itl_close.
    +
      zs. zs. zs.
      zs. zs. rewrite sllw_m1 by lia. zs. rewrite srlw_small' by lia. zs. zs.
      apply evt_done. unfold PC_IT_FILL. unfold it_here_val, it_here_op. fold w. unfold tx_match in K, K2.
      replace (w + 1 <? it_match (tx_ty X)) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (it_match (tx_ty X) <=? w) with false by (symmetry; apply Z.leb_gt; lia).
      itl_close.
  -
    zs. zs.
    zs. zs. rewrite sllw_m1 by lia. zs. rewrite srlw_small' by lia. zs. zs.
    apply evt_done. unfold PC_IT_FILL. unfold it_here_val, it_here_op. fold w. unfold tx_match in K.
    replace (w + 1 <? it_match (tx_ty X)) with true by (symmetry; apply Z.ltb_lt; lia).
    itl_close.
Qed.

Lemma land_range : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= a.
Proof.
  intros a b Ha Hb. split; [apply Z.land_nonneg; lia|].
  rewrite <- (Z.lor_ldiff_and a b) at 2.
  assert (H1 : 0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia).
  assert (H2 : Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  rewrite <- Z.lxor_lor by exact H2. rewrite <- Z.add_nocarry_lxor by exact H2. pose proof (Z.land_nonneg a b). lia.
Qed.

Lemma srliw_small : forall x k, 0 <= x < 2147483648 -> 0 <= k -> bv_swrap 32 (bv_wrap 32 x ≫ k) = x ≫ k.
Proof.
  intros x k Hx Hk. rewrite (bv_wrap_small 32 x) by (unfold bv_modulus; cbn; lia).
  pose proof (shiftr_le' x k ltac:(lia) ltac:(lia)). apply bv_swrap32_id. change (2^31) with 2147483648. lia.
Qed.

Lemma itab_incr_loop : forall n X root max cnt wk tb ms (huff c : Z)
    x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITL X root max PC_IT_INCR (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) cnt wk tb ms ->
  x9 = wz huff -> x22 = wz c -> itx_ok X -> 0 <= huff < 65536 -> 0 <= c < 65536 -> c < 2 ^ Z.of_nat n ->
  evt psegs (ITL X root max PC_IT_HUFF
               (mkLS x1 x6 x7 x8 x9 (wz 0) x16 (wz (incr_rec huff n c ≫ 1)) x23 x24 (wz (incr_rec huff n c)) x26 x27 x30 x31) cnt wk tb) ms.
Proof.
  induction n as [|n IH]; intros until x31; intros HL E9 E22 XO Rhuff Rc Rcn.
  all: itl_open HL; subst x9 x22; destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  all: pose proof (land_range c huff ltac:(lia) ltac:(lia)) as Rl; pose proof (shiftr_le' c 1 ltac:(lia) ltac:(lia)) as Rs.
  all: unfold PC_IT_INCR at 1; zs; zs; zs; zs; rewrite srliw_small by lia; zs; br_cases K.
  - exfalso. cbn [Z.of_nat Z.pow_pos Z.pow] in Rcn. assert (c = 0) by lia. subst c. rewrite Z.land_0_l in K. lia.
  - cbn [Z.of_nat Z.pow_pos Z.pow] in Rcn. assert (c = 0) by lia. subst c. cbn [incr_rec]. change (0 ≫ 1) with 0.
    rewrite Z.land_0_l. apply evt_done. unfold PC_IT_HUFF. itl_close.
  -
    cbn [incr_rec]. rewrite (Z.land_comm huff c). replace (Z.land c huff =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    eapply IH; [unfold PC_IT_INCR; itl_close| reflexivity| reflexivity| split; assumption| lia| lia|].
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Rcn by lia. lia.
  - cbn [incr_rec]. rewrite (Z.land_comm huff c). replace (Z.land c huff =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
    rewrite K. apply evt_done. unfold PC_IT_HUFF. itl_close.
Qed.
End Z_itab_head.

Module Z_itab_next.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_head.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].


Lemma land_le_r : forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros a b Hb. split; [apply Z.land_nonneg; lia|].
  rewrite <- (Z.lor_ldiff_and b a) at 2. rewrite (Z.land_comm b a).
  assert (H1 : 0 <= Z.ldiff b a) by (apply Z.ldiff_nonneg; lia).
  assert (H2 : Z.land (Z.ldiff b a) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  rewrite <- Z.lxor_lor by exact H2. rewrite <- Z.add_nocarry_lxor by exact H2. pose proof (Z.land_nonneg a b). lia.
Qed.

Lemma huff_next_mach : forall huff len, 0 <= huff < 65536 -> 1 <= len <= 15 ->
  let incr := it_incr_back huff len in
  Z.land (Z.land (Z.b2z (incr <? 1) + -1) 18446744073709551615) (Z.land (Z.land (incr + -1) 18446744073709551615) huff + incr)
  = it_huff_next huff len.
Proof.
  intros huff len Hh Hl. cbv zeta. unfold it_huff_next. set (incr := it_incr_back huff len).
  assert (Ri : 0 <= incr <= 16384).
  { subst incr. rewrite it_incr_back_rec, shl32_pow2' by lia. pose proof (incr_rec_range huff 32 (2 ^ (len - 1)) ltac:(apply Z.pow_nonneg; lia)).
    assert (2 ^ (len - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *. lia. }
  destruct (Z.eq_dec incr 0) as [E|E].
  - rewrite E. reflexivity.
  - replace (incr <? 1) with false by (symmetry; apply Z.ltb_ge; lia). replace (incr =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [Z.b2z negb Z.add]. rewrite Z.land_m1_l. rewrite (land_ones64 (incr + -1)) by lia.
    pose proof (land_le_r (incr + -1) huff ltac:(lia)). rewrite (Z.land_comm 18446744073709551615), land_ones64 by lia.
    rewrite (Z.land_comm huff). replace (incr - 1) with (incr + -1) by lia. reflexivity.
Qed.

Lemma itab_nextsym : forall X root max cnt wk tb ms (huff sym len incr : Z)
    x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITL X root max PC_IT_HUFF (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) cnt wk tb ms ->
  x6 = wz len -> x9 = wz huff -> x25 = wz incr -> x31 = wz sym ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> incr = it_incr_back huff len ->
  0 <= sym < 288 -> 1 <= len <= 15 -> 0 <= huff < 65536 -> 1 <= max <= 15 -> ty16 wk -> ty16 cnt -> arr_len cnt = 16 ->
  (let c := wrap16 (arr_get cnt len - 1) in c = 0 -> len <> max ->
   let w' := arr_get wk (sym + 1) in sym + 1 < 288 /\ 0 <= w' /\ 0 <= tx_lofs X + w' < 320 /\ 1 <= arr_get (tx_lens X) (tx_lofs X + w') <= 15) ->
  evt psegs (fun ms' => exists x10' x25' x26',
    let c := wrap16 (arr_get cnt len - 1) in
    ITL X root max (if (c =? 0) && (len =? max) then PC_IT_DONE else PC_IT_NEXT)
        (mkLS x1 (wz (if (c =? 0) && negb (len =? max) then arr_get (tx_lens X) (tx_lofs X + arr_get wk (sym + 1)) else len))
              x7 x8 (wz (it_huff_next huff len)) x10' x16 (wz (bv_unsigned (tx_sp X) + -136 + 2 * len)) x23 x24 x25' x26' x27 x30 (wz (sym + 1)))
        (arr_set cnt len c) wk tb ms') ms.
Proof.
  intros until x31; intros HL E6 E9 E25 E31 XO IST0 Hincr Rsym Rlen Rhuff Rmax TYW TYC LC Hnx.
  itl_open HL; subst x6 x9 x25 x31; destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (ilens_munch (tx_m0 X) m _ _ _ (ist_lens _ _ _ IST0) MU WM ltac:(cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as Gl.
  unfold ilens, u16arr in Gl. change (is_lens (tx_s X)) with (tx_lens X) in Gl. pose proof (av16_zlength (tx_lens X) 320 ltac:(lia)) as L16l.
  assert (Rincr : 0 <= incr <= 16384).
  { rewrite Hincr, it_incr_back_rec, shl32_pow2' by lia. pose proof (incr_rec_range huff 32 (2 ^ (len - 1)) ltac:(apply Z.pow_nonneg; lia)).
    assert (2 ^ (len - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *. lia. }
  pose proof (TYC len) as Rcl. set (cl := arr_get cnt len) in *. pose proof (av32_zlength tb 1444 ltac:(lia)) as L32.
  pose proof (land_le_r (Z.land (incr + -1) 18446744073709551615) huff ltac:(lia)) as Rl.
  unfold PC_IT_HUFF. zs. zs. zs. zs.
  zs. rewrite zext32_x2 by lia. zs. zs.
  pose proof (u16arr_read psegs _ (bv_unsigned (tx_sp X) + -136) (av16 cnt 16) len (wz cl) (wa (bv_unsigned (tx_sp X) + -136 + 2 * len)) CNT (av16_nth cnt 16 len ltac:(lia)) ltac:(lia) eq_refl) as RD.
  zs. clear RD. zs. zs. zs. pose proof (huff_next_mach huff len Rhuff Rlen) as HN; cbv zeta in HN; rewrite <- Hincr in HN; rewrite HN; clear HN. zs. zs. zs. zs.
  st16 CNT cnt 16 (bv_unsigned (tx_sp X) + -136) len (wrap16 (cl - 1)) ltac:(rewrite le2_swrap16_add by lia; do 3 f_equal; lia).
  zs. br_cases K; rewrite dec48_land in K by lia.
  -
    apply evt_done. do 3 eexists. cbv zeta. fold cl.
    replace (wrap16 (cl - 1) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. unfold PC_IT_NEXT. itl_close.
  -
    assert (Hc0 : wrap16 (cl - 1) = 0) by lia.
    zs. br_cases K2.
    +
      apply evt_done. do 3 eexists. cbv zeta. fold cl. replace (wrap16 (cl - 1) =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (len =? max) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb negb]. unfold PC_IT_DONE. itl_close.
    +
      destruct (Hnx Hc0 ltac:(lia)) as (Rs1 & Rw1 & Rli & Rln).
      zs. zs. rewrite zext32_x2 by lia. zs. ld16 Gw wk 288 (il_As (tx_L X) + 808) (sym + 1) ltac:(apply TYW).
      zs. replace (arr_get wk (sym + 1) ≪ 1) with (2 * arr_get wk (sym + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). zs.
      pose proof (u16arr_read psegs _ (il_As (tx_L X) + 168) (av16 (tx_lens X) 320) (tx_lofs X + arr_get wk (sym + 1)) _
                    (wa (tx_lensA X + 2 * arr_get wk (sym + 1))) Gl (av16_nth (tx_lens X) 320 (tx_lofs X + arr_get wk (sym + 1)) ltac:(lia))
                    ltac:(lia) ltac:(unfold tx_lensA; f_equal; lia)) as RD.
      zs. rewrite zx16_small by lia. clear RD.
      apply evt_done. do 3 eexists. cbv zeta. fold cl. replace (wrap16 (cl - 1) =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (len =? max) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. unfold PC_IT_NEXT. itl_close.
Qed.
End Z_itab_next.

Module Z_itab_sub.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_head OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_next.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].


Lemma itab_left : forall n X root max cnt wk tb ms (k dp lft : Z)
    x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITL X root max PC_IT_LEFT (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) cnt wk tb ms ->
  x16 = wz lft -> x23 = wz (max - dp) -> x25 = wz dp -> x26 = wz k ->
  itx_ok X -> 0 <= dp <= k -> k < max -> max <= 15 -> 0 < lft <= 2 ^ k -> ty16 cnt -> arr_len cnt = 16 -> max - k <= Z.of_nat n ->
  evt psegs (fun ms' => exists x10' x26',
    let c := fst (curr_rec cnt dp max n (k - dp) lft) in
    ITL X root max PC_IT_USED (mkLS x1 x6 x7 x8 x9 x10' (wz (2 ^ c)) x22 (wz c) x24 x25 x26' x27 x30 x31) cnt wk tb ms') ms.
Proof.
  induction n as [|n IH]; intros until x31; intros HL E16 E23 E25 E26 XO Rdp Rk Rmax Rlft TYC LC Rn; [lia|].
  itl_open HL; subst x16 x23 x25 x26; destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (TYC k) as Rck. pose proof (pow2_le15 k ltac:(lia)) as Pk.
  cbn [curr_rec]. rewrite curr_step_small' by lia. replace (k - dp + dp) with k by lia.
  replace (k <? max) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold PC_IT_LEFT at 1. zs. zs. rewrite zext32_x2 by lia. zs. ld16 CNT cnt 16 (bv_unsigned (tx_sp X) + -136) k ltac:(lia).
  zs. zs. br_sgtz KL.
  -
    replace (lft - arr_get cnt k <=? 0) with true by (symmetry; apply Z.leb_le; lia). cbn [fst].
    zs. zs. rewrite sllw_1 by lia.
    apply evt_done. do 2 eexists. unfold PC_IT_USED. itl_close.
  -
    replace (lft - arr_get cnt k <=? 0) with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
    zs. zs. zs. br_cases KM.
    +
      replace ((lft - arr_get cnt k) ≪ 1) with (2 * (lft - arr_get cnt k)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      replace (k - dp + 1) with (k + 1 - dp) by lia.
      eapply IH; [unfold PC_IT_LEFT; itl_close| reflexivity| reflexivity| reflexivity| reflexivity| split; assumption| lia| lia| lia| | exact TYC| exact LC| lia].
      rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
    +
      zs. zs. rewrite sllw_1 by lia.
      replace (fst (curr_rec cnt dp max n (k - dp + 1) ((lft - arr_get cnt k) ≪ 1))) with (max - dp).
      2:{ destruct n as [|n']; cbn [curr_rec]; [cbn [fst]; lia|]. rewrite curr_step_small' by lia.
          replace (k - dp + 1 + dp <? max) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst]. lia. }
      apply evt_done. do 2 eexists. unfold PC_IT_USED. itl_close.
Qed.

Definition PC_IT_SUB2 : Z := 0x1f410.

Definition used_post (X : itx) (root max : Z) (cnt wk tb : arr) (huff sym len next curr used low' c : Z) (x1 x27 : word) : machine_state -> Prop :=
  fun ms' =>
      let next' := next + 2 ^ curr in
      let used' := used + 2 ^ c in
      if it_not_enough (tx_ty X) used' then exists q', ITL X root max PC_IT_EPI q' cnt wk tb ms' /\ l16 q' = wz 1
      else exists x10' x22' x24' x25' x26',
        ITL X root max PC_IT_TRIP (mkLS x1 (wz len) (wz (2 ^ c)) (wz (il_As (tx_L X) + 1384 + 4 * next')) (wz huff) x10' (wz root) x22'
                                         (wz (lowx low')) x24' x25' x26' x27 (wz used') (wz sym)) cnt wk
            (arr_set tb (tx_table X + low') (code_pack c root (next' - tx_table X))) ms'.

Lemma itab_used : forall X root max cnt wk tb ms (huff sym len next curr used low' c : Z)
    x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITL X root max PC_IT_USED (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) cnt wk tb ms ->
  x6 = wz len -> x7 = wz (2 ^ curr) -> x8 = wz (il_As (tx_L X) + 1384 + 4 * next) -> x9 = wz huff -> x16 = wz (2 ^ c) -> x23 = wz c ->
  x24 = wz low' -> x25 = wz root -> x30 = wz used -> x31 = wz sym ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) ->
  1 <= root <= 15 -> 1 <= len <= 15 -> 0 <= curr <= 15 -> 0 <= c <= 15 -> 0 <= huff < 65536 -> 0 <= used < 65536 -> 0 <= sym < 65536 ->
  0 <= low' < 65536 -> 0 <= tx_table X <= next -> next <= 1444 -> arr_len tb = 1444 -> ty32 tb ->
  (it_not_enough (tx_ty X) (used + 2 ^ c) = false -> 0 <= tx_table X + low' < 1444) ->
  evt psegs (used_post X root max cnt wk tb huff sym len next curr used low' c x1 x27) ms.
Proof.
  intros until x31; intros HL E6 E7 E8 E9 E16 E23 E24 E25 E30 E31 XO IST0 Rroot Rlen Rcurr Rc Rhuff Rused Rsym Rlow Rtab Rroom LT TYT ENT.
  itl_open HL; subst x6 x7 x8 x9 x16 x23 x24 x25 x30 x31; destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (pow2_le15 c ltac:(lia)) as Pc. pose proof (pow2_le15 curr ltac:(lia)) as Pcu.
  assert (RfL : 0 <= tx_fL X <= 1) by (unfold tx_fL; destruct (tx_ty X); lia).
  assert (RfD : 0 <= tx_fD X <= 1) by (unfold tx_fD; destruct (tx_ty X); lia).
  unfold used_post. cbv zeta. rewrite (not_enough_mach X) by lia.
  unfold PC_IT_USED at 1. zs. zs. zs. zs. zs. zs. zs. br_cases K5; rewrite (Z.add_comm (2 ^ c) used) in K5.
  {
    replace (Z.land (tx_fL X) (Z.lxor (Z.b2z (used + 2 ^ c <? 853)) 1) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb].
    apply evt_done. cbv beta. eexists (mkLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). split; [unfold PC_IT_EPI; itl_close| reflexivity]. }
  replace (Z.land (tx_fL X) (Z.lxor (Z.b2z (used + 2 ^ c <? 853)) 1) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb].
  zs. zs. zs. zs. zs. br_cases K6; rewrite (Z.add_comm (2 ^ c) used) in K6.
  {
    replace (Z.land (tx_fD X) (Z.lxor (Z.b2z (used + 2 ^ c <? 593)) 1) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    apply evt_done. cbv beta. eexists (mkLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). split; [unfold PC_IT_EPI; itl_close| reflexivity]. }
  replace (Z.land (tx_fD X) (Z.lxor (Z.b2z (used + 2 ^ c <? 593)) 1) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
  specialize (ENT ltac:(rewrite not_enough_mach by lia; rewrite K5, K6; reflexivity)).
  pose proof (isA_munch (tx_m0 X) m _ _ _ (ist_A _ _ _ IST0) MU WM ltac:(cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as GA.
  unfold isA, isA_cells in GA. change (is_next (tx_s X)) with (tx_table X) in GA.
  zs. zs. zs. rewrite zext32_x4' by lia. zs. zs. replace (low' ≪ 2) with (4 * low') by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; lia).
  zs. zs. zs.
  match goal with |- context [wz (?d ≫ 2)] =>
    replace (d ≫ 2) with (next + 2 ^ curr - tx_table X) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 2) with 4; Z.div_mod_to_equations; lia) end.
  set (idx := tx_table X + low'). set (A := il_As (tx_L X) + 1384) in *.
  pose proof (TYT idx) as Rc0. pose proof (av32_zlength tb 1444 ltac:(lia)) as L32.
  pose proof (u32arr_store_ok_part m A (av32 tb 1444) idx 0 1 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le1 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_b0 m0 A tb 1444 idx w c Gc ltac:(lia) ltac:(lia) Rc0 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * idx) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  pose proof (av32_zlength (arr_set tb idx (put_b0 (arr_get tb idx) c)) 1444 ltac:(lia)) as L32.
  pose proof (put_b0_range (arr_get tb idx) c Rc0) as Rc1.
  pose proof (u32arr_store_ok_part _ A _ idx 1 1 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le1 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_b1 m0 A tb 1444 idx _ w root Gc ltac:(lia) ltac:(lia) Rc1 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * idx + 1) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  pose proof (av32_zlength (arr_set tb idx (put_b1 (put_b0 (arr_get tb idx) c) root)) 1444 ltac:(lia)) as L32.
  pose proof (put_b1_range _ root Rc1) as Rc2.
  pose proof (u32arr_store_ok_part _ A _ idx 2 2 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_h1 m0 A tb 1444 idx _ w (next + 2 ^ curr - tx_table X) Gc ltac:(lia) ltac:(lia) Rc2 ltac:(rewrite unsigned_lit_wrap; apply Z.mod_mod_divide; exists 281474976710656; reflexivity)) as Gc';
      replace (A + 4 * idx + 2) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  rewrite put3_pack in Gc. clear Rc0 Rc1 Rc2.
  pose proof (av32_zlength (arr_set tb idx (code_pack c root (next + 2 ^ curr - tx_table X))) 1444 ltac:(lia)) as L32.
  zs. zs. zs. rewrite sllw_1 by lia. zs. Show.
  apply evt_done. cbv beta. do 5 eexists. unfold PC_IT_TRIP. unfold lowx. replace (low' =? 4294967295) with false by (symmetry; apply Z.eqb_neq; lia).
  itl_close.
Qed.

Lemma itab_sub2 : forall X root max cnt wk tb ms (huff sym len next curr used low' : Z)
    x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITL X root max PC_IT_SUB2 (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) cnt wk tb ms ->
  x6 = wz len -> x7 = wz (2 ^ curr) -> x8 = wz (il_As (tx_L X) + 1384 + 4 * next) -> x9 = wz huff -> x24 = wz low' -> x25 = wz root ->
  x30 = wz used -> x31 = wz sym ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) ->
  1 <= root <= 15 -> 1 <= max <= 15 -> root < len <= 15 -> 0 <= curr <= 15 -> 0 <= huff < 65536 -> 0 <= used < 65536 -> 0 <= sym < 65536 ->
  0 <= low' < 65536 -> 0 <= tx_table X <= next -> next <= 1444 -> ty16 cnt -> arr_len cnt = 16 -> arr_len tb = 1444 -> ty32 tb ->
  (it_not_enough (tx_ty X) (used + 2 ^ it_subtable_curr cnt len root max) = false -> 0 <= tx_table X + low' < 1444) ->
  evt psegs (used_post X root max cnt wk tb huff sym len next curr used low' (it_subtable_curr cnt len root max) x1 x27) ms.
Proof.
  intros until x31; intros HL E6 E7 E8 E9 E24 E25 E30 E31 XO IST0 Rroot Rmax Rlen Rcurr Rhuff Rused Rsym Rlow Rtab Rroom TYC LC LT TYT SUBOK.
  pose proof XO as XO'.
  itl_open HL; subst x6 x7 x8 x9 x24 x25 x30 x31; destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (pow2_le15 (len - root) ltac:(lia)) as Plr.
  rewrite it_subtable_curr_eq in * by lia.
  pose proof (curr_rec_bound cnt root max 16 (len - root) (2 ^ (len - root)) ltac:(lia) ltac:(lia) ltac:(lia)) as CB.
  unfold PC_IT_SUB2 at 1. zs. zs. rewrite sllw_1 by lia. zs. br_cases K4.
  -
    revert CB SUBOK. cbn [curr_rec]. rewrite curr_step_small' by lia. replace (len - root + root <? max) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst].
    intros CB SUBOK.
    eapply itab_used; [unfold PC_IT_USED; itl_close| reflexivity..| exact XO'| exact IST0| | | | | | | | | | | exact LT| exact TYT| exact SUBOK]; lia.
  -
    zs. zs.
    eapply evt_cut.
    { eapply (itab_left 16); [unfold PC_IT_LEFT; itl_close| reflexivity| reflexivity| reflexivity| reflexivity| exact XO'| lia| lia| lia| | exact TYC| exact LC| cbn; lia].
      pose proof (pow2_le15 len ltac:(lia)). split; [lia|]. apply Z.pow_le_mono_r; lia. }
    cbv beta. intros ms1 (x10' & x26' & HL1). cbv zeta in HL1. replace (len - root) with (len - root) in HL1 by lia.
    eapply itab_used; [exact HL1| reflexivity..| exact XO'| exact IST0| | | | | | | | | | | exact LT| exact TYT| exact SUBOK]; lia.
Qed.

Definition sub_post (X : itx) (root max : Z) (cnt wk tb : arr) (huff sym len next curr drop low used : Z) (x1 x27 : word) : machine_state -> Prop :=
  fun ms' =>
    let mask := 2 ^ root - 1 in
    if (root <? len) && negb (Z.land huff mask =? low)
    then used_post X root max cnt wk tb huff sym len next curr used (Z.land huff mask) (it_subtable_curr cnt len root max) x1 x27 ms'
    else exists x10' x22' x24' x25' x26',
        ITL X root max PC_IT_TRIP (mkLS x1 (wz len) (wz (2 ^ curr)) (wz (il_As (tx_L X) + 1384 + 4 * next)) (wz huff) x10' (wz drop) x22'
                                         (wz (lowx low)) x24' x25' x26' x27 (wz used) (wz sym)) cnt wk tb ms'.

Lemma itab_sub : forall X root max cnt wk tb ms (huff sym len next curr drop low used : Z)
    x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITL X root max PC_IT_NEXT (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) cnt wk tb ms ->
  x6 = wz len -> x7 = wz (2 ^ curr) -> x8 = wz (il_As (tx_L X) + 1384 + 4 * next) -> x9 = wz huff -> x16 = wz drop ->
  x23 = wz (lowx low) -> x30 = wz used -> x31 = wz sym ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) ->
  1 <= root <= 15 -> 1 <= max <= 15 -> 1 <= len <= 15 -> 0 <= curr <= 15 -> 0 <= huff < 65536 -> 0 <= used < 65536 -> 0 <= sym < 65536 ->
  (if drop =? 0 then root else drop) = root -> 0 <= drop <= 15 -> (low = 4294967295 \/ 0 <= low < 65536) ->
  0 <= tx_table X <= next -> next <= 1444 -> ty16 cnt -> arr_len cnt = 16 -> arr_len tb = 1444 -> ty32 tb ->
  (root < len -> Z.land huff (2 ^ root - 1) <> low -> it_not_enough (tx_ty X) (used + 2 ^ it_subtable_curr cnt len root max) = false ->
   0 <= tx_table X + Z.land huff (2 ^ root - 1) < 1444) ->
  evt psegs (sub_post X root max cnt wk tb huff sym len next curr drop low used x1 x27) ms.
Proof.
  intros until x31; intros HL E6 E7 E8 E9 E16 E23 E30 E31 XO IST0 Rroot Rmax Rlen Rcurr Rhuff Rused Rsym Hdp Rdrop Rlow Rtab Rroom TYC LC LT TYT SUBOK.
  pose proof XO as XO'.
  itl_open HL; subst x6 x7 x8 x9 x16 x23 x30 x31; destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (pow2_root_bounds root Rroot) as Pr. pose proof (land_le_r huff (2 ^ root - 1) ltac:(lia)) as Rlm.
  unfold sub_post. cbv zeta.
  unfold PC_IT_NEXT at 1. zs. br_cases K1.
  {
    replace (root <? len) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
    apply evt_done. do 5 eexists. unfold PC_IT_TRIP. itl_close. }
  replace (root <? len) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  zs. zs. br_cases K2.
  {
    apply (proj1 (lowx_test (Z.land huff (2 ^ root - 1)) low ltac:(lia) Rlow)) in K2.
    replace (Z.land huff (2 ^ root - 1) =? low) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
    apply evt_done. do 5 eexists. unfold PC_IT_TRIP. itl_close. }
  assert (NEL : Z.land huff (2 ^ root - 1) <> low) by (intros E; apply K2, (proj2 (lowx_test (Z.land huff (2 ^ root - 1)) low ltac:(lia) Rlow)), E). clear K2.
  replace (Z.land huff (2 ^ root - 1) =? low) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  specialize (SUBOK ltac:(lia) NEL).
  zs. zs. br_cases K3.
  - eapply itab_sub2; [unfold PC_IT_SUB2; itl_close| reflexivity..| exact XO'| exact IST0| | | | | | | | | | | exact TYC| exact LC| exact LT| exact TYT| exact SUBOK]; lia.
  - zs. replace drop with root by (rewrite <- Hdp; replace (drop =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply itab_sub2; [unfold PC_IT_SUB2; itl_close| reflexivity..| exact XO'| exact IST0| | | | | | | | | | | exact TYC| exact LC| exact LT| exact TYT| exact SUBOK]; lia.
Qed.
End Z_itab_sub.

Module Z_itab_trip.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_fill OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_head OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_next OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_sub.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].


Lemma it_huff_next_range : forall huff len, 0 <= huff < 65536 -> 1 <= len <= 15 -> 0 <= it_huff_next huff len < 65536.
Proof.
  intros huff len Hh Hl. unfold it_huff_next. rewrite it_incr_back_rec, shl32_pow2' by lia.
  pose proof (incr_rec_range huff 32 (2 ^ (len - 1)) ltac:(apply Z.pow_nonneg; lia)) as Hr.
  assert (2 ^ (len - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *.
  destruct (Z.eqb_spec (incr_rec huff 32 (2 ^ (len - 1))) 0); cbn [negb]; [lia|].
  pose proof (land_le_r huff (incr_rec huff 32 (2 ^ (len - 1)) - 1) ltac:(lia)). lia.
Qed.

Lemma fill_iter_ty : forall here hs next incr j tbl, 0 <= here < 2 ^ 32 -> ty32 tbl -> ty32 (fill_iter here hs next incr j tbl).
Proof.
  intros here hs next incr j. induction j as [|j IH]; intros tbl Hh Ht; cbn [fill_iter]; [exact Ht|].
  apply IH; [exact Hh| apply ty32_set; [exact Ht| exact Hh]].
Qed.

Lemma itab_incr0 : forall X root max cnt wk tb ms (len : Z) x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITL X root max PC_IT_INCR0 (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) cnt wk tb ms ->
  x6 = wz len -> itx_ok X -> 1 <= len <= 15 ->
  evt psegs (ITL X root max PC_IT_INCR (mkLS x1 x6 x7 x8 x9 (wz (len - 1)) x16 (wz (2 ^ (len - 1))) x23 x24 x25 x26 x27 x30 x31) cnt wk tb) ms.
Proof.
  intros until x31; intros HL E6 XO Rlen.
  itl_open HL; subst x6; destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  unfold PC_IT_INCR0 at 1. zs. zs. rewrite sllw_1 by lia. apply evt_done. unfold PC_IT_INCR. itl_close.
Qed.

Definition TREGS (X : itx) (st : ItSt) (q : lscr) : Prop :=
  l6 q = wz (t_len st) /\ l7 q = wz (2 ^ t_curr st) /\ l8 q = wz (il_As (tx_L X) + 1384 + 4 * t_next st) /\ l9 q = wz (t_huff st) /\
  l16 q = wz (t_drop st) /\ l23 q = wz (lowx (t_low st)) /\ l30 q = wz (t_used st) /\ l31 q = wz (t_sym st).
Definition DREGS (X : itx) (st : ItSt) (q : lscr) : Prop :=
  l8 q = wz (il_As (tx_L X) + 1384 + 4 * t_next st) /\ l9 q = wz (t_huff st) /\ l24 q = wz (t_len st - t_drop st) /\ l30 q = wz (t_used st).

Definition LINV (X : itx) (root : Z) (st : ItSt) : Prop :=
  (if t_drop st =? 0 then root else t_drop st) = root /\ 0 <= t_drop st <= 15 /\ (t_low st = 4294967295 \/ 0 <= t_low st < 65536) /\
  0 <= tx_table X <= t_next st /\
  ty16 (t_count st) /\ arr_len (t_count st) = 16 /\ ty32 (t_tbl st) /\ arr_len (t_tbl st) = 1444 /\ ty16 (t_work st) /\ arr_len (t_work st) = 288.

Definition trip_post (X : itx) (root max : Z) (r : ItStep) : machine_state -> Prop :=
  fun ms' => match r with
  | ItCont st' => exists q', ITL X root max PC_IT_TRIP q' (t_count st') (t_work st') (t_tbl st') ms' /\ TREGS X st' q' /\ LINV X root st'
  | ItBreak st' => exists q', ITL X root max PC_IT_DONE q' (t_count st') (t_work st') (t_tbl st') ms' /\ DREGS X st' q' /\ LINV X root st'
                   /\ 0 <= t_huff st' < 65536 /\ 0 <= t_len st' - t_drop st' <= 15 /\ 0 <= t_used st' < 65536 /\ 0 <= t_next st' < 1444
  | ItFail st' => exists q', ITL X root max PC_IT_EPI q' (t_count st') (t_work st') (t_tbl st') ms' /\ l16 q' = wz 1 /\ LINV X root st'
  end.

Lemma it_step_brk : forall x st s1, it_st1 x st = s1 -> it_brk x st = true -> it_step x st = ItBreak s1.
Proof. intros x st s1 E B. rewrite it_step_eq, B, E. reflexivity. Qed.
Lemma it_step_nosub : forall x st s1, it_st1 x st = s1 -> it_brk x st = false ->
  (x_root x <? t_len s1) && negb (Z.land (t_huff s1) (x_mask x) =? t_low s1) = false -> it_step x st = ItCont s1.
Proof. intros x st s1 E B C. rewrite it_step_eq, B, E. unfold it_sub. rewrite C. reflexivity. Qed.
Lemma it_step_sub : forall x st s1, it_st1 x st = s1 -> it_brk x st = false ->
  (x_root x <? t_len s1) && negb (Z.land (t_huff s1) (x_mask x) =? t_low s1) = true ->
  let drop := if t_drop s1 =? 0 then x_root x else t_drop s1 in
  let next := t_next s1 + t_min s1 in
  let curr := it_subtable_curr (t_count s1) (t_len s1) drop (x_max x) in
  let used := wrap32 (t_used s1 + Z.shiftl 1 curr) in
  it_step x st
  = if it_not_enough (x_ty x) used
    then ItFail (mkItSt (t_huff s1) (t_sym s1) (t_len s1) next curr drop (t_low s1) used (t_min s1) (t_count s1) (t_tbl s1) (t_work s1))
    else ItCont (mkItSt (t_huff s1) (t_sym s1) (t_len s1) next curr drop (Z.land (t_huff s1) (x_mask x)) used (t_min s1) (t_count s1)
                  (arr_set (t_tbl s1) (x_table x + Z.land (t_huff s1) (x_mask x)) (code_pack curr (x_root x) (next - x_table x))) (t_work s1)).
Proof. intros x st s1 E B C. rewrite it_step_eq, B, E. unfold it_sub. rewrite C. reflexivity. Qed.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- ty16 _ => fail | |- ty32 _ => fail end).

Lemma itab_trip : forall X root max st q ms,
  ITL X root max PC_IT_TRIP q (t_count st) (t_work st) (t_tbl st) ms -> TREGS X st q -> LINV X root st ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> 1 <= root <= 15 -> 1 <= max <= 15 ->
  it_trip_ok (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) 288 320 1444 st = true ->
  (forall st', it_step (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) st = ItCont st' ->
     it_trip_ok (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) 288 320 1444 st' = true) ->
  (tx_ty X = LENS -> arr_get (t_work st) (t_sym st) < 286) -> (tx_ty X = CODES -> arr_get (t_work st) (t_sym st) < 19) ->
  evt psegs (trip_post X root max (it_step (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) st)) ms.
Proof.
  intros X root max st q ms HL HR HI XO IST0 Rroot Rmax TOK TOK2 LX0 LC0.
  set (x := itm_ctx _ _ _ _ _ _) in *.
  pose proof (trip_ok_basic x _ _ _ st TOK) as (Bsym & Blen & Bdrop & Bcurr & Bhuff & Bnext & Bused & Bmin).
  pose proof (trip_ok_work x _ _ _ st TOK) as Bw. cbv zeta in Bw. destruct Bw as [Bw Bw3].
  pose proof (trip_ok_fill x _ _ _ st TOK) as Bfill. rewrite !Z.shiftl_1_l in Bfill.
  pose proof (trip_ok_next x _ _ _ st TOK) as Bnx. cbv zeta in Bnx.
  pose proof (trip_ok_sub x _ _ _ st TOK) as Bsub.
  destruct HR as (E6 & E7 & E8 & E9 & E16 & E23 & E30 & E31).
  destruct HI as (Hdp & Rdrop & Rlow & Rtab & TYC & LC & TYT & LT & TYW & LW).
  destruct st as [huff sym len next curr drop low used min count tbl work].
  destruct q as [x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31].
  cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work l1 l6 l7 l8 l9 l10 l16 l22 l23 l24 l25 l26 l27 l30 l31] in *.
  subst x. cbn [x_ty x_lens x_lens_ofs x_table x_root x_max x_mask itm_ctx] in *.
  pose proof (pow2_le15 (len - drop) ltac:(lia)) as Pld. pose proof (pow2_le15 curr ltac:(lia)) as Pcu.
  assert (Hhs : 0 <= huff ≫ drop <= huff) by (apply shiftr_le'; lia).
  eapply evt_cut.
  { eapply itab_head; [exact HL| exact E6| exact E7| exact E9| exact E16| exact E31| exact XO| lia| lia| lia| lia| exact TYW| | exact LX0| exact LC0].
    cbv zeta. intros Hm. apply Bw3; [apply Z.ltb_ge; lia| apply Z.leb_le; lia]. }
  cbv beta. intros ms1 HL1. clear HL.
  set (incr := 2 ^ (len - drop)) in *.
  set (j := Z.to_nat (2 ^ (curr - (len - drop)))).
  assert (Hj : Z.of_nat j * incr = 2 ^ curr).
  { subst j incr. rewrite Z2Nat.id by (apply Z.pow_nonneg; lia). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hj1 : (1 <= j)%nat).
  { subst j. pose proof (Z.pow_le_mono_r 2 0 (curr - (len - drop)) ltac:(lia) ltac:(lia)) as P. change (2 ^ 0) with 1 in P. lia. }
  set (here := code_pack (it_here_op (tx_ty X) work (arr_get work sym)) (len - drop) (it_here_val (tx_ty X) work (arr_get work sym))).
  pose proof (it_here_op_range (tx_ty X) work (arr_get work sym)) as Rop.
  pose proof (it_here_val_range (tx_ty X) work (arr_get work sym) TYW Bw ltac:(intros Hm; apply Bw3; [apply Z.ltb_ge; lia| apply Z.leb_le; lia])) as Rval.
  eapply evt_cut.
  { eapply (itab_fill j); [exact HL1| reflexivity| reflexivity| reflexivity| subst incr; reflexivity| subst incr; reflexivity| rewrite E7; f_equal; lia| exact E8
     | exact XO| exact Hj1| subst incr; reflexivity| lia| lia| lia| lia| lia| exact LT| exact TYT| exact Rop| exact Rval]. }
  cbv beta. intros ms2 HL2. clear HL1. fold here in HL2.
  eapply evt_cut. { eapply itab_incr0; [exact HL2| exact E6| exact XO| lia]. }
  cbv beta. intros ms3 HL3. clear HL2.
  pose proof (pow2_le15 (len - 1) ltac:(lia)) as Pl1.
  eapply evt_cut.
  { eapply (itab_incr_loop 32); [exact HL3| exact E9| reflexivity| exact XO| lia| lia|].
    apply (Z.le_lt_trans _ (2 ^ 15)); [lia|]. apply Z.pow_lt_mono_r; cbn; lia. }
  cbv beta. intros ms4 HL4. clear HL3.
  rewrite <- (shl32_pow2' (len - 1)), <- it_incr_back_rec in HL4 by lia.
  pose proof (it_huff_next_range huff len Bhuff Blen) as Rh'.
  eapply evt_cut.
  { eapply itab_nextsym; [exact HL4| exact E6| exact E9| reflexivity| exact E31| exact XO| exact IST0| reflexivity| lia| lia| lia| lia| exact TYW| exact TYC| exact LC|].
    cbv zeta. intros Hc Hm. exact (Bnx Hc Hm). }
  cbv beta. intros ms5 (x10' & x25' & x26' & HL5). clear HL4. cbv zeta in HL5.
  set (c := wrap16 (arr_get count len - 1)) in *.
  set (huff' := it_huff_next huff len) in *.
  set (tbl' := fill_iter here (huff ≫ drop) next incr j tbl) in *.
  set (len' := if (c =? 0) && negb (len =? max) then arr_get (tx_lens X) (tx_lofs X + arr_get work (sym + 1)) else len) in *.
  set (x := itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) in *.
  set (st0 := {| t_huff := huff; t_sym := sym; t_len := len; t_next := next; t_curr := curr; t_drop := drop; t_low := low; t_used := used;
                 t_min := min; t_count := count; t_tbl := tbl; t_work := work |}) in *.
  set (s1 := {| t_huff := huff'; t_sym := sym + 1; t_len := len'; t_next := next; t_curr := curr; t_drop := drop; t_low := low; t_used := used;
                t_min := 2 ^ curr; t_count := arr_set count len c; t_tbl := tbl'; t_work := work |}).
  assert (Ebrk : it_brk x st0 = (c =? 0) && (len =? max)) by reflexivity.
  assert (Est1 : it_st1 x st0 = s1).
  { subst s1 st0 x. unfold it_st1. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work x_ty x_lens x_lens_ofs x_table x_root x_max x_mask itm_ctx].
    rewrite !shl32_pow2' by lia. fold incr. rewrite <- Hj. rewrite (it_fill_spec _ incr huff drop next j tbl Hj1 ltac:(lia) ltac:(lia)).
    rewrite Hj. rewrite code_pack_wrap8_bits. rewrite (wrap32_id (sym + 1)) by lia. reflexivity. }
  assert (Hlen' : 1 <= len' <= 15).
  { subst len'. destruct (Z.eqb_spec c 0) as [Ec|Ec]; cbn [andb]; [|lia]. destruct (Z.eqb_spec len max) as [Em|Em]; cbn [negb]; [lia|].
    destruct (Bnx Ec Em) as (_ & _ & _ & W4). exact W4. }
  assert (TYC' : ty16 (arr_set count len c)) by (apply ty16_set; [exact TYC| apply wrap16_ty]).
  assert (TYT' : ty32 tbl') by (apply fill_iter_ty; [apply code_pack_ty| exact TYT]).
  assert (LT' : arr_len tbl' = 1444) by (subst tbl'; rewrite fill_iter_len; exact LT).
  assert (Hic : incr <= 2 ^ curr) by (subst incr; apply Z.pow_le_mono_r; lia).
  pose proof (pow2_root_bounds root Rroot) as Pr.
  assert (Emask : x_mask x = 2 ^ root - 1) by (subst x; cbn [x_mask itm_ctx]; rewrite itm_used_pow2 by lia; reflexivity).
  destruct (Sumbool.sumbool_of_bool ((c =? 0) && (len =? max))) as [EB|EB]; rewrite EB in Ebrk.
  -
    rewrite (it_step_brk x st0 s1 Est1 Ebrk).
    apply andb_prop in EB as [E1 E2]. rewrite E1, E2 in HL5. cbn [andb negb] in HL5.
    assert (El : len' = len) by (subst len'; rewrite E1, E2; reflexivity).
    apply evt_done. subst s1. cbn [trip_post t_count t_work t_tbl t_huff t_len t_drop t_used t_next]. eexists. split; [exact HL5|]. split; [|split].
    + unfold DREGS. cbn [t_next t_huff t_len t_drop t_used l8 l9 l24 l30]. rewrite <- El in *. splits; assumption || reflexivity.
    + unfold LINV. cbn [t_drop t_low t_next t_count t_tbl t_work]. rewrite arr_len_set. splits; try assumption; lia.
    + rewrite El. splits; lia.
  - rewrite EB in HL5.
    eapply evt_mono.
    { eapply itab_sub; [exact HL5| reflexivity| exact E7| exact E8| reflexivity| exact E16| exact E23| exact E30| reflexivity| exact XO| exact IST0
        | lia| lia| exact Hlen'| lia| exact Rh'| lia| lia| exact Hdp| lia| exact Rlow| lia| lia| exact TYC'| rewrite arr_len_set; exact LC| exact LT'| exact TYT'|].
      intros Hrl NEL ENT.
      assert (COND : (x_root x <? t_len s1) && negb (Z.land (t_huff s1) (x_mask x) =? t_low s1) = true).
      { rewrite Emask. subst x s1. cbn [x_root itm_ctx t_len t_huff t_low]. apply andb_true_intro. split; [apply Z.ltb_lt; exact Hrl| apply Bool.negb_true_iff, Z.eqb_neq; exact NEL]. }
      pose proof (it_step_sub x st0 s1 Est1 Ebrk COND) as ES. cbv zeta in ES. rewrite Emask in ES.
      subst s1. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work] in ES. rewrite Hdp in ES.
      replace (x_max x) with max in ES by (subst x; reflexivity). replace (x_ty x) with (tx_ty X) in ES by (subst x; reflexivity).
      rewrite Z.shiftl_1_l, wrap32_id, ENT in ES.
      2:{ pose proof (curr_rec_bound (arr_set count len c) root max 16 (len' - root) (2 ^ (len' - root)) ltac:(lia) ltac:(lia) ltac:(lia)) as CB.
          rewrite <- it_subtable_curr_eq in CB by lia. pose proof (pow2_le15 (it_subtable_curr (arr_set count len c) len' root max) ltac:(lia)). lia. }
      destruct (Bsub _ ES ltac:(cbn [t_low]; left; exact NEL)) as (B1 & _ & _). cbn [t_low] in B1. replace (x_table x) with (tx_table X) in B1 by (subst x; reflexivity). exact B1. }
    cbv beta. intros ms6 P6. fold tbl' in P6. unfold sub_post in P6. cbv zeta in P6.
    destruct (Sumbool.sumbool_of_bool ((root <? len') && negb (Z.land huff' (2 ^ root - 1) =? low))) as [ES|ES]; rewrite ES in P6.
    +
      assert (COND : (x_root x <? t_len s1) && negb (Z.land (t_huff s1) (x_mask x) =? t_low s1) = true) by (rewrite Emask; subst x s1; exact ES).
      pose proof (it_step_sub x st0 s1 Est1 Ebrk COND) as EST. cbv zeta in EST. rewrite Emask in EST.
      subst s1. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work] in EST. rewrite Hdp in EST.
      replace (x_max x) with max in EST by (subst x; reflexivity). replace (x_ty x) with (tx_ty X) in EST by (subst x; reflexivity).
      replace (x_table x) with (tx_table X) in EST by (subst x; reflexivity).
      set (curr' := it_subtable_curr (arr_set count len c) len' root max) in *.
      assert (Rc' : 1 <= curr' <= 15).
      { pose proof (curr_rec_bound (arr_set count len c) root max 16 (len' - root) (2 ^ (len' - root)) ltac:(lia) ltac:(lia) ltac:(lia)) as CB.
        rewrite <- it_subtable_curr_eq in CB by lia. apply andb_prop in ES as [ES1 _]. apply Z.ltb_lt in ES1. lia. }
      pose proof (pow2_le15 curr' ltac:(lia)) as Pc'.
      rewrite Z.shiftl_1_l, wrap32_id in EST by lia. rewrite EST. unfold used_post in P6. cbv zeta in P6.
      destruct (it_not_enough (tx_ty X) (used + 2 ^ curr')).
      *
        destruct P6 as (q' & HL6 & E16'). cbn [trip_post t_count t_work t_tbl]. exists q'. split; [exact HL6|]. split; [exact E16'|].
        unfold LINV. cbn [t_drop t_low t_next t_count t_tbl t_work]. rewrite arr_len_set.
        splits; try assumption; try lia. destruct (root =? 0); reflexivity.
      * destruct P6 as (x10'' & x22'' & x24'' & x25'' & x26'' & HL6). cbn [trip_post t_count t_work t_tbl]. eexists. split; [exact HL6|]. split.
        -- unfold TREGS. cbn [t_len t_curr t_next t_huff t_drop t_low t_used t_sym l6 l7 l8 l9 l16 l23 l30 l31]. splits; reflexivity.
        -- unfold LINV. cbn [t_drop t_low t_next t_count t_tbl t_work]. rewrite !arr_len_set.
           pose proof (land_le_r huff' (2 ^ root - 1) ltac:(lia)).
           splits; try assumption; try lia. { destruct (root =? 0); reflexivity. } apply ty32_set; [exact TYT'| apply code_pack_ty].
    +
      assert (COND : (x_root x <? t_len s1) && negb (Z.land (t_huff s1) (x_mask x) =? t_low s1) = false) by (rewrite Emask; subst x s1; exact ES).
      rewrite (it_step_nosub x st0 s1 Est1 Ebrk COND). subst s1.
      destruct P6 as (x10'' & x22'' & x24'' & x25'' & x26'' & HL6). cbn [trip_post t_count t_work t_tbl]. eexists. split; [exact HL6|]. split.
      * unfold TREGS. cbn [t_len t_curr t_next t_huff t_drop t_low t_used t_sym l6 l7 l8 l9 l16 l23 l30 l31]. splits; reflexivity.
      * unfold LINV. cbn [t_drop t_low t_next t_count t_tbl t_work]. rewrite !arr_len_set. splits; try assumption; lia.
Qed.
End Z_itab_trip.

Module Z_itab_lx.
(* 1.4's lext[29] is 71 where the model has 203, so the walk reads only lext[0..28].
   it_lx: every trip of a LENS table reads a work entry below 286. it_lx_intro proves it from the model's own
   sorted-work facts (RefInflateSafeH.ItSim2.trip_spec / wsym_facts) when codes <= 286. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees ModelRel ItDefs ItGen.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItMath.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItSort.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItSimPre.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItSim1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItSim2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableModel.
Local Open Scope Z_scope.

Fixpoint it_lx (n : nat) (x : ItCtx) (st : ItSt) : Prop :=
  match n with
  | O => True
  | S n' => ((x_ty x = LENS -> arr_get (t_work st) (t_sym st) < 286) /\
             (x_ty x = CODES -> arr_get (t_work st) (t_sym st) < 19)) /\
            match it_step x st with ItCont st' => it_lx n' x st' | _ => True end
  end.

Lemma it_lx_S : forall n x st, it_lx (S n) x st =
  (((x_ty x = LENS -> arr_get (t_work st) (t_sym st) < 286) /\
    (x_ty x = CODES -> arr_get (t_work st) (t_sym st) < 19)) /\
   match it_step x st with ItCont st' => it_lx n x st' | _ => True end).
Proof. reflexivity. Qed.

Lemma it_lx_dists : forall n x st, x_ty x = DISTS -> it_lx n x st.
Proof.
  induction n as [|n IH]; intros x st HT; [exact I|]. rewrite it_lx_S.
  split; [split; intros E; rewrite HT in E; discriminate E|].
  destruct (it_step x st) as [s|s|s]; [apply IH; exact HT| exact I| exact I].
Qed.

Lemma lx_loop : forall ty lens lens_ofs codes ll wl table root,
  0 <= codes <= 288 ->
  (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15) ->
  ll = lens_list lens lens_ofs codes -> wl = wl_of ll ->
  MINL wl <= root <= MAXL wl -> 1 <= MAXL wl -> TM wl (MAXL wl) <= 2 ^ MAXL wl ->
  (ty = CODES -> codes <= 19) -> (ty = LENS -> codes <= 286) ->
  forall n k st, 0 <= k < NZ wl -> StM ll wl table root k st -> it_lx n (X ty lens lens_ofs wl table root) st.
Proof.
  intros ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty H286.
  induction n as [|n IH]; intros k st Hk SM; [exact I|].
  rewrite it_lx_S.
  pose proof (trip_spec ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k st Hk SM) as TS.
  pose proof (wsym_facts ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k Hk) as [WR _].
  pose proof SM as (_ & Es & _ & _ & _ & _ & _ & _ & _ & _ & Hw).
  split.
  - split; intros HT; unfold X in HT; cbn [x_ty] in HT; rewrite Es, (Hw k Hk).
    + specialize (H286 HT). lia.
    + specialize (Hty HT). lia.
  - destruct (it_step (X ty lens lens_ofs wl table root) st) as [st'|st'|st']; [|exact I|exact I].
    destruct TS as (Hk1 & _ & SM' & _). exact (IH (k + 1) st' ltac:(lia) SM').
Qed.

Lemma it_lx_intro : forall ty lens lens_ofs codes tbl table bits work cnt max min root,
  0 <= codes <= 288 -> (ty = CODES -> codes <= 19) -> (ty = LENS -> codes <= 286) ->
  (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15) -> codes <= arr_len work ->
  cnt = itm_count lens lens_ofs codes -> itm_max cnt = max -> max <> 0 ->
  itm_reject ty max (it_left_check cnt) = false ->
  itm_min cnt max = min -> itm_root bits max min = root ->
  it_lx (Z.to_nat (codes + 1)) (itm_ctx ty lens lens_ofs table root max)
        (itm_st0 min table root cnt tbl (itm_work lens lens_ofs codes (itm_offs cnt) work)).
Proof.
  intros ty lens lens_ofs codes tbl table bits work cnt max min root Hcodes Hty19 H286 Hlens HWN Ecnt EM NZm NR EMIN ER.
  remember (lens_list lens lens_ofs codes) as ll eqn:Ell.
  remember (wl_of ll) as wl eqn:Ewl.
  pose proof (HW lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as HW0.
  pose proof (HL lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as HL0.
  pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItSimPre.Hll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as Hll'.
  pose proof (count_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as [CL CC].
  unfold itm_count in Ecnt.
  change (it_count lens lens_ofs codes (it_zero_count (arr_make 16 0))) with (CNT lens lens_ofs codes) in Ecnt.
  subst cnt. set (C := CNT lens lens_ofs codes) in *.
  pose proof (MAXL_spec wl HW0 HL0) as [M1 [M2 M3]].
  unfold itm_max in EM. rewrite (find_max_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) in EM. subst max.
  assert (HM1 : 1 <= MAXL wl) by lia.
  unfold itm_min in EMIN. rewrite (find_min_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC HM1) in EMIN. subst min.
  unfold itm_reject in NR. rewrite (left_check_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) in NR.
  pose proof (LEFT_sign wl HW0 HL0) as [LS1 [LS2 LS3]].
  destruct (Z.ltb_spec (LEFT wl) 0) as [HLn|HLn]; [simpl in NR; discriminate NR|].
  assert (HK : TM wl (MAXL wl) <= 2 ^ MAXL wl).
  { destruct (Z.le_gt_cases (TM wl (MAXL wl)) (2 ^ MAXL wl)) as [G|G]; [exact G|]. apply LS1 in G. lia. }
  assert (RR : MINL wl <= root <= MAXL wl).
  { pose proof (MINL_spec wl HW0 HL0 HM1) as [A _]. subst root. unfold itm_root.
    destruct (Z.ltb_spec (MAXL wl) bits); [destruct (Z.ltb_spec (MAXL wl) (MINL wl)) | destruct (Z.ltb_spec bits (MINL wl))]; lia. }
  pose proof (root_range wl HW0 HL0 root RR HM1) as RR2.
  pose proof (offs_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) as [OL OC].
  unfold itm_offs. change (it_offs C (arr_make 16 0)) with (OFS C). set (O := OFS C) in OL, OC |- *.
  unfold itm_work. rewrite (sort_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl O work OL OC).
  unfold itm_ctx, itm_st0. rewrite itm_used_pow2 by lia.
  change (mkItCtx ty lens lens_ofs table root (MAXL wl) (2 ^ root - 1)) with (X ty lens lens_ofs wl table root).
  pose proof (NZ_pos wl HW0 HL0 HM1) as NP.
  pose proof (NZ_le_codes lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as NZC.
  apply (lx_loop ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl RR HM1 HK Hty19 H286 _ 0); [lia|].
  unfold StM. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_work].
  pose proof (lay_inv wl HW0 HL0 root RR HM1 0 ltac:(lia)) as [LI _].
  assert (HS : islong wl root 0 = false).
  { unfold islong. rewrite (len_at_0 wl HW0 HL0 HM1). apply Z.ltb_ge. lia. }
  destruct (LI HS) as [N0 [C0 U0]]. rewrite N0, C0, U0. unfold ItDefs.drop, ItDefs.low. rewrite HS.
  rewrite (len_at_0 wl HW0 HL0 HM1).
  repeat split; try reflexivity; try lia.
  - intros l Hl. rewrite CC by lia. unfold REM. rewrite (len_at_0 wl HW0 HL0 HM1).
    pose proof (MINL_spec wl HW0 HL0 HM1) as [A [B D]]. unfold rank_at. rewrite (len_at_0 wl HW0 HL0 HM1).
    rewrite (OFF_below_MINL wl HW0 HL0 (MINL wl)) by lia.
    destruct (Z.ltb_spec l (MINL wl)); [apply D; lia|]. destruct (Z.eqb_spec l (MINL wl)); [subst; lia | reflexivity].
  - intros j Hj. rewrite Ewl in Hj |- *. apply (sorted_work ll Hll'); [|exact Hj].
    pose proof (NZ_le_NC ll Hll') as NN. rewrite (NC_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) in NN. lia.
Qed.
End Z_itab_lx.

Module Z_itab_loop.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_trip OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_lx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].


Lemma itab_loop : forall k X root max st q ms,
  ITL X root max PC_IT_TRIP q (t_count st) (t_work st) (t_tbl st) ms -> TREGS X st q -> LINV X root st ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> 1 <= root <= 15 -> 1 <= max <= 15 ->
  it_loop_ok k (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) 288 320 1444 st = true ->
  it_lx k (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) st ->
  tx_call X = it_fin (tx_table X) root (tx_bits X) (it_loop_n (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) (Z.of_nat k) st) ->
  evt psegs (itab_post X) ms.
Proof.
  induction k as [|k IH]; intros X root max st q ms HL HR HI XO IST0 Rroot Rmax OK LX CALL; [discriminate OK|].
  set (x := itm_ctx _ _ _ _ _ _) in *.
  rewrite it_loop_ok_S in OK. apply andb_prop in OK as [TOK OK].
  rewrite it_lx_S in LX. destruct LX as [[LX0 LC0] LX].
  rewrite it_loop_n_step in CALL by lia. replace (Z.of_nat (S k) - 1) with (Z.of_nat k) in CALL by lia.
  eapply evt_cut.
  { eapply itab_trip; [exact HL| exact HR| exact HI| exact XO| exact IST0| exact Rroot| exact Rmax| exact TOK| | exact LX0| exact LC0].
    intros st' ES. fold x in ES. rewrite ES in OK. destruct k as [|k']; [discriminate OK|]. rewrite it_loop_ok_S in OK. apply andb_prop in OK as [TOK' _]. exact TOK'. }
  cbv beta. intros ms1 TP. fold x in TP.
  pose proof (trip_ok_basic x _ _ _ st TOK) as (Bsym & Blen & Bdrop & Bcurr & Bhuff & Bnext & Bused & Bmin).
  pose proof (trip_ok_fill x _ _ _ st TOK) as Bfill. rewrite !Z.shiftl_1_l in Bfill.
  destruct (it_step x st) as [st'|st'|st'].
  -
    destruct TP as (q' & HL' & HR' & HI'). eapply IH; [exact HL'| exact HR'| exact HI'| exact XO| exact IST0| exact Rroot| exact Rmax| exact OK| exact LX| exact CALL].
  -
    destruct TP as (q' & HL' & HR' & HI' & Rh & Rb & Ru & Rn). destruct q' as [x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31].
    destruct HR' as (E8 & E9 & E24 & E30). cbn [l8 l9 l24 l30] in E8, E9, E24, E30.
    destruct HI' as (_ & _ & _ & Rtab & _ & _ & TYT & LT & _ & LW).
    cbn [it_fin] in CALL.
    eapply itab_done; [exact HL'| exact E8| exact E9| exact E24| exact E30| exact XO| exact IST0| exact Rroot| lia| lia| lia| lia| lia| | exact LW| exact LT| exact TYT| exact CALL].
    intros NE. revert OK. replace (t_huff st' =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb]. intros OK.
    apply andb_prop in OK as [_ OK]. apply Z.ltb_lt in OK. exact OK.
  -
    destruct TP as (q' & HL' & E16 & HI'). destruct HI' as (_ & _ & _ & _ & _ & _ & _ & LT & _ & LW).
    cbn [it_fin] in CALL.
    eapply itab_fail_exit; [exact HL'| exact E16| exact XO| exact IST0| exact LW| exact LT| exact CALL].
Qed.
End Z_itab_loop.

Module Z_itab_init.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_trip OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_loop OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_lx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
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
End Z_itab_init.


Module Z_itab_kraft.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_offs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3 RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
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
Lemma shl1 : forall x, x ≪ 1 = 2 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia. lia. Qed.
Lemma land16_small : forall x, 0 <= x < 65536 -> Z.land x 65535 = x.
Proof. intros x H. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^16) with 65536. lia. Qed.

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
    (x1 x8 x9 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word),
  rw_cells psegs m (bv_unsigned (tx_sp X) + -192) low -> Z.of_nat (cells_size low) = 26 ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -166) (ofs_junk o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15) ->
  u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16)) ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -104) (it_saved X) -> stk psegs m (tx_lo X) (bv_unsigned (tx_sp X) + -192) ->
  u8arr psegs m (il_As (tx_L X) + 808) (u16s (av16 wk 288)) -> u32arr psegs m (il_As (tx_L X) + 1384) (av32 tb 1444) ->
  u8arr psegs m (il_As (tx_L X) + 168) (u16s (av16 (tx_lens X) 320)) ->
  mem_inv psegs m -> munch (tx_W1 X) (tx_m0 X) m -> wmono psegs (tx_m0 X) m ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ty16 cnt -> arr_len cnt = 16 -> arr_len wk = 288 -> arr_len tb = 1444 ->
  (itm_reject (tx_ty X) max (it_left_check cnt) = true -> tx_call X = (-1, tb, tx_table X, tx_bits X, wk)) ->
  (itm_reject (tx_ty X) max (it_left_check cnt) = false -> forall x7' x16' x27' : word,
     evt psegs (itab_post X)
       (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) (wz max) (wz min) x7' (wz (arr_get cnt 4)) (wz (arr_get cnt 5)) (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16' (wz root)
             (wz (arr_get cnt 6)) (wz (arr_get cnt 7)) (wz (arr_get cnt 8)) (wz (arr_get cnt 9)) (wz (arr_get cnt 10)) (wz (arr_get cnt 11))
             (wz (arr_get cnt 12)) (wz (arr_get cnt 13)) (wz (arr_get cnt 14)) x27' (wz (if max =? 1 then 0 else 1))
             (wz (arr_get cnt 1)) (wz (arr_get cnt 2)) (wz (arr_get cnt 3)))
        (tx_F X) (wz PC_IT_OFFS) (tx_fc X) None m (seg_rom psegs))) ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) (wz max) (wz min) (wz (arr_get cnt 15)) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 (wz root)
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz (if max =? 1 then 0 else 1)) x29 x30 x31)
        (tx_F X) (wz PC_IT_KRAFT) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros LOW SZ OFSC CNT SAV ST Gw Gc Gl MI MU WM XO IST0 TYC LC LW LT REJ K.
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (it_saved_bound _ m SAV) as BSP.
  pose proof (cnt_cells_of_arr _ _ _ CNT) as CC. unfold cnt_cells in CC.
  pose proof (TYC 1) as R1. pose proof (TYC 2) as R2. pose proof (TYC 3) as R3. pose proof (TYC 4) as R4. pose proof (TYC 5) as R5.
  pose proof (TYC 6) as R6. pose proof (TYC 7) as R7. pose proof (TYC 8) as R8. pose proof (TYC 9) as R9. pose proof (TYC 10) as R10.
  pose proof (TYC 11) as R11. pose proof (TYC 12) as R12. pose proof (TYC 13) as R13. pose proof (TYC 14) as R14. pose proof (TYC 15) as R15.
  pose proof (it_left_check_rec cnt) as LCK. pose proof (ity_code_range (tx_ty X)) as Rity.
  assert (FAIL : forall (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    itm_reject (tx_ty X) max (it_left_check cnt) = true ->
    evt psegs (itab_post X) (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (wz (-1)) x17
                                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz 0x1f4f4) (tx_fc X) None m (seg_rom psegs))).
  { intros; eapply itab_ret_exit'; [exact LOW| exact SZ| exact OFSC| reflexivity| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact MI| exact MU| exact WM
      | exact XO'| exact IST0| exact LW| exact LT| apply REJ; assumption]. }
  unfold PC_IT_KRAFT. zs. rewrite zx16_small by lia. zs. zs. zs. br_cases K1.
  {
    apply FAIL. rewrite (lc_stop _ cnt _ 1 1 (2 - arr_get cnt 1) LCK ltac:(lia) ltac:(lia) ltac:(lia)). apply reject_none. }
  pose proof (lc_next _ cnt _ 1 2 1 (2 - arr_get cnt 1) LCK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as LCK1. clear LCK; rename LCK1 into LCK.
  zs. rewrite shl1. zs. zs. rewrite zx16_small by lia. zs. zs. zs. rewrite land16_small by lia.
  zs. zs. lazymatch goal with |- context [bv_lts (wz ?e) (wz 0)] =>
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
  { apply K. rewrite LCK. unfold itm_reject.
    lazymatch goal with |- context [0 <? ?e] => replace (0 <? e) with false by (symmetry; apply Z.ltb_ge; lia) end. reflexivity. }
  zs. zs. rewrite kraft_flag. zs. if_cases K17; rewrite bne_b2z in K17.
  { apply FAIL. rewrite LCK. unfold itm_reject. rewrite K17. lazymatch goal with |- context [0 <? ?e] => replace (0 <? e) with true by (symmetry; apply Z.ltb_lt; lia) end. reflexivity. }
  apply K. rewrite LCK. unfold itm_reject. rewrite K17. lazymatch goal with |- context [0 <? ?e] => replace (0 <? e) with true by (symmetry; apply Z.ltb_lt; lia) end. reflexivity.
Qed.
End Z_itab_kraft.


Module Z_itab_max.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3 RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
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
Lemma find_min_rec_range : forall cnt max n mn, mn <= max -> mn <= find_min_rec cnt max n mn <= max.
Proof.
  intros cnt max n. induction n as [|n IH]; intros mn Hm; cbn [find_min_rec]; [lia|].
  destruct (Z.ltb_spec mn max); cbn [andb]; [|lia]. destruct (arr_get cnt mn =? 0); [|lia].
  specialize (IH (mn + 1) ltac:(lia)). lia.
Qed.

Lemma itab_ldbits : forall X m Q (pc : Z) (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  (pc = 0x1ef04 \/ pc = 0x1ef14) -> isA m (tx_L X) (tx_s X) -> 0 <= tx_bits X <= 15 ->
  evt psegs Q (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 (wz (tx_bits X))
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz (pc + 4)) (tx_fc X) None m (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz pc) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros PC GA Rb H. unfold isA, isA_cells in GA.
  assert (E14 : wz (tx_bitsA X) = wz (il_As (tx_L X) + (if tx_dsel X then 140 else 136))) by reflexivity.
  assert (E17 : tx_bits X = (if tx_dsel X then is_distbits (tx_s X) else is_lenbits (tx_s X))) by reflexivity.
  rewrite E17 in H, Rb. revert H. rewrite E14. destruct (tx_dsel X); intros H; destruct PC as [-> | ->]; zs; exact H.
Qed.

Section MaxMin.
Variables (X : itx) (cnt : arr) (m : mem).
Definition kraft_K : Prop :=
  forall (max min root : Z) (x1 x8 x9 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word),
  itm_max cnt = max -> itm_min cnt max = min -> itm_root (tx_bits X) max min = root -> 1 <= max <= 15 -> 1 <= min <= 15 -> 1 <= root <= 15 ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) (wz max) (wz min) (wz (arr_get cnt 15)) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 (wz root)
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz (if max =? 1 then 0 else 1)) x29 x30 x31)
        (tx_F X) (wz PC_IT_KRAFT) (tx_fc X) None m (seg_rom psegs)).
Definition nosym_K : Prop :=
  forall (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  itm_max cnt = 0 ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_NOSYM) (tx_fc X) None m (seg_rom psegs)).

Hypothesis CNT : u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16)).
Hypothesis XO : itx_ok X.
Hypothesis TYC : ty16 cnt.
Hypothesis LC : arr_len cnt = 16.
Hypothesis Rb : 0 <= tx_bits X <= 15.
Hypothesis KR : kraft_K.
Hypothesis KN : nosym_K.

Lemma itab_minloop : forall n (max mn root0 : Z) (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 : word),
  itm_max cnt = max -> 2 <= max <= 15 -> 1 <= mn < max -> max - mn <= Z.of_nat n ->
  itm_min cnt max = find_min_rec cnt max n mn -> root0 = (if max <? tx_bits X then max else tx_bits X) ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) (wz max) (wz mn) (wz (arr_get cnt 15)) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808))
             (wz (bv_unsigned (tx_sp X) + -136 + 2 * mn)) (wz root0)
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz 1) (wz (max - mn)) x30 x31)
        (tx_F X) (wz PC_IT_MINL) (tx_fc X) None m (seg_rom psegs)).
Proof.
  induction n as [|n IH]; intros until x31; intros EM Rmax Rmn Rn FM ER0; [lia|].
  pose proof XO as XO'. destruct XO' as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (av16_zlength cnt 16 ltac:(lia)) as L16c. pose proof (TYC mn) as Rc.
  assert (Rr0 : 0 <= root0 <= 15) by (rewrite ER0; destruct (Z.ltb_spec max (tx_bits X)); lia).
  assert (JOIN : forall (min : Z) (y16 y29 y30 : word), itm_min cnt max = min -> 1 <= min <= max ->
    evt psegs (itab_post X)
      (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) (wz max) (wz min) (wz (arr_get cnt 15)) x8 x9 (wz (ity_code (tx_ty X)))
               (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) y16 (wz root0)
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz 1) y29 y30 x31)
          (tx_F X) (wz PC_IT_MINJ) (tx_fc X) None m (seg_rom psegs))).
  { intros min y16 y29 y30 EMIN Rmin. unfold PC_IT_MINJ. zs. br_cases K.
    - replace (wz 1) with (wz (if max =? 1 then 0 else 1)) by (replace (max =? 1) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      apply (KR max min root0); try assumption; try lia. unfold itm_root. rewrite <- ER0.
      replace (root0 <? min) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - zs. replace (wz 1) with (wz (if max =? 1 then 0 else 1)) by (replace (max =? 1) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      apply (KR max min min); try assumption; try lia. unfold itm_root. rewrite <- ER0.
      destruct (Z.ltb_spec root0 min); lia. }
  unfold PC_IT_MINL.
  pose proof (u16arr_read psegs _ (bv_unsigned (tx_sp X) + -136) (av16 cnt 16) mn _ (wa (bv_unsigned (tx_sp X) + -136 + 2 * mn)) CNT
                (av16_nth cnt 16 mn ltac:(lia)) ltac:(lia) eq_refl) as RD.
  zs. rewrite zx16_small by lia. clear RD. zs. br_cases K.
  -
    apply (JOIN mn); [| lia]. exact (fm_stop _ cnt max n mn FM K).
  - pose proof (fm_next _ cnt max n mn (mn + 1) FM ltac:(lia) eq_refl K) as FM'. clear FM.
    zs. zs. zs. zs. br_cases Kb2.
    +
      replace (bv_unsigned (tx_sp X) + -136 + 2 * mn + 2) with (bv_unsigned (tx_sp X) + -136 + 2 * (mn + 1)) by lia.
      replace (max - mn + -1) with (max - (mn + 1)) by lia.
      eapply (IH max (mn + 1) root0); [exact EM| lia| lia| lia| exact FM'| exact ER0].
    +
      zs. replace (mn + 1) with max in FM' by lia. apply (JOIN max); [| lia]. exact (fm_end _ cnt max n FM').
Qed.

Lemma itab_maxj : forall (max : Z) (x1 x6 x7 x8 x9 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  itm_max cnt = max -> 2 <= max <= 15 -> x7 = wz (arr_get cnt 15) ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) (wz max) x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 (wz (tx_bits X))
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_MAXJ) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros EM Rmax ->.
  pose proof XO as XO'. destruct XO' as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (itm_min_rec cnt max ltac:(lia)) as FM.
  unfold PC_IT_MAXJ. zs. br_cases K.
  - zs. zs. zs. zs.
    replace (wz (bv_unsigned (tx_sp X) + -134)) with (wz (bv_unsigned (tx_sp X) + -136 + 2 * 1)) by (f_equal; lia).
    eapply (itab_minloop 16 max 1 (tx_bits X)); [exact EM| lia| lia| lia| exact FM|].
    replace (max <? tx_bits X) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - zs. zs. zs. zs. zs.
    replace (wz (bv_unsigned (tx_sp X) + -134)) with (wz (bv_unsigned (tx_sp X) + -136 + 2 * 1)) by (f_equal; lia).
    eapply (itab_minloop 16 max 1 max); [exact EM| lia| lia| lia| exact FM|].
    destruct (Z.ltb_spec max (tx_bits X)); lia.
Qed.

Ltac mxblk MX Z15 cnt k k' :=
  zs; rewrite zx16_small by lia; zs; let K := fresh "K" in br_cases K;
  [ let M := fresh "MX" in pose proof (mx_next _ cnt _ k k' MX ltac:(lia) ltac:(lia) K) as M; clear MX; rename M into MX
  | zs; zs; zs; apply (itab_maxj k); [exact (mx_stop _ cnt _ k MX ltac:(lia) K)| lia| exact Z15] ].

Definition PC_IT_MAX14 : Z := 0x1ef18.
Lemma itab_cascade : forall (x1 x5 x6 x7 x8 x9 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  itm_max cnt = find_max_rec cnt 15 14 -> arr_get cnt 15 = 0 ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 (wz (tx_bits X))
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_MAX14) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros MX Z15.
  pose proof XO as XO'. destruct XO' as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (cnt_cells_of_arr _ _ _ CNT) as CC. unfold cnt_cells in CC.
  pose proof (TYC 1) as R1. pose proof (TYC 2) as R2. pose proof (TYC 3) as R3. pose proof (TYC 4) as R4. pose proof (TYC 5) as R5.
  pose proof (TYC 6) as R6. pose proof (TYC 7) as R7. pose proof (TYC 8) as R8. pose proof (TYC 9) as R9. pose proof (TYC 10) as R10.
  pose proof (TYC 11) as R11. pose proof (TYC 12) as R12. pose proof (TYC 13) as R13. pose proof (TYC 14) as R14. pose proof (TYC 15) as R15.
  assert (Z15w : wz 0 = wz (arr_get cnt 15)) by (rewrite Z15; reflexivity).
  unfold PC_IT_MAX14.
  mxblk MX Z15w cnt 14 13. mxblk MX Z15w cnt 13 12. mxblk MX Z15w cnt 12 11. mxblk MX Z15w cnt 11 10. mxblk MX Z15w cnt 10 9.
  mxblk MX Z15w cnt 9 8. mxblk MX Z15w cnt 8 7. mxblk MX Z15w cnt 7 6. mxblk MX Z15w cnt 6 5. mxblk MX Z15w cnt 5 4.
  mxblk MX Z15w cnt 4 3. mxblk MX Z15w cnt 3 2.
  zs. rewrite zx16_small by lia. zs. br_cases Kb2.
  2:{ zs. zs. apply (itab_maxj 2); [exact (mx_stop _ cnt _ 2 MX ltac:(lia) Kb2)| lia| exact Z15w]. }
  pose proof (mx_next _ cnt _ 2 1 MX ltac:(lia) ltac:(lia) Kb2) as MX1. clear MX.
  zs. rewrite zx16_small by lia. zs. br_cases Kb1.
  { apply KN. exact (mx_zero _ cnt _ (mx_next _ cnt _ 1 0 MX1 ltac:(lia) ltac:(lia) Kb1)). }
  pose proof (mx_stop _ cnt _ 1 MX1 ltac:(lia) Kb1) as EM. clear MX1.
  zs. zs. zs. zs. zs. zs. br_cases Kb3.
  2:{ exfalso. destruct (0 <? tx_bits X); cbn in Kb3; lia. }
  zs. eapply evt_eq; [| eapply (KR 1 1 1); [exact EM| | | lia| lia| lia]].
  - unfold PC_IT_KRAFT. rewrite Z15. reflexivity.
  - rewrite itm_min_rec by lia. cbn [find_min_rec]. rewrite Z.ltb_irrefl. reflexivity.
  - unfold itm_root. destruct (Z.ltb_spec 1 (tx_bits X)); [reflexivity|]. destruct (Z.ltb_spec (tx_bits X) 1); lia.
Qed.

Lemma itab_cntx : forall (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  isA m (tx_L X) (tx_s X) ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_CNTX) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros GA.
  pose proof XO as XO'. destruct XO' as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (cnt_cells_of_arr _ _ _ CNT) as CC. unfold cnt_cells in CC. pose proof (TYC 15) as R15.
  pose proof (itm_max_rec cnt) as MX.
  unfold PC_IT_CNTX. zs. rewrite zx16_small by lia.
  apply (itab_ldbits X m _ 0x1ef04); [left; reflexivity| exact GA| exact Rb|]. zs. br_cases K.
  - apply itab_cascade; [| exact K]. exact (mx_next _ cnt _ 15 14 MX ltac:(lia) ltac:(lia) K).
  - zs. zs. apply (itab_maxj 15); [exact (mx_stop _ cnt _ 15 MX ltac:(lia) K)| lia| reflexivity].
Qed.

Lemma itab_max0 : forall (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  isA m (tx_L X) (tx_s X) -> (forall i, arr_get cnt i = 0) ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_MAX0) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros GA Z0. pose proof (itm_max_rec cnt) as MX.
  unfold PC_IT_MAX0. apply (itab_ldbits X m _ 0x1ef14); [right; reflexivity| exact GA| exact Rb|].
  apply itab_cascade; [| apply Z0]. exact (mx_next _ cnt _ 15 14 MX ltac:(lia) ltac:(lia) (Z0 15)).
Qed.
End MaxMin.
End Z_itab_max.


Module Z_itab_nosym.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_itab_defs Z_itab_pure Z_itab_ldefs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_offs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].

Lemma itab_nosym : forall X low cnt wk tb m o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15
    (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  rw_cells psegs m (bv_unsigned (tx_sp X) + -192) low -> Z.of_nat (cells_size low) = 26 ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -166) (ofs_junk o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15) ->
  u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16)) ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -104) (it_saved X) -> stk psegs m (tx_lo X) (bv_unsigned (tx_sp X) + -192) ->
  u8arr psegs m (il_As (tx_L X) + 808) (u16s (av16 wk 288)) -> u32arr psegs m (il_As (tx_L X) + 1384) (av32 tb 1444) ->
  mem_inv psegs m -> munch (tx_W1 X) (tx_m0 X) m -> wmono psegs (tx_m0 X) m ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> arr_len wk = 288 -> arr_len tb = 1444 -> ty32 tb ->
  0 <= tx_table X -> tx_table X + 2 <= 1444 ->
  tx_call X = (0, arr_set (arr_set tb (tx_table X) (code_pack 64 1 0)) (tx_table X + 1) (code_pack 64 1 0), tx_table X + 2, 1, wk) ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (tx_F X) (wz PC_IT_NOSYM) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros LOW SZ OFSC CNT SAV ST Gw Gc MI MU WM XO IST0 LW LT TYT Rt0 Rt2 CALL. pose proof XO as XO'.
  destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof (it_saved_bound _ m SAV) as BSP. unfold ofs_junk in OFSC.
  pose proof (av16_zlength cnt 16 ltac:(lia)) as L16c. pose proof (av16_zlength wk 288 ltac:(lia)) as L16w.
  pose proof (av32_zlength tb 1444 ltac:(lia)) as L32.
  pose proof (isA_munch (tx_m0 X) m _ _ _ (ist_A _ _ _ IST0) MU WM ltac:(unfold tx_W1; cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as GA.
  pose proof (isT_munch (tx_m0 X) m _ _ _ (ist_T _ _ _ IST0) MU WM ltac:(unfold tx_W1; cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as GT.
  pose proof (ilens_munch (tx_m0 X) m _ _ _ (ist_lens _ _ _ IST0) MU WM ltac:(unfold tx_W1; cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as Gl.
  assert (Gwin : iwin m (tx_L X) (tx_s X)).
  { apply (iwin_munch (tx_m0 X) m _ _ _ (ist_win _ _ _ IST0) MU WM). intros NE. pose proof (XWIN NE). destruct LAY as [_ LW']. destruct (LW' NE) as [_ AP].
    unfold apart in AP. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]]. }
  pose proof (munch_refl [(il_As (tx_L X) + 136, il_As (tx_L X) + 144); (il_As (tx_L X) + 160, il_As (tx_L X) + 168);
                          (il_As (tx_L X) + 1384 + 4 * tx_table X, il_As (tx_L X) + 1384 + 4 * tx_table X + 8)] m) as MUa.
  pose proof (wmono_refl psegs m) as WMa.
  apply (munch_weaken _ _ _ _ (tx_W1_sub X)) in MU. unfold tx_W1, tx_W in MU.
  unfold isA, isA_cells in GA. change (is_next (tx_s X)) with (tx_table X) in GA.
  set (A := il_As (tx_L X) + 1384) in *.
  unfold PC_IT_NOSYM. zs. zs. zs. zs.
  pose proof (TYT (tx_table X)) as Rc0.
  pose proof (u32arr_store_ok_part _ A _ (tx_table X) 0 2 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_h0 m0 A tb 1444 (tx_table X) w 320 Gc ltac:(lia) ltac:(lia) Rc0 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * tx_table X) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  pose proof (av32_zlength (arr_set tb (tx_table X) (put_h0 (arr_get tb (tx_table X)) 320)) 1444 ltac:(lia)) as L32.
  pose proof (put_h0_range (arr_get tb (tx_table X)) 320 Rc0) as Rc1.
  zs.
  pose proof (u32arr_store_ok_part _ A _ (tx_table X) 2 2 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_h1 m0 A tb 1444 (tx_table X) _ w 0 Gc ltac:(lia) ltac:(lia) Rc1 ltac:(reflexivity)) as Gc';
      replace (A + 4 * tx_table X + 2) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  rewrite put2_pack in Gc by lia. change (320 mod 256) with 64 in Gc. change (320 / 256) with 1 in Gc. clear Rc0 Rc1.
  set (tb1 := arr_set tb (tx_table X) (code_pack 64 1 0)) in Gc.
  pose proof (av32_zlength tb1 1444 ltac:(lia)) as L32. pose proof (arr_len_set tb (tx_table X) (code_pack 64 1 0)) as LT1. fold tb1 in LT1.
  assert (TYT1 : ty32 tb1) by (apply ty32_set; [exact TYT| apply code_pack_ty]).
  zs. zs.
  pose proof (TYT1 (tx_table X + 1)) as Rc0.
  pose proof (u32arr_store_ok_part _ A _ (tx_table X + 1) 0 2 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_h0 m0 A tb1 1444 (tx_table X + 1) w 320 Gc ltac:(lia) ltac:(lia) Rc0 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * (tx_table X + 1)) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  pose proof (av32_zlength (arr_set tb1 (tx_table X + 1) (put_h0 (arr_get tb1 (tx_table X + 1)) 320)) 1444 ltac:(lia)) as L32.
  pose proof (put_h0_range (arr_get tb1 (tx_table X + 1)) 320 Rc0) as Rc1.
  pose proof (u32arr_store_ok_part _ A _ (tx_table X + 1) 2 2 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_h1 m0 A tb1 1444 (tx_table X + 1) _ w 0 Gc ltac:(lia) ltac:(lia) Rc1 ltac:(reflexivity)) as Gc';
      replace (A + 4 * (tx_table X + 1) + 2) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  rewrite put2_pack in Gc by lia. change (320 mod 256) with 64 in Gc. change (320 / 256) with 1 in Gc. clear Rc0 Rc1.
  set (tb2 := arr_set tb1 (tx_table X + 1) (code_pack 64 1 0)) in Gc.
  pose proof (av32_zlength tb2 1444 ltac:(lia)) as L32. pose proof (arr_len_set tb1 (tx_table X + 1) (code_pack 64 1 0)) as LT2. fold tb2 in LT2.
  zs. zs. zs. unfold tx_bitsA. destruct (tx_dsel X) eqn:ED; zs.
  all: subst A; subst tb2; subst tb1.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    pose proof (isT_munch m mf _ _ _ GT MUa WMa ltac:(cbn [disjoint_from]; lia)) as GT';
    pose proof (ilens_munch m mf _ _ _ Gl MUa WMa ltac:(cbn [disjoint_from]; lia)) as Gl';
    assert (Gwin' : iwin mf (tx_L X) (tx_s X)) by (apply (iwin_munch m mf _ _ _ Gwin MUa WMa); intros NE; cbn [disjoint_from]; destruct LAY as [[_ _] LW']; destruct (LW' NE) as [_ AP]; unfold apart in AP; lia) end.
  all: destruct (itab_frame_merge' X _ _ _ _ LOW SZ OFSC ltac:(reflexivity) CNT SAV) as (j & FR).
  all: eapply (itab_epilogue X 0 (it_res_state (tx_s X) (tx_dsel X) (arr_set (arr_set tb (tx_table X) (code_pack 64 1 0)) (tx_table X + 1) (code_pack 64 1 0)) (tx_table X + 2) 1 wk));
    [exact XO'| exact FR| exact ST| | exact MI| exact MU| exact WM| apply it_result_eq; exact CALL].
  all: apply IST_result; [exact XO'| | exact GT'| exact Gl'| split; [exact (proj1 Gw)| exact (proj2 Gw)]| exact Gc| exact Gwin'| exact LW| rewrite !arr_len_set; exact LT].
  all: unfold isA, it_res_state, it_bits_set; rewrite ED; unfold isA_cells; ired; close_cells GA.
Qed.
End Z_itab_nosym.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab_ldefs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_offs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_sort OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_init OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_kraft OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_max OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_nosym OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_itab.Z_itab_lx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3 RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].

Record ITCM (X : itx) (low ofsc : list cell) (cnt wk tb : arr) (m : mem) : Prop := mkITCM {
  cm_low : rw_cells psegs m (bv_unsigned (tx_sp X) + -192) low;
  cm_ofs : rw_cells psegs m (bv_unsigned (tx_sp X) + -166) ofsc;
  cm_cnt : u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16));
  cm_sav : rw_cells psegs m (bv_unsigned (tx_sp X) + -104) (it_saved X);
  cm_stk : stk psegs m (tx_lo X) (bv_unsigned (tx_sp X) + -192);
  cm_work : u8arr psegs m (il_As (tx_L X) + 808) (u16s (av16 wk 288));
  cm_codes : u32arr psegs m (il_As (tx_L X) + 1384) (av32 tb 1444);
  cm_lens : u8arr psegs m (il_As (tx_L X) + 168) (u16s (av16 (tx_lens X) 320));
  cm_mi : mem_inv psegs m;
  cm_mu : munch (tx_W1 X) (tx_m0 X) m;
  cm_wm : wmono psegs (tx_m0 X) m }.

Definition low_shape (low : list cell) : Prop := exists j1 ja jb j2, low = [CB 8 j1; CB 8 ja; CB 8 jb; CB 2 j2].
Definition ofs_shape (ofsc : list cell) : Prop :=
  exists o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15, ofsc = ofs_junk o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15.

Section Phases.
Variables (X : itx) (low ofsc : list cell) (cnt : arr) (m : mem).
Hypothesis CM : ITCM X low ofsc cnt (is_work (tx_s X)) (is_codes (tx_s X)) m.
Hypothesis LSH : low_shape low.
Hypothesis OSH : ofs_shape ofsc.
Hypothesis XO : itx_ok X.
Hypothesis IST0 : IST (tx_m0 X) (tx_L X) (tx_s X).
Hypothesis Ecnt : cnt = itm_count (tx_lens X) (tx_lofs X) (tx_codes X).
Hypothesis SAFE : it_safe (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X) (is_work (tx_s X)) = true.
Hypothesis ATY0 : ATY (tx_s X).
Hypothesis L15 : forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15.
Hypothesis Rtab : 0 <= tx_table X <= 1444.
Hypothesis Rb : 0 <= tx_bits X <= 15.
Hypothesis HCX : it_codes_ok (tx_ty X) (tx_codes X).

Lemma cnt_ty16 : ty16 cnt.
Proof. intros i. rewrite Ecnt, itm_count_eq. apply itm_count_k_range. Qed.
Lemma cnt_len : arr_len cnt = 16.
Proof. rewrite Ecnt, itm_count_eq. apply itm_count_k_len. Qed.

Lemma itab_KN : nosym_K X cnt m.
Proof.
  unfold nosym_K. intros until x31; intros EM0.
  destruct CM as [LOW OFSC CNT SAV ST Gw Gc Gl MI MU WM]. destruct LSH as (j1 & ja & jb & j2 & EL). destruct OSH as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & o12 & o13 & o14 & o15 & EO).
  subst low ofsc. pose proof (xo_arrs X XO) as (LL & LW & LT & _). destruct ATY0 as (TYL & TYW & TYT).
  pose proof (it_safe_max0 _ _ _ _ _ _ _ _ SAFE) as SM. cbv zeta in SM. rewrite <- Ecnt in SM. specialize (SM EM0).
  eapply itab_nosym; [exact LOW| reflexivity| exact OFSC| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact MI| exact MU| exact WM
    | exact XO| exact IST0| exact LW| exact LT| exact TYT| lia| lia|].
  unfold tx_call. apply inflate_table_eq_max0. rewrite <- Ecnt. exact EM0.
Qed.

Lemma itab_KR : kraft_K X cnt m.
Proof.
  unfold kraft_K. intros until x31; intros EM EMIN ER Rmax Rmin Rroot.
  destruct CM as [LOW OFSC CNT SAV ST Gw Gc Gl MI MU WM]. destruct LSH as (j1 & ja & jb & j2 & EL). destruct OSH as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & o12 & o13 & o14 & o15 & EO).
  subst low ofsc. pose proof (xo_arrs X XO) as (LL & LW & LT & _). destruct ATY0 as (TYL & TYW & TYT).
  assert (NZ : itm_max (itm_count (tx_lens X) (tx_lofs X) (tx_codes X)) <> 0) by (rewrite <- Ecnt; lia).
  eapply itab_kraft; [exact LOW| reflexivity| exact OFSC| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact Gl| exact MI| exact MU| exact WM
    | exact XO| exact IST0| apply cnt_ty16| apply cnt_len| exact LW| exact LT| |].
  -
    intros R. unfold tx_call. apply inflate_table_eq_reject; [exact NZ|]. rewrite <- Ecnt, EM. exact R.
  - intros NR x7' x16' x27'.
    pose proof (it_safe_sort _ _ _ _ _ _ _ _ SAFE NZ) as SS. cbv zeta in SS. rewrite <- Ecnt, EM, EMIN, ER, LW, LT in SS.
    unfold tx_lens in SS at 2. rewrite LL in SS. specialize (SS NR). destruct SS as [SOK LP].
    eapply evt_cut; [eapply itab_offs; [exact LOW| reflexivity| exact OFSC| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact Gl| exact MI| exact MU| exact WM
      | exact XO| apply cnt_ty16| apply cnt_len| exact LW| exact LT]|].
    intros ms' (y1 & y7 & y8 & y9 & y16 & y18 & y19 & y20 & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & m' & -> & SM).
    eapply evt_cut; [eapply itab_sort; [exact SM| reflexivity| exact XO| intros i; rewrite itm_offs_eq; apply itm_offs_k_range| rewrite itm_offs_eq; apply itm_offs_k_len
      | exact TYW| exact LW| exact TYL| exact L15| rewrite <- it_sort_ok_eq; exact SOK]|].
    intros ms'' (z1 & z7 & z8 & z9 & z12 & z16 & z18 & z19 & z20 & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z28 & z29 & z30 & z31 & m'' & -> & SM').
    pose proof (itm_sort_k_len (tx_lens X) (tx_lofs X) (tx_codes X) (itm_offs cnt) (is_work (tx_s X))) as [_ LW1]. rewrite LW in LW1.
    rewrite itm_work_eq in LP.
    eapply itab_type; [apply ITSM_ITM; exact SM'| exact XO| exact IST0| exact Rroot| exact Rmax| exact Rmin| lia| apply cnt_ty16| apply cnt_len| exact TYT| exact LT
      | intros i; apply itm_sort_k_work_range; exact TYW| exact LW1| |].
    + intros NE. unfold tx_call. rewrite (inflate_table_eq_nospace (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X) (is_work (tx_s X)) NZ);
        rewrite <- ?Ecnt, ?EM, ?EMIN, ?ER; [rewrite itm_work_eq; reflexivity| exact NR| exact NE].
    + intros NE. destruct (LP NE) as (_ & _ & OK). split; [exact OK|]. split.
      { assert (HC19 : tx_ty X = CODES -> tx_codes X <= 19) by (intros E; pose proof HCX as H; rewrite E in H; exact H).
        assert (HL286 : tx_ty X = LENS -> tx_codes X <= 286) by (intros E; pose proof HCX as H; rewrite E in H; exact H).
        destruct (ity_code_cases (tx_ty X)) as [[_ TY]|[[_ TY]|[_ TY]]].
        3: { apply it_lx_dists. unfold itm_ctx. cbn [x_ty]. exact TY. }
        all: assert (H288 : 0 <= tx_codes X <= 288)
               by (pose proof (xo_codes X XO); first [pose proof (HC19 TY) | pose proof (HL286 TY)]; lia).
        all: assert (LX := it_lx_intro (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X)
                         (is_work (tx_s X)) cnt max min root H288 HC19 HL286
                         ltac:(intros i Hi; unfold tx_lens; pose proof (TYL i); split; [lia|];
                               replace i with (tx_lofs X + (i - tx_lofs X)) by lia; apply L15; pose proof (xo_codes X XO); lia)
                         ltac:(lia) Ecnt EM ltac:(lia) NR EMIN ER).
        all: rewrite itm_work_eq in LX; exact LX. }
      unfold tx_call. rewrite (inflate_table_eq_loop (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X) (is_work (tx_s X)) NZ);
        rewrite <- ?Ecnt, ?EM, ?EMIN, ?ER; [rewrite itm_work_eq; reflexivity| exact NR| exact NE].
Qed.
End Phases.

Definition cnt_post (X : itx) (low ofsc : list cell) (wk tb : arr) (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    : machine_state -> Prop :=
  fun ms' => exists x6 x7 m',
    ms' = MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) (wz (tx_lensA X + 2 * tx_codes X)) x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
                 (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808))
                 (wz (tx_lensA X + 2 * tx_codes X)) (wz (bv_unsigned (tx_sp X) + -136))
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_CNTX) (tx_fc X) None m' (seg_rom psegs)
    /\ ITCM X low ofsc (itm_count_k (tx_lens X) (tx_lofs X) (tx_codes X)) wk tb m'.

Lemma itab_count_loop : forall n X low ofsc cnt wk tb m (k : Z) (x1 x6 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  ITCM X low ofsc cnt wk tb m -> cnt = itm_count_k (tx_lens X) (tx_lofs X) k ->
  Z.of_nat (cells_size low) = 26 -> Z.of_nat (cells_size ofsc) = 30 ->
  itx_ok X -> ty16 (tx_lens X) -> (forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15) ->
  0 <= k < tx_codes X -> tx_codes X - k <= Z.of_nat n -> arr_len wk = 288 -> arr_len tb = 1444 ->
  evt psegs (cnt_post X low ofsc wk tb x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) (wz (tx_lensA X + 2 * k)) x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808))
             (wz (tx_lensA X + 2 * tx_codes X)) (wz (bv_unsigned (tx_sp X) + -136))
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_CNT) (tx_fc X) None m (seg_rom psegs)).
Proof.
  induction n as [|n IH]; intros until x31; intros CM Ec SZ SZO XO TYL L15 Rk Rn LW LT; [lia|].
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  destruct CM as [LOW OFSC CNT SAV ST Gw Gc Gl MI MU WM]. unfold tx_W1 in MU. pose proof (it_saved_bound _ m SAV) as BSP.
  pose proof (av16_zlength cnt 16 ltac:(lia)) as L16c. pose proof (av16_zlength wk 288 ltac:(lia)) as L16w.
  pose proof (av32_zlength tb 1444 ltac:(lia)) as L32. pose proof (av16_zlength (tx_lens X) 320 ltac:(lia)) as L16l.
  assert (RLA : 0 < tx_lensA X /\ tx_lensA X + 2 * tx_codes X < 2 ^ 62) by (unfold tx_lensA; lia).
  assert (LC : arr_len cnt = 16) by (rewrite Ec; apply itm_count_k_len).
  assert (TYC : ty16 cnt) by (intros i; rewrite Ec; apply itm_count_k_range).
  pose proof (L15 k ltac:(lia)) as Rl. pose proof (TYL (tx_lofs X + k)) as Rl0. set (len := arr_get (tx_lens X) (tx_lofs X + k)) in *.
  pose proof (TYC len) as Rc. set (c := arr_get cnt len) in *.
  unfold PC_IT_CNT.
  pose proof (u16arr_read psegs _ (il_As (tx_L X) + 168) (av16 (tx_lens X) 320) (tx_lofs X + k) _ (wa (tx_lensA X + 2 * k)) Gl
                (av16_nth (tx_lens X) 320 (tx_lofs X + k) ltac:(lia)) ltac:(lia) ltac:(unfold tx_lensA; f_equal; lia)) as RD.
  zs. rewrite zx16_small by lia. clear RD. fold len.
  zs. zs. zs.
  pose proof (u16arr_read psegs _ (bv_unsigned (tx_sp X) + -136) (av16 cnt 16) len (wz c) (wa (bv_unsigned (tx_sp X) + -136 + 2 * len)) CNT (av16_nth cnt 16 len ltac:(lia)) ltac:(lia) eq_refl) as RD.
  zs. clear RD. zs. rewrite (shl1 len).
  st16 CNT cnt 16 (bv_unsigned (tx_sp X) + -136) len (wrap16 (c + 1)) ltac:(rewrite le2_swrap16_add by lia; reflexivity).
  assert (Ec' : arr_set cnt len (wrap16 (c + 1)) = itm_count_k (tx_lens X) (tx_lofs X) (k + 1)).
  { rewrite itm_count_k_step by lia. cbv zeta. rewrite <- Ec. reflexivity. }
  zs. br_cases K.
  -
    replace (tx_lensA X + 2 * k + 2) with (tx_lensA X + 2 * (k + 1)) by lia.
    eapply (IH X low ofsc _ wk tb _ (k + 1)); [| exact Ec'| exact SZ| exact SZO| exact XO'| exact TYL| exact L15| lia| lia| exact LW| exact LT].
    split; assumption.
  -
    apply evt_done. unfold cnt_post, PC_IT_CNTX. do 3 eexists.
    replace (tx_lensA X + 2 * k + 2) with (tx_lensA X + 2 * tx_codes X) by lia. split; [reflexivity|].
    replace (tx_codes X) with (k + 1) by lia. rewrite <- Ec'. split; assumption.
Qed.

Lemma low_split : forall m A junk, rw_cells psegs m A [CB 26 junk] -> exists low, rw_cells psegs m A low /\ low_shape low.
Proof.
  intros m A junk H. pose proof (rw_cells_split_CB psegs m A [] 26 junk [] [8; 8; 8; 2]%nat H eq_refl) as H'.
  cbn [app mk_CB_cells] in H'. eexists. split; [exact H'|]. do 4 eexists. reflexivity.
Qed.
Lemma ofs_split : forall m A junk, rw_cells psegs m A [CB 30 junk] -> exists ofsc, rw_cells psegs m A ofsc /\ ofs_shape ofsc.
Proof.
  intros m A junk H. pose proof (rw_cells_split_CB psegs m A [] 30 junk [] [2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2]%nat H eq_refl) as H'.
  cbn [app mk_CB_cells] in H'. eexists. split; [exact H'|]. do 15 eexists. reflexivity.
Qed.
Lemma low_shape_size : forall low, low_shape low -> Z.of_nat (cells_size low) = 26.
Proof. intros low (j1 & ja & jb & j2 & ->). reflexivity. Qed.
Lemma ofs_shape_size : forall ofsc, ofs_shape ofsc -> Z.of_nat (cells_size ofsc) = 30.
Proof. intros ofsc (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & o12 & o13 & o14 & o15 & ->). reflexivity. Qed.

Lemma cnt_zero_view : forall m A lens lofs,
  rw_cells psegs m A [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> u8arr psegs m A (u16s (av16 (itm_count_k lens lofs 0) 16)).
Proof.
  intros m A lens lofs H. rewrite itm_count_k_0 by lia. apply (u8arr_of_rw_cells psegs m A 32).
  apply (rw_cells_recast m A _ _ H); [cbn; split; [reflexivity| exact I]|].
  unfold av16. change (zseq 16) with [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]. cbn [map].
  rewrite !it_zero_count_spec. reflexivity.
Qed.

Lemma ITCM_isA : forall X low ofsc cnt wk tb m, itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ITCM X low ofsc cnt wk tb m -> isA m (tx_L X) (tx_s X).
Proof.
  intros X low ofsc cnt wk tb m XO ST CM. apply (isA_munch (tx_m0 X) m _ _ (tx_W1 X)); [exact (ist_A _ _ _ ST)| exact (cm_mu _ _ _ _ _ _ _ CM)| exact (cm_wm _ _ _ _ _ _ _ CM)|].
  pose proof (xo_As X XO) as HA. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]].
Qed.

Lemma itab_function : forall X (x5 x6 x7 x16 x17 x28 x29 x30 x31 : word),
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> mem_inv psegs (tx_m0 X) ->
  stk psegs (tx_m0 X) (tx_lo X) (bv_unsigned (tx_sp X)) ->
  0 <= tx_table X <= 1444 -> 0 <= tx_bits X <= 15 ->
  it_safe (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X) (is_work (tx_s X)) = true ->
  ATY (tx_s X) -> (forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15) ->
  it_codes_ok (tx_ty X) (tx_codes X) ->
  evt psegs (itab_post X)
    (MS (mkR (tx_ra X) (tx_sp X) (tx_gp X) (tx_tp X) x5 x6 x7 (tx_s0 X) (tx_s1 X) (wz (ity_code (tx_ty X))) (wz (tx_lensA X)) (wz (tx_codes X))
             (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17 (tx_s2 X) (tx_s3 X) (tx_s4 X) (tx_s5 X)
             (tx_s6 X) (tx_s7 X) (tx_s8 X) (tx_s9 X) (tx_s10 X) (tx_s11 X) x28 x29 x30 x31)
        (tx_F X) (wz Z_INFLATE_TABLE) (tx_fc X) None (tx_m0 X) (seg_rom psegs)).
Proof.
  intros until x31; intros XO IST0 MI ST Rtab Rb SAFE ATY0 L15 HCX. pose proof XO as XO'.
  destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  assert (LO0 : 0 <= tx_lo X) by exact (proj1 ST).
  pose proof (munch_refl (tx_W1 X) (tx_m0 X)) as MU. unfold tx_W1 in MU. pose proof (wmono_refl psegs (tx_m0 X)) as WM.
  pose proof IST0 as [GA GT Gl Gw Gc Gwin _ _]. unfold ilens, u16arr in Gl. unfold iwork, u16arr in Gw. unfold icodes in Gc.
  change (is_lens (tx_s X)) with (tx_lens X) in Gl.
  pose proof ARRS as (LL & LW & LT & _). pose proof ATY0 as (TYL & TYW & TYT). change (is_lens (tx_s X)) with (tx_lens X) in TYL.
  pose proof (av16_zlength (tx_lens X) 320 ltac:(unfold tx_lens; lia)) as L16l. pose proof (av16_zlength (is_work (tx_s X)) 288 ltac:(lia)) as L16w.
  pose proof (av32_zlength (is_codes (tx_s X)) 1444 ltac:(lia)) as L32.
  assert (RLA : 0 < tx_lensA X /\ tx_lensA X + 2 * tx_codes X < 2 ^ 62) by (unfold tx_lensA; lia).
  set (m := tx_m0 X) in *.
  carve_frame 104%nat ST. rename FR into SAV.
  carve_frame 32%nat ST. rename FR into CNT.
  carve_frame 30%nat ST. destruct (ofs_split _ _ _ FR) as (ofsc & OFSC & OSH). clear FR. pose proof (ofs_shape_size ofsc OSH) as SZO.
  carve_frame 26%nat ST. destruct (low_split _ _ _ FR) as (low & LOW & LSH). clear FR. pose proof (low_shape_size low LSH) as SZ.
  unfold Z_INFLATE_TABLE. do 18 zs.
  apply (cnt_zero_view _ _ (tx_lens X) (tx_lofs X)) in CNT.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (CM : ITCM X low ofsc (itm_count_k (tx_lens X) (tx_lofs X) 0) (is_work (tx_s X)) (is_codes (tx_s X)) m1) by (split; assumption) end.
  zs. br_cases K.
  -
    assert (Ecnt : itm_count_k (tx_lens X) (tx_lofs X) 0 = itm_count (tx_lens X) (tx_lofs X) (tx_codes X)) by (rewrite itm_count_eq, K; reflexivity).
    eapply (itab_max0 X _ _ CNT XO' ltac:(intros i; apply itm_count_k_range) Rb);
      [ eapply itab_KR; eassumption| eapply itab_KN; eassumption| eapply ITCM_isA; eassumption| intros i; rewrite itm_count_k_0 by lia; apply it_zero_count_spec].
  -
    zs. zs. rewrite zext32_x2 by lia. zs. zs. zs.
    replace (wz (tx_lensA X)) with (wz (tx_lensA X + 2 * 0)) at 2 by (f_equal; lia).
    eapply evt_cut; [eapply (itab_count_loop (Z.to_nat (tx_codes X)) X low ofsc _ _ _ _ 0);
      [exact CM| reflexivity| exact SZ| exact SZO| exact XO'| exact TYL| exact L15| lia| lia| exact LW| exact LT]|].
    intros ms' (y6 & y7 & m' & -> & CM').
    eapply (itab_cntx X _ m' (cm_cnt _ _ _ _ _ _ _ CM') XO' ltac:(intros i; apply itm_count_k_range) Rb);
      [ eapply itab_KR; try eassumption; symmetry; apply itm_count_eq| eapply itab_KN; try eassumption; symmetry; apply itm_count_eq| eapply ITCM_isA; eassumption].
Qed.

Theorem inflate_table_proof : inflate_table_stmt.
Proof.
  unfold inflate_table_stmt.
  intros L s ty dsel lens_ofs codes lo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST MI STK Rlo HAS HWIN Rlofs Rcodes Rsum Rnext Rbits SAFE ATY0 L15 H286 -> -> -> -> -> ->.
  pose proof (ist_lay _ _ _ ST) as [BA _]. unfold blk_ok in BA. unfold Z_ITABLE_STACK in Rlo.
  apply (itab_function (mkITX L s ty dsel lens_ofs codes lo m sp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)); cbn [tx_lo tx_sp tx_L tx_s tx_m0 tx_table tx_bits tx_ty tx_lens tx_lofs tx_codes tx_dsel].
  - constructor; cbn [tx_lo tx_sp tx_L tx_s tx_lofs tx_codes]; [unfold Z_ITABLE_STACK; lia| lia| exact HWIN| lia| exact (ist_arrs _ _ _ ST)| exact (ist_lay _ _ _ ST)].
  - exact ST.
  - exact MI.
  - exact STK.
  - exact Rnext.
  - exact Rbits.
  - exact SAFE.
  - exact ATY0.
  - exact L15.
  - exact H286.
Qed.
