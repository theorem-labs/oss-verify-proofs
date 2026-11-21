(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Zh_kit Z_infl_iface Z_itab_kit Z_itab_defs. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_itab_pure. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_itab_ldefs Z_itab_exit Z_itab_offs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees ItableModel ItableModel2 RefInflateSafeTY.
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

(* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  zs.
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  zs. zs.
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
