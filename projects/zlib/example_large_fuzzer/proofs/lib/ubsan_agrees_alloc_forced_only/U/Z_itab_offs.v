From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Zh_kit Z_infl_iface Z_infl_pure2 Z_itab_kit Z_itab_defs Z_itab_ldefs Z_ukit Z_itab_exit Z_itab_head Z_itab_next Z_itab_sub Z_itab_init Z_itab_sort.
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
Ltac norm_psum :=
  repeat match goal with |- context [Z.to_nat ?e] => let v := eval vm_compute in (Z.to_nat e) in change (Z.to_nat e) with v end;
  cbn [psum];
  repeat match goal with |- context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v end.
Definition ofs_junk (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 : list byte) : list cell :=
  [CB 2 o1; CB 2 o2; CB 2 o3; CB 2 o4; CB 2 o5; CB 2 o6; CB 2 o7; CB 2 o8; CB 2 o9; CB 2 o10; CB 2 o11; CB 2 o12; CB 2 o13; CB 2 o14; CB 2 o15].
Definition offs_post (X : itx) (low : list cell) (cnt wk tb : arr) (x5 x6 x17 : word) : machine_state -> Prop :=
  fun ms' => exists x1 x8 x9 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
    ms' = MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 (wz (bv_unsigned (tx_sp X) + -168)) x8 x9 (wz (ity_code (tx_ty X)))
                 (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_SORT0) (tx_fc X) None m' (seg_rom usegs)
    /\ ITSM X low cnt (itm_offs cnt) wk tb m'.
Lemma itab_offs : forall X low cnt wk tb m o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 (x1 x5 x6 x7 x16 x17 x27 x29 : word),
  rw_cells usegs m (bv_unsigned (tx_sp X) + -208) low -> Z.of_nat (cells_size low) = 42 ->
  rw_cells usegs m (bv_unsigned (tx_sp X) + -166) (ofs_junk o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15) ->
  u8arr usegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16)) ->
  rw_cells usegs m (bv_unsigned (tx_sp X) + -104) (it_saved X) -> stk usegs m (tx_lo X) (bv_unsigned (tx_sp X) + -208) ->
  u8arr usegs m (il_As (tx_L X) + 808) (u16s (av16 wk 288)) -> u32arr usegs m (il_As (tx_L X) + 1384) (av32 tb 1444) ->
  u8arr usegs m (il_As (tx_L X) + 168) (u16s (av16 (tx_lens X) 320)) ->
  mem_inv usegs m -> munch (tx_W1 X) (tx_m0 X) m -> wmono usegs (tx_m0 X) m ->
  itx_ok X -> ty16 cnt -> arr_len cnt = 16 -> arr_len wk = 288 -> arr_len tb = 1444 ->
  evt usegs (offs_post X low cnt wk tb x5 x6 x17)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 x7 (wz (arr_get cnt 4)) (wz (arr_get cnt 5)) (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             (wz (arr_get cnt 6)) (wz (arr_get cnt 7)) (wz (arr_get cnt 8)) (wz (arr_get cnt 9)) (wz (arr_get cnt 10)) (wz (arr_get cnt 11))
             (wz (arr_get cnt 12)) (wz (arr_get cnt 13)) (wz (arr_get cnt 14)) x27 (wz (arr_get cnt 1)) x29 (wz (arr_get cnt 2)) (wz (arr_get cnt 3)))
        (tx_F X) (wz PC_IT_OFFS) (tx_fc X) None m (seg_rom usegs)).
Proof.
  intros until x29; intros LOW SZ OFSC CNT SAV ST Gw Gc Gl MI MU WM XO TYC LC LW LT.
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO. unfold tx_W1 in MU.
  pose proof (it_saved_bound _ m SAV) as BSP. unfold ofs_junk in OFSC.
  pose proof (av16_zlength cnt 16 ltac:(lia)) as L16c. pose proof (av16_zlength wk 288 ltac:(lia)) as L16w.
  pose proof (av32_zlength tb 1444 ltac:(lia)) as L32. pose proof (av16_zlength (tx_lens X) 320 ltac:(lia)) as L16l.
  pose proof (TYC 1) as R1. pose proof (TYC 2) as R2. pose proof (TYC 3) as R3. pose proof (TYC 4) as R4. pose proof (TYC 5) as R5.
  pose proof (TYC 6) as R6. pose proof (TYC 7) as R7. pose proof (TYC 8) as R8. pose proof (TYC 9) as R9. pose proof (TYC 10) as R10.
  pose proof (TYC 11) as R11. pose proof (TYC 12) as R12. pose proof (TYC 13) as R13. pose proof (TYC 14) as R14.
  unfold PC_IT_OFFS. zs. zs. zs. br_false. do 28 zs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    assert (OFS : u8arr usegs mf (bv_unsigned (tx_sp X) + -166) (u16s (av16s (itm_offs cnt) 1 15))) end.
  { lazymatch goal with |- u8arr _ ?mf _ _ => apply (ofs_arr_of_cells mf) end.
    eapply rw_cells_recast; [exact OFSC| cbn; tauto|].
    unfold ofs_cells. rewrite !itm_offs_psum by lia. cbn [cells_bytes cbytes app].
    repeat (apply (f_equal2 (@app byte)); [rewrite <- le2_wz_wrap16; f_equal; f_equal; norm_psum; lia|]). reflexivity. }
  clear OFSC. apply evt_done. unfold offs_post, PC_IT_SORT0. do 19 eexists. split; [reflexivity|]. split; assumption.
Qed.
