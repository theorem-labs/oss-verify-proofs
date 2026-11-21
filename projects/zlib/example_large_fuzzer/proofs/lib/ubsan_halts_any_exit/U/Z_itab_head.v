From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Zh_kit Z_infl_iface Z_infl_pure2 Z_itab_kit Z_itab_defs Z_itab_ldefs Z_ukit Z_itab_exit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_itab_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees ItableModel ItableModel2 RefInflateSafeTY.
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
Lemma shl1 : forall x, x ≪ 1 = 2 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia. lia. Qed.
Lemma shl8 : forall x, x ≪ 8 = x * 256.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma shl16 : forall x, x ≪ 16 = x * 65536.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma lor_op_bits : forall op b, 0 <= op < 256 -> 0 <= b -> Z.lor op (b * 256) = b * 256 + op.
Proof. intros op b Ho Hb. rewrite Z.lor_comm. change 256 with (2 ^ 8). apply lor_hi_lo; lia. Qed.
Lemma lor_val_lo : forall v lo, 0 <= lo < 65536 -> 0 <= v -> Z.lor (v * 65536) lo = v * 65536 + lo.
Proof. intros v lo Hl Hv. change 65536 with (2 ^ 16). apply lor_hi_lo; lia. Qed.
Lemma shr16_pack : forall v lo, 0 <= lo < 65536 -> 0 <= v -> (v * 65536 + lo) ≫ 16 = v.
Proof. intros v lo Hl Hv. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. Z.div_mod_to_equations. lia. Qed.
Lemma extra_base_facts : forall X, tx_ty X <> CODES ->
  0 < tx_extraA X /\ tx_extraA X + 1024 < 2 ^ 62 /\ tx_extraA X mod 2 = 0 /\
  0 < tx_baseA X /\ tx_baseA X + 1024 < 2 ^ 62 /\ tx_baseA X mod 2 = 0 /\ tx_flagA X = 1.
Proof.
  intros X HNC. unfold tx_extraA, tx_baseA, tx_flagA, Z_LEXT, Z_LBASE, Z_DEXT, Z_DBASE.
  destruct (tx_ty X); [exfalso; exact (HNC eq_refl)| |]; repeat split; first [reflexivity | lia].
Qed.
Lemma itab_here : forall X root max cnt wk tb ms (huff len curr drop next opv val : Z)
    x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
  ITL X root max PC_IT_HERE (mkLS x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31) cnt wk tb ms ->
  x6 = wz (len - drop) -> x7 = wz opv -> x23 = wz val -> x9 = wz (il_As (tx_L X) + 1384 + 4 * next) -> x30 = wz huff ->
  x21 = wz drop -> x25 = wz curr ->
  itx_ok X -> 1 <= len <= 15 -> 0 <= drop <= len -> 0 <= huff < 65536 -> 0 <= curr <= 15 -> 0 <= next <= 1444 -> 0 <= opv < 256 -> 0 <= val < 65536 ->
  evt usegs (ITL X root max PC_IT_FILL
               (mkLS x1 (wz ((len - drop) * 256)) (wz (2 ^ curr)) x9 x16 (wz 1) (wz val) (wz (2 ^ curr)) x21 x22
                     (wz (val * 65536 + ((len - drop) * 256 + opv))) x25 x26 x27 (wz (- 2 ^ (len - drop))) x29 x30
                     (wz (huff ≫ drop + 2 ^ curr - 2 ^ (len - drop)))) cnt wk tb) ms.
Proof.
  intros until x31. intros HL E6 E7 E23 E9 E30 E21 E25 XO Rlen Rdrop Rhuff Rcurr Rnext Ropv Rval.
  itl_open HL. subst x6 x7 x23 x9 x30 x21 x25.
  destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]. unfold Z_ITABLE_STACK in XLO.
  pose proof (pow2_le15 (len - drop) ltac:(lia)) as Hp2. pose proof (pow2_le15 curr ltac:(lia)) as Hpc.
  assert (Hhs : 0 <= huff ≫ drop <= huff) by (apply shiftr_le'; lia).
  unfold PC_IT_HERE. zs. ustep PC_IT_TRAP. zs. zs. rewrite sllw_m1 by lia. zs. zs. rewrite sllw_1 by lia. zs. rewrite srlw_small' by lia.
  zs. rewrite shl16. zs. rewrite shl8. zs. rewrite lor_op_bits by lia. zs. zs. rewrite lor_val_lo by lia. zs. zs.
  replace (0 <? il_As (tx_L X) + 1384 + 4 * next) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  zs. rewrite shr16_pack by lia. zs.
  apply evt_done. unfold PC_IT_FILL. itl_close.
Qed.
Lemma itab_head : forall X root max cnt wk tb ms (huff sym len curr drop next : Z)
    x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
  ITL X root max PC_IT_TRIP (mkLS x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31) cnt wk tb ms ->
  x6 = wz (len - drop) -> x7 = wz (il_As (tx_L X) + 808 + 2 * sym) -> x9 = wz (il_As (tx_L X) + 1384 + 4 * next) -> x30 = wz huff ->
  x21 = wz drop -> x25 = wz curr ->
  itx_ok X -> 0 <= sym < 288 -> 1 <= len <= 15 -> 0 <= drop <= len -> 0 <= huff < 65536 -> 0 <= curr <= 15 -> 0 <= next <= 1444 -> ty16 wk ->
  (let w := arr_get wk sym in it_match (tx_ty X) <= w -> w - it_match (tx_ty X) < it_ext_len (tx_ty X) 288) ->
  (tx_ty X = LENS -> arr_get wk sym < 286) -> (tx_ty X = CODES -> arr_get wk sym < 19) ->
  evt usegs (ITL X root max PC_IT_FILL
               (mkLS x1 (wz ((len - drop) * 256)) (wz (2 ^ curr)) x9 x16 (wz 1) (wz (it_here_val (tx_ty X) wk (arr_get wk sym))) (wz (2 ^ curr)) x21 x22
                     (wz (it_here_val (tx_ty X) wk (arr_get wk sym) * 65536 + ((len - drop) * 256 + it_here_op (tx_ty X) wk (arr_get wk sym))))
                     x25 x26 x27 (wz (- 2 ^ (len - drop))) x29 x30 (wz (huff ≫ drop + 2 ^ curr - 2 ^ (len - drop)))) cnt wk tb) ms.
Proof.
  intros until x31. intros HL E6 E7 E9 E30 E21 E25 XO Rsym Rlen Rdrop Rhuff Rcurr Rnext TYW Rext RLX RLC.
  itl_open HL. subst x6 x7 x9 x30 x21 x25.
  destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]. unfold Z_ITABLE_STACK in XLO.
  pose proof (TYW sym) as Rw. cbv zeta in Rext.
  assert (Rmt : 0 <= tx_match X <= 257) by (unfold tx_match; destruct (tx_ty X); cbn; lia).
  assert (Emt : tx_match X = it_match (tx_ty X)) by reflexivity.
  assert (Rel : it_ext_len (tx_ty X) 288 <= 288) by (destruct (tx_ty X); cbn; lia).
  pose proof (pow2_le15 (len - drop) ltac:(lia)) as Hp2. pose proof (pow2_le15 curr ltac:(lia)) as Hpc.
  assert (Hhs : 0 <= huff ≫ drop <= huff) by (apply shiftr_le'; lia).
  unfold PC_IT_TRIP. ustep PC_IT_TRAP. ustep PC_IT_TRAP.
  ld16 Gw wk 288 (il_As (tx_L X) + 808) sym ltac:(lia).
  set (w := arr_get wk sym) in *.
  zs. zs. br_cases K.
  -  zs. br_cases K2.
    +
      assert (HNC : tx_ty X <> CODES).
      { intros HC. specialize (RLC HC). assert (tx_match X = 20) by (rewrite Emt, HC; reflexivity). lia. }
      pose proof (extra_base_facts X HNC) as (XE1 & XE2 & XE3 & XB1 & XB2 & XB3 & XF).
      zs. zs. zs. rewrite zext32_x2 by lia. zs. zs. ustep PC_IT_TRAP. zs. zs. rewrite XF. uwalk 0x22294 PC_IT_TRAP.
      zs. rewrite land_ones32 by lia. zs. rewrite shl1. zs. zs.
      pose proof (extra_read X m wk (w - tx_match X) MI Gw ltac:(lia)
                    ltac:(intros HT; specialize (RLX HT); rewrite Emt, HT; cbn [it_match]; lia) HNC) as RD1.
      pose proof (base_read X m wk (w - tx_match X) MI Gw ltac:(lia) HNC) as RD2.
      zs. cbv beta. rewrite bv8_unsigned_wrap. clear RD1.
      zs. rewrite (zx16_small (it_base (tx_ty X) wk (w - tx_match X))) by (apply it_base_range; [exact TYW| lia]). clear RD2.
      pose proof (it_here_op_range (tx_ty X) wk w) as Rop. pose proof (it_here_val_range (tx_ty X) wk w TYW Rw Rext) as Rval.
      eapply (itab_here X root max cnt wk tb _ huff len curr drop next (it_here_op (tx_ty X) wk w) (it_here_val (tx_ty X) wk w));
        [unfold PC_IT_HERE; itl_close| reflexivity| | | reflexivity| reflexivity| reflexivity| reflexivity| split; assumption| lia| lia| lia| lia| lia| exact Rop| exact Rval];
        unfold it_here_val, it_here_op; unfold tx_match in K, K2;
        replace (w + 1 <? it_match (tx_ty X)) with false by (symmetry; apply Z.ltb_ge; lia);
        replace (it_match (tx_ty X) <=? w) with true by (symmetry; apply Z.leb_le; lia); [rewrite wrap8_mod; reflexivity| reflexivity].
    +
      zs. zs. zs.
      pose proof (it_here_op_range (tx_ty X) wk w) as Rop. pose proof (it_here_val_range (tx_ty X) wk w TYW Rw Rext) as Rval.
      eapply (itab_here X root max cnt wk tb _ huff len curr drop next (it_here_op (tx_ty X) wk w) (it_here_val (tx_ty X) wk w));
        [unfold PC_IT_HERE; itl_close| reflexivity| | | reflexivity| reflexivity| reflexivity| reflexivity| split; assumption| lia| lia| lia| lia| lia| exact Rop| exact Rval];
        unfold it_here_val, it_here_op; unfold tx_match in K, K2;
        replace (w + 1 <? it_match (tx_ty X)) with false by (symmetry; apply Z.ltb_ge; lia);
        replace (it_match (tx_ty X) <=? w) with false by (symmetry; apply Z.leb_gt; lia); reflexivity.
  -
    zs. zs.
    pose proof (it_here_op_range (tx_ty X) wk w) as Rop. pose proof (it_here_val_range (tx_ty X) wk w TYW Rw Rext) as Rval.
    eapply (itab_here X root max cnt wk tb _ huff len curr drop next (it_here_op (tx_ty X) wk w) (it_here_val (tx_ty X) wk w));
      [unfold PC_IT_HERE; itl_close| reflexivity| | | reflexivity| reflexivity| reflexivity| reflexivity| split; assumption| lia| lia| lia| lia| lia| exact Rop| exact Rval];
      unfold it_here_val, it_here_op; unfold tx_match in K;
      replace (w + 1 <? it_match (tx_ty X)) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity.
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
    x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
  ITL X root max PC_IT_INCR (mkLS x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31) cnt wk tb ms ->
  x30 = wz huff -> x18 = wz c -> itx_ok X -> 0 <= huff < 65536 -> 0 <= c < 65536 -> c < 2 ^ Z.of_nat n ->
  evt usegs (ITL X root max PC_IT_HUFF
               (mkLS x1 x6 (wz (incr_rec huff n c)) x9 x16 (wz (incr_rec huff n c ≫ 1)) x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 (wz 0)) cnt wk tb) ms.
Proof.
  induction n as [|n IH]; intros until x31; intros HL E30 E18 XO Rhuff Rc Rcn.
  all: itl_open HL; subst x30 x18; destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
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
