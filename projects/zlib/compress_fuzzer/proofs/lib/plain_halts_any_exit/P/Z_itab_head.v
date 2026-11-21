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
