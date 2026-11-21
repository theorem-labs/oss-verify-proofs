(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Zh_kit Z_infl_iface Z_itab_kit Z_itab_defs Z_itab_pure Z_itab_ldefs Z_itab_head.
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
