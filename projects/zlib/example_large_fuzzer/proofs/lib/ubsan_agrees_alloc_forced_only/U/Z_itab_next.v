(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Zh_kit Z_infl_iface Z_infl_pure2 Z_itab_kit Z_itab_defs Z_itab_ldefs Z_ukit Z_itab_exit Z_itab_fill Z_itab_head.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_itab_pure.
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
Lemma shl_32 : forall x, x ≪ 32 = x * 4294967296.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma mul32_shr31 : forall x, 0 <= x -> (x * 4294967296) ≫ 31 = 2 * x.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 31) with 2147483648. Z.div_mod_to_equations. lia. Qed.
Lemma mul32_shr30 : forall x, 0 <= x -> (x * 4294967296) ≫ 30 = 4 * x.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 30) with 1073741824. Z.div_mod_to_equations. lia. Qed.
Lemma mul32_shr32 : forall x, 0 <= x -> (x * 4294967296) ≫ 32 = x.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296. Z.div_mod_to_equations. lia. Qed.
Lemma itab_nextsym : forall X root max cnt wk tb ms (huff sym len incr b6 : Z)
    x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
  ITL X root max PC_IT_HUFF (mkLS x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31) cnt wk tb ms ->
  x26 = wz len -> x30 = wz huff -> x7 = wz incr -> x22 = wz sym -> x6 = wz b6 ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> incr = it_incr_back huff len ->
  0 <= sym < 288 -> 1 <= len <= 15 -> 0 <= huff < 65536 -> 1 <= max <= 15 -> ty16 wk -> ty16 cnt -> arr_len cnt = 16 ->
  (let c := wrap16 (arr_get cnt len - 1) in c = 0 -> len <> max ->
   let w' := arr_get wk (sym + 1) in sym + 1 < 288 /\ 0 <= w' /\ 0 <= tx_lofs X + w' < 320 /\ 1 <= arr_get (tx_lens X) (tx_lofs X + w') <= 15) ->
  evt usegs (fun ms' => exists x6' x7' x18' x19' x28',
    let c := wrap16 (arr_get cnt len - 1) in
    ITL X root max (if (c =? 0) && (len =? max) then PC_IT_DONE else PC_IT_NEXT)
        (mkLS x1 (if (c =? 0) && negb (len =? max) then x6' else x6) x7' x9 x16 x18' x19' x20 x21 (wz (sym + 1)) x23 x25
              (wz (if (c =? 0) && negb (len =? max) then arr_get (tx_lens X) (tx_lofs X + arr_get wk (sym + 1)) else len))
              x27 x28' x29 (wz (it_huff_next huff len)) (wz ((sym + 1) * 4294967296)))
        (arr_set cnt len c) wk tb ms') ms.
Proof.
  intros until x31; intros HL E26 E30 E7 E22 E6 XO IST0 Hincr Rsym Rlen Rhuff Rmax TYW TYC LC Hnx.
  itl_open HL; subst x26 x30 x7 x22 x6; destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (ilens_munch (tx_m0 X) m _ _ _ (ist_lens _ _ _ IST0) MU WM ltac:(cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as Gl.
  unfold ilens, u16arr in Gl. change (is_lens (tx_s X)) with (tx_lens X) in Gl. pose proof (av16_zlength (tx_lens X) 320 ltac:(lia)) as L16l.
  assert (RLA : 0 < tx_lensA X /\ tx_lensA X + 2 * 320 < 2 ^ 62 /\ tx_lensA X mod 2 = 0) by (unfold tx_lensA; lia).
  assert (Rincr : 0 <= incr <= 16384).
  { rewrite Hincr, it_incr_back_rec, shl32_pow2' by lia. pose proof (incr_rec_range huff 32 (2 ^ (len - 1)) ltac:(apply Z.pow_nonneg; lia)).
    assert (2 ^ (len - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *. lia. }
  pose proof (TYC len) as Rcl. set (cl := arr_get cnt len) in *. pose proof (av32_zlength tb 1444 ltac:(lia)) as L32.
  pose proof (land_le_r (Z.land (incr + -1) 18446744073709551615) huff ltac:(lia)) as Rl.
  unfold PC_IT_HUFF. zs. ustep PC_IT_TRAP. zs. rewrite (shl1 len). unfold notc. ustep PC_IT_TRAP.
  zs. zs. zs. zs. zs.
  pose proof (u16arr_read usegs _ (bv_unsigned (tx_sp X) + -136) (av16 cnt 16) len (wz cl) (wa (bv_unsigned (tx_sp X) + -136 + 2 * len)) CNT (av16_nth cnt 16 len ltac:(lia)) ltac:(lia) eq_refl) as RD.
  zs. clear RD. zs. zs. zs. zs. zs.
  pose proof (huff_next_mach huff len Rhuff Rlen) as HN; cbv zeta in HN; rewrite <- Hincr in HN; rewrite HN; clear HN.
  zs. zs.
  st16 CNT cnt 16 (bv_unsigned (tx_sp X) + -136) len (wrap16 (cl - 1)) ltac:(rewrite le2_swrap16_add by lia; do 3 f_equal; lia).
  zs. zs. rewrite shl_32. zs. br_cases K; rewrite dec48_land in K by lia.
  -
    apply evt_done. exists (wz 0). do 4 eexists. cbv zeta. fold cl.
    replace (wrap16 (cl - 1) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. unfold PC_IT_NEXT. itl_close.
  -
    assert (Hc0 : wrap16 (cl - 1) = 0) by lia.
    zs. br_cases K2.
    +
      apply evt_done. exists (wz 0). do 4 eexists. cbv zeta. fold cl. replace (wrap16 (cl - 1) =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (len =? max) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb negb]. unfold PC_IT_DONE. itl_close.
    +
      destruct (Hnx Hc0 ltac:(lia)) as (Rs1 & Rw1 & Rli & Rln).
      zs. rewrite mul32_shr31 by lia. zs. unfold notw. ustep PC_IT_TRAP. zs. ustep PC_IT_TRAP. ustep PC_IT_TRAP.
      ld16 Gw wk 288 (il_As (tx_L X) + 808) (sym + 1) ltac:(apply TYW).
      zs. rewrite (shl1 (arr_get wk (sym + 1))). zs.
      uwalk 0x223ec PC_IT_TRAP.
      pose proof (u16arr_read usegs _ (il_As (tx_L X) + 168) (av16 (tx_lens X) 320) (tx_lofs X + arr_get wk (sym + 1)) _
                    (wa (tx_lensA X + 2 * arr_get wk (sym + 1))) Gl (av16_nth (tx_lens X) 320 (tx_lofs X + arr_get wk (sym + 1)) ltac:(lia))
                    ltac:(lia) ltac:(unfold tx_lensA; f_equal; lia)) as RD.
      zs. rewrite zx16_small by lia. clear RD.
      apply evt_done. do 5 eexists. cbv zeta. fold cl. replace (wrap16 (cl - 1) =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (len =? max) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. unfold PC_IT_NEXT. itl_close.
Qed.
