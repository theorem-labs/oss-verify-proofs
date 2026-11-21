(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Zh_kit Z_infl_iface Z_infl_pure2 Z_itab_kit Z_itab_defs Z_itab_ldefs Z_ukit Z_itab_exit Z_itab_fill Z_itab_head Z_itab_next.
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
Lemma shr30_small : forall a, 0 <= a < 1073741824 -> a ≫ 30 = 0.
Proof. intros a Ha. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. change (2 ^ 30) with 1073741824. lia. Qed.
Lemma itab_left : forall n X root max cnt wk tb ms (k dp lft : Z)
    x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
  ITL X root max PC_IT_LEFT (mkLS x23 x7 x6 x9 x16 x28 x19 x20 x21 x22 x1 x25 x26 x27 x18 x29 x30 x31) cnt wk tb ms ->
  x7 = wz lft -> x25 = wz (max - dp) -> x1 = wz dp -> x16 = wz k ->
  itx_ok X -> 0 <= dp <= k -> k < max -> max <= 15 -> 0 < lft <= 2 ^ k -> ty16 cnt -> arr_len cnt = 16 -> max - k <= Z.of_nat n ->
  evt usegs (fun ms' => exists x7' x16' x28',
    let c := fst (curr_rec cnt dp max n (k - dp) lft) in
    ITL X root max PC_IT_USED (mkLS x23 x7' x6 x9 x16' x28' x19 x20 x21 x22 x1 (wz c) x26 x27 x18 x29 x30 x31) cnt wk tb ms') ms.
Proof.
  induction n as [|n IH]; intros until x31; intros HL E7 E25 E1 E16 XO Rdp Rk Rmax Rlft TYC LC Rn; [lia|].
  itl_open HL; subst x7 x25 x1 x16; destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (TYC k) as Rck. pose proof (pow2_le15 k ltac:(lia)) as Pk.
  cbn [curr_rec]. rewrite curr_step_small' by lia. replace (k - dp + dp) with k by lia.
  replace (k <? max) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold PC_IT_LEFT at 1. zs. rewrite (shl1 k). unfold notc. ustep PC_IT_TRAP. zs. ld16 CNT cnt 16 (bv_unsigned (tx_sp X) + -136) k ltac:(lia).
  zs. zs. br_sgtz KL.
  -
    replace (lft - arr_get cnt k <=? 0) with true by (symmetry; apply Z.leb_le; lia). cbn [fst].
    zs. zs. ustep PC_IT_TRAP.
    apply evt_done. do 3 eexists. unfold PC_IT_USED. itl_close.
  -
    replace (lft - arr_get cnt k <=? 0) with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
    zs. rewrite srliw_small, shr30_small by lia. ustep PC_IT_TRAP. zs. zs. zs. br_cases KM.
    +
      replace ((lft - arr_get cnt k) ≪ 1) with (2 * (lft - arr_get cnt k)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      replace (k - dp + 1) with (k + 1 - dp) by lia.
      eapply IH; [unfold PC_IT_LEFT; itl_close| reflexivity| reflexivity| reflexivity| reflexivity| split; assumption| lia| lia| lia| | exact TYC| exact LC| lia].
      rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
    +
      zs. zs. ustep PC_IT_TRAP.
      replace (fst (curr_rec cnt dp max n (k - dp + 1) ((lft - arr_get cnt k) ≪ 1))) with (max - dp).
      2:{ destruct n as [|n']; cbn [curr_rec]; [cbn [fst]; lia|]. rewrite curr_step_small' by lia.
          replace (k - dp + 1 + dp <? max) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst]. lia. }
      apply evt_done. do 3 eexists. unfold PC_IT_USED. itl_close.
Qed.
Definition PC_IT_ENTRY : Z := 0x224c8.
Definition used_post (X : itx) (root max : Z) (cnt wk tb : arr) (huff sym len next curr used low' c : Z) : machine_state -> Prop :=
  fun ms' =>
      let next' := next + 2 ^ curr in
      let used' := used + 2 ^ c in
      if it_not_enough (tx_ty X) used' then exists q', ITL X root max PC_IT_EPI q' cnt wk tb ms' /\ l16 q' = wz 1
      else exists x1' x18' x19' x20' x23' x27' x28' x31',
        ITL X root max PC_IT_TRIP (mkLS x1' (wz (len - root)) (wz (il_As (tx_L X) + 808 + 2 * sym)) (wz (il_As (tx_L X) + 1384 + 4 * next')) (wz low')
                                         x18' x19' x20' (wz root) (wz sym) x23' (wz c) (wz len) x27' x28' (wz used') (wz huff) x31') cnt wk
            (arr_set tb (tx_table X + low') (code_pack c root (next' - tx_table X))) ms'.
Lemma itab_used_entry : forall X root max cnt wk tb ms (huff sym len next curr used' low' c : Z)
    x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
  ITL X root max PC_IT_ENTRY (mkLS x23 x7 x6 x9 x16 x28 x19 x20 x21 x22 x1 x25 x26 x27 x18 x29 x30 x31) cnt wk tb ms ->
  x1 = wz root -> x6 = wz (il_As (tx_L X) + 1384 + 4 * (next + 2 ^ curr)) -> x23 = wz low' -> x25 = wz c -> x26 = wz len -> x22 = wz sym ->
  x31 = wz (sym * 4294967296) -> x29 = wz used' -> x30 = wz huff ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) ->
  1 <= root <= 15 -> 1 <= len <= 15 -> 0 <= curr <= 15 -> 0 <= c <= 15 -> 0 <= sym <= 288 ->
  0 <= low' < 65536 -> 0 <= tx_table X <= next -> next <= 1444 -> arr_len tb = 1444 -> ty32 tb -> 0 <= tx_table X + low' < 1444 ->
  evt usegs (fun ms' => exists x1' x18' x19' x20' x23' x27' x28' x31',
        ITL X root max PC_IT_TRIP (mkLS x1' (wz (len - root)) (wz (il_As (tx_L X) + 808 + 2 * sym)) (wz (il_As (tx_L X) + 1384 + 4 * (next + 2 ^ curr))) (wz low')
                                         x18' x19' x20' (wz root) (wz sym) x23' (wz c) (wz len) x27' x28' (wz used') (wz huff) x31') cnt wk
            (arr_set tb (tx_table X + low') (code_pack c root (next + 2 ^ curr - tx_table X))) ms') ms.
Proof.
  intros until x31; intros HL E1 E6 E23 E25 E26 E22 E31 E29 E30 XO IST0 Rroot Rlen Rcurr Rc Rsym Rlow Rtab Rroom LT TYT ENT.
  itl_open HL; subst x1 x6 x23 x25 x26 x22 x31 x29 x30; destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (pow2_le15 c ltac:(lia)) as Pc. pose proof (pow2_le15 curr ltac:(lia)) as Pcu.
  pose proof (isA_munch (tx_m0 X) m _ _ _ (ist_A _ _ _ IST0) MU WM ltac:(cbn [disjoint_from]; split; [lia| split; [lia| exact I]])) as GA.
  unfold isA, isA_cells in GA. change (is_next (tx_s X)) with (tx_table X) in GA.
  unfold PC_IT_ENTRY at 1. zs. zs. rewrite shl2. zs. uwalk 0x224f4 PC_IT_TRAP.
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
  ustep PC_IT_TRAP. zs. zs.
  match goal with |- context [wz (?d ≫ 2)] =>
    replace (d ≫ 2) with (next + 2 ^ curr - tx_table X) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 2) with 4; Z.div_mod_to_equations; lia) end.
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
      pose proof (av32_put_h1 m0 A tb 1444 idx _ w (next + 2 ^ curr - tx_table X) Gc ltac:(lia) ltac:(lia) Rc2 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * idx + 2) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  rewrite put3_pack in Gc. clear Rc0 Rc1 Rc2.
  pose proof (av32_zlength (arr_set tb idx (code_pack c root (next + 2 ^ curr - tx_table X))) 1444 ltac:(lia)) as L32.
  zs. zs.
  zs. zs. rewrite mul32_shr31 by lia. zs. zs. zs. zs. unfold notw. ustep PC_IT_TRAP.
  apply evt_done. do 8 eexists. unfold PC_IT_TRIP. subst idx A. itl_close.
Qed.
Lemma lor1_b2z : forall b, Z.lor 1 (Z.b2z b) = 1.
Proof. intros [|]; reflexivity. Qed.
Lemma lor0_b2z : forall b, Z.lor 0 (Z.b2z b) = Z.b2z b.
Proof. intros [|]; reflexivity. Qed.
Lemma ity_code_cases : forall ty, (ity_code ty = 0 /\ ty = CODES) \/ (ity_code ty = 1 /\ ty = LENS) \/ (ity_code ty = 2 /\ ty = DISTS).
Proof. intros [| |]; cbn; tauto. Qed.
Lemma itab_used : forall X root max cnt wk tb ms (huff sym len next curr used low' c : Z)
    x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
  ITL X root max PC_IT_USED (mkLS x23 x7 x6 x9 x16 x28 x19 x20 x21 x22 x1 x25 x26 x27 x18 x29 x30 x31) cnt wk tb ms ->
  x1 = wz root -> x6 = wz (il_As (tx_L X) + 1384 + 4 * (next + 2 ^ curr)) -> x23 = wz low' -> x25 = wz c -> x26 = wz len -> x22 = wz sym ->
  x31 = wz (sym * 4294967296) -> x29 = wz used -> x30 = wz huff ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) ->
  1 <= root <= 15 -> 1 <= len <= 15 -> 0 <= curr <= 15 -> 0 <= c <= 15 -> 0 <= huff < 65536 -> 0 <= used < 65536 -> 0 <= sym <= 288 ->
  0 <= low' < 65536 -> 0 <= tx_table X <= next -> next <= 1444 -> arr_len tb = 1444 -> ty32 tb ->
  (it_not_enough (tx_ty X) (used + 2 ^ c) = false -> 0 <= tx_table X + low' < 1444) ->
  evt usegs (used_post X root max cnt wk tb huff sym len next curr used low' c) ms.
Proof.
  intros until x31; intros HL E1 E6 E23 E25 E26 E22 E31 E29 E30 XO IST0 Rroot Rlen Rcurr Rc Rhuff Rused Rsym Rlow Rtab Rroom LT TYT ENT.
  pose proof XO as XO'.
  itl_open HL; subst x1 x6 x23 x25 x26 x22 x31 x29 x30; destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (pow2_le15 c ltac:(lia)) as Pc. pose proof (pow2_le15 curr ltac:(lia)) as Pcu.
  unfold used_post. cbv zeta.
  unfold PC_IT_USED at 1. destruct (ity_code_cases (tx_ty X)) as [[EC TY]|[[EC TY]|[EC TY]]]; rewrite EC.
  -
    assert (EN : it_not_enough (tx_ty X) (used + 2 ^ c) = false) by (rewrite TY; reflexivity). rewrite EN in *.
    zs. zs. zs. zs. rewrite sllw_1 by lia. zs. zs. zs. replace (0 <? 18446744073709551615) with true by reflexivity. rewrite lor1_b2z.
    zs. br_false. zs. zs. zs. zs. zs. replace (18446744073709551614 <? 1) with false by reflexivity. cbn [Z.b2z Z.land].
    zs. br_false. specialize (ENT eq_refl).
    eapply itab_used_entry; [unfold PC_IT_ENTRY; itl_close| treg| treg| treg| treg| treg| treg| treg| treg| treg| exact XO'| exact IST0| | | | | | | | | exact LT| exact TYT| exact ENT]; lia.
  -
    assert (EN : it_not_enough (tx_ty X) (used + 2 ^ c) = (852 <? used + 2 ^ c)) by (rewrite TY; reflexivity). rewrite EN in *.
    zs. zs. zs. zs. rewrite sllw_1 by lia. zs. zs. zs. replace (0 <? 0) with false by reflexivity. rewrite lor0_b2z.
    zs. br_cases K5.
    {
      replace (852 <? used + 2 ^ c) with true by (symmetry; apply Z.ltb_lt; lia).
      apply evt_done. cbv beta. eexists (mkLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). split; [unfold PC_IT_EPI; itl_close| reflexivity]. }
    replace (852 <? used + 2 ^ c) with false in * by (symmetry; apply Z.ltb_ge; lia).
    zs. zs. zs. zs. zs. replace (18446744073709551615 <? 1) with false by reflexivity. cbn [Z.b2z Z.land].
    zs. br_false. specialize (ENT eq_refl).
    eapply itab_used_entry; [unfold PC_IT_ENTRY; itl_close| treg| treg| treg| treg| treg| treg| treg| treg| treg| exact XO'| exact IST0| | | | | | | | | exact LT| exact TYT| exact ENT]; lia.
  -
    assert (EN : it_not_enough (tx_ty X) (used + 2 ^ c) = (592 <? used + 2 ^ c)) by (rewrite TY; reflexivity). rewrite EN in *.
    zs. zs. zs. zs. rewrite sllw_1 by lia. zs. zs. zs. replace (0 <? 1) with true by reflexivity. rewrite lor1_b2z.
    zs. br_false. zs. zs. zs. zs. zs. replace (0 <? 1) with true by reflexivity.
    destruct (Z.ltb_spec (2 ^ c + used) 593) as [K6|K6].
    2:{
      change (Z.land (Z.b2z true) (Z.lxor (Z.b2z false) 1)) with 1. zs. br_true.
      replace (592 <? used + 2 ^ c) with true by (symmetry; apply Z.ltb_lt; lia).
      apply evt_done. cbv beta. eexists (mkLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). split; [unfold PC_IT_EPI; itl_close| reflexivity]. }
    change (Z.land (Z.b2z true) (Z.lxor (Z.b2z true) 1)) with 0. zs. br_false.
    replace (592 <? used + 2 ^ c) with false in * by (symmetry; apply Z.ltb_ge; lia). specialize (ENT eq_refl).
    eapply itab_used_entry; [unfold PC_IT_ENTRY; itl_close| treg| treg| treg| treg| treg| treg| treg| treg| treg| exact XO'| exact IST0| | | | | | | | | exact LT| exact TYT| exact ENT]; lia.
Qed.
Lemma sext_lowx : forall low, (low = 4294967295 \/ 0 <= low < 65536) -> bv_swrap 32 (Z.land (lowx low) 18446744073709551615 + 0) = lowx low.
Proof.
  intros low Hl. unfold lowx. destruct Hl as [-> | Hl].
  - rewrite Z.eqb_refl. reflexivity.
  - replace (low =? 4294967295) with false by (symmetry; apply Z.eqb_neq; lia). rewrite land_ones64 by lia. rewrite Z.add_0_r.
    apply bv_swrap32_id. change (2^31) with 2147483648. lia.
Qed.
Definition PC_IT_SUB2 : Z := 0x2241c.
Lemma itab_sub2 : forall X root max cnt wk tb ms (huff sym len next curr used low' : Z)
    x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
  ITL X root max PC_IT_SUB2 (mkLS x23 x7 x6 x9 x16 x28 x19 x20 x21 x22 x1 x25 x26 x27 x18 x29 x30 x31) cnt wk tb ms ->
  x1 = wz root -> x26 = wz len -> x20 = wz (2 ^ curr) -> x9 = wz (il_As (tx_L X) + 1384 + 4 * next) -> x30 = wz huff -> x23 = wz low' ->
  x29 = wz used -> x22 = wz sym -> x31 = wz (sym * 4294967296) ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) ->
  1 <= root <= 15 -> 1 <= max <= 15 -> root < len <= 15 -> 0 <= curr <= 15 -> 0 <= huff < 65536 -> 0 <= used < 65536 -> 0 <= sym <= 288 ->
  0 <= low' < 65536 -> 0 <= tx_table X <= next -> next <= 1444 -> ty16 cnt -> arr_len cnt = 16 -> arr_len tb = 1444 -> ty32 tb ->
  (it_not_enough (tx_ty X) (used + 2 ^ it_subtable_curr cnt len root max) = false -> 0 <= tx_table X + low' < 1444) ->
  evt usegs (used_post X root max cnt wk tb huff sym len next curr used low' (it_subtable_curr cnt len root max)) ms.
Proof.
  intros until x31; intros HL E1 E26 E20 E9 E30 E23 E29 E22 E31 XO IST0 Rroot Rmax Rlen Rcurr Rhuff Rused Rsym Rlow Rtab Rroom TYC LC LT TYT SUBOK.
  pose proof XO as XO'.
  itl_open HL; subst x1 x26 x20 x9 x30 x23 x29 x22 x31; destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (pow2_le15 (len - root) ltac:(lia)) as Plr. pose proof (pow2_le15 curr ltac:(lia)) as Pcu.
  rewrite it_subtable_curr_eq in * by lia.
  pose proof (curr_rec_bound cnt root max 16 (len - root) (2 ^ (len - root)) ltac:(lia) ltac:(lia) ltac:(lia)) as CB.
  unfold PC_IT_SUB2 at 1. ustep PC_IT_TRAP. zs. rewrite shl_32. zs. rewrite mul32_shr30 by lia. zs. ustep PC_IT_TRAP. ustep PC_IT_TRAP.
  zs. zs. ustep PC_IT_TRAP. zs. br_cases K4.
  -
    revert CB SUBOK. cbn [curr_rec]. rewrite curr_step_small' by lia. replace (len - root + root <? max) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst].
    intros CB SUBOK.
    eapply itab_used; [unfold PC_IT_USED; itl_close| treg..| exact XO'| exact IST0| | | | | | | | | | | exact LT| exact TYT| exact SUBOK]; lia.
  -
    zs. zs. rewrite sllw_1 by lia. zs. zs.
    eapply evt_cut.
    { eapply (itab_left 16); [unfold PC_IT_LEFT; itl_close| reflexivity| treg| reflexivity| reflexivity| exact XO'| lia| lia| lia| | exact TYC| exact LC| cbn; lia].
      pose proof (pow2_le15 len ltac:(lia)). split; [lia|]. apply Z.pow_le_mono_r; lia. }
    cbv beta. intros ms1 (x7' & x16' & x28' & HL1). cbv zeta in HL1.
    eapply itab_used; [exact HL1| treg..| exact XO'| exact IST0| | | | | | | | | | | exact LT| exact TYT| exact SUBOK]; lia.
Qed.
Definition sub_post (X : itx) (root max : Z) (cnt wk tb : arr) (huff sym len next curr drop low used : Z) : machine_state -> Prop :=
  fun ms' =>
    let mask := 2 ^ root - 1 in
    if (root <? len) && negb (Z.land huff mask =? low)
    then used_post X root max cnt wk tb huff sym len next curr used (Z.land huff mask) (it_subtable_curr cnt len root max) ms'
    else exists x1' x18' x19' x20' x23' x27' x28' x31',
        ITL X root max PC_IT_TRIP (mkLS x1' (wz (len - drop)) (wz (il_As (tx_L X) + 808 + 2 * sym)) (wz (il_As (tx_L X) + 1384 + 4 * next)) (wz (lowx low))
                                         x18' x19' x20' (wz drop) (wz sym) x23' (wz curr) (wz len) x27' x28' (wz used) (wz huff) x31') cnt wk tb ms'.
Lemma itab_sub : forall X root max cnt wk tb ms (huff sym len next curr drop low used : Z)
    x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
  ITL X root max PC_IT_NEXT (mkLS x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31) cnt wk tb ms ->
  x26 = wz len -> x20 = wz (2 ^ curr) -> x9 = wz (il_As (tx_L X) + 1384 + 4 * next) -> x30 = wz huff -> x21 = wz drop ->
  x16 = wz (lowx low) -> x29 = wz used -> x22 = wz sym -> x31 = wz (sym * 4294967296) -> x25 = wz curr ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) ->
  1 <= root <= 15 -> 1 <= max <= 15 -> 1 <= len <= 15 -> 0 <= curr <= 15 -> 0 <= huff < 65536 -> 0 <= used < 65536 -> 0 <= sym <= 288 ->
  (if drop =? 0 then root else drop) = root -> 0 <= drop <= 15 -> (low = 4294967295 \/ 0 <= low < 65536) ->
  0 <= tx_table X <= next -> next <= 1444 -> ty16 cnt -> arr_len cnt = 16 -> arr_len tb = 1444 -> ty32 tb ->
  (root < len -> Z.land huff (2 ^ root - 1) <> low -> it_not_enough (tx_ty X) (used + 2 ^ it_subtable_curr cnt len root max) = false ->
   0 <= tx_table X + Z.land huff (2 ^ root - 1) < 1444) ->
  evt usegs (sub_post X root max cnt wk tb huff sym len next curr drop low used) ms.
Proof.
  intros until x31; intros HL E26 E20 E9 E30 E21 E16 E29 E22 E31 E25 XO IST0 Rroot Rmax Rlen Rcurr Rhuff Rused Rsym Hdp Rdrop Rlow Rtab Rroom TYC LC LT TYT SUBOK.
  pose proof XO as XO'.
  itl_open HL; subst x26 x20 x9 x30 x21 x16 x29 x22 x31 x25; destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof (pow2_root_bounds root Rroot) as Pr. pose proof (land_le_r huff (2 ^ root - 1) ltac:(lia)) as Rlm. pose proof (pow2_le15 curr ltac:(lia)) as Pcu.
  assert (Rlx : lowx low = -1 \/ 0 <= lowx low < 65536) by (unfold lowx; destruct Rlow as [->|R]; [left; reflexivity| right; replace (low =? 4294967295) with false by (symmetry; apply Z.eqb_neq; lia); lia]).
  assert (SAME : forall (y1 y6 y12 y23 y24 : word) m', ITM X (it_low X root jg) cnt ofs wk tb m' ->
    evt usegs (fun ms' => exists x1' x18' x19' x20' x23' x27' x28' x31',
        ITL X root max PC_IT_TRIP (mkLS x1' (wz (len - drop)) (wz (il_As (tx_L X) + 808 + 2 * sym)) (wz (il_As (tx_L X) + 1384 + 4 * next)) (wz (lowx low))
                                         x18' x19' x20' (wz drop) (wz sym) x23' (wz curr) (wz len) x27' x28' (wz used) (wz huff) x31') cnt wk tb ms')
      (MS (mkR y1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) (wz max) y6 (wz (tx_match X)) (wz (sym * 4294967296)) (wz (bv_unsigned (tx_sp X) + -136))
               (wz (ity_code (tx_ty X))) (wz (tx_lensA X)) y12 (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808))
               (wz (lowx low)) (wz root) (wz (il_As (tx_L X) + 1384 + 4 * next)) x19 (wz (2 ^ curr)) x28 (wz drop) y23 y24 (wz (notc X)) (wz curr) (wz len) x18 (wz sym) (wz used) (wz huff))
          (tx_F X) (wz PC_IT_SUBJ) (tx_fc X) None m' (seg_rom usegs))).
  { intros y1 y6 y12 y23 y24 m' TM. destruct TM as [LOW' OFS' CNT' SAV' ST' Gw' Gc' MI' MU' WM']. unfold it_low in LOW'. unfold tx_W1 in MU'. unfold u16arr in Gw'.
    pose proof (it_saved_bound _ m' SAV') as BSP'.
    unfold PC_IT_SUBJ. zs. zs. zs. zs. rewrite mul32_shr31 by lia. zs. zs. zs. zs. unfold notw. ustep PC_IT_TRAP.
    apply evt_done. do 8 eexists. unfold PC_IT_TRIP. itl_close. }
  unfold sub_post. cbv zeta.
  unfold PC_IT_NEXT at 1. zs. br_cases K1.
  {
    replace (root <? len) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
    apply SAME. itm_close. }
  replace (root <? len) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  zs. zs. zs. rewrite sext_lowx by exact Rlow. zs. br_cases K2.
  {
    apply (proj1 (lowx_test (Z.land huff (2 ^ root - 1)) low ltac:(lia) Rlow)) in K2.
    replace (Z.land huff (2 ^ root - 1) =? low) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
    apply SAME. itm_close. }
  assert (NEL : Z.land huff (2 ^ root - 1) <> low) by (intros E; apply K2, (proj2 (lowx_test (Z.land huff (2 ^ root - 1)) low ltac:(lia) Rlow)), E). clear K2.
  replace (Z.land huff (2 ^ root - 1) =? low) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  specialize (SUBOK ltac:(lia) NEL).
  zs. zs. br_cases K3.
  - eapply itab_sub2; [unfold PC_IT_SUB2; itl_close| treg..| exact XO'| exact IST0| | | | | | | | | | | exact TYC| exact LC| exact LT| exact TYT| exact SUBOK]; lia.
  - zs. replace drop with root by (rewrite <- Hdp; replace (drop =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply itab_sub2; [unfold PC_IT_SUB2; itl_close| treg..| exact XO'| exact IST0| | | | | | | | | | | exact TYC| exact LC| exact LT| exact TYT| exact SUBOK]; lia.
Qed.
