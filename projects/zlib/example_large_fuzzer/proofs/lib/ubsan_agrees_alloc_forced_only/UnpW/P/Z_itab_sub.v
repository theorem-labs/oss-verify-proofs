(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Zh_kit Z_infl_iface Z_itab_kit Z_itab_defs. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_itab_pure. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_itab_ldefs Z_itab_head Z_itab_next.
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

Definition PC_IT_SUB2 : Z := 0x1f7d8.

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
