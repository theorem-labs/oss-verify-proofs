(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (17 recorded proofs replaced by written proofs (rz_log_small, rz_log_range_small, rz_size_eq and 14 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From stdpp Require Import bitvector.definitions.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AModelFacts () := "C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec8AsanCtrl6rz_logC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega6VarMap1t01c59OSSVerify5KrLib5BothW;AModelFacts<rz_log_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib5BothW;AModelFactsBrz_log_range_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AModelFacts:rz_size_eqC1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01c59OSSVerify5KrLib5BothW;AModelFacts?rounded_size_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7needed0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega7EnvRing5PExpr07K47Corelib7Numbers7BinNums1N02K47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1N01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1ZCtestbit_ones_nonnegC56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z<ldiff_ones_rK47Corelib4Init9Datatypes4bool02C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6NArith6BinNat1N3subC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3oppC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions?bv_half_modulusC45stdpp9bitvector;definitions>bv_swrap_smallC56Stdlib6ZArith6BinInt1Z9mod_smallC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib7Numbers7BinNums1N00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec8AsanCtrl8class_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AModelFacts;small_factsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7amallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init9Datatypes3orbC56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec8AsanCtrl;cache_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl>chunk_user_begC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lnotC59OSSVerify5KrLib4Spec8AsanCtrl7poison0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;large_allocC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:init_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6aundef04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aundef_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlAcls_set_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCpopulate_free_arrayC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib4Spec8AsanCtrl4aretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl3aev00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3oddC59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AModelFacts>class_id_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AModelFactsCsize_of_class_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z3minC59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~".
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma rz_log_small : forall n, 1 <= n <= 448 -> rz_log n = (if n <=? 48 then 0 else if n <=? 96 then 1 else 2).
Proof. intros n H. unfold rz_log. destruct (n <=? 48); [reflexivity|]. destruct (n <=? 96); [reflexivity|].
  replace (n <=? 448) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma rz_log_range_small : forall n, 1 <= n <= 448 -> 0 <= rz_log n <= 2.
Proof. intros n H. rewrite rz_log_small by lia. destruct (n <=? 48); [lia|]. destruct (n <=? 96); lia. Qed.

Lemma rz_size_eq : forall n, rz_size n = 16 * 2 ^ rz_log n.
Proof. intros n. unfold rz_size. rewrite Z.shiftl_mul_pow2. reflexivity. unfold rz_log.
  repeat (destruct (_ <=? _)); lia. Qed.

Lemma rounded_size_eq : forall n, rounded_size n = (Z.max n 8 + 7) / 8 * 8.
Proof. intros n. unfold rounded_size, rup. f_equal. f_equal. lia. Qed.

Lemma small_facts : forall n, 1 <= n <= 448 ->
  is_primary n = true /\ needed_size n = rounded_size n + rz_size n
  /\ 16 <= rz_size n <= 64 /\ rz_size n = 16 * 2 ^ rz_log n
  /\ Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0
  /\ 24 <= needed_size n <= 512.
Proof.
  intros n H.
  pose proof (rz_log_range_small n H) as R. pose proof (rz_size_eq n) as S.
  assert (S2 : 16 <= rz_size n <= 64).
  { rewrite S. assert (2 ^ rz_log n = 1 \/ 2 ^ rz_log n = 2 \/ 2 ^ rz_log n = 4).
    { destruct (Z.eq_dec (rz_log n) 0) as [->|]; [left; reflexivity|]. destruct (Z.eq_dec (rz_log n) 1) as [->|]; [right; left; reflexivity|].
      replace (rz_log n) with 2 by lia. right; right; reflexivity. } lia. }
  pose proof (rounded_size_eq n) as RS.
  assert (RR : Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0).
  { rewrite RS. Z.div_mod_to_equations. lia. }
  assert (P : is_primary n = true).
  { unfold is_primary, needed0, K_MAX_SIZE. apply Z.leb_le. lia. }
  assert (NS : needed_size n = rounded_size n + rz_size n).
  { unfold needed_size. rewrite P. reflexivity. }
  assert (UP : rounded_size n + rz_size n <= 512).
  { rewrite S, RS. rewrite rz_log_small by lia.
    destruct (Z.leb_spec n 48); [cbn; Z.div_mod_to_equations; lia|].
    destruct (Z.leb_spec n 96); cbn; Z.div_mod_to_equations; lia. }
  rewrite NS. split; [exact P|]. split; [reflexivity|]. split; [lia|]. split; [exact S|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* [comment removed for export] *)
Lemma land_align8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
  intros x Hx.
  replace 18446744073709551608 with (Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity.
  replace (x - x mod 8) with (Z.shiftl (Z.shiftr x 3) 3).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma rounded_size_align : forall n, rounded_size n = Z.max n 8 + 7 - (Z.max n 8 + 7) mod 8.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma sllw_rz : forall n, 1 <= n <= 448 ->
  bv_swrap 32 (Z.shiftl 16 ((rz_log n mod 18446744073709551616) mod 32)) = rz_size n.
Proof.
  intros n N. pose proof (rz_log_range_small n N) as RLR. pose proof (rz_size_eq n) as RZE.
  rewrite !(Z.mod_small (rz_log n)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite RZE.
  assert (P4 : 2 ^ rz_log n <= 2 ^ 2) by (apply Z.pow_le_mono_r; lia).
  assert (P1 : 0 < 2 ^ rz_log n) by (apply Z.pow_pos_nonneg; lia).
  apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N (32 - 1)) with 2147483648 by reflexivity. lia.
Qed.

(* [comment removed for export] *)
Lemma land_align8_48 : forall x, 0 <= x < 2^48 -> Z.land x 281474976710648 = x - x mod 8.
Proof.
  intros x Hx.
  replace 281474976710648 with (Z.ldiff (Z.ones 48) (Z.ones 3)) by reflexivity.
  replace (x - x mod 8) with (Z.shiftl (Z.shiftr x 3) 3).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 48) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 48; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma rz_size_small_cases : forall n, 1 <= n <= 448 -> rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64.
Proof.
  intros n N. rewrite rz_size_eq, (rz_log_small n N).
  destruct (n <=? 48); [left; reflexivity|]. destruct (n <=? 96); [right; left; reflexivity| right; right; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma amalloc_fast_eq : forall RESV st n c,
  1 <= n <= 448 -> class_id (needed_size n) = c -> 0 < c_count (get_cls st c) ->
  amalloc ATOP RESV st n =
    SRet (set_next (N.succ (a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)))
            (set_live (<[ a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) := CPrim c n ]>
                        (a_live (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)))
               (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)),
          Some (a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st))).
Proof.
  intros RESV st n c N HC POS. pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  unfold amalloc.
  replace (2 ^ 40 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (2 ^ 40 <? needed_size n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  rewrite PRIM. unfold cache_alloc. rewrite HC.
  replace (0 <? c_count (get_cls st c)) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma a_next_put_cls : forall c r st, a_next (put_cls c r st) = a_next st.
Proof. intros. reflexivity. Qed.
Lemma a_live_put_cls : forall c r st, a_live (put_cls c r st) = a_live st.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma class_id_small : forall s, s <= 512 -> class_id s = Z.shiftr (s + 31) 5.
Proof. intros s Hs. unfold class_id. replace (s <=? 512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
Lemma size_of_class_small : forall c, c <= 16 -> size_of_class c = 32 * c.
Proof. intros c Hc. unfold size_of_class. replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
Lemma class_small_facts : forall n c, 1 <= n <= 448 -> class_id (needed_size n) = c ->
  1 <= c <= 16 /\ Z.shiftr (needed_size n + 31) 5 = c /\ size_of_class c = 32 * c /\ needed_size n <= size_of_class c <= 512.
Proof.
  intros n c N HC. pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  rewrite class_id_small in HC by lia.
  assert (C : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  pose proof (size_of_class_small c ltac:(lia)) as S.
  split; [exact C|]. split; [exact HC|]. split; [exact S|].
  rewrite S. rewrite <- HC. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.
Lemma max_cached_le16 : forall c, 1 <= c -> max_cached c <= 16.
Proof. intros c Hc. unfold max_cached. lia. Qed.
End CANSEC1.
