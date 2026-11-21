(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (13 recorded proofs replaced by written proofs (Z_to_le_bytes_le_val, le8_of_bytes, le4_of_bytes and 10 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MState Mem Cells Step Arr Bytes InitMem Tac.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ABytes () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib3Lib5Bytes<bytes_ok_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Bytes<le_val_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Bytes6le_valC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions@Z_to_bv_unsignedC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef3mapK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List:length_mapC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyc59OSSVerify5KrLib5BothW6ABytesDZ_to_le_bytes_le_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z9mod_smallC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib3Lib5BytesDbytes_le_to_Z_le_valC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3appc59OSSVerify5KrLib5BothW6ABytes<le8_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List<firstn_skipnC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List<length_skipnC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List=length_firstnC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List;skipn_skipnK59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC47Corelib4Init3Nat3addC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalc59OSSVerify5KrLib5BothW6ABytes<le4_of_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6ABytes<le2_of_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib5BothW6ABytes>words_of_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6ABytesAwords_of_bytes_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z:shiftr_0_lC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z;shiftr_eq_0C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=shiftr_shiftrc59OSSVerify5KrLib5BothW6ABytes?le8_small_splitC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib4Init5Logic3iffC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC46Stdlib6ZArith:ZArith_dec8Z_lt_decC59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C47Corelib7Classes?RelationClasses=iff_ReflexiveC46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma Z_to_le_bytes_le_val : forall bs : list byte,
  Z_to_le_bytes (length bs) (le_val (map bv_unsigned bs)) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length map le_val Z_to_le_bytes].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as V.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    replace ((bv_unsigned b + 256 * le_val (map bv_unsigned bs)) mod 256) with (bv_unsigned b); [reflexivity|].
    Z.div_mod_to_equations. nia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace ((bv_unsigned b + 256 * le_val (map bv_unsigned bs)) / 256) with (le_val (map bv_unsigned bs)) by (Z.div_mod_to_equations; nia).
    exact IH.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word.
  rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as V. rewrite length_map, L in V.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). change (256 ^ Z.of_nat 8) with (2^64) in V.
  rewrite Z.mod_small by lia. rewrite <- L at 1. apply Z_to_le_bytes_le_val.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le4, word_to_le_bytes, le_bytes_to_word.
  rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as V. rewrite length_map, L in V.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). change (256 ^ Z.of_nat 4) with (2^32) in V.
  rewrite Z.mod_small by lia. rewrite <- L at 1. apply Z_to_le_bytes_le_val.
Qed.
Lemma le2_of_bytes : forall bs : list byte, length bs = 2%nat -> le2 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le2, word_to_le_bytes, le_bytes_to_word.
  rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as V. rewrite length_map, L in V.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). change (256 ^ Z.of_nat 2) with (2^16) in V.
  rewrite Z.mod_small by lia. rewrite <- L at 1. apply Z_to_le_bytes_le_val.
Qed.

(* [comment removed for export] *)
Lemma c8_of_CB : forall m A bs, rw_cells bsegs m A [CB 8 bs] -> exists w : word, rw_cells bsegs m A [C8 w] /\ le8 w = bs.
Proof.
  intros m A bs H. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  exists (le_bytes_to_word bs). split; [| apply le8_of_bytes; exact L].
  eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by exact L. reflexivity.
Qed.
Lemma c8c8_of_CB : forall m A bs, rw_cells bsegs m A [CB 16 bs] -> exists w1 w2 : word, rw_cells bsegs m A [C8 w1; C8 w2].
Proof.
  intros m A bs H. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  exists (le_bytes_to_word (firstn 8 bs)), (le_bytes_to_word (skipn 8 bs)).
  eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite !le8_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
  rewrite ?app_nil_r. apply firstn_skipn.
Qed.
(* [comment removed for export] *)
Lemma hdr_of_CB : forall m A bs, rw_cells bsegs m A [CB 16 bs] ->
  exists b0 b1 szh szl ctxj : Z,
    rw_cells bsegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b0 < 256 /\ 0 <= b1 < 256.
Proof.
  intros m A bs H. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  destruct bs as [|x0 [|x1 bs2]]; cbn in L; try lia.
  exists (bv_unsigned x0), (bv_unsigned x1), (bv_unsigned (le_bytes_to_word (firstn 2 bs2))),
         (bv_unsigned (le_bytes_to_word (firstn 4 (skipn 2 bs2)))), (bv_unsigned (le_bytes_to_word (skipn 6 bs2))).
  pose proof (bv_unsigned_in_range 8 x0) as R0. pose proof (bv_unsigned_in_range 8 x1) as R1. unfold bv_modulus in R0, R1. cbn in R0, R1.
  split; [| lia].
  rewrite !Z_to_bv_bv_unsigned. rewrite !definitions.Z_to_bv_bv_unsigned.
  eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app].
  rewrite le2_of_bytes by (rewrite length_firstn; lia).
  rewrite le4_of_bytes by (rewrite length_firstn, length_skipn; lia).
  rewrite le8_of_bytes by (rewrite length_skipn; lia).
  cbn [app]. do 2 apply (f_equal (cons _)). rewrite ?app_nil_r.
  transitivity (firstn 2 bs2 ++ (firstn 4 (skipn 2 bs2) ++ skipn 6 bs2)); [rewrite ?app_assoc; reflexivity|].
  replace (skipn 6 bs2) with (skipn 4 (skipn 2 bs2)) by (rewrite skipn_skipn; reflexivity).
  rewrite firstn_skipn. apply firstn_skipn.
Qed.

Fixpoint words_of_bytes (bs : list byte) : list word :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest => le_bytes_to_word [b0;b1;b2;b3;b4;b5;b6;b7] :: words_of_bytes rest
  | _ => []
  end.

Lemma words_of_bytes_ok : forall k bs, length bs = (8 * k)%nat ->
  u64s (words_of_bytes bs) = bs /\ length (words_of_bytes bs) = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - destruct bs; [split; reflexivity| cbn in L; lia].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 rest]]]]]]]]; cbn in L; try lia.
    destruct (IH rest ltac:(lia)) as [U Lk].
    cbn [words_of_bytes u64s length]. rewrite le8_of_bytes by reflexivity. cbn. rewrite U, Lk. split; reflexivity.
Qed.

Lemma u64arr_of_CB : forall m A k bs,
  rw_cells bsegs m A [CB (8 * k) bs] -> u64arr bsegs m A (words_of_bytes bs) /\ length (words_of_bytes bs) = k.
Proof.
  intros m A k bs [[WF BA] WR]. cbn in WF. destruct WF as [L _].
  destruct (words_of_bytes_ok k bs ltac:(lia)) as [U Lk].
  split; [|exact Lk]. split.
  - rewrite U. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. exact BA.
  - rewrite Lk. cbn [cells_size csize Nat.add] in WR. replace (8 * Z.of_nat k) with (Z.of_nat (8 * k + 0)) by lia. exact WR.
Qed.

(* [comment removed for export] *)
Lemma le8_small_split : forall z, 0 <= z < 2^32 -> le8 (Z_to_bv 64 z) = le4 (Z_to_bv 64 z) ++ le4 (Z_to_bv 64 0).
Proof.
  intros z Hz. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia.
  change (8+8) with 16. change (16+8) with 24. change (24+8) with 32. change (32+8) with 40. change (40+8) with 48. change (48+8) with 56.
  assert (E : forall k, 32 <= k -> Z.shiftr z k = 0).
  { intros k Hk. destruct (Z.eq_dec z 0) as [->|]; [apply Z.shiftr_0_l|]. apply Z.shiftr_eq_0; [lia|].
    apply Z.lt_le_trans with 32; [apply Z.log2_lt_pow2; lia| lia]. }
  rewrite (E 32), (E 40), (E 48), (E 56) by lia. rewrite !Z.shiftr_0_l. reflexivity.
Qed.

Lemma rw_cells_C8_to_C4C4_zero : forall m A,
  rw_cells bsegs m A [C8 (Z_to_bv 64 0)] -> rw_cells bsegs m A [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof.
  intros m A H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite (le8_small_split 0) by lia. rewrite app_nil_r. reflexivity.
Qed.

Lemma rw_cells_C4C4_to_C8 : forall m A z,
  0 <= z < 2^32 ->
  rw_cells bsegs m A [C4 (Z_to_bv 64 z); C4 (Z_to_bv 64 0)] -> rw_cells bsegs m A [C8 (Z_to_bv 64 z)].
Proof.
  intros m A z Hz H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite (le8_small_split z) by lia. rewrite app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac take_cells k cs :=
  lazymatch k with
  | O => constr:(@nil cell)
  | S ?k' => lazymatch cs with ?c :: ?rest => let p := take_cells k' rest in constr:(c :: p) end
  end.
Ltac drop_cells k cs :=
  lazymatch k with
  | O => cs
  | S ?k' => lazymatch cs with _ :: ?rest => drop_cells k' rest end
  end.
Ltac rw_split H k H1 H2 :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let cs1 := take_cells k cs in let cs2 := drop_cells k cs in
    let sz := eval cbv in (Z.of_nat (cells_size cs1)) in
    change cs with (cs1 ++ cs2) in H; apply rw_cells_app in H; destruct H as [H1 H2];
    change (Z.of_nat (cells_size cs1)) with sz in H2;
    repeat match type of H2 with rw_cells _ _ (?X + ?a + ?b)%Z _ =>
      lazymatch a with Z0 => fail | Zpos _ => idtac | Zneg _ => idtac end;
      lazymatch b with Z0 => fail | Zpos _ => idtac | Zneg _ => idtac end;
      let c := eval vm_compute in (a + b)%Z in
      replace (X + a + b)%Z with (X + c)%Z in H2 by lia end
  end.
(* [comment removed for export] *)
Ltac rw_join H1 H2 H :=
  lazymatch type of H1 with rw_cells ?segs ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    let sz := eval cbv in (Z.of_nat (cells_size cs1)) in
    replace A2 with (A + sz)%Z in H2 by lia;
    pose proof (proj2 (rw_cells_app segs m A cs1 cs2) (conj H1 H2)) as H; clear H1 H2;
    cbn [app] in H
  end end.
(* [comment removed for export] *)
Ltac cb_split3 H a b c :=
  lazymatch type of H with rw_cells ?segs ?m ?A [CB ?n ?junk] =>
    apply (rw_cells_split_CB segs m A [] n junk [] [a; b; c]%nat) in H; [| cbn; lia];
    cbn [app mk_CB_cells] in H
  end.
