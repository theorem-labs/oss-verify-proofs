(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (22 recorded proofs replaced by written proofs (le4_two_bytes, rw_C1x4_to_C4, rw_C4_to_C1x4 and 19 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AKitQ () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divK47Corelib7Numbers7BinNums8positive01K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib3Mem<Z_to_bv8_modC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpK46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z=shiftr_shiftrC45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing3Pol03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes:comparison00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes6option00K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appc59OSSVerify5KrLib5BothW5AKitQ=le4_two_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes3nat00K59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C56Stdlib6ZArith4Znat5Z2Nat2idK47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib3Lib5Frame?stk_of_rw_cellsC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC59OSSVerify5KrLib3Lib5Frame9stk_mergeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib6Common6StrFunAnth_error_repeat'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List=repeat_lengthC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr8u64s_appC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib5Lists4List:length_appK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c59OSSVerify5KrLib5BothW5AKitQ9stk_of_cbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW5AKitQ6stk_cbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW5AKitQ:u64arr_nilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rc59OSSVerify5KrLib5BothW5AKitQ;u64arr_snocC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4xorbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z=div_pow2_bitsC56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z9lxor_specC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib5BothW5AKitQ=byte0_cas_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW5AKitQ9afree_unwC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00I59OSSVerify5KrLib5BothW5ABase6uchain00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8AFREE_PCC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<uchain_frameC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA9rng_fp_leC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma le4_two_bytes : forall b0 b1 : Z, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  le4 (Z_to_bv 64 (b0 + 256 * b1)) = [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros b0 b1 H0 H1. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_shiftr by lia. change (8+8) with 16. change (16+8) with 24. rewrite !Z.shiftr_div_pow2 by lia.
  change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
  f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
  f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
  f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
  f_equal. apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia.
Qed.

Lemma rw_C1x4_to_C4 : forall m A (b0 b1 : Z), 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells bsegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m A [C4 (Z_to_bv 64 (b0 + 256 * b1))].
Proof.
  intros m A b0 b1 H0 H1 H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
Lemma rw_C4_to_C1x4 : forall m A (b0 b1 : Z), 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells bsegs m A [C4 (Z_to_bv 64 (b0 + 256 * b1))] ->
  rw_cells bsegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  intros m A b0 b1 H0 H1 H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rw_hdr_to_C4 : forall m A (b0 b1 : Z) cs, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells bsegs m A (C1 (Z_to_bv 8 b0) :: C1 (Z_to_bv 8 b1) :: C2 (Z_to_bv 64 0) :: cs) ->
  rw_cells bsegs m A (C4 (Z_to_bv 64 (b0 + 256 * b1)) :: cs).
Proof.
  intros m A b0 b1 cs H0 H1 H. pose proof H as [[Hwf _] _]. cbn in Hwf.
  eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
Lemma rw_C4_to_hdr : forall m A (b0 b1 : Z) cs, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells bsegs m A (C4 (Z_to_bv 64 (b0 + 256 * b1)) :: cs) ->
  rw_cells bsegs m A (C1 (Z_to_bv 8 b0) :: C1 (Z_to_bv 8 b1) :: C2 (Z_to_bv 64 0) :: cs).
Proof.
  intros m A b0 b1 cs H0 H1 H. pose proof H as [[Hwf _] _]. cbn in Hwf.
  eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stk_cb : forall m lo hi, stk bsegs m lo hi -> lo <= hi ->
  exists bs, rw_cells bsegs m lo [CB (Z.to_nat (hi - lo)) bs].
Proof.
  intros m lo hi ST Hle. destruct (stk_carve bsegs m lo hi (Z.to_nat (hi - lo)) ST ltac:(lia)) as [_ [bs H]].
  exists bs. rewrite Z2Nat.id in H by lia. replace (hi - (hi - lo)) with lo in H by lia. exact H.
Qed.
Lemma stk_of_cb : forall m lo n bs, rw_cells bsegs m lo [CB (Z.to_nat n) bs] -> 0 <= n -> stk bsegs m lo (lo + n).
Proof.
  intros m lo n bs H Hn. pose proof (stk_of_rw_cells bsegs m lo _ H) as S. cbn [cells_size csize] in S.
  rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S.
Qed.
(* [comment removed for export] *)
Lemma stk_merge3 : forall m a b c d, stk bsegs m a b -> stk bsegs m b c -> stk bsegs m c d -> a <= b <= c -> c <= d -> stk bsegs m a d.
Proof. intros. eapply stk_merge; [| eapply stk_merge; [| | ]|]; eauto; lia. Qed.

(* [comment removed for export] *)
Lemma stk_any_write : forall m lo hi a bs, stk bsegs m lo hi -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  stk bsegs (write_to_mem m (wa a) bs) lo hi.
Proof. intros. apply stk_write; assumption. Qed.

(* [comment removed for export] *)
Lemma cb_zero_le8 : forall m A n j,
  rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
  0 <= j -> 8 * j + 8 <= n ->
  bytes_at bsegs m (A + 8 * j) (le8 (Z_to_bv 64 0)).
Proof.
  intros m A n j [[_ HB] _] Hj Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  destruct HB as (H0 & H1 & HB). rewrite repeat_length in H1, HB.
  split; [lia|]. split; [rewrite length_le8; lia|].
  intros i Hi. rewrite length_le8 in Hi.
  replace (A + 8 * j + Z.of_nat i) with (A + Z.of_nat (Z.to_nat (8 * j) + i)) by lia.
  rewrite HB by lia. rewrite nth_error_repeat' by lia.
  replace (le8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8) by reflexivity.
  rewrite nth_error_repeat' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u64arr_snoc : forall m A ws (w : word),
  u64arr bsegs m A ws -> rw_cells bsegs m (A + 8 * Z.of_nat (length ws)) [C8 w] ->
  u64arr bsegs m A (ws ++ [w]).
Proof.
  intros m A ws w [HB HW] [[_ HB2] HW2]. cbn [cells_bytes cbytes app cells_size csize Nat.add] in HB2, HW2.
  rewrite app_nil_r in HB2. split.
  - rewrite u64s_app. cbn [u64s app]. rewrite app_nil_r. apply bytes_at_app. split; [exact HB|].
    rewrite u64s_length. replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia. exact HB2.
  - rewrite length_app. cbn [length]. destruct HW as (H0 & H1 & HW). destruct HW2 as (_ & H3 & HW2).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (8 * Z.of_nat (length ws))); [apply HW; lia|].
    replace (A + i) with (A + 8 * Z.of_nat (length ws) + (i - 8 * Z.of_nat (length ws))) by lia. apply HW2. lia.
Qed.

(* [comment removed for export] *)
Lemma junk_stk : forall m A len, (exists bs, rw_cells bsegs m A [CB (Z.to_nat len) bs]) -> 0 <= len -> stk bsegs m A (A + len).
Proof. intros m A len [bs H] Hl. eapply stk_of_cb; eauto. Qed.
Lemma stk_junk : forall m A hi, stk bsegs m A hi -> A <= hi -> exists bs, rw_cells bsegs m A [CB (Z.to_nat (hi - A)) bs].
Proof. intros. apply stk_cb; assumption. Qed.

Lemma u64arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u64arr bsegs m A [].
Proof.
  intros m A H0 H1. split.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.
Lemma u64arr_one : forall m A (w : word), rw_cells bsegs m A [C8 w] -> u64arr bsegs m A [w].
Proof.
  intros m A w H. pose proof (rw_cells_bound bsegs m A _ H) as B. cbn [cells_size csize Nat.add] in B.
  change [w] with ([] ++ [w]). apply u64arr_snoc; [apply u64arr_nil; lia|]. cbn [length Z.of_nat Z.mul]. rewrite Z.add_0_r. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma byte0_of_word : forall s0 hi, 0 <= s0 < 256 -> 0 <= hi -> Z.land (s0 + 256 * hi) 255 = s0.
Proof.
  intros s0 hi H0 Hh. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256.
  Z.div_mod_to_equations. lia.
Qed.
Lemma byte0_cas_val : forall x s1, 0 <= x -> 0 <= s1 < 256 ->
  Z.lxor x (Z.land (Z.lxor x s1) 255) = x - x mod 256 + s1.
Proof.
  intros x s1 Hx Hs. set (r := x - x mod 256 + s1).
  assert (Hr : 0 <= r) by (subst r; Z.div_mod_to_equations; lia).
  assert (Rlo : r mod 2^8 = s1) by (subst r; change (2^8) with 256; Z.div_mod_to_equations; lia).
  assert (Rhi : r / 2^8 = x / 2^8) by (subst r; change (2^8) with 256; Z.div_mod_to_equations; lia).
  apply Z.bits_inj'. intros k Hk.
  rewrite Z.lxor_spec, Z.land_spec, Z.lxor_spec. change 255 with (Z.ones 8).
  destruct (Z_lt_le_dec k 8) as [Hlt|Hge].
  - rewrite Z.ones_spec_low by lia. rewrite <- (Z.mod_pow2_bits_low r 8 k) by lia. rewrite Rlo.
    destruct (Z.testbit x k), (Z.testbit s1 k); reflexivity.
  - rewrite Z.ones_spec_high by lia.
    replace k with ((k - 8) + 8) at 4 by lia. rewrite <- (Z.div_pow2_bits r 8 (k - 8)) by lia. rewrite Rhi.
    rewrite Z.div_pow2_bits by lia. replace (k - 8 + 8) with k by lia.
    destruct (Z.testbit x k), (Z.testbit s1 k); reflexivity.
Qed.
(* [comment removed for export] *)
Lemma byte0_cas : forall s0 s1 hi, 0 <= s0 < 256 -> 0 <= s1 < 256 -> 0 <= hi ->
  Z.lxor (s0 + 256 * hi) (Z.land (Z.lxor (s0 + 256 * hi) s1) 255) = s1 + 256 * hi.
Proof. intros. rewrite byte0_cas_val by lia. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition afree_unw (RNG : footprint) (lo : Z) (m : amem) (top : Z) (sp s0 ra : word) (trt : list Z) : Prop :=
  (exists tr, trt = bv_unsigned ra :: tr /\ uchain m top AFREE_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr
              /\ (length tr <= 28)%nat /\ bv_unsigned sp + 16 < top /\ rng RNG lo (top - lo))
  \/ (trt = [] /\ top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47).

Lemma afree_unw_length : forall RNG lo m top sp s0 ra trt, afree_unw RNG lo m top sp s0 ra trt -> (length trt <= 29)%nat.
Proof. intros RNG lo m top sp s0 ra trt [(tr & -> & _ & L & _)|(-> & _)]; cbn; lia. Qed.

Lemma afree_unw_sp47 : forall RNG lo m top sp s0 ra trt, afree_unw RNG lo m top sp s0 ra trt -> top <= 2^47 -> bv_unsigned sp < 2^47.
Proof. intros RNG lo m top sp s0 ra trt [(tr & _ & _ & _ & B & _)|(_ & _ & B)] T; lia. Qed.

Lemma afree_unw_frame : forall RNG lo m m' top sp s0 ra trt,
  afree_unw RNG lo m top sp s0 ra trt -> (forall a, bv_unsigned s0 - 16 <= a < top -> m' (wa a) = m (wa a)) -> afree_unw RNG lo m' top sp s0 ra trt.
Proof.
  intros RNG lo m m' top sp s0 ra trt [(tr & E & UC & L & T & R)|H] AG; [left| right; exact H].
  exists tr. split; [exact E|]. split; [| split; [exact L| split; [exact T| exact R]]].
  eapply uchain_frame; [exact UC| exact AG].
Qed.

Lemma afree_unw_rng_mono : forall RNG RNG' lo m top sp s0 ra trt,
  afree_unw RNG lo m top sp s0 ra trt -> fp_le RNG RNG' -> afree_unw RNG' lo m top sp s0 ra trt.
Proof.
  intros RNG RNG' lo m top sp s0 ra trt [(tr & E & UC & L & T & R)|H] LE; [left| right; exact H].
  exists tr. repeat (split; [assumption|]). eapply ITreeA.rng_fp_le; [exact LE| exact R].
Qed.
End CANSEC1.
