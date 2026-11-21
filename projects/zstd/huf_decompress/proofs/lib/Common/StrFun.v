(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (75 recorded proofs replaced by written proofs (find_byte_Some, find_byte_None, find_byte_app_l and 72 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MState Mem Cells Step Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_StrFun () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List9nth_errorC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List:map_repeatK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C47Corelib4Init5Peano2ltK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00c59OSSVerify5KrLib6Common6StrFun9find_byteC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic7f_equalC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic3notC47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnc59OSSVerify5KrLib6Common6StrFun?find_byte_app_lC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<firstn_skipnc59OSSVerify5KrLib6Common6StrFun>find_byte_SomeC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat=lt_trichotomyI47Corelib4Init5Logic2or00c59OSSVerify5KrLib6Common6StrFun>find_byte_NoneC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List<nth_error_Inc59OSSVerify5KrLib6Common6StrFunDfind_byte_None_introC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic5proj2c59OSSVerify5KrLib6Common6StrFun?find_byte_notinC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun?find_byte_app_rC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op201C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib6Common6StrFun=find_byte_hitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib5Lists4List;firstn_all2C46Stdlib5Lists4List:firstn_appC56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib6Common6StrFun<str_bytes_nzC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C46Stdlib5Lists4List9in_or_appC46Stdlib5Lists4List9app_nil_rC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC47Corelib4Init5Logic8iff_reflC46Stdlib5Lists4List:length_appK47Corelib4Init5Logic2or02c59OSSVerify5KrLib6Common6StrFun>find_byte_cstrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFunDfind_byte_cstr_shortC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun9memchr_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib6Common6StrFun:memchr_resC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specc59OSSVerify5KrLib6Common6StrFun;strnlen_resC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<length_skipnC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC46Stdlib5Lists4List>nth_error_app2C46Stdlib5Lists4List;skipn_skipnC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minc59OSSVerify5KrLib6Common6StrFun<memcmp_modelC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC47Corelib7Classes?RelationClasses>iff_TransitiveC59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib3Mem9upd_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemEbytes_at_write_insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wr_at_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@upd_bytes_lengthC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib3Lib3Mem>wr_at_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun6filledC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List=repeat_lengthC56Stdlib5Arith8PeanoNat3Nat3lebC56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init9Datatypes4andbC56Stdlib5Arith8PeanoNat3Nat9leb_spec0C56Stdlib5Arith8PeanoNat3Nat9ltb_spec0c59OSSVerify5KrLib6Common6StrFunAnth_error_repeat'C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC59OSSVerify5KrLib3Lib3Mem=upd_bytes_nthC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphc59OSSVerify5KrLib6Common6StrFun:filled_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesC46Stdlib5Lists4List>nth_error_NoneC46Stdlib5Lists4List=nth_error_extC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z9lt_pred_lC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z9div_add_lC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z<ldiff_ones_rC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z4lnotK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z:ldiff_landC56Stdlib6ZArith6BinInt1Z:land_assocc59OSSVerify5KrLib6Common6StrFun4zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:in_map_iffC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List6in_seqC46Stdlib5Lists4List8map_consc59OSSVerify5KrLib6Common6StrFun<forallb_zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;list_eq_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib6Common6StrFun:list_Z_eqbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decc59OSSVerify5KrLib6Common6StrFun=list_Z_eqb_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions=bv_wrap_smallC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib6Common6StrFun@map_unsigned_injC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun8bcast_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun3BC4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun3BC8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun<Z_to_bv8_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun6copiedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_allC56Stdlib5Arith8PeanoNat3Nat8sub_diagC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryc59OSSVerify5KrLib6Common6StrFun>firstn_app_lenC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib6Common6StrFunDapp_firstn_mid_skipnC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transc59OSSVerify5KrLib6Common6StrFun:copied_updC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6ltb_ltC46Stdlib5Lists4List?nth_error_skipnC46Stdlib5Lists4List@nth_error_firstnC46Stdlib5Lists4List=firstn_firstnC46Stdlib5Lists4ListAskipn_firstn_commC59OSSVerify5KrLib3Lib3Arr?nth_error_splitC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appC59OSSVerify5KrLib3Lib5Bytes6le_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun:byte_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib3Lib5BytesDbytes_le_to_Z_le_valC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC45stdpp9bitvector;definitions9bv_signedK46Stdlib9micromega:ZMicromega;ZArithProof04c59OSSVerify5KrLib6Common6StrFun=bv_swrap32_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFunAle_bytes_to_word4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemAsigned_of_extractC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib3Mem:sext_smallC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes:comparison02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib3Lib5Bytes<bytes_ok_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Bytes<le_val_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib3Lib5Bytes?lor_shiftl8_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFunBZ_to_le_bytes_to_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemAZ_to_le_bytes_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun;le1_of_mod8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun<lw_unsigned4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun<le4_of_mod32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8land_0_lC56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith8Zbitwise1Z<add_lor_landc59OSSVerify5KrLib6Common6StrFun7lor_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_commC56Stdlib6ZArith6BinInt1Z=pow_lt_mono_rC59OSSVerify5KrLib3Lib7ZBridgeBzb_land_pow2_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8mod_sameC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z9land_diagC56Stdlib6ZArith6BinInt1Z@land_lor_distr_rC59OSSVerify5KrLib3Lib5Bytes?land_mod_pow2_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun?land_single_bitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge<zb_land_maskC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6StrFun<firstn_S_nthC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib5Arith8PeanoNat3Nat6leb_leC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib5Arith8PeanoNat3Nat6ltb_ge".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint find_byte (c : Z) (l : list byte) : option nat :=
  match l with
  | [] => None
  | b :: l' => if bv_unsigned b =? c then Some 0%nat
               else match find_byte c l' with Some i => Some (S i) | None => None end
  end.

Lemma find_byte_Some : forall c l i, find_byte c l = Some i ->
  (i < length l)%nat /\ (exists b, nth_error l i = Some b /\ bv_unsigned b = c) /\
  (forall j b, (j < i)%nat -> nth_error l j = Some b -> bv_unsigned b <> c).
Proof.
  intros c l; induction l as [|b l IH]; intros i H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec (bv_unsigned b) c) as [E|NE].
  - injection H as <-. cbn. split; [lia|]. split. { exists b. auto. } intros; lia.
  - destruct (find_byte c l) as [i'|] eqn:F; [|discriminate]. injection H as <-.
    destruct (IH i' eq_refl) as (Hl & (b' & Hn & Hb') & Hmin). cbn. split; [lia|]. split. { exists b'. auto. }
    intros [|j] b2 Hj Hn2; cbn in Hn2. { injection Hn2 as <-. exact NE. } eapply Hmin; [|exact Hn2]. lia.
Qed.

Lemma find_byte_None : forall c l, find_byte c l = None -> forall j b, nth_error l j = Some b -> bv_unsigned b <> c.
Proof.
  intros c l; induction l as [|b l IH]; intros H j b2 Hn; [destruct j; discriminate|].
  cbn in H. destruct (Z.eqb_spec (bv_unsigned b) c) as [E|NE]; [discriminate|].
  destruct (find_byte c l) eqn:F; [discriminate|].
  destruct j as [|j]; cbn in Hn. { injection Hn as <-. exact NE. } eapply IH; eauto.
Qed.

Lemma find_byte_app_l : forall c l1 l2 i, find_byte c l1 = Some i -> find_byte c (l1 ++ l2) = Some i.
Proof.
  intros c l1; induction l1 as [|b l1 IH]; intros l2 i H; cbn in *; [discriminate|].
  destruct (bv_unsigned b =? c); [exact H|]. destruct (find_byte c l1) eqn:F; [|discriminate].
  rewrite (IH l2 n eq_refl). exact H.
Qed.

Lemma find_byte_app_r : forall c l1 l2, find_byte c l1 = None ->
  find_byte c (l1 ++ l2) = match find_byte c l2 with Some i => Some (length l1 + i)%nat | None => None end.
Proof.
  intros c l1; induction l1 as [|b l1 IH]; intros l2 H; cbn in *. { destruct (find_byte c l2); reflexivity. }
  destruct (bv_unsigned b =? c); [discriminate|]. destruct (find_byte c l1) eqn:F; [discriminate|].
  rewrite (IH l2 eq_refl). destruct (find_byte c l2); reflexivity.
Qed.

Lemma find_byte_firstn : forall c l n i, find_byte c (firstn n l) = Some i -> find_byte c l = Some i.
Proof.
  intros c l n i H. rewrite <- (firstn_skipn n l). apply find_byte_app_l. exact H.
Qed.

Lemma find_byte_charact : forall c l i b,
  nth_error l i = Some b -> bv_unsigned b = c ->
  (forall j b', (j < i)%nat -> nth_error l j = Some b' -> bv_unsigned b' <> c) ->
  find_byte c l = Some i.
Proof.
  intros c l i b Hn Hb Hmin. destruct (find_byte c l) as [i'|] eqn:F.
  - destruct (find_byte_Some _ _ _ F) as (Hl & (b' & Hn' & Hb') & Hmin').
    destruct (Nat.lt_trichotomy i i') as [Hlt|[->|Hgt]].
    + exfalso. exact (Hmin' _ _ Hlt Hn Hb).
    + reflexivity.
    + exfalso. exact (Hmin _ _ Hgt Hn' Hb').
  - exfalso. exact (find_byte_None _ _ F _ _ Hn Hb).
Qed.

Lemma find_byte_None_intro : forall c l,
  (forall j b, nth_error l j = Some b -> bv_unsigned b <> c) -> find_byte c l = None.
Proof.
  intros c l H. destruct (find_byte c l) as [i|] eqn:F; [|reflexivity].
  destruct (find_byte_Some _ _ _ F) as (_ & (b & Hn & Hb) & _). exfalso. exact (H _ _ Hn Hb).
Qed.

Lemma find_byte_notin : forall c l, (forall b, In b l -> bv_unsigned b <> c) -> find_byte c l = None.
Proof.
  intros c l H. apply find_byte_None_intro. intros j b Hn. apply H. eapply nth_error_In; eauto.
Qed.

Lemma find_byte_hit : forall c l b rest,
  (forall b', In b' l -> bv_unsigned b' <> c) -> bv_unsigned b = c ->
  find_byte c (l ++ b :: rest) = Some (length l).
Proof.
  intros c l b rest Hl Hb. rewrite find_byte_app_r by (apply find_byte_notin; exact Hl).
  cbn. rewrite (proj2 (Z.eqb_eq _ _) Hb). f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition memchr_res (A : Z) (c : Z) (n : Z) (buf : list byte) : Z :=
  match find_byte c (firstn (Z.to_nat n) buf) with Some i => A + Z.of_nat i | None => 0 end.

(* [comment removed for export] *)
Definition memchr_ok (A c n : Z) (buf : list byte) : Prop :=
  match find_byte c (firstn (Z.to_nat n) buf) with
  | Some j => (n <= Z.of_nat (length buf) \/
               Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= Z.of_nat (length buf))%Z
  | None => (n <= Z.of_nat (length buf))%Z
  end.

(* [comment removed for export] *)
Definition strnlen_res (n : Z) (buf : list byte) : Z :=
  match find_byte 0 (firstn (Z.to_nat n) buf) with Some i => Z.of_nat i | None => n end.

(* [comment removed for export] *)
Section NulTerminated.
  Variables (A n : Z) (str slack : list byte).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.

  Lemma str_bytes_nz : forall b, In b str -> bv_unsigned b <> 0.
  Proof. intros b Hb E. apply NONUL. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. Qed.

  Lemma find_byte_cstr : (Z.of_nat (length str) < n)%Z ->
    find_byte 0 (firstn (Z.to_nat n) (str ++ Z_to_bv 8 0 :: slack)) = Some (length str).
  Proof.
    intros Hn. rewrite firstn_app. rewrite firstn_all2 by lia.
    destruct (Z.to_nat n - length str)%nat as [|k] eqn:E; [lia|]. cbn [firstn].
    apply find_byte_hit; [apply str_bytes_nz| reflexivity].
  Qed.

  Lemma find_byte_cstr_short : (n <= Z.of_nat (length str))%Z ->
    find_byte 0 (firstn (Z.to_nat n) (str ++ Z_to_bv 8 0 :: slack)) = None.
  Proof.
    intros Hn. rewrite firstn_app. replace (Z.to_nat n - length str)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
    apply find_byte_notin. intros b Hb. apply str_bytes_nz. rewrite <- (firstn_skipn (Z.to_nat n) str). apply in_or_app. left. exact Hb.
  Qed.

  Lemma memchr_ok_cstr : memchr_ok A 0 n (str ++ Z_to_bv 8 0 :: slack).
  Proof.
    unfold memchr_ok. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n) as [Hn|Hn].
    - rewrite find_byte_cstr by lia. right. rewrite length_app. cbn [length]. lia.
    - rewrite find_byte_cstr_short by lia. rewrite length_app. cbn [length]. lia.
  Qed.

  Lemma memchr_res_cstr :
    memchr_res A 0 n (str ++ Z_to_bv 8 0 :: slack) = (if Z.of_nat (length str) <? n then A + Z.of_nat (length str) else 0)%Z.
  Proof.
    unfold memchr_res. destruct (Z.ltb_spec0 (Z.of_nat (length str)) n).
    - rewrite find_byte_cstr by lia. reflexivity.
    - rewrite find_byte_cstr_short by lia. reflexivity.
  Qed.

  Lemma strnlen_res_cstr :
    strnlen_res n (str ++ Z_to_bv 8 0 :: slack) = Z.min (Z.of_nat (length str)) n.
  Proof.
    unfold strnlen_res. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n).
    - rewrite find_byte_cstr by lia. lia.
    - rewrite find_byte_cstr_short by lia. lia.
  Qed.
End NulTerminated.

(* [comment removed for export] *)
Fixpoint strncmp_walk (l r : list byte) (k : nat) {struct l} : option Z :=
  match l, r with
  | a :: l', b :: r' =>
      if ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0 || negb (bv_unsigned a =? bv_unsigned b))%bool
      then Some (bv_unsigned a - bv_unsigned b)
      else match k with O => Some (bv_unsigned a - bv_unsigned b) | S k' => strncmp_walk l' r' k' end
  | _, _ => None
  end.
Definition strncmp_model (l r : list byte) (n : Z) : option Z :=
  if n =? 0 then Some 0 else strncmp_walk l r (Z.to_nat (n - 1)).

Lemma skipn_cons_nth : forall {X} (l : list X) i a l', skipn i l = a :: l' -> nth_error l i = Some a /\ l' = skipn (S i) l.
Proof.
  intros X l i a l' H. split.
  - rewrite <- (firstn_skipn i l), H. rewrite nth_error_app2 by (rewrite firstn_length; pose proof (skipn_length i l) as L; rewrite H in L; cbn in L; lia).
    rewrite firstn_length. replace (i - _)%nat with 0%nat by (pose proof (skipn_length i l) as L; rewrite H in L; cbn in L; lia). reflexivity.
  - replace (S i) with (1 + i)%nat by lia. rewrite <- skipn_skipn, H. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint memcmp_model (l r : list byte) (n : nat) {struct n} : option Z :=
  match n with
  | O => Some 0
  | S n' =>
      match l, r with
      | a :: l', b :: r' => if bv_unsigned a =? bv_unsigned b then memcmp_model l' r' n' else Some (bv_unsigned a - bv_unsigned b)
      | _, _ => None
      end
  end.

Lemma memcmp_model_total : forall l r n, (n <= length l)%nat -> (n <= length r)%nat -> exists v, memcmp_model l r n = Some v.
Proof.
  intros l r n; revert l r; induction n as [|n IH]; intros [|a l] [|b r] Hl Hr; cbn in *; try lia; try (eexists; reflexivity).
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH; lia| eexists; reflexivity].
Qed.

Lemma memcmp_model_zero : forall l r n, (n <= length l)%nat -> (n <= length r)%nat ->
  memcmp_model l r n = Some 0 <-> firstn n l = firstn n r.
Proof.
  intros l r n; revert l r; induction n as [|n IH]; intros [|a l] [|b r] Hl Hr; cbn in *; try lia; try (split; reflexivity).
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + rewrite IH by lia. assert (Hab : a = b) by (apply bv_eq; exact E). rewrite Hab. split; [intros ->; reflexivity| intros H; injection H; auto].
    + split. { intros H. exfalso. apply NE. injection H. pose proof (bv_unsigned_in_range 8 a). pose proof (bv_unsigned_in_range 8 b). lia. }
      intros H. injection H as Hab _. subst. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list MemImageType.Segment.

Lemma u8arr_write_bytes : forall m A bs (i : Z) xs,
  u8arr segs m A bs -> (0 <= i)%Z -> (Z.to_nat i + length xs <= length bs)%nat ->
  u8arr segs (write_to_mem m (wa (A + i)) xs) A (upd_bytes bs (Z.to_nat i) xs).
Proof.
  intros m A bs i xs [Hb Hw] Hi Hl. split.
  - apply bytes_at_write_inside; assumption.
  - rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
Qed.

Lemma u8arr_store_ok_n : forall m A bs (i : Z) n a,
  u8arr segs m A bs -> (0 <= i)%Z -> (i + Z.of_nat n <= Z.of_nat (length bs))%Z -> a = wa (A + i) ->
  store_ok segs m a n = true.
Proof. intros m A bs i n a [_ Hw] Hi Hn ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma rw_cells_CB_length : forall m A n bs, rw_cells segs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[H _] _]. cbn in H. tauto. Qed.
End WithSegs.

(* [comment removed for export] *)
Definition filled (c : byte) (bs : list byte) (Q : Z -> Prop) : Prop :=
  forall j, (0 <= j < Z.of_nat (length bs))%Z -> Q j -> nth_error bs (Z.to_nat j) = Some c.

Lemma filled_init : forall c bs, filled c bs (fun _ => False).
Proof. intros c bs j _ []. Qed.

Lemma filled_mono : forall c bs (Q Q' : Z -> Prop), filled c bs Q -> (forall j, Q' j -> Q j) -> filled c bs Q'.
Proof. intros c bs Q Q' H HQ j Hj Hq. apply H; auto. Qed.

Lemma nth_error_repeat' : forall {X} (x : X) k i, (i < k)%nat -> nth_error (repeat x k) i = Some x.
Proof. intros X x k; induction k as [|k IH]; intros [|i] H; cbn; try lia; auto. apply IH. lia. Qed.

Lemma filled_upd : forall c bs Q i k,
  filled c bs Q -> (i + k <= length bs)%nat ->
  filled c (upd_bytes bs i (repeat c k)) (fun j => Q j \/ (Z.of_nat i <= j < Z.of_nat i + Z.of_nat k)%Z).
Proof.
  intros c bs Q i k HF Hk j Hj HQ. rewrite upd_bytes_length in Hj by (rewrite repeat_length; lia).
  rewrite upd_bytes_nth by (rewrite ?repeat_length; lia). rewrite repeat_length.
  destruct (Nat.leb_spec0 i (Z.to_nat j)); destruct (Nat.ltb_spec0 (Z.to_nat j) (i + k)); cbn [andb];
    first [ apply nth_error_repeat'; lia | destruct HQ as [HQ|HQ]; [apply HF; [lia| exact HQ] | exfalso; lia] ].
Qed.

Lemma filled_updZ : forall c bs Q (i : Z) k,
  filled c bs Q -> (0 <= i)%Z -> (Z.to_nat i + k <= length bs)%nat ->
  filled c (upd_bytes bs (Z.to_nat i) (repeat c k)) (fun j => Q j \/ (i <= j < i + Z.of_nat k)%Z).
Proof.
  intros c bs Q i k HF Hi Hk j Hj HQ. apply (filled_upd c bs Q (Z.to_nat i) k HF Hk j Hj). destruct HQ; [left; assumption| right; lia].
Qed.

Lemma filled_all : forall c bs Q, filled c bs Q -> (forall j, (0 <= j < Z.of_nat (length bs))%Z -> Q j) -> bs = repeat c (length bs).
Proof.
  intros c bs Q HF HQ. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite nth_error_repeat' by lia. replace i with (Z.to_nat (Z.of_nat i)) by lia. apply HF; [lia|]. apply HQ. lia.
  - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). reflexivity.
Qed.

Lemma Z_to_bv8_mod : forall z, Z_to_bv 8 z = Z_to_bv 8 (z mod 256).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 256)%Z. rewrite Z.mod_mod by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_align_down : forall x j, 0 <= x < 2^64 -> 0 <= j <= 64 ->
  Z.land x (2^64 - 2^j) = x - x mod 2^j.
Proof.
  intros x j Hx Hj.
  replace (2^64 - 2^j)%Z with (Z.ldiff (Z.ones 64) (Z.ones j)).
  2:{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
      unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
      replace (2^64)%Z with (2^j * 2^(64-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      replace (Z.pred (1 * (2 ^ j * 2 ^ (64 - j))))%Z with ((2^(64-j) - 1) * 2^j + (2^j - 1))%Z by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by (split; [lia| apply Z.lt_pred_l || lia]). lia. }
  rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod x (2^j)%Z ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma forallb_zseq : forall n f, forallb f (zseq n) = true -> forall c, 0 <= c < Z.of_nat n -> f c = true.
Proof.
  intros n f H c Hc. rewrite forallb_forall in H. apply H. unfold zseq. apply in_map_iff.
  exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma brute256_ok : forall (P : Z -> bool), forallb P (zseq 256) = true -> forall c, 0 <= c < 256 -> P c = true.
Proof. intros P H c Hc. exact (forallb_zseq 256 P H c Hc). Qed.

Lemma word_eq_of_eqb : forall x y : Z, (x mod 2^64 =? y mod 2^64) = true -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply Z.eqb_eq in H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

Lemma map_unsigned_inj : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hx Hl. f_equal; [apply bv_eq; exact Hx| apply IH; exact Hl].
Qed.

Definition list_Z_eqb (l1 l2 : list Z) : bool := if list_eq_dec Z.eq_dec l1 l2 then true else false.
Lemma list_Z_eqb_eq : forall l1 l2, list_Z_eqb l1 l2 = true -> l1 = l2.
Proof. intros l1 l2. unfold list_Z_eqb. destruct (list_eq_dec Z.eq_dec l1 l2); [auto|discriminate]. Qed.

Lemma bcast_ok : forall (F : Z -> list byte) k,
  forallb (fun c => list_Z_eqb (map bv_unsigned (F c)) (repeat c k)) (zseq 256) = true ->
  forall c, 0 <= c < 256 -> F c = repeat (Z_to_bv 8 c) k.
Proof.
  intros F k H c Hc. apply map_unsigned_inj.
  pose proof (forallb_zseq 256 _ H c Hc) as E. cbn beta in E. apply list_Z_eqb_eq in E. rewrite E.
  rewrite map_repeat. f_equal. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition BC4 := 16843009.
Definition BC8 := 72340172838076673.

Lemma le4_bcast_s : forall c, 0 <= c < 256 -> le4 (Z_to_bv 64 (bv_swrap 32 (c * BC4))) = repeat (Z_to_bv 8 c) 4.
Proof. apply (bcast_ok (fun c => le4 (Z_to_bv 64 (bv_swrap 32 (c * BC4)))) 4). vm_compute. reflexivity. Qed.
Lemma le4_bcast : forall c, 0 <= c < 256 -> le4 (Z_to_bv 64 (c * BC4)) = repeat (Z_to_bv 8 c) 4.
Proof. apply (bcast_ok (fun c => le4 (Z_to_bv 64 (c * BC4))) 4). vm_compute. reflexivity. Qed.
Lemma le8_bcast : forall c, 0 <= c < 256 -> le8 (Z_to_bv 64 (c * BC8)) = repeat (Z_to_bv 8 c) 8.
Proof. apply (bcast_ok (fun c => le8 (Z_to_bv 64 (c * BC8))) 8). vm_compute. reflexivity. Qed.
Lemma le1_byte : forall x : word, le1 x = [Z_to_bv 8 (bv_unsigned x mod 256)].
Proof. intros x. cbn. rewrite <- Z_to_bv8_mod. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition copied (src bs : list byte) (k : nat) : Prop :=
  length bs = length src /\ firstn k bs = firstn k src.

Lemma copied_0 : forall src bs, length bs = length src -> copied src bs 0.
Proof. intros src bs H. split; [exact H| reflexivity]. Qed.

Lemma copied_all : forall src bs k, copied src bs k -> (length src <= k)%nat -> bs = src.
Proof.
  intros src bs k [Hl Hf] Hk. rewrite <- (firstn_all2 (n:=k) bs) by lia. rewrite <- (firstn_all2 (n:=k) src) by lia. exact Hf.
Qed.

Lemma firstn_app_len : forall {X} (a b : list X) k, k = length a -> firstn k (a ++ b) = a.
Proof. intros X a b k ->. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma app_firstn_mid_skipn : forall {X} (l : list X) p k,
  firstn p l ++ firstn k (skipn p l) ++ skipn (p + k) l = l.
Proof.
  intros X l p k. rewrite <- (firstn_skipn p l) at 4. f_equal.
  replace (skipn (p + k) l) with (skipn k (skipn p l)) by (rewrite skipn_skipn; f_equal; lia). apply firstn_skipn.
Qed.

Lemma copied_upd : forall src bs p xs,
  copied src bs p -> firstn (length xs) (skipn p src) = xs -> (p + length xs <= length src)%nat ->
  copied src (upd_bytes bs p xs) (p + length xs).
Proof.
  intros src bs p xs [Hl Hf] Hx Hp. split.
  - rewrite upd_bytes_length by lia. exact Hl.
  - unfold upd_bytes. rewrite app_assoc.
    assert (L1 : length (firstn p bs ++ xs) = (p + length xs)%nat) by (rewrite app_length, firstn_length; lia).
    rewrite (firstn_app_len (firstn p bs ++ xs)) by lia.
    transitivity (firstn (p + length xs) (firstn p src ++ xs ++ skipn (p + length xs) src)).
    + assert (L2 : length (firstn p src ++ xs) = (p + length xs)%nat) by (rewrite app_length, firstn_length; lia).
      rewrite app_assoc, (firstn_app_len (firstn p src ++ xs)) by lia. rewrite Hf. reflexivity.
    + f_equal. etransitivity; [ | apply (app_firstn_mid_skipn src p (length xs))]. rewrite Hx. reflexivity.
Qed.

Lemma copied_updZ : forall src bs (P : Z) xs,
  copied src bs (Z.to_nat P) -> (0 <= P)%Z -> firstn (length xs) (skipn (Z.to_nat P) src) = xs ->
  (Z.to_nat P + length xs <= length src)%nat ->
  copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat (length xs))).
Proof.
  intros src bs P xs HC HP Hx Hl. replace (Z.to_nat (P + Z.of_nat (length xs))) with (Z.to_nat P + length xs)%nat by lia.
  apply copied_upd; assumption.
Qed.

(* [comment removed for export] *)
Lemma window_ex : forall (l : list byte) (i : Z) (k : nat), (Z.to_nat i + k <= length l)%nat ->
  exists xs, firstn k (skipn (Z.to_nat i) l) = xs /\ length xs = k.
Proof. intros l i k H. eexists. split; [reflexivity|]. rewrite firstn_length, skipn_length. lia. Qed.

Lemma window_nth : forall (l xs : list byte) (base : Z) (k c : nat) (i : Z),
  firstn k (skipn (Z.to_nat base) l) = xs -> (0 <= base)%Z -> (c < k)%nat -> i = base + Z.of_nat c ->
  nth_error l (Z.to_nat i) = nth_error xs c.
Proof.
  intros l xs base k c i H Hb Hc ->. rewrite <- H. rewrite nth_error_firstn.
  replace (Nat.ltb c k) with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_error_skipn. f_equal. lia.
Qed.

Lemma window_sub : forall (l xs : list byte) (base : Z) (k c j : nat) (i : Z),
  firstn k (skipn (Z.to_nat base) l) = xs -> (0 <= base)%Z -> (c + j <= k)%nat -> i = base + Z.of_nat c ->
  firstn j (skipn (Z.to_nat i) l) = firstn j (skipn c xs).
Proof.
  intros l xs base k c j i H Hb Hc ->. rewrite <- H.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn by lia. f_equal; [lia|]. f_equal. lia.
Qed.

Lemma window_shift : forall (l xs : list byte) (base : Z) (k c : nat) (i : Z),
  firstn k (skipn (Z.to_nat base) l) = xs -> (0 <= base)%Z -> (c <= k)%nat -> i = base + Z.of_nat c ->
  firstn (k - c) (skipn (Z.to_nat i) l) = skipn c xs.
Proof.
  intros l xs base k c i H Hb Hc ->. rewrite <- H.
  rewrite skipn_firstn_comm, skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma nth_error_first1 : forall (l : list byte) i x, nth_error l i = Some x -> firstn 1 (skipn i l) = [x].
Proof.
  intros l i x H. destruct (nth_error_split _ _ _ H) as (pre & post & E & Hlen). rewrite E at 1.
  rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

Lemma bv_wrap32_eq : forall z, bv_wrap 32 z = z mod 2^32.
Proof. reflexivity. Qed.
Lemma bv_swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.

Lemma le_bytes_to_word4 : forall b0 b1 b2 b3 : byte,
  bv_unsigned (le_bytes_to_word [b0;b1;b2;b3]) = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.
Proof.
  intros. unfold le_bytes_to_word. rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma lw_unsigned4 : forall b0 b1 b2 b3 : byte,
  bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word [b0;b1;b2;b3]))) =
  bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3 + (2^64 - 2^32) * (bv_unsigned b3 / 128).
Proof.
  intros. rewrite sext_small, Z_to_bv_unsigned, signed_of_extract, le_bytes_to_word4 by reflexivity.
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  rewrite bv_swrap32_eq. change (bv_wrap 64 ?x) with (x mod 2^64).
  Z.div_mod_to_equations. lia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma le4_of_mod32 : forall (v : word) (bs : list byte), length bs = 4%nat ->
  bv_unsigned v mod 2^32 = le_val (map bv_unsigned bs) -> le4 v = bs.
Proof.
  intros v bs Hl Hv. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). change (2 ^ 32) with (2^32) in *. rewrite Hv.
  rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma le1_of_mod8 : forall (v : word) (b : byte), bv_unsigned v mod 2^8 = bv_unsigned b -> le1 v = [b].
Proof.
  intros v b Hv. unfold le1. rewrite <- (Z_to_le_bytes_mod 1 _ 8) by (cbn; lia). change (2^8) with (2^8) in *. rewrite Hv.
  cbn. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma le1_zxb : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof. intros b. apply le1_of_mod8. pose proof (byte_range b). rewrite unsigned_lit by lia. apply Z.mod_small. cbn. lia. Qed.

Lemma le4_lw : forall w : list byte, length w = 4%nat -> le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word w))) = w.
Proof.
  intros w Hl. destruct w as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try (cbn in Hl; discriminate).
  apply le4_of_mod32; [reflexivity|]. rewrite lw_unsigned4. cbn [map le_val].
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma lor_add : forall hi lo k, 0 <= k -> 0 <= lo < 2^k -> hi mod 2^k = 0 -> Z.lor hi lo = hi + lo.
Proof.
  intros hi lo k Hk Hlo Hhi.
  assert (HL : Z.land hi lo = 0).
  { rewrite <- (Z.mod_small lo (2^k)) by lia. rewrite <- Z.land_ones by lia.
    rewrite (Z.land_comm lo), Z.land_assoc, Z.land_ones, Hhi by lia. apply Z.land_0_l. }
  pose proof (Z.add_lor_land hi lo). lia.
Qed.
Lemma lor_add' : forall lo hi k, 0 <= k -> 0 <= lo < 2^k -> hi mod 2^k = 0 -> Z.lor lo hi = lo + hi.
Proof. intros. rewrite Z.lor_comm, (lor_add hi lo k); lia. Qed.

(* [comment removed for export] *)
Lemma land_single_bit : forall x k, 0 <= x -> 0 <= k ->
  Z.land x (2^k) = if x mod 2^(k+1) <? 2^k then 0 else 2^k.
Proof.
  intros x k Hx Hk.
  assert (Hpk : 0 < 2^k < 2^(k+1)). { split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]. }
  rewrite (Z.land_comm x), <- (land_mod_pow2_r (2^k) x (k+1)) by lia.
  set (r := x mod 2^(k+1)).
  assert (Hr : 0 <= r < 2^(k+1)) by (subst r; apply Z.mod_pos_bound; lia).
  rewrite Z.pow_add_r in Hr by lia. change (2^1) with 2 in Hr.
  destruct (Z.ltb_spec0 r (2^k)) as [Hl|Hl].
  - rewrite Z.land_comm. apply zb_land_pow2_small; lia.
  - replace r with (Z.lor (2^k) (r - 2^k)).
    2:{ rewrite lor_add with (k := k); try lia. rewrite Z.mod_same; lia. }
    rewrite Z.land_lor_distr_r, Z.land_diag, (Z.land_comm (2^k)), zb_land_pow2_small by lia. apply Z.lor_0_r.
Qed.

Lemma land_bit_2 : forall x, 0 <= x -> Z.land x 2 = if x mod 4 <? 2 then 0 else 2.
Proof. intros x Hx. exact (land_single_bit x 1 Hx ltac:(lia)). Qed.
Lemma land_bit_4 : forall x, 0 <= x -> Z.land x 4 = if x mod 8 <? 4 then 0 else 4.
Proof. intros x Hx. exact (land_single_bit x 2 Hx ltac:(lia)). Qed.
Lemma land_bit_8 : forall x, 0 <= x -> Z.land x 8 = if x mod 16 <? 8 then 0 else 8.
Proof. intros x Hx. exact (land_single_bit x 3 Hx ltac:(lia)). Qed.
Lemma land_bit_16 : forall x, 0 <= x -> Z.land x 16 = if x mod 32 <? 16 then 0 else 16.
Proof. intros x Hx. exact (land_single_bit x 4 Hx ltac:(lia)). Qed.

Lemma land_1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (2^1 - 1) at 1. rewrite zb_land_mask by lia. reflexivity. Qed.
Lemma land_3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (2^2 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.
Lemma land_7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma copied_upd_other : forall src bs p i xs,
  copied src bs p -> (p <= i)%nat -> (i + length xs <= length bs)%nat -> copied src (upd_bytes bs i xs) p.
Proof.
  intros src bs p i xs [Hl Hf] Hi Hx. split.
  - rewrite upd_bytes_length by lia. exact Hl.
  - unfold upd_bytes. rewrite firstn_app, firstn_firstn by lia. replace (Nat.min p i) with p by lia.
    rewrite firstn_length. replace (p - Nat.min i (length bs))%nat with 0%nat by lia. cbn. rewrite app_nil_r. exact Hf.
Qed.

Lemma firstn_S_nth : forall {X} (l : list X) p x, nth_error l p = Some x -> firstn (S p) l = firstn p l ++ [x].
Proof.
  intros X l; induction l as [|a l IH]; intros [|p] x H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - rewrite (IH p x H). reflexivity.
Qed.

Lemma copied_S : forall src bs p x,
  copied src bs p -> nth_error bs p = Some x -> nth_error src p = Some x -> copied src bs (S p).
Proof.
  intros src bs p x [Hl Hf] Hb Hs. split; [exact Hl|].
  rewrite (firstn_S_nth bs p x Hb), (firstn_S_nth src p x Hs), Hf. reflexivity.
Qed.

Lemma upd_bytes_nth_same1 : forall (bs : list byte) i x, (i < length bs)%nat -> nth_error (upd_bytes bs i [x]) i = Some x.
Proof.
  intros bs i x Hi. rewrite upd_bytes_nth by (cbn; lia). cbn [length].
  replace (Nat.leb i i && Nat.ltb i (i + 1))%bool with true. 2:{ symmetry. apply andb_true_iff. split; [apply Nat.leb_le| apply Nat.ltb_lt]; lia. }
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma upd_bytes_nth_after : forall (bs xs : list byte) i j, (j + length xs <= i)%nat -> (i < length bs)%nat ->
  nth_error (upd_bytes bs j xs) i = nth_error bs i.
Proof.
  intros bs xs i j Hj Hi. rewrite upd_bytes_nth by lia.
  replace (Nat.leb j i && Nat.ltb i (j + length xs))%bool with false; [reflexivity|].
  symmetry. apply andb_false_iff. right. apply Nat.ltb_ge. lia.
Qed.
