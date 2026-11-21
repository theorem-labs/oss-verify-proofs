(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (43 recorded proofs replaced by written proofs (sxv_range, swrap32_eq', sxv_small and 40 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_malloc_free () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I35stdpp9countable9Countable00C35stdpp4base;RelDecisionK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions8bv_swrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc59OSSVerify5KrLib6Malloc=F_malloc_free3sxvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib6Malloc=F_malloc_free;swrap32_eq'C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree;sbind_ret_lC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc3rd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4rd16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4rd32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@get_nominal_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dec_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?nontrivial_freeC1?~~~~~~~~~~~~~~~C35stdpp4base4fmapC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C59OSSVerify5KrLib6Malloc9MallocRep<mod_mod_pow2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib6Malloc=F_malloc_free;mod64_mod32C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge=Z_to_bv_mod64C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib6Malloc9MallocRep;wz_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04C56Stdlib6ZArith6BinInt1Z7add_0_rc59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03c59OSSVerify5KrLib6Malloc=F_malloc_free9sextw_sxvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftlI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z;land_nonnegK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z:shiftl_1_lC59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3zxbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6zxb_b8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib3Lib7ZBridge5inr64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge9zr_land_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowc59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_mod32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z3lorC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init9Datatypes3orbc59OSSVerify5KrLib6Malloc=F_malloc_free>sxv_testbit_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC56Stdlib6ZArith6BinInt1Z=pow_lt_mono_rc59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C56Stdlib6ZArith6BinInt1Z<testbit_trueC56Stdlib6ZArith9BinIntDef1Z7testbitC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationc59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_casesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula09C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z;lxor_nonnegC47Corelib4Init9Datatypes4xorbC59OSSVerify5KrLib3Lib8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9lxor_specC59OSSVerify5KrLib3Lib8PropExecAZ_bounded_by_bitsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC59OSSVerify5KrLib3Lib7ZBridge<zb_land_maskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeCzb_land_lor_distr_lC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalc59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_congrC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc59OSSVerify5KrLib6Malloc=F_malloc_free:sxv_eq_iffC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC59OSSVerify5KrLib3Lib8PropExec;Z_lor_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:lor_nonnegc59OSSVerify5KrLib6Malloc=F_malloc_free=lor_sxv_mod32C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC47Corelib7Classes?RelationClasses>iff_TransitiveC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3MemAZ_to_le_bytes_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc=F_malloc_free?add_bit_nocarryC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc=F_malloc_free9le4_congrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib6Malloc=F_malloc_free9wr_at_subC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7area_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z?mul_add_distr_rC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>peek_answer_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_reflC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3bitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6Malloc:slot_startC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9get_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init9Datatypes?andb_true_introC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc=F_malloc_free@get_meta_rec_wr8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc=F_malloc_freeAget_meta_rec_wr16C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc=F_malloc_free9rd8_knownC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06c59OSSVerify5KrLib6Malloc=F_malloc_free=optr_eqb_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc=F_malloc_free:rd16_knownC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6Malloc4freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7testbitC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4FUELC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableK59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc7mapinfoC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition AGP : Z := 0x1a800.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sxv (v : Z) : Z := (bv_swrap 32 v) mod 2^64.

Lemma sxv_range v : 0 <= sxv v < 2^64.
Proof. unfold sxv. apply Z.mod_pos_bound. lia. Qed.

Lemma swrap32_eq' z : bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.

End CANSEC1.
Ltac pow_lits :=
  change (2^64)%Z with 18446744073709551616%Z in *;
  change (2^63)%Z with 9223372036854775808%Z in *;
  change (2^33)%Z with 8589934592%Z in *;
  change (2^32)%Z with 4294967296%Z in *;
  change (2^31)%Z with 2147483648%Z in *.
Ltac mlia := pow_lits; Z.div_mod_to_equations; lia.

Section CANSEC2. Context {rc : runConstT}.
Lemma sxv_small v : 0 <= v < 2^31 -> sxv v = v.
Proof. intros. unfold sxv. rewrite swrap32_eq'. rewrite (Z.mod_small (v + 2^31)) by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma mod64_mod32 z : (z mod 2^64) mod 2^32 = z mod 2^32.
Proof. apply mod_mod_pow2. lia. Qed.

Lemma sxv_mod32 v : (sxv v) mod 2^32 = v mod 2^32.
Proof. unfold sxv. rewrite mod64_mod32, swrap32_eq'. mlia. Qed.

Lemma sx32_wz_sxv v : 0 <= v < 2^64 -> sx32 (wz v) = wz (sxv v).
Proof. intros. unfold sx32, sxv. rewrite wz_unsigned by lia. unfold wz. rewrite Z_to_bv_mod64. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sextw_sxv v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)) + 0)) = wz (sxv v).
Proof.
  rewrite wz_unsigned by (apply sxv_range). rewrite Z.add_0_r. unfold wz, sxv.
  rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 v mod 2^64))). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.
Lemma sextw_sxv' v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)))) = wz (sxv v).
Proof. rewrite <- (Z.add_0_r (bv_unsigned _)). apply sextw_sxv. Qed.

(* [comment removed for export] *)
Lemma self_word b3 : 0 <= b3 < 256 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 b3))) 31)) mod 32)))
  = wz (sxv (2 ^ (Z.land b3 31))).
Proof.
  intros. rewrite zxb_b8, (wz_unsigned b3) by lia.
  assert (0 <= Z.land b3 31 < 32).
  { split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite (wz_unsigned (Z.land b3 31)) by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma all_word mword : 0 <= mword ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (mword mod 32)))) + -1))
  = wz (sxv (2 ^ (mword mod 32 + 1) - 1)).
Proof.
  intros. rewrite unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  replace (2 * 2 ^ (mword mod 32)) with (2 ^ (mword mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
  unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  set (y := 2 ^ (mword mod 32 + 1)). rewrite !swrap32_eq'. mlia.
Qed.

Lemma lor_range64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof. intros. apply (zr_lor a b); unfold inr64; lia. Qed.

Lemma land_range64 a b : 0 <= a < 2^64 -> 0 <= b -> 0 <= Z.land a b < 2^64.
Proof. intros. apply (zr_land_l a b); unfold inr64; lia. Qed.

(* [comment removed for export] *)
Lemma sxv_testbit_lo v i : 0 <= v < 2^32 -> 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
  intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.

Lemma sxv_cases v : 0 <= v < 2^32 -> (v < 2^31 /\ sxv v = v) \/ (2^31 <= v /\ sxv v = v + 2^64 - 2^32).
Proof.
  intros. unfold sxv. rewrite swrap32_eq'.
  destruct (Z.lt_ge_cases v (2^31)); [left|right]; split; auto; pow_lits; Z.div_mod_to_equations; nia.
Qed.

(* [comment removed for export] *)
Lemma free_assert_ok freed avail idx :
  0 <= freed < 2^32 -> 0 <= avail < 2^32 -> 0 <= idx < 32 ->
  Z.testbit freed idx = false -> Z.testbit avail idx = false ->
  Z.land (sxv (2^idx)) (Z.lor (sxv freed) (sxv avail)) = 0.
Proof.
  intros HF HA HI TF TA.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64).
  2:{ rewrite (Z.bits_above_log2 (sxv (2^idx))); [reflexivity| apply sxv_range |].
      pose proof (sxv_range (2^idx)). destruct (Z.eq_dec (sxv (2^idx)) 0) as [->|]. cbn; lia.
      apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia]. }
  destruct (Z.lt_ge_cases idx 31).
  - rewrite (sxv_small (2^idx)) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec idx n); [|reflexivity]. subst n. cbn.
    rewrite !sxv_testbit_lo by lia. rewrite TF, TA. reflexivity.
  - assert (idx = 31) by lia. subst idx.
    (* [comment removed for export] *)
    assert (Hlt : forall v, 0 <= v < 2^32 -> Z.testbit v 31 = false -> v < 2^31).
    { intros v Hv Hb. destruct (Z.lt_ge_cases v (2^31)); auto.
      exfalso. assert (Z.testbit v 31 = true); [|congruence].
      rewrite Z.testbit_true by lia. replace (v / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity. }
    pose proof (Hlt freed HF TF). pose proof (Hlt avail HA TA).
    rewrite (sxv_small freed), (sxv_small avail) by lia.
    destruct (Z.lt_ge_cases n 31).
    + replace (Z.testbit (sxv (2^31)) n) with false; [reflexivity|].
      symmetry. rewrite sxv_testbit_lo by lia. rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
    + assert (Lg : forall v, 0 <= v < 2^31 -> Z.testbit v n = false).
      { intros v Hv. destruct (Z.eq_dec v 0) as [->|]. apply Z.bits_0.
        apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 31); [apply Z.log2_lt_pow2; lia| lia]. }
      rewrite (Lg freed), (Lg avail) by lia. apply andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma sxv_zero v : 0 <= v < 2^32 -> sxv v = 0 <-> v = 0.
Proof. intros. destruct (sxv_cases v H) as [[? ->]|[? ->]]; lia. Qed.

(* [comment removed for export] *)
Lemma add_bit_nocarry v idx : 0 <= v < 2^32 -> 0 <= idx < 32 -> Z.testbit v idx = false ->
  v + 2^idx < 2^32.
Proof.
  intros Hv Hi Hb.
  assert (HL : Z.land v (2^idx) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec idx n); [subst; rewrite Hb; reflexivity | apply andb_false_r]. }
  rewrite (Z.add_nocarry_lxor _ _ HL).
  assert (0 <= 2^idx < 2^32) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
  apply Z_bounded_by_bits; [lia | apply Z.lxor_nonneg; lia |].
  intros k Hk. rewrite Z.lxor_spec, (Z_testbit_high 32 v k), (Z_testbit_high 32 (2^idx) k) by lia. reflexivity.
Qed.

Lemma sxv_congr v w : v mod 2^32 = w mod 2^32 -> sxv v = sxv w.
Proof. intros E. unfold sxv. rewrite !swrap32_eq'. f_equal. f_equal. rewrite <- Zplus_mod_idemp_l, E, Zplus_mod_idemp_l. reflexivity. Qed.

Lemma lor_sxv_mod32 f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
  (Z.lor (sxv f) (sxv a)) mod 2^32 = Z.lor f a.
Proof.
  intros. rewrite <- zb_land_mask, zb_land_lor_distr_l, !zb_land_mask, !sxv_mod32, !Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma addw_word x y : Z_to_bv 64 (bv_swrap 32 (x + y)) = wz (sxv (x + y)).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

Lemma wz_inj a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> wz a = wz b -> a = b.
Proof. intros Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !wz_unsigned in E by lia. exact E. Qed.

Lemma sxv_eq_iff v w : sxv v = sxv w <-> v mod 2^32 = w mod 2^32.
Proof. split; [| apply sxv_congr]. intros E. rewrite <- (sxv_mod32 v), <- (sxv_mod32 w), E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma free_all_test freed avail idx li :
  0 <= freed < 2^32 -> 0 <= avail < 2^32 -> 0 <= idx <= li -> li < 32 ->
  (sxv (sxv (2^idx) + Z.lor (sxv freed) (sxv avail)) = sxv (2^(li + 1) - 1)
   <-> Z.lor freed avail + 2^idx = 2^(li+1) - 1).
Proof.
  intros HF HA HI HL. rewrite sxv_eq_iff.
  rewrite <- Zplus_mod_idemp_r, lor_sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32 by lia.
  assert (X1 : 0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
  assert (XY : 2^idx < 2^(li+1)) by (apply Z.pow_lt_mono_r; lia).
  assert (Y32 : 2^(li+1) <= 2^32) by (apply Z.pow_le_mono_r; lia).
  pose proof (Z_lor_range freed avail ltac:(lia) ltac:(lia)).
  assert (HLr : Z.lor freed avail < 2^32).
  { apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |]. intros k Hk.
    rewrite Z.lor_spec, (Z_testbit_high 32 freed k), (Z_testbit_high 32 avail k) by lia. reflexivity. }
  set (X := 2^idx) in *. set (Y := 2^(li+1)) in *. set (L := Z.lor freed avail) in *.
  clearbody X Y L. rewrite (Z.mod_small X) by lia. mlia.
Qed.

(* [comment removed for export] *)
Lemma le4_congr (a b : word) : bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> le4 a = le4 b.
Proof. intros E. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia). rewrite E. reflexivity. Qed.

Lemma free_store_val freed idx : 0 <= freed < 2^32 -> 0 <= idx < 32 -> Z.testbit freed idx = false ->
  le4 (wz (sxv (sxv (2^idx) + sxv freed))) = le4 (wz (freed + 2^idx)).
Proof.
  intros. pose proof (add_bit_nocarry freed idx ltac:(lia) ltac:(lia) ltac:(assumption)).
  assert (0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
  apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
  rewrite sxv_mod32, <- Zplus_mod_idemp_r, sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32, !Z.mod_small by lia. lia.
Qed.

Lemma self_word' b3 : 0 <= b3 < 256 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 (Z.land b3 31)) mod 32)))
  = wz (sxv (2 ^ (Z.land b3 31))).
Proof.
  intros.
  assert (0 <= Z.land b3 31 < 32).
  { split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite (wz_unsigned (Z.land b3 31)) by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma sllw2_word e : 0 <= e ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (e mod 32))) = wz (sxv (2 ^ (e mod 32 + 1))).
Proof.
  intros. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  replace (2 * 2 ^ (e mod 32)) with (2 ^ (e mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma addiw_m1_word y : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv y)) + -1)) = wz (sxv (y - 1)).
Proof.
  rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.

Lemma rw_cells_congr segs m A cs cs' :
  cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' ->
  rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof. intros EB ES WF [[_ B] W]. split; [split; [exact WF| rewrite <- EB; exact B] | rewrite <- ES; exact W]. Qed.

Lemma le1_neg1 : le1 (Z_to_bv 64 (-1)) = [b8 255].
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
End CANSEC2.
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          let E := fresh "EQ" m' in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
          clear HB; try rename H' into H
        end
    end
  end.

Section CANSEC3. Context {rc : runConstT}.
Definition frozen (P : Prop) : Prop := P.

Definition free_W (sp : word) (P G : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.

(* [comment removed for export] *)
End CANSEC3.
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT}.
Lemma wr_at_sub : forall segs m A n A' n',
  wr_at segs m A n -> A <= A' -> A' + n' <= A + n -> wr_at segs m A' n'.
Proof.
  intros segs m A n A' n' (H0 & H1 & H) LA LB. split; [lia|]. split; [lia|].
  intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed.

Lemma rw_cells_prefix : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1.
Proof.
  intros segs m A cs1 cs2 [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 _].
  split; [split; [exact WF1 | exact B1] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

Lemma bytes_at_at : forall segs m a a' bs, bytes_at segs m a bs -> a = a' -> bytes_at segs m a' bs.
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_of_bytes : forall segs m A cs,
  cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
Proof. intros. split; [split|]; assumption. Qed.

(* [comment removed for export] *)
Lemma area_of_slot : forall (a : aptr) k, snd a mod 4096 = 0 -> 0 <= k < 101 ->
  area_of (aadd a (24 + 40 * k)) = a.
Proof.
  intros [ar ao] k Hm Hk. unfold area_of, aadd. cbn [fst snd] in *. f_equal.
  replace (ao + (24 + 40 * k)) with ((24 + 40 * k) + (ao / 4096) * 4096) by (Z.div_mod_to_equations; nia).
  rewrite Z.mod_add, Z.mod_small by lia. Z.div_mod_to_equations; nia.
Qed.

Lemma page_off_mod : forall b o x, b mod 4096 = 0 -> o mod 4096 = 0 -> 0 <= x < 4096 -> (b + o + x) mod 4096 = x.
Proof.
  intros b o x Hb Ho Hx.
  replace (b + o + x) with (x + (b / 4096 + o / 4096) * 4096) by (Z.div_mod_to_equations; nia).
  rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.

Lemma base16_mod : forall b po, b mod 4096 = 0 -> po mod 16 = 0 -> (b + po) mod 16 = 0.
Proof.
  intros b po Hb Hp. replace (b + po) with ((b / 4096) * 256 * 16 + (po / 16) * 16) by (Z.div_mod_to_equations; lia).
  rewrite <- Z.mul_add_distr_r, Z.mod_mul. reflexivity. lia.
Qed.

(* [comment removed for export] *)
Definition freeW (sp : word) (P G : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rd8_known {R} st q v (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.

Lemma rd16_known {R} st q v0 v1 (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v0 ->
  cell_read (get_shadow st (fst q)) (snd q + 1) = Known v1 ->
  rd16 st q k = k (v0 + 256 * v1).
Proof. intros H0 H1. unfold rd16, rd8. rewrite H0. cbn [fst snd aadd]. rewrite H1. reflexivity. Qed.

Lemma get_meta_rec_wr8 st q v g : get_meta_rec (wr8 q v st) g = get_meta_rec st g.
Proof. reflexivity. Qed.
Lemma get_meta_rec_wr16 st q v g : get_meta_rec (wr16 q v st) g = get_meta_rec st g.
Proof. reflexivity. Qed.

Lemma optr_eqb_refl : forall q : aptr, optr_eqb (Some q) (Some q) = true.
Proof. intros [qa qb]. unfold optr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma free_trivial_model : forall st (p : aptr) g gh ar (b3 lo hi : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  let st' := upd_meta g (m_set_freed (m_freed mr + bit idx)) (wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)) in
  let reserved := Z.shiftr b3 5 in
  let e := aadd (slot_start' mr idx) (get_stride mr - IB) in
  po mod 16 = 0 ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
  0 <= m_avail mr -> 0 <= m_freed mr -> 0 <= b3 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  (m_maplen mr <> 0 -> off16 <= m_maplen mr * 4096 / UNIT - 1) ->
  (* [comment removed for export] *)
  reserved < 5 -> reserved <= snd e - po ->
  cell_read sh (snd e - reserved) = Known 0 -> cell_read sh (snd e) = Known 0 ->
  (* [comment removed for export] *)
  m_freed mr <> 0 -> Z.lor (m_freed mr) (m_avail mr) + bit idx <> mask_upto (m_last_idx mr) ->
  free st (Some p) = ret st'.
Proof.
  intros until hi. intros sh po off16 idx base mr st' reserved e AL C4 C3 C2 C1 Hgh Hg Hmem Har Hchk AV FR B3
         Hidx Hav Hfr Hsc Hsc63 Hml RES5 RESe E1 E0 Hfz Hall.
  unfold free, free_hdr, get_meta, guard. fold po. rewrite (proj2 (Z.eqb_eq _ _) AL).
  rewrite (rd16_known st (aadd p (-2)) lo hi) by (cbn [fst snd aadd]; fold po; first [replace (po + -2) with (po - 2) by lia; exact C2 | replace (po + -2 + 1) with (po - 1) by lia; exact C1]).
  cbv beta.
  rewrite (rd8_known st (aadd p (-3)) b3) by (cbn [fst snd aadd]; fold po; replace (po + -3) with (po - 3) by lia; exact C3).
  cbv beta.
  rewrite (rd8_known st (aadd p (-4)) 0) by (cbn [fst snd aadd]; fold po; replace (po + -4) with (po - 4) by lia; exact C4).
  cbv beta. cbn [Z.eqb negb].
  fold off16. fold base. unfold get_group. rewrite Hgh, Hg. fold mr. rewrite Hmem, optr_eqb_refl.
  fold idx. replace (idx <=? m_last_idx mr) with true by (symmetry; apply Z.leb_le; lia).
  unfold testbit. rewrite Hav, Hfr. cbn [negb].
  rewrite Har, Hchk, Z.eqb_refl.
  match goal with |- context [if (if ?c then ?x else ?y) then _ else SVis (EUndef (UAssert 16)) _] =>
    replace (if c then x else y) with true end.
  2:{ destruct (Z.ltb_spec (m_sizeclass mr) 48).
      - specialize (Hsc ltac:(lia)). symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
      - specialize (Hsc63 ltac:(lia)). symmetry. apply Z.eqb_eq. lia. }
  match goal with |- context [if (if ?c then ?x else ?y) then _ else SVis (EUndef (UAssert 17)) _] =>
    replace (if c then x else y) with true end.
  2:{ destruct (Z.eqb_spec (m_maplen mr) 0); cbn [negb]; [reflexivity|]. symmetry. apply Z.leb_le. apply Hml. assumption. }
  unfold slot_start. rewrite Hmem.
  assert (He : aadd (aadd base (UNIT + get_stride mr * idx)) (get_stride mr - IB) = e) by (unfold e, slot_start'; rewrite Hmem; reflexivity).
  rewrite He.
  assert (Fe : fst e = fst p) by (rewrite <- He; reflexivity).
  unfold get_nominal_size.
  rewrite (rd8_known st (aadd p (-3)) b3) by (cbn [fst snd aadd]; fold po; replace (po + -3) with (po - 3) by lia; exact C3).
  cbv beta. fold reserved.
  replace (5 <=? reserved) with false by (symmetry; apply Z.leb_gt; lia).
  fold po. replace (reserved <=? snd e - po) with true by (symmetry; apply Z.leb_le; lia).
  rewrite (rd8_known st (aadd e (- reserved)) 0) by (cbn [fst snd aadd]; rewrite Fe; fold sh; replace (snd e + - reserved) with (snd e - reserved) by lia; exact E1).
  cbv beta. cbn [Z.eqb].
  rewrite (rd8_known st e 0) by (rewrite Fe; exact E0).
  unfold guard. cbn [Z.eqb]. unfold Malloc.ret at 1. rewrite sbind_ret_l.
  unfold free_tail, guard. rewrite !get_meta_rec_wr16, !get_meta_rec_wr8. fold mr.
  unfold testbit. rewrite Z.lor_spec, Hfr, Hav. cbn [orb negb].
  replace (m_freed mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hfz).
  replace (Z.lor (m_freed mr) (m_avail mr) + bit idx =? mask_upto (m_last_idx mr)) with false by (symmetry; apply Z.eqb_neq; exact Hall).
  cbn [orb negb]. reflexivity.
Qed.


End CANSEC4.
