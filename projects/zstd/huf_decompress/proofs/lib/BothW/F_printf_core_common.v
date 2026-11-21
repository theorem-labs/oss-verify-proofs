(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (90 recorded proofs replaced by written proofs (zb_length, zb_app, nth_error_zb and 87 more)). *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import Stdio_kit Stdio_kitI F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import Printf_zfacts F_printf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_printf_core_common () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib3Lib3Arr@upd_firstn_skipnC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List:firstn_mapI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00C46Stdlib5Lists4List7map_appC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List=nth_error_mapI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes:option_mapK47Corelib4Init5Logic2eq01C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8map_consC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notC46Stdlib5Lists4List=nth_error_nthI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_NoneC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec6Prelim4znthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leI47Corelib4Init9Datatypes4bool00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C46Stdlib5Lists4List6nth_okK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesc59OSSVerify5KrLib5BothWDF_printf_core_common>znth_nth_errorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common<nth_error_zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr9u8ro_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List6nth_InC47Corelib4Init5Logic5proj1C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4xorbC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9lxor_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List:skipn_all2K47Corelib7Numbers7BinNums1Z02C47Corelib4Init3Nat3addC59OSSVerify5KrLib3Lib3Arr?nth_error_splitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib5Lists7ListDef5skipnC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib4Init3Nat3subC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib5Lists4List9skipn_appC46Stdlib5Lists4List9app_assocC35stdpp7tactics<f_equal_helpC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_1_rC56Stdlib6ZArith4Znat5Z2Nat7inj_addc59OSSVerify5KrLib5BothWDF_printf_core_common3sfxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib5Lists4List;skipn_skipnC46Stdlib5Lists4List<length_skipnC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z;lt_ge_casesc59OSSVerify5KrLib5BothWDF_printf_core_common8sfx_consC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos6to_natC47Corelib4Init5Logic7f_equalC57Corelib7BinNums6PosDef3Pos7compareC47Corelib4Init9Datatypes7CompOppK47Corelib4Init5Logic3and01c59OSSVerify5KrLib5BothWDF_printf_core_common7sfx_nilC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib6Common<Printf_model7lit_runC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes3orbC47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z8eqb_specK46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib5BothWDF_printf_core_common>lit_run_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common9sfx_skipnC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat9ltb_spec0C46Stdlib5Lists4List?nth_error_skipnC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib5Lists4List@nth_error_firstnc59OSSVerify5KrLib5BothWDF_printf_core_common>lit_run_firstnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common:lit_run_inC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z3oppC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z>div_unique_posC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7div_divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z3lorC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model:digits_auxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common<digits_aux_SC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z7pow_0_rC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z9div_smallC59OSSVerify5KrLib6Common<Printf_model:dec_digitsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lt_transc59OSSVerify5KrLib5BothWDF_printf_core_common?digits_aux_fuelC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8f_equal2c59OSSVerify5KrLib5BothWDF_printf_core_common>digits_aux_accC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_commonAdigits_aux_lengthC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=length_firstnC47Corelib4Init3Nat3minC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List=firstn_firstnC46Stdlib5Lists4List:firstn_appC56Stdlib6ZArith4Znat5Nat2Z7inj_minc59OSSVerify5KrLib5BothWDF_printf_core_common?upd_firstn_partC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common<upd_skipn_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model:hex_digitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model7XDIGITSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC59OSSVerify5KrLib5BothW=Printf_zfacts>Zrange_forallbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common;hexchar_ok0C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib5BothWDF_printf_core_common<hexchar_ok32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common=hexchar_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6wrap64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat:wrap64_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat4lo64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat4hi64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib3Lib5Bytes;lor_lt_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5mk128C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec>Z_shiftr_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat8is_neg64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5sra63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5shl64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat<wrap64_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common=shr64_range64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;Z_lor_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib6Common9SoftFloat5add64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat<clz64_mirrorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5sub64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6sext32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common;mk128_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegC59OSSVerify5KrLib2AS8PropExec<Z_lxor_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common;sra63_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Bytes<land_lt_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat9f128_of_dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6INF_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat;IMPLICIT_HIC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC59OSSVerify5KrLib6Common;SFW1_lemmas:swrap32_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge=Z_to_bv_mod64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4zx32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_diagC56Stdlib6ZArith6BinInt1Z:land_assocC59OSSVerify5KrLib6Common<F_fmt_fp_libCbytes_le_to_Z_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib6Common<F_fmt_fp_libBZ_to_le_bytes_to_ZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common<le8_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;printf_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib6Common<Printf_model9parse_dirC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4convC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model3dir00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common=printf_loop_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4mpadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8fp_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_flC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lnotC59OSSVerify5KrLib6Common<Printf_model3d_wC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib6Common<Printf_model3d_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8LEFT_ADJC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8ZERO_PADC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5BothWDF_printf_core_common;In_firstn_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common:In_skipn_wC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List2hdc59OSSVerify5KrLib5BothWDF_printf_core_common:Forall_subC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9skipn_mapC46Stdlib5Lists4List<firstn_skipnC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat5min_lI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5BothW=Printf_zfacts?parse_dir_shapeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8is_digitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;parse_flagsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_xpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model9conv_typeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_tyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model6getintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=Printf_zfactsAgetint_some_rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8firstn_0C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kitBrw_cells_bytes_at'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@bytes_at_ov_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib5BothW9F_pop_arg;firstn4_le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5r_rloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5r_rhiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit7shcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit?shclean_app_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow7app_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4KLOWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5KHIGHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4KENDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4appWC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstc59OSSVerify5KrLib5BothWDF_printf_core_common4appBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit7ashsafeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit@ashenv_transportC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common9ashsafe_WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit@rclean_transportC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW9Stdio_kit6region00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common6appW_WC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getc59OSSVerify5KrLib5BothWDF_printf_core_common3FokC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common4POSTC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib5BothWDF_printf_core_common;Forall_znthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image@ro_bytes_b_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;ro_bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=Printf_zfacts7STATES0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=Printf_zfacts?conv_type_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common=states0_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common;zbytes_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=Printf_zfacts<states0_convC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common6PFXSTRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common9pfx_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common<bytes_at_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common8zb_skipnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common9zb_firstnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common=xdigits_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common3JT1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common9jt1_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idc59OSSVerify5KrLib5BothWDF_printf_core_common9zb_lengthC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01c59OSSVerify5KrLib5BothWDF_printf_core_common<jt1_read_litC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib6Common<Printf_model5T_DBLC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib6Common<Printf_model5T_PTRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model5T_INTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model6T_UINTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;SFW1_lemmas<zb_land_pow2C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool3eqbc59OSSVerify5KrLib5BothWDF_printf_core_common<nzmask_bits'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1Z9lnot_specC56Stdlib6ZArith8Zbitwise1Z?sub_land_same_lC56Stdlib6ZArith6BinInt1Z7lxor_eqC56Stdlib6ZArith6BinInt1Z>lxor_nilpotentc59OSSVerify5KrLib5BothWDF_printf_core_common?land_lxor_distrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF6implAMC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib5BothW6MonadF5postFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common<implAM_eq_msC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_printf_iface?sink_frame_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_printf_iface6arg_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4rrngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5inregC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K59OSSVerify5KrLib6Common<Printf_model4parg02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_printf_iface7args_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common8arg_ok_WC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common8lo_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common:lo_cells14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5BothW9F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_pop_arg=va_area_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_SomeC59OSSVerify5KrLib5BothW9F_pop_arg<pop_arg_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_pop_arg<pop_arg_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common4FokdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_pop_arg:pop_arg_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_pop_arg:pop_arg_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun9memchr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=Strnlen_iface:strnlen_rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common7env_nowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6ashenvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common6rc_nowC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib4LibA5StepF9stepF_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=Strnlen_iface>strnlen_a_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun;strnlen_resC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI4ELinuxProcessSemantics5Riscv5Instr5instr00C59OSSVerify5KrLib5BothW=Strnlen_iface?STRNLEN_I_DEPTHC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffc59OSSVerify5KrLib5BothWDF_printf_core_common6u8_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_printf_iface8out_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common9out_postqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_printf_iface8out_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF;implAM_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_printf_iface9OUT_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:StdioFiles;GLOBALS_TOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_printf_iface;fpcall_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_printf_iface;fpcall_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothWDF_printf_core_common8fp_postqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit<FMT_FP_DEPTHC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
(* [comment removed for export] *)

Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac show_goal := match goal with |- ?G => idtac "GOAL:" G end.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac plia := unfold zlength, got_ssp, ssp_guard, PC_DEPTH, OUT_DEPTH, GLOBALS_TOP, FMT_FP_DEPTH, INT_MAX in *; lia.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.
(* [comment removed for export] *)
Tactic Notation "callw" tactic3(tac) :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtF_cut; [ tac | post_call segs m ]
  end.
Ltac fix_stk := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
(* [comment removed for export] *)
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).
(* [comment removed for export] *)
Ltac fixr := try (rewrite !swrap32_small by lia); try (rewrite !Z.add_0_r).
(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition hide (P : Prop) := P.
End CANSEC1.
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
  lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

(* [comment removed for export] *)
Ltac ienter := ienterF.
Ltac ileave := ileaveF.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma nth_error_zb : forall l i c, nth_error l i = Some c -> nth_error (zb l) i = Some (Z_to_bv 8 c).
Proof. intros l i c H. unfold zb. rewrite nth_error_map, H. reflexivity. Qed.
Lemma znth_nth_error : forall l i, (0 <= i < zlength l)%Z -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof.
  intros l i Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (nth_error l (Z.to_nat i)) as [c|] eqn:E.
  - rewrite (nth_error_nth _ _ _ E). reflexivity.
  - apply nth_error_None in E. unfold zlength in Hi. lia.
Qed.
Lemma zbytes_read : forall m A l i a,
  bytes_at bsegs m A (zb l) -> (0 <= i < zlength l)%Z -> a = wa (A + i) ->
  ov_read_bytes bsegs m a 1 = Some [Z_to_bv 8 (znth l i)].
Proof.
  intros m A l i a HB Hi ->.
  eapply (u8ro_read bsegs m A (zb l) i); [exact HB | | lia | reflexivity].
  apply nth_error_zb. apply znth_nth_error. exact Hi.
Qed.
Lemma Forall_znth : forall (P : Z -> Prop) l i, Forall P l -> (0 <= i < zlength l)%Z -> P (znth l i).
Proof.
  intros P l i HF Hi. apply (proj1 (Forall_forall P l) HF). unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  apply nth_In. unfold zlength in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma land_lxor_distr : forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof. intros. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec. destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity. Qed.

(* [comment removed for export] *)
Section Sfx.
  Variable fmt : list Z.
  Definition sfx (k : Z) : list Z := skipn (Z.to_nat k) fmt.
  Lemma sfx_cons : forall k, (0 <= k < zlength fmt)%Z -> sfx k = znth fmt k :: sfx (k + 1).
  Proof.
    intros k Hk. unfold sfx. rewrite Z2Nat.inj_add, Nat.add_1_r by lia.
    pose proof (znth_nth_error fmt k Hk) as E.
    destruct (nth_error_split fmt (Z.to_nat k) _ E) as (pre & post & Efmt & Hlen).
    rewrite Efmt at 1 2. rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. cbn [skipn app].
    rewrite <- Efmt. f_equal. rewrite Efmt at 1. change (pre ++ znth fmt k :: post) with (pre ++ ([znth fmt k] ++ post)).
    rewrite app_assoc, skipn_app, skipn_all2 by (rewrite length_app; cbn; lia). rewrite length_app. cbn [length].
    replace (S (Z.to_nat k) - (length pre + 1))%nat with 0%nat by lia. reflexivity.
  Qed.
  Lemma sfx_nil : forall k, (zlength fmt <= k)%Z -> sfx k = [].
  Proof. intros k Hk. unfold sfx. apply skipn_all2. unfold zlength in Hk. lia. Qed.
  Lemma sfx_skipn : forall n k, (0 <= k)%Z -> skipn n (sfx k) = sfx (k + Z.of_nat n).
  Proof. intros n k Hk. unfold sfx. rewrite skipn_skipn. f_equal. lia. Qed.
  Lemma sfx_length : forall k, (0 <= k <= zlength fmt)%Z -> zlength (sfx k) = (zlength fmt - k)%Z.
  Proof. intros k Hk. unfold sfx, zlength in *. rewrite length_skipn. lia. Qed.
  Lemma sfx_cons_inv : forall k c s, (0 <= k)%Z -> sfx k = c :: s -> (k < zlength fmt)%Z /\ c = znth fmt k /\ s = sfx (k + 1).
  Proof.
    intros k c s Hk E. destruct (Z.lt_ge_cases k (zlength fmt)) as [Hlt|Hge].
    - rewrite sfx_cons in E by lia. injection E as <- <-. split; [exact Hlt| split; reflexivity].
    - rewrite sfx_nil in E by lia. discriminate.
  Qed.

  Lemma lit_run_firstn : forall s, lit_run s = firstn (length (lit_run s)) s.
  Proof. induction s as [|c s IH]; cbn; [reflexivity|]. destruct ((c =? 0) || (c =? 37))%Z; cbn; [reflexivity|]. f_equal. exact IH. Qed.
  Lemma lit_run_length : forall s, (length (lit_run s) <= length s)%nat.
  Proof. induction s as [|c s IH]; cbn; [lia|]. destruct ((c =? 0) || (c =? 37))%Z; cbn; lia. Qed.
  Lemma lit_run_in : forall s j c, nth_error (lit_run s) j = Some c -> c <> 0%Z /\ c <> 37%Z.
  Proof.
    induction s as [|c s IH]; intros j c' H; cbn in H. { destruct j; discriminate. }
    destruct (Z.eqb_spec c 0); [destruct j; discriminate|]. destruct (Z.eqb_spec c 37); [destruct j; discriminate|]. cbn in H.
    destruct j as [|j]; cbn in H. { injection H as <-. lia. } eapply IH. exact H.
  Qed.
  Lemma lit_run_stop : forall s c s', skipn (length (lit_run s)) s = c :: s' -> c = 0%Z \/ c = 37%Z.
  Proof.
    induction s as [|c s IH]; intros c' s' H; cbn in H; [discriminate|].
    destruct (Z.eqb_spec c 0); [cbn in H; injection H as <- _; lia|]. destruct (Z.eqb_spec c 37); [cbn in H; injection H as <- _; lia|].
    cbn in H. eapply IH. exact H.
  Qed.
  (* [comment removed for export] *)
  Lemma lit_run_sfx : forall i, (0 <= i)%Z -> let n := zlength (lit_run (sfx i)) in
    (i + n <= Z.max i (zlength fmt))%Z /\ skipn (length (lit_run (sfx i))) (sfx i) = sfx (i + n)
    /\ (forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z
    /\ lit_run (sfx i) = firstn (Z.to_nat n) (sfx i).
  Proof.
    intros i Hi. cbv zeta. pose proof (lit_run_length (sfx i)) as L. unfold zlength.
    split. { unfold sfx in L |- *. rewrite length_skipn in L. lia. }
    split. { rewrite sfx_skipn by lia. reflexivity. }
    split.
    - intros j Hj.
      assert (E : nth_error (lit_run (sfx i)) (Z.to_nat j) = Some (znth fmt (i + j))).
      { rewrite lit_run_firstn. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 (Z.to_nat j) (length (lit_run (sfx i)))); [|lia].
        unfold sfx. rewrite nth_error_skipn. replace (Z.to_nat i + Z.to_nat j)%nat with (Z.to_nat (i + j)) by lia.
        apply znth_nth_error. unfold sfx in *. rewrite length_skipn in L. unfold zlength. lia. }
      exact (lit_run_in _ _ _ E).
    - rewrite Nat2Z.id. apply lit_run_firstn.
  Qed.
End Sfx.

Lemma land_M64_id : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma landM64_zero : forall p, (-2^63 <= p < 2^63)%Z -> (Z.land p 18446744073709551615 = 0 <-> p = 0)%Z.
Proof.
  intros p Hp. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  split; intros H; [|subst p; reflexivity]. Z.div_mod_to_equations. nia.
Qed.
Lemma if_false_Z : forall a b : Z, (if false then a else b) = b.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC2"] "h01ah11bp;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0p10030p4p710R0p8P2p1003Np4p7210p8p1004?p4p7210P0p8p1004kp4p710P0p8p100A_p4p7210P0p8p1006Gp4p710P0p8p1006fp4p7210P0p8g00@ij20Tg00;fR0f0,00X10W0o"). Qed.
Lemma if_true_Z : forall a b : Z, (if true then a else b) = a.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC2"] "h01ah11bp;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0p10030p4p710R0p8P2p1003Np4p7210p8p1004?p4p7210P0p8p1004kp4p710P0p8p100A_p4p7210P0p8p1006Gp4p710P0p8p1006fp4p7210P0p8g00@ij20Tg00;fR0f1,00X10W0o"). Qed.

(* [comment removed for export] *)
Lemma div10_magic : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (Z.shiftr (x * 14757395258967641293) 64) 3 = (x / 10)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia. change (2^64 * 2^3)%Z with (2^67)%Z.
  pose proof (Z.div_mod x 10 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R.
  pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0. pose proof (Z.div_lt_upper_bound x 10 (2^64) ltac:(lia) ltac:(lia)) as Q1.
  set (q := (x / 10)%Z) in *. set (s := (x mod 10)%Z) in *. clearbody q s. subst x.
  symmetry. apply (Z.div_unique_pos _ _ _ (2 * q + s * 14757395258967641293)%Z).
  - change (2^67)%Z with 147573952589676412928%Z. change (2^64)%Z with 18446744073709551616%Z in Q1. lia.
  - change (2^67)%Z with 147573952589676412928%Z. lia.
Qed.
Lemma lor48_digit : forall d, (0 <= d < 10)%Z -> Z.lor d 48 = (48 + d)%Z.
Proof.
  intros d Hd.
  assert (H : (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9)%Z) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
Qed.
Lemma le1_small : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma digits_aux_S : forall f b d y acc,
  digits_aux (S f) b d y acc = if y =? 0 then acc else digits_aux f b d (y / b) (d (y mod b) :: acc).
Proof. reflexivity. Qed.
Lemma digits_aux_acc : forall f b d y acc, digits_aux f b d y acc = digits_aux f b d y [] ++ acc.
Proof.
  induction f as [|f IH]; intros b d y acc; [reflexivity|]. rewrite !digits_aux_S.
  destruct (y =? 0)%Z; [reflexivity|]. rewrite (IH _ _ _ (d (y mod b)%Z :: acc)), (IH _ _ _ [d (y mod b)%Z]). rewrite <- app_assoc. reflexivity.
Qed.
Lemma digits_aux_fuel : forall b f d y acc, (1 < b)%Z -> (0 <= y < b ^ Z.of_nat f)%Z ->
  digits_aux f b d y acc = digits_aux (S f) b d y acc.
Proof.
  intros b. induction f as [|f IH]; intros d y acc Hb Hy.
  - rewrite digits_aux_S. rewrite Z.pow_0_r in Hy. replace y with 0%Z by lia. reflexivity.
  - rewrite !digits_aux_S. destruct (Z.eqb_spec y 0); [reflexivity|].
    apply IH; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hy by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_comm. lia.
Qed.
Lemma dec_digits_0 : dec_digits 0 = [].
Proof. reflexivity. Qed.
Lemma dec_digits_small : forall x, (1 <= x <= 9)%Z -> dec_digits x = [48 + x]%Z.
Proof.
  intros x Hx. unfold dec_digits. change 20%nat with (S (S 18)). rewrite !digits_aux_S.
  destruct (Z.eqb_spec x 0); [lia|]. rewrite Z.div_small by lia. cbn [Z.eqb]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma dec_digits_step : forall x, (10 <= x < 2^64)%Z -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10]%Z.
Proof.
  intros x Hx. unfold dec_digits at 1. change 20%nat with (S 19). rewrite digits_aux_S.
  destruct (Z.eqb_spec x 0); [lia|]. rewrite digits_aux_acc. apply (f_equal2 (@app Z)); [|reflexivity]. unfold dec_digits. apply digits_aux_fuel; [lia|].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  apply Z.lt_trans with (2^64)%Z; [lia|]. vm_compute. reflexivity.
Qed.
Lemma digits_aux_length : forall f b d y acc, (length (digits_aux f b d y acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros b d y acc; [cbn; lia|]. rewrite digits_aux_S.
  destruct (y =? 0)%Z; [cbn; lia|]. specialize (IH b d (y / b)%Z (d (y mod b)%Z :: acc)). cbn [length] in IH. lia.
Qed.
Lemma dec_digits_length : forall x, (length (dec_digits x) <= 20)%nat.
Proof. intros x. unfold dec_digits. pose proof (digits_aux_length 20 10 (fun v => 48 + v)%Z x []) as L. cbn [length Nat.add] in L. exact L. Qed.
Lemma dec_digits_range : forall x, Forall (fun c => 48 <= c < 58)%Z (dec_digits x).
Proof.
  intros x. unfold dec_digits.
  assert (G : forall f y acc, Forall (fun c => 48 <= c < 58)%Z acc -> Forall (fun c => 48 <= c < 58)%Z (digits_aux f 10 (fun v => 48 + v)%Z y acc)).
  { induction f as [|f IH]; intros y acc Ha; [exact Ha|]. rewrite digits_aux_S.
    destruct (Z.eqb_spec y 0); [exact Ha|]. apply IH. constructor; [|exact Ha]. pose proof (Z.mod_pos_bound y 10 ltac:(lia)). lia. }
  apply G. constructor.
Qed.

Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells bsegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.
Lemma upd_firstn_part : forall {X} (l : list X) i x n, (n <= i < length l)%nat -> firstn n (upd l i x) = firstn n l.
Proof.
  intros X l i x n H. rewrite upd_firstn_skipn by lia. rewrite firstn_app, firstn_firstn, length_firstn.
  replace (Nat.min n i) with n by lia. replace (n - Nat.min i (length l))%nat with 0%nat by lia. cbn. apply app_nil_r.
Qed.
Lemma upd_skipn_at : forall {X} (l : list X) i x, (i < length l)%nat -> skipn i (upd l i x) = x :: skipn (S i) l.
Proof.
  intros X l i x H. rewrite upd_firstn_skipn by lia. rewrite skipn_app, length_firstn.
  replace (Nat.min i (length l)) with i by lia. rewrite Nat.sub_diag, skipn_all2 by (rewrite length_firstn; lia). reflexivity.
Qed.

Lemma hex_digits_0 : forall l, hex_digits l 0 = [].
Proof. reflexivity. Qed.
Lemma hex_digits_step : forall l x, (0 < x < 2^64)%Z ->
  hex_digits l x = hex_digits l (x / 16) ++ [Z.lor (znth XDIGITS (x mod 16)) l].
Proof.
  intros l x Hx. unfold hex_digits at 1. change 16%nat with (S 15). rewrite digits_aux_S.
  destruct (Z.eqb_spec x 0); [lia|]. rewrite digits_aux_acc. apply (f_equal2 (@app Z)); [|reflexivity]. unfold hex_digits. apply digits_aux_fuel; [lia|].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  change (16 * 16 ^ Z.of_nat 15)%Z with (2^64)%Z. lia.
Qed.
Lemma hex_digits_length : forall l x, (length (hex_digits l x) <= 16)%nat.
Proof. intros l x. unfold hex_digits. pose proof (digits_aux_length 16 16 (fun v => Z.lor (znth XDIGITS v) l) x []) as L. cbn [length Nat.add] in L. exact L. Qed.
Lemma hexchar_ok0 : forall n, (0 <= n < 0 + Z.of_nat 16)%Z -> ((48 <=? Z.lor (znth XDIGITS n) 0) && (Z.lor (znth XDIGITS n) 0 <? 103))%Z = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma hexchar_ok32 : forall n, (0 <= n < 0 + Z.of_nat 16)%Z -> ((48 <=? Z.lor (znth XDIGITS n) 32) && (Z.lor (znth XDIGITS n) 32 <? 103))%Z = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma hexchar_range : forall l v, (l = 0 \/ l = 32)%Z -> (0 <= v < 16)%Z -> (48 <= Z.lor (znth XDIGITS v) l < 103)%Z.
Proof.
  intros l v [-> | ->] Hv.
  - pose proof (hexchar_ok0 v ltac:(cbn; lia)) as E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - pose proof (hexchar_ok32 v ltac:(cbn; lia)) as E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.
Lemma hex_digits_range : forall l x, (l = 0 \/ l = 32)%Z -> Forall (fun c => 48 <= c < 103)%Z (hex_digits l x).
Proof.
  intros l x Hl. unfold hex_digits.
  assert (G : forall f y acc, Forall (fun c => 48 <= c < 103)%Z acc -> Forall (fun c => 48 <= c < 103)%Z (digits_aux f 16 (fun v => Z.lor (znth XDIGITS v) l) y acc)).
  { induction f as [|f IH]; intros y acc Ha; [exact Ha|]. rewrite digits_aux_S.
    destruct (Z.eqb_spec y 0); [exact Ha|]. apply IH. constructor; [|exact Ha]. apply hexchar_range; [exact Hl|]. pose proof (Z.mod_pos_bound y 16 ltac:(lia)). lia. }
  apply G. constructor.
Qed.

Lemma ift : forall (X : Type) (a b : X), (if true then a else b) = a.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC2"] "h01Xh11ah21bp;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0p10030p4p710R1p8P2p1003Np4p7210p8p1004?p4p7210P1p8p102Tnp6051000R2P0p8P2p101[ep4p710R0p8P2p102PBp4p710R3p8P2p100:lp4p710R4p8P2p1004kp4p710R5p8P2p1006Gp4p710R2p8p102V=p6051000R6P0p8P6P3p8P6P4p8P6P5p8P6P2p8P5P1p8p100A_p4p7210P1p8P2P1p8p1006fp4p7210P1p8g00@ij20Tp200f0f1R1f2/01W2W1W0o"). Qed.
Lemma iff : forall (X : Type) (a b : X), (if false then a else b) = b.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC2"] "h01Xh11ah21bp;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0p10030p4p710R1p8P2p1003Np4p7210p8p1004?p4p7210P1p8p102Tnp6051000R2P0p8P2p101[ep4p710R0p8P2p102PBp4p710R3p8P2p100:lp4p710R4p8P2p1004kp4p710R5p8P2p1006Gp4p710R2p8p102V=p6051000R6P0p8P6P3p8P6P4p8P6P5p8P6P2p8P5P1p8p100A_p4p7210P1p8P2P1p8p1006fp4p7210P1p8g00@ij20Tp200f0R1f1f2/01W2W1W0o"). Qed.

Lemma lo64_range : forall y, (0 <= lo64 y < 2^64)%Z.
Proof. intros y. unfold lo64. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall y, (0 <= hi64 y < 2^64)%Z.
Proof. intros y. unfold hi64. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma lo64_hi64 : forall y, (0 <= y < 2^128)%Z -> (lo64 y + 2^64 * hi64 y)%Z = y.
Proof.
  intros y Hy. unfold lo64, hi64. rewrite !wrap64_mod. rewrite Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small (y / 2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; change (2^64 * 2^64)%Z with (2^128)%Z; lia]).
  pose proof (Z.div_mod y (2^64) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Section Ranges128.
  Local Open Scope Z_scope.
  Lemma mk128_range : forall hi lo, 0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= mk128 hi lo < 2^128.
  Proof.
    intros hi lo Hh Hl. unfold mk128. apply Bytes.lor_lt_pow2; [|lia].
    rewrite Z.shiftl_mul_pow2 by lia. change (2^128) with (2^64 * 2^64). nia.
  Qed.
  Lemma shr64_range64 : forall a k, 0 <= a < 2^64 -> 0 <= k -> 0 <= Z.shiftr a k < 2^64.
  Proof. intros. apply PropExec.Z_shiftr_range; lia. Qed.
  Lemma sra63_range : forall x, 0 <= sra63 x < 2^64.
  Proof. intros x. unfold sra63, ONES64. destruct (is_neg64 x); cbn; lia. Qed.
  Lemma f128_of_d_range : forall d, 0 <= f128_of_d d < 2^128.
  Proof.
    intros d. unfold f128_of_d.
    set (aRep := lo64 d). set (aExp := Z.shiftr (shl64 aRep 1) 53). set (aSig := Z.shiftr (shl64 aRep 12) 12).
    set (signHi := shl64 (Z.shiftr aRep 63) 63).
    assert (RaRep : 0 <= aRep < 2^64) by (subst aRep; unfold lo64; apply SoftFloat.wrap64_range).
    assert (RaSig : 0 <= aSig < 2^64) by (subst aSig; apply shr64_range64; [apply SoftFloat.wrap64_range | lia]).
    assert (RsignHi : 0 <= signHi < 2^64) by (subst signHi; apply SoftFloat.wrap64_range).
    assert (RINF : 0 <= INF_HI < 2^64) by (unfold INF_HI; lia).
    assert (RIMP : 0 <= IMPLICIT_HI < 2^64) by (unfold IMPLICIT_HI; lia).
    assert (G : forall e s, 0 <= e < 2^64 -> 0 <= s < 2^64 -> 0 <= Z.lor (Z.lor e s) signHi < 2^64).
    { intros e s He Hs. apply PropExec.Z_lor_range; [apply PropExec.Z_lor_range|]; lia. }
    cbv zeta.
    destruct (negb (aExp =? 0)).
    - destruct (negb (aExp =? 2047)); apply mk128_range; try apply SoftFloat.wrap64_range;
        apply G; try apply SoftFloat.wrap64_range; try (apply shr64_range64; lia). exact RINF.
    - destruct (aSig =? 0).
      + apply mk128_range; [|lia]. apply G; [apply SoftFloat.wrap64_range | lia].
      + apply mk128_range.
        * apply G; [apply SoftFloat.wrap64_range|]. apply PropExec.Z_lxor_range; [|exact RIMP].
          destruct (negb (is_neg64 _)); [apply SoftFloat.wrap64_range|]. apply shr64_range64; [|apply Z.land_nonneg; lia].
          apply shr64_range64; lia.
        * apply Bytes.land_lt_pow2; [apply sra63_range|].
          pose proof (SoftFloat.wrap64_range (Z.shiftl aSig (Z.land (add64 (clz64_mirror aSig) 49) 63))). unfold shl64. lia.
  Qed.
End Ranges128.

(* [comment removed for export] *)
Lemma sx32_int : forall (slot : word) i, (-2^31 <= i < 2^31)%Z -> (bv_unsigned slot mod 2^32 = i mod 2^32)%Z ->
  sx32 slot = Z_to_bv 64 (i mod 2^64).
Proof.
  intros slot i Hi E. unfold sx32. rewrite Z_to_bv_mod64. apply Z_to_bv_eqm. f_equal.
  change (2^32)%Z with 4294967296%Z in E.
  rewrite swrap32_eq. rewrite <- Zplus_mod_idemp_l, E, Zplus_mod_idemp_l.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma zx32_uint : forall (slot : word) u, (bv_unsigned slot mod 2^32 = u)%Z -> zx32 slot = Z_to_bv 64 u.
Proof. intros slot u E. unfold zx32. rewrite E. reflexivity. Qed.

Lemma land_land_same : forall a m, Z.land (Z.land a m) m = Z.land a m.
Proof. intros. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. Qed.

(* [comment removed for export] *)
Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma cb8_c8_in : forall m A pre post bs, rw_cells bsegs m A (pre ++ CB 8 bs :: post) -> rw_cells bsegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
End CANSEC2.
Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let rec go pre l := lazymatch l with
     | CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
     | ?c :: ?l' => go constr:(pre ++ [c]) l'
     | [] => idtac end in
  go constr:(@nil cell) cs end.

(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
Lemma printf_loop_S : forall {St : Type} (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z) fuel s args cnt,
  printf_loop OUT OUTFP (S fuel) s args cnt =
      match s with
      | [] => munr
      | c :: _ =>
        if (c =? 0)%Z then mret cnt else
        let lit := lit_run s in
        let l := zlength lit in
        let s1 := skipn (Datatypes.length lit) s in
        match s1 with
        | [] => munr
        | c1 :: s2 =>
          if ((c1 =? 37) && match s2 with [] => true | c2 :: _ => (c2 =? 37) end)%Z
          then munr
          else if (0 <? l)%Z then
            (if (INT_MAX - cnt <? l)%Z then munr
             else OUT lit ;;; printf_loop OUT OUTFP fuel s1 args (cnt + l))
          else
            match parse_dir s2, args with
            | Some (d, s3), a :: args' =>
                OUT [] ;;;
                cnt' <- conv OUT OUTFP cnt d a ;;
                printf_loop OUT OUTFP fuel s3 args' cnt'
            | _, _ => munr
            end
        end
      end.
Proof. reflexivity. Qed.
Lemma fp_calls_S : forall fuel s args,
  fp_calls (S fuel) s args =
    match s with
    | [] => []
    | c :: _ =>
      if (c =? 0)%Z then [] else
      let lit := lit_run s in
      let s1 := skipn (Datatypes.length lit) s in
      if (0 <? zlength lit)%Z then fp_calls fuel s1 args
      else match s1 with
           | _ :: s2 =>
             match parse_dir s2, args with
             | Some (d, s3), a :: args' =>
                 match a with
                 | PA_g dd =>
                     let fl := (if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD))%Z in
                     (f128_of_d dd, d_w d, d_p d, fl, d_t d) :: fp_calls fuel s3 args'
                 | _ => fp_calls fuel s3 args'
                 end
             | _, _ => []
             end
           | _ => []
           end
    end.
Proof. reflexivity. Qed.

Lemma In_firstn_w : forall {A} (x : A) n l, In x (firstn n l) -> In x l.
Proof. intros A x n l. revert n. induction l as [|y l IH]; intros [|n] H; cbn in H; try contradiction. destruct H as [->|H]; [left; reflexivity | right; eapply IH; exact H]. Qed.
Lemma In_skipn_w : forall {A} (x : A) n l, In x (skipn n l) -> In x l.
Proof. intros A x n l. revert n. induction l as [|y l IH]; intros [|n] H; cbn in H; try contradiction; [exact H|]. right. eapply IH. exact H. Qed.
Lemma Forall_sub : forall {A} (P : A -> Prop) (l : list A) n k, Forall P l -> Forall P (firstn n (skipn k l)).
Proof.
  intros A P l n k H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall P l) H).
  eapply In_skipn_w. eapply In_firstn_w. exact Hx.
Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. rewrite firstn_map. reflexivity. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. rewrite skipn_map. reflexivity. Qed.
Lemma bytes_at_sub : forall m A (l : list byte) k n,
  bytes_at bsegs m A l -> (k <= length l)%nat ->
  bytes_at bsegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m A l k n H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H]. rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma parse_dir_conv_type : forall s d rest, parse_dir s = Some (d, rest) -> conv_type (d_t d) = Some (d_ty d).
Proof.
  intros s d rest PD. destruct (parse_dir_shape _ _ _ PD) as (_ & SH). destruct (parse_flags s 0) as [fl0 s1'].
  destruct SH as (_ & c1 & s1b & _ & _ & s2 & _ & c2 & s2b & _ & PX).
  destruct PX as [(_ & _ & _ & Ht & _ & CT) | (_ & _ & c3 & s3b & _ & _ & s3 & _ & _ & CT)]; [rewrite Ht|]; exact CT.
Qed.

Lemma parse_dir_xp : forall s d rest, parse_dir s = Some (d, rest) ->
  ((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z.
Proof.
  intros s d rest PD. destruct (parse_dir_shape _ _ _ PD) as (_ & SH). destruct (parse_flags s 0) as [fl0 s1'].
  destruct SH as (_ & c1 & s1b & _ & _ & s2 & _ & c2 & s2b & _ & PX).
  destruct PX as [(_ & Hp & Hx & _) | (_ & Hx & c3 & s3b & _ & _ & s3 & G & _)].
  - left. split; [exact Hx | exact Hp].
  - right. split; [exact Hx|]. eapply getint_some_range; [|exact G]. unfold INT_MAX. lia.
Qed.

(* [comment removed for export] *)
Lemma c8_read4 : forall m A pre (w : word) post a,
  rw_cells bsegs m A (pre ++ C8 w :: post) -> a = wa (A + Z.of_nat (cells_size pre)) ->
  ov_read_bytes bsegs m a 4 = Some (le4 w).
Proof.
  intros m A pre w post a H ->.
  apply (proj1 (rw_cells_app bsegs m A pre (C8 w :: post))) in H. destruct H as [_ H].
  pose proof (rw_cells_bytes_at' _ _ _ _ H) as Hb. cbn [cells_bytes cbytes] in Hb.
  pose proof (bytes_at_ov_read bsegs m _ _ 0 4 Hb) as R. rewrite Z.add_0_r in R.
  rewrite R. 2:{ cbn [skipn]. rewrite length_app, length_le8. lia. }
  change (skipn 0 (le8 w ++ cells_bytes post)) with (le8 w ++ cells_bytes post).
  rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r, firstn4_le8. reflexivity.
Qed.

Lemma bytes_at_nil : forall m a, (0 <= a)%Z -> (a <= 2^64)%Z -> bytes_at bsegs m a [].
Proof. intros m a H0 H1. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Local Ltac acc_hint ::= lazymatch goal with |- acc_in _ (wa ?e, ?n) => change (wa e) with (Z_to_bv 64 e : word); solve_acc1 end.
  Local Ltac acc_enrich ::=
    repeat match goal with
    | H : nth_error ?l ?k = Some ?x |- _ =>
        lazymatch goal with _ : (k < length l)%nat |- _ => fail | _ => pose proof (nth_error_some_bound l k x H) end
    end;
    rewrite ?u32s_length, ?u64s_length, ?length_app, ?repeat_length, ?zb_length in *; cbn [length] in *; unfold zlength in *.
  Context {St : Type}.
  Variables (Fp B BS : Z) (RB : region) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS RB SINK TOPOK OUT.
  Hypothesis HSTRN : strnlen_a_stmt.
  (* [comment removed for export] *)
  Variables (RNG : footprint) (rstk rfmt : region).
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 2^47)%Z.            (* [comment removed for export] *)
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 724992)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((737200 <= Fp /\ Fp + 232 <= 762616) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((6345432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  (* [comment removed for export] *)
  Hypothesis KH : (KHIGH <= lo)%Z.
  Hypothesis RSK : (r_lo rstk <= lo /\ q <= r_hi rstk)%Z.
  Hypothesis RFM : inreg rfmt A (zlength fmt).
  Hypothesis RPF : inreg rfmt 68436 9.            (* [comment removed for export] *)
  Hypothesis RBI : inreg RB B BS.
  Hypothesis RG_stk : rng RNG lo (q - lo).
  Hypothesis RG_img : rng_aimg RNG.
  Hypothesis RG_ap : rng RNG AP 8.
  Hypothesis RG_va : rng RNG VA (8 * zlength slots).
  Hypothesis RG_F : rng RNG Fp 232.
  Hypothesis RG_B : rng RNG B BS.
  Hypothesis RG_fmt : rng RNG A (zlength fmt).
  Hypothesis RR_stk : rrng RNG rstk.
  Hypothesis RR_fmt : rrng RNG rfmt.
  Hypothesis RR_B : rrng RNG RB.
  Hypothesis ENV0 : ashenv m0.
  Hypothesis RC_stk : rclean m0 rstk.
  Hypothesis RC_fmt : rclean m0 rfmt.
  Hypothesis RC_B : rclean m0 RB.

  Notation sfx := (sfx fmt).
  Definition ctx_all : unit :=
    let _ := (RB, RNG, rstk, rfmt, ra, q, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc0, m0,
              lo, canary, A, fmt, AP, VA, slots, nla, nlt) in tt.

  (* [comment removed for export] *)
  Definition W : list (Z * Z) := [(lo, q); (AP, AP + 8); (Fp, Fp + 232); (B, B + BS)]%Z.
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).

  (* [comment removed for export] *)
  Lemma appB : (B + BS <= KLOW \/ KHIGH <= B)%Z.
  Proof.
    clear - RC_B RBI. destruct RC_B as [SH LT]. pose proof (shclean_app_blk _ _ _ _ _ SH) as [_ AB].
    unfold inreg in RBI. unfold KLOW, KHIGH, KEND in *. lia.
  Qed.
  Lemma appW_W : appW W.
  Proof using Fp B BS RB q m0 lo AP VA LO SEP_F HAP KH RBI RC_B. clear SFR SFL TOK HOUT HSTRN HF GLO QHI TQ FRM0 HA SEP_B HVA A0 VAHI BS0 RSK RFM RPF RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt.
    pose proof appB as APPB.
    clear - LO SEP_F HAP KH APPB. unfold W, PC_DEPTH, GLOBALS_TOP in *. unfold appW.
    repeat (apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH in *; lia|]). apply Forall_nil.
  Qed.
  Lemma ashsafe_W : ashsafe W.
  Proof using Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP KH. clear SFR SFL TOK HOUT HSTRN HF QHI TQ FRM0 HA HVA A0 VAHI BS0 RSK RFM RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    clear - LO GLO SEP_F SEP_B HAP KH. unfold W, PC_DEPTH, GLOBALS_TOP in *.
    unfold ashsafe; cbn [disjoint_from]; unfold KHIGH in *. repeat split; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma env_now : forall m, munch W m0 m -> wmono bsegs m0 m -> ashenv m.
  Proof using Fp B BS q m0 lo AP VA LO GLO SEP_F SEP_B HAP KH ENV0. clear SFR SFL TOK HOUT HSTRN HF QHI TQ FRM0 HA HVA A0 VAHI BS0 RSK RFM RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B RC_stk RC_fmt RC_B. intros m MU WM. exact (ashenv_transport _ _ _ ENV0 MU WM ashsafe_W). Qed.
  Lemma rc_now : forall r m, rclean m0 r -> munch W m0 m -> wmono bsegs m0 m -> rclean m r.
  Proof using Fp B BS RB q m0 lo AP VA LO SEP_F HAP KH RBI RC_B. clear SFR SFL TOK HOUT HSTRN HF GLO QHI TQ FRM0 HA SEP_B HVA A0 VAHI BS0 RSK RFM RPF RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt. intros r m RC MU WM. exact (rclean_transport _ _ _ _ RC MU WM appW_W). Qed.
  Notation FPv := (Z_to_bv 64 Fp).

  Definition Fokd (F1 F2 : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k.
  Definition Fok (Ft : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k.
  Lemma Fok_refl : Fok F.
Proof using F.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h02_Hh11kp;1p;2p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0p10030p4p710R1p8P2p1003NR2p4p7210p8p1004?p4p7210P1p8p102Tnp6051000R3P0p8P3p101[ep4p710R0p8P3p102PBp4p710R4p8P3p100:lp4p710R5p8P3p1004kp4p710R6p8P3p1006Gp4p710R3p8p102V=p6051000R7P0p8P7P4p8P7P5p8P7P6p8P7P3p8p103RUp6051000R7P2p4p710p8P7p103Sbp4p710p8P6P1p8p103]7p6051000R6p103_ip4p710R7p8P6P0p8P6P1p8P6p101[Cp4p710R2p8p103^Bp6051000R5P7p8P5P0p8P5P2p8p103`@p6051001R2P0p8P2p100kMp4p710p8P2P6p8P2P5p8P2p103_Lp4p710p8p100A_p4p7210P1p8P3P1p8p1006fp4p7210P1p8g007ej10Tg00U[j1:Tg008Jj11Tg008hj12Tg027Dj29Tg014bj18Tg00;Lj37Tg00MCj14Tg04K8j25Tg00@ij26Tg04Kbj13Tg00<D#0R1#:R3#1R2#2g00;ff0,92%03#837#4%01#0#0#0#0#1#2p,1FR1f1'5'6W0W1%31eo"). Qed.
  Lemma Fok_trans : forall F1 F2, Fok F1 -> (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
  Proof using F. clear SFR SFL TOK HOUT HSTRN HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 KH RSK RFM RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B. intros F1 F2 H1 H2 k Hk. rewrite (H2 k Hk). apply H1. exact Hk. Qed.

  Definition POST : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ munch W m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m'
      /\ frm0 fc' /\ Fok Ft
      /\ stk bsegs m' lo q
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ rw_cells bsegs m' AP [C8 apv]
      /\ (0 <= r <= INT_MAX)%Z.

  (* [comment removed for export] *)
  Definition hi_cells : list cell :=
    [C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  (* [comment removed for export] *)
  Definition lo_cells (pfx s2s za pl plp l10n alo ahi : word) (j128 : list byte) : list cell :=
    [C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
     C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364);
     C8 alo; C8 ahi; CB 24 j128].

  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) : Prop :=
    mem_inv bsegs m /\ munch W m0 m /\ wmono bsegs m0 m
    /\ rw_cells bsegs m (q + -112) hi_cells
    /\ stk bsegs m lo (q + -544)
    /\ bytes_at bsegs m A (zb fmt)
    /\ va_area m VA slots
    /\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells bsegs m ssp_guard [C8 canary].
  (* [comment removed for export] *)
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  (* [comment removed for export] *)
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.

  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
    try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
         lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
    try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
         lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
    unfold zlength in *; hush.
  Ltac hyp :=
    lazymatch goal with
    | |- rw_cells _ ?m ?A ?cs =>
        match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
    | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
    end.
  Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.

  (* [comment removed for export] *)
  Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).

  Lemma u8_lit : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
  Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
  Lemma fmt_rng : forall i, (0 <= i < zlength fmt)%Z -> (0 <= znth fmt i < 256)%Z.
  Proof using fmt HF. clear SFR SFL TOK HOUT HSTRN LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 KH RSK RFM RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B. intros i Hi. exact (Forall_znth _ fmt i HF Hi). Qed.
  (* [comment removed for export] *)
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).

  (* [comment removed for export] *)
  Ltac rd_fmt idx :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.

  (* [comment removed for export] *)
  Lemma states0_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m 0x22428 (zb STATES0).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h07__arithh14__ffh28__varmaph35__with42MIh51mp;1p;2p;4p;3p;8p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0p10030p4p710R1p8P2p1003NR2p4p7210p8p1004?p4p7210P1p8p102Tnp6051000R3P0p8P3p101[ep4p710R0p8P3p102PBp4p710R4p8P3g00:lR5p4p710R6p8P3p1004kp4p710R7p8P3p1006Gp4p710R3p8p102V=p6051000R8P0p8P8P4p8P8P6p8P8P7p8P8P3p8p103RUp6051000R8P2p4p710R2p8P8p103Sbp4p710R8p8P7P1p8p103]7p6051000R7p103_ip4p710R6p8P7P0p8P7P1p8P7p101[Cp4p710R4p8p103^Bp6051000R9P6p8P9P0p8P9P4p8p103`@p6051001R4P0p8P4p100kMp4p710p8P4P7p8P4P9p8P4p103_Lp4p710p8p104Lep6051002R4P2p8P4P8p8p100A_p4p7210P1p8P3P1p8p1006fp4p7210P1p8g007ej10Tg008Jj16Tg008hj17Tg00>cj1QTg04Pgj2OTg00U[j11Tg014bj13Tg00:1j1ATg00FJj1@Tg007Ej1?Tg01DFj1=Tg00GHj1<Tg00Gfj1PTg00I4j24Tg00IWj4;Tg00Jdj2NTg00@ij2KTg00KFj2ETg00;Lj39Tg00L2j3DTg00LQj4CTg00B<j25Tg01Ddj3BTg01fLj3FTg00e7j28Tg01eOj2GTP5j2HTg00O;j1ITg04Q[j3JTg04RTj4>Tg04SSj8LTg00X5j7MTf0R5#0#0p=2f1R1g00[mg00\LR3P3g00\lR3P5g00]LFMp=:g00<DR8#0R4#2R2#0#2R9#6R7#7%62#7R2#Q[g00jXR0/O5P0P1%08#2#1#2#1#2#2#1#0#1#0#2#3R6g04TK#AR:P5g00_[R;#@R<%?;R;g00;fR=#=R>%<=R?%P=R@P=g00[ORA,4=g00`nRB14=6RCC;':1N@3R3P5f2RDg00_;REg00aURF'KRG1E5D=9EFdAD=A1CCR1b1b2b315A6P5b0P<P;P>P?P=%18#1#0#1#0#3R8,4=9B=CPB%34R4,4==F=7C;,:@P3P1b1b2b31868%39,G4R4'5P5b01H2:#I,86/54eP0P:P6PGAJ06:=9EFdC>GLW4W5o"). Qed.
  (* [comment removed for export] *)
  Lemma states0_read : forall m t ty, mem_inv bsegs m -> conv_type t = Some ty ->
    ov_read_bytes bsegs m (wa (t + 140328 + -65)) 1 = Some [Z_to_bv 8 ty].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h04__x1h17__arithh24__ffh38__varmaph45__with52tyh62CTh72MIh81Rh91mh:1tp;1p;2p;3p;4p;8p;6p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0g002TR1p4p710p8P0p10030p4p710R3p8P2p1003NR2p4p7210p8p1004?p4p7210P3p8p102Tnp6051000R4P0p8P4p101[ep4p710R0p8P4p102PBp4p710R5p8P4p100:lp4p710R6p8P4p1004kp4p710R7p8P4p1006Gp4p710R4p8p102V=p6051000R8P0p8P8P5p8P8P6p8P8P7p8P8P4p8p103RUp6051000R8P2p4p710R2p8P8p103Sbp4p710R8p8P7P3p8p103]7p6051000R7p103_ip4p710R6p8P7P0p8P7P3p8P7p101[Cp4p710R5p8p103^Bp6051000R9P6p8P9P0p8P9P5p8p103`@p6051001R5P0p8P5p100kMp4p710p8P5P7p8P5P9p8P5p103_Lp4p710p8p104Lep6051002R5P2p8P5P8p8p100A_p4p7210P3p8P4P3p8p1006fp4p7210P3p8g007ej10Tg008Jj1?Tg008hj1ETg00>cj1;Tg04Pgj2XTg03hmj1UTg00?cj2BTg00;Lj37Tg04UKj3LTg00U[j11Tg014bj18Tg00B<j25Tg00Clj2>Tg01AAj2=Tg00Vdj2YTg007Ej1FTg00e7j22Tg01B^j1VTg00eTR3j1DTg00R@j1TTg00fCj4STg009Kj2QTg00FJj1ATg00T]j3PTg04VSj2OTg00Fjj2NTg00GHj1MTg00Gfj1KTg00I4j24Tg00HQj2JTg00JBj1ITg01EGj3HTg00IWj4:Tg00Yaj8GTg00Jdj2RTg00@ij2CTg00KFj2bTg00L2j3aTg00LQj4`Tg00CPj2_Tg01Ddj3<Tg01Ffj8^Tg04W`j8ZTg04Xkj3[TP1j6\Tg00X5j7WTg00Y=j7]Tf0R1#0#0p=3g00;fR4f1R8g00`nP1C:p=9P8g00[mR5g00\LR2P2g00\lR9P1g00]LFWp=6f2R7P5P2P2P9P8P1F]p=@g00<DR0#0#3R6#3R:#0#?#ER;%?6R6#ER<#;[g00jXR=/X7%;4%U71B4837f3R>?L71%1:R:#8R?/5>%10#1R@#1#0#1#0#8RA,5>'>P4g04TKRBf4RC/=?RD'Y%F<RE#;P=f6f5R=%00#3#1#3#1#3#3#1#0#1#0#3#8RF'2%V:R:'2#Dg00bP#TCS1Q61%A<5P<,BE37X54P=PFPBPD12CF/2:RB#D1O=7g00_[RE#AR<%FERE1N48R6%M4RG%K4RHP5P2P2P9144?R51J40R0'9,6H144A,90,6H5@H%I2g00[OR2,44AH405R5'9,6HP4P5g00`G%0@#1#0#8R@,44C:,6H5@HGG1RH9R9P1P7g00_;RIg00aURJ'C1b17=7IJdAa428C`RJb2b3b4X0415?1151A'>1=8?RA,521_A@'>[^04P1P=P8O2b1P4P;P3P3PB12FDP;\4/C3P<PEP6PGP4144FRG9<40144:5<4g00c[A<4G5C:,6HP9PJb2b3b4X04121F/2:1=1?,2F574^04P1P=O1b1G^GZP>A[C>8E\b8W6W7X54X:4W9o"). Qed.

  (* [comment removed for export] *)
  Definition PFXSTR : list Z := [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z.
  Lemma pfx_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m 68436 (zb PFXSTR).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h07__arithh14__ffh28__varmaph35__with42MIh51mp;1p;2p;4p;3p;8p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0p10030p4p710R1p8P2p1003NR2p4p7210p8p1004?p4p7210P1p8p102Tnp6051000R3P0p8P3p101[ep4p710R0p8P3p102PBp4p710R4p8P3g00:lR5p4p710R6p8P3p1004kp4p710R7p8P3p1006Gp4p710R3p8p102V=p6051000R8P0p8P8P4p8P8P6p8P8P7p8P8P3p8p103RUp6051000R8P2p4p710R2p8P8p103Sbp4p710R8p8P7P1p8p103]7p6051000R7p103_ip4p710R6p8P7P0p8P7P1p8P7p101[Cp4p710R4p8p103^Bp6051000R9P6p8P9P0p8P9P4p8p103`@p6051001R4P0p8P4p100kMp4p710p8P4P7p8P4P9p8P4p103_Lp4p710p8p104Lep6051002R4P2p8P4P8p8p100A_p4p7210P1p8P3P1p8p1006fp4p7210P1p8g007ej10Tg008Jj1:Tg008hj16Tg00>cj1>Tg04Pgj2PTg00U[j11Tg014bj13Tg00:1j1BTg00FJj1@Tg007Ej1?Tg01DFj1=Tg00GHj1<Tg00Gfj1;Tg00I4j22Tg00IWj49Tg00Jdj2OTg00@ij2NTg00KFj2MTg00;Lj37Tg00L2j3DTg00LQj4CTg00B<j24Tg01Ddj3ATg01fLj3ETg00e7j28Tg01eOj2FTP5j2GTg00O;j1HTg04Q[j3ITg04RTj4JTg04SSj8KTg00X5j7LTf1R5g00[mg00\LR1P1g00\lR1f0R3g00]LFLp=5g00<D#0R8#0R4#0R2#0R9#0#0R7#:R0#6%:2#6R2#>[g00jXR6/P3P6P5%19#0#1#1#0#1#0#1#0#1#0#0#3R9g04Z0#BR:P3g00_[R;#@R<%?;R;g00;fR=#=R>%<=R?%;=R@P=g00[ORA,2=g00`nRB12=9RCC9'51O@1R1P3f2RDg00_;REg00aURF'NRG1M3D=7EFdAD=A5CCR5b1b2b314A9P3b0P<P;P>P?P=%14#3R4,2=9A=CPB%38R8,2==E=0C9,5@P1P5b1b2b31894%37,F8R8'4P3b01G2:#H,89/48eP6P:P9PGAI69:=7EFdCJGKW4W5o"). Qed.
  Lemma pfx_sub : forall m k n, mem_inv bsegs m -> (k + n <= 9)%nat ->
    bytes_at bsegs m (68436 + Z.of_nat k) (zb (firstn n (skipn k PFXSTR))).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h04__x1h14__x2h21lh32Hkh43Hk0h52MIh67__arithh74__ffh88__varmaph95__with:4cstrh;5cstr0h<1kh=1mh>1np;1p;2p;3p;4p;7p;6p;<p;Bp;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0g0030R1p4p710R3p8P2p1003NR2p4p7210p8p1004?p4p7210P3p8p102Tnp6051000R4P0p8P4g01[eR0p4p710R5p8P4p102PBp4p710R6p8P4g00:lR7p4p710R8p8P4p1004kp4p710R9p8P4p1006Gp4p710R4p8p102V=p6051000R:P5p8P:P6p8P:P8p8P:P9p8P:P4p8p103RUp6051000R:P2p4p710R2p8P:p103Sbp4p710R:p8P9P3p8p103]7p6051000R9p103_ip4p710R8p8P9P5p8P9P3p8P9p101[Cp4p710R6p8p103^Bp6051000R;P8p8P;P5p8P;P6p8p103`@p6051001R6P5p8P6p100kMp4p710p8P6P9p8P6P;p8P6p103_Lp4p710p8p104Lep6051002R6P2p8P6P:p8p100A_p4p7210P3p8P4P3p8p1006fp4p7210P3p8g007ej10Tg008Jj1CTg008hj1ATg00>cj1LTg04Pgj2hTg015@j2GTg00R@j11Tg00N>R3j26Tg007Ej1FTg018Dj3?Tg00:1j19TP0j3;Tg00U[j12Tg014bj1HTg00O;R0j14Tg00e7R4j2:Tg00dBj4ETg04[6j2YTg00B<R:j23Tg00@ij25Tg00P8j4VTg00P_j1UTg00R_j28Tg00SHj3@Tg00T1j2STg00FJj1RTg00T]j3QTg00Fjj2PTg01DFj1OTg00U=j4KTg00GHj1MTg00Gfj1NTg00I4j2=Tg00HQj2>Tg00JBj1JTg01Ddj3TTg00Jdj2gTg00KFj2fTg00;Lj3eTg00L2j3dTg00LQj4bTg00m?j4^TP7j2]Tg04\?j7\Tg04]Kj2[TP1j6DTg04^Sj2ZTg00Zjl<_Tg01K2lB`Tg00IWj4aTg00X5j7XTg00Yaj8cTg00<iR1g00;fR7P3P0P:g00^Yf5R:f4R3f3R6f2R2f1R;f0R9M<_p=BP1P1P1P7P7P7g01HHP0P0P0P4g01L<P:P3P6P2P;P9MB`p=WP7P;g00`nP9Cap=<P;g00[mR4g00\LR0P0g00\lR5P9g00]LFXp=7P6P4P0P0P5P2P;P9Gcp=Ig00<DR4#0R8#0R<#0R=#0R>#0#0#C#A%C=#AR=#L[g00jXR?/h21G2;g00bPR@#1RA#1RB#1#1#1#1#1#1#1RC'6%F=RDg04Z0RE9?76RF#9RG9;=2P?P:%2>#0#2#2#0#2#0#2#0#2#0#0#HR>%43RH':RIP9CEX2DPD%9ERJ9?=6P?P:PIA;=69CEX2DP3P>PJP6P21Y3;166C%46R>%2<#HR<'3P6P>157>RDPCP<157<RIEB1G62R:/6C%42R?,:>RK/3<RLP:PKP6P>PDP2P?157?EWPCP<PIEBP9CVPL%U3R3g00[ORL/3HRHP3PHg00_[RH187B187A187@5@75@7g00bo'S%RH3Q%FHP71P72P;%O7CK%M7%N7RH1=7L1>78R8'<,7H%J0R0PH1>74R4=T781=7<R8'<,7HP01<48,7HCICI1gH5P9P2g00_;RHg00aUR5'51f92=eH5dAd7L;Cbb7b8b9X07X1713L;1:;2/3<132<[[^07^17P9f6#4f7#4P;P6O4b6b;b:b4C^1]=J,66eF\PG1[6EEDA;72F#91Z2FEDW3W5X>1X<1W=o"). Qed.
  Lemma xdigits_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m 140792 (zb XDIGITS).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h07__arithh14__ffh28__varmaph35__with42MIh51mp;1p;2p;4p;3p;8p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0p10030p4p710R1p8P2p1003NR2p4p7210p8p1004?p4p7210P1p8p102Tnp6051000R3P0p8P3p101[ep4p710R0p8P3p102PBp4p710R4p8P3g00:lR5p4p710R6p8P3p1004kp4p710R7p8P3p1006Gp4p710R3p8p102V=p6051000R8P0p8P8P4p8P8P6p8P8P7p8P8P3p8p103RUp6051000R8P2p4p710R2p8P8p103Sbp4p710R8p8P7P1p8p103]7p6051000R7p103_ip4p710R6p8P7P0p8P7P1p8P7p101[Cp4p710R4p8p103^Bp6051000R9P6p8P9P0p8P9P4p8p103`@p6051001R4P0p8P4p100kMp4p710p8P4P7p8P4P9p8P4p103_Lp4p710p8p104Lep6051002R4P2p8P4P8p8p100A_p4p7210P1p8P3P1p8p1006fp4p7210P1p8g007ej10Tg008Jj1:Tg008hj16Tg00>cj1>Tg04Pgj2PTg00U[j11Tg014bj13Tg00:1j1BTg00FJj1@Tg007Ej1?Tg01DFj1=Tg00GHj1<Tg00Gfj1;Tg00I4j22Tg00IWj49Tg00Jdj2OTg00@ij2NTg00KFj2MTg00;Lj37Tg00L2j3DTg00LQj4CTg00B<j24Tg01Ddj3ATg01fLj3ETg00e7j28Tg01eOj2FTP5j2GTg00O;j1HTg04Q[j3ITg04RTj4JTg04SSj8KTg00X5j7LTf1R5g00[mg00\LR1P1g00\lR1f0R3g00]LFLp=5g00<DR8#0R4#0#0R2#0R9#0#0R7#:R0#6%:2#6R2#>[g00jXR6/P3P6P5%08#0#0#1#0#0#1#0#1#1#1#1#1#1#0#0#0#3R8g02XL#BR:P3g00_[R;#@R<%?;R;g00;fR=#=R>%<=R?%;=R@P=g00[ORA,2=g00`nRB12=8RCC9'51O@1R1P3f2RDg00_;REg00aURF'NRG1M3D=7EFdAD=A5CCR5b1b2b314A8P3b0P<P;P>P?P=%39R9,2=9A=CPB%34R4,2==E=0C9,5@P1P5b1b2b31889%37,F4R4'4P3b01G2:#H,88/44eP6P:P8PGAI68:=7EFdCJGKW4W5o"). Qed.
  Lemma xdigits_read : forall m v, mem_inv bsegs m -> (0 <= v < 16)%Z ->
    ov_read_bytes bsegs m (wa (140792 + v)) 1 = Some [Z_to_bv 8 (znth XDIGITS v)].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h04__x1h12Hvh22MIh37__arithh44__ffh58__varmaph65__with71mh81vp;1p;2p;4p;7p;8p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0p10030p4p710R1p8P2p1003NR2p4p7210p8p1004?p4p7210P1p8p102Tnp6051000R3P0p8P3p101[ep4p710R0p8P3p102PBp4p710R4p8P3p100:lp4p710R5p8P3p1004kp4p710R6p8P3p1006Gp4p710R3p8p102V=p6051000R7P0p8P7P4p8P7P5p8P7P6p8P7P3p8p103RUp6051000R7P2p4p710R2p8P7p103Sbp4p710R7p8P6P1p8p103]7p6051000R6p103_ip4p710R5p8P6P0p8P6P1p8P6p101[Cp4p710R4p8p103^Bp6051000R8P5p8P8P0p8P8P4p8p103`@p6051001R4P0p8P4p100kMp4p710p8P4P6p8P4P8p8P4p103_Lp4p710p8p104Lep6051002R4P2p8P4P7p8p100A_p4p7210P1p8P3P1p8p1006fp4p7210P1p8g007ej11Tg008Jj18Tg008hj1<Tg00>cj1QTg04Pgj2LTg00B<j26Tg014bj17Tg00CPj25Tg00Clj2:Tg00U[j10Tg00e7j2>Tg00eTj1=Tg04_\j2PTg00FJj1OTg007Ej1NTg00Fjj2KTg00GHj1HTg00Gfj1GTg00I4j29Tg00HQj2ETg00IWj44Tg00Y=j7DTg00JBj1CTg00Yaj8BTg00Jdj2FTg00@ij23Tg00KFj2ATg00;Lj3ITg00L2j3JTg00LQj4@Tg04W`j8?Tg00X5j7MTf0R1#1#1p=2f1R3g00[mR7g00\LR4P4g00\lR2P1g00]LFMp=;g00<DR8#1#2R6#1R0#2#8#<R5%86#<#Q[g00;fR6g00jX/L3g00[OR9/63%70R0,53':R:f3R;%18#2#0#2#0#1#0#0#0#0#0#0#1#2#7R<g02XLf2R=1><=#=R<1P;3g00_[R>#O%N>1K63%H6%G6R>P7P4P4P2P>P7P4P4P2P61969g00`n1E68R8C4,;>P6P8g00`G1960C4,;>FDR8%C4P8GB1F>2P1P=g00_;R>g00aUR2'31A1==I>2dAJ693C@b4b5b6X0616911510':P:[^06P1P;P3O2b3135<G?W1W2W8W7o"). Qed.

  (* [comment removed for export] *)
  Definition JT1 : list Z := [176; 96; 8; 0; 48; 97; 8; 0; 80; 98; 8; 0; 48; 97; 8; 0; 176; 96; 8; 0; 176; 96; 8; 0; 176; 96; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 20; 99; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 176; 98; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 176; 96; 8; 0; 48; 97; 8; 0; 112; 98; 8; 0; 0; 97; 8; 0; 176; 96; 8; 0; 176; 96; 8; 0; 176; 96; 8; 0; 48; 97; 8; 0; 0; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 92; 97; 8; 0; 252; 97; 8; 0; 168; 97; 8; 0; 156; 98; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 72; 97; 8; 0; 48; 97; 8; 0; 56; 98; 8; 0; 48; 97; 8; 0; 48; 97; 8; 0; 176; 98; 8; 0]%Z.
  Lemma jt1_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m 140000 (zb JT1).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h07__arithh14__ffh28__varmaph35__with42MIh51mp;1p;2p;4p;3p;8p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0p10030p4p710R1p8P2p1003NR2p4p7210p8p1004?p4p7210P1p8p102Tnp6051000R3P0p8P3p101[ep4p710R0p8P3p102PBp4p710R4p8P3g00:lR5p4p710R6p8P3p1004kp4p710R7p8P3p1006Gp4p710R3p8p102V=p6051000R8P0p8P8P4p8P8P6p8P8P7p8P8P3p8p103RUp6051000R8P2p4p710R2p8P8p103Sbp4p710R8p8P7P1p8p103]7p6051000R7p103_ip4p710R6p8P7P0p8P7P1p8P7p101[Cp4p710R4p8p103^Bp6051000R9P6p8P9P0p8P9P4p8p103`@p6051001R4P0p8P4p100kMp4p710p8P4P7p8P4P9p8P4p103_Lp4p710p8p104Lep6051002R4P2p8P4P8p8p100A_p4p7210P1p8P3P1p8p1006fp4p7210P1p8g007ej10Tg008Jj16Tg008hj17Tg00>cj1QTg04Pgj2OTg00U[j12Tg014bj13Tg00:1j1ATg00FJj1@Tg007Ej1?Tg01DFj1=Tg00GHj1<Tg00Gfj1PTg00I4j24Tg00IWj4;Tg00Jdj2NTg00@ij2KTg00KFj2ETg00;Lj39Tg00L2j3DTg00LQj4CTg00B<j25Tg01Ddj3BTg01fLj3FTg00e7j28Tg01eOj2GTP5j2HTg00O;j1ITg04Q[j3JTg04RTj4>Tg04SSj8LTg00X5j7MTf0R5#0#0p=1f1R1g00[mg00\LR3P3g00\lR3P5g00]LFMp=:g00<DR8#0R4#1R2#0#1R9#6R7#7%62#7R2#Q[g00jXR0/O5P0P1%08#1#2#0#1#2#0#2#2#2#0#1#1#3R6g04`i#AR:P5g00_[R;#@R<%?;R;g00;fR=#=R>%<=R?%P=R@P=g00[ORA,4=g00`nRB14=6RCC;':1N@3R3P5f2RDg00_;REg00aURF'KRG1E5D=9EFdAD=A1CCR1b1b2b315A6P5b0P<P;P>P?P=%28#2#0#1#1#3R8,4=9B=CPB%34R4,4==F=7C;,:@P3P1b1b2b31868%39,G4R4'5P5b01H2:#I,86/54eP0P:P6PGAJ06:=9EFdC>GLW4W5o"). Qed.
  Lemma jt1_read_lit : forall m (t : Z) bs, mem_inv bsegs m -> (65 <= t <= 120)%Z ->
    firstn 4 (skipn (Z.to_nat (4 * (t - 65))) (zb JT1)) = bs ->
    ov_read_bytes bsegs m (wa (140000 + 4 * (t - 65))) 4 = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h04__p1h14__x1h21Rh37__arithh44__ffh54__p2h64__p3h78__varmaph85__with94__x2h:2bsh;1xh<1Hh=2H0h>2Hth?2MIh@1mhA1nhB1thC1zhD2z0p&0p;1p;2p;3p;4p;7p;6p;8p;<p;Bp-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0g002TR1p4p710p8P0g0030R3p4p710R4p8P2p1003NR2p4p7210p8p1004?p4p7210P4p8p102Tnp6051000R5P0p8P5g01[eR0p4p710R6p8P5p102PBp4p710R7p8P5g00:lR8p4p710R9p8P5p1004kp4p710R:p8P5p1006Gp4p710R5p8p102V=p6051000R;P6p8P;P7p8P;P9p8P;P:p8P;P5p8p103RUp6051000R;P2p4p710R2p8P;p103Sbp4p710R;p8P:P4p8p103]7p6051000R:p103_ip4p710R9p8P:P6p8P:P4p8P:p101[Cp4p710R7p8p103^Bp6051000R<P9p8P<P6p8P<P7p8p103`@p6051001R7P6p8P7p100kMp4p710p8P7P:p8P7P<p8P7p103_Lp4p710p8p104Lep6051002R7P2p8P7P;p8p100A_p4p7210P4p8P5P4p8p1006fp4p7210P4p8g007ej11Tg008Jj1UTg008hj1OTg00>cj1]Tg007Ej1YTg04Pgj2oTg00U[j14Tg014bj1@Tg00B<R4j23Tg00Clj28Tg01AAj26Tg01jGj27Tg00EjR5j1ATg00:1k101Tg018Dj3=TP0j3?Tg00;Lj32Tg00e7R0j2<Tg00eTj1ETg00fCj4CTg00?cj2DTg04alj2gTg040Lj7fTg015@j2BTP8j2[Tg00N>R8j29Tg00O;R;j1bTg00R_j2TTg00SHj3STg00T1j2aTg01nkj2PTg00FJj1`Tg00T]j3NTg00Fjj2QTg00GHj1_Tg00Gfj1^Tg00I4j2>Tg00HQj2MTg00JBk102Tg01EGj3\Tg01oWj3ZTg00Jdk200Tg00@ij2FTg00KFj2|Tg00L2j3{Tg00LQj4yTg04c5j2xTP1j6XTg00O[j2KTg00QDj2kTg00CPj2VTg00Qfj2WTg01DFj1jTg00U=j4iTg00IWj4LTg00V@j7hTg01Ddj3qTg00m?j4rTg04cSj1sTP3j6tTg00R@j10Tg00X5j7wTg00XYj6eTg00Y=j7dTg00Yaj8zTg00ZEl<cTg01K2lB}Tg00Zjl<~Tf0R3#1#1p=5%03#0p=Rg00;fR1f1R7g00`nP3CLp=IP7g00[mR2g00\LR<P<g00\lR:P3g00]LFwp=;P7P2P<P<P:P3Eep=Hf2R6P2P<P<P:P7P3Fdp=Gf3R9P2P<P<P:P6P7P3Gzp=J%03#0#0#0p=v%03#0#0#0#0#0#0#0p=u%03#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=p%03#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=:P1g00<iR=P1P1P5f4R5P;P9g00]lP6P7P3M<cp=nP=P=P=P1P1P1g01HHP;P;P;P0g01L<f5R0P5P9P6P7P3MB}p=mP=P1P8P;P4g00^YP0P5P9P6P7P3M<~p=lg00<DR4#1R;#1R8#1R>#5R?#1#U#O%U>#OR>#][%Y>R@g00jXRA/o6%4?#@R?/36%44#4RB#4#1#5#@RC,36RD'8g00bPRE#RRF#RRG%@8R8169?'7#Ag04`iRH$01RI5=>5?>=2@6P@165?,78#ARJ==>I9?>G%]@RKPAf6RL%14#5#4#1#5#4#1#4#4#4#1#5#5#@RM160?,78RN'<#EPGCC1D@332X:@PAP0PMPIPJPG1g06Ff1BJG1[>IRJ'9PAPL%ANRO#bRP,<M#EPGCCA=>OI9?>G,D@52K[P1PP16L?,78RP#ARQ/BGRR/9JPAf81<M7#EPGCCf7RS/6?,78RT#ARU==>I9?>G,D@52K[XC1P3PNp-0RVg00_[RW1T1ERE1T1FRF9S1Eg00bo'aRX'P%`WRY3N%YWRZ1Q17%_1R[%^1R\1>1?R]1M14R4'I,;\1H\95G\&02<R^g00[OR_,>1R`1>18RaA\14]5Z1'I,;\CJ200\:RbP3P6g00_;Rcg00aURd'F1|36=2cddA{1_7CyRdb4b7b8X11W013?3/87167?,78Rc,3_[^11^0VP313LCPLP9O3b3,xNEX1BOG/9JPAPS1<MP#EPGCCA=>QI9?>G,D@52K[P3P=1[1HRK1BUG/93XA=%vG#u#p#:#:#:#:#:#:R=,9R1K_PRU/<8R@%1B#5#5#@RB'3PRP@PQPUP3X;11K_3X;1PPPP1F1PDnPGP81F18EmP=PB1F1BEl1k_P1V_PA21UP'813P_A21U_'8'W1K_TP1AS1FE/PX=NWYPZP11Q16P7%j1CiP[P\P\P2P<P<P:1H\5P1P4g00c[R51M1;R;=\1]9Z1aCL,;\5G\1H\0P1P4P5P`CL,;\5G\FhP^P\1H\L1>1C,I;,;\5G\P^Aq14a1>1B'I,;\CJCJPbPdb4b7b8X11X91X0VX5VX6VA213c,86A213_,89'W180D1<68/3B[[^11^91^0V^5V^6VP3f9RV,3?16V?,78R8/3_1V_8PVP7P6PLO7b3bDb=Cr19RKePJ%sHEtO1b2b2P9P3EXW<W>W?W:XB1W@o"). Qed.
  Lemma jt1_read_s : forall m t, mem_inv bsegs m -> t = 115%Z -> ov_read_bytes bsegs m (wa (140000 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 72; Z_to_bv 8 97; Z_to_bv 8 8; Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h01th11Hh22MIh37__arithh44__ffh58__varmaph65__with71mp;1p;2p;3p;4p;7p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0g0030R1p4p710R3p8P2p1003NR2p4p7210p8p1004?p4p7210P3p8p102Tnp6051000R4P0p8P4g01[eR0p4p710R5p8P4p102PBp4p710R6p8P4p100:lp4p710R7p8P4p1004kp4p710R8p8P4p1006Gp4p710R4p8p102V=p6051000R9P5p8P9P6p8P9P7p8P9P8p8P9P4p8p103RUp6051000R9P2p4p710R2p8P9p103Sbp4p710R9p8P8P3p8p103]7p6051000R8p103_ip4p710R7p8P8P5p8P8P3p8P8p101[Cp4p710R6p8p103^Bp6051000R:P7p8P:P5p8P:P6p8p103`@p6051001R6P5p8P6p100kMp4p710p8P6P8p8P6P:p8P6p103_Lp4p710p8p104Lep6051002R6P2p8P6P9p8p100A_p4p7210P3p8P4P3p8p1006fp4p7210P3p8g007ej11Tg008Jj1ATg008hj1@Tg00>cj1FTg04Pgj2UTg00U[j15Tg014bj10Tg00;Lj37Tg007Ej1>Tg01AAj2CTg01jGj2GTg00e7j2YTg00eTj1VTg00R@j1;Tg00fCj4TTg009Kj28Tg00FJj1BTg00T]j32Tg00?cj2RTg01DFj1QTg00GHj1PTg00Gfj1OTg00I4j2<Tg00IWj4?Tg00Y=j7MTg00Jdj2LTg00@ij2DTg00KFj2KTg00L2j3JTg00LQj4NTg00B<j2ETg00Clj2ITg04d\j29Tg04eOj3:Tg00Ejj1HTg00:1j1STg018Dj3\TP0j3[Tg04f2j6ZTP1j6XTg00X5j7WTf0R1#1#1p=4%11#5p=6%51#1#1#1p=3f1R0g00[mR3g00\LR4P4g00\lR9P1g00]LFWp==g00<DR6#4R2#1R:#4R8#1#A#@%A:R5#@R7#F[g00;fR;g00jXR</U0%56#5R=#1#6#5#0R>97;0P;P>%>7R?#FP<f4%46#6#4#6#6#5#3#4#0%02R2%58#0R8,C1'G'Y#Vg00bP#;#;#;#;R<CT%46#3#0,85%36#6#0,85%0:R:,85g00[OR@,85%B7RA527527527527RB,R?37X0;f3P>PBP0g00_[RC#B%>C%Q;%P;%O;RCP3P4P4P9P;1<;8g00`nR41<;>R3C?,=CP;P3P4%3=#0R=,<;C?,=CFM1LC9P1f2RCg00_;R9g00aUR4'D1K1C=794dAJ;@0CNb4b5b61E8>1E>='IP1b3%46#3#0%46#3#0,955:5%36#6#0%36#6#0,955:5195:9:5:195@9:5@=27A527527527,D?1C>8,G2#Hg04`i#S5\79[7<=7?BdEZPCP1EXW1W2W0W7o"). Qed.
  Lemma jt1_read_d : forall m t, mem_inv bsegs m -> (t = 100 \/ t = 105)%Z -> ov_read_bytes bsegs m (wa (140000 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 97; Z_to_bv 8 8; Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h01Hh17__arithh24__ffh38__varmaph45__with51th62MIh71mp;1p;2p;4p;3p;6p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0g0030R1p4p710R3p8P2p1003NR2p4p7210p8p1004?p4p7210P3p8p102Tnp6051000R4P0p8P4g01[eR0p4p710R5p8P4p102PBp4p710R6p8P4p100:lp4p710R7p8P4p1004kp4p710R8p8P4p1006Gp4p710R4p8p102V=p6051000R9P5p8P9P6p8P9P7p8P9P8p8P9P4p8p103RUp6051000R9P2p4p710R2p8P9p103Sbp4p710R9p8P8P3p8p103]7p6051000R8p103_ip4p710R7p8P8P5p8P8P3p8P8p101[Cp4p710R6p8p103^Bp6051000R:P7p8P:P5p8P:P6p8p103`@p6051001R6P5p8P6p100kMp4p710p8P6P8p8P6P:p8P6p103_Lp4p710p8p104Lep6051002R6P2p8P6P9p8p100A_p4p7210P3p8P4P3p8p1006fp4p7210P3p8g007ej14Tg008Jj1JTg008hj1ETg00>cj1RTg04Pgj2\Tg00U[j16Tg014bj11Tg00QfR3j2UTg007Ej1CTg01AAj2;Tg01jGj29Tg00e7j2NTg00eTj1MTg00R@j1=Tg00fCj4LTg009Kj2<Tg00FJj1KTg00T]j32Tg00?cj2[Tg00;Lj35Tg01DFj1ZTg00GHj1YTg00Gfj1XTg00I4j2:Tg00Jdj2WTg00@ij2FTg00KFj2VTg00L2j3TTg00LQj4STg00B<j2>Tg00Clj2DTg04d\j2BTg04eOj3ATg00Ejj1QTg00:1j1`Tg018Dj3PTP0j3OTg04f2j6ITP1j6HTg00IWj4_Tg00X5j7^Tg00Y=j7]Tf0R1#4#4p=0%41#6p=3g00;fR0f1R4;51p=7%61#4p=8P0P4g00`nP1C_p=@P4g00[mR9g00\LR6P6g00\lR2P1g00]LF^p=?f2R:P9P6P6P2P4P1F]p=Gg00<DR6#0R9#4R8#0R5#4#J#E%J8R7#ER;#R[g00jXR</\4%66R=#4R>#3#0#1R?,74%8>#3#1R>,74'UP317:?17:>%C;R3#RR@P<f4RA%06#3#0#3#3#6#8#0#0#1RB%19R9f3RC%65#1R5';'9'N#Mg00bP#=#=#=#=RDCLg00[ORE,<7%86#0#3#1,<7%18R8,<71<7E%K;RF52;52;52;52;RG,[3RH35P117C?P0P?P<f61;15,99,NB#MPDCL=5@HX50RHf5R@P?PGPCg00_[RB#KR<%CBRB%Z0RI%Y0RJ%X0RK1:05RL1:0?RM'@,?K%6=#8#0#1R=,:0RN,@M,?K3G1WK2R2P1P:g00_;RMg00aURO'F1V1:=5MOdAT0E4CSR4b2b3b41>5?1>?='DP1b11B7E9A7E%86#0#3#1%86#0#3#1,B75A71B789A781B7E9A7E=2;F52;52;52;,F3RF1;?5,99#Qg04`i#`R?5P;9O;D=53GdEIPAP1EHW0P1O117C>P0P>PHP@P>PGPCP<PBPIPJ1:0>RJ,@L,?K1@JN,?K5GKP2P4b2b3b41>5>1>>='DP1b1PF1;>5,99#Q=P;?9O;D=53GdEIPAP1EHW0P1O1n200100000021100011000W0W6X50W7o"). Qed.
  Lemma jt1_read_u : forall m t, mem_inv bsegs m -> t = 117%Z -> ov_read_bytes bsegs m (wa (140000 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 56; Z_to_bv 8 98; Z_to_bv 8 8; Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h01th11Hh22MIh37__arithh44__ffh58__varmaph65__with71mp;1p;2p;3p;4p;7p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0g0030R1p4p710R3p8P2p1003NR2p4p7210p8p1004?p4p7210P3p8p102Tnp6051000R4P0p8P4g01[eR0p4p710R5p8P4p102PBp4p710R6p8P4p100:lp4p710R7p8P4p1004kp4p710R8p8P4p1006Gp4p710R4p8p102V=p6051000R9P5p8P9P6p8P9P7p8P9P8p8P9P4p8p103RUp6051000R9P2p4p710R2p8P9p103Sbp4p710R9p8P8P3p8p103]7p6051000R8p103_ip4p710R7p8P8P5p8P8P3p8P8p101[Cp4p710R6p8p103^Bp6051000R:P7p8P:P5p8P:P6p8p103`@p6051001R6P5p8P6p100kMp4p710p8P6P8p8P6P:p8P6p103_Lp4p710p8p104Lep6051002R6P2p8P6P9p8p100A_p4p7210P3p8P4P3p8p1006fp4p7210P3p8g007ej15Tg008Jj1CTg008hj1>Tg00>cj1GTg04Pgj2VTg00U[j10Tg014bj17Tg00;Lj38Tg007Ej1ETg01AAj2HTg01jGj2FTg00e7j2WTg00eTj1UTg00R@j1;Tg00fCj4TTg009Kj2:Tg00FJj1DTg00T]j33Tg00?cj2STg01DFj1RTg00GHj1QTg00Gfj1OTg00I4j2=Tg00IWj4ATg00Y=j7NTg00Jdj2MTg00@ij2?Tg00KFj2LTg00L2j3KTg00LQj4JTg00B<j2BTg00Clj2PTg04d\j2<Tg04eOj39Tg00Ejj1ITg00:1j1]Tg018Dj3\TP0j3[Tg04f2j6ZTP1j6YTg00X5j7XTf0R1#5#5p=6%51#0p=2%01#5#5p=4%51#7p=1f1R0g00[mR3g00\LR4P4g00\lR9P1g00]LFXp=@g00<DR6#6R2#5R:#6R8#5#C#>%C:R5#>R7#G[g00;fR;g00jXR</V0%06#0R=#2#2#7R>98;0P;P>%E7R?#GP<f4%66#2#6#2#2#0#4#6#1%72R2%08#7R8,H1'F'W#Ug00bP#;#;#;#;R<CT%06#4#1,:5%46#2#1,:5%7:R:,:5g00[OR@,:5%D7RA537537537537RB,S?38X0;f3P>PBP0g00_[RC#D%EC%R;%Q;%O;RCP3P4P4P9P;1=;8g00`nR41=;>R3CA,@CP;P3P4%4=#1R=,=;CA,@CFN1MC9P1f2RCg00_;R9g00aUR4'?1L1C=894dAK;@0CJb4b5b61B8>1B>='PP1b3%06#4#1%06#4#1,<5595%46#2#1%46#2#1,<55951<5:995:1<5@995@=37A537537537,??1H>8,F2#Ig04`i#]5\79[7<=8?BdEZPCP1EYW1W2W0W7o"). Qed.
  Lemma jt1_read_x : forall m t, mem_inv bsegs m -> (t = 120 \/ t = 88)%Z -> ov_read_bytes bsegs m (wa (140000 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 176; Z_to_bv 8 98; Z_to_bv 8 8; Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "h01Hh17__arithh24__ffh38__varmaph45__with51th62MIh71mp;1p;2p;4p;3p;6p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0p1002Tp4p710p8P0g0030R1p4p710R3p8P2p1003NR2p4p7210p8p1004?p4p7210P3p8p102Tnp6051000R4P0p8P4g01[eR0p4p710R5p8P4p102PBp4p710R6p8P4p100:lp4p710R7p8P4p1004kp4p710R8p8P4p1006Gp4p710R4p8p102V=p6051000R9P5p8P9P6p8P9P7p8P9P8p8P9P4p8p103RUp6051000R9P2p4p710R2p8P9p103Sbp4p710R9p8P8P3p8p103]7p6051000R8p103_ip4p710R7p8P8P5p8P8P3p8P8p101[Cp4p710R6p8p103^Bp6051000R:P7p8P:P5p8P:P6p8p103`@p6051001R6P5p8P6p100kMp4p710p8P6P8p8P6P:p8P6p103_Lp4p710p8p104Lep6051002R6P2p8P6P9p8p100A_p4p7210P3p8P4P3p8p1006fp4p7210P3p8g007ej14Tg008Jj1LTg008hj1GTg00>cj1STg04Pgj2`Tg00U[j11Tg00QfR3j2YTg007Ej1PTg014bj1<Tg01AAj28Tg01jGj2;Tg00e7j2OTg00eTj1NTg00R@j1>Tg00fCj4MTg009Kj2?Tg00FJj1KTg00T]j35Tg00?cj2]Tg00;Lj37Tg01DFj1\Tg00GHj1[Tg00Gfj1ZTg00I4j2BTg00Jdj2XTg00@ij2FTg00KFj2WTg00L2j3VTg00LQj4UTg00B<j2=Tg00Clj2ETg04d\j2ATg04eOj3@Tg00Ejj1TTg00:1j1bTg018Dj3RTP0j3JTg04f2j6QTP1j6ITg00IWj4aTg00X5j7_Tg00Y=j7^Tf0R1#4#4p=0%11#1p=C%41#<p=3g00;fR0f1R4;71p=6%41#1p=2%11#4p=DP0P4g00`nP1Cap=9P4g00[mR9g00\LR6P6g00\lR2P1g00]LF_p=:f2R:P9P6P6P2P4P1F^p=Hg00<DR6#4R9#4R8#4R5#0R7#4#L#G%L5R;#GR<#S[g00jXR=/`4%16#C#0#3R>,64%C9#0#3R9,64'YP316:>16:9%P<R3#SR?P=f4R@%06#2#0#2#2#C#0#0#3RA%<8R8f3RB%17#<R7'8';'O#Ng00bP#>#>#>#>RCCM%26#D#0#3,?;%16#0#2#3,?;%<5R5,?;g00[ORD,?;%K<RE55<55<55<55<RF,]3RG37P116B>P0P>P=f61817,;8,OA#NPCCM=7?GX50RGf5R?P>PFPBg00_[RA#KR=%PARA%\0RH%[0RI%Z0RJ1B07RK1B0>RL'9,:J19LL,:J3H1XJ2R2P1P:g00_;RMg00aURN'F1W1:=7MNdAV0D4CUR4b2b3b41=7>1=>>'EP1b1%26#D#0#3%26#D#0#3,A;5@;%16#0#2#3%16#0#2#3,A;5@;1A;59@;51A;D9@;D=5<E55<55<55<,F3RE18>7,;8#Tg04`i#bRD5R<9J<C=73FdEQP@P1EIW0P1O116B9P0P9PGP?P9PFPBP=PAPHPI1B09RI,9K,:J19IL,:J5HJP2P4b2b3b41=791=9>'EP1b1PE1897,;8#T=R<D9J<C=73FdEQP@P1EIW0P1O1n200100000021100011000W0W6X50W7o"). Qed.
  Lemma jt1_read_fp : forall m t, mem_inv bsegs m -> conv_type t = Some T_DBL -> ov_read_bytes bsegs m (wa (140000 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 176; Z_to_bv 8 96; Z_to_bv 8 8; Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "p'0h05Heqb2h11Hh24Heqbh35Heqb0h45Heqb1h52CTh67__arithh74__ffh88__varmaph95__with:1th;1bi001bh<1eh=1mh>2b1h?2b2h@1nhA2MIi011oi021pi031zp%0p;1p;2p;3p;6p;4p;7p;9p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0g002TR1p4p710p8P0g0030R3p4p710R4p8P2p1003NR2p4p7210p8p1004?p4p7210P4p8p102Tnp6051000R5P0p8P5g01[eR0p4p710R6p8P5p102PBp4p710R7p8P5p100:lp4p710R8p8P5p1004kp4p710R9p8P5p1006Gp4p710R5p8p102V=p6051000R:P6p8P:P7p8P:P8p8P:P9p8P:P5p8p103RUp6051000R:P2p4p710R2p8P:p103Sbp4p710R:p8P9P4p8p103]7p6051000R9p103_ip4p710R8p8P9P6p8P9P4p8P9p101[Cp4p710R7p8p103^Bp6051000R;P8p8P;P6p8P;P7p8p103`@p6051001R7P6p8P7p100kMp4p710p8P7P9p8P7P;p8P7p103_Lp4p710p8p104Lep6051002R7P2p8P7P:p8p100A_p4p7210P4p8P5P4p8p1006fp4p7210P4p8g007ej15Tg008Jj1dTg008hj1aTg00>cR4j1`Tg04Pgj2uTg03hmj1pTg00?cj2MTg00;Lj31Tg00U[j14Tg01ZIj20Tg00@ij2_Tg014bj1ITg00JBj1nTg007Ej1hTg00R@j1ZTg009Kj2WTg00FJj1cTg00T]j3DTP1j6UTg01U=j2TTg00QfR1j2BTg04g>j2jTg04g^j2|Tg01DFj1zTg00GHj1yTg00Gfj1xTg00Jdj2tTg00KFj2sTg00L2j3rTg00LQj4qTg00B<j29Tg00ClR5j2JTg04d\j2YTg04eOj3XTg00Ejj1NTg00:1j1oTg018Dj3PTP0j3LTg04f2j6OTg01Zfj23Tg01AAj2^Tg01jGj2]Tg00e7j2eTg00eTj1fTg00fCj4gTg00I4j2mTg00IWj4lTg00X5j7vTg00Y=j7wTP3l9kTf0R3#5#5p=F%53#4p=C%43#Ip=>g00_;R0f1R:;13p=H%53#Ip=[f3R7f2R2'010:3'3p=6%43#5p=V%53#5#5#Ip=?f5R;f4R9'01072'310:3'3p=<f7R6f6R8'010;9'3/37/32/3:/33p=@g00jXR<P81^72,]9,e;#fP:Cg=163p==g00aUR=9103p=2g013DR>9103p=;13:3=10=p=b1097,3;/32/3:/33p=i1097/32/3:/33p=\10:3,32=10=p=E10:3=10=p=8g00;fR??1:3p=A10:3,32=10>p=71^:3,]2,e7#fp={P<P7P2P:Cg=193p=S1m?3p=GP2g00[mR>g00\LR@P@g00\lRAP?P:g00`nP3Clg00]LFvp=:P2P>P@P@PAP:P3Fwp=R1^:3,]2p=QP?P6P8P;P9P7P2P:P3M9kp=Kg00<DR@#5R>#5RB#5RC#FRD#5#d#a%dCRE#aRF#`[1u<:%`?R<%p:g04h>,M?31%4@RG#4RH#5RI#C#>RJ,02P01_03RK107J/H3P010;J/H3P0P<P:%>B,M?RLP0P<P8%5GRG#CRM#5RN#[ROP8%4G#F#>RGC6RP%4>R>#[,M?RQP0P<P8%VI#>RIP8%4H#?RHP8%4>R>#?RRE<%I>,M?R>P0P<P8%>NRNP8%4MRS#[RT%>SRS,08%4CRU#5#>RV,08%4URU#[RW,08%>URU,08G@%IM,M?RM%n?R8n0100000020000n0100000020000n0100000020000n0100000020000=1<M%hFRX#`RYf8RZ%F@#C#F#C#C#4#4#F#?R[%IBRBP6%>DRDg00bP#Z#Z#Z#ZR\%C@#V#?,WE%4@#F#?,WE%ICRC,WEg00[OR],WE%cFR^5DF5DF5DF5DFR_,MXR`G=Ra]5]2P:109JR9#2A1<LMP<PLP4P?p-0RLP3P?PLP3g01XPRbg04i<RcPLP3PcPLP3PbPcPLP3PbPcPLP3PbPbg01X4Rdn011020003100001000000Pbn011020003101021010200Pbn011020003101021010200PbPbn011020003101021010200Pbn011030003001010210102Pbn10110100021010300X<<g01XmRePMP3EUPb1Ta3b1W5W2%;9P0P<P;POP;PGC6PQP0P<P;PIP;PHP;PRE<P>P0P<P;PNP;PT10;S10;V10;W10;UG@PMP8n0100000020000n0100000020000n0100000020000=1<MPPP0PKP6POP6PGC6/H3P0f9R6POP6PGC6/H3P0P<P:PQP0P<f:RPPIPPPHPPPRE<R;P>P0P<PPPNPPPT10PS10PV10PW10PUG@PMP8n0100000020000n0100000020000n0100000020000=1<MPYf<RPP[PBf;R9PDP\P`G=Ra]5]3P:PZPOPZPGC6RZ#2A1<QMP<PQP4P?PLP3P?PLP3PbPcPLP3PbPdPbn011020003100001000000Pbn011030003001010210102Pbn10110100021010300X<<PePMP3EUPb1Ta3b1W5W3%;ZP0P<P6PIP6PHP6PRE<P>P0P<P6PNP6PT106S106V106W106UG@PMP8n0100000020000n0100000020000=1<MP;P0PKP9PIP9PHP9PRE</H3P0f=R;PIP;PHP;PRE</H3P0P<P:P>P0P<f>R6PNP6PT106S106V106W106UG@R6PMP8n0100000020000n0100000020000=1<MPYf@RZP[PBf?RaPDP\P`G=RQ]5]4P:PPPIPPPHPPPRE<RP#2A1<>MP<P>P4P?PLP3P?PLP3PbPcPLP3PcPLP3PdPbPbn011020003100001000000PbPbn011020003101021010200Pbn011030003001010210102Pbn10110100021010300X<<PePMP3EUPb1TQ3b1W5W4%;PP0P<P;PNP;PT10;S10;V10;W10;UG@PMP8n0100000020000=1<MP6P0PKPaPNPaPT10aS10aV10aW10aUG@/H3P0fARKPNPKPT10KS10KV10KW10KUG@/H3P0P<P:PMP8n0100000020000=1<MPYfDRKP[PBfCR6PDP\P`G=R;]5]0P:PZPNPZPT10ZS10ZV10ZW10ZUG@RZ#2A1<MMP51b:3%22RP%2:RQ'B[Rc%23,BQ1b2:RQ[%27/BP\Q1j:3P:n2001000000120000000X?0X>0RQPc^?0^>0RcP3106NP6PT106S106V106WEiRP106UR>P2O3%2P%2>'BP1PKPN10KT10KS10KVD\?EKW18KUPYfFP[PBfERKPDP\P`G=P3PKPN10KT10KS10KVD\?EKWPQPcP3fGR>PN10>T10>S10>VD\RP10>WRfP:O3%2P%2f'BP1fHRfPNPfPTPfPSE<?EfV18fWPYfJS00P[PBfIRPPDP\P`G=P3PPPNPPPTPPPSE<?EPVPQPcP3fKRgPNPgPTPgPSE<Rh10gVRiP:O3%2h%2i'BP1fLRiPNPiPTC6?EiS18iVPYfNRhP[PBfMRjPDP\P`G=P3PjPNPjPTC6?EjSPQPcP3fORkPNPkPTC6Rl10kSRmP:O3%2l%2m'BP1fPRm/0N?EmT18mSPYfRRlP[PBfQRnPDP\P`G=P310nN?EnTPQPcP3fSRc/0NRQ10cTRoP:O3%2Q%2o'BP1fTR1/8N181TPYfVRoP[PBfURQPDP\P`G=P318QNP518:31A2:[R51A:3182:Rp[1A72\p1|:3P:n2001000000120000000X=?X@?RpP5^=?^@?R5P3fWRqPNP:O31AqNPN103J#;Rr10:O?7:GRsP2PIP2PHC6?72RRtPYf]P[PBP7PDC{R7P\P`DS]4]3]2X:?R[10NJ#;10NO?7NGPNPIPNPHC6?7NRf\RuPNP_fZRvg00_[Rw#cRx%hwRw%z?Ry%y?Rz%x?R{%GDR|%GNR}5:{%GHR~9:{}3R1t{ARAP3P21_0=1s32#2dAr?]:CqR=b7b8b919DN19NH'JP3b6%C@#V#?%C@#V#?,YE5XE%4@#F#?%4@#F#?,YE5XE1YEC9XEC1YE]9XE]=DF^5DF5DF5DF,_XR^AQBND#Ng04`i#oRN5PF9LF\=1X_dEOW4W3W2fXR]P3PcPkPgGKb0b1W0P3O118QTPpP5P3PqPTP:O31AqTPTP[10TJ#;10TO?7TGPTPIPTPHC6?7TRPuPTP_PvPxPwPyPz%GTRv9:{|A:{v~5R{PAP=b7b8b919DT19TH'JP3b6P^AQBTD#N=PFN9LF\=1X_dEOW4W3W2P]P3PcPkPgGKb0b1W0P3O1n200100000021100011000b0b1W0P3O118nSPpP5P3PcPSP:O31AcSPSPYfYP7P\P`DS^4t^3s^2rX:?10SJ#;10SO?7SGPSPIPSPHC6?7SRP]PSP_PoPxPwPyPz%GSRo9:{|A:{o~5R{PAP=b7b8b919DS19SH'JP3b6P^AQBSD#N=PFN9LF\=1X_dEOW4W3W2P1P3PkPgP>GKb0b1W0P3O1n200100000021100011000b0b1W0P3O118jVPpP5P3PkPVP:O31AkVPVPYPQP7P\P`DS^4t^3s^2rX:?10VJ#;10VO?7VGPVPIPVPHC6?7VRP1PVP_PlPxPwPyPz%GVRl9:{|A:{l~5R{PAP=b7b8b919DV19VH'JP3b6P^AQBVD#N=PFN9LF\=1X_dEOW4W3W2PmP3PgP>P6GKb0b1W0P3O1n200100000021100011000b0b1W0P3O118PWPpP5P3PgPWP:O31AgWPWPYPnP7P\P`DS^4t^3s^2rX:?10WJ#;10WO?7WGPWPIPWPHC6?7WRPmPWP_PhPxPwPyPz%GWRh9:{|A:{h~5R{PAP=b7b8b919DW19WH'JP3b6P^AQBWD#N=PFN9LF\=1X_dEOW4W3W2PiP3P>P6PaGKb0b1W0P3O1n200100000021100011000b0b1W0P3O118KUPpP5P3P>PUP:O31A>UPUPYPjP7P\P`DS^4t^3s^2rX:?10UJ#;10UO?7UGPUPIPUPHC6?7URPiPUP_Q00PxPwPyPz%GURz9:{|A:{z~5R{PAP=b7b8b919DU19UH'JP3b6P^AQBUD#N=PFN9LF\=1X_dEOW4W3W2PfP3P6PaP9GKb0b1W0P3O1n200100000021100011000b0b1W5W0%;ZA1<8MP<P8P4P?PLP3PbPdn10110100021000000X<<PePMP3EUPb1T;3b1W5W0n0110001020101P3P2O2b0b;W5W4n0110001020101P3P2O2b4b;W5W3n0110001020101P3P2O2b3b;W5W2n0110001020101P3P2O2b2b;W5WAX:?W=o"). Qed.

  Lemma conv_type_cases : forall t ty, conv_type t = Some ty ->
    (ty = T_PTR /\ t = 115%Z) \/ (ty = T_INT /\ (t = 100 \/ t = 105)%Z) \/ (ty = T_UINT /\ (t = 117 \/ t = 120 \/ t = 88)%Z) \/ (ty = T_DBL).
  Proof.
    clear. intros t ty CT. unfold conv_type in CT.
    repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [injection CT as <-|] end; try discriminate CT;
    repeat match goal with E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
      subst; auto 10.
  Qed.

  (* [comment removed for export] *)
  Lemma fl_shl50 : forall fl, (0 <= fl < 131072)%Z ->
    (Z.land (Z.shiftl fl 50) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 8192 = 0)%Z.
  Proof.
    clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
    change 8192%Z with (2^13)%Z. rewrite zb_land_pow2 by lia.
    change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    split; intros H; Z.div_mod_to_equations; nia.
  Qed.
  Lemma nzmask_bits' : forall n, (0 <= n < 0 + Z.of_nat 64)%Z -> Bool.eqb (Z.testbit 18446744073709486079 n) (negb (Z.testbit 65536 n)) = true.
  Proof. clear. apply Zrange_forallb. vm_compute. reflexivity. Qed.
  Lemma nzmask_eq : forall fl, (0 <= fl < 131072)%Z -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
  Proof.
    clear. intros fl Hfl. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases n 64).
    - pose proof (nzmask_bits' n ltac:(cbn; lia)) as E. destruct (Z.testbit 18446744073709486079 n), (Z.testbit 65536 n); cbn in E; try discriminate; reflexivity.
    - replace (Z.testbit fl n) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec fl 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with 17%Z; [apply Z.log2_lt_pow2; cbn in *; lia|lia].
  Qed.
  Lemma land_bound' : forall a m, (0 <= a)%Z -> (0 <= m)%Z -> (0 <= Z.land a m <= a)%Z.
  Proof.
    clear. intros a m Ha Hm. split; [apply Z.land_nonneg; left; exact Ha|].
    pose proof (Z.sub_land_same_l a m) as E.
    assert (0 <= Z.land a (Z.lnot m))%Z by (apply Z.land_nonneg; left; exact Ha). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sextw_small : forall p, (-2147483648 <= p < 2147483648)%Z -> bv_swrap 32 (Z.land p 18446744073709551615 + 0) = p.
  Proof.
    clear. intros p Hp. rewrite Z.add_0_r. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite swrap32_eq.
    replace (p mod 2 ^ 64)%Z with (p + 2^64 * (- (p / 2^64)))%Z by (Z.div_mod_to_equations; lia).
    change (2^64)%Z with (4294967296 * 4294967296)%Z.
    set (kq := (- (p / (4294967296 * 4294967296)))%Z). clearbody kq. Z.div_mod_to_equations. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma pad_test_xor : forall fl b, Z.land b 73728 = b ->
    (Z.land (Z.lxor fl b) 73728 =? 0)%Z = (Z.land fl 73728 =? b)%Z.
  Proof.
    clear. intros fl b Hb. rewrite land_lxor_distr, Hb.
    destruct (Z.eqb_spec (Z.lxor (Z.land fl 73728) b) 0) as [E|E]; destruct (Z.eqb_spec (Z.land fl 73728) b) as [E2|E2]; try reflexivity; exfalso.
    - apply E2. apply Z.lxor_eq. exact E.
    - apply E. rewrite E2. apply Z.lxor_nilpotent.
  Qed.

  (* [comment removed for export] *)
  Ltac the_mi k := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.

  (* [comment removed for export] *)
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
  (* [comment removed for export] *)
  Tactic Notation "jump" tactic3(tac) := eapply evtF_eq; [ | tac ]; [ mseq | .. ].
  Lemma implAM_eq_ms : forall {X} (c : M St X) s Q ms ms', ms = ms' -> implAM RNG c s Q ms' -> implAM RNG c s Q ms.
  Proof. intros X c s Q ms ms' -> H. exact H. Qed.
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
    eapply implAM_eq_ms; [ | tac ]; [ mseq | .. ].

  (* [comment removed for export] *)
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

  (* [comment removed for export] *)
  Lemma sink_store : forall m st a (bs : list byte),
    SINK m st -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
    (a + Z.of_nat (length bs) <= Fp \/ Fp + 232 <= a)%Z -> (a + Z.of_nat (length bs) <= B \/ B + BS <= a)%Z ->
    SINK (write_to_mem m (wa a) bs) st.
  Proof using Fp B BS SINK SFR. clear SFL TOK HOUT HSTRN HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 KH RSK RFM RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    intros m st a bs HS Ha Hb D1 D2.
    apply (SFR [(a, a + Z.of_nat (length bs))]%Z m _ st HS).
    - apply munch_write; [apply munch_refl | lia | lia | cbn; lia].
    - apply wmono_write. apply wmono_refl.
    - constructor; [cbn; lia | constructor].
    - constructor; [cbn; lia | constructor].
  Qed.
  Lemma sink_call : forall Wc m m' st,
    SINK m st -> munch Wc m m' -> wmono bsegs m m' ->
    Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv)%Z Wc ->
    Forall (fun iv => snd iv <= B \/ B + BS <= fst iv)%Z Wc ->
    SINK m' st.
  Proof using Fp B BS SINK SFR. clear SFL TOK HOUT HSTRN HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 KH RSK RFM RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B. intros Wc m m' st HS MU WM D1 D2. exact (SFR Wc m m' st HS MU WM D1 D2). Qed.

  (* [comment removed for export] *)
  Lemma arg_ok_W : forall m m' w a, arg_ok Fp B BS RNG m lo q AP w a -> munch W m m' -> wmono bsegs m m' -> arg_ok Fp B BS RNG m' lo q AP w a.
  Proof using Fp B BS RB RNG q m0 lo fmt AP VA slots LO SEP_F HAP KH RBI RC_B. clear SFR SFL TOK HOUT HSTRN HF GLO QHI TQ FRM0 HA SEP_B HVA A0 VAHI BS0 RSK RFM RPF RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt.
    intros m m' w a H MU WM. destruct a as [s|i|u|d]; cbn in H |- *; try exact H.
    destruct H as (slack & BYs & Hs & PAD & NZ & D1 & D2 & D3 & D4 & D5 & RGs & r & RC & IR & RR). exists slack.
    split; [|repeat (split; [assumption|])].
    - eapply bytes_at_transport; [exact BYs | exact MU |].
      unfold W. cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
    - exists r. split; [| split; [exact IR | exact RR]]. eapply rclean_transport; [exact RC | exact MU | exact WM | apply appW_W].
  Qed.
  Lemma args_ok_W : forall m m' ws args, args_ok Fp B BS RNG m lo q AP ws args -> munch W m m' -> wmono bsegs m m' -> args_ok Fp B BS RNG m' lo q AP ws args.
  Proof using Fp B BS RB RNG q m0 lo fmt AP VA slots LO SEP_F HAP KH RBI RC_B. clear SFR SFL TOK HOUT HSTRN HF GLO QHI TQ FRM0 HA SEP_B HVA A0 VAHI BS0 RSK RFM RPF RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt.
    intros m m' ws args. revert ws. induction args as [|a args IH]; intros ws H MU WM; [destruct ws; exact I|].
    cbn [args_ok] in H |- *.
    destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2]. split; [eapply arg_ok_W; eauto | apply IH; assumption].
  Qed.
  (* [comment removed for export] *)
  Lemma arg_ok_s_W : forall m m' w s, arg_ok Fp B BS RNG m lo q AP w (PA_s s) -> munch W m m' ->
    exists slack : list byte,
        bytes_at bsegs m' (bv_unsigned w) (zb s ++ Z_to_bv 8 0 :: slack)
        /\ Forall (fun c => 0 < c < 256)%Z s
        /\ ((- (bv_unsigned w + zlength s + 1)) mod 8 <= zlength slack)%Z
        /\ (0 < bv_unsigned w)%Z
        /\ (bv_unsigned w + zlength s + 1 + zlength slack <= lo \/ q <= bv_unsigned w)%Z
        /\ (bv_unsigned w + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= bv_unsigned w)%Z
        /\ (bv_unsigned w + zlength s + 1 + zlength slack <= B \/ B + BS <= bv_unsigned w)%Z
        /\ (bv_unsigned w + zlength s + 1 + zlength slack <= AP \/ AP + 8 <= bv_unsigned w)%Z
        /\ (bv_unsigned w + zlength s + 1 <= 2^47)%Z                    (* [comment removed for export] *)
        /\ rng RNG (bv_unsigned w) (zlength s + 1 + zlength slack)
        /\ exists r : region, rclean m r /\ inreg r (bv_unsigned w) (zlength s + 1 + zlength slack) /\ rrng RNG r.
  Proof using Fp B BS RNG q lo fmt AP slots. clear SFR SFL TOK HOUT HSTRN HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 KH RSK RFM RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    intros m m' w s H MU. cbn in H.
    destruct H as (slack & BYs & Hs & PAD & NZ & D1 & D2 & D3 & D4 & D5 & RGs & RR). exists slack.
    split; [|repeat (split; [assumption|]); exact RR].
    eapply bytes_at_transport; [exact BYs | exact MU |].
    unfold W. cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
  Qed.

  (* [comment removed for export] *)
  Definition lo_cells14 (pfx s2s za pl plp l10n : word) : list cell :=
    [C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
     C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364)].
  Lemma lo_split : forall m pfx s2s za pl plp l10n alo ahi j128,
    rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
    rw_cells bsegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) /\
    rw_cells bsegs m (q + -544 + 112) [C8 alo; C8 ahi] /\ rw_cells bsegs m (q + -544 + 128) [CB 24 j128].
  Proof using q AP nla nlt. clear SFR SFL TOK HOUT HSTRN HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 KH RSK RFM RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    clear. intros. unfold lo_cells in H.
    apply (proj1 (rw_cells_app bsegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add app] in H2.
    change (Z.of_nat 112) with 112%Z in H2.
    apply (proj1 (rw_cells_app bsegs m _ [_;_] _)) in H2. destruct H2 as [H2 H3]. cbn [cells_size csize Nat.add app] in H3.
    change (Z.of_nat 16) with 16%Z in H3.
    split; [exact H1|]. split; [exact H2|]. replace (q + -544 + 128)%Z with (q + -544 + 112 + 16)%Z by lia. exact H3.
  Qed.
  Lemma lo_join : forall m pfx s2s za pl plp l10n alo ahi j128,
    rw_cells bsegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) ->
    rw_cells bsegs m (q + -544 + 112) [C8 alo; C8 ahi] -> rw_cells bsegs m (q + -544 + 128) [CB 24 j128] ->
    rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128).
  Proof using q AP nla nlt. clear SFR SFL TOK HOUT HSTRN HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 KH RSK RFM RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    clear. intros. unfold lo_cells.
    apply (proj2 (rw_cells_app bsegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)). split; [exact H|]. cbn [cells_size csize Nat.add app].
    change (Z.of_nat 112) with 112%Z.
    apply (proj2 (rw_cells_app bsegs m _ [_;_] _)). cbn [cells_size csize Nat.add app]. change (Z.of_nat 16) with 16%Z. split; [exact H0|].
    replace (q + -544 + 112 + 16)%Z with (q + -544 + 128)%Z by lia. exact H1.
  Qed.

  (* [comment removed for export] *)
  Ltac transport_chunks segs m a bs ::=
    repeat match goal with
    | H : bytes_at segs m ?A2 ?bs2 |- _ =>
        first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
                [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
    | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
    | H : rw_cells segs m ?A2 ?cs2 |- _ =>
        first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
                [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
    | H : ro_cells segs m ?A2 ?cs2 |- _ =>
        first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
                [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
    | H : u8arr segs m ?A2 ?xs |- _ =>
        first [ apply (u8arr_frame segs m A2 xs a bs) in H;
                [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
    | H : u8ro segs m ?A2 ?xs |- _ =>
        first [ apply (u8ro_frame segs m A2 xs a bs) in H;
                [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
    | H : SINK m ?st |- _ =>
        first [ apply (sink_store m st a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia | simpl_sizes; slia ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
    end.
  Ltac transport_after_call segs m m' MU WM ::=
    let W := lazymatch type of MU with munch ?W _ _ => W end in
    repeat match goal with
    | H : bytes_at segs m ?A2 ?bs2 |- _ =>
        first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
    | H : rw_cells segs m ?A2 ?cs2 |- _ =>
        first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : ro_cells segs m ?A2 ?cs2 |- _ =>
        first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : u8arr segs m ?A2 ?xs |- _ =>
        first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : u8ro segs m ?A2 ?xs |- _ =>
        first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : SINK m ?st |- _ =>
        first [ eapply (sink_call W m m' st) in H;
                [ | exact MU | exact WM
                | repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : stk segs m ?loq ?hiq |- _ =>
        first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
              | clear H ]
    | H : munch ?Wq ?mq m |- _ =>
        first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
              | fail 100 "callee footprint not inside caller footprint" ]
    | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pop_arg_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (a0v k ty : Z) (slot x y : word),
    a0v = (q + -544 + 112)%Z ->
    rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] ->
    va_area m VA slots -> nth_error slots (Z.to_nat k) = Some slot -> (0 <= k)%Z ->
    rw_cells bsegs m (q + -544 + 112) [C8 x; C8 y] ->
    stk bsegs m lo (q + -544) ->
    mem_inv bsegs m ->
    (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL)%Z ->
    evtF bsegs RNG (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft' m',
                 ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          Ft' (ret_pc ra') fc None m' (seg_rom bsegs)
                 /\ munch [(q + -544 - 16, q + -544); (AP, AP + 8); (q + -544 + 112, q + -544 + 112 + 16)]%Z m m'
                 /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ stk bsegs m' lo (q + -544)
                 /\ rw_cells bsegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (k + 1)))]
                 /\ rw_cells bsegs m' (q + -544 + 112) [C8 (F_pop_arg.pop_arg_lo ty slot); C8 (F_pop_arg.pop_arg_hi ty slot y)]
                 /\ Fokd Ft Ft')
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 ty) (Z_to_bv 64 AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0xa8c78) fc None m (seg_rom bsegs)).
Proof using RNG q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA RG_stk RG_img RG_ap RG_va.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "p'0h02m'h11kh23Ft'h33t6'h43t5'h53t4'h63t3'h73a7'h83a6'h93a5'h:3a4'h;3a3'h<2Fth=3a2'h>3a1'h?3a0'h@2t6hA3t2'hB3t1'hC2t5hD3t0'hE2t4hF4__x1hG2t3hH1HhI2a7hJ4__x2hK2a6hL2a5hM2a4hN2a3hO1zhP2a2hQ7__sat13hR7__sat14hS7__sat15hT4cstrhU7__arithhV4__ffhW8__varmaphX5__withY2a1hZ2a0h[3H12h\3IL0h]4__p1h^7__sat16h_2t2h`3z12ha2t1hb4__x3hc2t0hd3ms'he2Hahf1Phg7__sat12hh1xi001xhi1Ahj4__p2hk4__p3hl4__x4hm4__x5hn3a0vho1lhp1nhq3APChr4APC'hs4ARGCht5ARGC'hu2Eahv2Ephw2Eqhx2H0hy2HFhz2Hkh{2ILh|2MIh}3MI'h~2MUi013NTHi022STi033ST'i043ST1i053ST2i062TYi073VAAi084VAA'i092VBi0:2WMi0;1ai0<1ei0=2fci0>1mi0?1oi0@3ra'i0A2s0i0B2s1i0C3s10i0D3s11i0E2s2i0F2s3i0G2s4i0H2s5i0I2s6i0J2s7i0K2s8i0L2s9i0M4sloti0N2tyi0O1yp%0p%1p%2p&0p&1p;1p;2p;3p;Op;7p;4p;6p;Kp;op;Lp;5p;:p;8p;<p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0g002TR1p4p710p8P0g0030R3p4p710R4p8P2p1003NR2p4p7210R5p8g004?R6p4p7210P4p8p102Tnp6051000R7P0p8P7p101[ep4p710R0p8P7p102PBp4p710R8p8P7g00:lR9p4p710R:p8P7p1004kp4p710R;p8P7p1006Gp4p710R7p8p102V=p6051000R<P0p8P<P8p8P<P:p8P<P;p8P<P7p8p103RUp6051000R<P2p4p710R2p8P<p103Sbp4p710R<p8P;P4p8p103]7p6051000R;p103_ip4p710R:p8P;P0p8P;P4p8P;p101[Cp4p710R8p8p103^Bp6051000R=P:p8P=P0p8P=P8p8p103`@p6051001R8P0p8P8p100kMp4p710p8P8P;p8P8P=p8P8p103_Lp4p710p8p104Lep6051002R8P2p8P8p105@np4p710p8P8p1058Zp4p710p8P8P<p8p1059Qp605311001R<P5p8P<p1056[p4p7210p8p100A_p4p7210P4p8P7P4p8p1006fp4p7210P4p8g007ej1GTg008Jk102Tg008hk10<Tg00U[j1\TP6k21=Tg00>cS00k10=Tg01B^k10lTg00e7j2=Tg014bj1VTg00FJk10LTg05Sbj3sTg00EjR6j1{Tg00?Ek300Tg00?ck20@Tg00;Lj3BTg03FQj1HTg00Qfj2OTg009Kj2NTg05T^lO1Tg00JBk106Tg05UPk10iTg03M@k20eTg01AAj2STg00T]j3?Tg016SR4j20Tg05VIj73Tg05W;k40:Tg01jGj2zTg05Wok410TP9k20>Tg00O;R9k10}Tg01eOk20WTg00B<j29Tg00ClS01j24Tg00P_k10wTg01m_k20[Tg00CPR7j2TTg01nGk30VTg007Ek10UTg00Fjj2}Tg01DFk10tTg00GHk10sTg00Gfk10rTg00HQj2vTg00Jdk20oTg00@ij2tTg00KFk20nTg00L2k30mTg00LQk40kTg05Y1k70jTg00R@j1rTg00R_k20TTg00T1k20ETg01fLk30STg00I4k20RTg027nk20DTg027Dk207Tg022Jk20hTg0233k30gTg01oWk30fTg00MCj1yTg00lgR<j2pTg05Yik30dTP1k604Tg01U=k20cTP3k60CTg05ZLmK0bmL0`Tg00P8k40OTg00QDk20NTg05Dok30BTg05[Mk70MTg05\Emo0aTg05]Fj1;Tg04K8k203Tg04C?j3MTg05^<k20;Tg05H7k51:Tg04AGk316Tg05_@m:15Tg05`Ek812Tg01S[j4jTg05JVk40ITg05a=k70~Tg02H;j4LTg05b6k40YTg04Pgk20|Tg03X7k40{Tg05bhk30XTg05cgj2~Tg04D3k30HTg00U=k40zTg01EGk30yTg00IWk40^Tg00X5k70\Tg01Ddk30xTg00Y=k711Tg00Yak80GTg00SHk30vTg00XYk613Tg00O[k214Tg00ZEm<0uTg00Zjm<17Tg00V@k718Tf0R3#\#Gp=w%G3#G#G#Gp=ig00;fR1f1R5;B3p=lf2R81z53'=p>0Ag00jXR2f4R=f3R;g02NoR01N85#H;?3CLp>0Jg00[OR:/93p=JA?053p>0qP2P;P8A?053CLp>0pP2P8P5P3H0Yp=C20|23p=Uf6R>f5R?%;=P;P8P5P3F3p=:P1P1P5P3H0{p=c1=53,z8,=;,N=p=5B0X;85#H=?03p=2P2P>P?1~=;#H=?08CL20;53'4p=>P2P=P;%H8=?05CL/43p=6B0H2=;1453,48'4p=7g057SS02?B?=AM;85/43'4p=8%G3#Gp>01%\3#\p>0?P2P=P;%H5=?039?08CLp>0ZP1P8P5P3H0zp=k20R13p=hB0y153p=uP8g00[mS03g00\LS04Q04g00\lS05P1P5g00`nP3H0^g00]LR@K0\p=@B0x153p=IP8Q03Q04Q04Q05P5P3K11p=XP;Q03Q04Q04Q05P8P5P3L0Gp=YP2P;P8P5H0Y/43p>0F20T13p=xB0v153p=qP1P5g00`GP3H0^p>09P5Q03Q04Q04Q05P3P@K0\p>08P>Q03Q04Q04Q05P?P=P;Q03Q04Q04Q05P8P5P3L0GL0Gp=bP5Q03Q04Q04Q05P3J13p>05P1P=P;P8P5P3J0Cp=E214:3p=gP1g00<iR@P1P1P6P=P9P;g00]lP8P5P3N<0up>0QP@P1P<P9P7g00n`P?P=P;P8P5P3N<17p>0P1953,O8p=]P8Q03Q04Q04Q05P5P3K18p=fQ02f7R7P>P?P=P;P8P5P3F33Bp=oB0H253p=KP2P7P>1=85,z;,==,N?#H=?03CLp=R1~85#H=?03p=|P2P8P5P3CLp=_203539B;8p=<1453,48p>0_AM;85/43,4=p=e1=85,z;,==,N?#H=?03p=QP2P=P;P8CL1453'4p>1<1453,48,4;,4=p=mP2P;P8P5CL/43p>0KP2P>P?1~=;#H=?08CL1453'4p=AP2P7P>1~?=#HB0X;85#H=?035?0CLp=W20;53,48,4;,4=,4?p=`Q02?B=;1453,48'4p=F1453,48,4;,4=,4?p=a203;8203535B=p=DAs;85/43p=PP2P?P=1~;8#H=?05CL/43p=^P2P;P8P5CL/43,4=,4?p=ZAM?=;B0H285/43'4p=nQ02?B85/43p=[P2P=P;P8CL20;53'4p>0]Q02?B53p>1;1453,48,4;p>19P>P?P=P;P8P5P3H0IH0Ip=dg00<DR9#GR<#GS06#GR6#GRA#GRB#GRC$02RD$0<RE%\<RF$02S0701=ERG&02B$0<&026$0<$0=\ERBp,1qS08%w6#i$0lRH'=RI%\9RJ#\#i#VRK'=RL,l?PLf8RMp,2APRNPDp,2VARO%V6R6<0A>&0L0R0I0Jf9RPp,5slotsRQ7sOS09&0=ERR%{M:00EQ20@E>3B%JPf<RSPL%H7%H>RT00q0H0pf=RUp,2loRV;CIf>RW#Ug04iaRX9B1Sg04j_RY9B1Sg04k]RZ9B1Sg04h>R[9B1S'O'O'OP2p,3RNGS0:Q02fAR\fmS0;1NDIR]p,2gpR^p,2tpR_f@R`f?RaPWfiS0<fhRbPUPSf;Rcf:RdPPPMP7P>fbS0=faS0>f`S0?f_S0@f^S0Af]S0Bf\S0Cf[S0DfZS0EfYS0FP?P=P;P8MO1P5Q0;fSS0G&06EReP3&0i2RfF:20e11Rg%VARA,SIRh/cIRi1=N6S0H,cN1=LAS0I,cL&0LgS0J5?gS0K5?g3?RjfRS0LP3Q0LP3%U3RkAC3VIRlP3PNPDPOP6fPS0M%V9RmD5P0P3PLfOS0NfNS0OQ0NQ0OfLS0PP0C2fTS0QP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWdS0RQ0DP]P^P_Q0EQ0FfXS0SfWS0TfVS0U1NDM1NDUS0V1NDNS0WfUS0XQ0QQ0GQ0LfQRnQ0MQ0NQ0OfMS0YQ0PfKS0ZfJS0[fIRofHS0\fGRpfFS0]fES0^fDS0_fCS0`MO1fBS0a%G9#w#w$01#\#w$01#\$0?#w$01#V,NDS0bP\PeP`PfF3H0:[[[[[[[[Xn1P7PNPD1z6?S0c,=OP0I0JAsMOQS0d%{7:00EQ20@E?5BR%JMPcPLPTP?P0I0ZACSVI%UUS0eAB1cXAB1cYAB1cZAB1c['O'O'OPaPOPQP>H10%JOS0f20>EQS0g$0}S0h:0AO6R[%V<RZ%VCRC+0WRY'9'4P2P`PVPhPIP;Q0g$0wS0iQ0h#JS0j%\F$0?RX#VRT-0[ZS0k1T:ZRq%JT20WZTRr,T:[[S0l%JZRsg01X4S0mB0VZT5UWeS0nQ0m%Jr[^esS0o20[ZCS0p%JC1T:Y[\qS0qQ0mB0VZC5UXesS0rQ0m%JY[^esS0sg00_[Rs$0LS0t&0UsS0u1}18S0v&0t1RC7k5Rq&0s1S0w&0r1RT1v19Rt1v1<S0x%GFS0y$01#\$01#i#VR<#hRu'u5@TS0zQ04$06S0{Q0x%hHS0|'IS0}%hARv'uS0~9@TtS10Q0~Q0}5@T5XTCYQ05-0oTS11P3P8g00_;Rwg00aURx't20n38=BwxdB0m1:5H0kS12bVbWbXXF1XJ11S5<S13,93S141=8HRx/SAS15,95S16Q15/9x'4[^F1^J1P3Q08PVp,2LOS17O3S18bUS19bgbQbRbSbTK0jP`PVPhAC`hIS1:H0FQ01AC\VhAC\hIS1;P2Q0:Q02P\foS1<P]P^P_P`PaPWfkRwfjS1=PUPSPcPdPPPMP7P>fdS1>fcS1?Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DP?P=P;P8MO1P5Q1<Q0XPeP3PfF:PjQ0QP3Q0QP3PkPlP3PNPDPOP6Q0LPmD5P0P3PLPnQ0MPnQ0MQ0OP0C2Q0UP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWdQ0BP]P^P_Q0CQ0DQ0EQ0FQ0S1NDLS1@1NDaQ0WQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZQ0[PoQ0\PpQ0]Q0^MO1Q0_Q0bQ0`PeQ0aPfF3H0:P3Q0`?CVhQ0_?ChIQ0iQ0jQ0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sg00bPRy#rRz#rS1A#x%xz20T1yS1B'q'qS1Cg00boRy+0EQ0t5?sS1DQ0uPqQ0wPT%hZRZ&02X60S1-09t-08TRXQ0{PT%w9#i$0?$0?#i#i#i#VR9#hQ0x5@TS1EQ0{PTQ0x1utu5@TS1FQ0{20R1:RzQ0|,ItR{5@TB0S1ZDRZ-09{-08T5XTCYFbQ11Q12bVbWbXXF1XJ11T3rS1G1998Rr1S8<,9;R|1=;HR}#J1T}Y'4[[[^F1^J1P3PVQ08p,3QHIp,3GLOS1HQ17O5S1IbUbgbQbRbSbT-0DI207D]R~/lIQ0iQ0jQ0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ1DQ0uPqQ0wPTPXQ0{PTQ1EQ0{PTQ1FQ0{%hKS1J,I{RX9@Tz209XZ-08T5XTCYFbQ11Q12bVbWbXXF1XJ1Q1G1=}KS1K#JQ1K/TY'4\|\r[^F1^J1Q1IbUbgbQbRbSbT-0DLQ1@-07DRr/lLQ0iQ0jQ0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sp-0R|Q1A#rS1A#xQ1C'q00Ey20h16Q1A#rS1A#rS1C#r#x60g1Q1C#xQ1A#xQ1B'q'q'q00EyQ0t5?s5?sQ0u1}1=1}1?7k81}1;S1B7k5Q0wPT%GJ,v1S1A9@TzQ0{PT205T7S1CQ06,v1Rs%h6RyQ1A60f1'I=@TZ5XTQ0{PT1Ity=@TsQ0{PT1v1JS1A=@TtQ0{PTQ1EQ0{PTQ0xQ1A/uu5@TQ0{A@TztRz209tZ-08T5XTFbFbFbQ11Q12bVbWbXXF1XJ1Xb1Xl1Xm1W]%J=Q0c,==/9Y,4>1=86RZ/9?19?;199?1S7<,9>%J>1T>Y'4[[[[[[^F1^J1^b1^l1^m1^]|P3Q0fQ0hPOQ08PVPNP?PUp,3HVAS0fp,3HAPS0cQ1HQ17O<bUbgbQbRbSbT-0DNQ0W-07DRY/lNg00b5p4p710R<&0U3RuQ01&0=8B00853&0683B#y20>;8,p5[RJ20>85,p3&0=;B00;85&06;3B#yRs[20>=;,p8\sB0d853P5n2001000000120000000Xp@WoWiPJ^p@^ou^i<P3PEPQ%{pR<PRQ0^-0@ERuABR3e#yZ0?RABRueRuPRQ0]-0@EQ00PEP|P3Q0mg01XPR@n10110?00021000000Z0<Rg01XmPeP3J04P@20c@3bxWH%yueB00EQ<PaJ0CO4bHQ0]#{Q0g'pP2Q0:Q1>P]P^P_Q0?Q0@Q0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0ZQ0[PrPYPOPQPpQ0]Q0^Q0`PoNK0bQ02P\fvS00P]P^P_P`PaPWfrS06fqS1IPUPSPcPdPPPMP7P>PwQ1=Q0<PbfgS1GffS1LfeS1MQ1>Q1?Q0=P?P=P;P8MO1P5Q00Q0CPeP3PfF:PjQ0DP3Q0DP3PkPlP3PNPDPOP6Q0FPmD5P0P3PLQ0SQ0TQ0SQ0TQ0XP0C2Q0BP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWdQ1>P]P^P_Q1?Q0=Q0>Q0?Q0@Q1@Q0],NDRuQ0WQ0AQ0BQ0CQ0DQ0EQ0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PMO1Q0ZQ0bQ0[PePoPfF3Q0:Q1>P]P^P_Q1?Q0=Q0>Q0?Q0@Q1@PuQ0WQ0AQ0BQ0CQ0DQ0EQ0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZQ0[PoPOPQPpQ0]Q0^Q0_Q0`PNQ0[P3PDQ0\:0AO6P0I0JXO1P\PYP5DEP`PaQ0g,p<%gpQ0h'TR@P<%g3Xh1S1NPpO1P3Xh1S1OQ1NPpPp1t1pI0QQ0gQ0hQ0h,t1S1PJ0PP3H0OR<P@Q0iQ0j20N:oRR1T:o%goRJ/lo'419o:AB1J:'4'ORJQ0[#gRsP1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ0tQ0u1}15S1QQ0wPTPzQ0{PzCYQ11Q12bVbWbXXF1%J3%J5[^F1P3Q0MPpO2bUbQbRbSb^b`b[bTb\PLQ0[P3Q0^#HQ0_P0I0ZXO1PUPrP8DEPIQ0[1S3ARz;C3XO1P=P~P;DEPc1tEuPdPI19A3XO1P<P@Q0iQ0jPRPJPsP1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ1DQ0uPqQ0wPTQ1EQ0{PTQ1FQ0{A@Tv{FbQ11Q12bVbWbXXF1XJ11995Q13,9819Ax[[^F1^J1P3PVQ08Q1HQ17O4bUbQbRbSb^b`b[bTb\P~P;DEPI193YXO1PN19I3XO1R9P<P@Q0iQ0jPRPJPsP1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ0tQ0uPqQ0wPTQ0x9@TtQ0{Q0x9@T{CYQ11Q12bVbWbXXF1XJ119351=5H/98[^F1^J1P3PNQ08Q0cO3bUbQbRbSb^b`b[bTb\PYP5DEP~P;DEPI193rXO1PLP9P<P@Q0iQ0jPRPJPsP1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ0tQ0uQ1QQ0wA@T{XQ11Q12bVbWbXXF11=3HRH1=HK'9^F1P3Q08O1bUbQbRbSb^b`b[bTb\PrP8DEP~P;DEPL1=Y6S1Q/931=3ARH;]YXO1PN1=36RX/9LQ0I;]3XO1P<P@Q0iQ0jPRPJPsP1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ0tQ0uPqQ0wPTQ0x=@TtQ0{205T=R{Q0}Q1J'IS0}/IvR9=@Tt5fTCYQ11Q12bVbWbXXF1XJ1X]|19531=xKS17/=ARx=];5[^F1^J1^]|P3Q0H/9LQ08PNQ0cO4bUbQbRbSb^b`b[bTb\PYP5DEPrP8DEPI19[z?]3OXO1P<P@Q0iQ0jPRPJPsP1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ1DQ0uQ1B?k8C9kC5S1HQ0wPT1v1FRF/Iy=@TtS13Q0{PTQ1A=@TFS1FQ0{205T?S1EQ1AQ0|'IRF=@Tt5fTFbQ11Q12bVbWbXXF1XJ1Xb1X]|19Z3RK198;RuA]?}8[[^F1^J1^b1^]|P319[hPNQ08POQ0fQ0cO6bUbQbRbSb^b`b[bTb\P~P;DEPN19[3R}?]XOXO1P<P@Q0iQ0jPRPJPsP1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ0tQ0uQ0v9kC5Q0wPTQ1A/Iy=@TtRyQ0{AfT{yCYQ11Q12bVbWbXXF1XJ1X]|1=56/93A];Z5[^F1^J1^]|P319[NPNPOQ0fO4bUbQbRbSb^b`b[bTb\PYP5DEPLA]}HOXO1P<P@Q0iQ0jPRPJPsP1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ1DQ0uQ1HQ0wPTQ13Q0{PTQ1FQ0{Q1EQ1J,IF/Iv=@Tt5fTFbQ11Q12bVbWbXXF1XJ1Xb1X]|Q1K/=A=]?8\u\K^F1^J1^b1^]|P319[LPNQ08POQ0fQ0cO6bUbQbRbSb^b`b[bTb\PrP8DEp,6RG_imgPIQ0:@0BzAXO1Q0:PVQ08/SVRzPhPAp,6RG_stkR[P<P@Q0iQ0jPRPJPsP1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ0tQ0uPqQ0wPTQ0zQ0{Q10Q0~/IvQ0x/ut,ItRv5@T5XTCYQ11Q12bVbWbXXF1XJ1Q14Q16Q15/=A1S85,=5RK'9'4[^F1^J1Q18bUbQbRbSb^b`b[bTb\K0MP~P;DEPNQ0:@0B36XO1p,5RG_apPYP5DEPLQ0:@0B3AXO1Q0:PVPzPLPAP[P<P@Q0iQ0jPRPJPsP1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ0tQ0uPqQ0wPTQ0zQ0{Q0}9@TtA@T9v5XTCYQ11Q12bVbWbXXF1XJ1Q14Q17,9519xK'4[^F1^J1Q18bUbQbRbSb^b`b[bTb\K0MPrP8DEp,5RG_vaNo0aQ02Q1MP]P^P_Q0>Q0?Q0EQ0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0PQ0ZPrPYPOPQQ0\PpQ0]Q0_Q0[P3NL0`S18P1P~Q0`fxR~P]P^P_P`PaPWftRKfsS14PUPSPcPdPPPMP7P>Q0;flS0zPwQ1=Q0<PbQ1GQ1LQ1MQ1>P?P=P;P8MO1P5%;~Q0APeP3PfGoRx1S\ARv/c\Q1Q,cYR91=rA,crQ0J5?g5?gRq5?gQ0BP3Q0B/K3RsP3PvP\P3PYPDPOP6Q0DPmP0GRRvQ0EQ0FQ0EQ0FQ0TP0C23|RJ9_3rAs3OQRRQ07$0<R@Q070073Q0y#V'l#yR<PE203;5R[Q0>P5C<[]1'4Rz40_H0F80_kDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EX_E,0EXaE,0EXcE,0EXO1P3PIP?J04Q0afwRuP]P^P_P`PaPWQ14Q06PUPSPcPdPPPMP7P>Q0zPwQ1=Q0<PbQ1GQ1LQ1MQ1>Q1?P?P=P;P8MO1P5%;uQ0BPeP3PfGoS0yA?giqQ0CP3Q0C/K3S07PkAC3hIRqPDPOP6Q0EPmP0EQS1Q9_3YP3PrQ0FQ0SQ0FQ0SQ0UP0C23|S16PRPEP[Q0?P5C<\<^1@I1<DmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EX_E,0EXaE,0EXcE,0EP1PrQ0_fyS10P]P^P_P`PaPWfuS0fPKPUPSPcPdPPPMP7P>fnS1KQ0;Q0zPwQ1=Q0<PbQ1GQ1LQ1MP?P=P;P8MO1P5Q10#;Q0@PeP3PfGoRr1=\A,c\Q0J5?g9?g99?giQ0AP3Q0A/K3RAPkPqPDPOP6Q0CPmP0EQRF9_3YP3P\Q0DQ0EQ0DQ0EQ0SP0C23|R}PEP[Q0=P5C<\<^1@,4RRHH0KDmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EX_E,0EXaE,0EXcE,0EXO1P3PLP?J04PxQ0K9?g99?giQ0BP3PsPkPqPvP3PLPJPzH0KDmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EX_E,0EXaE,0EXcE,0EP1PYQ0^fzRYP]P^P_P`PaPWQ00Q0fPUPSPcPdPPPMP7P>Q1<Q1KQ0;Q0zPwQ1=Q0<PbQ1GQ1LP?P=P;P8MO1P5%;YQ0?PeP3PfGoRz1=\6,c\Q0K5?g9?giQ0@P3Q0@/K3RiPkPqPDPOP6Q0BPmP0EQRg9_3\P3PLQ0CQ0DQ0CQ0DQ0FP0C2PRPEP[Q1?P5C<\<^1@FARJDmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EX_E,0EXaE,0EXcE,0EXO1P3PNP?J04PrPjQ0AP3PAPkPqA_3NFP3PLP}PHH0KDmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EX_E,0EXaE,0EXcE,0EP4PEPzPjQ0@P3PiPkPqA_3NgPJDmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EX_E,0EXaE,0EXcEQ0]f{RJP]P^P_P`PaPWPuQ00PUPSPcPdPPPMP7P>fpS0KQ1<Q1KQ0;Q0zPwQ1=Q0<PbQ1GP?P=P;P8MO1P5PJQ0>PeP3PfF:PjQ0?P3Q0?P3PkPlP3PNPDPOP6Q0APmD5P0P3PLQ0BQ0CQ0BQ0CQ0EP0C2Q0=P5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Ppf|S0JP]P^P_P`PaPWP~PuPUPSPcPdPPPMP7P>Q1IQ0KQ1<Q1KQ0;Q0zPwQ1=Q0<PbP?P=P;P8MO1P5Q0JQ0=PeP3PfF:PjQ0>P3Q0>P3PkPqP3PNPDPOP6Q0@PmD5P0P3PLQ0AQ0BQ0AQ0BQ0DP0C2PRPEP[Q1MP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EX_E,0EXaE,0EP4PEQ0\f}RgP]P^P_P\PaPWQ10P~PUPSPcPdPPPMP7P>Q06Q1IQ0KQ1<Q1KQ0;Q0zPwQ1=Q0<P?P=P;P8MO1P5PgQ1?PeP3PfF:PjQ0=P3Q0=P3PkPqP3PNPDPOP6Q0?PmD5P0P3PLQ0@Q0AQ0@Q0AQ0CP0C2PRPEP[Q1LP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EX_E,0EXaEQ0[p+01@RiP]P^P_P`PaPWPJPYPUPSPcPdPPPMP7P>PKQ14Q06Q1IQ0KQ1<Q1KQ0;Q0zPwP?P=P;P8MO1P5%;iRzQ1MPeP3PfF3Q1>=Mj3RHQ1>/K3R}PkPlP3PNPDPOP6Q0=PmP0GRRFP3PLQ0>Q0?Q0>Q0?Q0AP0GWRAQ1LP5E`DFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0[PiP]P^P_Q0`PaPWPJPYPUPSPcPdPPPMP7P>PKQ14Q06Q1IQ0KQ1<Q1KQ0;Q0zPwP?P=P;P8MO1P5PzQ1MPeP3PfF3PHP}PkPqPFPAPRPEP[PbP5C<\<^1@EaDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EX_E,0EP4PEQ0Zp+01ARAP]P^P_Q0_P`PWQ0JPJPUPSPcPdPPPMP7P>Q0fPKQ14Q06Q1IQ0KQ1<Q1KQ0;Q0zP?P=P;P8MO1P5PAQ1LPeP3PfF:PjQ1MP3Q1MP3PkPqP3PNPDPOP6Q1?PmD5P0P3PLQ0=Q0>Q0=Q0>Q0@P0C2PRPEP[Q0<P5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EX_EQ0Op+01DRFP]P^P_P`PaPWPif~S1JPUPSPcPdPPPMP7P>P~PuQ00Q0fPKQ14Q06Q1IQ0KQ1<P?P=P;P8MO1P5%;FR}Q0<PeP3PfF3AMjb3RH1Kb3RzPkPlP3PNPDPOP6Q1LPmP0GRRrP3PLQ1MQ1>Q1MQ1>Q0=P0GWRvQ1=P5E`DFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0Yp+01CRsP]P^P_Q0]Q0aPWQ1JPgPUPSPcPdPPPMP7P>PuQ00Q0fPKQ14Q06Q1IQ0KQ1<Q1KP?P=P;P8MO1P5PsPbPeP3PfF:PjQ1GP3Q1GP3PkPqP3PNPDPOP6Q1MPmD5P0P3PLQ1>Q1?Q1>Q1?Q0>P0C2PRPEP[PwP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZE,0EP4PEQ0OPFP]P^P_PpQ0`PaPiQ1JPUPSPcPdPPPMP7P>P~PuQ00Q0fPKQ14Q06Q1IQ0KQ1<P?P=P;P8MO1P5P}Q0<PeP3PfF3PHPzPkPqPrPvPRPEP[Q0zP5C<\<^1@EaDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EXZEQ0Lp+01HRvP]P^P_P`PaPWPFPsPUPSPcPdPPPMP7P>Q0JPJPYQ10P~PuQ00Q0fPKQ14P?P=P;P8MO1P5PvQ0;PeP3PfF:PjQ0zP3Q0zP3PkPlP3PNPDPOP6Q1=PmD5P0P3PLQ0<PbQ0<PbQ1LP0C2Q1KP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0Mp+01FS1FP]P^P_PoQ0^P\p+01BS13PAPUPSPcPdPPPMP7P>PYQ10P~PuQ00Q0fPKQ14Q06Q1IP?P=P;P8MO1P5Q1FPwPeP3PfF:PjQ1=P3Q1=P3PkPqP3PNPDPOP6PbPmD5P0P3PLQ1GQ1LQ1GQ1LQ1>P0C2PRPEP[Q1KP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYE,0EP4PEPnp+01GRrP]P^P_Q0[Q0]Q0aPsQ13PWPSPcPdPPPMP7P>PJPYQ10P~PuQ00Q0fPKQ14Q06P?P=P;P8MO1P5PrQ0zPeP3PfF:PjPwP3PwP3PkPqP3PNPDPOP6Q0<PmD5P0P3PLPbQ1GPbQ1GQ1MP0C2PRPEP[Q1<P5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EXYEQ0Up+01LRzP]P^P_P`PaPWPvPrPUPSPcPdPPPMP7P>PAPiQ1JPgQ0JPJPYQ10P~PuP?P=P;P8MO1P5%;zRHQ1IPeP3PfF3Q0K=Mj3R}Q0K/K3R9PkPlP3PNPDPOP6Q1KPmP0GRRxP3PLQ0;Q0zQ0;Q0zQ1=P0GWRZQ06P5E`DFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0Gp+01IRyP]P^P_Q0PQ0\Q0_p+01ES1HPFP`PSPcPdPPPMP7P>PgQ0JPJPYQ10P~PuQ00Q0fPKP?P=P;P8MO1P5PyQ1KPeP3PfF:PjQ0;P3Q0;P3PkPqP3PNPDPOP6PwPmD5P0P3PLQ1=Q0<Q1=Q0<Q1GP0C2PRPEP[Q1IP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPE,0EP4PEQ0Qp+01JR{P]P^P_Q0YPoQ0^Q1FQ1HP\PUPcPdPPPMP7P>Q1JPgQ0JPJPYQ10P~PuQ00Q0fP?P=P;P8MO1P5P{Q1<PeP3PfF:PjQ1KP3Q1KP3PkPqP3PNPDPOP6Q0zPmD5P0P3PLPwQ1=PwQ1=PbP0C2PRPEP[Q06P5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EXPEQ0Ep+01PRCP]P^P_P`PaPWPzp+01KS1DPUPSPcPdPPPMP7P>Q1HPFPsQ13PAPiQ1JPgQ0JPJP?P=P;P8MO1P5%;CS0|Q0fPeP3PfF3AMjK3S1R1KK3S1SPkPlP3PNPDPOP6Q06PmP0GRS1TP3PLQ1IQ0KQ1IQ0KQ1KP0GWRXQ00P5E`DFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0UPzP]P^P_Q0NQ0ZPpPvPrQ0`PaPcPdPPPMP7P>PAPiQ1JPgQ0JPJPYQ10P~PuP?P=P;P8MO1P5PHQ1IPeP3PfF3P}P9PkPqPxPZPRPEP[PKP5C<\<^1@EaDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNE,0EP4PEQ0Tp+01MRZP]P^P_Q0MQ0PQ0\PyPvQ0_P`PSPdPPPMP7P>Q13PAPiQ1JPgQ0JPJPYQ10P~P?P=P;P8MO1P5PZQ06PeP3PfF:PjQ1IP3Q1IP3PkPqP3PNPDPOP6Q1<PmD5P0P3PLQ1KQ0;Q1KQ0;PwP0C2PRPEP[Q0fP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EXNEQ0Ap+01TS1UP]P^P_P`PaPWPCp+01ORxPUPSPcPdPPPMP7P>PyPvPrQ1FQ1HPFPsQ13PAPiP?P=P;P8MO1P5Q1UQ10PeP3PfF:PjP~P3P~P3PkPlP3PNPDPOP6Q00PmD5P0P3PLQ0fPKQ0fPKQ06P0C2PYP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0FPxP]P^P_Q0LQ0OQ0[Q1DP{Q0]Q0aPWPdPPPMP7P>PFPsQ13PAPiQ1JPgQ0JPJPYP?P=P;P8MO1P5PxPKPeP3PfF:PjQ14P3Q14P3PkPqP3PNPDPOP6Q1IPmD5P0P3PLQ0KQ1<Q0KQ1<Q0;P0C2PRPEP[PuP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXME,0EP4PEQ0EPCP]P^P_Q0GQ0NQ0ZPzQ1DPpQ0`PaPcPPPMP7P>Q1HPFPsQ13PAPiQ1JPgQ0JPJP?P=P;P8MO1P5Q0|Q0fPeP3PfF3Q1RQ1SPkPqQ1TPXPRPEP[P~P5C<\<^1@EaDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EXMEQ0=p+01XS1TP]P^P_P`PaPWQ1Up+01SRXPUPSPcPdPPPMP7P>PZPzQ1DP{PyPvPrQ1FQ1HPFP?P=P;P8MO1P5Q1T#;S1SPgPeP3PfF3Q0J=Mj3S1RQ0J/K3S0|PkPlP3PNPDPOP6PYPmP0GRS1VP3PLQ10P~Q10P~Q00P0GWS1WQ1JP5E`DFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0Cp+01RS1XP]P^P_Q0XPnQ0Yp+01NR9PZPoQ0^P\PUPPPMP7P>PrQ1FQ1HPFPsQ13PAPiQ1JPgP?P=P;P8MO1P5Q1XPuPeP3PfF:PjQ00P3Q00P3PkPqP3PNPDPOP6PKPmD5P0P3PLQ14Q06Q14Q06Q0KP0C2PRPEP[PYP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLE,0EP4PEQ0BPXP]P^P_Q0UQ0LQ0OPxP9Q0[Q0]Q0aPWPdPMP7P>PvPrQ1FQ1HPFPsQ13PAPiQ1JP?P=P;P8MO1P5PXP~PeP3PfF:PjPuP3PuP3PkPqP3PNPDPOP6Q0fPmD5P0P3PLPKQ14PKQ14Q1IP0C2PRPEP[PJP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EXLEQ1Lp+01\S1YP]P^P_P`PaPWQ1Tp+01WR}PUPSPcPdPPPMP7P>p+01QS1ZPCPxP9PZPzQ1DP{PyPvP?P=P;P8MO1P5Q1Y#;S1[Q13PeP3PfF3AMjA3S1\1KA3S1]PkPlP3PNPDPOP6Q1JPmP0GRS1^P3PLPgQ0JPgQ0JPYP0GWS1_PsP5E`DFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0@p+01US1`P]P^P_Q0SQ0QQ0MQ1ZPCQ0PQ0\Q0_P`PSPMP7P>P{PyPvPrQ1FQ1HPFPsQ13PAP?P=P;P8MO1P5Q1`PYPeP3PfF:PjQ10P3Q10P3PkPqP3PNPDPOP6PuPmD5P0P3PLQ00Q0fQ00Q0fQ14P0C2PRPEP[PgP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKE,0EP4PEQ0?p+01VRHP]P^P_Q0FQ0XPnQ1XQ1ZQ0YPoQ0^P\PUPPP7P>Q1DP{PyPvPrQ1FQ1HPFPsQ13P?P=P;P8MO1P5PHPJPeP3PfF:PjPYP3PYP3PkPqP3PNPDPOP6P~PmD5P0P3PLPuQ00PuQ00PKP0C2PRPEP[Q1JP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EXKEQ1=p+01`S1aP]P^P_P`PaPWQ1Yp+01[S1bPUPSPcPdPPPMP7P>Q1`Q1UPXQ1XQ1ZPCPxP9PZPzP?P=P;P8MO1P5Q1aQ1FPeP3PfF:PjQ1HP3Q1HP3PkPlP3PNPDPOP6PsPmD5P0P3PLQ13PAQ13PAQ1JP0C2PrP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0=Q1TP]P^P_Q0DQ0TQ0GQ1UPXQ0NQ0ZPpQ0`PaPcP7P>PZPzQ1DP{PyPvPrQ1FQ1HPFP?P=P;P8MO1P5Q1SPgPeP3PfF3Q1RQ0|PkPqQ1VQ1WPRPEP[PAP5C<\<^1@EaDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIE,0EP4PEQ1?p+01YS1WP]P^P_Q0CQ0SQ0QQ1`Q1UQ0MQ0PQ0\Q0_P`PSPMP>P9PZPzQ1DP{PyPvPrQ1FQ1HP?P=P;P8MO1P5Q1WQ1JPeP3PfF:PjPgP3PgP3PkPqP3PNPDPOP6PJPmD5P0P3PLPYQ10PYQ10PuP0C2PRPEP[Q13P5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EXIEQ1Kp+01dS1VP]P^P_P`PaPWQ1ap+01_S0|PUPSPcPdPPPMP7P>Q1WQ1TP}PHQ1`Q1UPXQ1XQ1ZPCP?P=P;P8MO1P5Q1V#;S1RP{PeP3PfF3AMjy3S1S1Ky3S1cPkPlP3PNPDPOP6PrPmP0GRS1dP3PLQ1FQ1HQ1FQ1HPsP0GWS1eQ1DP5E`DFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q1MQ1bP]P^P_Q0AQ0EQ0UP}PHQ0LQ0OQ0[Q0]Q0aPWPdP>PCPxP9PZPzQ1DP{PyPvPrP?P=P;P8MO1P5Q1bPAPeP3PfF:PjPiP3PiP3PkPqP3PNPDPOP6PgPmD5P0P3PLQ0JPJQ0JPJQ10P0C2PRPEP[PFP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGE,0EP4PEQ1LQ1YP]P^P_Q0@Q0DQ0TQ1TP}Q0GQ0NQ0ZPpQ0`PaPcP7Q1ZPCPxP9PZPzQ1DP{PyPvP?P=P;P8MO1P5Q1[Q13PeP3PfF3Q1\Q1]PkPqQ1^Q1_PRPEP[Q1HP5C<\<^1@EaDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXGEQ06p+01hS1_P]P^P_P`PaPWQ1Vp+01cS1^PUPSPcPdPPPMP7P>p+01]S1]Q1YQ1bp+01ZS1\Q1WQ1TP}PHQ1`Q1UP?P=P;P8MO1P5Q1_#;S1[P9PeP3PfF3AMjZ3S1f1KZ3S1gPkPlP3PNPDPOP6Q1DPmP0GRS1hP3PLP{PyP{PyPrP0GWS1iPxP5E`DFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Pbp+01^S1jP]P^P_Q0>Q0BQ0FQ1\Q1WQ0XPnQ0YPoQ0^P\PUPPPXQ1XQ1ZPCPxP9PZPzQ1DP{P?P=P;P8MO1P5Q1jPFPeP3PfF:PjPsP3PsP3PkPqP3PNPDPOP6PAPmD5P0P3PLPiQ1JPiQ1JQ0JP0C2PRPEP[PrP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EP4PEQ0<Q0|P]P^P_Q0=Q0AQ0EQ1bQ1\Q0UQ0LQ0OQ0[Q0]Q0aPWPdQ1UPXQ1XQ1ZPCPxP9PZPzQ1DP>P=P;P8MO1P5Q0|Q1HPeP3PfF:PjPFP3PFP3PkPqP3PNPDPOP6Q13PmD5P0P3PLPAPiPAPiPgP0C2PRPEP[PvP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEEQ00p+01lS1kP]P^P_P`PaPWQ1_p+01gS1lPUPSPcPdPPPMP7P>p+01aS1mQ1aQ0|Q1jQ1]Q1YQ1bQ1\Q1WQ1TP?P=P;P8MO1P5Q1kQ1XPeP3PfF:PjQ1ZP3Q1ZP3PkPlP3PNPDPOP6PxPmD5P0P3PLP9PZP9PZQ1DP0C2PXP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3PwQ1mP]P^P_Q1>Q0?Q0CQ1]Q1YQ0SQ0QQ0MQ0PQ0\Q0_P`PSPHQ1`Q1UPXQ1XQ1ZPCPxP9PZPMP=P;P8MO1P5Q1mPrPeP3PfF:PjQ1FP3Q1FP3PkPqP3PNPDPOP6PFPmD5P0P3PLPsQ13PsQ13PiP0C2PRPEP[P{P5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCE,0EP4PEQ0zp+01bS1nP]P^P_Q1MQ0>Q0BQ1jQ1]Q0FQ0XPnQ0YPoQ0^P\PUP}PHQ1`Q1UPXQ1XQ1ZPCPxP9PPP?P;P8MO1P5Q1nPvPeP3PfF:PjPrP3PrP3PkPqP3PNPDPOP6Q1HPmD5P0P3PLPFPsPFPsPAP0C2PRPEP[Q1DP5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@E,0EXCEPYp+020S1oP]P^P_P`PaPWQ1kp+01kS1pPUPSPcPdPPPMP7P>p+01eS1qQ1VQ1^Q1nQ1mQ1aQ0|Q1jQ1]Q1YP?P=P;P8MO1P5Q1o#;S1rPHPeP3PfF3PjQ1`P3Q1`P3PkPlP3PNPDPOP6PXPmD5P0P3PLQ1XQ1ZQ1XQ1ZPxP0C2P}P5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q1KQ1VP]P^P_Q1GQ1?Q0@Q1aQ0|Q0DQ0TQ0GQ0NQ0ZPpQ0`PaQ1WQ1TP}PHQ1`Q1UPXQ1XQ1ZPCPcP7P;P8MO1P5Q1RP{PeP3PfF3Q1SQ1cPkPqQ1dQ1ePRPEP[PZP5C<\<^1@EaDFX0B,0BX<G,0GX@E,0EP4PEQ1<Q1qP]P^P_PbQ1>Q0?Q1mQ1aQ0CQ0SQ0QQ0MQ0PQ0\Q0_P`Q1\Q1WQ1TP}PHQ1`Q1UPXQ1XQ1ZPSPMP=P8MO1P5Q1qQ1DPeP3PfF:PjP{P3P{P3PkPqP3PNPDPOP6PvPmD5P0P3PLPrQ1FPrQ1FPFP0C2PRPEP[P9P5C<\<^1@FAD6D7E8X0B,0BX<G,0GX@EQ1Jp+024S1eP]P^P_P`PaPWQ1op+01oS1dPUPSPcPdPPPMP7P>p+01iS1cQ1_Q1lp+01fS1SQ1qQ1VQ1^Q1nQ1mQ1aP?P=P;P8MO1P5Q1eQ1\PeP3PfF:PjQ1WP3Q1WP3PkPlP3PNPDPOP6P}PmD5P0P3PLPHQ1`PHQ1`PXP0C2Q1bP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q1IQ1lP]P^P_Q1=Q1LQ0=Q1^Q1nQ0AQ0EQ0UQ0LQ0OQ0[Q0]Q0aQ1YQ1bQ1\Q1WQ1TP}PHQ1`Q1UPXPWPdP>P8MO1P5Q1lPZPeP3PfF:PjPzP3PzP3PkPqP3PNPDPOP6P{PmD5P0P3PLPyPvPyPvQ1FP0C2PRPEP[PCP5C<\<^1@FAD6D7E8X0B,0BX<G,0GP4PGQ06Q1_P]P^P_PwQ1GQ1?Q1VQ1^Q0@Q0DQ0TQ0GQ0NQ0ZPpQ0`Q1]Q1YQ1bQ1\Q1WQ1TP}PHQ1`Q1UPaPcP7P;MO1P5Q1[P9PeP3PfF3Q1fQ1gPkPqQ1hQ1iPRPEP[Q1ZP5C<\<^1@EaDFX0B,0BX<GPsp+028S1iP]P^P_P`PaPWQ1ep+023S1hPUPSPcPdPPPMP7P>p+01mS1gQ1kQ1pp+01jS1fQ1cQ1_Q1lQ1SQ1qQ1VP?P=P;P8MO1P5Q1iQ1jPeP3PfF:PjQ1]P3Q1]P3PkPlP3PNPDPOP6Q1bPmD5P0P3PLQ1\Q1WQ1\Q1WP}P0C2Q0|P5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3PKQ1fP]P^P_Q0;Q0<Q1MQ1SQ1qQ0>Q0BQ0FQ0XPnQ0YPoQ0^Q0|Q1jQ1]Q1YQ1bQ1\Q1WQ1TP}PHP\PUPPP?MO1P5Q1fPCPeP3PfF:PjPxP3PxP3PkPqP3PNPDPOP6PZPmD5P0P3PLPzQ1DPzQ1DPyP0C2PRPEP[PXP5C<\<^1@FAD6D7E8X0B,0BP4PBQ0fQ1pP]P^P_Q1KQ1=Q1LQ1lQ1SQ0=Q0AQ0EQ0UQ0LQ0OQ0[Q0]Q1aQ0|Q1jQ1]Q1YQ1bQ1\Q1WQ1TP}Q0aPWPdP>MO1P8Q1pQ1ZPeP3PfF:PjPCP3PCP3PkPqP3PNPDPOP6P9PmD5P0P3PLPZPzPZPzP{P0C2PRPEP=P5Q1UP5DD\<^1@FAD6D7E8X0BPrp+02<S1[P]P^P_P`PaPWQ1ip+027S1RPUPSPcPdPPPMP7P>p+021S1sQ1oQ1dp+01nS1tQ1gQ1kQ1pQ1fQ1cQ1_P?P=P;P8MO1P5Q1[Q1nPeP3PfF:PjQ1mP3Q1mP3PkPlP3PNPDPOP6Q0|PmD5P0P3PLQ1jQ1]Q1jQ1]Q1bP0C2Q1^P5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3PuQ1gP]P^P_Q0KQ0zPbQ1cQ1_Q1>Q0?Q0CQ0SQ0QQ0MQ0PQ0\Q1nQ1mQ1aQ0|Q1jQ1]Q1YQ1bQ1\Q1WQ0_P`PSPMMO1P=Q1gPXPeP3PfF:PjQ1XP3Q1XP3PkPqP3PNPDPOP6PCPmD5P0P3PLPxP9PxP9PzP0C2PRPEP>P5PHP5DD\<^1@FAD6D7E8Q01P~Q1tP]P^P_Q1IQ0;Q0<Q1fQ1cQ1MQ0>Q0BQ0FQ0XPnQ0YPoQ1^Q1nQ1mQ1aQ0|Q1jQ1]Q1YQ1bQ1\Q0^P\PUPPMO1P?Q1t#;Q1UPeP5PfGoPjPXP5PXP5%U5AC5hIP5PNPDPOP6Q1ZPmP0EQP5PLPCPxPCPxPZP0C2P5POPQPEP7P5P}P5DD\<^1@CPE^EZEnQ1Dp+02@RRP]P^P_P`PaPWQ1[p+02;S1uPUPSPcPdPPPMP7P>p+025S1vQ1eQ1hp+022S1wQ1sQ1oQ1dQ1tQ1gQ1kP?P=P;P8MO1P5PRQ1SPeP3PfF:PjQ1qP3Q1qP3PkPlP3PNPDPOP6Q1^PmD5P0P3PLQ1nQ1mQ1nQ1mQ0|P0C2Q1lP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3PYQ1oP]P^P_Q14Q1<PwQ1kQ1pQ1GQ1?Q0@Q0DQ0TQ0GQ0NQ0ZQ1qQ1VQ1^Q1nQ1mQ1aQ0|Q1jQ1]Q1YPpQ0`PaPcMO1P7Q1rPHPeP;PfGoQ02Q1sP]P^P_PKQ0KQ0zQ1gQ1kPbQ1>Q0?Q0CQ0SQ0QQ0MQ0PQ1SQ1qQ1VQ1^Q1nQ1mQ1aQ0|Q1jQ1]Q0\Q0_P`PSMO1PMQ1sP}PeP=PfF:Q02AMj}?S1kP}P?%U?AC?hIP?PNPDPOP6Q1`PmD5P0P?PLQ1UPXQ1UPXQ1ZP0C2P?POPQPEPcP5Q1bP5DD\<^1@CPE^D6D7S1r'4Q0ap+02DRqP]P^P_P`PaPWPRp+02?S1xPUPSPcPdPPPMP7P>p+029S1yQ1iQ1Rp+026S1zQ1vQ1eQ1hQ1wQ1sQ1oP?P=P;P8MO1P5%;qS1{Q1fPeP3PfF3R4PjQ1cP3Q1cP3PkPlP3PNPDPOP6Q1lPmP0EQS1|P3PLQ1SQ1qQ1SQ1qQ1^P0C2Q1pP5F>EZEnR[3[X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0E[WdPjPHP=PHP=%U=AC=hIP=PNPDPOP6Q1UPmP0EQP=PLPXQ1XPXQ1XPCP0C2P=POPQPEPdP5Q1\P5DD\<^1@CPE^EZEnQ01Q1kQ1rPqP]P^P_PvPFPiPRQ1xPJPuQ14Q1<PwQ1GQ1?Q0@Q1yQ1iQ1RQ1zQ1vQ1eQ1hQ1wQ1sQ1oQ0DQ0TQ0GQ0NMO1Q0ZQ1{Q1fPePpPfF3?[4[X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q1W=Mj7Q1\PM%UMACMhIPMPNPDPOP6Q1TPmD5P0PMPLP}PHP}PHQ1UP0C2Q0dPEPWP5Q1jP5DD\<^1@FAD6D7Q01Q1b/KP%UPACPhIPPPNPDPOP6Q1WPmP0EQPPPLQ1TP}Q1TP}Q1`P0C2Q09PEPaP5Q0|P5DD\<^1@FAEZp+02HR[P]P^P_PzPvPFPqp+02CS09PiPJPuQ14Q1<PwQ1GQ1?p+02=S0dQ1[Q1up+02:S1{Q1yQ1iQ1RQ1zQ1vQ1eQ0@Q0DQ0TQ0GMO1Q0N%;[R4Q1tPeQ0ZPfF3P[P]P^P_P`PaPWPqQ09PUPSPcPdPPPMP7P>Q0dQ1[Q1uQ1{Q1yQ1iQ1RQ1zQ1vQ1eP?P=P;P8MO1P5P4Q1tPeP3PfF3PjQ1gP3Q1gP3PkPlP3PNPDPOP6Q1pPmD5P0P3PLQ1fQ1cQ1fQ1cQ1lP0C23|S1cQ1dP5I0]D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q1]/Kc%USACShIPSPNPDPOP6Q1YPmP0EQPSPLQ1bQ1\Q1bQ1\Q1TP0C2PSPOPQPEQ0aP5Q1nP5DD\<^1@CPE^EZQ01Q0ePUPhPIPUPNPDPOP6Q1]PmD5P0PUPLQ1YQ1bQ1YQ1bQ1WP0C2PUPOPQPEQ0`P5Q1^P5DD\<^1@CPE^D6H0Fp+02LR4P]P^P_PCPzPvP[p+02GS0ePFPiPJPuQ14Q1<PwQ1Gp+02AS1rPRQ1xp+02>S1kQ0dQ1[Q1uQ1{Q1yQ1iQ1?Q0@Q0DQ0TMO1Q0G%;4S1}Q1wPeQ0NPfF3P4P]P^P_P`PaPWP[Q0ePUPSPcPdPPPMP7P>Q1rPRQ1xQ1kQ0dQ1[Q1uQ1{Q1yQ1iP?P=P;P8MO1P5Q1}Q1wPeP3PfF3PjQ1sP3Q1sP3PkPlP3PNPDPOP6Q1dPmD5P0P3PLQ1tQ1gQ1tQ1gQ1pP0C2Q1hP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3%UaQ1:P`PNPDPOP6Q1aPmP0GRP`PLQ0|Q1jQ0|Q1jQ1YP0C23|P`POPQPEQ0]P5Q1SP5DD\<^1@CPEZQ01Q1;P\PNPDPOP6Q1mPmD5P0P\PLQ1aQ0|Q1aQ0|Q1]P0C2P\POPQPEPpP5Q1lP5DD\<^1@CPE^D6p+02PS1;P]P^P_Q1UPCPzP4p+02KS1:PvPFPiPJPuQ14Q1<Pwp+02ES1}PqQ09p+02BS1~Q1rPRQ1xQ1kQ0dQ1[Q1GQ1?Q0@Q0DMO1S20Q0TQ1;#;S21Q1zPeQ0GPfF3S22Q1;P]P^P_P`PaPWP4Q1:PUPSPcPdPPPMP7P>Q1}PqQ09Q1~Q1rPRQ1xQ1kQ0dQ1[P?P=P;P8MO1P5Q21Q1zPeP3PfF3PjQ1vP3Q1vP3PkPlP3PNPDPOP6Q1hPmP0EQP3PLQ1wQ1sQ1wQ1sQ1dP0C2Q1RP5F>EZEnS233[X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0`?ChIQ0_PNPDPOP6Q1VPmD5P0Q0_PLQ1^Q1nQ1^Q1nQ1aP0C2Q0_POPQPEQ0[P5Q1fP5DD\<^1@CPE^D6Q01Q0^PNPDPOP6Q1qPmP0GRQ0^PLQ1VQ1^Q1VQ1^Q1mP0C2Q0^POPQPEQ0ZP5Q1pP5DD\<^1@CPE^p+02TS1pP]P^P_Q1TQ1UPCQ1;p+02OS1fPzPvPFPiPJPuQ14Q1<p+02IS24P[Q0ep+02FS25Q1}PqQ09Q1~Q1rPRPwQ1GQ1?Q0@MO1Q0DQ1p#;S26Q1{PeQ0TPfF3S27Q1pP]P^P_P`PaPWQ1;Q1fPUPSPcPdPPPMP7P>Q24P[Q0eQ25Q1}PqQ09Q1~Q1rPRP?P=P;P8MO1P5Q26Q1{PeP3PfF3PjQ1yP3Q1yP3PkPlP3PNPDPOP6Q1RPmP0EQP3PLQ1zQ1vQ1zQ1vQ1hP0C2Q1uP5F>EZEnS283[X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q1|9_pNQ0\PLQ1lQ1SQ1lQ1SQ1VP0C2Q0\POPQPEQ0OP5Q1tP5DD\<^1@CPE^Q01PoPLQ1_Q1lQ1_Q1lQ1qP0GWPoPOPQPEQ0NP5Q1dP5DD\<^1@CPp+02XS1qP]P^P_Q1YQ1TQ1UQ1pp+02SS1lPCPzPvPFPiPJPuQ14p+02MS1_P4Q1:p+02JS1VQ24P[Q0eQ25Q1}PqQ1<PwQ1GQ1?MO1Q0@Q1q#;S1SQ1kPeQ0DPfF3S1|Q1qP]P^P_P`PaPWQ1pQ1lPUPSPcPdPPPMP7P>Q1_P4Q1:Q1VQ24P[Q0eQ25Q1}PqP?P=P;P8MO1P5Q1SQ1kPeP3PfF3PjQ0dP3Q0dP3PkPlP3PNPDPOP6Q1uPmP0EQP3PLQ1{Q1yQ1{Q1yQ1RP0C2Q1xP5F>EZEnS293[X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0ZQ1c7_LQ0PPOPQPEQ0LP5Q1wP5DD\<^1@CPQ01Q0Y?sOQPEQ0GP5Q1hP5DD\<^1@p+02\S01P]P^P_Q1aQ1YQ1TQ1qp+02WS1cQ1UPCPzPvPFPiPJPup+02QS2:Q1;Q1fp+02NS2;Q1_P4Q1:Q1VQ24P[Q14Q1<PwQ1GMO1Q1?Q01#;S1?Q1~PeQ0@PfF3S2<Q01P]P^P_P`PaPWQ1qQ1cPUPSPcPdPPPMP7P>Q2:Q1;Q1fQ2;Q1_P4Q1:Q1VQ24P[P?P=P;P8MO1P5Q1?Q1~PeP3PfF3PjQ1rP3Q1rP3PkPlP3PNPDPOP6Q1xPmP0EQP3PLQ1kQ0dQ1kQ0dQ1uP0C2Q09P5F>EZEnS2=3[X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP3Q0N?sOQPEQ0UP5Q1zP5DD\<^1@PEp+02_R@P]P^P_Q1^Q0|Q1bp+02[R<p+02ZS1^P}PXPxQ1DPrPsQ1JPYQ1pQ1lp+02RRQQ2:Q1;Q1fQ2;Q1_P4Q1:Q00Q06Q1KQ1=MO1Q1L%;@RwQ1}PeQ0=PfF3P@P]P^P_P`PaPWP<Q1^PUPSPcPdPPPMP7P>Q1pQ1lPQQ2:Q1;Q1fQ2;Q1_P4Q1:P?P=P;P8MO1P5PwQ1}PeP3PfF3PjPqP3PqP3PkPlP3PNPDPOP6Q1~PmD5P0P3PLQ1rPRQ1rPRQ1kP0C2Q25P5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDEQ1XPEp+02^RwP]P^P_Q1nQ1jQ1\Q1^p+02YR@PHQ1XP9P{Q1FQ13PgQ10Q1lPQQ2:Q1;Q1fQ2;Q1_P4Q1:Q1VQ0fQ1IQ0;Q0<MO1Q1M%;wS2>PqPeQ0>PfF3PwP]P^P_Q1nPaPWQ1^P@PUPSPcPdPPPMP7P>Q1lPQQ2:Q1;Q1fQ2;Q1_P4Q1:Q1VP?P=P;P8MO1P5Q2>PqPeP3PfF3PjQ09P3Q09P3PkPlP3PNPDPOP6Q1rPmD5P0P3PLPRQ1xPRQ1xQ0dP0C2Q1}P5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBEP9PEp+02]RwP]P^P_Q1mQ1]Q1WP@Q1qQ1`Q1ZPZPyQ1HPAQ0JP~PQQ2:Q1;Q1fQ2;Q1_P4Q1:Q1VQ24PKQ0KQ0zPbMO1Q1>%;wS2>Q09PeQ0?PfF3PwP]P^P_Q1mQ1]PWP@Q1qPUPSPcPdPPPMP7P>PQQ2:Q1;Q1fQ2;Q1_P4Q1:Q1VQ24P?P=P;P8MO1P5Q2>Q09PeP3PfF3PjQ1~P3Q1~P3PkPlP3PNPDPOP6PRPmD5P0P3PLQ1xQ1kQ1xQ1kQ1[P0C2PqP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAEP{PEQ2<Q01P]P^P_Q1aQ1YQ1TQ1qQ1cPUPSPcPdPPPMP7P>Q2:Q1;Q1fQ2;Q1_P4Q1:Q1VQ24P[P?P=P;P8MO1P5Q1?Q1~PeP3PfF3Q2=3[X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?EQ1FPEP<P]P^P_Q0|Q1bP}Q1cp+02VRwPXPxQ1DPrPsQ1JPYQ00Q1;Q1fQ2;Q1_P4Q1:Q1VQ24P[Q0eQ06Q1KQ1=Q1LMO1Q0=%;<S2=Q1rPeQ0APfF3P<P]P^P_Q0|Q1bP}Q1cPwPXPSPcPdPPPMP7P>Q1;Q1fQ2;Q1_P4Q1:Q1VQ24P[Q0eP?P=P;P8MO1P5Q2=Q1rPeP3PfF3PjPRP3PRP3PkPlP3PNPDPOP6Q1kPmD5P0P3PLQ0dQ1[Q0dQ1[Q1{P0C2Q1~P5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>EQ13PEQ1^P]P^P_Q1jQ1\PHPwp+02UR<Q1XP9P{Q1FQ13PgQ10Q0fQ1fQ2;Q1_P4Q1:Q1VQ24P[Q0eQ25Q1IQ0;Q0<Q1MMO1Q0>Q1^#;S2=PRPeQ0BPfF3Q1^P]P^P_Q1jQ1\PHPwP<Q1XP9PcPdPPPMP7P>Q1fQ2;Q1_P4Q1:Q1VQ24P[Q0eQ25P?P=P;P8MO1P5Q2=PRPeP3PfF3PjQ1xP3Q1xP3PkPlP3PNPDPOP6Q0dPmD5P0P3PLQ1[Q1uQ1[Q1uQ1yP0C2Q1rP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=EPgPEP@P]P^P_Q1]Q1WQ1`P<Q1pQ1ZPZPyQ1HPAQ0JP~PKQ2;Q1_P4Q1:Q1VQ24P[Q0eQ25Q1}Q0KQ0zPbQ1>MO1Q0?%;@S2=Q1xPeQ0CPfF3P@P]P^P_Q1]Q1WQ1`P<Q1pQ1ZPZPyPdPPPMP7P>Q2;Q1_P4Q1:Q1VQ24P[Q0eQ25Q1}P?P=P;P8MO1P5Q2=Q1xPeP3PfF3PjQ1kP3Q1kP3PkPlP3PNPDPOP6Q1[PmD5P0P3PLQ1uQ1{Q1uQ1{Q1iP0C2PRP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;EQ10PEQ1|Q1qP]P^P_Q1YQ1TQ1UQ1pQ1lPCPzPvPFPPPMP7P>Q1_P4Q1:Q1VQ24P[Q0eQ25Q1}PqP?P=P;P8MO1P5Q1SQ1kPeP3PfF3Q293[X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:EQ0fPEQ1cP]P^P_Q1bP}PXQ1lPQPxQ1DPrPsQ1JPYQ00Q06P4Q1:Q1VQ24P[Q0eQ25Q1}PqQ09Q1KQ1=Q1LQ0=MO1Q0AQ1c#;R@Q0dPeQ0EPfF3Q1cP]P^P_Q1bP}PXQ1lPQPxQ1DPrPsQ1JPMP7P>P4Q1:Q1VQ24P[Q0eQ25Q1}PqQ09P?P=P;P8MO1P5P@Q0dPeP3PfF3PjQ1[P3Q1[P3PkPlP3PNPDPOP6Q1{PmD5P0P3PLQ1yQ1iQ1yQ1iQ1zP0C2Q1kP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9EQ1IPEPwP]P^P_Q1\PHQ1XPQQ2:P9P{Q1FQ13PgQ10Q0fQ1IQ1:Q1VQ24P[Q0eQ25Q1}PqQ09Q1~Q0;Q0<Q1MQ0>MO1Q0B%;wR@Q1[PeQ0FPfF3PwP]P^P_Q1\PHQ1XPQQ2:P9P{Q1FQ13PgQ10P7P>Q1:Q1VQ24P[Q0eQ25Q1}PqQ09Q1~P?P=P;P8MO1P5P@Q1[PeP3PfF3PjQ1uP3Q1uP3PkPlP3PNPDPOP6Q1yPmD5P0P3PLQ1iQ1RQ1iQ1RQ1vP0C2Q0dP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8EQ0;PEP<P]P^P_Q1WQ1`Q1ZQ2:Q1;PZPyQ1HPAQ0JP~PKQ0KQ1VQ24P[Q0eQ25Q1}PqQ09Q1~Q1rQ0zPbQ1>Q0?MO1Q0C%;<R@Q1uPeQ0SPfF3P<P]P^P_Q1WQ1`Q1ZQ2:Q1;PZPyQ1HPAQ0JP~PKP>Q1VQ24P[Q0eQ25Q1}PqQ09Q1~Q1rP?P=P;P8MO1P5P@Q1uPeP3PfF3PjQ1{P3Q1{P3PkPlP3PNPDPOP6Q1iPmD5P0P3PLQ1RQ1zQ1RQ1zQ1eP0C2Q1[P5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7EQ0<PEQ27Q1pP]P^P_Q1TQ1UPCQ1;Q1fPzPvPFPiPJPuQ14Q1<Q24P[Q0eQ25Q1}PqQ09Q1~Q1rPRP?P=P;P8MO1P5Q26Q1{PeP3PfF3Q283[X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6EQ1MPEQ1lP]P^P_P}PXPxQ1fQ2;Q1DPrPsQ1JPYQ00Q06Q1KP[Q0eQ25Q1}PqQ09Q1~Q1rPRQ1xQ1=Q1LQ0=Q0AMO1Q0EQ1l#;RuQ1yPeQ0UPfF3Q1lP]P^P_P}PXPxQ1fQ2;Q1DPrPsQ1JPYQ00Q06Q1KP[Q0eQ25Q1}PqQ09Q1~Q1rPRQ1xQ1=P=P;P8MO1P5PuQ1yPeP3PfF3PjQ1iP3Q1iP3PkPlP3PNPDPOP6Q1zPmD5P0P3PLQ1vQ1eQ1vQ1eQ1wP0C2Q1{P5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5EQ0>PEPQP]P^P_PHQ1XP9Q2;Q1_P{Q1FQ13PgQ10Q0fQ1IQ0;Q0eQ25Q1}PqQ09Q1~Q1rPRQ1xQ1kQ0<Q1MQ0>Q0BMO1Q0F%;QRuQ1iPeQ0XPfF3PQP]P^P_PHQ1XP9Q2;Q1_P{Q1FQ13PgQ10Q0fQ1IQ0;Q0eQ25Q1}PqQ09Q1~Q1rPRQ1xQ1kQ0<Q1MP;P8MO1P5PuQ1iPeP3PfF3PjQ1RP3Q1RP3PkPlP3PNPDPOP6Q1vPmD5P0P3PLQ1eQ1hQ1eQ1hQ1sP0C2Q1yP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4EQ0BPEQ2:P]P^P_Q1`Q1ZPZQ1_P4PyQ1HPAQ0JP~PKQ0KQ0zQ25Q1}PqQ09Q1~Q1rPRQ1xQ1kQ0dPbQ1>Q0?Q0CMO1Q0SQ2:#;RuQ1RPeQ0QPfF3Q2:P]P^P_Q1`Q1ZPZQ1_P4PyQ1HPAQ0JP~PKQ0KQ0zQ25Q1}PqQ09Q1~Q1rPRQ1xQ1kQ0dPbQ1>Q0?P8MO1P5PuQ1RPeP3PfF3PjQ1zP3Q1zP3PkPlP3PNPDPOP6Q1ePmD5P0P3PLQ1hQ1wQ1hQ1wQ1oP0C2Q1iP5F>D6D7E8X0B,0BX2G,0GX3EQ0FPGQ22Q20P5Q21Q1zPeP3PfF3Q233[X0B,0BX2GQ0XPBQ1fP]P^P_PXPxQ1DQ1:Q1VPrPsQ1JPYQ00Q06Q1KQ1=PqQ09Q1~Q1rPRQ1xQ1kQ0dQ1[Q1uQ1LQ0=Q0AQ0EMO1RqQ0UQ1f#;RYQ1vPeQ0LPfF3PqQ0UPYQ1vPeP3PfF3PjQ1eP3Q1eP3PkPlP3PNPDPOP6Q1wPmD5P0P3PLQ1sQ1oQ1sQ1oQ1tP0C2Q1zQ0UF>D6D7E8X0BPnQ2;P]P^P_Q1XP9P{Q1VQ24Q1FQ13PgQ10Q0fQ1IQ0;Q0<Q09Q1~Q1rPRQ1xQ1kQ0dQ1[Q1uQ1{Q1MQ0>Q0BQ0FMO1Q0XQ2;Q1ePePnPfF:RR01;RQ1h=MjnRgQ1h/KnR{%UnR9ACnVIRYPnPNPDPOP6Q1sPmP0GRRqPnPLQ1oQ1dQ1oQ1dQ1gP0GWRsQ1vQ0X+0;Rr'4Rx'4RX'4Ru'4RK'4R~'4Q02/tRPgP~PoP{PKQ0^P9PuP\PYPXP2PnPVPhPIP2PjQ1hPnPVPhQ0|PoQ0^Q1s#{RXQ0g'pQ1s#gQ0h'TRYPXQ1NQ1sO1Q1OQ1NQ1sQ1sQ1s,t1I0QQ0gQ0hQ1PJ0PQ1\H0ORXPYQ0iQ0jQ1h-0N:RuQ1h,T:Q1h#gR9Q1h'l'4Q1h/9:AB19:'4'OR9Q1e#gR:P1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ1B7k5Q0wPTQ0xQ1A5@TQ0{Q0~/ut,ItRtQ0~5@TQ1E5fTQ1A9@Tt205T>5fTQ0}9@TtQ1C5fTPTQ03Q04Q04Q05I1:5XT5XT5XTCYQ11Q12bVbWbXXF1XJ1Xb1X]|Xj|Xk|1958Q15/S5,=5RTQ15'9/O=19T;/O?Q17,9T/O>Q0mH19[^F1^J1^b1^]|^j|^k|P3Q0I/9VQ0H/9V19IVPNQ08PVQ0cO7bUbQbRbSb^b`b[bTb\1ShV:16jVeN:15PUPXPYQ0iQ0jPuP9P:P1Q0kQ0lQ0nQ0oQ0pQ0qQ0rQ0sQ19bQbRbSb^b`b[bTb\L12PqPxPPPsPrP?P3CjCjCjCjCjCjCjH0IFdFdFdFdFdFdFdFdWyY08P5P3O2n2001000010121000000WHWtP5P3O2n2001000010121000000WHWrP5P3O2n2001000010121000000WHY03P5P3O2n2001000010121000000WHW}P5P3O2n2001000010121000000WHY0:P5P3O2n2001000010121000000WHW~P5P3O2n2001000010121000000WHPJP3J0CWHP5P3O2n2011000010121000000WHX0BP5P3O2n2011000010121100000WHX2GP5P3O2n2011000010121100000WHX3EP5P3O2n2011000010121100000WHX4EP5P3O2n2011000010121100000WHX5EP5P3O2n2011000010121100000WHX6EP5P3O2n2011000010121100000WHX7EP5P3O2n2011000010121100000WHX8EP5P3O2n2011000010121100000WHX9EP5P3O2n2011000010121100000WHX:EP5P3O2n2011000010121100000WHX;EP5P3O2n2011000010121100000WHX=EP5P3O2n2011000010121100000WHX>EP5P3O2n2011000010121100000WHX?EP5P3O2n2011000010121100000WHXAEP5P3O2n2011000010121100000WHXBEP5P3O2n2011000010121100000WHXDEP5P3O2n2011000010121100000bfbfbfWfWdQ02Q18Q0yPjQ0CP3Q07PkPlQ1Q9_3NP3PLQ16Q0AP5I0]DmDeX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0E[]deK0~b{bvbubwY05Y04P5P3O2n2001000010121000000c0;P2Q0:Q0RQ0DP]P^P_Q0EQ0FQ0SQ0TQ0UQ1@Q0VQ0WQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZQ0[PoQ0\PpQ0]Q0^Q0_Q0`MO1Q0aQ0bP\PeP`PfF3H0:ec09P2Q0:Q02P\Q0zP]P^P_P`PaPWPbQ1GPUPSPcPdPPPMP7P>Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0SP?P=P;P8MO1P5Q0zQ0LPeP3PfF:PjPnP3PnP3PkPlP3PNPDPOP6Q0NPmD5P0P3PLQ0OQ0YQ0OQ0YQ0ZP0C2Q0GP5F>D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWdQ0EP]P^P_Q0FQ0SQ0TQ0UQ0XQ1@1NDSQ0WQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZQ0[PoQ0\PpQ0]Q0^Q0_Q0`Q0aMO1P\Q0bP`PePaPfF3H0:eY06W|Y02WsWzY01Y07WqP>P3DEWHZ0OEXhEZ0MEZ0N1X11Xn1Y0>Y0=W<X@EXCEXEEXGEZ0DEZ0CEZ0LEZ0KEZ0JEZ0IEZ0HEZ0GEZ0FEZ0EEXIEXKEXLEXMEXNEZ0BEZ0AEX_EXaEXcEY0@o"). Qed.

  (* [comment removed for export] *)
  Lemma strnlen_callq : forall ra' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (P n : Z) (buf : list byte) (r : region),
    stk bsegs m lo (q + -544) ->
    bytes_at bsegs m P buf ->
    memchr_ok P 0 n buf ->
    mem_inv bsegs m ->
    (P + Z.of_nat (length buf) <= lo \/ q <= P)%Z -> (0 < P < 2^64)%Z -> (0 <= n < 2^64)%Z ->
    munch W m0 m -> wmono bsegs m0 m ->
    rclean m0 r -> inreg r P (strnlen_rl n buf) -> (strnlen_rl n buf <= 2^40)%Z ->
    rng RNG P (Z.of_nat (length buf)) -> rrng RNG r ->
    evtF bsegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          Ft (ret_pc ra') fc None m' (seg_rom bsegs)
                 /\ munch [(lo, q + -544)]%Z m m'
                 /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ stk bsegs m' lo (q + -544)
                 /\ bytes_at bsegs m' P buf)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x41ad0) fc None m (seg_rom bsegs)).
Proof using Fp B BS RB HSTRN RNG q gp tp m0 lo AP VA LO GLO QHI SEP_F SEP_B HAP KH RBI RG_stk RG_img ENV0 RC_B.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "p'0h02m'h13t6'h23a1'h33t5'h43t4'h53t3'h63a7'h73a6'h83a5'h93a4'h:3a3'h;3a2'h<2t6h=3t2'h>2t5h?3t1'h@3t0'hA2t4hB2t3hC2a7hD1HhE2a6hF2a5hG2a4hH4__x1hI2a3hJ2a2hK4__x2hL2t2hM7__arithhN4__ffhO7__sat41hP7__sat42hQ7__sat43hR7__sat44hS7__sat45hT7__sat46hU8__varmaphV5__withW4cstrhX2HahY2t1hZ3ms'h[1zh\4__p1h]4__x3h^2t0h_2PSh`4__x4ha1mhb1xi001xhc2BBhd3BUFhe4BUF'hf3ENVhg2Eqhh2Fthi2Hnhj2IRhk2MIhl3MI'hm2MUhn3MU'ho3MU0hp2OKhq1Phr2P0hs3R40ht2RChu3RCmhv2RPhw2RRhx3SEPhy2SThz3ST'h{2WMh|3WM'h}3WM0h~1bi013bufi022fci031ni041ri053ra'i062s0i072s1i083s10i093s11i0:2s2i0;2s3i0<2s4i0=2s5i0>2s6i0?2s7i0@2s8i0A2s9p%0p%1p&0p;1p;2p;4p;3p;5p;Op;7p;6p;>p;Gp;Hp;:p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0g002TR1p4p710p8P0g0030R3p4p710R4p8P2p1003NR2p4p7210R5p8g004?R6p4p7210P4p8p102Tnp6051000R7P0p8P7p101[ep4p710R0p8P7p102PBp4p710R8p8P7g00:lR9p4p710R:p8P7p1004kp4p710R;p8P7p1006Gp4p710R7p8p102V=p6051000R<P0p8P<P8p8P<P:p8P<P;p8P<P7p8p103RUp6051000R<P2p4p710R2p8P<p103Sbp4p710R<p8P;P4p8p103]7p6051000R;p103_ip4p710R:p8P;P0p8P;P4p8P;p101[Cp4p710R8p8p103^Bp6051000R=P:p8P=P0p8P=P8p8p103`@p6051001R8P0p8P8g02GZR0p4p710p8P8P;p8P8P=p8P8p103_Lp4p710p8p104Lep6051002R8P2p8P8p105@np4p710p8P8p1058Zp4p710p8P8P<p8p1059Qp605311001R<P5p8P<p1056[p4p7210p8p100A_p4p7210P4p8P7P4p8p1006fp4p7210P4p8g007ej1=Tg008Jj1YTg008hj1oTg00U[j1GTP6k20hTg00>cj1gTg007Ek109Tg01B^k10_Tg00e7j2HTg05dfj4~TP9j2OTg00O;j1RTg00B<j29Tg00Qfj2_Tg014bj1<Tg01eOj2tTg00CPj2ETg00ClS00j26Tg04C?j3FTg04G5j2sTg05ebj2rTg05I\k306Tg05Doj3dTg05D6k205Tg05fek50TTg05g`k30QTg05hgk102Tg05ibk50GTg00P_j1vTg01m_j2mTg01nGj3zTg00R@j1|Tg00R_j2lTg00SHj3kTg00T1k20?Tg00FJj1yTg00T]j3]Tg00Fjj2jTg01DFk10kTg00U=j4hTg00GHk10gTg00Gfk10eTg00HQj2iTg00I4j2\Tg01fLk30;Tg00JBk10:Tg00Jdk20dTg00@ij2ITg00KFk20cTg00;Lj3@Tg00L2k30bTg00LQk40aTg01AAj2DTg027nk20`Tg009Kj2BTg027Dk208Tg03M@k207Tg05;ak20^Tg05>Ik20]Tg05T^lO1Tg05UPk10\Tg016SR9j20Tg05VIj74Tg05jhk10[Tg05kok10ZTg04d\j2qTg04eOj3{Tg05m7k20YTg05mck50XTg05nLk30WTg05o3k30VTg060>k20UTg061:j3xTg062Aj2nTg063Ik20STg0641k20RTg064ik20PTP3j6LTg065kk30OTg066Vk30LTg067;k30KTg0686k20JTg00?ck201Tg069;k20HTg06:=k10ITg03X7k400Tg06;=k10FTg06;nm>0MTg06<gk10ETP0k20DTg06=]mG0NmH0BTg05[Mk70CTg05]Fj18TP1k60zTg00MCk10xTg05H7k50wTg06>dk20>Tg06?Zk20vTg06@Ok60pTg01S[j4bTg05JVj4uTg05a=k70nTg06AJm:0mTg05W;k40lTg05b6k40<Tg00dBj4wTg04Pgk20jTg04D3j3pTg00IWk40@Tg00X5k70=Tg01EGk30iTg01Ddk30oTg00Y=k70fTg00Yak80qTg06BGk20rTg00XYk60sTg00V@k70tTg01\fk60uTf0R1#=#=p=Kg00jXR0f2R3f1R6P1H0<p=CP0P3P6P1Cwp=M20j01p=A1H36/91p=Qg00[OR4/E1p=T1941p=;Ap061p=X%G1#Gp=>g00;fR7P6g00`GP1H0@p=cP6g00[mS01g00\LS02Q02g00\lS03P1g00]LR<K0=p=a%G1#=p=`%=1#=#=#=p=:P3Q01Q02Q02Q03P7P6g00`nP1H0@P<K0=p=?B0i761p=[B0o761p=ZP3Q01Q02Q02Q03P6P1K0fp=Nf3R<Q01Q02Q02Q03P3P6P1L0qp=JP7P7P6P1H00p=f20r61,B3p=2f6R5f5R8f4R2#8P<P3P6P1F4p=7Ap058P0P3P6P1Cw,6<,62'6p=5g057SR=?@82AF<36/61'6p=3%=1#Gp=VP6Q01Q02Q02Q03P1J0sp>03P3Q01Q02Q02Q03P6P1K0tp>04f7R;P5P8P2P<P3P6P1F45@=p=eP0P<P3P6H0</61p=}1661,63p=^P0P3P6P1Cw,6<,62p=SAF82<Ap036/61'6p=WA@=36/61p=PA@=61p>0yP6Q01Q02Q02Q03P1J0up>0AP5P8P2P<P3P6P1CuCup=Ug00<DR:#=R>#=R?#=R@#KRA#=RB#YRC#oRD%G>RE#YRF00hD%YARA#oRG%Y@#oS04#g\DRHQ04$09g04I5p,2loRIp,1qS05%G@#KS06#=#K$0_S07'HR@5C2S08AM823P8P4P2P<C~%A;Q04/O8#R=Q;IQ05/9;'_f8RJ#T%<>RK%<BRL'tRM,EJRN'6%;J/6Ng04@Fp,2m0RNf;RO3Ff<RP,XNf9RQ,sNf:RNf=RR1rPO4061rRP%=ERS#KRT#<RU,tKRV'9p,3RNGS09f?S0:Q04/OR#R3dQ09005RP0fBS0;fAS0<Q0:PPI0TQ0<#;Q0<Q04Q0:'O#R;QM'6fCS0=@0Q;5Q0=$02f@S0>fDS0?P5PJP;I0GQ0?Q0>'sQ04Q0;'ORW#v%RW#;%GE#>RE#<RW,mKS0@%TKRX%;W1tKWRY#T[[S0A%;KRZg01X4S0BAzKW6UWXS0CQ0B%;Y[^XZS0D1mKUS0E%;U%TV[\XS0FQ0BAzKU6UXXZS0GQ0B%;V[^XZS0H1mKLS0I%;L%TM[\XS0JQ0BAzKL6UXXZS0KQ0B%;M[^XZS0Lg00_[S0Mg00bPRZ#|RL#|S0N,l7S0O1l7LS0P1l7Z5k75k7g00boS0Q+0?Q0M#yS0R3]Q0M$09S0SP71j73S0TP6&0k7S0UChS0V&0g7S0W&0e7RZ1i7:RL1\7KRK%YE60;7'c,aZQ02$0:S0XPZ%`:#:#>#>#:#:#:#<RE,\71i7>S0Y5?ZQ0XPZQ0Y%GT#K#:#<RT,\7S0Z,[LS0[5?ZQ0X1\74R>Q07,\7RX,ZLS0\5?ZQ0\B0;7KCS0]'c,aZ5NZCJCJCJQ03-0dZS0^P1P3g00_;RKg00aURU'I20c13=@KUdB0b746H0aS0_bNbUbVXH7XK71E1Y19E31D3T,9<Q07,H<RE#;1EEM'6[[[^H7^K7P1PIQ05p,3QHIp,3GLOp,2LOS0`O5bMbObPbQbRbSbTbW-0`@1BC@RE-08CRY=@7@20777RU1fI@%yURW3]R[fFR\+0^AF[\\fGR]-0]01X]]P0Q09Q0:ftR^PEp,2gpR_p,2tpR`f>RaPRPPfpRbfoRcfVS0afUS0b52CPOPNPQPJP;P5P8fhRdfgS0cffS0dfeRefdRffcRgfbS0efaS0ff`Rhf_S0gP2P<P3P6MO1fZRiP^fYRj&0:DRkP1&0\0RlF7P[fXS0hP1Q0hP1%A1RmAC1I@RnP1fWS0iQ0bF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DXZ=S0jPfPEP_P`PgQ0eQ0fPhQ0g1BC]Ro1BC\Rpf^S0kf]S0lf\S0mf[S0nPiPjQ0hQ0iQ0aQ0bfTS0ofSS0pfRS0qfQS0rfPS0sfOS0tfNS0ufMS0vfLS0wfKS0xMO1RqfJS0y%::#V#`#`#>#V#:#<Rr,BCS0zfIS0{PkfHRsPlF4RtPqQ0y%::#V#>#V#>#`#>#K#<,BCRuQ0{PkPsPlF4Rvg06CES0|#yRw%gD/Ik&0[=Rx$0ZRy%<?Rz,BC%G:S0}#K#V#>#KR{#=#:#:#:R|#<,qF9{F4%GS#YRS%<{R{1qS{3{R{+0YRFPqQ0yQ0zQ0{PkI0X40W>0V0s-0UlR}PePEP_P`PfPgQ0eQ0fPh1BCsPoQ0gQ0kQ0lQ0mQ0nPiPjQ0hQ0iQ0aQ0bQ0oQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wMO1S0~Q0xPuQ0yPkQ0{PlF4=x=w,nxRu9@y1XayPDQ0z20SS{R~+0RQ0~Q0xP1Q0yPkQ0{PlF4=x=w,nx=@yuX~DRuPD1Hr~,BCPuAx=vw,nxRx,IyQ0z-08C/H~,BC20Pr~ELQ0zB0OSC{60LCQ0z@0KS{ELA@y}xe20J0tP0PqQ0yQ0zQ0{PkPsPl%G|#`#>#>#<R|1qA|5{ARAPFPz%gGR|201GARG'IQ0z-0H0=@|Gdg013DRG,IK&0IA=@KGdg06DJRG0077RK#gR|PGP7PFPzH00-01KRK'I&0FA=@|KdN>0MELQ0|Q09$0E+0DP0Q09PfPEP_P`PhQ0gQ0hQ0iQ0aQ0bQ0oQ0pQ0qQ0rQ0sQ0tQ0yQ0{P]P\fERKPIPsNG0NQ0jPvp,5HSTRNQ09Q0?PfPEP_P`PgQ0eQ0fPhQ0gPoPpQ0kQ0lQ0mQ0nPiPjQ0hQ0iQ0aQ0bQ0oQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0{PsP]P\PKPI1IDoA@Dooe1IDpA@DppeQ04/OKRp#vRo%RpRp#;RvQ0@Q0AQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0KQ0Lp-0S0jQ0RQ0S1j76R|Q0WPZ1c>L,aZRA203Z<5NZQ0XPACJQ0^Q0_bNbUbVXH7W\Q0j%T1/66%T6[^H7]\P1Q0t/EMQ0tP\O3bMbObPbQbRbSbTbW%T]ePoPvQ0@Q0AQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0RQ0SP|Q0WPZA?Z>LQ0],cL,aZ5NZR>Q0XP>CJQ0^Q0_bNbUbVXH7%;11E1M'6%;61E6M'6[^H7P1Q0uPKO2bMbObPbQbRbSbTbW%;\1E\M'6eQ0;AMs]KeQ0<P]P4P\PKC~eQ0>%AseP7P@Q0{?CI1X[7Q0=ACsI@ePYP3ELP7P@g06E6R4,D1,9IX[7PoPvQ0@Q0AQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0RQ0SQ0VQ0WPZQ0YQ0Z'[9?ZLQ0XQ0Y/ZXRMQ06#>#:#<R>,\7S06'[9?ZLCJQ0^Q0_bNbUbVXH7XK71D6TS0Z,91Q07,H3S0]/D>S0|,96[^H7^K7P1Q05PIQ0`O3bMbObPbQbRbSbTbW1D@4RT,9IePYP3ELp,2KHg04;d/9IeP7P@Q04/O\#R=QsI191s'_X[7PoPvQ0@Q0AQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0RQ0SP7P71j72P3Q0UChP61j7<S0UChQ0WPZQ0Y,ZLQ0},i7S0}5?ZR|1i7?R?=?ZL604ZQ0X1Z?X=?ZL:04Z|CJQ0^Q0_bNbUbVXH7XK7X]7X`7AQ16319<1'_AQ63<Q07=Q26'_[^H7^K7^]7^`7P1Q05PIQ04Q0v'O#RQ0tP]O5bMbObPbQbRbSbTbWAQ]pI19@]'_ePYP3ELP2&02seP<Q0?,ssePQQ0?1r\KR|806]ePJ19|Vep,6RG_imgQ09%KB#:#:#<%V:#>#>#>#>#:#:#:#<3deP7P@Q091D1I7dIX[7Q09PIQ05/DIPI1D@IR:p,6RG_stkPoPvQ0@Q0AQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0RQ0SQ0VQ0WA?ZLL1[ML,ZLQ0Y/[L,ZL5?Z5NZQ0^Q0_bNbUbVXH7XK71911Q07,H6/D11D61,H15Q1'6^H7^K7P1Q05PIO2bMbObPbQbRbSbTbWK0CQ09?dI:ePYP3ELP;Q09?d]peP5Q09Q0?+05eOkPePEP_P`Q0fPhPjQ0hQ0iQ0aQ0bQ0oQ0pQ0qQ0rQ0sQ0xQ0yPsP]P\PIQ0{P1NH0BS0VP7PYQ0<fvRYPEP_P`PaPRPPfrRpfqR:Q0hQ0i52CPOPNPQPJP;P5P8fjS0~fiRLPdQ0cQ0dPePfPgQ0eQ0fP2P<P3P6MO1Q0m%8YQ0nPkP1PlGeRMQ0:/D4Q0:'f=]UW?Fi11Xi1R4P1PIQ0:Q0i9M1jRvC}7^m3^X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DXJD,0DX2D,0DXLD,0DXYD,0DX^D,0DX[7P1P@P2J0zQ0>fuRoPEP_P`PaPRPPP:PbQ0iQ0a52CPOPNPQPJP;P5P8PLPdQ0cQ0dPePfPgQ0eQ0fPhP2P<P3P6MO1Q0n%8oPiPkP1PlGeS101fT@=]UW?Fj1PjP1PmPnP1Q0hQ0aF5S113^X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DXJD,0DX2D,0DXLD,0DXYD,0DX^D,0DP9PD1D@>/f@=]UWRW?Fi116nv9^4m5^MX0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DXJD,0DX2D,0DXLD,0DXYD,0DX^DQ0;fwRMPEP_P`PaPRPPfsR4PpQ0h92CjPOPNPQPJP;P5P8fkRvQ0~PLPdQ0cQ0dPePfPgQ0eP2P<P3P6MO1Q0lPMQ0mPkP1PlF7P[Q0nP1Q0nP1PmPnP1PiQ0hF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0=fxRUPEP_P`PaPRPPP^P4A2CijPOPNPQPJP;P5P8flR>PvQ0~PLPdQ0cQ0dPePfPgP2P<P3P6MO1Q0kPUQ0lPkP1PlF7PWQ0mP1Q0mP1PmPnP1Q0nPjF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DXJD,0DX2D,0DXLD,0DXYD,0DP9PDQ0?fyRTPEP_P`Q0:PRPPPoP^Q0n=2CiPOPNPQPJP;P5P8fmS12P>PvQ0~PLPdQ0cQ0dPePfP2P<P3P6MO1Q0gPTQ0kPkP1PlF7PWQ0lP1Q0lP1PmPnP1Q0mPiF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DXJD,0DX2D,0DXLD,0DXYDP\f{RBPEP_P`PaPRPPPMPYQ0lQ0m52CR|POPNPQPJP;P5P8PcfnRVQ12P>PvQ0~PLPdQ0cQ0dP2P<P3P6MO1Q0f%8BR?PhPkP1PlF4P[Q0gP1Q0gP1PmPnP1Q0kQ0mF5RXE3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1P\PBPEP_P`Q0<PRPPPMPYP|POPNPQPJP;P5P8PcPVQ12P>PvQ0~PLPdQ0cQ0dP2P<P3P6MO1Q0fP?PhPkP1PlF4PWQ0gP1PXE3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DXJD,0DX2D,0DXLD,0DP9PDP]f|RXPEP_P`Q0;PaPPPUPMQ0kQ0l52CPOPNPQPJP;P5P8PbPcPVQ12P>PvQ0~PLPdQ0cP2P<P3P6MO1Q0ePXQ0fPkP1PlF7PWPhP1PhP1PmPnP1Q0gQ0lF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DXJD,0DX2D,0DXLDQ0yp+01@R?PEP_P`PaPRPPPBfzR|Q0f=2ChRAPOPNPQPJP;P5P8P4PpP:PbPcPVQ12P>PvQ0~P2P<P3P6MO1Pe%8?RzPfPkP1PlF4P[PgP1PgP1PmPnP1Q0ePhF5RFE3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0{f~RGPEP_P`Q0?Q0>PPP|PTQ0g92ChPOPNPQPJP;P5P8PpP:PbPcPVQ12P>PvQ0~PLP2P<P3P6MO1PfPGPgPkP1PlF7PWQ0eP1Q0eP1PmPnP1Q0fQ0gF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DXJD,0DX2D,0DP9PDQ0yP?PEP_P`PKQ0<PRPBP|PAPOPNPQPJP;P5P8P4PpP:PbPcPVQ12P>PvQ0~P2P<P3P6MO1PePzPfPkP1PlF4PWPgP1PFE3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DXJD,0DX2DQ0up+01DRFPEP_P`PaPRPPP?PGA2CefPOPNPQPJP;P5P8PMPYPoP^P4PpP:PbPcPVP2P<P3P6MO1PLPFPdPkP1PlF7P[Q0cP1Q0cP1PmPnP1Q0dPfF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0wp+01BRzPEP_P`P]Q0=Q0:f}RAPXQ0e92CgPOPNPQPJP;P5P8PoP^P4PpP:PbPcPVQ12P>P2P<P3P6MO1Q0cPzQ0dPkP1PlF7PWPeP1PeP1PmPnP1PfQ0eF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DXJD,0DP9PDQ0vp+01CS13PEP_P`PsQ0?Q0>PGPAA2CfgPPPNPQPJP;P5P8PYPoP^P4PpP:PbPcPVQ12P2P<P3P6MO1PdQ13Q0cPkP1PlF7PWQ0dP1Q0dP1PmPnP1PePgF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DXJDQ0qp+01HRqPEP_P`PaPRPPPFQ13A2CLdRtPOPNPQPJP;P5P8PBP|PTPUPMPYPoP^P4PpP2P<P3P6MO1Q12%8qRxP>PkP1PlF4P[PvP1PvP1PmPnP1Q0~PdF5R}E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0tp+01ERyPEP_P`Q0yP\Q0;p+01AR{P?Q0d=2CePaPNPQPJP;P5P8PUPMPYPoP^P4PpP:PbPcP2P<P3P6MO1Q0~PyPLPkP1PlF7PWPdP1PdP1PmPnP1Q0cPeF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXID,0DP9PDQ0sp+01FS14PEP_P`Q0xP]Q0=PzP{Q0cQ0d52CQ0:POPQPJP;P5P8PTPUPMPYPoP^P4PpP:PbP2P<P3P6MO1PvQ14Q0~PkP1PlF7PWPLP1PLP1PmPnP1PdQ0dF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DXIDQ0ap+01LRSPEP_P`PaPRPPPqp+01GS15Q12=2C>R~POPNPQPJP;P5P8P?PGPAPXPBP|PTPUPMPYP2P<P3P6MO1P:%8SRrPbPkP1PlF4P[PcP1PcP1PmPnP1PVP>F5RwE3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0qPqPEP_P`Q0vQ0{PKPFQ13PtQ0<PRPQPJP;P5P8PBP|PTPUPMPYPoP^P4PpP2P<P3P6MO1Q12PxP>PkP1PlF4PWPvP1P}E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGD,0DP9PDQ0pp+01IS16PEP_P`Q0uQ0yP\PyPFQ0~=2CLQ0;PaPNPJP;P5P8PXPBP|PTPUPMPYPoP^P4P2P<P3P6MO1PVQ16Q12PkP1PlF7PWP>P1P>P1PmPnP1PvPLF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DXGDPip+01PS17PEP_P`PaPRPPPSp+01KS18A2C:bPOPNPQPJP;P5P8PFQ13PzP{P?PGPAPXPBP|P2P<P3P6MO1PoQ17P^PkP1PlF7P[P4P1P4P1PmPnP1PpPbF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0bQ18PEP_P`Q0sQ0wPsQ15Q14A2C>vQ0?Q0>PPPJP;P5P8PGPAPXPBP|PTPUPMPYPoP2P<P3P6MO1PbQ18PcPkP1PlF7PWPVP1PVP1PmPnP1Q12PvF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFD,0DP9PDQ0aPSPEP_P`Q0rQ0vQ0{PqQ15P~PKQ0<PRPQP;P5P8P?PGPAPXPBP|PTPUPMPYP2P<P3P6MO1P:PrPbPkP1PlF4PWPcP1PwE3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DXFDQ0kp+01TS19PEP_P`PaPRPPQ17p+01OS1:A2Co^RwPOPNPQPJP;P5P8PqQ15Q14PyPFQ13PzP{P?PGP2P<P3P6MO1PTQ19#8RrPUPkP1PlF4P[PMP1PMP1PmPnP1PYP^F5R~E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0hp+01NS1;PEP_P`Q0pQ0tQ0xp+01JS1<Q16A2CcVP]Q0=Q0:POP;P5P8PzP{P?PGPAPXPBP|PTPUP2P<P3P6MO1P4Q1;PpPkP1PlF7PWP:P1P:P1PmPnP1PbPVF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXED,0DP9PDPjQ1:PEP_P`Q0oQ0sQ0wQ18Q1<A2CbcPsQ0?Q0>PPPJP5P8Q13PzP{P?PGPAPXPBP|PTP2P<P3P6MO1P^Q1:P4PkP1PlF7PWPpP1PpP1PmPnP1P:PcF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DXEDQ0ep+01XS1=PEP_P`PaPRPPQ19p+01SS1>A2CTUR}POPNPQPJP;P5P8PSQ18Q1<Q16PqQ15Q14PyPFQ13P2P<P3P6MO1PAQ1=#8RxPXPkP1PlF4P[PBP1PBP1PmPnP1P|PUF5RtE3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0np+01QS1?PEP_P`Q0aQ0qQ0up+01MS1@PSA2Cp:Q0yP\Q0;PaPNP5P8PyPFQ13PzP{P?PGPAPXPBP2P<P3P6MO1PYQ1?PoPkP1PlF7PWP^P1P^P1PmPnP1P4P:F5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCD,0DP9PDQ0mp+01RS1APEP_P`Q0iQ0pQ0tQ1;Q1@A2C4pQ0xP]Q0=Q0:POP;P8Q14PyPFQ13PzP{P?PGPAPXP2P<P3P6MO1PMQ1APYPkP1PlF7PWPoP1PoP1PmPnP1P^PpF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DXCDQ0dp+01\S1BPEP_P`PaPRPPQ1=p+01WS1CA2CAXPOPNPQPJP;P5P8Q17Q1:Q1;Q1@PSQ18Q1<Q16PqQ15P2P<P3P6MO1PzQ1BP{PkP1PlF7P[P?P1P?P1PmPnP1PGPXF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0kQ19PEP_P`PjQ0bQ0rQ17Q1:PwQ0vQ0{PKQ0<PRPQP8PqQ15Q14PyPFQ13PzP{P?PGP2P<P3P6MO1PTPrPUPkP1PlF4PWPMP1P~E3X0H,0HX<D,0DX>D,0DXAD,0DXBD,0DP9PDQ0gp+01US1DPEP_P`PiQ0aQ0qQ1?Q17A2CYoQ0uQ0yP\Q0;PaPNP5Q16PqQ15Q14PyPFQ13PzP{P?P2P<P3P6MO1P|Q1DPTPkP1PlF7PWPUP1PUP1PmPnP1PMPoF5E3X0H,0HX<D,0DX>D,0DXAD,0DXBDQ0~p+01`S1EPEP_P`PaPRPPQ1Bp+01[S1FA2Cz{R~POPNPQPJP;P5P8Q19Q1>Q1AQ1?Q17Q1:Q1;Q1@PSQ18P2P<P3P6MO1Q14Q1E#8RrPyPkP1PlF4P[PFP1PFP1PmPnP1Q13P{F5RwE3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0fQ1CPEP_P`Q0mQ0hQ0oQ1>Q1AA2CUMQ0sQ0wPsQ0?Q0>PPPJQ18Q1<Q16PqQ15Q14PyPFQ13PzP2P<P3P6MO1PXQ1CPBPkP1PlF7PWP|P1P|P1PmPnP1PTPMF5E3X0H,0HX<D,0DX>D,0DXAD,0DP9PDQ0eQ1=PEP_P`Q0lPjQ0bQ19Q1>P}Q0rQ0vQ0{PKQ0<PRPQPSQ18Q1<Q16PqQ15Q14PyPFQ13P8P<P3P6MO1PAPxPXPkP1PlF4PWPBP1PtE3X0H,0HX<D,0DX>D,0DXADPVp+01dS1GPEP_P`PaPRPPQ1Ep+01_S1HQ14=2CyS1IPOPNPQPJP;P5P8Q1=Q1Cp+01VS1JQ1DQ19Q1>Q1AQ1?Q17Q1:P2P<P3P6MO1Q1<Q1G#8RtQ16PkP1PlF4P[PqP1PqP1PmPnP1Q15PyF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Pfp+01ZS1KPEP_P`Q0gQ0nQ0iQ1JQ1DA2CB|Q0pQ0tQ0xP]Q0=Q0:POQ1;Q1@PSQ18Q1<Q16PqQ15Q14PyP;P<P3P6MO1P?Q1KPGPkP1PlF7PWPAP1PAP1PmPnP1PXP|F5E3X0H,0HX<D,0DX>D,0DP9PDPeQ1FPEP_P`PhQ0mQ0hQ1CQ1JA2CXBQ0oQ0sQ0wPsQ0?Q0>PPQ1:Q1;Q1@PSQ18Q1<Q16PqQ15Q14PJP2P3P6MO1P{Q1FP?PkP1PlF7PWPGP1PGP1PmPnP1PAPBF5E3X0H,0HX<D,0DX>DPpp+01hRxPEP_P`PaPRPPQ1Gp+01cS1LQ1<Q1652CPOPNPQPJP;P5P8Q1BQ1FQ1Kp+01YS1MQ1=Q1CQ1JQ1DQ19Q1>P2P<P3P6MO1Q1;PxQ1@PkP1PlF7P[PSP1PSP1PmPnP1Q18Q16F5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0cp+01]S1NPEP_P`Q0eQ0kPiQ1MQ1=A2CGAQ0aQ0qQ0uQ0yP\Q0;PaQ1?Q17Q1:Q1;Q1@PSQ18Q1<Q16PqPNP5P3P6MO1Q13Q1NPzPkP1PlF7PWP{P1P{P1PmPnP1P?PAF5E3X0H,0HX<D,0DP9PDPdp+01^S1OPEP_P`PgQ0gQ0nQ1KQ1MA2C?GQ0iQ0pQ0tQ0xP]Q0=Q0:Q1AQ1?Q17Q1:Q1;Q1@PSQ18Q1<Q16POP;P<P6MO1PFQ1OQ13PkP1PlF7PWPzP1PzP1PmPnP1P{PGF5E3X0H,0HX<DPYp+01lR}PEP_P`PaPRPPPxp+01gRuQ1;Q1@52CPOPNPQPJP;P5P8Q1EQ1HQ1OQ1NQ1BQ1FQ1KQ1MQ1=Q1CP2P<P3P6MO1Q1AP}Q1?PkP1PlF7P[Q17P1Q17P1PmPnP1Q1:Q1@F5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0~Q1EPEP_P`PeQ0fQ0lQ1BQ1FP~PjQ0bQ0rQ0vQ0{PKQ0<Q19Q1>Q1AQ1?Q17Q1:Q1;Q1@PSQ18PRPQP8P6MO1Q14PrPyPkP1PlF4PWPFP1PwE3X0H,0HP9PHPvp+01aS1PPEP_P`Q0dQ0eQ0kQ1NQ1BQ13=2CzPiQ0aQ0qQ0uQ0yP\Q0;Q1DQ19Q1>Q1AQ1?Q17Q1:Q1;Q1@PSPaPNP5P3MO1Q15Q1PQ14PkP1PlF7PWPyP1PyP1PmPnP1PFPzF5E3X0HP|p+020R9PEP_P`PaPRPPP}p+01kRwQ1AQ1?52CPOPNPQPJP;P5P8Q1GQ1Lp+01bS1QQ1PQ1EQ1HQ1OQ1NQ1BQ1FP2P<P3P6MO1Q1JP9Q1DPkP1PlF7P[Q19P1Q19P1PmPnP1Q1>Q1?F5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q12Q1LPEP_P`PdPfPhQ1HQ1OA2CyFQ0mQ0hQ0oQ0sQ0wPsQ0?Q1CQ1JQ1DQ19Q1>Q1AQ1?Q17Q1:Q1;Q0>PPPJP2MO1Q16Q1LPqPkP1PlF7PWQ15P1Q15P1PmPnP1Q14PFF5E3Q00PVQ1GPEP_P`PLPeQ0fQ1EQ1HQ1IQ0lPjQ0bQ0rQ0vQ0{PKQ1=Q1CQ1JQ1DQ19Q1>Q1AQ1?Q17Q1:Q0<PRPQP8MO1Q1<PtQ16PkP6PlGePWPqP6PqP6%A6AC6I@P6Q15PyDSEWPGp+024S1IPEP_P`PaPRPPP9p+01oRtQ1JQ1D52CPOPNPQPJP;P5P8PxPup+01fS1Rp+01eS1SQ1GQ1LQ1QQ1PQ1EQ1HP2P<P3P6MO1Q1KQ1IQ1MPkP1PlF7P[Q1=P1Q1=P1PmPnP1Q1CQ1DF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1PbQ1RPEP_P`PvQ0cPgQ1QQ1PQ1592CqQ0gQ0nQ0iQ0pQ0tQ0xP]Q1KQ1MQ1=Q1CQ1JQ1DQ19Q1>Q1AQ1?Q0=Q0:POP;MO1PSQ1R#8Q18PkP<PlGeP=PuPEP_P`P>PdPfQ1LQ1QQ16=2CqPhQ0mQ0hQ0oQ0sQ0wPsQ1FQ1KQ1MQ1=Q1CQ1JQ1DQ19Q1>Q1AQ0?Q0>PPPJMO1Q1@PuPSPkP2PlF7AFWS8S1TPSP8%A8AC8I@P8Q18Q16F5S1U'6Q0>p+028S1VPEP_P`PaPRPPQ1Ip+023S1WQ1KQ1M52CS1XPOPNPQPJP;P5P8P}Pwp+01jRrp+01iR~PxPuQ1RQ1SQ1GQ1LP2P<P3P6MO1Q1OQ1V#8S1YQ1NPkP1PlF4S1ZP[Q1BP1Q1BP1PmPnP1Q1FQ1MDSEWS1[3PX0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0D[XZ=PWQ18P2Q18P2%A2Q08P2Q1<PqDSEWQ00Q1TQ1UQ1VPEP_P`PAPTPoQ1IQ1WQ1XP:Q12PLPeQ0fQ0lPjP}PwPrP~PxPuQ1RQ1SQ1GQ1LQ0bQ0rQ0vQ0{MO1Q1OQ1YQ1NPkPKPlF4S1YQ1ZQ1[3PX0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q1;=FW;Q1:PJ%AJACJI@PJQ1;PSF5Q00Q17/XQ%AQACQI@PQQ1:Q1@DSp+02<S1:PEP_P`PzPAPTQ1Vp+027S1;Q1OQ1N52CS1[PoP:Q12PLPeQ0fQ0lP9Ptp+01nS1Zp+01mS1XP}PwPrP~PxPuPjQ0bQ0rQ0vMO1Q1QQ1:#8S1UQ1PPkQ0{PlF4S1TQ1:PEP_P`PaPRPPQ1VQ1;Q1[POPNPQPJP;P5P8P9PtQ1ZQ1XP}PwPrP~PxPuP2P<P3P6MO1Q1QQ1UQ1PPkP1PlF4P[Q1EP1Q1EP1PmPnP1Q1HQ1NDSEWS083PX0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q1A/XO%APACPI@PPQ1AQ17DSQ00%ARPRPIP@Q1>Q1?5MRC}p+02@S1?PEP_P`Q14PzPAQ1:p+02;S1>Q1QQ1P52CS17PTPoP:Q12PLPeQ0fQ1IQ1Wp+022S1Ap+021S1\P9PtQ1ZQ1XP}PwQ0lPjQ0bQ0rMO1Q1RQ1?#8S1]Q1SPkQ0vPlF4S1^Q1?PEP_P`PaPRPPQ1:Q1>Q17POPNPQPJP;P5P8Q1IQ1WQ1AQ1\P9PtQ1ZQ1XP}PwP2P<P3P6MO1Q1RQ1]Q1SPkP1PlF4P[Q1GP1Q1GP1PmPnP1Q1LQ1PDSEWS1_3PX0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0:#AQ0>PIP@Q0>Q1JQ193MC}Q00Q0<?CI@Q0<Q1CQ1D3Mp+02DS1DPEP_P`Q1<Q14PzQ1?p+02?S1CQ1RQ1S52CS00PAPTPoP:Q12PLPeQ1VQ1;p+026S1Jp+025S19Q1IQ1WQ1AQ1\P9PtQ0fQ0lPjQ0bMO1PrQ1D#8S1`P~PkQ0rPlF4S1aQ1DPEP_P`PaPRPPQ1?Q1CQ00POPNPQPJP;P5P8Q1VQ1;Q1JQ19Q1IQ1WQ1AQ1\P9PtP2P<P3P6MO1PrQ1`P~PkP1PlF4P[PxP1PxP1PmPnP1PuQ1SDSEWS1b3PX0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DP1Q0=?CI@Q0?Q1KQ1=3MPDp+02GS1=PEP_P`Q1@Q16Pyp+02CS1@p+02BS1cA2C~xS1dP{PXPUP^PbP>PdQ1>p+02:S1ep+029S1fQ1VQ1;Q1JQ19Q1IQ1WQ1APfPhQ0mQ0hMO1Q1XQ1=#8S1gP}PkQ0oPlF4Q1=PEP_P`PaPRPPQ1@Q1cQ1dPOPNPQPJP;P5P8Q1>Q1eQ1fQ1VQ1;Q1JQ19Q1IQ1WQ1AP2P<P3P6MO1Q1XQ1gP}PkP1PlF4P[PwP1PwP1PmPnP1PrPxF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@DPAPDp+02FS1gPEP_P`PSPqPFQ1cp+02AS1dA2CxuS1=P?PBPMP4PcPvQ0cQ1eQ1fQ1VQ1;Q1JQ19Q1IQ1WQ1AQ1\PgQ0gQ0nQ0iMO1P}Q1g#8S1hPwPkQ0pPlF4Q1gPEP_P`PSPRPPQ1cQ1dQ1=POPNPQPJP;P5P8Q1eQ1fQ1VQ1;Q1JQ19Q1IQ1WQ1AQ1\P2P<P3P6MO1P}Q1hPwPkP1PlF4P[PrP1PrP1PmPnP1P~PuF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?DPTPDp+02ERSPEP_P`Q18Q15Q13Q1dQ1?Q1R92CuS1hPGP|PYPpPVQ0~Q0dQ1fQ1VQ1;Q1JQ19Q1IQ1WQ1AQ1\P9Q0eQ0kPiQ0aMO1Pw%8SS1=PrPkQ0qPlF4PSPEP_P`Q18Q15PPQ1dQ1?Q1hPOPNPQPJP;P5P8Q1fQ1VQ1;Q1JQ19Q1IQ1WQ1AQ1\P9P2P<P3P6MO1PwQ1=PrPkP1PlF4P[P~P1P~P1PmPnP1PxQ1RF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=DPoPDQ1aQ1DPEP_P`Q1<Q14PzQ1?Q1CQ00POPNPQPJP;P5P8Q1VQ1;Q1JQ19Q1IQ1WQ1AQ1\P9PtP2P<P3P6MO1PrQ1`P~PkP1PlF4Q1b3PX0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2DP:PDQ1@PEP_P`Q16PyP{Q1Cp+02>S1bQ1SQ1G52CS1aPXPUP^PbP>PdPfQ1;Q1JQ19Q1IQ1WQ1AQ1\P9PtQ1ZPhQ0mQ0hQ0oMO1P~Q1@#8RSPxPkQ0sPlF4Q1@PEP_P`Q16PyP{Q1CQ1bQ1aPXPNPQPJP;P5P8Q1;Q1JQ19Q1IQ1WQ1AQ1\P9PtQ1ZP2P<P3P6MO1P~PSPxPkP1PlF4P[PuP1PuP1PmPnP1Q1RQ1GF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;DQ12PDQ1cPEP_P`PqPFP?Q1bp+02=RSQ1GQ1L52CS1aPBPMP4PcPvQ0cPgQ1JQ19Q1IQ1WQ1AQ1\P9PtQ1ZQ1XQ0gQ0nQ0iQ0pMO1PxQ1c#8S16PuPkQ0tPlF4Q1cPEP_P`PqPFP?Q1bPSQ1aPBPMPQPJP;P5P8Q1JQ19Q1IQ1WQ1AQ1\P9PtQ1ZQ1XP2P<P3P6MO1PxQ16PuPkP1PlF4P[Q1RP1Q1RP1PmPnP1Q1SQ1LF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:DPLPDQ1dPEP_P`Q15Q13PGPSQ1:Q1LQ1Q52CS16P|PYPpPVQ0~Q0dQ0eQ19Q1IQ1WQ1AQ1\P9PtQ1ZQ1XP}Q0kPiQ0aQ0qMO1PuQ1d#8RqQ1RPkQ0uPlF4Q1dPEP_P`Q15Q13PGPSQ1:Q16P|PYPpPJP;P5P8Q19Q1IQ1WQ1AQ1\P9PtQ1ZQ1XP}P2P<P3P6MO1PuPqQ1RPkP1PlF4P[Q1SP1Q1SP1PmPnP1Q1GQ1QF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9DPePDQ1^Q1?PEP_P`Q14PzPAQ1:Q1>Q17PTPoP:Q12P;P5P8Q1IQ1WQ1AQ1\P9PtQ1ZQ1XP}PwP2P<P3P6MO1Q1RQ1]Q1SPkP1PlF4Q1_3PX0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8DQ0fPDQ1CPEP_P`PyP{PXQ1>Q1eQ1PQ1E52CS1_PUP^PbP>PdPfPhQ1WQ1AQ1\P9PtQ1ZQ1XP}PwPrQ0mQ0hQ0oQ0sMO1Q1SQ1C#8RqQ1GPkQ0wPlF4Q1CPEP_P`PyP{PXQ1>Q1eQ1_PUP^PbP>PdP5P8Q1WQ1AQ1\P9PtQ1ZQ1XP}PwPrP2P<P3P6MO1Q1SPqQ1GPkP1PlF4P[Q1LP1Q1LP1PmPnP1Q1QQ1EF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7DQ0lPDQ1bPEP_P`PFP?PBQ1eQ1fQ1EQ1H52CRqPMP4PcPvQ0cPgQ0gQ1AQ1\P9PtQ1ZQ1XP}PwPrP~Q0nQ0iQ0pQ0tMO1Q1GQ1b#8RyQ1LPkQ0xPlF4Q1bPEP_P`PFP?PBQ1eQ1fPqPMP4PcPvQ0cPgP8Q1AQ1\P9PtQ1ZQ1XP}PwPrP~P2P<P3P6MO1Q1GPyQ1LPkP1PlF4P[Q1QP1Q1QP1PmPnP1Q1PQ1HF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6DPjPDPSPEP_P`Q13PGP|Q1fQ1VQ1HQ1O52CRyPYPpPVQ0~Q0dQ0eQ0kQ1\P9PtQ1ZQ1XP}PwPrP~PxPiQ0aQ0qQ0uMO1Q1L%8SRqQ1QPkQ0yPlF4PSPEP_P`Q13PGP|Q1fQ1VPyPYPpPVQ0~Q0dQ0eQ0kQ1\P9PtQ1ZQ1XP}PwPrP~PxP2P<P3P6MO1Q1LPqQ1QPkP1PlF4P[Q1PP1Q1PP1PmPnP1Q1EQ1OF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5DQ0bPDQ1TQ1:PEP_P`PzPAPTQ1VQ1;Q1[PoP:Q12PLPeQ0fQ0lP9PtQ1ZQ1XP}PwPrP~PxPuPjP<P3P6MO1Q1QQ1UQ1PPkP1PlF4Q083PX0H,0HX1D,0DX3D,0DX4DQ0rPDQ1>PEP_P`P{PXPUQ1;Q1JQ1NQ1B52CR9P^PbP>PdPfPhQ0mPtQ1ZQ1XP}PwPrP~PxPuQ1RQ0hQ0oQ0sQ0wMO1Q1PQ1>#8ReQ1EPkPsPlF4Q1>PEP_P`P{PXPUQ1;Q1JP9P^PbP>PdPfPhQ0mPtQ1ZQ1XP}PwPrP~PxPuQ1RQ0hQ0oP3P6MO1Q1PPeQ1EPkP1PlF4P[Q1HP1Q1HP1PmPnP1Q1OQ1BF5E3X0H,0HX1D,0DX3DQ0vPDQ1ePEP_P`P?PBPMQ1JQ19Q1BQ1F52CReP4PcPvQ0cPgQ0gQ0nQ1ZQ1XP}PwPrP~PxPuQ1RQ1SQ0iQ0pQ0tQ0xMO1Q1EQ1e#8RtQ1HPkP]PlF4Q1ePEP_P`P?PBPMQ1JQ19PeP4PcPvQ0cPgQ0gQ0nQ1ZQ1XP}PwPrP~PxPuQ1RQ1SQ0iQ0pQ0tP6MO1Q1EPtQ1HPkP1PlF4P[Q1OP1Q1OP1PmPnP1Q1NQ1FF5E3X0H,0HX1DQ0{PHQ1fPEP_P`PGP|PYQ19Q1IQ1FQ1K52CPpPVQ0~Q0dQ0eQ0kPiQ1XP}PwPrP~PxPuQ1RQ1SQ1GQ0aQ0qQ0uQ0yMO1RuQ1HQ1f#8RxQ1OPkP\PlF4PuQ1HPxQ1OPkP1PlF4P[Q1NP1Q1NP1PmPnP1Q1BQ1KF5E3X0HPKQ1YQ1Y+0yQ1B=F[KRxQ1B/XKRu%AKR~ACKI@RrQ1FQ1M5MKRw'6R}'6Rp'6RY'6Q1Y,I=PxPYPWP[Q1BPK19I11E1@'6$0xQ0B'6Q04Q1F'OR@#v%R@#;Q0@Q0AQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0jQ0MQ0N#|,l7Q0OQ0P5k75k7Q0Q+0?Q0R3]Q0SP7Q0TP6Q0UChQ0WPZQ0}Q0Y5?ZQ0YQ0\'c,aZR@5NZ-0AZ203Z85NZQ0XPZQ0}Q0[5?ZQ0XQ0\Q06'[Q0Y5?Z=NZ@-0AZPZQ01Q02Q02Q03I0w5NZCJCJQ0^Q0_bNbUbVXH7XK7X]7W\Q0j1936Q07,H1,E6'6g01XPRZ[/6<Q0Z,9<Q0|/9<Q0],E<'6PZ[Q0B'6[[^H7^K7^]7]\P1Q0BPIPQQ05PJQ0`O6bMbObPbQbRbSbTbWUXb720>[120>W6[^b7e20vW[ePRJ0pPuPpPQP~P}P8PrPwP6P1CbCbCbCbCbCuFUFUFUFUFUFUFUWeWzP6P1O2n2001000010121000000WDWlP6P1O2n2001000010121000000WDW|P6P1O2n2001000010121000000WDWnP6P1O2n2001000010121000000WDP:P1ELWDP6P1O2n2001000010121000000WDX0HP6P1O2n2011000010121100000WDX1DP6P1O2n2011000010121100000WDX3DP6P1O2n2011000010121100000WDX4DP6P1O2n2011000010121100000WDX5DP6P1O2n2011000010121100000WDX6DP6P1O2n2011000010121100000WDX7DP6P1O2n2011000010121100000WDX8DP6P1O2n2011000010121100000WDX9DP6P1O2n2011000010121100000WDX:DP6P1O2n2011000010121100000WDX;DP6P1O2n2011000010121100000WDX2DP6P1O2n2011000010121100000WDX=DP6P1O2n2011000010121100000WDX?DP6P1O2n2011000010121100000WDX@DP6P1O2n2011000010121100000b_W_XZ=Q0VQ10AF[j1Q113^X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0D[^Z=eK0nN:0mb{bmbgbubfbcP0Q09Q0:PVPEP_P`PaPRPPQ0~PLQ0sQ0t52CPOPNPQPJP;P5P8Q0eQ0fPhQ0gQ0kQ0lQ0mQ0nPiPjP2P<P3P6MO1Q0oPVQ0pPkP1PlF7P[Q0qP1Q0qP1PmPnP1Q0rQ0tF5E3X0H,0HX1D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX8D,0DX9D,0DX:D,0DX;D,0DX2D,0DX=D,0DX?D,0DX@D,0DXZ=Q0kPEP_P`Q0lQ0mQ0nPiPjQ0<,BCQ0>,BCQ0hQ0iQ0aQ0bQ0oQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wQ0xQ0yQ0{PsP]P\PKMO1Q0?Q0zQ0=PkQ0;PlF4H0leWwWvWsWjWtW}WoWiWrWxWkWpWdWyY04Y01Z037Xq7WaY02WhX<DX>DXADXBDZ09DZ08DZ0ADZ0@DZ0?DZ0>DZ0=DZ0<DZ0;DZ0:DXCDXEDXFDXGDXIDXJDZ07DZ06DXLDXYDX^DY05o"). Qed.

  Lemma zb_nonul : forall s, Forall (fun c => 0 < c < 256)%Z s -> ~ In (Z_to_bv 8 0) (zb s).
  Proof.
    clear. intros s HF IN. unfold zb in IN. apply in_map_iff in IN. destruct IN as (c & E & Hc).
    apply (proj1 (Forall_forall _ s) HF) in Hc.
    assert (E' : bv_unsigned (Z_to_bv 8 c) = bv_unsigned (Z_to_bv 8 0)) by (rewrite E; reflexivity).
    rewrite u8_lit in E' by lia. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in E'. lia.
  Qed.

  (* [comment removed for export] *)
  Definition out_postq (ra' : word) (Ft : bvmap 5 word) (fc : bv 32) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (S : Z) (bs : list Z) (m : word -> option byte) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra') fc None m' (seg_rom bsegs)
      /\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (q + -544)
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ bytes_at bsegs m' S (zb bs).
  Lemma out_callq : forall (rs : region) ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (S L : Z) (bs : list Z),
    SINK m st -> bytes_at bsegs m S (zb bs) -> Forall (fun c => 0 <= c < 256)%Z bs -> L = zlength bs ->
    stk bsegs m lo (q + -544) -> ssp_cells m canary -> mem_inv bsegs m ->
    (0 <= S)%Z -> (S < 2^64)%Z ->
    (S + zlength bs <= lo \/ q + -544 <= S)%Z -> (S + zlength bs <= Fp \/ Fp + 232 <= S)%Z -> (S + zlength bs <= B \/ B + BS <= S)%Z ->
    (zlength bs < 2^31)%Z ->
    (S + zlength bs <= 2^47)%Z ->                                   (* [comment removed for export] *)
    munch W m0 m -> wmono bsegs m0 m -> rclean m0 rs -> inreg rs S (zlength bs) -> rng RNG S (zlength bs) -> rrng RNG rs ->
    implAM RNG (OUT bs) st (out_postq ra' Ft fc s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S bs m)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) FPv a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0xa78d8) fc None m (seg_rom bsegs)).
Proof using Fp B BS RB SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "p'0h04__x1h14__x2h27__arithh34__ffh47__sat48h57__sat49h67__sat50h77__sat51h87__sat52h97__sat53h:8__varmaph;5__with<4cstrh=2Hah>2HOh?4__p1h@4__p2hA4__x3hB4__x4hC2a3hD2a4hE2a5hF2a6hG2a7hH3ms'hI2t0hJ2t1hK2t2hL2t3hM2t4hN2t5hO2t6hP1zhQ1LhR1PhS2SBhT4__x5hU1ahV2a0hW2a1hX2a2hY2m'hZ2s'h[2D1h\2D2h]2D3h^3ENVh_2Eqh`2Esha2Fthb1Hhc2HShd3HS0he3HS1hf3IRShg2LBhh2MIhi3MU0hj4RCBmhk3RCShl4RCSmhm4RNGbhn3RRSho2RShp1Shq3S47hr3SRChs3SSPht2SThu3WM0hv2bshw1chx2fchy1mhz1nh{3ra'h|2rsh}2s0h~2s1i003s10i013s11i022s2i032s3i042s4i052s5i062s6i072s7i082s8i092s9i0:2sti0;3st'i0<1up%0p%1p&0p;1p;2p;3p;Bp;Op;7p;5p;6p;4p;8p;Lp;Ep;:p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0g002TR1p4p710p8P0g0030R3p4p710R4p8P2p1003NR2p4p7210R5p8g004?R6p4p7210P4p8p102Tnp6051000R7P0p8P7p101[ep4p710R0p8P7p102PBp4p710R8p8P7g00:lR9p4p710R:p8P7p1004kp4p710R;p8P7p1006Gp4p710R7p8p102V=p6051000R<P0p8P<P8p8P<P:p8P<P;p8P<P7p8p103RUp6051000R<P2p4p710R2p8P<p103Sbp4p710R<p8P;P4p8p103]7p6051000R;p103_ip4p710R:p8P;P0p8P;P4p8P;p101[Cp4p710R8p8p103^Bp6051000R=P:p8P=P0p8P=P8p8p103`@p6051001R8P0p8P8g00kMR0p4p710p8P8P;p8P8P=p8P8p103_Lp4p710p8p,2StR8p4p300R=P2p8P=g06GcR2p4p710p8P=g056[R;p4p710p8P=P<p8p1059Qp605311001R<P5p8P<P;p4p7210p8p100A_p4p7210P4p8P7P4p8p1006fp4p7210P4p8g007ej16Tg008Jj1cTg008hj1wTg00U[j1FTP6k20VTg00>ck10PTg007Ek105Tg00:1j1KTg014bj1VTg00CPj24Tg00Clj2;TP0j3iTg00;Lj3DTg01B^k10OTg00e7j2>Tg06Hej2WTg01eOj2zTg04C?j3jTg04D3j3nTg04G5j2@Tg05I\j3TTg05Doj3?Tg05D6j2XTg06IdlBrmE01Tg009Kj23Tg05T^lOITg00JBk10:Tg05UPk10XTg05VIj7HTg05fek50WTP9j2uTg00O;j1ZTg04cSk10UTP1j6sTg05g`k30TTg05hgj1hTg05ibk509Tg00P_j1}Tg01m_j2|Tg01nGj3{Tg00R@j1qTg00R_j2fTg00T1j2pTg00FJk106Tg00T]j3PTg00Fjj2eTg01DFk10NTg00U=j4dTg00GHk10MTg00Gfk10ITg00HQj2gTg01fLk304Tg01EGj3bTg00I4k203Tg00Jdk20HTg00@ij2yTg00KFk20GTg00L2k30FTg00LQk40ETg00B<j22Tg01AAj2BTg027nk202Tg027Dj2`TP2k80DTg06JmlL\lOvTg00Qfj2aTg05[Mk70CTg05]Fk100Tg03M@k20BTg016Sj20Tg06Kom:0ATP3k60@Tg00dBk40?Tg00BXk207Tg05b6k40JTg04Pgk20>TP;k70KTg00SHk30LTg00IWj4~Tg00X5k708Tg01Ddk30=Tg00Y=k70<Tg00Yak80QTg00XYk60RTg00V@k70;Tg03X7k40STf0R;#6#6p=Ng00jXR3f2R2f1R1P;H0?p=Qg00[OR9/2;p=5g00;fR0007;p=1%F;#6p=C%6;#6#6#6p=RP3P2P1P;H0Jp=M20>3;p=[2070;,>1p=_f3R6/22121;'ap==%6;#Fp=<%6;#6#6#Vp=Gf4R4/>6/22121;'ap=J%F;#Fp=81>21/2;p=9f5R7g00\LR<P4P6P2P1P;K0Kp=U1u0;p=tB0L01;p=O2030;p=SP0P1g00`GP;C~p=oP1g00[mR5P<P<g00\lR=P;g00]LS00K08p=mP2P5P<P<P=P0P1g00`nP;C~Q00K08p=7B0=01;p=EP2P5P<P<P=P1P;K0<p=YP6P5P<P<P=P2P1P;L0Qp=A131;,`2p=:1u0;#Z,31p=L121;,a2p=]P1P5P<P<P=P;J0Rp=xP2P5P<P<P=P1P;K0;p=kP0P0P1P;H0Sp=l1;1;,;2p=^g04I5g00<DR5#6R:#6S01#6S02#NR>#6R?#cR@#wRA%F:RB#c00VA%c>#wQ02#c#wR>$0P\AS03&050p,4SINKRCP4P6O2%K19Q76%5;%N?RD#V,4;';Xw0S04=i02%169D04P0%14f9REp,2loRFp,1qS05Q02#C#R$0ORG'>RH3Mf:RIp,6canaryRJ'Wf;S06#[%5IQ06%V:RK%V?R?'zRL'4f<S07/_IRMPFPHQ07C=f=S08Q06'_RNp,2FpRO%F5S09#FRP#<#GS0:,>ORQQ08C=f>S0;Q07#1RRp,1BRSp,2BSRT,>SRUQ0;DJQ08#1RV%8P#VRP,zKRW'4f@S0<Q0;#1%FB#8RX#VRY,zKRZ39g04@FR[p,2m0R\fCS0=3jfDR]9n3\faR^,@\fbR_fBS0>#1R`7T]p,3RNGRafERbQ0=#13?fdRc,XaP8Pap,3OUTS0?PbO1fHRdPcfKS0@fJRef`Rff_RgfYRhfXRifWRjfVRkfURlfTRmfSRnfRRofQRpfPRqfGS0APbfIS0BMBrPc13@HRrp,2gpRsp,2tpRtfcRuP_P^PfPgQ0A,3@Q0<,3@13@ORvf^Rwf]Rxf\Ryf[S0CfZS0DPhPiPjPkPlPmPnPoPpPqfORzfNS0EfMS0FfLR{MOIQ0@%<5#N#8#8#N#<#C#8#G,3@S0GPe&0:AS0HQ0B&0X3S0IFHEU[[[[[[[[[[[[[[[[XQ0f8S0J?MFH1WEJ%[I%5E14ILQ06/_EPFPHQ06C=PMPOPQQ07C=PNPSPUQ08C=14RWf?S0K?9VZQ0>9j[\Q0=9n3\1@\fQ0=fAS0L#15T^A?a]`1XauP3PdfFR`%K]R\Q0>I0W%5`1u>\#Z=9`L';g00<iR\%Kb,u>%5d%Z;=9dL';Xz\P;%tbR\&0UbEsQ0A#5Q0A%Z\;9L';f7S0Mf6R\60Te%hefgR>Q0@P\Q0JQ0MI09Q0@/@>p,2RBR[P{p,4RC_BPEQ0JI091@{[Q0B#tRV#}%ZV#51|KYS0N149KRV%5Y149Z[[S0O%5KRRg01X4RNA{KY1UW=S0P%5Z\N^=RS0Q1|K?S0R%5?149L[\VS0SA{K?1VNX=RS0T%5L\N^=RS0U1|KPS0V%5P149W[\VS0WA{KP1VNX=RS0X%5W\N^=RS0Yg00_[S0Zg00bPRR#qRN#qS0[,f0S0\1f0NS0]1f0RS0^'O'Og00boS0_'pQ0Z$06S0`3PQ0Z$05S0aP01e02P1&0N0S0bCdS0c&0M0S0d&0I0RR1g05RN%SKRK%cX6040S0e'o,mRS0f&0:<RXPR%F5#R#<#8#C#R#R#GS0g#S1g0:R:57RS0hPXPR%6B#N#C#N#GS0i#SS0j9b0N97R:PX20309RB%SGS0k,ENS0l57RQ0lB040K@RK'o,mR5YRCACACA20HR=S0mP;P2g00_;R=g00aURP'y20G;2=D=PdB0F091H0ES0nb3b:b;X00X1014;ZS0oQ0g/22Q0i,B2,261>6GR9#5149L';[[[^00^10P;PFQ05p,3QHIS0pp,3GLOS0qp,2LOS0rO5b2b4b5b6b7b8b9b<-02H1`@rR9=D0H%teRP#}%ZP#5Q0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WQ0XQ0YQ0`Q0a1e01S0sQ0dPR1oNK,mRRKPXPRA7RBNRBPXAYRBKCACAQ0mQ0nb3b:b;X0014;L%51%52142L';[[^00P;PmQ0BPeO3b2b4b5b6b7b8b9b<-02{A:@@{=D0{p,4HOUTP8POPSPTP[PCp,5TOPOKS0tQ0?L0DP;PaflS0ufkS0vPrPsPtfjS0wfiRLfhRBP>ffRKQ0E,3@1L@{PvfeRPPcPuP_P^PfPgPwPxPyQ0CQ0DPhPiPjPkPlPmPnPoPpPqPzP{PFPJOXPCPqPzO2A:@@zQ0F#K5QpQ04Q0E5i0%1zS0x/4W1L@q%1qS0y,3@5DAADAvvS0zAMkF9g06LlS0{,B9,2Fg06Mo/2FS0|149ZQ0tP9O1Q0C/WJ%[y12QFS0}?]9O12UFS0~?]9SA:@@xR=Q0C'_PFP9P=C=A:@@wS10/_yS11POPQQ10C=A:@@gS12%1xS13'>S14PSPUQ12C=g04;d/2FS15%hup+01AS16,@cp+01BR=A:@@u%1^3T1@K[AT[STS171B9F9?aF%6D#R#G%65#8#8#8#8#C#R#R#G5?aS18A:@@B%1K5?aQ0:9?aOS19A?aSTS1:p+01JS1;,Xa1Xa[S1<fmRD9:@@Q0v#1;9ZP8PaQ0?Q0uO1foRVP8POPSPTPCp+01LS1=PrPsPtp+01HS1>p+01GS1?Q16p+01@S1@f~S1Af}S1Bf|S1Cf{S1DfzS1EfyS1FfxS1GfwS1HfrR?fqRYfnRM,3@R|,`@S1IQ0uPFPJfpS1JML\Q1=PrPsPtp+01KS1KQ1;p+01IS1LQ1>Q1?P|Q0u,L@Pvp+01FS1Mp+01ES1Np+01DR|p+01CR}P=Q16Q1@Q1AQ1BQ1CQ1DQ1EQ1FQ1GQ1HfvS1OfuS1PftS1QfsR~MOIP?Q0GPYQ0HQ1JQ0IFHEU[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[P0P9PCPoPpO2S1R13@pS1S,`@%KzS1T5QnQ04=i0qS1U%1pS1V/4WS1W1L@o%1oS1X,3@5DAS1YQ0zAMiF\Q0MQ0{'B,2FQ0|14EZQ0tPIO11WxJS1Z%[wS1[Q0}Q08;]OQ0~Q0;;]SQ14PFQ0KQ12C=A:@@fS1\%1wS1]'>S1^POPQQ1\C=A:@@^S1_%1gS1`PSPUQ1_DJQ15%hPS1_1@K}S1aA:@@P%1uS1b5T|1@B[S1cQ171BdF9?aFQ18Q0w9:@@%1BS1d5?aQ19Q1:Q1=,XaS1eQ1<13@VS1f,`@S1g%1DS1h;9ZP8PaQ0?PMO1S1iPYP8POPSPTPCp+01NS1jPrPsPtQ1;Q1LP}P=Q16Q1@Q1AQ1BQ1CQ1DQ1EQ1FQ1QP~Q1J,3@S1k,`@PMPFPJP?ML\Q1jPrPsPtp+01MS1lQ1=Q1KQ1;Q1LQ1k1L@MPvQ1>Q1?Q1MQ1NP|P}P=Q16Q1@Q1AQ1BQ1CQ1DQ1EQ1FQ1GQ1HQ1OQ1PMOIQ1QQ0GP~Q0HP?Q0IFHS1kEU[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[XP0P;PHP6EsPCPpPqO2A:@@qS1mQ0E#K5QoQ04=i0zQ0y/4W1L@pQ1V,3@5DAQ0zAMjFHQ0{,BH,2FS0{Q0|14HZS1VQ0tPHO1S0t1WyJ%[xQ0}?]HOS0}Q0~?]HSS0~Q11PFPHQ10C=Q14POPQQ12C=Q1^PSPUQ1\C=Q15%hc1@P=A:@@c%1_5T}1@>[Q171BHFS1\9?aFS1^Q18A:@@L%1>5?aQ19Q1:Q1K,XaQ1<Q1IQ0u#1;9ZP8PaQ0?PDO1Q1JP8POPSPTPCQ1lPrPsPtQ1LQ1>P=Q16Q1@Q1AQ1BQ1CQ1DQ1EQ1FQ1GP~P?Q1gPDPFPJPYML\Q1lPrPsPtQ1=Q1KQ1;Q1LQ1>Q1f1L@DPvQ1?Q1MQ1NP|P}P=Q16Q1@Q1AQ1BQ1CQ1DQ1EQ1FQ1GQ1HQ1OQ1PQ1QMOIP~Q0GP?Q0HPYQ0IFHEU[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[P0Q1mPCPnPoO2%Kq9Qm1Q04=i0pQ1X/4W1L@n%1n,3@5DAQ0zAMhFHQ0{Q0|Q1VQ0t1WwJ%[gQ0}Q0~Q0KQ1]PFPHQ0KDJQ0<Q1`POPQQ0<DJQ0L/_fPSPUQ0LC=Q15%hK1@>|Q1N%1c7Tb1@L[Q17Q1^Q18%1L9?aeQ19Q1:Q1l,XaQ1<%1M=9zZP8PaQ0?PVO1P?P8POPSPTPCp+01OR[PrPsPtQ1KQ1;P|P}P=Q16Q1@Q1AQ1BQ1CQ1DQ1EQ1PQ1QPqPVPFPJP~ML\P[PrPsPtQ1jQ1lQ1=Q1KQ1;13@Y1L@VPvQ1LQ1>Q1?Q1MQ1NP|P}P=Q16Q1@Q1AQ1BQ1CQ1DQ1EQ1FQ1GQ1HQ1OMOIQ1PQ0GQ1QQ0HP~Q0IFHEU[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[XP0P;PqP6EsQ1RQ1T9QnpQ1UQ1WQ1YQ0zAMiFHQ0{Q0|Q1VQ0tQ1ZQ1[Q0}Q0~PgQ13PFPHPgDJPfQ1]POPQPfDJP^Q1`PSPUP^DJQ15Q1_Q1aQ1b9T|PQ1cQ17Q1^Q18Q0wQ1d5?aQ19Q1:Q1eQ1<Q1h=9VZP8PaQ1iPYP8POPSPTPCQ1jPrPsPtQ1;Q1LP}P=Q16Q1@Q1AQ1BQ1CQ1DQ1EQ1FQ1QP~Q1JPMPFPJP?ML\Q1kEU[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[P8P<PaQ0?PzO1PoP8POPSPTPCPMPrPsPtQ0wPLPuP_P^PfPgPwPxPyQ0CQ0DPlPmPpPzPFPJPnML\PMPlPmQ0wPLPuP_P^PfPgPwPxPyQ0CQ0DPpPzPnMBrPMPrPsPtPDQ0uQ0vQ0wPLQ1S%tzR=#ZR[,3@PvPBP>PKPPPcPuP_P^PfPgPwPxPyQ0CQ0DPhPiPjPkMOIPlQ0GPmQ0HPnQ0IFHP;Q0EQ0FP{Q0>Q0x,3@,yA1yAvPe%}=R=%5[R[Q0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WQ0XQ0YQ0`Q0aQ0cQ0dPRQ0j9b0:97RNPXQ0k,E:S0jQ01#C#C#N#GRW#S5b097RNCAQ0mQ0nb3b:b;X00X10Q0i,B1,2;1>2G/BW,21[^00^10P;Q05PFQ0rO3b2b4b5b6b7b8b9b<Q0{eQ0qP=P[Q0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WQ0XQ0YQ0`Q0aQ0sQ0dPRQ0fPXQ0lQ0e'o,mRCAQ0mQ0nb3b:b;X00Q0o1>1GS0e/4Z[^00P;Q05Q0pO2b2b4b5b6b7b8b9b<Q1Vep,3TOKPHQ05P=P[Q0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WQ0XQ0YQ0`Q0aQ0sQ0dQ0l=7RNQ0mQ0nb3b:b;X00A9;G;^00P;Q05O1b2b4b5b6b7b8b9b<p,2TQO4Q0teQ0BPdP=P[Q0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WQ0XQ0Yp-0RZQ0ZQ0[#qRW,f0S0[Q0\Q0]'O'OQ0_'pQ0Z%qW,f0Q0[Q0^'O'OQ0_'pQ0`3P3PQ0aP0P01e04S0]P2Q0bCdP11e06S0bCdQ0dPRQ09,g0S0tQ01,g0RW57RPXPR1xR\Q0:#S,ENS01%<5#8#<#N#<#<#8#8#GS0l#S57R5YRQ02#VS02#SS0s,EW=7RNQ0M,xRS1V5YR5kRPXPRQ0hPXQ01=7R:Q0tQ0k'E=7RN5kRCACACAQ0mQ0nb3b:b;X00X10XA0XB0X?ZW@1226Q0:Q0l591,;7Q02=941/;\'aQ0g/26P6Q0:P41>7GS0:P6DJ[[[^00^10^A0^B0^?Z^@ZP;p,2VAS0g,2Q%<5#C#<#8#8#8#<#C#G/2Op,2APS0lQ05PFPOp,3HAPS01p,5SEP_FQ0qO9b2b4b5b6b7b8b9b<Q0}eP=P[Q0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0^'O'OQ0_'pQ0`3PQ0aP0P0Q0]P21e07CdP1Q0bCdQ0dPRQ09#6,g0RG97RWPXPRQ1V1EN:Q0t57RS0t5YRQ0s,EG=7RNQ0J,xR5YR5kRPXQ0tQ0k,EW=7RN5kRCACAQ0mQ0nb3b:b;X00X10XA0XB0XT0X?ZX@Z1264A9126,;\Q02=971Q0M';'aP2P6P4Q0:P2DJ[[^00^10^A0^B0^T0^?Z^@ZP;Q0g,2U%F5#R#<#C#C#<#<#C#8#G/2SQ0lQ05PFPTPSQ01p,5SEP_BO9b2b4b5b6b7b8b9b<Q0~ePbP]Q0=p,2KHQ0JQ0MQ08P\p,3RBIPaPFQ05/BFPFQ1\p,6RG_stkP=P[Q0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WQ0XQ0YQ0`Q0aQ0cQ0dA7RNNQ0j=b0N,ENAb0:N,EN57R5YRQ0mQ0nb3b:b;X00X1012;;Q0e/B;1B1;,>;59;';^00^10P;Q05PFO2b2b4b5b6b7b8b9b<K0CQ1^ep,6RG_imgQ07p,4RG_Fp,4RG_BQ06p,4RR_BQ0LOPP<g057SRRP8POPSPTPCP?PrPsPtPMPDP>PKPPPcPuP_P^PfPgPwPhPiPlPnPFPJPjP2P1P;MOvP~Q0DPhPVPMPBP>PKPPPcPuP_P^PfPgPkPmPiP6P2P1NE01[]H^Z8P;P8POPSPTPCPYPrPsPtPDQ0uPKPPPcPuP_P^PfPgPwPxPiPjPmPoPFPJPkQ00P1P;MOvP0P9Q03Q03Q0>P|PrPsPtQ0KQ0;Q08Q1@Q1AQ07Q06PIPEQ0JQ0MP\P7Q1GQ1HQ1OQ1PQ1QP~P?PYQ1JPVP4P6P2P1MOIQ0w&00|PLQ0HP;Q0IFH5DR20B00R|Q0<,lF1lOQ1lSU&06|5P|5P|RU3P?jB;An3B;%[;RQQ0<9M;FPCP;Q0=O21W;JR9%Kc9Q;K';3^3^3^WY'0XOA,0AXNA,0AXMA,0AXLA,0AXGA,0AXFA,0AXEA,0AXDA,0AXCA,0AXXA,0AXWA,0AXVA,0AXKA,0AXJA,0AXIA,0AXP0P;PHPEEsQ03Q03Q0LP}PrPsPtQ0KQ0;Q08Q1AQ1BQ07Q06PIPEQ0JQ0MP\P7Q1HQ1OQ1PQ1QP~P?PYQ1JPVPMP4P6P2P1MOIPL&00}PBQ0HP;Q0IFH5DR1lFH=P|U?j>;An3>;AM;FHPCP;Q0>O2%Ku9Q;P,;93^7^Q3^WY'0XOA,0AXNA,0AXMA,0AXLA,0AXGA,0AXFA,0AXEA,0AXDA,0AXCA,0AXXA,0AXWA,0AXVA,0AXKA,0AXJA,0AXIA,0AP;bRWRXHRZ0;8n0110<000101XU<P8POPSPTPCPYPrPsPtPDQ0uPKPPPcPuP_P^PfPgPwPxPiPjPmPoPFPJPkP2P1P;MOvP?PhPiPMPDP>PKPPPcPuP_P^PfPgPwPlPnPjP6P2P1NE01[^HR^Z8^U<eN:0Ab>b>b>b>b`b_bjblb^P8PaQ0?P`O1Q0BPPP{Q0@P^PfQ0DPhPiPjPkPlPmPnPoPpPdP`PeMBrPPPrPsPtPcPuP_P^Pf13@d%1`,3@PvPgPwPxPyQ0CQ0DPhPiPjPkPlPmPnPoPpPqPzQ0EQ0FMOIP{Q0GQ0@Q0HPeQ0IFHEUebSbSP8PaQ0?P]O1Q0APuPeQ0BPgPwPiPjPkPlPmPnPoPpPqPzP`P]PdMBrPuPrPsPtP_P^PfPgPw13@`%1],3@PvPxPyQ0CQ0DPhPiPjPkPlPmPnPoPpPqPzQ0EQ0FP{Q0@MOIPeQ0GQ0BQ0HPdQ0IFHEUeWnWoWfWkWuWiWqWgW]W\W[WeWdWhWsWtP7P;J0@WbWmWrWcWvXQ0Xp0Z0:8WyWxWaXOAXNAXMAXLAZ01AZ00AZ09AZ08AZ07AZ06AZ05AZ04AZ03AZ02AXGAXFAXEAXDAXCAX~AX}AXKAXJAXIAW{W|o"). Qed.

  (* [comment removed for export] *)
  Definition fp_postq (ra' : word) (Ft : bvmap 5 word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (m : word -> option byte) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
      ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft' (ret_pc ra') fc' None m' (seg_rom bsegs)
      /\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ frm0 fc' /\ Fokd Ft Ft'
      /\ stk bsegs m' lo (q + -544)
      /\ SINK m' st'
      /\ ssp_cells m' canary.
  Lemma fp_callq : forall ra' t0 t1 t2 s0 s1 (a1 a2 a7 : word) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (y w p fl t : Z),
    fpcall_stmt Fp B BS RB SINK TOPOK OUTFP (y, w, p, fl, t) ->
    SINK m st -> y = (bv_unsigned a1 + 2^64 * bv_unsigned a2)%Z -> bv_unsigned a7 <> 5%Z ->
    (-2^31 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
    stk bsegs m lo (q + -544) -> ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
    munch W m0 m -> wmono bsegs m0 m ->
    implAM RNG (OUTFP y w p fl t) st (fp_postq ra' Ft s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 FPv a1 a2 (Z_to_bv 64 w) (Z_to_bv 64 p) (Z_to_bv 64 fl) (Z_to_bv 64 t) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0xa8e80) fc None m (seg_rom bsegs)).
Proof using Fp B BS RB SINK TOPOK OUTFP TOK RNG q gp tp m0 lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["CANSEC3"; "PrintfCore"] "p'0h04__x1h12Hah24__x2h37__arithh44__ffh57__sat12h67__sat13h77__sat14h87__sat15h97__sat16h:7__sat17h;7__sat18h<7__sat19h=7__sat20h>7__sat21h?8__varmaph@5__withA4__p1hB4__p2hC4__x3hD4__x4hE3FPChF2FthG2a1hH2a2hI2a7hJ2t0hK2t1hL2t2hM2t3hN2t4hO2t5hP2t6hQ1PhR4__x5hS2a3hT2a4hU2a5hV2a6hW3fc'hX1khY2m'hZ3ms'h[1zh\3ENVh]2Eqh^3FRMh_2H7h`2HSha3Hflhb2Hphc2Hthd3Htahe2Hwhf2Hyhg2MIhh3MU0hi4RCBmhj3SSPhk2SThl3WM0hm1ahn2fcho2flhp1mhq1phr1rhs3ra'ht2s'hu2s0hv2s1hw3s10hx3s11hy2s2hz2s3h{2s4h|2s5h}2s6h~2s7i002s8i012s9i022sti033st'i041ti051wi061yp%0p%1p&0p;1p;2p;4p;9p;3p;5p;Ip;Op;7p;6p;?p;Lp;Bp;:p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p7210R2p8P0P1p4p73110p8P0p1001Cp4p7210p8p10027p4p710R0g002TR1p4p710p8P0p10030p4p710R3p8P2p1003NR2p4p7210R4p8g004?R5p4p7210P3p8p102Tnp6051000R6P0p8P6p101[ep4p710R0p8P6p102PBp4p710R7p8P6p100:lp4p710R8p8P6p1004kp4p710R9p8P6p1006Gp4p710R6p8p102V=p6051000R:P0p8P:P7p8P:P8p8P:P9p8P:P6p8p103RUp6051000R:P2p4p710R2p8P:p103Sbp4p710R:p8P9P3p8p103]7p6051000R9p103_ip4p710R8p8P9P0p8P9P3p8P9p101[Cp4p710R7p8p103^Bp6051000R;P8p8P;P0p8P;P7p8p103`@p6051001R7P0p8P7p100kMp4p710p8P7P9p8P7P;p8P7p103_Lp4p710p8p,2StR7p4p300R;P2p8P;g06O0R2p4p710p8P;g056[R9p4p710p8P;P:p8p1059Qp605311001R:P4p8P:P9p4p7210p8p100A_p4p7210P3p8P6P3p8p1006fp4p7210P3p8g007ej12Tg008Jj1ZTg008hj1lTg00U[j1>TP5k20MTg00>ck10FTg03M@j2qTg03X7j4dTP2m907Tg027Dj2?Tg014bj19Tg01eOj2aTg01jGj2kTg00e7j2:Tg01hSk10ETg00B<j21Tg00Clj2;Tg025jj2hTg01B^k109Tg06Hej2WTg04Pgj2VTg06P5j1YTg04C?j3rTg04D3j3uTg05g`k302Tg05hgj1iTg05ibk500Tg04G5j2cTg01m_j2UTg01nGj3bTg00R@j1mTg00R_j2`Tg00T1j2jTg00FJj1~Tg00T]j3JTg007Ek10NTg00Fjj2^Tg01DFk10LTg00U=j4_Tg00GHk10KTg00Gfk10JTg00HQj2\Tg01fLj3}Tg00JBj1{Tg01EGj3[Tg00I4j2zTg00Jdk20BTg00@ij2RTg00KFk20ATg00;Lj3=Tg00L2k30@Tg00LQk40?Tg00CPj2OTg01AAj2<Tg027nk20>Tg009Kj23Tg05I\k30=Tg05Doj3STg05D6k20<Tg06PelIgmL0:Tg05T^lOMTg05UPk10;Tg05VIj7NTP9j7fTP1j6yTg06Qjl?xmB06Tg00Qfj2oTg05[Mk708Tg05]Fj1wTg04K8j2pTg016Sj20Tg06Kom:05Tg00MCk104Tg05b6k40CTg00SHk30DTg00IWj4vTg00X5j7|Tg01Ddk303Tg00Y=k70GTg00Yak80HTg00XYk60ITg00V@k701Tf0R1#2#2p=Kg00;fR9P9f1R2P1Cdp=XA=921p=]A=921$04p=C%>1#>p=7f2R51O21';p=8g00[OR3/11p=6%21#>p=4%>1#2p=D%21#2#2#2p=Eg00jXR6P5P2P1H0Cp=P1O31p=TB0D921p=L1z91p=GP9P2g00`GP1Cvp=tP2g00[mR:g00\LR4P4g00\lR;P1g00]LR0F|p=s%21#2#2#9p=BP5P:P4P4P;P9P2g00`nP1CvP0F|p=5B03921p=AP5P:P4P4P;P2P1K0Gp=Qf3R0P:P4P4P;P5P2P1L0Hp=@1121,o5p=I1:52/11p=FP2P:P4P4P;P1J0Ip=nP5P:P4P4P;P2P1K01p=e1;21,;5p=Hg00<DR:#2R8#2S00#2S01#KR<#2R=#ZR>#lR?%>8R@#ZS0200M?RA%Z<#lRBQ01#Z#l$0F\?RCP7p,2FpRDp,1BREp,2BSRFp,2RBRGp,4SINKRHp,5TOPOKS03p,5OUTFPS041q99RI/q9RJ/q9P9PJP9PIP9f4RJ/X0P5CdP2CdP1CdN907PHf7RKf6RLO2fKS05,?>%98RM%9=RN'aROfJRP,?>RQ'k':,]L%9@S06,CQ%>:S07#>RQ#7#9RR,aMRS$0ES08/1KRT%9:RU,1K';%2@S09#2RV#9RW,aMRX98TK%6KRT%9<R<,aMRY78K%K=R=#9RZ98TKf8S0:/h<Q07#2S0;#K#4#9RT'Cf?S0<p,2loR[p,1qR\Q01#D#E$09R]':R^3Pf@R_p,6canaryR`'WfARa,V6fCRb#Yg04@Fp,2m0Rc;rbfDS0=9u6cfERc@0221%icPGfFRdp,4RC_BP5P2I001cdG1UM<S0>%TMRe%6<%TY[[S0?%6MRfg01X4RgAbM<2UW1S0@%6Y\g^1fS0A%>@#7R@#9Rh,UMS0B%6h1aMhRi#T[\eS0CAbMh2VgX1fS0D%6i\g^1fS0E1UMWS0F%6W%TX[\eS0GAbMW2VgX1fS0H%6X\g^1fS0I1UMNS0J%6N%TO[\eS0KAbMN2VgX1fS0L%6O\g^1fS0M1UMRS0N%6R%TS[\eS0OAbMR2VgX1fS0P%6S\g^1fS0Qg00_[Rfg00bPRg#mRS#mS0R,`9S0S1`9SS0T1`9gS0U'L'Lg00boS0V'j%~fRg3J&0NfS0WP91^95P2&0L9S0XC_S0Y&0K9S0Z&0J9RS1\9:RR%GMRM%Z@5}9S0['t,sSS0\%{4R4PS%>:#E#4#7#D#E#E#BS0]#G1\98R855SS0^P4PS%2V#D#K#BS0_#GS0`9[9R95S8P41z93%G]S0a,ARS0b55SQ0bA}9M>'t,sS5QSC@C@C@20BS;S0cP1P5g00_;R;g00aURM'R20A15==;MdB0@932H0?S0db4b?b@X09X291O1iS0eQ0]/15Q0_,<5,101:0]R3#6?83O[[[^09^29P1P[P\p,3QHIS0fp,3GLOS0gp,2LOS0hO5b3b5b6b7b8b9b:b;b<b=b>-0>^13>^R3,?>RM/]^Pap,3RNGR;faRVP3p,2gpR@p,2tpRef`RNf_RWf^Rhf]Rjf\Rk13>DRlf[RmfZRn13>cS0iQ0=,3>S0j13>bfBS0k,3>S0lfYRofXS0mfWRpfVRqfURrfTS0nfSS0ofRS0pfQS0qfPS0rfORsfNRtfMRufLS0sQ05PPfIRvfHRwfGRxP[P`OVPHPwPxO21?>kS0t1?>m,kO':,]xA=?llS0u13>wRy==?yRy1?>NQ06'CQ08/1uRz11uU';A8zuX%6uRz?8uYA8zuZ1ht</CTAPr[Mg06S2S0v,<M,1[g06Mo/1[S0w1OMiQ03PMO11Wn`1V6m%Yj%4Q#BRQ,:DS0x/1[S0y?IMD1:EFS0z/1[S0{?IMEg04;d/1[S0|%iN1cVGB0=GEFS0}1<M[9S;[%2=#E#B%2:#7#7#7#7#D#E#E#B5S;S0~AS;DQS10AS;EFS1120<;GS12P7P9P;Q04ffS13feS14fdS15fcR=fbRzO5fgR{P7PDPEPFPHp+01BS16P3P@Pef}S17f|S18fxR|fwS19fvS1:fuS1;ftR}fsS1<frS1=fqS1>fpS1?foS1@fjS1AP[P`fhS1BMIgQ16P3P@Pep+01AS1Cp+01@S1Df~S1EQ17Q18Plf{S1FfzS1GQ14,3>S1HQ15,3>S1I13>=S1J13>zfyR~P|Q19Q1:Q1;P}Q1<Q1=Q1>Q1?Q1@fnS1KfmS1LflS1MfkS1NMOMQ1A%4:#4#K#4#7#4#E#B,3>S1OfiS1P%{?S1QQ1B&0;6S1RFNFf[[[[[[[[[[[[[[[[[[[[[[[[[\y\y\y[[[[P9PMPHPPPvO21?>h1?>jS1S,kO':,]vQ0u13>PRy==?yRy1?>zQ06'CQ08/1sS1T11sU';Q1T?8sX%6sS1T?8sYQ1T?8sZQ0r/h</CTf=S1T9Pp[f>S1UQ0v'<,1[Q0w1O_iQ03PaO11Wk`1V6j%YWQ0y?IcDQ0{?IdEQ0|%iz1c=GQ0}Q05/<[9S;[Q0~Q10Q11Q12P7P9P;Q04Q1BP{Q13Q14Q15O5Q1PP7PDPEPFPHp+01DS1VP3P@PeQ1DQ1EQ1GP~P|Q19Q1:Q1;P}Q1<Q1=Q1>Q1MP[P`Q1AMIgQ1VP3P@Pep+01CS1VQ16Q1CQ1DQ1EPlQ17Q1813>{Q13,3>S1WQ1HQ1IQ1FQ1GP~P|Q19Q1:Q1;P}Q1<Q1=Q1>Q1?Q1@Q1KQ1LMOMQ1MQ1OQ1NQ1QQ1AQ1RFNFf[[[[[[[[[[[[[[[[[[[[[[[[[\y\y\y[[[[X[9P1P^P2EyPHPvPwO2Q1SQ0t,kO':,]wQ0u13>vRO==?ORO1?>VQ06'CQ08/1tRy11tU';A8ytX%6tRy?8tYA8ytZ1hs</CTAPq[^Q0v,<^,1[RTQ0w1O^iR<Q03P^O1Ry1Wm`1V6k%YhQ0y?I^DS0yQ0{?I^ES0{Q0|%iV1czGQ0}1<^[S039S;[S0vQ0~Q10Q11Q12P7P9P;Q04P{Q13Q14Q15P=O5Q1BP7PDPEPFPHQ1VP3P@PeQ1EQ17P~P|Q19Q1:Q1;P}Q1<Q1=Q1>Q1?Q1NP[P`Q1PMIgQ1VP3P@PeQ16Q1CQ1DQ1EQ17PlQ18Q1FQ1WQ1HQ1IQ1JQ1GP~P|Q19Q1:Q1;P}Q1<Q1=Q1>Q1?Q1@Q1KQ1LQ1MMOMQ1NQ1OQ1AQ1QQ1PQ1RFNFf[[[[[[[[[[[[[[[[[[[[[[[[[\O\O\O[[[[P7P9P;Q04PwPxPdPcQ0=O5PvP7PDPEPFPHP=P3P@PePWPhPnPoQ0mPpPqPrQ0nQ0oQ0pQ0qQ0sP[P`PPMIgP=Q0sPWPhPnPoQ0mPpPqPrQ0nQ0oQ0pQ0qPPM?xP=P3P@PePzPVPNPWPhPlPjPk13>xRO13>dRGQ0iQ0jPmPnPoQ0mPpPqPrQ0nQ0oQ0pQ0qQ0rPsPtPuMOMQ0sQ1OQ05Q1QPPQ1RFNP1Q0kPa1R?l1R?O1R?GQ0i,R?Q0j,R?P_Q0<Q1UQ1Tf<S0uf;S0wf:S0|Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0NQ0OQ0PQ0QQ0JQ0KQ0LQ0MPgQ0WQ0YQ0ZPSQ0`9[9895SRP4Q0a,A8S0`Q00#>#K#4#K#BRG#G5[995SRC@Q0cQ0db4b?b@X09X29Q0_,<2,111:5]/<G,12[^09^29P1P\P[Q0hO3b3b5b6b7b8b9b:b;b<b=b>PTeQ0gQ0BQ0CQ0DQ0EQ0>Q0?Q0@Q0AQ0FQ0GQ0HQ0IQ0NQ0OQ0PQ0QQ0JQ0KQ0LQ0MPgQ0W1^92RTQ0ZPSQ0\P4Q0bQ0['t,sSC@Q0cQ0db4b?b@X09Q0e1:2]RG/Oi[^09P1P\Q0fO2b3b5b6b7b8b9b:b;b<b=b>P<ep,3TOKP^P\Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0NQ0OQ0PQ0QQ0JQ0KQ0LQ0MPgQ0WPTQ0ZQ0b=5SRQ0cQ0db4b?b@X09AF1]1^09P1P\O1b3b5b6b7b8b9b:b;b<b=b>p,2TQO4Pyef9S0bQ0:PKQ0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0NQ0OQ0PQ0QQ0JQ0KQ0LQ0Mp-0RyQ0R#mRT,`9R<Q0SQ0T'L'LQ0V'j%mT,`9Q0U,L<'LQ0V'j=Jfg5JfQ0WP9P91^9JS0TP5Q0XC_P21^90S0XC_Q0ZPSQ07,\9RTQ00,\9Ri55SP4PS1nSL%GQ,ARRO%4:#7#4#K#4#4#7#7#BRZ#G55S5QSQ01#9RY#GRX,Ai=5SR1nSKRU5QS5eSP4PSQ0^P4A5SO8Q0a,AT=5SR5eSC@C@C@Q0cQ0db4b?b@X09X29XC9XD9XAyWB1150f5ROAF2QZ';AFJY2/;L'oQ0]/10AF0QJ1:O]R];I0[[[^09^29^C9^D9^Ay^ByP1Q0xp,2VARQ'1%4:#D#4#7#7#7#4#D#B/1Dp,2APS0]P\P[PDp,3HAPRZp,5SEP_FQ0gO9b3b5b6b7b8b9b:b;b<b=b>Q0yeQ0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0NQ0OQ0PQ0QQ0JQ0KQ0LQ0MQ0SQ0U'L,L<Q0V'j=JfgQ0WP9P9Q0TP51^9OC_P2Q0XC_Q0ZPSQ0;,\9Rf95SiP4PS1AR8=5STRT9QSU1AfX=5SRQ0:,nS5QS5eSP4Q0a,Ai=5SR9eSTC@C@Q0cQ0db4b?b@X09X29XC9XD9XR9XAyXBy110JAF250,;LAFOY2/;K'oAF50J?I]5[[^09^29^C9^D9^R9^Ay^ByP1Q0z/1Q%>:#E#4#D#D#4#4#D#7#B/1EQ0]P\P[PFPEPZp,5SEP_BO9b3b5b6b7b8b9b:b;b<b=b>Q0{ep,2KHPJP0p,3RBIP;P[1<\[P[Q03p,6RG_stkQ0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0NQ0OQ0PQ0QQ0JQ0KQ0LQ0MPgQ0WQ0YQ0ZA5SRRQ0`=[9R,ARA[98R,AR55S5QSQ0cQ0db4b?b@X09X2911111<G11<21,:15F1';^09^29P1P\P[O2b3b5b6b7b8b9b:b;b<b=b>K08Q0vep,6RG_imgp,4RG_Fp,4RG_Bp,4RR_BOPg057SR\P7PDPEPFPHQ13P3P@PePzPVPjPkPmPnPoQ0mPpPqPrQ0nPsP[P`PuP5P2P1NL0:RVP9PMP~P3P@PeP_Q0<Q1UQ1;P}Q0iQ1TQ0uQ0wQ0|Q0bQ0:PKQ1?Q1@Q1KQ1LQ1MQ1NQ1AQ1PQ1BP{PLPOPJP0MOMP5%w~P2Q1QP1Q1RFN9=\b1X[aQ0x,XDQ0z,XE%~I5JI5JIRE5JI?rN1Au6N11V61RN%Y2RDQ02#lR~Q02/?1Q09#9'CRM1pJ2RFQ15/p25=?[]XAP1[aPHP1Q0=O21W1`R`3H3H3H3HXYC,0CXWB,0BXFA,0AXP?,0?XO?,0?XN?,0?XM?,0?XI?,0?XV?,0?XU?,0?XT?,0?XS?,0?XH?,0?XG?,0?XL?,0?XK?,0?XJ?,0?X[9P1P^PLEyQ0kP|P3P@PeP_Q0<Q1UP}Q1<Q0jQ1TQ0uQ0wQ0|Q0bQ0:PKQ1@Q1KQ1LQ1MQ1NQ1AQ1PQ1BP{Q13PLPOPJP0MOMP5%w|P2Q1QP1Q1RFN5=\1X[^=JIE?rW1Au6W11p=29=?F\M^X~AP1[^PHP1PbO2;H`5HD7HN3HXYC,0CXWB,0BXFA,0AXP?,0?XO?,0?XN?,0?XM?,0?XI?,0?XV?,0?XU?,0?XT?,0?XS?,0?XH?,0?XG?,0?XL?,0?XK?,0?XJ?,0?P1bQWQWZZ037Xr9P{Q0rP=PzPhPjPkPmPnPoQ0mPpPqPrPtP0P5P2NB06\V^Z\^t7^m9eN:05bEbEb]bib\P7P9P;Q04PbQ0kPaP_Q0<O5Q0=PhPxPnPoPrQ0nQ0oQ0pQ0qQ0rPsPtPuQ0sPcM?xPhP3P@PePjPkPmPnPoPlQ0mPpQ0l13>a13>_Q0<,3>PqPrQ0nQ0oQ0pQ0qQ0rPsPtPuQ0sQ05PPPvPwMOMPxQ1OPdQ1QPcQ1RFNFfeWlWhW^WgWjWkWdWcWaWbWeW_WfW`WEZ049Xo9Xq9Z059Z069Z027WpWnWFXP?XO?XN?XM?Xx?Xw?Z01?Z00?X~?X}?X|?X{?Xz?Xy?XI?XH?XG?Xv?Xu?XL?XK?XJ?Wso"). Qed.

  Lemma conv_type_dbl : forall t, conv_type t = Some T_DBL -> (69 <= t <= 103)%Z /\ Z.lor t 32 <> 97%Z.
  Proof.
    clear. intros t CT. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in CT.
    repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [try discriminate CT|] end; try discriminate CT.
    repeat match goal with E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
      subst; (split; [lia | discriminate]).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac len_norm := unfold zlength, zrepeat; rewrite ?repeat_length, ?zb_length, ?length_map, ?length_firstn, ?length_skipn, ?length_app; cbn [length]; try rewrite !Z2Nat.id by lia.
  Ltac inreg_side := solve [ unfold inreg in *; len_norm; unfold zlength in *; lia ].
  Ltac rng_side :=
    lazymatch goal with |- rng ?RNG0 ?lo' ?len' =>
      first [ assumption
            | match goal with H : rng RNG0 ?lo ?len |- _ => apply (rng_sub' RNG0 lo len lo' len' H); solve [len_norm; unfold zlength in *; lia] end ]
    end.
  Ltac out_call_with r :=
    ileave; eapply implAM_bind;
    [ eapply (out_callq r);
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 721936 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 6203920 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | |
      | match goal with H : munch _ m0 _ |- _ => exact H end
      | match goal with H : wmono _ m0 _ |- _ => exact H end
      | first [ assumption | idtac ]
      | first [ inreg_side | idtac ]
      | first [ rng_side | idtac ]
      | first [ assumption | idtac ] ]
    | cbv beta ].
  Tactic Notation "out_call" constr(r) := out_call_with r.
  Tactic Notation "out_call" := out_call_with rfmt.
  (* [comment removed for export] *)
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call bsegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [bsegs bsegs] in *; fold bsegs in *.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition S_EXIT : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 apv] ->
      frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
      evtF bsegs RNG (POST r st)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8c24) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_SCAN : Prop :=
    forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n cnt' : Z) (Q : machine_state -> Prop),
      let _ := ctx_all in
      finv m ->
      (0 <= i)%Z -> (0 <= n)%Z -> (i + n < zlength fmt)%Z ->
      (forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
      (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->
      (0 < n \/ znth fmt i = 37)%Z ->
      (0 <= cnt' <= INT_MAX)%Z -> (n <= INT_MAX - cnt')%Z ->
      (forall a1 a2 : word,
         evtF bsegs RNG Q
           (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (2147483647 - cnt')) (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) (Z_to_bv 64 n) (Z_to_bv 64 (A + i)) x24 x25 (Z_to_bv 64 n) x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0xa7f70) fc None m (seg_rom bsegs))) ->
      evtF bsegs RNG Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt i)) x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 cnt') x20 x21 x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa7f14) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_FLAGS : Prop :=
    forall (x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (p k fl b : Z) (w3 : word) (FL : Z) (s1 : list Z),
      let _ := ctx_all in
      finv m -> (0 <= p)%Z -> (1 <= k)%Z -> (p + k <= zlength fmt)%Z ->
      bv_unsigned w3 = b -> (0 <= fl < 131072)%Z -> (0 <= b < 131072)%Z ->
      parse_flags (sfx (p + k)) (Z.lor fl b) = (FL, s1) -> s1 <> [] ->
      (forall (k' c' : Z) (a3 a4 a5 : word),
         (p + k <= k' < zlength fmt)%Z -> s1 = sfx k' -> c' = znth fmt k' -> flag_bit c' = None -> (0 <= FL < 131072)%Z ->
         evtF bsegs RNG Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 c') (Z_to_bv 64 (A + k')) a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 32)
                    x18 x19 x20 x21 x22 x23 (Z_to_bv 64 FL) x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0xa8028) fc None m (seg_rom bsegs))) ->
      evtF bsegs RNG Q
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 w3 (Z_to_bv 64 (A + p + k)) x15 (Z_to_bv 64 1) (Z_to_bv 64 32)
                 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8004) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_WLOOP : Prop :=
    forall (x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (pos acc w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
      is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (w, s2) -> s2 <> [] ->
      (forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
         (pos < k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
         evtF bsegs RNG Q
           (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
                    x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0xa8158) fc None m (seg_rom bsegs))) ->
      evtF bsegs RNG Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) x12 (Z_to_bv 64 (A + pos)) x14 x15 x16 x17
                 x18 x19 x20 x21 (Z_to_bv 64 acc) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa80bc) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_WIDTH : Prop :=
    forall (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k1 w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= k1 < zlength fmt)%Z ->
      getint (sfx k1) 0 = Some (w, s2) -> s2 <> [] ->
      (forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
         (k1 <= k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
         evtF bsegs RNG Q
           (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
                    x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0xa8158) fc None m (seg_rom bsegs))) ->
      evtF bsegs RNG Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8070) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_PLOOP : Prop :=
    forall (x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (pos acc p : Z) (s3 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
      is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (p, s3) -> s3 <> [] ->
      (forall (k3 : Z) (a1 a3 a4 : word),
         (pos < k3 < zlength fmt)%Z -> s3 = sfx k3 -> is_digit (znth fmt k3) = false -> (0 <= p <= INT_MAX)%Z ->
         evtF bsegs RNG Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0xa8290) fc None m (seg_rom bsegs))) ->
      evtF bsegs RNG Q
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) (Z_to_bv 64 (A + pos)) x13 x14 x15 (Z_to_bv 64 10) (Z_to_bv 64 8)
                 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 acc) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa821c) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_PREC : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k2 k3 p : Z) (xp : bool) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= k2 < zlength fmt)%Z ->
      ( (znth fmt k2 <> 46 /\ p = -1 /\ xp = false /\ k3 = k2)
        \/ (znth fmt k2 = 46 /\ xp = true /\ k2 + 1 < zlength fmt /\ znth fmt (k2 + 1) <> 42
            /\ getint (sfx (k2 + 1)) 0 = Some (p, sfx k3) /\ k2 + 1 <= k3 < zlength fmt) )%Z ->
      (forall (a1 a3 a4 : word),
         (-1 <= p <= INT_MAX)%Z ->
         evtF bsegs RNG Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0xa8290) fc None m (seg_rom bsegs))) ->
      evtF bsegs RNG Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 (Z_to_bv 64 (A + k2)) x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8158) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_STATE : Prop :=
    forall (x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k3 ty : Z),
      let _ := ctx_all in
      finv m -> (0 <= k3 < zlength fmt)%Z -> conv_type (znth fmt k3) = Some ty ->
      (forall (a2 a3 : word),
         evtF bsegs RNG Q
           (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 ty) a2 a3 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 (Z_to_bv 64 (A + k3 + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 0) x28 x29 x30 x31)
               Ft (Z_to_bv 64 0xa8310) fc None m (seg_rom bsegs))) ->
      evtF bsegs RNG Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (A + k3)) x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8290) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_DIR : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (i : Z) (d : dir) (rest : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= i)%Z -> (i + 1 <= zlength fmt)%Z ->
      parse_dir (sfx (i + 1)) = Some (d, rest) ->
      (forall (k4 : Z) (a2 a3 a4 t1 : word),
         (i + 1 < k4 <= zlength fmt)%Z -> rest = sfx k4 -> znth fmt (k4 - 1) = d_t d ->
         (0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
         evtF bsegs RNG Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                    (Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) a2 a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 (Z_to_bv 64 (A + k4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
               Ft (Z_to_bv 64 0xa8310) fc None m (seg_rom bsegs))) ->
      evtF bsegs RNG Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa7f94) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition S_END : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 apv] ->
      frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
      evtF bsegs RNG (POST r st)
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) FPv x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8acc) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_HEAD (fuel : nat) : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i cnt l k : Z) (args : list parg)
           (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i)%Z -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l <= INT_MAX)%Z ->
      implAM RNG (printf_loop OUT OUTFP fuel (sfx i) args (cnt + l)) st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 cnt) FPv (Z_to_bv 64 (A + i)) x22 x23 x24 x25 (Z_to_bv 64 l) x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa7ef8) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_CONV : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (d : dir) (a : parg) (args : list parg)
           (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) (a :: args) ->
      match a with PA_g dd =>
        fpcall_stmt Fp B BS RB SINK TOPOK OUTFP
          (f128_of_d dd, d_w d, d_p d, (if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD))%Z, d_t d)
      | _ => True end ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (1 <= i4 <= zlength fmt)%Z -> znth fmt (i4 - 1) = d_t d -> conv_type (d_t d) = Some (d_ty d) ->
      (0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
      ((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z ->
      (0 <= c <= INT_MAX)%Z ->
      implAM RNG (cnt' <- conv OUT OUTFP c d a ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) x12 x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8310) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition body_loc (BA n : Z) : Prop :=
    ((q + -392 <= BA /\ BA + n <= q + -368)
     \/ ((BA + n <= lo \/ q <= BA) /\ (BA + n <= Fp \/ Fp + 232 <= BA) /\ (BA + n <= B \/ B + BS <= BA)
         /\ BA + n <= 2^47))%Z.                                    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition S_TAIL : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (prefix body : list Z) (BA PFXA : Z)
           (s2s za plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at bsegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> body_loc BA (zlength body) -> (BA + zlength body < 2^64)%Z -> (zlength body <= INT_MAX)%Z ->
      (* [comment removed for export] *)
      (exists rb, rclean m0 rb /\ inreg rb BA (zlength body) /\ rrng RNG rb) -> rng RNG BA (zlength body) ->
      (forall m', mem_inv bsegs m' -> bytes_at bsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 724992)%Z -> (zlength prefix <= 2)%Z -> (68436 <= PFXA)%Z -> (PFXA + zlength prefix <= 68445)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      implAM RNG (cnt' <- conv_tail OUT c fl w p prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 (Z_to_bv 64 (BA + zlength body)) x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8794) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition tregs (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 t3 t4 t5 t6 : word) (i4 c w BA wq pq : Z) : bvmap 5 word :=
    mkR xra SPv gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 a4 a5 a6 a7
        s2 (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) s8 s9 (Z_to_bv 64 wq) (Z_to_bv 64 pq) t3 t4 t5 t6.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Definition tinv (m : word -> option byte) (st : St) (k i4 : Z) (args : list parg) (fuel : nat)
      (PFXA fl n pl pq BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte) : Prop :=
    finv m
    /\ rw_cells bsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) (Z_to_bv 64 (Z.land fl 73728)) (Z_to_bv 64 n) (Z_to_bv 64 pl) (Z_to_bv 64 (pl + pq)) (Z_to_bv 64 0) alo ahi j128)
    /\ rw_cells bsegs m (q + -392) [CB 24 digs]
    /\ rw_cells bsegs m (q + -368) [CB 256 pad]
    /\ SINK m st /\ rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] /\ (0 <= k)%Z
    /\ args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args
    /\ Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args)
    /\ bytes_at bsegs m BA (zb body) /\ Forall (fun c => 0 <= c < 256)%Z body /\ body_loc BA n /\ (BA + n < 2^64)%Z /\ n = zlength body
    /\ (exists rb, rclean m0 rb /\ inreg rb BA n /\ rrng RNG rb) /\ rng RNG BA n
    /\ (forall m', mem_inv bsegs m' -> bytes_at bsegs m' PFXA (zb prefix)) /\ Forall (fun c => 0 <= c < 256)%Z prefix
    /\ (0 <= PFXA)%Z /\ (PFXA + pl <= 724992)%Z /\ pl = zlength prefix /\ (pl <= 2)%Z /\ (68436 <= PFXA)%Z /\ (PFXA + pl <= 68445)%Z
    /\ (0 <= i4 <= zlength fmt)%Z /\ (0 <= fl < 131072)%Z /\ (0 <= n <= INT_MAX)%Z /\ (n <= pq)%Z /\ (pl + pq <= INT_MAX)%Z.

  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    let rb := fresh "rb" in let RCb := fresh "RCb" in let IRb := fresh "IRb" in let RRb := fresh "RRb" in let RGb := fresh "RGb" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & (rb & RCb & IRb & RRb) & RGb & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & PFlo & PFhi & Hi4 & Hfl & HnI & Hnp & Hplp);
    pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
    pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
    let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
  (* [comment removed for export] *)
  Ltac mk_tinv :=
    lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      unfold tinv, body_loc;
      split; [mk_finv|];
      split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
      split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
      split; [match goal with H : SINK m _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
      split; [lia|];
      split; [assumption|];
      split; [assumption|];
      split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
      split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [first [assumption | reflexivity | lia | zl] |];
      split; [match goal with H : rclean m0 ?r, H2 : inreg ?r _ _, H3 : rrng _ ?r |- _ => exists r; split; [exact H| split; [exact H2| exact H3]] end |];
      split; [assumption|];
      repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
    end.

  (* [comment removed for export] *)
  Definition S_T6 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implAM RNG (mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0xa89b0) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_T5 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implAM RNG (OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0xa8994) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_T4 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implAM RNG (mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0xa8910) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_T3 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implAM RNG (mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0xa8888) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_T2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implAM RNG (OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0xa886c) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_T1 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      Z.land fl 73728 = 0%Z ->
      implAM RNG (mpad OUT 32 wq (pl + pq) fl ;;; OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0xa87ec) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_INTC2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p argi : Z) (prefix body : list Z) (BA PFXA : Z)
           (s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at bsegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
      (forall m', mem_inv bsegs m' -> bytes_at bsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 724992)%Z -> (zlength prefix <= 2)%Z -> (68436 <= PFXA)%Z -> (PFXA + zlength prefix <= 68445)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      (0 <= argi < 2^64)%Z ->
      implAM RNG (cnt' <- (if ((argi =? 0) && (p =? 0))%Z then conv_tail OUT c fl w p prefix []
                            else conv_tail OUT c fl w (Z.max p (zlength body + (if (argi =? 0)%Z then 1 else 0))) prefix body) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa875c) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_INTC : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) (BA PFXA : Z)
           (s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at bsegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
      (forall m', mem_inv bsegs m' -> bytes_at bsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 724992)%Z -> (zlength prefix <= 2)%Z -> (68436 <= PFXA)%Z -> (PFXA + zlength prefix <= 68445)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= argi < 2^64)%Z ->
      implAM RNG (cnt' <- conv_int OUT c fl w p xp argi prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8744) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition dloop_post (x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Ft : bvmap 5 word) (fc : bv 32) (x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (a2 a3 : word) (xq : Z) (W : list Z) (m' : word -> option byte),
      ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xq) (Z_to_bv 64 (q + -392 + (j - zlength W))) a2 a3
                    (Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
                    x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength W))) x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0xa872c) fc None m' (seg_rom bsegs)
      /\ munch [(q + -392, q + -368)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength W)) ds ++ zb W ++ skipn (Z.to_nat j) ds)]
      /\ (1 <= xq <= 9)%Z /\ dec_digits x = (48 + xq)%Z :: W /\ (zlength W + 1 <= j)%Z.
  Definition S_DLOOP : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x j : Z) (ds : list byte),
      let _ := ctx_all in
      mem_inv bsegs m -> rw_cells bsegs m (q + -392) [CB 24 ds] ->
      (10 <= x < 2^64)%Z -> (zlength (dec_digits x) <= j <= 24)%Z -> x11 = Z_to_bv 64 (q + -392 + j) ->
      evtF bsegs RNG (dloop_post x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc x j ds m)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) x11 x12 x13
                 (Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa86f4) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_FMTU2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (x d jj : Z) (W prefix : list Z) (PFXA : Z)
           (pfx s2s za plp ahi : word) (j128 pre pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 (pre ++ zb W)] -> zlength pre = jj -> (1 <= jj)%Z ->
      ((d = 0 /\ W = [] /\ dec_digits x = []) \/ (1 <= d <= 9 /\ dec_digits x = (48 + d) :: W))%Z ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (forall m', mem_inv bsegs m' -> bytes_at bsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 724992)%Z -> (zlength prefix <= 2)%Z -> (68436 <= PFXA)%Z -> (PFXA + zlength prefix <= 68445)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= x < 2^64)%Z ->
      implAM RNG (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 d) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 PFXA)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 (q + -392 + jj)) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa872c) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_FMTU : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (x : Z) (prefix : list Z) (PFXA : Z)
           (pfx s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (forall m', mem_inv bsegs m' -> bytes_at bsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 724992)%Z -> (zlength prefix <= 2)%Z -> (68436 <= PFXA)%Z -> (PFXA + zlength prefix <= 68445)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= x < 2^64)%Z ->
      implAM RNG (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 x) x11 x12 x13 (Z_to_bv 64 10) x15 x16 (Z_to_bv 64 PFXA)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa86e4) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition S_CV_D : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (i : Z)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (i mod 2^64)) ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (-2^31 <= i < 2^31)%Z ->
      implAM RNG (cnt' <- (let '(argi, prefix) :=
                               (if INTMAX_MAX <? i mod 2^64 then ((- (i mod 2^64)) mod 2^64, [45])
                                else if negb (Z.land fl MARK_POS =? 0) then (i mod 2^64, [43])
                                else if negb (Z.land fl PAD_POS =? 0) then (i mod 2^64, [32])
                                else (i mod 2^64, []))%Z in
                            conv_int OUT c fl w p xp argi prefix (dec_digits argi)) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa83e0) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_CV_U : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (u : Z)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= u < 2^32)%Z ->
      implAM RNG (cnt' <- conv_int OUT c fl w p xp u [] (dec_digits u) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8518) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition xloop_post (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Ft : bvmap 5 word) (fc : bv 32) (l x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (a2 a3 : word) (m' : word -> option byte),
      let H := hex_digits l x in
      ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 l) a2 a3 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength H))) x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0xa85d0) fc None m' (seg_rom bsegs)
      /\ munch [(q + -392, q + -368)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength H)) ds ++ zb H ++ skipn (Z.to_nat j) ds)]
      /\ (zlength H <= j)%Z.
  Definition S_XLOOP : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l x j : Z) (ds : list byte),
      let _ := ctx_all in
      mem_inv bsegs m -> rw_cells bsegs m (q + -392) [CB 24 ds] ->
      (0 < x < 2^64)%Z -> (l = 0 \/ l = 32)%Z -> (zlength (hex_digits l x) <= j <= 24)%Z -> x23 = Z_to_bv 64 (q + -392 + j) ->
      evtF bsegs RNG (xloop_post x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc l x j ds m)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) (Z_to_bv 64 l) x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa85a8) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_CV_X : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (u t : Z)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= u < 2^32)%Z -> (t = 120 \/ t = 88)%Z ->
      implAM RNG (cnt' <- conv_int OUT c fl w p xp u
                              (if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0) then (if t =? 120 then [48; 120] else [48; 88]) else [])%Z
                              (hex_digits (Z.land t 32) u) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8590) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_CV_S : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p fl10 : Z) (xp : bool) (P : Z) (s : list Z) (slack : list byte)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 P) ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      bytes_at bsegs m P (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256)%Z s ->
      ((- (P + zlength s + 1)) mod 8 <= zlength slack)%Z -> (0 < P)%Z ->
      (P + zlength s + 1 + zlength slack <= lo \/ q <= P)%Z ->
      (P + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= P)%Z ->
      (P + zlength s + 1 + zlength slack <= B \/ B + BS <= P)%Z ->
      (P + zlength s + 1 <= 2^47)%Z ->                              (* [comment removed for export] *)
      rng RNG P (zlength s + 1 + zlength slack) ->
      (exists r, rclean m0 r /\ inreg r P (zlength s + 1 + zlength slack) /\ rrng RNG r) ->
      (fl10 = Z.land fl (Z.lnot 65536))%Z ->
      implAM RNG (cnt' <- (if (p <? 0) && (INT_MAX <=? zlength s) then munr
                            else conv_tail OUT c (Z.land fl (Z.lnot ZERO_PAD)) w (if p <? 0 then zlength s else Z.min (zlength s) p) []
                                           (firstn (Z.to_nat (if p <? 0 then zlength s else Z.min (zlength s) p)) s))%Z ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 fl10) x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8428) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_CV_FP : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (y t : Z)
           (pfx s2s za pl plp : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      fpcall_stmt Fp B BS RB SINK TOPOK OUTFP (y, w, p, fl, t) ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= y < 2^128)%Z -> conv_type t = Some T_DBL ->
      implAM RNG (cnt' <- (if xp && (p <? 0) then munr
                            else if (1 <? w) || (2^20 <=? p) then munr
                            else r <- OUTFP y w p fl t ;; if (r <? 0) || (INT_MAX - c <? r) then munr else mret (c + r))%Z ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0xa8390) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition POST1 : Z -> machine_state -> Prop :=
    fun r ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               F (ret_pc ra) fc0 None m' (seg_rom bsegs)
      /\ munch [(lo, q)] m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo q
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition S_EXIT1 : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m -> munch [(lo, q)] m0 m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      (0 <= r < 2^64)%Z ->
      evtF bsegs RNG (POST1 r)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0xa8c24) fc0 None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_P1 : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m -> munch [(lo, q)] m0 m ->
      rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells bsegs m (q + -392) [CB 24 digs] ->
      rw_cells bsegs m (q + -368) [CB 256 pad] ->
      pass1_ok fmt = true ->
      evtF bsegs RNG (POST1 0)
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 A) x22 x23 x24 x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0xa7ef8) fc0 None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition S_PRO : Prop :=
    forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (f : Z) (Q : machine_state -> Prop),
      let _ := ctx_all in
      stk bsegs m0 lo q -> mem_inv bsegs m0 -> bytes_at bsegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      (0 <= f < 2^64)%Z ->
      (forall (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte) (a0 a1 a2 a3 : word),
         finv m -> munch [(q + -544, q)]%Z m0 m ->
         rw_cells bsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
         rw_cells bsegs m (q + -392) [CB 24 digs] ->
         rw_cells bsegs m (q + -368) [CB 256 pad] ->
         evtF bsegs RNG Q
           (MS (mkR ra SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 nlt x15 x16 x17
                    s2e (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 A) s6e s7e s8e s9e (Z_to_bv 64 0) s11e x28 x29 x30 x31)
               F (Z_to_bv 64 0xa7ef8) fc0 None m (seg_rom bsegs))) ->
      evtF bsegs RNG Q
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 f) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0xa7e48) fc0 None m0 (seg_rom bsegs)).

End PrintfCore.
End CANSEC3.
