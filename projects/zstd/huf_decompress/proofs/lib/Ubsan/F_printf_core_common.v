(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (86 recorded proofs replaced by written proofs (zb_length, zb_app, nth_error_zb and 83 more)). *)
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
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import F_memset F_memcpy F_memchr F_strnlen Stdio_kit F_syscalls StdioFiles.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import Printf_zfacts F_printf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_printf_core_common () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib3Lib3Arr@upd_firstn_skipnC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List:firstn_mapI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00C46Stdlib5Lists4List7map_appC47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes:option_mapK47Corelib4Init5Logic2eq01C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List=nth_error_mapC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notC46Stdlib5Lists4List=nth_error_nthI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_NoneC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec6Prelim4znthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leI47Corelib4Init9Datatypes4bool00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C46Stdlib5Lists4List6nth_okK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesc59OSSVerify5KrLib5UbsanDF_printf_core_common>znth_nth_errorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common<nth_error_zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr9u8ro_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List6nth_InC47Corelib4Init5Logic5proj1C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4xorbC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9lxor_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z02C47Corelib4Init3Nat3addC59OSSVerify5KrLib3Lib3Arr?nth_error_splitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib5Lists7ListDef5skipnC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib4Init3Nat3subC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appC46Stdlib5Lists4List9app_assocC35stdpp7tactics<f_equal_helpC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_1_rC56Stdlib6ZArith4Znat5Z2Nat7inj_addc59OSSVerify5KrLib5UbsanDF_printf_core_common3sfxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib5Lists4List;skipn_skipnC47Corelib4Init5Logic8iff_reflC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith6BinInt1Z;lt_ge_casesc59OSSVerify5KrLib5UbsanDF_printf_core_common8sfx_consC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos6to_natC47Corelib4Init5Logic7f_equalC57Corelib7BinNums6PosDef3Pos7compareC47Corelib4Init9Datatypes7CompOppK47Corelib4Init5Logic3and01c59OSSVerify5KrLib5UbsanDF_printf_core_common7sfx_nilC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib6Common<Printf_model7lit_runC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes3orbC47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z8eqb_specK46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib5UbsanDF_printf_core_common>lit_run_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common9sfx_skipnC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat9ltb_spec0C46Stdlib5Lists4List?nth_error_skipnC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib5Lists4List@nth_error_firstnc59OSSVerify5KrLib5UbsanDF_printf_core_common>lit_run_firstnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common:lit_run_inC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z3oppC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z>div_unique_posC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7div_divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z3lorC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model:digits_auxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common<digits_aux_SC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z7pow_0_rC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z9div_smallC59OSSVerify5KrLib6Common<Printf_model:dec_digitsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lt_transc59OSSVerify5KrLib5UbsanDF_printf_core_common?digits_aux_fuelC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8f_equal2c59OSSVerify5KrLib5UbsanDF_printf_core_common>digits_aux_accC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_commonAdigits_aux_lengthC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=length_firstnC47Corelib4Init3Nat3minC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List=firstn_firstnC46Stdlib5Lists4List:firstn_appC56Stdlib6ZArith4Znat5Nat2Z7inj_minC59OSSVerify5KrLib6Common<Printf_model:hex_digitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model7XDIGITSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC59OSSVerify5KrLib5Ubsan=Printf_zfacts>Zrange_forallbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common;hexchar_ok0C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib5UbsanDF_printf_core_common<hexchar_ok32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common=hexchar_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6wrap64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat:wrap64_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat4lo64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat4hi64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib3Lib5Bytes;lor_lt_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5mk128C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec>Z_shiftr_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat8is_neg64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5sra63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5shl64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat<wrap64_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common=shr64_range64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec;Z_lor_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib6Common9SoftFloat5add64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat<clz64_mirrorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5sub64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6sext32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common;mk128_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegC59OSSVerify5KrLib3Lib8PropExec<Z_lxor_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common;sra63_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Bytes<land_lt_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat9f128_of_dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6INF_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat;IMPLICIT_HIC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC59OSSVerify5KrLib6Common;SFW1_lemmas:swrap32_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge=Z_to_bv_mod64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4zx32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_diagC56Stdlib6ZArith6BinInt1Z:land_assocC59OSSVerify5KrLib6Common<F_fmt_fp_libCbytes_le_to_Z_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib6Common<F_fmt_fp_libBZ_to_le_bytes_to_ZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common<le8_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;printf_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib6Common<Printf_model9parse_dirC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4convC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model3dir00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8fp_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_flC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lnotC59OSSVerify5KrLib6Common<Printf_model3d_wC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib6Common<Printf_model3d_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8LEFT_ADJC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8ZERO_PADC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5UbsanDF_printf_core_common;In_firstn_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common:In_skipn_wC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List9skipn_mapC46Stdlib5Lists4List<firstn_skipnC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat5min_lI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5Ubsan=Printf_zfacts?parse_dir_shapeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8is_digitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;parse_flagsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_xpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model9conv_typeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_tyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model6getintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Printf_zfactsAgetint_some_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9Stdio_kitBrw_cells_bytes_at'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@bytes_at_ov_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib5Ubsan9F_pop_arg;firstn4_le8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8firstn_0C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getc59OSSVerify5KrLib5UbsanDF_printf_core_common3FokC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common4POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4mpadC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib5UbsanDF_printf_core_common;Forall_znthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image@ro_bytes_b_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;ro_bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Printf_zfacts7STATES0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Printf_zfacts?conv_type_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common=states0_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common;zbytes_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Printf_zfacts<states0_convC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common6PFXSTRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common9pfx_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common<bytes_at_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common8zb_skipnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common9zb_firstnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common=xdigits_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common3JT1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common9jt1_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idc59OSSVerify5KrLib5UbsanDF_printf_core_common9zb_lengthC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01c59OSSVerify5KrLib5UbsanDF_printf_core_common<jt1_read_litC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib6Common<Printf_model5T_DBLC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib6Common<Printf_model5T_PTRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model5T_INTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model6T_UINTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;SFW1_lemmas<zb_land_pow2C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool3eqbc59OSSVerify5KrLib5UbsanDF_printf_core_common<nzmask_bits'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1Z9lnot_specC56Stdlib6ZArith8Zbitwise1Z?sub_land_same_lC56Stdlib6ZArith6BinInt1Z7lxor_eqC56Stdlib6ZArith6BinInt1Z>lxor_nilpotentc59OSSVerify5KrLib5UbsanDF_printf_core_common?land_lxor_distrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface?sink_frame_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface6arg_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K59OSSVerify5KrLib6Common<Printf_model4parg02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface7args_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common8arg_ok_WC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common8lo_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common:lo_cells14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5Ubsan9F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9F_pop_arg=va_area_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_SomeC59OSSVerify5KrLib5Ubsan9F_pop_arg<pop_arg_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9F_pop_arg<pop_arg_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common4FokdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9F_pop_arg:pop_arg_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9F_pop_arg:pop_arg_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun9memchr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9F_strnlen<strnlen_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9F_strnlen<strnlen_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun;strnlen_resC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffc59OSSVerify5KrLib5UbsanDF_printf_core_common6u8_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC59OSSVerify5KrLib5Ubsan>F_printf_iface8out_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common9out_postqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface8out_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface9OUT_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles;GLOBALS_TOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface;fpcall_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface;fpcall_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5UbsanDF_printf_core_common8fp_postqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9Stdio_kit<FMT_FP_DEPTHC1?~~~~~~~~~~~~~~~".
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
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ]
  end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
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
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Definition hide (P : Prop) := P.
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
  lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

(* [comment removed for export] *)
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM usegs c s Q ms) | _ => idtac end.

(* [comment removed for export] *)
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
  bytes_at usegs m A (zb l) -> (0 <= i < zlength l)%Z -> a = wa (A + i) ->
  ov_read_bytes usegs m a 1 = Some [Z_to_bv 8 (znth l i)].
Proof.
  intros m A l i a HB Hi ->.
  eapply (u8ro_read usegs m A (zb l) i); [exact HB | | lia | reflexivity].
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
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) [] "h01ah11bp;2g00@Gj20Tg00;fR0f0,00X10W0o"). Qed.
Lemma if_true_Z : forall a b : Z, (if true then a else b) = a.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) [] "h01ah11bp;2g00@Gj20Tg00;fR0f1,00X10W0o"). Qed.

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

Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells usegs m A [CB n bs] -> length bs = n.
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
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) [] "h01Xh11ah21bp;2g00@Gj20Tp200f0f1R0f2/00W2W1W0o"). Qed.
Lemma iff : forall (X : Type) (a b : X), (if false then a else b) = b.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) [] "h01Xh11ah21bp;2g00@Gj20Tp200f0R0f1f2/00W2W1W0o"). Qed.

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
    assert (RaRep : 0 <= aRep < 2^64) by (subst aRep; unfold lo64; apply wrap64_range).
    assert (RaSig : 0 <= aSig < 2^64) by (subst aSig; apply shr64_range64; [apply wrap64_range | lia]).
    assert (RsignHi : 0 <= signHi < 2^64) by (subst signHi; apply wrap64_range).
    assert (RINF : 0 <= INF_HI < 2^64) by (unfold INF_HI; lia).
    assert (RIMP : 0 <= IMPLICIT_HI < 2^64) by (unfold IMPLICIT_HI; lia).
    assert (G : forall e s, 0 <= e < 2^64 -> 0 <= s < 2^64 -> 0 <= Z.lor (Z.lor e s) signHi < 2^64).
    { intros e s He Hs. apply PropExec.Z_lor_range; [apply PropExec.Z_lor_range|]; lia. }
    cbv zeta.
    destruct (negb (aExp =? 0)).
    - destruct (negb (aExp =? 2047)); apply mk128_range; try apply wrap64_range;
        apply G; try apply wrap64_range; try (apply shr64_range64; lia). exact RINF.
    - destruct (aSig =? 0).
      + apply mk128_range; [|lia]. apply G; [apply wrap64_range | lia].
      + apply mk128_range.
        * apply G; [apply wrap64_range|]. apply PropExec.Z_lxor_range; [|exact RIMP].
          destruct (negb (is_neg64 _)); [apply wrap64_range|]. apply shr64_range64; [|apply Z.land_nonneg; lia].
          apply shr64_range64; lia.
        * apply Bytes.land_lt_pow2; [apply sra63_range|].
          pose proof (wrap64_range (Z.shiftl aSig (Z.land (add64 (clz64_mirror aSig) 49) 63))). unfold shl64. lia.
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
Lemma cb8_c8_in : forall m A pre post bs, rw_cells usegs m A (pre ++ CB 8 bs :: post) -> rw_cells usegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let rec go pre l := lazymatch l with
     | CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
     | ?c :: ?l' => go constr:(pre ++ [c]) l'
     | [] => idtac end in
  go constr:(@nil cell) cs end.

(* [comment removed for export] *)
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
  bytes_at usegs m A l -> (k <= length l)%nat ->
  bytes_at usegs m (A + Z.of_nat k) (firstn n (skipn k l)).
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
  rw_cells usegs m A (pre ++ C8 w :: post) -> a = wa (A + Z.of_nat (cells_size pre)) ->
  ov_read_bytes usegs m a 4 = Some (le4 w).
Proof.
  intros m A pre w post a H ->.
  apply (proj1 (rw_cells_app usegs m A pre (C8 w :: post))) in H. destruct H as [_ H].
  pose proof (rw_cells_bytes_at' _ _ _ _ H) as Hb. cbn [cells_bytes cbytes] in Hb.
  pose proof (bytes_at_ov_read usegs m _ _ 0 4 Hb) as R. rewrite Z.add_0_r in R.
  rewrite R. 2:{ cbn [skipn]. rewrite length_app, length_le8. lia. }
  change (skipn 0 (le8 w ++ cells_bytes post)) with (le8 w ++ cells_bytes post).
  rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r, firstn4_le8. reflexivity.
Qed.

Lemma bytes_at_nil : forall m a, (0 <= a)%Z -> (a <= 2^64)%Z -> bytes_at usegs m a [].
Proof. intros m a H0 H1. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
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
  Hypothesis HA : (A + zlength fmt <= 172032)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((173360 <= Fp /\ Fp + 232 <= 375568) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((375576 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Notation sfx := (sfx fmt).
  Definition ctx_all : unit :=
    let _ := (ra, q, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc0, m0,
              lo, canary, A, fmt, AP, VA, slots, nla, nlt) in tt.

  (* [comment removed for export] *)
  Definition W : list (Z * Z) := [(lo, q); (AP, AP + 8); (Fp, Fp + 232); (B, B + BS)]%Z.
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).

  Definition Fokd (F1 F2 : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k.
  Definition Fok (Ft : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k.
  Lemma Fok_refl : Fok F.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h02_Hh11kp;1p;2p;3g007ej10Tg00U>j1:Tg008Jj11Tg008hj12Tg026gj29Tg013Gj18Tg00;Lj37Tg00Lfj14Tg03n1j25Tg00@Gj26Tg03n[j13Tg00<D#0R0#:R1#1R2#2g00;ff0,92%01#837#4%00#0#0#0#0#1#2p,1FR0f1'5'6W0W1%30eo"). Qed.
  Lemma Fok_trans : forall F1 F2, Fok F1 -> (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
  Proof. intros F1 F2 H1 H2 k Hk. rewrite (H2 k Hk). apply H1. exact Hk. Qed.

  Definition POST : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch W m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
      /\ frm0 fc' /\ Fok Ft
      /\ stk usegs m' lo q
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ rw_cells usegs m' AP [C8 apv]
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
    mem_inv usegs m /\ munch W m0 m /\ wmono usegs m0 m
    /\ rw_cells usegs m (q + -112) hi_cells
    /\ stk usegs m lo (q + -544)
    /\ bytes_at usegs m A (zb fmt)
    /\ va_area m VA slots
    /\ rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].
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
  Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).

  Lemma u8_lit : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
  Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
  Lemma fmt_rng : forall i, (0 <= i < zlength fmt)%Z -> (0 <= znth fmt i < 256)%Z.
  Proof. intros i Hi. exact (Forall_znth _ fmt i HF Hi). Qed.
  (* [comment removed for export] *)
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).

  (* [comment removed for export] *)
  Ltac rd_fmt idx :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.

  (* [comment removed for export] *)
  Lemma states0_bytes : forall m, mem_inv usegs m -> bytes_at usegs m 0x10838 (zb STATES0).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h07__arithh14__ffh28__varmaph35__with42MIh51mp;1p;2p;4p;3p;8p;7p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej10Tg008Jj16Tg008hj17Tg00>Aj1QTg044]j2OTg00U>j11Tg013Gj13Tg00:1j1ATg00Emj1@Tg007Ej1?Tg01Bkj1=Tg00Fkj1<Tg00GIj1PTg00HWj24Tg00I:j4;Tg00JGj2NTg00@Gj2KTg00Jij2ETg00;Lj39Tg00KUj3DTg00L4j4CTg00A_j25Tg01CIj3BTg01eoj3FTg00dZj28Tg01e2j2GTg00:lj2HTg00N^j1ITg045Qj3JTg046Jj4>Tg047Ij8LTg00WXj7MTf0R0#0#0p=2f1R1g00[Pg00[oR2P2g00\OR2P0g00\oFMp=:g00<DR3#0R4#2R5#0#2R6#6R7#7%65#7R5#Q[g00j;R8/O0P8P1%23#2#1#0#2#2#1#1#1#0#2#3R9g048A#AR:P0g00_>R;#@R<%?;R;g00;fR=#=R>%<=R?%P=R@P=g00[2RA,4=g00`QRB14=9RCC;':1N@2R2P0f2RDg00^^REg00a8RF'KRG1E0D=9EFdAD=A1CCR1b1b2b315A9P0b0P<P;P>P?P=%13#1#0#1#0#3R3,4=9B=CPB%34R4,4==F=7C;,:@P2P1b1b2b31893%36,G4R4'5P0b01H5:#I,89/54eP8P:P9PGAJ89:=9EFdC>GLW4W5o"). Qed.
  (* [comment removed for export] *)
  Lemma states0_read : forall m t ty, mem_inv usegs m -> conv_type t = Some ty ->
    ov_read_bytes usegs m (wa (t + 67640 + -65)) 1 = Some [Z_to_bv 8 ty].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h04__x1h17__arithh24__ffh38__varmaph45__with52tyh62CTh72MIh81Rh91mh:1tp;1p;2p;3p;4p;8p;6p;7p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej11Tg008Jj1?Tg008hj1ETg00>Aj1;Tg044]j2XTg03bMj1UTg00?Aj2BTg00;Lj37Tg049Aj3LTg00U>j10Tg013Gj18Tg00A_j25Tg00COj2>Tg01?fj2=Tg00VGj2YTg007Ej1FTg00dZj22Tg01ACj1VTg00e7R0j1DTg00Qcj1TTg00efj4STg009Kj2QTg00Emj1ATg00T@j3PTg04:Ij2OTg00FMj2NTg00Fkj1MTg00GIj1KTg00HWj24Tg00H4j2JTg00Iej1ITg01Clj3HTg00I:j4:Tg00YDj8GTg00JGj2RTg00@Gj2CTg00Jij2bTg00KUj3aTg00L4j4`Tg00C3j2_Tg01CIj3<Tg01FIj8^Tg04;Vj8ZTg04<aj3[Tg002Tj6\Tg00WXj7WTg00X`j7]Tf0R1#1#1p=3g00;fR2f1R3g00`QP1C:p=9P3g00[PR4g00[oR5P5g00\OR6P1g00\oFWp=6f2R7P4P5P5P6P3P1F]p=@g00<DR8#1#3R9#3R:#1#?#ER;%?9R9#ER<#;[g00j;R=/X7%;2%U71B2337f3R>?L71%0:R:#8R?/5>%08#0R@#0#1#0#1#8RA,5>'>P2g048ARBf4RC/=?RD'Y%F<RE#;P=f6f5R=%38#3#0#1#3#3#0#0#0#1#3#8RF'2%V:R:'2#Dg00b3#TCS1Q91%A<5P<,BE37X52P=PFPBPD12CF/2:RB#D1O=7g00_>RE#AR<%FERE1N23R9%M2RG%K2RHP4P5P5P6142?R41J28R8'9,6H142A,98,6H5@H%I5g00[2R5,42AH284R4'9,6HP2P4g00_j%1@#0#1#8R@,42C:,6H5@HGG1RH6R6P1P7g00^^RIg00a8RJ'C1b17=7IJdAa253C`RJb2b3b4X0215?1151A'>1=3?RA,551_A@'>[^02P1P=P3O2b1P2P;P0P0PB12FDP;\2/C0P<PEP9PGP2142FRG9<28142:5<2g00c>A<2G4C:,6HP6PJb2b3b4X02121F/2:1=1?,2F572^02P1P=O1b1G^GZP>A[C>3E\b8W6W7X52X:2W9o"). Qed.

  (* [comment removed for export] *)
  Definition PFXSTR : list Z := [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z.
  Lemma pfx_bytes : forall m, mem_inv usegs m -> bytes_at usegs m 66200 (zb PFXSTR).
  Proof.
    clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  Qed.
  Lemma pfx_sub : forall m k n, mem_inv usegs m -> (k + n <= 9)%nat ->
    bytes_at usegs m (66200 + Z.of_nat k) (zb (firstn n (skipn k PFXSTR))).
  Proof.
    clear. intros m k n MI Hk. rewrite zb_firstn, zb_skipn. apply bytes_at_sub; [apply pfx_bytes; exact MI|]. cbn. lia.
  Qed.
  Lemma xdigits_bytes : forall m, mem_inv usegs m -> bytes_at usegs m 68104 (zb XDIGITS).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h07__arithh14__ffh28__varmaph35__with42MIh51mp;1p;2p;4p;3p;8p;7p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej10Tg008Jj16Tg008hj17Tg00>Aj1QTg044]j2OTg00U>j14Tg013Gj12Tg00:1j1ATg00Emj1@Tg007Ej1?Tg01Bkj1=Tg00Fkj1<Tg00GIj1PTg00HWj23Tg00I:j4;Tg00JGj2NTg00@Gj2KTg00Jij2ETg00;Lj39Tg00KUj3DTg00L4j4CTg00A_j25Tg01CIj3BTg01eoj3FTg00dZj28Tg01e2j2GTg00:lj2HTg00N^j1ITg045Qj3JTg046Jj4>Tg047Ij8LTg00WXj7MTf0R0#0#0p=1f1R1g00[Pg00[oR2P2g00\OR2P0g00\oFMp=:g00<DR3#0R4#1R5#0R6#1R7#6R8#7%65#7R5#Q[g00j;R9/O0P9P1%13#1#4#0#4#0#1#1#4#0#1#2R3g02UT#AR:P0g00_>R;#@R<%?;R;g00;fR=#=R>%<=R?%P=R@P=g00[2RA,3=g00`QRB13=3RCC;':1N@2R2P0f2RDg00^^REg00a8RF'KRG1E0D=9EFdAD=A1CCR1b1b2b315A3P0b0P<P;P>P?P=%26R6,3=9B=CPB%24R4,3==F=8C;,:@P2P1b1b2b31836%27,G4R4'5P0b01H5:#I,83/54eP9P:P3PGAJ93:=9EFdC>GLW4W5o"). Qed.
  Lemma xdigits_read : forall m v, mem_inv usegs m -> (0 <= v < 16)%Z ->
    ov_read_bytes usegs m (wa (68104 + v)) 1 = Some [Z_to_bv 8 (znth XDIGITS v)].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h04__x1h12Hvh22MIh37__arithh44__ffh58__varmaph65__with71mh81vp;1p;2p;4p;7p;8p;3p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej10Tg008Jj18Tg008hj1<Tg00>Aj1QTg044]j2LTg00A_j26Tg013Gj17Tg00C3j25Tg00COj2:Tg00U>j12Tg00dZj2>Tg00e7j1=Tg04CRj2PTg00Emj1OTg007Ej1NTg00FMj2KTg00Fkj1HTg00GIj1GTg00HWj29Tg00H4j2ETg00I:j44Tg00X`j7DTg00Iej1CTg00YDj8BTg00JGj2FTg00@Gj23Tg00Jij2ATg00;Lj3ITg00KUj3JTg00L4j4@Tg04;Vj8?Tg00WXj7MTf0R0#0#0p=1f1R1g00[PR2g00[oR3P3g00\OR4P0g00\oFMp=;g00<DR5#0#1R6#0R7#1#8#<R8%86#<#Q[g00;fR6g00j;/L1g00[2R9/61%77R7,51':R:f3R;%15#1#2#0#2#0#1#1#2#0#1#7R<g02UTf2R=1><=#=R<1P;1g00_>R>#O%N>1K61%H6%G6R>P2P3P3P4P>P2P3P3P4P61969g00`Q1E65R5C4,;>P6P5g00_j1967C4,;>FDR5%C3P5GB1F>4P0P=g00^^R>g00a8R4'31A0==I>4dAJ691C@b4b5b6X0616901507':P:[^06P0P;P1O2b3138<G?W1W2W8W7o"). Qed.

  (* [comment removed for export] *)
  Definition JT1 : list Z := [244; 64; 1; 0; 116; 65; 1; 0; 148; 66; 1; 0; 116; 65; 1; 0; 244; 64; 1; 0; 244; 64; 1; 0; 244; 64; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 88; 67; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 244; 66; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 244; 64; 1; 0; 116; 65; 1; 0; 180; 66; 1; 0; 68; 65; 1; 0; 244; 64; 1; 0; 244; 64; 1; 0; 244; 64; 1; 0; 116; 65; 1; 0; 68; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 160; 65; 1; 0; 64; 66; 1; 0; 236; 65; 1; 0; 224; 66; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 140; 65; 1; 0; 116; 65; 1; 0; 124; 66; 1; 0; 116; 65; 1; 0; 116; 65; 1; 0; 244; 66; 1; 0]%Z.
  Lemma jt1_bytes : forall m, mem_inv usegs m -> bytes_at usegs m 67312 (zb JT1).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h07__arithh14__ffh28__varmaph35__with42MIh51mp;1p;2p;4p;3p;8p;7p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej12Tg008Jj16Tg008hj17Tg00>Aj1QTg044]j2OTg00U>j11Tg013Gj13Tg00:1j1ATg00Emj1@Tg007Ej1?Tg01Bkj1=Tg00Fkj1<Tg00GIj1PTg00HWj24Tg00I:j4;Tg00JGj2NTg00@Gj2KTg00Jij2ETg00;Lj39Tg00KUj3DTg00L4j4CTg00A_j25Tg01CIj3BTg01eoj3FTg00dZj28Tg01e2j2GTg00:lj2HTg00N^j1ITg045Qj3JTg046Jj4>Tg047Ij8LTg00WXj7MTf0R0#2#2p=0f1R1g00[Pg00[oR2P2g00\OR2P0g00\oFMp=:g00<DR3#2R4#0R5#2#0R6#6R7#7%65#7R5#Q[g00j;R8/O0P8P1%23#0#0#1#1#2#1#1#1#1#0#0#3R9g04D_#AR:P0g00_>R;#@R<%?;R;g00;fR=#=R>%<=R?%P=R@P=g00[2RA,4=g00`QRB14=9RCC;':1N@2R2P0f2RDg00^^REg00a8RF'KRG1E0D=9EFdAD=A1CCR1b1b2b315A9P0b0P<P;P>P?P=%13#1#2#0#0#3R3,4=9B=CPB%34R4,4==F=7C;,:@P2P1b1b2b31893%36,G4R4'5P0b01H5:#I,89/54eP8P:P9PGAJ89:=9EFdC>GLW4W5o"). Qed.
  Lemma jt1_read_lit : forall m (t : Z) bs, mem_inv usegs m -> (65 <= t <= 120)%Z ->
    firstn 4 (skipn (Z.to_nat (4 * (t - 65))) (zb JT1)) = bs ->
    ov_read_bytes usegs m (wa (67312 + 4 * (t - 65))) 4 = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h04__p1h14__x1h21Rh37__arithh44__ffh54__p2h64__p3h78__varmaph85__with94__x2h:2bsh;1xh<1Hh=2H0h>2Hth?2MIh@1mhA1nhB1thC1zhD2z0p&0p;1p;2p;3p;4p;7p;6p;8p;<p;Bp103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej13Tg008Jj1UTg008hj1OTg00>Aj1]Tg007Ej1YTg044]j2oTg00U>j12Tg013Gj1@Tg00A_R0j24Tg00COj28Tg01?fj26Tg01ijj27Tg00EMR1j1ATg00:1k101Tg016ij3=Tg01[Hj3?Tg00;Lj31Tg00dZR2j2<Tg00e7j1ETg00efj4CTg00?Aj2DTg04Ebj2gTg03iOj7fTg013ej2BTg00:lj2[Tg00MaR3j29Tg00N^R4j1bTg00RBj2TTg00Rkj3STg00STj2aTg01nNj2PTg00Emj1`Tg00T@j3NTg00FMj2QTg00Fkj1_Tg00GIj1^Tg00HWj2>Tg00H4j2MTg00Iek102Tg01Clj3\Tg01o:j3ZTg00JGk200Tg00@Gj2FTg00Jij2|Tg00KUj3{Tg00L4j4yTg04Fkj2xTg002Tj6XTg00O>j2KTg00Pgj2kTg00C3j2VTg00QIj2WTg01Bkj1jTg00T`j4iTg00I:j4LTg00Ucj7hTg01CIj3qTg00lbj4rTg04GIj1sTg0030j6tTg00Qcj10Tg00WXj7wTg00X<j6eTg00X`j7dTg00YDj8zTg00Yhl<cTg01JUlB}Tg00ZMl<~Tf0R5#3#3p=5%05#0p=Rg00;fR6f1R7g00`QP5CLp=IP7g00[PR8g00[oR9P9g00\OR:P5g00\oFwp=;P7P8P9P9P:P5Eep=Hf2R;P8P9P9P:P7P5Fdp=Gf3R<P8P9P9P:P;P7P5Gzp=J%05#0#0#0p=v%05#0#0#0#0#0#0#0p=u%05#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=p%05#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=:P6g00<iR=P6P6P1f4R1P4P<g00]OP;P7P5M<cp=nP=P=P=P6P6P6g01GkP4P4P4P2g01K_f5R2P1P<P;P7P5MB}p=mP=P6P3P4P0g00^<P2P1P<P;P7P5M<~p=lg00<DR0#3R4#3R3#3R>#5R?#3#U#O%U>#OR>#][%Y>R@g00j;RA/o;%2?#@R?/4;%20#2RB#2#3#5#@RC,4;RD'8g00b3RE#RRF#RRG%@3R316<?'7#Ag04D_RH$01RI5=>5?>=1@;P@161?,73#ARJ==>I9?>G%]@RKPAf6RL%30#5#5#2#2#3#2#2#2#2#5#5#@RM162?,73RN'<#EPGCC1D@531X:@PAP2PMPIPJPG1g2;Ff1BJG1[>IRJ'9PAPL%ANRO#bRP,<M#EPGCCA=>OI9?>G,D@51K[P6PP16L?,73RP#ARQ/BGRR/9JPAf81<M7#EPGCCf7RS/6?,73RT#ARU==>I9?>G,D@51K[XC6P5PNp-0RVg00_>RW1T6ERE1T6FRF9S6Eg00bR'aRX'P%`WRY3N%YWRZ1Q67%_6R[%^6R\1>6?R]1M60R0'I,;\1H\<5G\&029R^g00[2R_,>6R`1>63RaA\60]5Z6'I,;\CJ200\:RbP5P;g00^^Rcg00a8Rd'F1|5;=1cddA{6_7CyRdb4b7b8X16W014?5/87167?,73Rc,4_[^16^0VP514LCPLP<O3b3,xNEX1BOG/9JPAPS1<MP#EPGCCA=>QI9?>G,D@51K[P5P=1[6HRK1BUG/95XA=%vG#u#p#:#:#:#:#:#:R=,9R1K_PRU/<3R@%3B#5#5#@RB'4PRP@PQPUP5X;61K_5X;6PPPP1F6PDnPGP31F63EmP=PB1F6BEl1k_P1V_PA16UP'814P_A16U_'8'W1K_TP6AS6FE/PX=NWYPZP61Q6;P7%j6CiP[P\P\P8P9P9P:1H\1P6P0g00c>R11M64R4=\6]9Z6aCL,;\5G\1H\2P6P0P1P`CL,;\5G\FhP^P\1H\L1>6C,I4,;\5G\P^Aq60a1>6B'I,;\CJCJPbPdb4b7b8X16X96X0VX5VX6VA165c,8;A165_,8<'W182D1<;3/4B[[^16^96^0V^5V^6VP5f9RV,4?16V?,73R3/4_1V_3PVP7P;PLO7b3bDb=Cr19RKePJ%sHEtO1b2b2P<P5EXW<W>W?W:XB6W@o"). Qed.
  Lemma jt1_read_s : forall m t, mem_inv usegs m -> t = 115%Z -> ov_read_bytes usegs m (wa (67312 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 140; Z_to_bv 8 65; Z_to_bv 8 1; Z_to_bv 8 0].
Proof.
  intros m t H Ht. subst t. apply jt1_read_lit; [exact H | lia | reflexivity].
Qed.
  Lemma jt1_read_d : forall m t, mem_inv usegs m -> (t = 100 \/ t = 105)%Z -> ov_read_bytes usegs m (wa (67312 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 68; Z_to_bv 8 65; Z_to_bv 8 1; Z_to_bv 8 0].
Proof.
  intros m t H [-> | ->]; (apply jt1_read_lit; [exact H | lia | reflexivity]).
Qed.
  Lemma jt1_read_u : forall m t, mem_inv usegs m -> t = 117%Z -> ov_read_bytes usegs m (wa (67312 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 124; Z_to_bv 8 66; Z_to_bv 8 1; Z_to_bv 8 0].
Proof.
  intros m t H Ht. subst t. apply jt1_read_lit; [exact H | lia | reflexivity].
Qed.
  Lemma jt1_read_x : forall m t, mem_inv usegs m -> (t = 120 \/ t = 88)%Z -> ov_read_bytes usegs m (wa (67312 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 244; Z_to_bv 8 66; Z_to_bv 8 1; Z_to_bv 8 0].
Proof.
  intros m t H [-> | ->]; (apply jt1_read_lit; [exact H | lia | reflexivity]).
Qed.
  Lemma jt1_read_fp : forall m t, mem_inv usegs m -> conv_type t = Some T_DBL -> ov_read_bytes usegs m (wa (67312 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 244; Z_to_bv 8 64; Z_to_bv 8 1; Z_to_bv 8 0].
Proof.
  intros m t H Ht.
  assert (Hc : (t = 101 \/ t = 102 \/ t = 103 \/ t = 69 \/ t = 70 \/ t = 71)%Z).
  { unfold conv_type in Ht.
    destruct (t =? 115)%Z; [exfalso; unfold T_PTR, T_DBL in Ht; congruence|].
    destruct ((t =? 100) || (t =? 105))%Z; [exfalso; unfold T_INT, T_DBL in Ht; congruence|].
    destruct ((t =? 117) || (t =? 120) || (t =? 88))%Z; [exfalso; unfold T_UINT, T_DBL in Ht; congruence|].
    destruct ((t =? 101) || (t =? 102) || (t =? 103) || (t =? 69) || (t =? 70) || (t =? 71))%Z eqn:E4;
      [|discriminate Ht].
    rewrite !Bool.orb_true_iff, !Z.eqb_eq in E4. lia. }
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; (apply jt1_read_lit; [exact H | lia | reflexivity]).
Qed.

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
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.

  (* [comment removed for export] *)
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
  (* [comment removed for export] *)
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Lemma implM_eq_ms : forall {X} (c : M St X) s Q ms ms', ms = ms' -> implM usegs c s Q ms' -> implM usegs c s Q ms.
  Proof. intros X c s Q ms ms' -> H. exact H. Qed.
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].

  (* [comment removed for export] *)
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

  (* [comment removed for export] *)
  Lemma sink_store : forall m st a (bs : list byte),
    SINK m st -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
    (a + Z.of_nat (length bs) <= Fp \/ Fp + 232 <= a)%Z -> (a + Z.of_nat (length bs) <= B \/ B + BS <= a)%Z ->
    SINK (write_to_mem m (wa a) bs) st.
  Proof.
    intros m st a bs HS Ha Hb D1 D2.
    apply (SFR [(a, a + Z.of_nat (length bs))]%Z m _ st HS).
    - apply munch_write; [apply munch_refl | lia | lia | cbn; lia].
    - apply wmono_write. apply wmono_refl.
    - constructor; [cbn; lia | constructor].
    - constructor; [cbn; lia | constructor].
  Qed.
  Lemma sink_call : forall Wc m m' st,
    SINK m st -> munch Wc m m' -> wmono usegs m m' ->
    Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv)%Z Wc ->
    Forall (fun iv => snd iv <= B \/ B + BS <= fst iv)%Z Wc ->
    SINK m' st.
  Proof. intros Wc m m' st HS MU WM D1 D2. exact (SFR Wc m m' st HS MU WM D1 D2). Qed.

  (* [comment removed for export] *)
  Lemma arg_ok_W : forall m m' w a, arg_ok Fp B BS m lo q AP w a -> munch W m m' -> arg_ok Fp B BS m' lo q AP w a.
  Proof.
    intros m m' w a H MU. destruct a as [s|i|u|d]; cbn in H |- *; try exact H.
    destruct H as (slack & BYs & Hs & PAD & NZ & D1 & D2 & D3 & D4 & D5). exists slack.
    split; [|repeat (split; [assumption|]); assumption].
    eapply bytes_at_transport; [exact BYs | exact MU |].
    unfold W. cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
  Qed.
  Lemma args_ok_W : forall m m' ws args, args_ok Fp B BS m lo q AP ws args -> munch W m m' -> args_ok Fp B BS m' lo q AP ws args.
  Proof.
    intros m m' ws args. revert ws. induction args as [|a args IH]; intros ws H MU; [destruct ws; exact I|].
    cbn [args_ok] in H |- *.
    destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2]. split; [eapply arg_ok_W; eauto | apply IH; assumption].
  Qed.

  (* [comment removed for export] *)
  Definition lo_cells14 (pfx s2s za pl plp l10n : word) : list cell :=
    [C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
     C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364)].
  Lemma lo_split : forall m pfx s2s za pl plp l10n alo ahi j128,
    rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
    rw_cells usegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) /\
    rw_cells usegs m (q + -544 + 112) [C8 alo; C8 ahi] /\ rw_cells usegs m (q + -544 + 128) [CB 24 j128].
  Proof.
    clear. intros. unfold lo_cells in H.
    apply (proj1 (rw_cells_app usegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add app] in H2.
    change (Z.of_nat 112) with 112%Z in H2.
    apply (proj1 (rw_cells_app usegs m _ [_;_] _)) in H2. destruct H2 as [H2 H3]. cbn [cells_size csize Nat.add app] in H3.
    change (Z.of_nat 16) with 16%Z in H3.
    split; [exact H1|]. split; [exact H2|]. replace (q + -544 + 128)%Z with (q + -544 + 112 + 16)%Z by lia. exact H3.
  Qed.
  Lemma lo_join : forall m pfx s2s za pl plp l10n alo ahi j128,
    rw_cells usegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) ->
    rw_cells usegs m (q + -544 + 112) [C8 alo; C8 ahi] -> rw_cells usegs m (q + -544 + 128) [CB 24 j128] ->
    rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128).
  Proof.
    clear. intros. unfold lo_cells.
    apply (proj2 (rw_cells_app usegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)). split; [exact H|]. cbn [cells_size csize Nat.add app].
    change (Z.of_nat 112) with 112%Z.
    apply (proj2 (rw_cells_app usegs m _ [_;_] _)). cbn [cells_size csize Nat.add app]. change (Z.of_nat 16) with 16%Z. split; [exact H0|].
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
    rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] ->
    va_area m VA slots -> nth_error slots (Z.to_nat k) = Some slot -> (0 <= k)%Z ->
    rw_cells usegs m (q + -544 + 112) [C8 x; C8 y] ->
    stk usegs m lo (q + -544) ->
    mem_inv usegs m ->
    (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL)%Z ->
    evt usegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft' m',
                 ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          Ft' (ret_pc ra') fc None m' (seg_rom usegs)
                 /\ munch [(q + -544 - 16, q + -544); (AP, AP + 8); (q + -544 + 112, q + -544 + 112 + 16)]%Z m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (q + -544)
                 /\ rw_cells usegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (k + 1)))]
                 /\ rw_cells usegs m' (q + -544 + 112) [C8 (F_pop_arg.pop_arg_lo ty slot); C8 (F_pop_arg.pop_arg_hi ty slot y)]
                 /\ Fokd Ft Ft')
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 ty) (Z_to_bv 64 AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x250cc) fc None m (seg_rom usegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "p'0h02m'h11kh23Ft'h33t6'h43t5'h53t4'h63t3'h73a7'h83a6'h93a5'h:3a4'h;3a3'h<2Fth=3a2'h>3a1'h?3a0'h@2t6hA3t2'hB3t1'hC2t5hD3t0'hE2t4hF2t3hG1HhH2a7hI4__x1hJ2a6hK2a5hL4__x2hM2a4hN2a3hO2a2hP2a1hQ1zhR7__sat13hS7__sat14hT7__sat15hU4cstrhV5cstr0hW7__arithhX4__ffhY8__varmaphZ5__with[2a0h\4__p1h]2t2h^3H12h_3IL0h`7__sat16ha2t1hb3z12hc4__x3hd2t0he3ms'hf2Hahg1Phh7__sat12hi1xi001xhj1Ahk4__p2hl4__p3hm4__x4hn4__x5ho3a0vhp1lhq1nhr3APChs4APC'ht4ARGChu5ARGC'hv2Eahw2Ephx2Eqhy2H0hz2HFh{2Hkh|2ILh}2MIh~3MI'i012MUi023NTHi032STi043ST'i053ST1i063ST2i072TYi083VAAi094VAA'i0:2VBi0;2WMi0<1ai0=1ei0>2fci0?1mi0@1oi0A3ra'i0B2s0i0C2s1i0D3s10i0E3s11i0F2s2i0G2s3i0H2s4i0I2s5i0J2s6i0K2s7i0L2s8i0M2s9i0N4sloti0O2tyi0P1yp%0p%1p%2p&0p&1p;1p;2p;3p;Op;7p;4p;6p;Kp;ip;Lp;5p;:p;8p;<p103o^p6051002p104e@p4p710p8g007ej1MTg008Jj1}Tg008hk107Tg00U>j1GTg004?k210Tg00>AS00k10@Tg01ACk10kTg00dZj2?Tg013Gj1VTg00Emk10KTg057Kj3wTg00EMR0k103Tg00>cj3|Tg00?Ak20?Tg00;Lj3ATg03C\j1HTg00QIj2QTg009Kj2NTg058GlO1Tg00Iek108Tg0599k10hTg03JKk20eTg01?fj2\Tg00T@j3>Tg0158R1j20Tg05:2j73Tg05:dk30ATg01ijj2{Tg05;Uk416Tg00:lk200Tg00N^R2k10[Tg01e2k20ZTg00A_j29Tg00COS01j24Tg00PBk10VTg01mBk20]Tg00C3R3j2TTg01mjk30XTg007Ek10WTg00FMk201Tg01Bkk10uTg00Fkk10tTg00GIk10sTg00H4j2uTg01Clj3~Tg00JGk20qTg00@Gj2rTg00Jik20oTg00KUk30nTg00L4k40mTg05<Wk70lTg00Qcj1qTg00RBk20UTg00STk20DTg01eok30TTg00HWk20STg027Qk20CTg026gk20:Tg021mk20jTg022Vk30iTg01o:k30gTg00Lfj1zTg00lJR4j2vTg05=Ok30fTg002Tk605Tg01T`k20dTg0030k60BTg05>2mK0cmL0aTg00O[k40PTg00Pgk20OTg05?3mi0bTg05@4j1;Tg03n1k204Tg04bfj3LTg05@jk20>Tg04j]k519Tg04kAk317Tg05Anm:15Tg05C3k813Tg01S>j4eTg04m>k40ITg05Ckk60~Tg02G^j4KTg05Dak40\Tg044]k20}Tg03S8k40|Tg05ESk30YTg05FRk202Tg04cZk30HTg00T`k40{Tg00I:k40GTg01CIk30zTg00WXk70LTg00X`k711Tg00YDk809Tg00Rkk30yTg00X<k612Tg00O>k20xTg00Yhm<0wTg00ZMm<14Tg00Uck70vTf0R5#M#Mp=x%G5#Mp>0F%M5#M#M#Mp=jg00;fR6f1R7;A5p=gf2R81{75'?p>0Ng00j;R9f4R:f3R;g02NRR<1N87#H;>5CKp>0Jg00[2R=/95p=FA><75p>0rP9P;P8A><75CKp>0pP9P8P7P5H0\p=C20}95p=Uf6R>f5R?%;:P;P8P7P5F3p=:P6P6P7P5H0|p=b1?75,{8,?;,N:p=6B0Y;87#H=><5p=2P9P>P?202:;#H=><8CK20>75'4p==P9P:P;%H8=><7CK/45p=5B0H9:;1475,48'4p=7g04[FS02?A?:AL;87/45'4p=8P9P:P;%H7=><59><8CKp>0^P6P8P7P5H0{p=X20S65p=lP6P7g00`QR@P5H0Gp=tB0z675p=OP8g00[PS03g00[oS04Q04g00\OS05P6P7P@P5H0Gg00\oR@K0Lp=BP8Q03Q04Q04Q05P7P5K11p=aP:Q03Q04Q04Q05P;Q03Q04Q04Q05P8P@K0LP7P5L09p=sP9P;P8P7H0\/45p>0E20U65p=pB0y675p=oP6P7g00_jP5H0Gp>0=P7Q03Q04Q04Q05P5P@K0Lp>0<P;Q03Q04Q04Q05P8P7P5L09p>0;P>Q03Q04Q04Q05P?P:P;Q03Q04Q04Q05P8P7P5L09L09p=iP7Q03Q04Q04Q05P5J12p>06P6P:P;P8P7P5J0Bp=J20x=5p=hP6g00<iR@P6P6P0P:P2P;g00]OP8P7P5N<0wp>0RP@P6P4P2P3g00nCP?P:P;P8P7P5N<14p>0Q1975,Q8p=]P8Q03Q04Q04Q05P7P5K0vp=fQ02f7R3P>P?P:P;P8P7P5F33Ap=nB0H975p=IP9P3P>1?87,{;,?:,N?#H=><5CKp=R20287#H=><5p=yP9P8P7P5CKp=[204759A;8p=<1475,48p>0`AL;87/45,4:p=d1?87,{;,?:,N?#H=><5p=SP9P:P;P8CK1475'4p>1;1475,48,4;,4:p=mP9P;P8P7CK/45p>0MP9P>P?202:;#H=><8CK1475'4p=@P9P3P>202?:#HB0Y;87#H=><55><CKp=Z20>75,48,4;,4:,4?p=cQ02?A:;1475,48'4p=E1475,48,4;,4:,4?p=_204;8204755A:p=DAw;87/45p=PP9P?P:202;8#H=><7CK/45p=^P9P;P8P7CK/45,4:,4?p=YAL?:;B0H987/45'4p=kQ02?A87/45p=WP9P:P;P8CK20>75'4p>0_Q02?A75p>1:1475,48,4;p>18P>P?P:P;P8P7P5H0IH0Ip=`g00<DR2#MR4#xR0#MRA#MRB#MRC#}RD$07RE%G4RF#}S06010ERG%}B$07%}0$07$0@\ERBp,1qS07&0F0#j$0kRH'?RI%G2S08#GS09#j#VRJ'?RK,g?PKf8RLp,2APRMPDp,2VARN%V0RO<0N>&0K<R<I0Jf9RPp,5slotsRQ7wNS0:&0@ERR&03L9|EQ20?E>3A%FPf<RSPK%H3%H>RT00r<H0pf=RUp,2loRV;CIf>RW#Ug04MWRX9A6Sg04NURY9A6Sg04OSRZ9A6Sg04L4R[9A6S'Q'Q'QQ02fAR\fmS0;1NDIR]p,2gpR^p,2tpR_f@R`f?RaPWfiS0<fhRbPUPSf;Rcf:RdPPPLP3P>fbS0=faS0>f`S0?f_S0@f^S0Af]S0Bf\S0Cf[S0DfZS0EfYS0FP?P:P;P8MO1P7Q0;fSS0G&08EReP5&0h9RfF:20e66Rg%VARA,\IRh/bIRi1?MOS0H,bM1?KAS0I,bK&0KgS0J5>gS0K5>g3>RjfRS0LP5Q0LP5%U5RkAC5VIRlP5PMPDPNPOfPS0M%V2RmD6P<P5PKfOS0NfNS0OQ0NQ0OfLS0PP<C2fTS0QP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWeS0RQ0DP]P^P_Q0EQ0FfXS0SfWS0TfVS0U1NDL1NDUS0V1NDMS0WfUS0XQ0QQ0GQ0LfQRnQ0MQ0NQ0OfMS0YQ0PfKS0ZfJRofIS0[fHS0\fGRpfFS0]fES0^fDS0_fCS0`MO1fBS0a%x2$0F#G#j#G#G#x#G#G#x#V,NDS0bP\PeP`PfF360A9[[[[[[[[Xo6P3PMPD1{O?S0c,?NP<I0JAwLNQS0d&0339|EQ20?E?5AR%FLPcPKPTP?P<I0^ACSVI%UUS0eAA6cXAA6cYAA6cZAA6c['Q'Q'QPaPNPQP>H16%FNS0f200EQS0g$0[S0h:0NNOR[%V4RZ%VCRC+0ZRY'9'4P9P`PVPhPIP;p,3fmt-006RX$0VS0i&0[X#FS0jQ0g$0VS0kQ0h#FS0l%GF#G#GRX#VRT-0]ZS0m1T=ZRq%FT20ZZTRr,T=[[S0n%FZRsg01WWS0oB0XZT7UWfS0pQ0o%Fr[^fsS0q20]ZCS0r%FC1T=Y[\qS0sQ0oB0XZC7UXfsS0tQ0o%FY[^fsS0ug00_>Rs$0KS0v&0WsS0w20168S0x&0u6RC7X7Rq&0t6S0y&0s6RTPT1u62Rt1u64S0z%MFS0{#x#G#x#j#VRF#lR45~6'tQ04$08S0|Q0z%lHS0}'OS0~%lARu5~6S109BTtQ10Q0~5BT5aTDsQ05-0qTS11P5P8g00^^Rvg00a8Rw'r20o58=AvwdB0n6=7H0mS12bXbYbZXI6XL61\7FS13,951?8HRw/\AS14,97Q14/9w'4[^I6^L6P5Q07PVp,2LOS15O3bWS16bhbRbSbTbVbUK0lP`PVPhAC`hIS17H0EQ01AC\VhAC\hIS18Q02P\foS19P]P^P_P`PaPWfkRvfjS1:PUPSPcPdPPPLP3P>fdS1;fcS1<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DP?P:P;P8MO1P7Q19Q0XPeP5PfF:PjQ0QP5Q0QP5PkPlP5PMPDPNPOQ0LPmD6P<P5PKPnQ0MPnQ0MQ0OP<C2Q0UP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWeQ0BP]P^P_Q0CQ0DQ0EQ0FQ0S1NDKS1=1NDaQ0WQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZPoQ0[Q0\PpQ0]Q0^MO1Q0_Q0bQ0`PeQ0aPfF360A9P5Q0`?CVhQ0_?ChIQ0iQ0jQ0kQ0lQ0mQ0nQ0pQ0qQ0rQ0sQ0tQ0ug00b3Rx#qRy#qS1>#p%py20U6xS1?'o'oS1@g00bRRx+0DQ0v5>sS1AQ0wPqQ0yPT%lZRZ%}X60T6-0=t-0<TRXQ0|PT%M2#G#G$0F#G#j#j#j#VR2#lQ0z5BTS1BQ0|PTQ0zA~6t45BTS1CQ0|20S6=RyQ0},OtRz5BTB0T6ZDRZ-0=z-0<T5aTH0;FiQ11Q12bXbYbZXI6XL61T5rS1D1928Rr1\8F,9;R{1?;HR|#F1T|Y'4[[[^I6^L6P5PVQ07p,3QHIp,3GLOS1EQ15O5S1FbWbhbRbSbTbVbU-0CI20:D]R}/gIQ0iQ0jQ0kQ0lQ0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ1AQ0wPqQ0yPTPXQ0|PTQ1BQ0|PTQ1CQ0|%lJS1G,OzRX9BTy20=XZ-0<T5aTH0;FiQ11Q12bXbYbZXI6XL6Q1D1?|JR~#F1T~Y'4\{\r[^I6^L6Q1FbWbhbRbSbTbVbU-0CKQ1=-0:DRr/gKQ0iQ0jQ0kQ0lQ0mQ0nQ0pQ0qQ0rQ0sQ0tQ0up-0R{Q1>#qS1>#pQ1@'o00Dx20j6OQ1>#qS1>#qS1@#q#p60i6Q1@#pQ1>#pQ1?'o'o'o00DxQ0v5>s5>sQ0w2016??X?C9XC82016:9XC;7X7Q0yPTPTQ0{,u6S1?,tyQ0|PT206T3S1>Q09,u6Rs%lORxQ1?60g6'O=BTZ5aTQ0|PT1Otx=BTsQ0|PTPTQ08,u6S08/ttQ0|PTQ1BQ0|PTQ0zQ08=~645BTQ0|ABTytS1?20=tZ-0<T5aTFiDsFiDsQ11Q12bXbYbZXI6XL6Xc6Xm6Xn6W\%F:Q0c,?:/9Y,4>1?8ORZ/9?19?;192?1\3F,9>%F>1T>Y'4[[[[[[^I6^L6^c6^m6^n6^\{P5Q0fQ0hPNQ07PVPMP?PWp,3HVAS0fp,3HAPS0cQ1EQ15O<bWbhbRbSbTbVbU-0CMQ0W-0:DRY/gMg00aXp4p710RF&0W5RyQ01&0@8A|875&0883A#z200;8,v7[R420087,v5&0@;A|;87&08;3A#zRs[200:;,v8\sB0f875P7n2001000000120000000Xq@WpWjP4^q@^py^jFP5PEPQ&03pRFPRQ0^-0?ERyAAR5e#zZ0@RAARyeRyPRQ0]-0?EQ00PEP{P5Q0og01X3R@n10110@00021000000Z0=Rg01XPPeP5J05P@20d@5byWG%zyeA|EQFPaJ0BO4bGQ0]$03Q0g'vP9Q1;P]P^P_Q0?Q0@Q0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0ZPoPrPYPNPQPpQ0]Q0^Q0`Q0[NK0cQ02P\fvS00P]P^P_P`PaPWfrS09fqS1@PUPSPcPdPPPLP3P>PvQ1:Q0<PbfgS1FffS1DfeS1HQ1;Q1<Q0=P?P:P;P8MO1P7Q00Q0CPeP5PfF:PjQ0DP5Q0DP5PkPlP5PMPDPNPOQ0FPmD6P<P5PKQ0SQ0TQ0SQ0TQ0XP<C2Q0BP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWeQ1;P]P^P_Q1<Q0=Q0>Q0?Q0@Q1=Q0],NDRyQ0WQ0AQ0BQ0CQ0DQ0EQ0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PMO1Q0ZQ0bPoPeQ0[PfF3Q1;P]P^P_Q1<Q0=Q0>Q0?Q0@Q1=PyQ0WQ0AQ0BQ0CQ0DQ0EQ0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZPoQ0[PNPQPpQ0]Q0^Q0_Q0`PMPoP5PDQ0\:0NNOP<I0JXQ6P\PYP7DJP`PaQ0g,vF%hpQ0h'TR@PF%h5Xi6S1IPpO1P5Xi6S1JQ1IPpPp1r6pI0RQ0gQ0hQ0h,r6S1KJ0QP5H0PRFP@Q0iQ0jQ0kQ0l20O=oRR1T=o%hoR4/go'419o=AA64='4'QR4Q0Z#hRsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0w20167S1LQ0yPTQ1?Q0|Q1?H0;Q11Q12bXbYbZXI6%F5%F7[^I6P5PnQ0\O2bWbRbSbTb`bbb^bVbUb_PKPoP5Q0^#HQ0_P<I0^XQ6PUPrP8DJPI1\5AS1?=Co5XQ6P:P}P;DJPc1rEyPdPI19A5XQ6PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ1AQ0wPqQ0yPTQ1BQ0|PTQ1CQ0|ABTuzFiQ11Q12bXbYbZXI6XL61927Q13,9819Aw[[^I6^L6P5PVQ07Q1EQ15O4bWbRbSbTb`bbb^bVbUb_P}P;DJPI195YXQ6PM19I5XQ6R2PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wPqQ0yPTPTQ0z,ttQ0|Q0z9BTzDsQ11Q12bXbYbZXI6XL619571?7H/98[^I6^L6P5PMQ07Q0cO3bWbRbSbTb`bbb^bVbUb_PYP7DJP}P;DJPI195rXQ6PKP2PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wQ1LQ0yABTzXQ11Q12bXbYbZXI61?5HRH1?HJ'9^I6P5Q07O1bWbRbSbTb`bbb^bVbUb_PrP8DJP}P;DJPK1?YORH/951?5ARX;]YXQ6PM1?5ORz/9KQ0I;]5XQ6PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wPqQ0yPTPTQ0z/ttQ0|206T:RqQ0~Q1G'OS0~/Ou=BTt5fTDsQ11Q12bXbYbZXI6XL6X\{19751?wJS1L/?A=];7[^I6^L6^\{P5Q0H/9KQ07PMQ0cO4bWbRbSbTb`bbb^bVbUb_PYP7DJPrP8DJPIQ1?,9[?]5NXQ6PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ1AQ0w2016;S1??X;C?X;CQ0x7X7S15Q0yPT1u60R0/Ox=BTtRwQ0|PTQ08=BT0R0Q0|206T?S1EQ08Q0}'ORJ=BTt5fTFiQ11Q12bXbYbZXI6XL6Xc6X\{19Z5R2198;RyA]?|8[[^I6^L6^c6^\{P519[hPMQ07PNQ0fQ0cO6bWbRbSbTb`bbb^bVbUb_P}P;DJPM19[5R|?]zNXQ6PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wQ0x9XC7Q0yPTQ08/Ox=BTtRxQ0|AfTqxH0;Q11Q12bXbYbZXI6XL6X\{1?7O/95A];Z7[^I6^L6^\{P519[MPMPNQ0fO4bWbRbSbTb`bbb^bVbUb_PYP7DJPKA]|XNXQ6PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ1AQ0wQ15Q0yPTPwQ0|PTP0Q0|Q1EQ1G,OJ/Ou=BTt5fTFiQ11Q12bXbYbZXI6XL6Xc6X\{1?~A=]?8\y\2^I6^L6^c6^\{P519[KPMQ07PNQ0fQ0cO6bWbRbSbTb`bbb^bVbUb_PrP8DJNi0bQ02Q1HP]P^P_Q0>Q0?Q0EQ0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0PQ0ZPrPYPNPQQ0\PpQ0]Q0_PoP5NL0aS0fP6P}Q0`fxR}P]P^P_P`PaPWftR[fsS1GPUPSPcPdPPPLP3P>Q0;flS15PvQ1:Q0<PbQ1FQ1DQ1HQ1;P?P:P;P8MO1P7%;}Q0APeP5PfGnR21\\ARy/b\1bYHRH1?rA,brQ0J5>g5>gR~5>gQ0BP5Q0B/I5RuP5PyP\P5PYPDPNPOQ0DPmP<GRRyQ0EQ0FQ0EQ0FQ0TP<C23yRJ9[5rAw5NQR0Q06$07RwQ0600:5Q0{#V'g#zRsPE204;7R4Q0>P7C<[]1'4RR40`H0E80`kDdX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EXQ6P5PIP?J05Q0afwR@P]P^P_P`PaPWQ1GQ09PUPSPcPdPPPLP3P>Q15PvQ1:Q0<PbQ1FQ1DQ1HQ1;Q1<P?P:P;P8MO1P7%;@Q0BPeP5PfGnS0{A>gi~Q0CP5Q0C/I5S06PkAC5hIR~PDPNPOQ0EPmP<ESS1A9[5YP5PrQ0FQ0SQ0FQ0SQ0UP<C23yS0}P0PEP4Q0?P7C<\s^1wI1;DmDdX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EP6PrQ0_fyS13P]P^P_P`PaPWfuS1CP[PUPSPcPdPPPLP3P>fnS1BQ0;Q15PvQ1:Q0<PbQ1FQ1DQ1HP?P:P;P8MO1P7Q13#;Q0@PeP5PfGnRr1?\A,b\Q0J5>g9>gH9>giQ0AP5Q0A/I5RAPkP~PDPNPOQ0CPmP<ESRF9[5YP5P\Q0DQ0EQ0DQ0EQ0SP<C23yR|PEP4Q0=P7C<\s^1w,40RXH0MDmDdX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EXQ6P5PKP?J05P2Q0K9>gH9>giQ0BP5PuPkP~PyP5PKPJPRH0MDmDdX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EP6PYQ0^fzRYP]P^P_P`PaPWQ00Q1CPUPSPcPdPPPLP3P>Q19Q1BQ0;Q15PvQ1:Q0<PbQ1FQ1DP?P:P;P8MO1P7%;YQ0?PeP5PfGnRR1?\O,b\Q0K5>g9>giQ0@P5Q0@/I5RiPkP~PDPNPOQ0BPmP<ESRg9[5\P5PKQ0CQ0DQ0CQ0DQ0FP<C2P0PEP4Q1<P7C<\s^1wF@RJDmDdX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EXQ6P5PMP?J05PrPjQ0AP5PAPkP~A[5MFP5PKP|PXH0MDmDdX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EP1PEPRPjQ0@P5PiPkP~A[5MgPJDmDdX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdEQ0]f{RJP]P^P_P`PaPWP@Q00PUPSPcPdPPPLP3P>fpS0KQ19Q1BQ0;Q15PvQ1:Q0<PbQ1FP?P:P;P8MO1P7PJQ0>PeP5PfF:PjQ0?P5Q0?P5PkPlP5PMPDPNPOQ0APmD6P<P5PKQ0BQ0CQ0BQ0CQ0EP<C2Q0=P7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Ppf|S0JP]P^P_P`PaPWP}P@PUPSPcPdPPPLP3P>Q1@Q0KQ19Q1BQ0;Q15PvQ1:Q0<PbP?P:P;P8MO1P7Q0JQ0=PeP5PfF:PjQ0>P5Q0>P5PkP~P5PMPDPNPOQ0@PmD6P<P5PKQ0AQ0BQ0AQ0BQ0DP<C2P0PEP4Q1HP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EP1PEQ0\f}RgP]P^P_P\PaPWQ13P}PUPSPcPdPPPLP3P>Q09Q1@Q0KQ19Q1BQ0;Q15PvQ1:Q0<P?P:P;P8MO1P7PgQ1<PeP5PfF:PjQ0=P5Q0=P5PkP~P5PMPDPNPOQ0?PmD6P<P5PKQ0@Q0AQ0@Q0AQ0CP<C2P0PEP4Q1DP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaEPop+01@RiP]P^P_P`PaPWPJPYPUPSPcPdPPPLP3P>P[Q1GQ09Q1@Q0KQ19Q1BQ0;Q15PvP?P:P;P8MO1P7%;iRRQ1HPeP5PfF3Q1;=Lj5RXQ1;/I5R|PkPlP5PMPDPNPOQ0=PmP<GRRFP5PKQ0>Q0?Q0>Q0?Q0AP<GZRAQ1DP7EcDEX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5PoPiP]P^P_Q0`PaPWPJPYPUPSPcPdPPPLP3P>P[Q1GQ09Q1@Q0KQ19Q1BQ0;Q15PvP?P:P;P8MO1P7PRQ1HPeP5PfF3PXP|PkP~PFPAP0PEP4PbP7C<\s^1wE_DEX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EP1PEQ0Zp+01ARAP]P^P_Q0_P`PWQ0JPJPUPSPcPdPPPLP3P>Q1CP[Q1GQ09Q1@Q0KQ19Q1BQ0;Q15P?P:P;P8MO1P7PAQ1DPeP5PfF:PjQ1HP5Q1HP5PkP~P5PMPDPNPOQ1<PmD6P<P5PKQ0=Q0>Q0=Q0>Q0@P<C2P0PEP4Q0<P7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]EQ0Op+01DRFP]P^P_P`PaPWPif~S1MPUPSPcPdPPPLP3P>P}P@Q00Q1CP[Q1GQ09Q1@Q0KQ19P?P:P;P8MO1P7%;FR|Q0<PeP5PfF3ALjb5RX1Ib5RRPkPlP5PMPDPNPOQ1DPmP<GRRrP5PKQ1HQ1;Q1HQ1;Q0=P<GZRyQ1:P7EcDEX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0Yp+01CRuP]P^P_Q0]Q0aPWQ1MPgPUPSPcPdPPPLP3P>P@Q00Q1CP[Q1GQ09Q1@Q0KQ19Q1BP?P:P;P8MO1P7PuPbPeP5PfF:PjQ1FP5Q1FP5PkP~P5PMPDPNPOQ1HPmD6P<P5PKQ1;Q1<Q1;Q1<Q0>P<C2P0PEP4PvP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EP1PEQ0OPFP]P^P_PpQ0`PaPiQ1MPUPSPcPdPPPLP3P>P}P@Q00Q1CP[Q1GQ09Q1@Q0KQ19P?P:P;P8MO1P7P|Q0<PeP5PfF3PXPRPkP~PrPyP0PEP4Q15P7C<\s^1wE_DEX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[EQ0Lp+01HRyP]P^P_P`PaPWPFPuPUPSPcPdPPPLP3P>Q0JPJPYQ13P}P@Q00Q1CP[Q1GP?P:P;P8MO1P7PyQ0;PeP5PfF:PjQ15P5Q15P5PkPlP5PMPDPNPOQ1:PmD6P<P5PKQ0<PbQ0<PbQ1DP<C2Q1BP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0Mp+01FS1NP]P^P_Q0[Q0^P\p+01BS1OPAPUPSPcPdPPPLP3P>PYQ13P}P@Q00Q1CP[Q1GQ09Q1@P?P:P;P8MO1P7Q1NPvPeP5PfF:PjQ1:P5Q1:P5PkP~P5PMPDPNPOPbPmD6P<P5PKQ1FQ1DQ1FQ1DQ1;P<C2P0PEP4Q1BP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EP1PEPnp+01GRrP]P^P_PoQ0]Q0aPuQ1OPWPSPcPdPPPLP3P>PJPYQ13P}P@Q00Q1CP[Q1GQ09P?P:P;P8MO1P7PrQ15PeP5PfF:PjPvP5PvP5PkP~P5PMPDPNPOQ0<PmD6P<P5PKPbQ1FPbQ1FQ1HP<C2P0PEP4Q19P7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPEQ0Up+01LRRP]P^P_P`PaPWPyPrPUPSPcPdPPPLP3P>PAPiQ1MPgQ0JPJPYQ13P}P@P?P:P;P8MO1P7%;RRXQ1@PeP5PfF3Q0K=Lj5R|Q0K/I5RHPkPlP5PMPDPNPOQ1BPmP<GRR2P5PKQ0;Q15Q0;Q15Q1:P<GZRZQ09P7EcDEX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0Gp+01IRxP]P^P_Q0PQ0\Q0_p+01ES1PPFP`PSPcPdPPPLP3P>PgQ0JPJPYQ13P}P@Q00Q1CP[P?P:P;P8MO1P7PxQ1BPeP5PfF:PjQ0;P5Q0;P5PkP~P5PMPDPNPOPvPmD6P<P5PKQ1:Q0<Q1:Q0<Q1FP<C2P0PEP4Q1@P7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EP1PEQ0Qp+01JRqP]P^P_Q0YQ0[Q0^Q1NQ1PP\PUPcPdPPPLP3P>Q1MPgQ0JPJPYQ13P}P@Q00Q1CP?P:P;P8MO1P7PqQ19PeP5PfF:PjQ1BP5Q1BP5PkP~P5PMPDPNPOQ15PmD6P<P5PKPvQ1:PvQ1:PbP<C2P0PEP4Q09P7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOEQ0Ep+01PRCP]P^P_P`PaPWPRp+01KS1QPUPSPcPdPPPLP3P>Q1PPFPuQ1OPAPiQ1MPgQ0JPJP?P:P;P8MO1P7%;CS1RQ1CPeP5PfF3ALj[5S1S1I[5S1TPkPlP5PMPDPNPOQ09PmP<GRS1UP5PKQ1@Q0KQ1@Q0KQ1BP<GZRzQ00P7EcDEX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0UPRP]P^P_Q0NQ0ZPpPyPrQ0`PaPcPdPPPLP3P>PAPiQ1MPgQ0JPJPYQ13P}P@P?P:P;P8MO1P7PXQ1@PeP5PfF3P|PHPkP~P2PZP0PEP4P[P7C<\s^1wE_DEX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EP1PEQ0Tp+01MRZP]P^P_Q0MQ0PQ0\PxPyQ0_P`PSPdPPPLP3P>Q1OPAPiQ1MPgQ0JPJPYQ13P}P?P:P;P8MO1P7PZQ09PeP5PfF:PjQ1@P5Q1@P5PkP~P5PMPDPNPOQ19PmD6P<P5PKQ1BQ0;Q1BQ0;PvP<C2P0PEP4Q1CP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNEQ0Ap+01TS1VP]P^P_P`PaPWPCp+01OR2PUPSPcPdPPPLP3P>PxPyPrQ1NQ1PPFPuQ1OPAPiP?P:P;P8MO1P7Q1VQ13PeP5PfF:PjP}P5P}P5PkPlP5PMPDPNPOQ00PmD6P<P5PKQ1CP[Q1CP[Q09P<C2PYP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0FP2P]P^P_Q0LQ0OPoQ1QPqQ0]Q0aPWPdPPPLP3P>PFPuQ1OPAPiQ1MPgQ0JPJPYP?P:P;P8MO1P7P2P[PeP5PfF:PjQ1GP5Q1GP5PkP~P5PMPDPNPOQ1@PmD6P<P5PKQ0KQ19Q0KQ19Q0;P<C2P0PEP4P@P7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EP1PEQ0EPCP]P^P_Q0GQ0NQ0ZPRQ1QPpQ0`PaPcPPPLP3P>Q1PPFPuQ1OPAPiQ1MPgQ0JPJP?P:P;P8MO1P7Q1RQ1CPeP5PfF3Q1SQ1TPkP~Q1UPzP0PEP4P}P7C<\s^1wE_DEX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXMEQ0=p+01XS1UP]P^P_P`PaPWQ1Vp+01SRzPUPSPcPdPPPLP3P>PZPRQ1QPqPxPyPrQ1NQ1PPFP?P:P;P8MO1P7Q1U#;S1TPgPeP5PfF3Q0J=Lj5S1SQ0J/I5S1RPkPlP5PMPDPNPOPYPmP<GRS1WP5PKQ13P}Q13P}Q00P<GZS1XQ1MP7EcDEX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0Cp+01RS1YP]P^P_Q0XPnQ0Yp+01NRHPZQ0[Q0^P\PUPPPLP3P>PrQ1NQ1PPFPuQ1OPAPiQ1MPgP?P:P;P8MO1P7Q1YP@PeP5PfF:PjQ00P5Q00P5PkP~P5PMPDPNPOP[PmD6P<P5PKQ1GQ09Q1GQ09Q0KP<C2P0PEP4PYP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EP1PEQ0BPzP]P^P_Q0UQ0LQ0OP2PHPoQ0]Q0aPWPdPLP3P>PyPrQ1NQ1PPFPuQ1OPAPiQ1MP?P:P;P8MO1P7PzP}PeP5PfF:PjP@P5P@P5PkP~P5PMPDPNPOQ1CPmD6P<P5PKP[Q1GP[Q1GQ1@P<C2P0PEP4PJP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKEQ1Dp+01\S1ZP]P^P_P`PaPWQ1Up+01WR|PUPSPcPdPPPLP3P>p+01QS1[PCP2PHPZPRQ1QPqPxPyP?P:P;P8MO1P7Q1Z#;S1\Q1OPeP5PfF3ALjA5S1]1IA5S1^PkPlP5PMPDPNPOQ1MPmP<GRS1_P5PKPgQ0JPgQ0JPYP<GZS1`PuP7EcDEX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0@p+01US1aP]P^P_Q0SQ0QQ0MQ1[PCQ0PQ0\Q0_P`PSPLP3P>PqPxPyPrQ1NQ1PPFPuQ1OPAP?P:P;P8MO1P7Q1aPYPeP5PfF:PjQ13P5Q13P5PkP~P5PMPDPNPOP@PmD6P<P5PKQ00Q1CQ00Q1CQ1GP<C2P0PEP4PgP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EP1PEQ0?p+01VRXP]P^P_Q0FQ0XPnQ1YQ1[Q0YQ0[Q0^P\PUPPP3P>Q1QPqPxPyPrQ1NQ1PPFPuQ1OP?P:P;P8MO1P7PXPJPeP5PfF:PjPYP5PYP5PkP~P5PMPDPNPOP}PmD6P<P5PKP@Q00P@Q00P[P<C2P0PEP4Q1MP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJEQ1:p+01`S1bP]P^P_P`PaPWQ1Zp+01[S1cPUPSPcPdPPPLP3P>Q1aQ1VPzQ1YQ1[PCP2PHPZPRP?P:P;P8MO1P7Q1bQ1NPeP5PfF:PjQ1PP5Q1PP5PkPlP5PMPDPNPOPuPmD6P<P5PKQ1OPAQ1OPAQ1MP<C2PrP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0=Q1UP]P^P_Q0DQ0TQ0GQ1VPzQ0NQ0ZPpQ0`PaPcP3P>PZPRQ1QPqPxPyPrQ1NQ1PPFP?P:P;P8MO1P7Q1TPgPeP5PfF3Q1SQ1RPkP~Q1WQ1XP0PEP4PAP7C<\s^1wE_DEX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EP1PEQ1<p+01YS1XP]P^P_Q0CQ0SQ0QQ1aQ1VQ0MQ0PQ0\Q0_P`PSPLP>PHPZPRQ1QPqPxPyPrQ1NQ1PP?P:P;P8MO1P7Q1XQ1MPeP5PfF:PjPgP5PgP5PkP~P5PMPDPNPOPJPmD6P<P5PKPYQ13PYQ13P@P<C2P0PEP4Q1OP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHEQ1Bp+01dS1WP]P^P_P`PaPWQ1bp+01_S1RPUPSPcPdPPPLP3P>Q1XQ1UP|PXQ1aQ1VPzQ1YQ1[PCP?P:P;P8MO1P7Q1W#;S1SPqPeP5PfF3ALjx5S1T1Ix5S1dPkPlP5PMPDPNPOPrPmP<GRS1eP5PKQ1NQ1PQ1NQ1PPuP<GZS1fQ1QP7EcDEX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1HQ1cP]P^P_Q0AQ0EQ0UP|PXQ0LQ0OPoQ0]Q0aPWPdP>PCP2PHPZPRQ1QPqPxPyPrP?P:P;P8MO1P7Q1cPAPeP5PfF:PjPiP5PiP5PkP~P5PMPDPNPOPgPmD6P<P5PKQ0JPJQ0JPJQ13P<C2P0PEP4PFP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EP1PEQ1DQ1ZP]P^P_Q0@Q0DQ0TQ1UP|Q0GQ0NQ0ZPpQ0`PaPcP3Q1[PCP2PHPZPRQ1QPqPxPyP?P:P;P8MO1P7Q1\Q1OPeP5PfF3Q1]Q1^PkP~Q1_Q1`P0PEP4Q1PP7C<\s^1wE_DEX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFEQ09p+01hS1`P]P^P_P`PaPWQ1Wp+01cS1_PUPSPcPdPPPLP3P>p+01]S1^Q1ZQ1cp+01ZS1]Q1XQ1UP|PXQ1aQ1VP?P:P;P8MO1P7Q1`#;S1\PHPeP5PfF3ALjZ5S1g1IZ5S1hPkPlP5PMPDPNPOQ1QPmP<GRS1iP5PKPqPxPqPxPrP<GZS1jP2P7EcDEX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Pbp+01^S1kP]P^P_Q0>Q0BQ0FQ1]Q1XQ0XPnQ0YQ0[Q0^P\PUPPPzQ1YQ1[PCP2PHPZPRQ1QPqP?P:P;P8MO1P7Q1kPFPeP5PfF:PjPuP5PuP5PkP~P5PMPDPNPOPAPmD6P<P5PKPiQ1MPiQ1MQ0JP<C2P0PEP4PrP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EP1PEQ0<Q1RP]P^P_Q0=Q0AQ0EQ1cQ1]Q0UQ0LQ0OPoQ0]Q0aPWPdQ1VPzQ1YQ1[PCP2PHPZPRQ1QP>P:P;P8MO1P7Q1RQ1PPeP5PfF:PjPFP5PFP5PkP~P5PMPDPNPOQ1OPmD6P<P5PKPAPiPAPiPgP<C2P0PEP4PyP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEEQ00p+01lS1lP]P^P_P`PaPWQ1`p+01gS1mPUPSPcPdPPPLP3P>p+01aS1nQ1bQ1RQ1kQ1^Q1ZQ1cQ1]Q1XQ1UP?P:P;P8MO1P7Q1lQ1YPeP5PfF:PjQ1[P5Q1[P5PkPlP5PMPDPNPOP2PmD6P<P5PKPHPZPHPZQ1QP<C2PzP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5PvQ1nP]P^P_Q1;Q0?Q0CQ1^Q1ZQ0SQ0QQ0MQ0PQ0\Q0_P`PSPXQ1aQ1VPzQ1YQ1[PCP2PHPZPLP:P;P8MO1P7Q1nPrPeP5PfF:PjQ1NP5Q1NP5PkP~P5PMPDPNPOPFPmD6P<P5PKPuQ1OPuQ1OPiP<C2P0PEP4PqP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCE,0EP1PEQ15p+01bS1oP]P^P_Q1HQ0>Q0BQ1kQ1^Q0FQ0XPnQ0YQ0[Q0^P\PUP|PXQ1aQ1VPzQ1YQ1[PCP2PHPPP?P;P8MO1P7Q1oPyPeP5PfF:PjPrP5PrP5PkP~P5PMPDPNPOQ1PPmD6P<P5PKPFPuPFPuPAP<C2P0PEP4Q1QP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@E,0EXCEPYp+020S1pP]P^P_P`PaPWQ1lp+01kS1qPUPSPcPdPPPLP3P>p+01eS1rQ1WQ1_Q1oQ1nQ1bQ1RQ1kQ1^Q1ZP?P:P;P8MO1P7Q1p#;S1sPXPeP5PfF3PjQ1aP5Q1aP5PkPlP5PMPDPNPOPzPmD6P<P5PKQ1YQ1[Q1YQ1[P2P<C2P|P7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1BQ1WP]P^P_Q1FQ1<Q0@Q1bQ1RQ0DQ0TQ0GQ0NQ0ZPpQ0`PaQ1XQ1UP|PXQ1aQ1VPzQ1YQ1[PCPcP3P;P8MO1P7Q1SPqPeP5PfF3Q1TQ1dPkP~Q1eQ1fP0PEP4PZP7C<\s^1wE_DEX0B,0BX<G,0GX@E,0EP1PEQ19Q1rP]P^P_PbQ1;Q0?Q1nQ1bQ0CQ0SQ0QQ0MQ0PQ0\Q0_P`Q1]Q1XQ1UP|PXQ1aQ1VPzQ1YQ1[PSPLP:P8MO1P7Q1rQ1QPeP5PfF:PjPqP5PqP5PkP~P5PMPDPNPOPyPmD6P<P5PKPrQ1NPrQ1NPFP<C2P0PEP4PHP7C<\s^1wF@D5D7E8X0B,0BX<G,0GX@EQ1Mp+024S1fP]P^P_P`PaPWQ1pp+01oS1ePUPSPcPdPPPLP3P>p+01iS1dQ1`Q1mp+01fS1TQ1rQ1WQ1_Q1oQ1nQ1bP?P:P;P8MO1P7Q1fQ1]PeP5PfF:PjQ1XP5Q1XP5PkPlP5PMPDPNPOP|PmD6P<P5PKPXQ1aPXQ1aPzP<C2Q1cP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1@Q1mP]P^P_Q1:Q1DQ0=Q1_Q1oQ0AQ0EQ0UQ0LQ0OPoQ0]Q0aQ1ZQ1cQ1]Q1XQ1UP|PXQ1aQ1VPzPWPdP>P8MO1P7Q1mPZPeP5PfF:PjPRP5PRP5PkP~P5PMPDPNPOPqPmD6P<P5PKPxPyPxPyQ1NP<C2P0PEP4PCP7C<\s^1wF@D5D7E8X0B,0BX<G,0GP1PGQ09Q1`P]P^P_PvQ1FQ1<Q1WQ1_Q0@Q0DQ0TQ0GQ0NQ0ZPpQ0`Q1^Q1ZQ1cQ1]Q1XQ1UP|PXQ1aQ1VPaPcP3P;MO1P7Q1\PHPeP5PfF3Q1gQ1hPkP~Q1iQ1jP0PEP4Q1[P7C<\s^1wE_DEX0B,0BX<GPup+028S1jP]P^P_P`PaPWQ1fp+023S1iPUPSPcPdPPPLP3P>p+01mS1hQ1lQ1qp+01jS1gQ1dQ1`Q1mQ1TQ1rQ1WP?P:P;P8MO1P7Q1jQ1kPeP5PfF:PjQ1^P5Q1^P5PkPlP5PMPDPNPOQ1cPmD6P<P5PKQ1]Q1XQ1]Q1XP|P<C2Q1RP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5P[Q1gP]P^P_Q0;Q0<Q1HQ1TQ1rQ0>Q0BQ0FQ0XPnQ0YQ0[Q0^Q1RQ1kQ1^Q1ZQ1cQ1]Q1XQ1UP|PXP\PUPPP?MO1P7Q1gPCPeP5PfF:PjP2P5P2P5PkP~P5PMPDPNPOPZPmD6P<P5PKPRQ1QPRQ1QPxP<C2P0PEP4PzP7C<\s^1wF@D5D7E8X0B,0BP1PBQ1CQ1qP]P^P_Q1BQ1:Q1DQ1mQ1TQ0=Q0AQ0EQ0UQ0LQ0OPoQ0]Q1bQ1RQ1kQ1^Q1ZQ1cQ1]Q1XQ1UP|Q0aPWPdP>MO1P8Q1qQ1[PeP5PfF:PjPCP5PCP5PkP~P5PMPDPNPOPHPmD6P<P5PKPZPRPZPRPqP<C2P0PEP:P7Q1VP7DD\s^1wF@D5D7E8X0BPrp+02<S1\P]P^P_P`PaPWQ1jp+027S1SPUPSPcPdPPPLP3P>p+021S1tQ1pQ1ep+01nS1uQ1hQ1lQ1qQ1gQ1dQ1`P?P:P;P8MO1P7Q1\Q1oPeP5PfF:PjQ1nP5Q1nP5PkPlP5PMPDPNPOQ1RPmD6P<P5PKQ1kQ1^Q1kQ1^Q1cP<C2Q1_P7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5P@Q1hP]P^P_Q0KQ15PbQ1dQ1`Q1;Q0?Q0CQ0SQ0QQ0MQ0PQ0\Q1oQ1nQ1bQ1RQ1kQ1^Q1ZQ1cQ1]Q1XQ0_P`PSPLMO1P:Q1hPzPeP5PfF:PjQ1YP5Q1YP5PkP~P5PMPDPNPOPCPmD6P<P5PKP2PHP2PHPRP<C2P0PEP>P7PXP7DD\s^1wF@D5D7E8Q01P}Q1uP]P^P_Q1@Q0;Q0<Q1gQ1dQ1HQ0>Q0BQ0FQ0XPnQ0YQ0[Q1_Q1oQ1nQ1bQ1RQ1kQ1^Q1ZQ1cQ1]Q0^P\PUPPMO1P?Q1u#;Q1VPeP7PfGnPjPzP7PzP7%U7AC7hIP7PMPDPNPOQ1[PmP<ESP7PKPCP2PCP2PZP<C2P7PNPQPEP3P7P|P7DD\s^1wCPE^EYEkQ1Qp+02@R0P]P^P_P`PaPWQ1\p+02;S1vPUPSPcPdPPPLP3P>p+025S1wQ1fQ1ip+022S1xQ1tQ1pQ1eQ1uQ1hQ1lP?P:P;P8MO1P7P0Q1TPeP5PfF:PjQ1rP5Q1rP5PkPlP5PMPDPNPOQ1_PmD6P<P5PKQ1oQ1nQ1oQ1nQ1RP<C2Q1mP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5PYQ1pP]P^P_Q1GQ19PvQ1lQ1qQ1FQ1<Q0@Q0DQ0TQ0GQ0NQ0ZQ1rQ1WQ1_Q1oQ1nQ1bQ1RQ1kQ1^Q1ZPpQ0`PaPcMO1P3Q1sPXPeP;PfGnQ02Q1tP]P^P_P[Q0KQ15Q1hQ1lPbQ1;Q0?Q0CQ0SQ0QQ0MQ0PQ1TQ1rQ1WQ1_Q1oQ1nQ1bQ1RQ1kQ1^Q0\Q0_P`PSMO1PLQ1tP|PeP:PfF:Q02ALj|?S1lP|P?%U?AC?hIP?PMPDPNPOQ1aPmD6P<P?PKQ1VPzQ1VPzQ1[P<C2P?PNPQPEPcP7Q1cP7DD\s^1wCPE^D5D7S1s'4Q0ap+02DR~P]P^P_P`PaPWP0p+02?S1yPUPSPcPdPPPLP3P>p+029S1zQ1jQ1Sp+026S1{Q1wQ1fQ1iQ1xQ1tQ1pP?P:P;P8MO1P7%;~S1|Q1gPeP5PfF3R1PjQ1dP5Q1dP5PkPlP5PMPDPNPOQ1mPmP<ESS1}P5PKQ1TQ1rQ1TQ1rQ1_P<C2Q1qP7F=EYEkR43WX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0E[WePjPXP:PXP:%U:AC:hIP:PMPDPNPOQ1VPmP<ESP:PKPzQ1YPzQ1YPCP<C2P:PNPQPEPdP7Q1]P7DD\s^1wCPE^EYEkQ01Q1lQ1sP~P]P^P_PyPFPiP0Q1yPJP@Q1GQ19PvQ1FQ1<Q0@Q1zQ1jQ1SQ1{Q1wQ1fQ1iQ1xQ1tQ1pQ0DQ0TQ0GQ0NMO1Q0ZQ1|Q1gPePpPfF3?W14X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1X=Lj3Q1]PL%ULACLhIPLPMPDPNPOQ1UPmD6P<PLPKP|PXP|PXQ1VP<C2Q0dPEPWP7Q1kP7DD\s^1wF@D5D7Q01Q1c/IP%UPACPhIPPPMPDPNPOQ1XPmP<ESPPPKQ1UP|Q1UP|Q1aP<C2Q0:PEPaP7Q1RP7DD\s^1wF@EYp+02HR4P]P^P_PRPyPFP~p+02CS0:PiPJP@Q1GQ19PvQ1FQ1<p+02=S0dQ1\Q1vp+02:S1|Q1zQ1jQ1SQ1{Q1wQ1fQ0@Q0DQ0TQ0GMO1Q0N%;4R1Q1uPeQ0ZPfF3P4P]P^P_P`PaPWP~Q0:PUPSPcPdPPPLP3P>Q0dQ1\Q1vQ1|Q1zQ1jQ1SQ1{Q1wQ1fP?P:P;P8MO1P7P1Q1uPeP5PfF3PjQ1hP5Q1hP5PkPlP5PMPDPNPOQ1qPmD6P<P5PKQ1gQ1dQ1gQ1dQ1mP<C23yS1dQ1eP7I0_D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1^/Ic%USACShIPSPMPDPNPOQ1ZPmP<ESPSPKQ1cQ1]Q1cQ1]Q1UP<C2PSPNPQPEQ0aP7Q1oP7DD\s^1wCPE^EYQ01Q0ePUPhPIPUPMPDPNPOQ1^PmD6P<PUPKQ1ZQ1cQ1ZQ1cQ1XP<C2PUPNPQPEQ0`P7Q1_P7DD\s^1wCPE^D5H0Ep+02LR1P]P^P_PCPRPyP4p+02GS0ePFPiPJP@Q1GQ19PvQ1Fp+02AS1sP0Q1yp+02>S1lQ0dQ1\Q1vQ1|Q1zQ1jQ1<Q0@Q0DQ0TMO1Q0G%;1S1~Q1xPeQ0NPfF3P1P]P^P_P`PaPWP4Q0ePUPSPcPdPPPLP3P>Q1sP0Q1yQ1lQ0dQ1\Q1vQ1|Q1zQ1jP?P:P;P8MO1P7Q1~Q1xPeP5PfF3PjQ1tP5Q1tP5PkPlP5PMPDPNPOQ1ePmD6P<P5PKQ1uQ1hQ1uQ1hQ1qP<C2Q1iP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5%UaQ17P`PMPDPNPOQ1bPmP<GRP`PKQ1RQ1kQ1RQ1kQ1ZP<C23yP`PNPQPEQ0]P7Q1TP7DD\s^1wCPEYQ01Q18P\PMPDPNPOQ1nPmD6P<P\PKQ1bQ1RQ1bQ1RQ1^P<C2P\PNPQPEPpP7Q1mP7DD\s^1wCPE^D5p+02PS18P]P^P_Q1VPCPRP1p+02KS17PyPFPiPJP@Q1GQ19Pvp+02ES1~P~Q0:p+02BS20Q1sP0Q1yQ1lQ0dQ1\Q1FQ1<Q0@Q0DMO1S21Q0TQ18#;S22Q1{PeQ0GPfF3S23Q18P]P^P_P`PaPWP1Q17PUPSPcPdPPPLP3P>Q1~P~Q0:Q20Q1sP0Q1yQ1lQ0dQ1\P?P:P;P8MO1P7Q22Q1{PeP5PfF3PjQ1wP5Q1wP5PkPlP5PMPDPNPOQ1iPmP<ESP5PKQ1xQ1tQ1xQ1tQ1eP<C2Q1SP7F=EYEkS243WX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0`?ChIQ0_PMPDPNPOQ1WPmD6P<Q0_PKQ1_Q1oQ1_Q1oQ1bP<C2Q0_PNPQPEPoP7Q1gP7DD\s^1wCPE^D5Q01Q0^PMPDPNPOQ1rPmP<GRQ0^PKQ1WQ1_Q1WQ1_Q1nP<C2Q0^PNPQPEQ0ZP7Q1qP7DD\s^1wCPE^p+02TS1qP]P^P_Q1UQ1VPCQ18p+02OS1gPRPyPFPiPJP@Q1GQ19p+02IS25P4Q0ep+02FS26Q1~P~Q0:Q20Q1sP0PvQ1FQ1<Q0@MO1Q0DQ1q#;S27Q1|PeQ0TPfF3S28Q1qP]P^P_P`PaPWQ18Q1gPUPSPcPdPPPLP3P>Q25P4Q0eQ26Q1~P~Q0:Q20Q1sP0P?P:P;P8MO1P7Q27Q1|PeP5PfF3PjQ1zP5Q1zP5PkPlP5PMPDPNPOQ1SPmP<ESP5PKQ1{Q1wQ1{Q1wQ1iP<C2Q1vP7F=EYEkS293WX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1}9[pMQ0\PKQ1mQ1TQ1mQ1TQ1WP<C2Q0\PNPQPEQ0OP7Q1uP7DD\s^1wCPE^Q01Q0[PKQ1`Q1mQ1`Q1mQ1rP<GZQ0[PNPQPEQ0NP7Q1eP7DD\s^1wCPp+02XS1rP]P^P_Q1ZQ1UQ1VQ1qp+02SS1mPCPRPyPFPiPJP@Q1Gp+02MS1`P1Q17p+02JS1WQ25P4Q0eQ26Q1~P~Q19PvQ1FQ1<MO1Q0@Q1r#;S1TQ1lPeQ0DPfF3S1}Q1rP]P^P_P`PaPWQ1qQ1mPUPSPcPdPPPLP3P>Q1`P1Q17Q1WQ25P4Q0eQ26Q1~P~P?P:P;P8MO1P7Q1TQ1lPeP5PfF3PjQ0dP5Q0dP5PkPlP5PMPDPNPOQ1vPmP<ESP5PKQ1|Q1zQ1|Q1zQ1SP<C2Q1yP7F=EYEkS2:3WX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0ZQ1d7[KQ0PPNPQPEQ0LP7Q1xP7DD\s^1wCPQ01Q0Y?wNQPEQ0GP7Q1iP7DD\s^1wp+02\S01P]P^P_Q1bQ1ZQ1UQ1rp+02WS1dQ1VPCPRPyPFPiPJP@p+02QS2;Q18Q1gp+02NS2<Q1`P1Q17Q1WQ25P4Q1GQ19PvQ1FMO1Q1<Q01#;S1<Q20PeQ0@PfF3S2=Q01P]P^P_P`PaPWQ1rQ1dPUPSPcPdPPPLP3P>Q2;Q18Q1gQ2<Q1`P1Q17Q1WQ25P4P?P:P;P8MO1P7Q1<Q20PeP5PfF3PjQ1sP5Q1sP5PkPlP5PMPDPNPOQ1yPmP<ESP5PKQ1lQ0dQ1lQ0dQ1vP<C2Q0:P7F=EYEkS2>3WX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0N?wNQPEQ0UP7Q1{P7DD\s^1wPEp+02_RwP]P^P_Q1_Q1RQ1cp+02[Rsp+02ZS1_P|PzP2Q1QPrPuQ1MPYQ1qQ1mp+02RRQQ2;Q18Q1gQ2<Q1`P1Q17Q00Q09Q1BQ1:MO1Q1D%;wRvQ1~PeQ0=PfF3PwP]P^P_P`PaPWPsQ1_PUPSPcPdPPPLP3P>Q1qQ1mPQQ2;Q18Q1gQ2<Q1`P1Q17P?P:P;P8MO1P7PvQ1~PeP5PfF3PjP~P5P~P5PkPlP5PMPDPNPOQ20PmD6P<P5PKQ1sP0Q1sP0Q1lP<C2Q26P7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDEQ1YPEp+02^RvP]P^P_Q1oQ1kQ1]Q1_p+02YRwPXQ1YPHPqQ1NQ1OPgQ13Q1mPQQ2;Q18Q1gQ2<Q1`P1Q17Q1WQ1CQ1@Q0;Q0<MO1Q1H%;vS2?P~PeQ0>PfF3PvP]P^P_Q1oPaPWQ1_PwPUPSPcPdPPPLP3P>Q1mPQQ2;Q18Q1gQ2<Q1`P1Q17Q1WP?P:P;P8MO1P7Q2?P~PeP5PfF3PjQ0:P5Q0:P5PkPlP5PMPDPNPOQ1sPmD6P<P5PKP0Q1yP0Q1yQ0dP<C2Q1~P7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBEPHPEp+02]RvP]P^P_Q1nQ1^Q1XPwQ1rQ1aQ1[PZPxQ1PPAQ0JP}PQQ2;Q18Q1gQ2<Q1`P1Q17Q1WQ25P[Q0KQ15PbMO1Q1;%;vS2?Q0:PeQ0?PfF3PvP]P^P_Q1nQ1^PWPwQ1rPUPSPcPdPPPLP3P>PQQ2;Q18Q1gQ2<Q1`P1Q17Q1WQ25P?P:P;P8MO1P7Q2?Q0:PeP5PfF3PjQ20P5Q20P5PkPlP5PMPDPNPOP0PmD6P<P5PKQ1yQ1lQ1yQ1lQ1\P<C2P~P7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAEPqPEQ2=Q01P]P^P_Q1bQ1ZQ1UQ1rQ1dPUPSPcPdPPPLP3P>Q2;Q18Q1gQ2<Q1`P1Q17Q1WQ25P4P?P:P;P8MO1P7Q1<Q20PeP5PfF3Q2>3WX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?EQ1NPEPsP]P^P_Q1RQ1cP|Q1dp+02VRvPzP2Q1QPrPuQ1MPYQ00Q18Q1gQ2<Q1`P1Q17Q1WQ25P4Q0eQ09Q1BQ1:Q1DMO1Q0=%;sS2>Q1sPeQ0APfF3PsP]P^P_Q1RQ1cP|Q1dPvPzPSPcPdPPPLP3P>Q18Q1gQ2<Q1`P1Q17Q1WQ25P4Q0eP?P:P;P8MO1P7Q2>Q1sPeP5PfF3PjP0P5P0P5PkPlP5PMPDPNPOQ1lPmD6P<P5PKQ0dQ1\Q0dQ1\Q1|P<C2Q20P7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>EQ1OPEQ1_P]P^P_Q1kQ1]PXPvp+02URsQ1YPHPqQ1NQ1OPgQ13Q1CQ1gQ2<Q1`P1Q17Q1WQ25P4Q0eQ26Q1@Q0;Q0<Q1HMO1Q0>Q1_#;S2>P0PeQ0BPfF3Q1_P]P^P_Q1kQ1]PXPvPsQ1YPHPcPdPPPLP3P>Q1gQ2<Q1`P1Q17Q1WQ25P4Q0eQ26P?P:P;P8MO1P7Q2>P0PeP5PfF3PjQ1yP5Q1yP5PkPlP5PMPDPNPOQ0dPmD6P<P5PKQ1\Q1vQ1\Q1vQ1zP<C2Q1sP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=EPgPEPwP]P^P_Q1^Q1XQ1aPsQ1qQ1[PZPxQ1PPAQ0JP}P[Q2<Q1`P1Q17Q1WQ25P4Q0eQ26Q1~Q0KQ15PbQ1;MO1Q0?%;wS2>Q1yPeQ0CPfF3PwP]P^P_Q1^Q1XQ1aPsQ1qQ1[PZPxPdPPPLP3P>Q2<Q1`P1Q17Q1WQ25P4Q0eQ26Q1~P?P:P;P8MO1P7Q2>Q1yPeP5PfF3PjQ1lP5Q1lP5PkPlP5PMPDPNPOQ1\PmD6P<P5PKQ1vQ1|Q1vQ1|Q1jP<C2P0P7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;EQ13PEQ1}Q1rP]P^P_Q1ZQ1UQ1VQ1qQ1mPCPRPyPFPPPLP3P>Q1`P1Q17Q1WQ25P4Q0eQ26Q1~P~P?P:P;P8MO1P7Q1TQ1lPeP5PfF3Q2:3WX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:EQ1CPEQ1dP]P^P_Q1cP|PzQ1mPQP2Q1QPrPuQ1MPYQ00Q09P1Q17Q1WQ25P4Q0eQ26Q1~P~Q0:Q1BQ1:Q1DQ0=MO1Q0AQ1d#;RwQ0dPeQ0EPfF3Q1dP]P^P_Q1cP|PzQ1mPQP2Q1QPrPuQ1MPLP3P>P1Q17Q1WQ25P4Q0eQ26Q1~P~Q0:P?P:P;P8MO1P7PwQ0dPeP5PfF3PjQ1\P5Q1\P5PkPlP5PMPDPNPOQ1|PmD6P<P5PKQ1zQ1jQ1zQ1jQ1{P<C2Q1lP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9EQ1@PEPvP]P^P_Q1]PXQ1YPQQ2;PHPqQ1NQ1OPgQ13Q1CQ1@Q17Q1WQ25P4Q0eQ26Q1~P~Q0:Q20Q0;Q0<Q1HQ0>MO1Q0B%;vRwQ1\PeQ0FPfF3PvP]P^P_Q1]PXQ1YPQQ2;PHPqQ1NQ1OPgQ13P3P>Q17Q1WQ25P4Q0eQ26Q1~P~Q0:Q20P?P:P;P8MO1P7PwQ1\PeP5PfF3PjQ1vP5Q1vP5PkPlP5PMPDPNPOQ1zPmD6P<P5PKQ1jQ1SQ1jQ1SQ1wP<C2Q0dP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8EQ0;PEPsP]P^P_Q1XQ1aQ1[Q2;Q18PZPxQ1PPAQ0JP}P[Q0KQ1WQ25P4Q0eQ26Q1~P~Q0:Q20Q1sQ15PbQ1;Q0?MO1Q0C%;sRwQ1vPeQ0SPfF3PsP]P^P_Q1XQ1aQ1[Q2;Q18PZPxQ1PPAQ0JP}P[P>Q1WQ25P4Q0eQ26Q1~P~Q0:Q20Q1sP?P:P;P8MO1P7PwQ1vPeP5PfF3PjQ1|P5Q1|P5PkPlP5PMPDPNPOQ1jPmD6P<P5PKQ1SQ1{Q1SQ1{Q1fP<C2Q1\P7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7EQ0<PEQ28Q1qP]P^P_Q1UQ1VPCQ18Q1gPRPyPFPiPJP@Q1GQ19Q25P4Q0eQ26Q1~P~Q0:Q20Q1sP0P?P:P;P8MO1P7Q27Q1|PeP5PfF3Q293WX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6EQ1HPEQ1mP]P^P_P|PzP2Q1gQ2<Q1QPrPuQ1MPYQ00Q09Q1BP4Q0eQ26Q1~P~Q0:Q20Q1sP0Q1yQ1:Q1DQ0=Q0AMO1Q0EQ1m#;R@Q1zPeQ0UPfF3Q1mP]P^P_P|PzP2Q1gQ2<Q1QPrPuQ1MPYQ00Q09Q1BP4Q0eQ26Q1~P~Q0:Q20Q1sP0Q1yQ1:P:P;P8MO1P7P@Q1zPeP5PfF3PjQ1jP5Q1jP5PkPlP5PMPDPNPOQ1{PmD6P<P5PKQ1wQ1fQ1wQ1fQ1xP<C2Q1|P7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5EQ0>PEPQP]P^P_PXQ1YPHQ2<Q1`PqQ1NQ1OPgQ13Q1CQ1@Q0;Q0eQ26Q1~P~Q0:Q20Q1sP0Q1yQ1lQ0<Q1HQ0>Q0BMO1Q0F%;QR@Q1jPeQ0XPfF3PQP]P^P_PXQ1YPHQ2<Q1`PqQ1NQ1OPgQ13Q1CQ1@Q0;Q0eQ26Q1~P~Q0:Q20Q1sP0Q1yQ1lQ0<Q1HP;P8MO1P7P@Q1jPeP5PfF3PjQ1SP5Q1SP5PkPlP5PMPDPNPOQ1wPmD6P<P5PKQ1fQ1iQ1fQ1iQ1tP<C2Q1zP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4EQ0BPEQ2;P]P^P_Q1aQ1[PZQ1`P1PxQ1PPAQ0JP}P[Q0KQ15Q26Q1~P~Q0:Q20Q1sP0Q1yQ1lQ0dPbQ1;Q0?Q0CMO1Q0SQ2;#;R@Q1SPeQ0QPfF3Q2;P]P^P_Q1aQ1[PZQ1`P1PxQ1PPAQ0JP}P[Q0KQ15Q26Q1~P~Q0:Q20Q1sP0Q1yQ1lQ0dPbQ1;Q0?P8MO1P7P@Q1SPeP5PfF3PjQ1{P5Q1{P5PkPlP5PMPDPNPOQ1fPmD6P<P5PKQ1iQ1xQ1iQ1xQ1pP<C2Q1jP7F=D5D7E8X0B,0BX2G,0GX3EQ0FPGQ23Q21P7Q22Q1{PeP5PfF3Q243WX0B,0BX2GQ0XPBQ1gP]P^P_PzP2Q1QQ17Q1WPrPuQ1MPYQ00Q09Q1BQ1:P~Q0:Q20Q1sP0Q1yQ1lQ0dQ1\Q1vQ1DQ0=Q0AQ0EMO1R~Q0UQ1g#;RYQ1wPeQ0LPfF3P~Q0UPYQ1wPeP5PfF3PjQ1fP5Q1fP5PkPlP5PMPDPNPOQ1xPmD6P<P5PKQ1tQ1pQ1tQ1pQ1uP<C2Q1{Q0UF=D5D7E8X0BPnQ2<P]P^P_Q1YPHPqQ1WQ25Q1NQ1OPgQ13Q1CQ1@Q0;Q0<Q0:Q20Q1sP0Q1yQ1lQ0dQ1\Q1vQ1|Q1HQ0>Q0BQ0FMO1Q0XQ2<Q1fPePnPfF:R001:0Q1i=LjnRgQ1i/InRq%UnRHACnVIRYPnPMPDPNPOQ1tPmP<GRR~PnPKQ1pQ1eQ1pQ1eQ1hP<GZRuQ1wQ0X+0>Rr'4R2'4Rz'4R@'4R['4R}'4Q02/r0PgP}Q0[PqP[Q0^PHP@P\PYPzP9PnPVPhPIP9PjQ1iPnPVPhQ1RQ0[Q0^Q1t$03RzQ0g'vQ1t#hQ0h'TRYPzQ1IQ1tO1Q1JQ1IQ1tQ1tQ1t,r6I0RQ0gQ0hQ1KJ0QQ1]H0PRzPYQ0iQ0jQ0kQ0lQ1f-0O=R@Q1f,T=Q1f#hRHQ1f'g'4Q1f/9=AA6H='4'QRHQ1w#hR=P6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wQ0xQ1?7X7Q0yPTPTQ0zQ08'tQ0|Q10=~6t,OtRtQ105BTQ1E5fTQ089BTt206T>5fTQ0~9BTtQ1>5fTPTQ03Q04Q04Q05I195aT5aT5aTDsQ11Q12bXbYbZXI6XL6Xc6X\{Xk{Xl{1978Q14/\7,?7RTQ14'9/Q:19T;/Q?Q1L,9T/Q>Q0oH18[^I6^L6^c6^\{^k{^l{P5Q0I/9VQ0H/9V19IVPMQ07PVQ0cO7bWbRbSbTb`bbb^bVbUb_1\hV:17jVeN:15PUPzPYQ0iQ0jQ0kQ0lP@PHP=P6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ16bRbSbTb`bbb^bVbUb_L13P~P2PPPuPrP?P5CeCeCeCeCeCeCeH0IF`F`F`F`F`F`F`F`WzY09P7P5O2n2001000010121000000WGWuP7P5O2n2001000010121000000WGWsP7P5O2n2001000010121000000WGY04P7P5O2n2001000010121000000WGW~P7P5O2n2001000010121000000WGY0;P7P5O2n2001000010121000000WGY01P7P5O2n2001000010121000000WGPJP5J0BWGP7P5O2n2011000010121000000WGX0BP7P5O2n2011000010121100000WGX2GP7P5O2n2011000010121100000WGX3EP7P5O2n2011000010121100000WGX4EP7P5O2n2011000010121100000WGX5EP7P5O2n2011000010121100000WGX6EP7P5O2n2011000010121100000WGX7EP7P5O2n2011000010121100000WGX8EP7P5O2n2011000010121100000WGX9EP7P5O2n2011000010121100000WGX:EP7P5O2n2011000010121100000WGX;EP7P5O2n2011000010121100000WGX=EP7P5O2n2011000010121100000WGX>EP7P5O2n2011000010121100000WGX?EP7P5O2n2011000010121100000WGXAEP7P5O2n2011000010121100000WGXBEP7P5O2n2011000010121100000WGXDEP7P5O2n2011000010121100000bgbgbgWgWeQ02Q0fQ0{PjQ0CP5Q06PkPlQ1A9[5MP5PKQ0}Q0AP7I0_DmDdX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0E[]eeJ0~b|bwbvbxY06Y05P7P5O2n2001000010121000000c0<Q0RQ0DP]P^P_Q0EQ0FQ0SQ0TQ0UQ1=Q0VQ0WQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZPoQ0[Q0\PpQ0]Q0^Q0_Q0`MO1Q0aQ0bP\PeP`PfF360A9ec0:Q02P\Q15P]P^P_P`PaPWPbQ1FPUPSPcPdPPPLP3P>Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0SP?P:P;P8MO1P7Q15Q0LPeP5PfF:PjPnP5PnP5PkPlP5PMPDPNPOQ0NPmD6P<P5PKQ0OQ0YQ0OQ0YQ0ZP<C2Q0GP7F=D5D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWeQ0EP]P^P_Q0FQ0SQ0TQ0UQ0XQ1=1NDSQ0WQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZPoQ0[Q0\PpQ0]Q0^Q0_Q0`Q0aMO1P\Q0bP`PePaPfF360A9eY07W}Y03WtW{Y02Y08WrP>P5DJWGZ0PEXiEZ0NEZ0O6X16Xo6Y0?Y0>W<X@EXCEXEEXFEZ0EEZ0DEZ0MEZ0LEZ0KEZ0JEZ0IEZ0HEZ0GEZ0FEXHEXJEXKEXMEXNEZ0CEZ0BEX]EXaEXdEY0Ao"). Qed.

  (* [comment removed for export] *)
  Lemma strnlen_callq : forall ra' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (P n : Z) (buf : list byte),
    stk usegs m lo (q + -544) ->
    bytes_at usegs m P buf ->
    memchr_ok P 0 n buf ->
    mem_inv usegs m ->
    (P + Z.of_nat (length buf) <= lo \/ q <= P)%Z -> (0 < P < 2^64)%Z -> (0 <= n < 2^64)%Z ->
    evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          Ft (ret_pc ra') fc None m' (seg_rom usegs)
                 /\ munch [(q + -544 - 32, q + -544)]%Z m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (q + -544)
                 /\ bytes_at usegs m' P buf)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x28fa8) fc None m (seg_rom usegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "p'0h02m'h13a1'h23t6'h33t5'h43t4'h53t3'h63a7'h73a6'h82t6h93a5'h:3a4'h;2t5h<3a3'h=3a2'h>2t4h?3t2'h@2t3hA3t1'hB2a7hC3t0'hD2a6hE2a5hF1HhG2a4hH2a3hI2a2hJ4__x1hK2t2hL1zhM2t1hN2t0hO7__arithhP4__ffhQ7__sat12hR7__sat13hS7__sat14hT7__sat15hU8__varmaphV5__withW4__x2hX4cstrhY3ms'hZ2Hah[2PSh\4__p1h]4__x3h^4__x4h_2BBh`3BUFha4BUF'hb2Eahc2Enhd2Eqhe2Fthf2Hnhg2MIhh3MI'hi2MUhj2OKhk1Phl2P0hm3SEPhn2STho3ST'hp2WMhq3bufhr2fchs1mht1nhu3ra'hv2s0hw2s1hx3s10hy3s11hz2s2h{2s3h|2s4h}2s5h~2s6i002s7i012s8i022s9i031xp%0p%1p&0p;1p;2p;4p;5p;3p;Gp;Op;7p;6p;[p;Hp;8p103o^p6051002p104e@p4p710p8g007ej1>Tg008Jj1XTg008hj1oTg00U>j1LTg004?k20ITg00>Ak10ETg007Ej1yTg01ACk10:Tg00dZj2CTg05GQj4qTg00:lj2JTg00N^j1KTg00A_j2;Tg00QIj2YTg013Gj1QTg01e2j2xTg00C3j2OTg00COS00j29Tg05HMk50=Tg00PBj1\Tg01mBj2sTg01mjj3rTg00Qcj1pTg00RBj2`Tg00Rkj3aTg00STj2|Tg00Emj1}Tg00T@j3^Tg00FMj2]Tg01Bkk102Tg00T`j4hTg00Fkk10KTg00GIk10JTg00H4j2gTg00HWj2UTg01eok301Tg00Iek100Tg01Clj3ZTg01CIj3cTg00JGk20HTg00@Gj2~Tg00Jik20GTg00;Lj3PTg00KUk30FTg00L4k40DTg01?fj2HTg027Qj2mTg009Kj2?Tg026gj2FTg05IHmG0CmH0>Tg058GlO1Tg0599k10BTg03JKk20ATg03S8j4wTg0158R0j20Tg05:2j73Tg00X<k60@Tg05JIm[0?Tg05@4j17Tg04bfj3DTg002Tj6jTg01S>j4WTg04m>j4iTg0030j6tTg05Ckk609Tg05:dk308Tg05Daj4uTg00cej4dTg044]k207Tg00I:j4zTg00WXj7{Tg00X`k706Tg00YDk805Tg05KJk204Tg04cZj3nTg00Uck703Tf0R1#>#>p=[%L1#>p=T%>1#>#>#>p=Vg00j;S01f2R2f1R3P1Cup=@Q01P2P3P1Cdp=MQ010071p=Ag00[2R4/O1p=S1;41p==%L1#Lp=_g00;fR5P3g00_jP1Czp=fP3g00[PR6g00[oR7P7g00\OR8P1g00\oR9F{p=eP2P6P7P7P8P5P3g00`QP1CzP9F{p=BP2P6P7P7P8P3P1K06p=bf3R9P6P7P7P8P2P3P1L05p=E20431,?2p=2f6R:f5R;f4R<#7P9P2P3P1F3p=6Q01?n:;Q01P2P3P1Cd,99,9<'9p=4g04[FS02?P;<AD923/91'9p=5P5P<P9P2P3P1Etp=IP2P6P7P7P8P3P1K03p=vQ02f7R=P:P;P<P9P2P3P1F33Pp=lQ01?n31p=RQ01P9P2P3Cu/91p=k1931,92p=GQ01P2P3P1Cd,99,9<p=:Q02?P23/91p=8Q01P2P3P1Cd,99p>0<AD;<9Q01?n23/91'9p=<Q02?P31p>0;P:P;P<P9P2P3P1CiCip=Ng00<DR>#>R?#>S03#>R@#[RA#>RB#XRC#oRD%L?RE#X00ID%XA#o%X@#oRF$0E\DRG%yFp,2loRHp,1qRI%T@#V$0:R@'CRJ5@9AM<93P<P4P9P2Cq%A:1JF<#K,C:/;H1;I:'Y%S=%Q?RK%QBRB'xRL,O=RM'9%==/9MQ01f:RMf9RNP=P;I0=%=N1JF=#K,CN/;L'9f8RO,JFRP#\%KP#=%LE#_RP#QRQ,sKRR%SKRS%=Q1xKQRT#S[[RU%=KRVg01WWRWArKQ3UWZRQ%=T\W^ZVRX1sKBRY%=B%SL[\SRSArKB3VWXZVRB%=L\W^ZVRVg00_>RWg00b3RZ#pR[#pS04,`5S051`5[S061`5Z5a55a5g00bRS07'|%}WRZ3^%yWR[P51]52P3&025S08ChS09&0K5R\&0J5R]1g5>R^1U5KRK%XP6015'f,e]&007RPP]%>>#_#T#L#V#V#V#QR_,U51g5?R?5B]PPP]%>E#[#L#[#V#QRE,U5S0:9Z5^9B]?PP1U54R`1U5@S0;9c5^Ra5B]B015KCRK,fa,e]5b]CECECE20H]8RaP1P2g00^^Rbg00a8Rc'~20G12=PbcdB0F543H0DRcbPbUbVXJ5XW51O1T1;_21H2E,;91C9@R_#=1O_L'9[[[^J5^W5P1PHPIp,3QHIp,3GLOp,2LOS0<O5bObQbRbSbTbX,mJ1?CJR_,FCS0==P5Jf;RT1JFNRb#\%Kb#=PRPUPQPXPYPSPBPVPZP[1]53S0>P\P]1f`^,e]S0?1f^K,e]RK5b]PPAB]`^=b]KRKCEPaPcbPbUbVXJ5%S1S0@1O1LR`'9%=31O3L'9Rb[^J5P1fAS0APNO2RdbObQbRbSbTbX'm1?CT,FC=P5TRe1JFMRf#\%Kf#=PRPUPQPXPYPSPBPVPZP[Q0>P\P]PKPPPKCEPaPcbPbUbVXJ5%=1/9`Pb[^J5PdbObQbRbSbTbX,mTPeQ01fZReP_p,2gpRdp,2tpRbfVS0BfUS0CfNS0DfMS0EfLR`fKS0FfJS0GfIS0HfHS0IfGS0JfFS0KfES0Lf@RKf?Rff=Rg,?CRhf<Ri,?CRjPTPHf>RkNG0CQ02PffjRlP_PdPbPkPgPiffRmfeS0MQ0F92C`PTPMPNPOP=P:P;f^Rnf]Rof\Rpf[RqPefYRrfXRsfWS0NQ0BQ0CP<P9P2P3MO1fPRtPlfORu&00DRvP1Q01$0BRwF620A55RxP5P5%QARA,HJS0OPJCw%}xS0P3^RyQ0DP1Q0DP1%A1RzA@1HJR{P1Q0EQ0FF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DWYPeP_PdPbPrPsQ0NQ0BQ0CPhPjfTR|fSS0QfRS0RfQR}PtPuQ0DQ0EP`Q0FQ0GQ0HQ0IQ0JQ0KQ0LfDS0SfCS0TfBS0UQ0AMO1PK%>>#T#[#_#_#T#T#T#[#Q,?CS0VPfPvPkPwF3PeP_PdPbPrPsQ0NQ0BQ0CPhPjP|Q0QQ0RP}PtPuQ0DQ0EP`Q0FQ0GQ0HQ0IQ0JQ0KQ0LQ0SQ0TQ0UQ0APKPfPkPTPHPJA@fH1XL5PMQ0=P2DIPgAMf1iXL5PN1FChR~P3DIPgP1P4P~PiCqXL5PiPkP4P1PiCqXL5PO1FCjP1DIP~P3DIP=PJ1H1AS0W,;HXL51JFTRj#\S0X%Kj#=S0YPRPUPQPXPYPSPBPVPZP[Q09P\P]Q0:9Z5?9B]^PPQ0;9c5?1U5AS095Z59B]^CEPaPcbPbUbVXJ5XW51H3E,;11C2@/HA,;3[^J5^W5P1PIPHQ0<O3bObQbRbSbTbXQ0=P2DIPJ1?CkS0Z,FCRj1JFi#KR4'CQ0W';1;1j'YXL5Pg1C14Q0O';1;J1'YXL5Q0XQ0YPRPUPQPXPYPSPBPVQ04#p,`5Q05Q065a55a5Q07'|=^WZP[P5P51]5<P2Q08ChP31]59ChP\P]Ac5^?R?Q03,g5RW5B]%L>,g5R>=B]^5v]PPP]Q0:9Z5>9B]WPPQ0;9c5>R>Q095Z59B]?AB]>^5v]CECEPaPcbPbUbVXJ5XW5X]5X^51C13/;91;21'Y1H9E,;<1C291C<@R@/HA';1;@2'Y[[^J5^W5^]5^^5P1PHPIQ0A,JF#KQ0TPiQ0<O6bObQbRbSbTbXP~P3DIQ0=P2DIPgQ0@XL5Q0XQ0YPRPUPQPXPYPSPBPVp-0RVPZP[Q0>P\P]Q0?P]P6P7P7P8P9J0@5b]PPQ0?CEPaPcbPbUbVXJ5W\Q0@/93%S3[^J5^\VP1Q0T/OLQ0TPTO3bObQbRbSbTbXP~P3DIN[0?Q02PqP_PdPbQ0NQ0BPuQ0DQ0EP`Q0FQ0GQ0HQ0IQ0JQ0KQ0APKQ0ZPhPiPHPfP1NH0>S0ZP5Q0=Q0AflRhP_PdPbPkPgPifhR~fgRLQ0D,?C,FCRVQ0E52CPTPMPNPOP=P:P;f`Rcf_RaPnPoPpPqPePrPsQ0NP<P9P2P3MO1Q0R%7hP}PvP1PwGlRPP5P51HfAPfCwQ0P5^x?Dt11Rt1RxP1PHPf1?Cu,FCRAQ0E5M1Ck7Gz3GX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DXL5P1PJP<EjfkR]P_PdPbPkPgPiPLPmQ0E,?C,FC=2C`PTPMPNPOP=P:P;PaPnPoPpPqPePrPsQ0NQ0BP<P9P2P3MO1P}%7]S0PPtPvP1PwF3ADyu1S0=1Ru1S0@PzP{P1PVP`D:3G58KX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DP51?CK,FCRVQ0UfmR8P_PdPbPkPgPifiR7P~Q0D92CAPTPMPNPOP=P:P;faRAPcPaPnPoPpPqPePrPsP<P9P2P3MO1Q0Q%78R6Q0RPvP1PwF3ADy}1R\1R}1R[PzP{P1PfQ0DD:3G38X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DXL5P1PKP<EjADyt1P{P1PuQ0EH0<9Gxz5GPX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DP5PVQ0TfnRVP_PdPbPkPgPiPlP7A2CfuPTPMPNPOP=P:P;fbS0?PAPcPaPnPoPpPqPePrP<P9P2P3MO1P|%7VRPQ0QPvP1PwF3PyQ0RP1Q0RP1PzP{P1P}PuD:E<Rx38X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DXL5P1PKP<EjQ0UP8P_PdPbPkPgPiP7P~Q0D92CuPTPMPNPOP=P:P;PAPcPaPnPoPpPqPePrPsP<P9P2P3MO1Q0QP6Q0RPvP1PwF3PzP{P1PtQ0DD:9G\[38X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DP0PDQ0TPVP_PdPbPkPgPiPlP7A2CtuPTPMPNPOP=P:P;Q0?PAPcPaPnPoPpPqPePrP<P9P2P3MO1P|PPQ0QPvP1PwF3;8xX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXNDQ0SfoRxP_PdPbPkPgPiP]PlA2C}tPTPMPNPOP=P:P;fcS0>Q0?PAPcPaPnPoPpPqPeP<P9P2P3MO1Q0CPxP|PvP1PwF6PyQ0QP1Q0QP1PzP{P1Q0RPtF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0LfpRPP_PdPbPkPgPiPhP]Q0R=2C}PTPMPNPOP=P:P;fdR[Q0>Q0?PAPcPaPnPoPpPqP<P9P2P3MO1Q0BPPQ0CPvP1PwF6PyP|P1P|P1PzP{P1Q0QP}F4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DP0PDQ0KfqS0YP_PdPbPfPgPiP8PhQ0QQ0R52CPTPMPNPOP=P:P;Q0MP[Q0>Q0?PAPcPaPnPoPpP<P9P2P3MO1Q0NQ0YQ0BPvP1PwF6PyQ0CP1Q0CP1PzP{P1P|Q0RF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMDQ0IfsR\P_PdPbPkPgPiPxPVQ0C=2C|R6PTPMPNPOP=P:P;PLPmQ0MP[Q0>Q0?PAPcPaPnP<P9P2P3MO1Pr%7\RZPsPvP1PwF3PyQ0NP1Q0NP1PzP{P1Q0BP|D:E<RB38X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0IP\P_PdPbQ0APgPiPxPVP6PTPMPNPOP=P:P;PLPmQ0MP[Q0>Q0?PAPcPaPnP<P9P2P3MO1PrPZPsPvP1PwF3;8BX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DP0PDQ0HftRBP_PdPbQ0UPkPiPPPxQ0BQ0C52CPTPMPNPOP=P:P;P~PLPmQ0MP[Q0>Q0?PAPcPaP<P9P2P3MO1PePBPrPvP1PwF6PyPsP1PsP1PzP{P1Q0NQ0CF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKDfwRZP_PdPbPkPgPiP\frR6A2CrsRSPTPMPNPOP=P:P;P]PlP7P~PLPmQ0MP[Q0>Q0?P<P9P2P3MO1Po%7ZRYPpPvP1PwF3PyPqP1PqP1PzP{P1PePsD:E<RX58`X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0FfvRQP_PdPbQ0SPKPiP6Q0YQ0N92CsPTPMPNPOP=P:P;PlP7P~PLPmQ0MP[Q0>Q0?PAP<P9P2P3MO1PpPQPqPvP1PwF6PyPeP1PeP1PzP{P1PrQ0NF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DP0PDPZP_PdPbQ0LQ0APgP\P6PSPTPMPNPOP=P:P;P]PlP7P~PLPmQ0MP[Q0>Q0?P<P9P2P3MO1PoPYPpPvP1PwF3=8`XX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1DPtf{RXP_PdPbPkPgPiPZPQA2CopPTPMPNPOP=P:P;PxPVP8PhP]PlP7P~PLPmP<P9P2P3MO1PAPXPcPvP1PwF6PyPaP1PaP1PzP{P1PnPpF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0DfyRYP_PdPbQ0JQ0TPffuRSPBA2CqePTPMPNPOP=P:P;P8PhP]PlP7P~PLPmQ0MP[P<P9P2P3MO1PaPYPnPvP1PwF6PyPoP1PoP1PzP{P1PpPeF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DP0PDPufzRUP_PdPbQ0IQ0SPKPQPSA2CpqPiPMPNPOP=P:P;PVP8PhP]PlP7P~PLPmQ0MP<P9P2P3MO1PcPUPaPvP1PwF6PyPnP1PnP1PzP{P1PoPqF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXIDp+01@RRP_PdPbPkPgPiPXPUA2CAcRFPTPMPNPOP=P:P;P\P6Q0YPPPxPVP8PhP]PlP<P9P2P3MO1Q0M%7RRIP[PvP1PwF3PyQ0>P1Q0>P1PzP{P1Q0?PcD:E<R@58|X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1P}f|REP_PdPbQ0GQ0KQ0UfxR>PZA2CnoPkPMPNPOP=P:P;PPPxPVP8PhP]PlP7P~PLP<P9P2P3MO1Q0?PEPAPvP1PwF6PyPcP1PcP1PzP{P1PaPoF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DP0PDQ0Rf}R^P_PdPbQ0FQ0JQ0TPYP>A2CanPfPTPNPOP=P:P;Q0YPPPxPVP8PhP]PlP7P~P<P9P2P3MO1Q0>P^Q0?PvP1PwF6PyPAP1PAP1PzP{P1PcPnF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHDp+01DR?P_PdPbPkPgPiPRf~RWQ0M=2C[S0XPTPMPNPOP=P:P;PZPQPSPBP\P6Q0YPPPxPVP<P9P2P3MO1P7%7?R4P~PvP1PwF3PyPLP1PLP1PzP{P1PmP[D:E<Rj58sX0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1PRP_PdPbQ0EQ0HQ0LPXPUPFQ0APgPNPOP=P:P;P\P6Q0YPPPxPVP8PhP]PlP<P9P2P3MO1Q0MPIP[PvP1PwF3=8|@X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DP0PDQ0Cp+01AR@P_PdPbQ0DQ0GQ0KPEPXQ0?=2CAQ0UPkPMPOP=P:P;PBP\P6Q0YPPPxPVP8PhP]P<P9P2P3MO1PmP@Q0MPvP1PwF6PyP[P1P[P1PzP{P1Q0>PAF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGDPpp+01HS0<P_PdPbPkPgPiP?p+01CS09A2C7~PTPMPNPOP=P:P;PXPUPYP>PZPQPSPBP\P6P<P9P2P3MO1P8Q0<PhPvP1PwF6PyP]P1P]P1PzP{P1PlP~F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0NQ09P_PdPbPtP`Q0IPWP^Q0>92C[Q0SPKPiPOP=P:P;PQPSPBP\P6Q0YPPPxPVP8P<P9P2P3MO1P~Q09PLPvP1PwF6PyPmP1PmP1PzP{P1Q0MQ0>F4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DP0PDP?P_PdPbP}Q0EQ0HPRPWQ0XQ0LQ0APgPNP=P:P;PZPQPSPBP\P6Q0YPPPxPVP<P9P2P3MO1P7P4P~PvP1PwF3=8sjX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXEDp+01LS0XP_PdPbPkPgPiQ0<p+01GS0;A2C8hRjPTPMPNPOP=P:P;PRPWP^PEPXPUPYP>PZPQP<P9P2P3MO1Q0YQ0X#7R4PPPvP1PwF3PyPxP1PxP1PzP{P1PVPhD:E<RI58cX0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Pep+01FS0:P_PdPbQ0QPuQ0Fp+01BS03P@A2CLmQ0JQ0TPfPTP=P:P;PYP>PZPQPSPBP\P6Q0YPPP<P9P2P3MO1P]Q0:PlPvP1PwF6PyP7P1P7P1PzP{P1P~PmF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DP0PDPqQ0;P_PdPbP|PtP`Q09Q03A2C~LQ0IQ0SPKPiPOP:P;PUPYP>PZPQPSPBP\P6Q0YP<P9P2P3MO1PhQ0;P]PvP1PwF6PyPlP1PlP1PzP{P1P7PLF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDDp+01PS08P_PdPbPkPgPiQ0Xp+01KS07Q0Y=2CPS06PTPMPNPOP=P:P;P?Q09Q03P@PRPWP^PEPXPUP<P9P2P3MO1PSQ08#7S05PBPvP1PwF3PyP\P1P\P1PzP{P1P6PPD:E<RF58[X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Pop+01IS04P_PdPbQ0BQ0RQ0Dp+01ES0OP?A2Cl7Q0GQ0KQ0UPkPMP:P;PEPXPUPYP>PZPQPSPBP\P<P9P2P3MO1PVQ04P8PvP1PwF6PyPhP1PhP1PzP{P1P]P7F4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DP0PDPnp+01JS0WP_PdPbQ0NQ0QPuQ0:Q0OA2C]lQ0FQ0JQ0TPfPTP=P;P^PEPXPUPYP>PZPQPSPBP<P9P2P3MO1PxQ0WPVPvP1PwF6PyP8P1P8P1PzP{P1PhPlF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBDP~p+01TS0[P_PdPbPkPgPiQ08p+01OS0\A2CSBPTPMPNPOP=P:P;Q0<Q0;Q0:Q0OP?Q09Q03P@PRPWP<P9P2P3MO1PYQ0[P>PvP1PwF6PyPZP1PZP1PzP{P1PQPBF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0XP_PdPbPrQ0CP}Q0<Q0;PjQ0EQ0HQ0LQ0APgPNP;PRPWP^PEPXPUPYP>PZPQP<P9P2P3MO1Q0YP4PPPvP1PwF3=8cIX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DP0PDPAp+01MS0]P_PdPbPeQ0BQ0RQ04Q0<A2CV8Q0DQ0GQ0KQ0UPkPMP:P@PRPWP^PEPXPUPYP>PZP<P9P2P3MO1P6Q0]Q0YPvP1PwF6PyPPP1PPP1PzP{P1PxP8F4E5X0G,0GX8D,0DX;D,0DX>D,0DX@Dp+01XS0^P_PdPbPkPgPiQ0[p+01SS0_A2CY>S0`PTPMPNPOP=P:P;Q0XQ07Q0WQ04Q0<Q0;Q0:Q0OP?Q09P<P9P2P3MO1P^Q0^#7S0aPEPvP1PwF3PyPXP1PXP1PzP{P1PUP>D:E<RI58hX0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0>Q0\P_PdPbPpPsP|Q07Q0WA2CPxPtP`Q0IQ0SPKPiPOQ09Q03P@PRPWP^PEPXPUPYP<P9P2P3MO1PBQ0\P\PvP1PwF6PyP6P1P6P1PzP{P1Q0YPxF4E5X0G,0GX8D,0DX;D,0DX>D,0DP0PDQ08P_PdPbPoPrQ0CQ0XQ07Q06P}Q0EQ0HQ0LQ0APgPNP?Q09Q03P@PRPWP^PEPXPUP;P9P2P3MO1PSQ05PBPvP1PwF3=8[FX0G,0GX8D,0DX;D,0DX>DPPp+01\S05P_PdPbPkPgPiQ0^p+01WS06A2C^ES0bPTPMPNPOP=P:P;Q08Q0\p+01NS0cQ0]Q0XQ07Q0WQ04Q0<Q0;P<P9P2P3MO1Q03Q05#7S0dP@PvP1PwF3PyPRP1PRP1PzP{P1PWPEF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Pmp+01RS0eP_PdPbPaPqQ0NQ0cQ0]A2C\6Q0QPuQ0FQ0JQ0TPfPTQ0:Q0OP?Q09Q03P@PRPWP^PEP=P9P2P3MO1PZQ0ePQPvP1PwF6PyPSP1PSP1PzP{P1PBP6F4E5X0G,0GX8D,0DX;D,0DP0PDPLQ0_P_PdPbPcPpPsQ0\Q0cA2CB\P|PtP`Q0IQ0SPKPiQ0;Q0:Q0OP?Q09Q03P@PRPWP^POP<P2P3MO1P>Q0_PZPvP1PwF6PyPQP1PQP1PzP{P1PSP\F4E5X0G,0GX8D,0DX;DPBp+01`RFP_PdPbPkPgPiQ05p+01[S0fQ03=2C@PTPMPNPOP=P:P;Q0[Q0_Q0ep+01QS0gQ08Q0\Q0cQ0]Q0XQ07P<P9P2P3MO1Q0:PFQ0OPvP1PwF6PyP?P1P?P1PzP{P1Q09P@F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1P7p+01US0hP_PdPbQ0?PnPeQ0gQ08A2CQSQ0BQ0RQ0DQ0GQ0KQ0UPkQ04Q0<Q0;Q0:Q0OP?Q09Q03P@PRPMP:P2P3MO1PUQ0hPYPvP1PwF6PyP>P1P>P1PzP{P1PZPSF4E5X0G,0GX8D,0DP0PDPlp+01VS0iP_PdPbQ0>PaPqQ0eQ0gA2CZQQ0NQ0QPuQ0FQ0JQ0TPfQ0WQ04Q0<Q0;Q0:Q0OP?Q09Q03P@PTP=P9P3MO1PXQ0iPUPvP1PwF6PyPYP1PYP1PzP{P1P>PQF4E5X0G,0GX8DP>p+01dR4P_PdPbPkPgPiPFp+01_RjQ0:Q0O52CPTPMPNPOP=P:P;Q0^Q06Q0iQ0hQ0[Q0_Q0eQ0gQ08Q0\P<P9P2P3MO1Q0WP4Q04PvP1PwF6PyQ0<P1Q0<P1PzP{P1Q0;Q0OF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0^P_PdPbQ0MPAPoQ0[Q0_Q0`PrQ0CP}Q0EQ0HQ0LQ0AQ0XQ07Q0WQ04Q0<Q0;Q0:Q0OP?Q09PgPNP;P3MO1P^Q0aPEPvP1PwF3=8hIX0G,0GP0PGP8p+01YS0aP_PdPbPmQ0?PnQ0hQ0[A2CUYPeQ0BQ0RQ0DQ0GQ0KQ0UQ0]Q0XQ07Q0WQ04Q0<Q0;Q0:Q0OP?PkPMP:P2MO1PWQ0aP^PvP1PwF6PyPEP1PEP1PzP{P1PXPYF4E5X0GPEp+01hR0P_PdPbPkPgPiP4p+01cRIQ0WQ0452CPTPMPNPOP=P:P;Q05Q0fp+01ZS0`Q0aQ0^Q06Q0iQ0hQ0[Q0_P<P9P2P3MO1Q0cP0Q0]PvP1PwF6PyQ0XP1Q0XP1PzP{P1Q07Q04F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1PxQ0fP_PdPbP~P[PcQ06Q0iA2CEXPpPsP|PtP`Q0IQ0SQ0\Q0cQ0]Q0XQ07Q0WQ04Q0<Q0;Q0:PKPiPOP<MO1P@Q0fPRPvP1PwF6PyPWP1PWP1PzP{P1P^PXF4E5Q00PPQ05P_PdPbP7Q0MPAQ0^Q06Q0bPoPrQ0CP}Q0EQ0HQ0LQ08Q0\Q0cQ0]Q0XQ07Q0WQ04Q0<Q0;Q0APgPNP;MO1Q03Q0dP@PvP3PwGlPyPRP3PRP3%A3A@3HJP3PWPED:E<P@p+01lS0dP_PdPbPkPgPiP0p+01gS0bQ0cQ0]52CPTPMPNPOP=P:P;PFPjp+01^S0jp+01]S0kQ05Q0fQ0`Q0aQ0^Q06P<P9P2P3MO1Q0eQ0dQ0gPvP1PwF6PyQ08P1Q08P1PzP{P1Q0\Q0]F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1P6Q0jP_PdPbP]PLQ0>Q0`Q0aA2CRWPaPqQ0NQ0QPuQ0FQ0JQ0eQ0gQ08Q0\Q0cQ0]Q0XQ07Q0WQ04Q0TPfPTP=MO1P?Q0j#7Q09PvP9PwGlQ02PjP_PdPbPhP~P[Q0fQ0`A2C@RPcPpPsP|PtP`Q0IQ0_Q0eQ0gQ08Q0\Q0cQ0]Q0XQ07Q0WQ0SPKPiPOMO1Q0OPjP?PvP<PwF6Q02ADy?;S0lP?P;%A;A@;HJP;Q09P@F4S0m'9p+020S0nP_PdPbPkPgPiQ0dp+01kS0oQ0eQ0g52CS0pPTPMPNPOP=P:P;P4PIp+01bS0qp+01aS0rPFPjQ0jQ0kQ05Q0fP<P9P2P3MO1Q0iQ0n#7S0sQ0hPvP1PwF3S0tPyQ0[P1Q0[P1PzP{P1Q0_Q0gD:E<S0u58KX0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0D[WYPyQ09P<Q09P<%A<A@<HJP<Q03PRD:E<Q00Q0lQ0mQ0nP_PdPbP^PYPSQ0dQ0oQ0pQ0YP8P7Q0MPAPoPrP4PIQ0qQ0rPFPjQ0jQ0kQ05Q0fQ0CP}Q0EQ0HMO1Q0iQ0sQ0hPvQ0LPwF3S0sQ0tQ0u38X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0:=Dy=Q0;PO%AOA@OHJPOQ0:P?F4Q00Q0</RN%ANA@NHJPNQ0;Q0OD:p+024S0uP_PdPbQ03P^PYQ0np+01oS0tQ0iQ0h52CS0pPSQ0YP8P7Q0MPAPoP0Q0bp+01fS0mp+01eS0lP4PIQ0qQ0rPFPjPrQ0CP}Q0EMO1Q0`Q0u#7S0vQ0aPvQ0HPwF3S0wQ0uP_PdPbPkPgPiQ0nQ0tQ0pPTPMPNPOP=P:P;P0Q0bQ0mQ0lP4PIQ0qQ0rPFPjP<P9P2P3MO1Q0`Q0vQ0aPvP1PwF3PyQ0^P1Q0^P1PzP{P1Q06Q0hD:E<S0x38X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0W/RT%AiA@iHJPiQ0WQ0<D:Q00%AgPgPHPJQ07Q045MgCkp+028S0yP_PdPbQ0:Q03P^Q0up+023S0zQ0`Q0a52CS0{PYPSQ0YP8P7Q0MPAQ0dQ0op+01jS0|p+01iS0}P0Q0bQ0mQ0lP4PIPoPrQ0CP}MO1Q0jQ0y#7S0~Q0kPvQ0EPwF3S10Q0yP_PdPbPkPgPiQ0uQ0zQ0{PTPMPNPOP=P:P;Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lP4PIP<P9P2P3MO1Q0jQ0~Q0kPvP1PwF3PyQ05P1Q05P1PzP{P1Q0fQ0aD:E<S1138X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1%AfPKPHPJQ0cQ0X5MKCkQ00Q0A?@HJQ0AQ0\Q0]3Mp+02<S0\P_PdPbQ0WQ0:Q03Q0yp+027S00Q0jQ0k52CS0cP^PYPSQ0YP8P7Q0MQ0nQ0tp+01nS12p+01mS13Q0dQ0oQ0|Q0}P0Q0bPAPoPrQ0CMO1Q0qQ0\#7S14Q0rPvP}PwF3S15Q0\P_PdPbPkPgPiQ0yQ00Q0cPTPMPNPOP=P:P;Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}P0Q0bP<P9P2P3MO1Q0qQ14Q0rPvP1PwF3PyPFP1PFP1PzP{P1PjQ0kD:E<S1638X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0T?@HJQ0SQ0eQ083MPDp+02?S08P_PdPbQ0]Q04Q0Op+02;S0]p+02:S17Q0r=2CFS18P@PEP>PBPPPhP~Q0zp+022S19p+021S1:Q0nQ0tQ12Q13Q0dQ0oQ0|P[PcPpPsMO1Q0lQ08#7S1;P4PvP|PwF3Q08P_PdPbPkPgPiQ0]Q17Q18PTPMPNPOP=P:P;Q0zQ19Q1:Q0nQ0tQ12Q13Q0dQ0oQ0|P<P9P2P3MO1Q0lQ1;P4PvP1PwF3PyPIP1PIP1PzP{P1Q0qPFF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCDP^PDp+02>S1;P_PdPbQ0XQ0<P?Q17p+029S18A2CFjS08PRPXPZP\PxP]PLQ19Q1:Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}Q0>PaPqQ0NMO1P4Q1;#7S1<PIPvQ0QPwF3Q1;P_PdPbQ0XPgPiQ17Q18Q08PTPMPNPOP=P:P;Q19Q1:Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}P<P9P2P3MO1P4Q1<PIPvP1PwF3PyQ0qP1Q0qP1PzP{P1Q0rPjF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXADPYPDp+02=S1<P_PdPbQ07Q0;Q09Q18Q0yQ0j92CjS08PWPUPQP6PVPlPmQ1:Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}P0Q0?PnPeQ0BMO1PIQ1<#7S0XQ0qPvQ0RPwF3Q1<P_PdPbQ07Q0;PiQ18Q0yQ08PTPMPNPOP=P:P;Q1:Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}P0P<P9P2P3MO1PIQ0XQ0qPvP1PwF3PyQ0rP1Q0rP1PzP{P1PFQ0jF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?DPSPDQ15Q0\P_PdPbQ0WQ0:Q03Q0yQ00Q0cPTPMPNPOP=P:P;Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}P0Q0bP<P9P2P3MO1Q0qQ14Q0rPvP1PwF3Q1638X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1DQ0YPDQ0]P_PdPbQ04Q0OP@Q00p+026S16Q0kQ0552CS15PEP>PBPPPhP~P[Q0tQ12Q13Q0dQ0oQ0|Q0}P0Q0bQ0mPcPpPsP|MO1Q0rQ0]#7S14PFPvPtPwF3Q0]P_PdPbQ04Q0OP@Q00Q16Q15PEPMPNPOP=P:P;Q0tQ12Q13Q0dQ0oQ0|Q0}P0Q0bQ0mP<P9P2P3MO1Q0rQ14PFPvP1PwF3PyPjP1PjP1PzP{P1Q0jQ05F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=DP8PDQ17P_PdPbQ0<P?PRQ16p+025S14Q05Q0f52CS15PXPZP\PxP]PLQ0>Q12Q13Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lPaPqQ0NQ0QMO1PFQ17#7S04PjPvPuPwF3Q17P_PdPbQ0<P?PRQ16Q14Q15PXPZPNPOP=P:P;Q12Q13Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lP<P9P2P3MO1PFQ04PjPvP1PwF3PyQ0jP1Q0jP1PzP{P1Q0kQ0fF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<DP7PDQ18P_PdPbQ0;Q09PWQ14Q0uQ0fQ0`52CS04PUPQP6PVPlPmQ0?Q13Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lP4PnPeQ0BQ0RMO1PjQ18#7S15Q0jPvQ0DPwF3Q18P_PdPbQ0;Q09PWQ14Q0uQ04PUPQP6POP=P:P;Q13Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lP4P<P9P2P3MO1PjQ15Q0jPvP1PwF3PyQ0kP1Q0kP1PzP{P1Q05Q0`F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:DQ0MPDQ10Q0yP_PdPbQ0:Q03P^Q0uQ0zQ0{PYPSQ0YP8P=P:P;Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lP4PIP<P9P2P3MO1Q0jQ0~Q0kPvP1PwF3Q1138X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9DPAPDQ00P_PdPbQ0OP@PEQ0zQ19Q0aQ0^52CS11P>PBPPPhP~P[PcQ0oQ0|Q0}P0Q0bQ0mQ0lP4PIQ0qPpPsP|PtMO1Q0kQ00#7S10Q05PvP`PwF3Q00P_PdPbQ0OP@PEQ0zQ19Q11P>PBPPPhP~P:P;Q0oQ0|Q0}P0Q0bQ0mQ0lP4PIQ0qP<P9P2P3MO1Q0kQ10Q05PvP1PwF3PyQ0fP1Q0fP1PzP{P1Q0`Q0^F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7DPoPDQ16P_PdPbP?PRPXQ19Q1:Q0^Q0652CS10PZP\PxP]PLQ0>PaQ0|Q0}P0Q0bQ0mQ0lP4PIQ0qQ0rPqQ0NQ0QPuMO1Q05Q16#7S0oQ0fPvQ0FPwF3Q16P_PdPbP?PRPXQ19Q1:Q10PZP\PxP]PLQ0>P;Q0|Q0}P0Q0bQ0mQ0lP4PIQ0qQ0rP<P9P2P3MO1Q05Q0oQ0fPvP1PwF3PyQ0`P1Q0`P1PzP{P1Q0aQ06F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6DPrPDQ14P_PdPbQ09PWPUQ1:Q0nQ06Q0i52CS0oPQP6PVPlPmQ0?PnQ0}P0Q0bQ0mQ0lP4PIQ0qQ0rPFPeQ0BQ0RQ0DMO1Q0fQ14#7R?Q0`PvQ0GPwF3Q14P_PdPbQ09PWPUQ1:Q0nQ0oPQP6PVPlPmQ0?PnQ0}P0Q0bQ0mQ0lP4PIQ0qQ0rPFP<P9P2P3MO1Q0fP?Q0`PvP1PwF3PyQ0aP1Q0aP1PzP{P1Q0^Q0iF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5DQ0CPDQ0wQ0uP_PdPbQ03P^PYQ0nQ0tQ0pPSQ0YP8P7Q0MPAPoP0Q0bQ0mQ0lP4PIQ0qQ0rPFPjPrP9P2P3MO1Q0`Q0vQ0aPvP1PwF3Q0x38X0G,0GX2D,0DX3D,0DX4DP}PDQ0zP_PdPbP@PEP>Q0tQ12Q0hQ0[52CR0PBPPPhP~P[PcPpQ0bQ0mQ0lP4PIQ0qQ0rPFPjQ0jPsP|PtP`MO1Q0aQ0z#7R7Q0^PvQ0IPwF3Q0zP_PdPbP@PEP>Q0tQ12P0PBPPPhP~P[PcPpQ0bQ0mQ0lP4PIQ0qQ0rPFPjQ0jPsP|P2P3MO1Q0aP7Q0^PvP1PwF3PyQ06P1Q06P1PzP{P1Q0iQ0[F4E5X0G,0GX2D,0DX3DQ0EPDQ19P_PdPbPRPXPZQ12Q13Q0[Q0_52CR7P\PxP]PLQ0>PaPqQ0mQ0lP4PIQ0qQ0rPFPjQ0jQ0kQ0NQ0QPuQ0FMO1Q0^Q19#7RcQ06PvQ0JPwF3Q19P_PdPbPRPXPZQ12Q13P7P\PxP]PLQ0>PaPqQ0mQ0lP4PIQ0qQ0rPFPjQ0jQ0kQ0NQ0QPuP3MO1Q0^PcQ06PvP1PwF3PyQ0iP1Q0iP1PzP{P1Q0hQ0_F4E5X0G,0GX2DQ0HPGQ1:P_PdPbPWPUPQQ13Q0dQ0_Q0e52CP6PVPlPmQ0?PnPeQ0lP4PIQ0qQ0rPFPjQ0jQ0kQ05Q0BQ0RQ0DQ0GMO1RjQ06Q1:#7RFQ0iPvQ0KPwF3PjQ06PFQ0iPvP1PwF3PyQ0hP1Q0hP1PzP{P1Q0[Q0eF4E5X0GQ0LQ0sQ0s+0;Q0[Q0L5DyRFQ0[Q0L'RRjQ0L#ARIQ0L?@HJRJQ0LQ0_Q0g3MRH'9R4'9Rl'9RV'9Q02Q0s'~PFPVPgPjPlPNPIP4P;PJPHP3P1CWCWCWCWCWCiFNFNFNFNFNFNFNWaWoP3P1O2n2001000010121000000WFWhP3P1O2n2001000010121000000WFWpP3P1O2n2001000010121000000WFWiP3P1O2n2001000010121000000WFP\P1EtWFP3P1O2n2001000010121000000WFX0GP3P1O2n2001000010121103000WFX2DP3P1O2n2011000010121103000WFX3DP3P1O2n2011000010121103000WFX4DP3P1O2n2011000010121103000WFX5DP3P1O2n2011000010121103000WFX6DP3P1O2n2011000010121103000WFX7DP3P1O2n2011000010121103000WFX9DP3P1O2n2011000010121103000WFX:DP3P1O2n2011000010121103000WFX<DP3P1O2n2011000010121103000WFX=DP3P1O2n2011000010121103000WFX1DP3P1O2n2011000010121103000WFX?DP3P1O2n2011000010121103000WFXADP3P1O2n2011000010121103000WFXCDP3P1O2n2011000010121103000b[b[b[W[WYQ02Q0ZP]P_PdPbPkPgPiPLPmQ0E=2C`PTPMPNPOP=P:P;PaPnPoPpPqPePrPsQ0NQ0BP<P9P2P3MO1P}Q0PPtPvP1PwF3Q0=Q0@PzP{P1Q0DP`D:3G58KX0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0D[]YeJ09bcbbbdb_Q01Q02PfPmP_PdPbPkPgPiQ0?PAQ0IQ0J52CPTPMPNPOP=P:P;PePrPsQ0NQ0BQ0CP|Q0QQ0RP}P<P9P2P3MO1P`PmQ0FPvP1PwF6PyQ0GP1Q0GP1PzP{P1Q0HQ0JF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DWYQ0BP_PdPbQ0CP|Q0QQ0RP}1?CN1?COPtPuQ0DQ0EP`Q0FQ0GQ0HQ0IQ0JQ0KQ0LQ0SQ0TQ0UQ0APKPfPkPgMO1PiQ0VPTPvPMPwF3408eWfWlWmWgWjW`WnWqXt5Xk5WsWrWeX8DX;DX>DX@DXyDXxDZ02DZ01DZ00DX~DX}DX|DX{DXzDXBDXDDXEDXGDXHDXIDXwDXvDXKDXMDXNDWuo"). Qed.

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
               Ft (ret_pc ra') fc None m' (seg_rom usegs)
      /\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (q + -544)
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ bytes_at usegs m' S (zb bs).
  Lemma out_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (S L : Z) (bs : list Z),
    SINK m st -> bytes_at usegs m S (zb bs) -> Forall (fun c => 0 <= c < 256)%Z bs -> L = zlength bs ->
    stk usegs m lo (q + -544) -> ssp_cells m canary -> mem_inv usegs m ->
    (0 <= S)%Z -> (S < 2^64)%Z ->
    (S + zlength bs <= lo \/ q + -544 <= S)%Z -> (S + zlength bs <= Fp \/ Fp + 232 <= S)%Z -> (S + zlength bs <= B \/ B + BS <= S)%Z ->
    (zlength bs < 2^31)%Z ->
    (S + zlength bs <= 2^47)%Z ->                                   (* [comment removed for export] *)
    implM usegs (OUT bs) st (out_postq ra' Ft fc s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S bs m)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) FPv a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x23a60) fc None m (seg_rom usegs)).
Proof using BS0 GLO HAP HOUT LO QHI SEP_B SEP_F TOK TQ fmt slots.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "p'0h04__x1h14__x2h27__arithh34__ffh47__sat48h57__sat49h67__sat50h77__sat51h87__sat52h97__sat53h:8__varmaph;5__with<4cstrh=5cstr0h>5cstr1h?2Hah@2HOhA4__p1hB4__p2hC4__x3hD4__x4hE2a3hF2a4hG2a5hH2a6hI2a7hJ3ms'hK2t0hL2t1hM2t2hN2t3hO2t4hP2t5hQ2t6hR1zhS1LhT1PhU2SBhV4__x5hW1ahX2a0hY2a1hZ2a2h[2m'h\2s'h]2D1h^2D2h_2D3h`2Eqha2Eshb2Fthc1Hhd2HShe3HS0hf3HS1hg2LBhh2MIhi3RNGhj1Shk3S47hl3SRChm3SSPhn2STho2bshp1chq2fchr1mhs1nht3ra'hu2s0hv2s1hw3s10hx3s11hy2s2hz2s3h{2s4h|2s5h}2s6h~2s7i002s8i012s9i022sti033st'i041up%0p%1p&0p;1p;2p;3p;Bp;Op;7p;5p;6p;4p;Lp;Ep;:p;8p,2StR0p4p300g05NJR1p4p710p8g007ej18Tg008Jj1^Tg008hj1nTg00U>j1QTg004?k20MTg00>Ak10ETg007Ej1yTg00:1j1HTg013Gj1STg00C3j24Tg00COj2:Tg00k0j3aTg00;Lj3?Tg01ACk10KTg00dZj29Tg05OLj2RTg01e2j2oTg05PKlBflEwTg009Kj21Tg058GlOBTg00Iej1}Tg0599k105Tg05:2j7ETg05HMk501Tg00:lj2\Tg00N^j1FTg04GIk10NTg002Tj6kTg00PBj1bTg01mBj2sTg01mjj3rTg00Qcj1jTg00RBj2`Tg00STj2iTg00Emk100Tg00T@j3OTg00FMj2_Tg01Bkk10LTg00Fkk10JTg00GIk10ITg00H4j2YTg01eoj3|Tg01Clj3qTg00HWj2zTg00JGk20CTg00@Gj2pTg00Jik20BTg00KUk30ATg00L4k40@Tg00A_j22Tg01?fj2VTg027Qj2xTg026gj2=TP1k70=Tg05QTlL[lOlTg00QIj2]Tg05@4j1vTg03JKk20<Tg04bfj3uTg04cZj3tTg0158j20Tg05RVm:0;Tg0030k60:Tg00cek409Tg00B;k208Tg05Dak407Tg044]k20>Tg04ZQk70?Tg00Rkk306Tg00T`k40DTg00I:j4{Tg00WXj7~Tg01CIk304Tg00X`k70FTg00YDk803Tg00X<k60GTg00Uck70HTg03S8k402Tf0R1#8#8p=3g00j;R2f2R3f1R4P1H09p=Ig00[2R5/21p=5g00;fR60081p=6%Q1#8p=CP2P3P4P1H07p=G20>21p=Tf3R7/231241']p=>%81#Qp=D%81#Sp=Jf4R8/97/231241']p=@%Q1#Qp=A1934/21p=;P8P2g00[oR9P7P3P4P1K0?p=K1\61p=cB06641p=PP6P3P4P1H0Dp=Z1z61p=NP6P4g00_jP1C{p=hP4g00[PR:P9P9g00\OR;P1g00\oS00F~p=gP3P:P9P9P;P6P4g00`QP1C{Q00F~p=7B04641p=MP3P:P9P9P;P4P1K0Fp=XP7P:P9P9P;P3P4P1L03p=<1\61#F,14p=L1241,]3p=UP4P:P9P9P;P1J0Gp=mP3P:P9P9P;P4P1K0Hp=dP6P6P4P1H02p=e1:41,:3p=Wg00<DR:#8R<#8S01#8S02#3R=#8R>#^R?#nR@%Q<RA#^00M@%^=#nQ02#^#nR=$0E\@S03%y6p,4SINKRBP8P7O2f5RC%H47I7%51%3>S04#S,41':Xp6S05=a63%679?68P6%68f9RDp,2loREp,1qS06Q02#C#3#3$0KRF'9RG3Gf:RHp,6canaryRI'Rf;S07#T%5HQ07%S<RJ%S>R>'oRK'4f<S08%6H'9RLPEPGQ08C>f=S09Q07#6'9RMp,2FpRN%Q:S0:#QRO#D#3#JS0;,9NRPQ09C>f>RQQ08#6RRp,1BRSp,2BSRT,9SRUPQD@Q09#6RV%AO#SRO,oJRW'4f@RX%6QS0<%QA#ARY#SRZ,oJR[3;P0p,3OUTS0=f?R\O1fBR]f^R^fER_fDS0>fZR`fYRafSRbfRRcfQRdfPRefORffNRgfMRhfLRifKRjfJRkfARlP\fCRmMBfP^11?GRnp,2gpRop,2tpRpf]Rqf\Rrf[RsP`Pa11?l11?H11?NRtfXRufWRvfVRwfURxfTRyPbPcPdPePfPgPhPiPjPkfIRzfHR{fGR|fFR}MOBP_%3:#D#A#D#3#A#3#3#J,1?S0?Q0>%}@S0@Pm&052S0AFEDK[[[[[[[[[[XS6f8S0B?GEG1RDI%TH%5D14HKQ07%6DPEPGQ07D@PLPNPPQ08C>PMPSPUQ09C>14RWA;\V[P2P]PX%HQRVQ08I01%5X1\=V#F=;XK':g00<iRV%H\,\=%5]%F1=;]K':XsVP1%c\RV&0N\Ek%5l%FV=;lK':p,3fmt#cRV#bS0C%FV#5S0Dp,5slots,\@RV#bS0E%FV#5S0F%c]RV#b%FV#51sJZS0G145JRV%5Z145[[[S0H%5JR=g01WWRRArJZ4UW?S0I%5[\R^?=S0J1sJ>S0K%5>145K[\VS0LArJ>4VRX?=S0M%5K\R^?=S0N1sJOS0O%5O145W[\VS0PArJO4VRX?=S0Q%5W\R^?=S0Rg00_>R=g00b3RR#jRO#jS0S,`6S0T1`6OS0U1`6RS0V'P'Pg00bRS0W'i&00=S0X3O%y=S0Y1_63&0L6S0Z7Z4S0[&0J6S0\&0I6RR1Y6:RO%NJRJ%^Y5|6S0]'h,gRS0^%}9RYPR%8:#A#C#C#3#3#3#3#3#JS0_#N1Y6<R<57RS0`PYPR%8A#3#C#3#3#JS0a#NS0b9q6O97R<PY1z65RA%NFS0c,MOS0d57RQ0dA|6J?RJ'h,gR5XRC<C<C<20CR;S0eP1P3g00^^R;g00a8RV'p20B13=?;VdB0A654H0@S0fb3b:b;X06X16141[S0gQ0_/23Q0a,V3,27197FR5#5145K':[[[^06^16P1PEQ06p,3QHIS0hp,3GLOS0ip,2LOS0jO5b2b4b5b6b7b8b9b>b=b<,xG1=?nR5=?6GQ0CQ0DQ0EQ0F%cmRV#b%FVRV#5Q0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0XQ0Y1_64S0kQ0\PR1hOJ,gRRJPYPRA7RAORAPYAXRAJC<C<Q0eQ0fb3b:b;X06141K%54%53143K':[[^06P1PhP]PmO3b2b4b5b6b7b8b9b>b=b<,xm11?m,=?=?6mp,4HOUTP0PNPSPTPBp,5TOPOKS0lQ0=K0=P1fbS0mPnPoPpfaS0nf`S0of_RKP^Pq11?_11?VPtPrPsP`PaPuPvPwPxPyPbPcPdPePfPgPhPiPjPkPzP{P|P}PmPEPIOVPBP|P}O211?},=?Q0>#H5I{Q05=a6_%6}S0p/4W1L?|%6|S0q,1?5?@A?@ttS0rAGhE5g05SPS0s,V5,2Eg05TS/2ES0t145[Q0lP5O11RcI%Tb12PES0u?U5N12UES0v?U5S11?y,=?RV%6cPEP5PVD@11?x,=?S0w%6b'9S0xPNPPQ0wC>11?w,=?S0y%6yS0z'9S0{PSPUQ0yC>11?v,=?S0|%6xS0}'9S0~/2[P0Q0=PwO1PaP0PNPSPTPBfuS10PnPoPpfqS11fpS12fjRVfiRAfhRJfgR;ffR>feRZfdRMfcRLQ0mQ0nPrPs11?uR~,=?S13PwPEPIP`ML[Q10PnPoPpftS14fsS15frS16Q11Q12P~1L?wPtfoS17fnS18fmS19flS1:fkR~PVPAPJP;P>PZPMPLQ0mQ0nQ0oPKP^PqMOBPrQ0?PsQ0@P`Q0AFEDK[[[[[[[[[[[[[[[[[[[P6P5PBPzP{O2S1;11?{S1<,=?%H}S1=5IkQ05=a6|S1>%6{S1?/4WS1@1L?z%6zS1A,1?5?@S1BQ0rf6S1C9GfEf7S1DQ0s'V,2EQ0t14D[Q0lPHO11RyIS1E%TxS1FQ0uQ09;UNQ0v?UQSQ0{PEP\Q0yC>Q0~PNPPQ0|C>Q13%6wS1G'9S1HPSPUQ13C>11?aS13,=?S1I%6vS1J;;[P0Q0=PuO1S1KPsP0PNPSPTPBfwS1LPnPoPpQ15Q16Q1:P~PVPAPJP;P>PZPMPLP^Pq11?`S1M,=?PuPEPIPrML[Q1LPnPoPpfvS1NQ10Q14Q15Q16Q1M1L?uPtQ11Q12Q17Q18Q19Q1:P~PVPAPJP;P>PZPMPLQ0mQ0nQ0oPKMOBP^Q0?PqQ0@PrQ0AFES1MDK[[[[[[[[[[[[[[[[[[[XR6P1PGP7EkPBP{P|O211?|,=?S1O%H_5IzQ05=a6}Q0q/4W%c{S0q#FS1P,1?Q1?,1?5?@Q0rAGgEGQ0s,VG,2ES0sQ0t14G[S1?Q0lPGO1S0l1RbI%TyQ0u?UGNS0uQ0v?UGSS0vQ0xPEPGQ0wC>Q0{PNPPQ0yC>Q0~PSPUQ0|C>Q1H/2[P0Q0=PvO1P`P0PNPSPTPBQ1NPnPoPpQ16Q11P~PVPAPJP;P>PZPMPLQ0mPqPrQ1IPvPEPIPsML[Q1NPnPoPpQ10Q14Q15Q16Q11Q131L?vPtQ12Q17Q18Q19Q1:P~PVPAPJP;P>PZPMPLQ0mQ0nQ0oPKP^MOBPqQ0?PrQ0@PsQ0AFEDK[[[[[[[[[[[[[[[[[[[P6Q1OPBPkPzO2%H|9Ij4Q05=a6{Q1A/4W1L?k%6k,1?5?@Q0rAGeEGQ0sQ0tQ1?Q0l1RxI%TwQ0uQ0vP\Q0}PEPGP\D@PXQ1GPNPPPXD@PlQ1JPSPUPlD@%6u=;][P0Q0=PaO1PrP0PNPSPTPBfxRWPnPoPpQ14Q15Q19Q1:P~PVPAPJP;P>PZPMPKP^PmPaPEPIPqML[PWPnPoPpQ1LQ1NQ10Q14Q1511?s1L?aPtQ16Q11Q12Q17Q18Q19Q1:P~PVPAPJP;P>PZPMPLQ0mQ0nQ0oMOBPKQ0?P^Q0@PqQ0AFEDK[[[[[[[[[[[[[[[[[[[XR6P1P|P7EkQ1;Q1=9Ik{Q1>Q1@Q1BQ0rAGfEGQ0sQ0tQ1?Q0lQ1EQ1FQ0uQ0vPwQ0zPEPGPwD@PvQ0}PNPPPvD@PuQ1GPSPUPuD@Q1J=;a[P0Q1KPsP0PNPSPTPBQ1LPnPoPpQ15Q16Q1:P~PVPAPJP;P>PZPMPLP^PqP`PuPEPIPrML[Q1MDK[[[[[[[[[[[[[[[[[[[P0P2P9Q0=P}O1PzP0PNPSPTPBPZPnPoPpQ0nQ0oP`PaPuPvPwPxPyPbPcPdPiPjP{P}PEPIPkML[PZPiPjQ0nQ0oP`PaPuPvPwPxPyPbPcPdP{P}PkMBfPZPnPoPpPMPLQ0mQ0nQ0oQ1<1L?}PtPKP^PqPrPsP`PaPuPvPwPxPyPbPcPdPePfPgPhMOBPiQ0?PjQ0@PkQ0AFEP1P_Q0>PmPDQ0p,1?,p@1p@tPlQ0CQ0DQ0EQ0FQ0q#bS0qQ1P#5S1PQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0XQ0YQ0[Q0\PRQ0b9q6<97ROPYQ0c,M<Q04#8#JRW#N5q697ROC<Q0eQ0fb3b:b;X06X16Q0a,V4,21193F/VW,24[^06^16P1Q06PEQ0jO3b2b4b5b6b7b8b9b>b=b<Q0seQ0iQ0CQ0DQ0EQ0FQ0qQ1PQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0XQ0YQ0kQ0\PRQ0^PYQ0dQ0]'h,gRC<Q0eQ0fb3b:b;X06Q0g194F/4[[^06P1Q06Q0hO2b2b4b5b6b7b8b9b>b=b<Q1?ep,3TOKPGQ06Q0CQ0DQ0EQ0FQ0qQ1PQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0XQ0YQ0kQ0\Q0d=7ROQ0eQ0fb3b:b;X06A;1F1^06P1Q06O1b2b4b5b6b7b8b9b>b=b<p,2TQO4Q0lePXP\Q0CQ0DQ0EQ0FQ0qQ1PQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0Rp-0R[Q0S#jRW,`6S0SQ0TQ0U'P'PQ0W'i%jW,`6Q0SQ0V'P'PQ0W'iQ0X5O=5O=Q0YQ0Z1_687Z31_67S0U7Z4Q0\PRQ0:,Y6RWQ0:#8,Y6S0:57RPYPRQ1C,mRQ0;#N,MOS0l%8:#A#D#A#D#C#3#C#3#JS0d#N57R5XRQ0:Q02#SS0k#NS1?'M=7ROQ1D,mRS0:5XR5dRPYPRQ0`PYQ0l=7R<Q0c,MW=7RO5dRC<C<C<Q0eQ0fb3b:b;X06X16XC6XD6XA[WB1237Q0;Q0d5;4,:CQ0k=;84Q1C':']Q0_/27P7Q0;P819CFS0;P7D@[[[^06^16^C6^D6^A[^B[P1p,2VAS0_,2P%D:#D#3#C#C#D#C#3#J/2Np,2APS0dQ06PEPNp,3HAPS0lp,5SEP_FQ0iO9b2b4b5b6b7b8b9b>b=b<Q0ueQ0CQ0DQ0EQ0FQ0qQ1PQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0V'P'PQ0W'iQ0X5O=Q0Y1_6CQ0Z7Z8Q0Z7Z3Q0U7Z4Q0\PRQ01,Y6R=Q02,Y6RF57RPYPRQ0:1MO<=7RWRW5XRQ1?,MF=7ROQ0B,mR5XR5dRPYQ0c,M==7RO9dRWC<C<Q0eQ0fb3b:b;X06X16XC6XD6XV6XA[XB[1278Q1CA;437':Q0k=;C4Q1D':']P3P7P8Q0;P3D@[[^06^16^C6^D6^V6^A[^B[P1Q0_,2U%8:#A#D#A#D#C#3#A#3#J/2SQ0dQ06PEPTPSQ0lp,5SEP_BO9b2b4b5b6b7b8b9b>b=b<Q0veQ08Q07PHQ0BOCP9g04[FR:P0PNPSPTPBPAPnPoPpPZPMP^PqPrPsP`PaPuPvPwPxPePfPiPkPEPIPgP3P4P1MOlPVPdPeP>PZPKP^PqPrPsP`PaPuPvPwPhPjPfP7P3P4MEw[]J^\0P1P0PNPSPTPBPJPnPoPpPMPLPqPrPsP`PaPuPvPwPxPyPfPgPjPzPEPIPhQ00P4P1MOlP6P5Q03Q03fzR5PnPoPpP\PQQ09Q1NQ10Q08Q07PHPDQ0BQ1DQ1CPCQ17Q18Q19Q1:P~PVPAPJP;P>P8P7P3P4MOBQ0n%v5Q0oQ0@P1Q0AFE9?:]20<66R51eEX1eNP1eSU&0055O55O5RU3O?uK1At2K1%T1RPAG1EXPBP1PmO21R1IR[%Hs9I1q':3W3W3WW['0XQ@,0@XP@,0@XO@,0@XN@,0@XI@,0@XH@,0@XG@,0@XF@,0@XE@,0@XZ@,0@XY@,0@XX@,0@XM@,0@XL@,0@XK@,0@XR6P1PGPDEkQ03Q03fyRWPnPoPpP\PQQ09Q10Q14Q08Q07PHPDQ0BQ1DQ1CPCQ18Q19Q1:P~PVPAPJP;P>PZP8P7P3P4MOBQ0o%vWPKQ0@P1Q0AFE9?:l1eEG=O5U?u^1At2^1AG1EGPBP1P]O2%H`9I1r,:[3W7WP3WW['0XQ@,0@XP@,0@XO@,0@XN@,0@XI@,0@XH@,0@XG@,0@XF@,0@XE@,0@XZ@,0@XY@,0@XX@,0@XM@,0@XL@,0@XK@,0@P1bTWTXJ:Z030n01104000101XW9P0PNPSPTPBPJPnPoPpPMPLPqPrPsP`PaPuPvPwPxPyPfPgPjPzPEPIPhP3P4P1MOlPAPePfPZPMP^PqPrPsP`PaPuPvPwPxPiPkPgP7P3P4MEw[^J:^\0^W9eN:0;b@b@b@b@bab`P0Q0=PXO1PmPKP}P_PsP`PyPbPcPdPePfPgPhPiPjP]PXQ0>MBfPKPnPoPpP^PqPrPsP`11?]%6X,1?PtPaPuPvPwPxPyPbPcPdPePfPgPhPiPjPkPzP{P|MOBP}Q0?P_Q0@Q0>Q0AFEDKebUbUP0Q0=PQO1PlPqQ0>PmPaPuPcPdPePfPgPhPiPjPkPzPXPQP]MBfPqPnPoPpPrPsP`PaPu11?XQ0<,1?PtPvPwPxPyPbPcPdPePfPgPhPiPjPkPzP{P|P}P_MOBQ0>Q0?PmQ0@P]Q0AFEDKeWkWgW_W^W]WfWeWhWmWnPCP1J0:WcWiWlWdWoXS6Xj6Z020WrWqWbXQ@XP@XO@XN@Xx@Xw@Z01@Z00@X~@X}@X|@X{@Xz@Xy@XI@XH@XG@XF@XE@Xv@Xu@XM@XL@XK@Wto"). Qed.

  (* [comment removed for export] *)
  Definition fp_postq (ra' : word) (Ft : bvmap 5 word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (m : word -> option byte) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
      ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft' (ret_pc ra') fc' None m' (seg_rom usegs)
      /\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ frm0 fc' /\ Fokd Ft Ft'
      /\ stk usegs m' lo (q + -544)
      /\ SINK m' st'
      /\ ssp_cells m' canary.
  Lemma fp_callq : forall ra' t0 t1 t2 s0 s1 (a1 a2 a7 : word) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (y w p fl t : Z),
    fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
    SINK m st -> y = (bv_unsigned a1 + 2^64 * bv_unsigned a2)%Z -> bv_unsigned a7 <> 5%Z ->
    (-2^31 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
    stk usegs m lo (q + -544) -> ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
    implM usegs (OUTFP y w p fl t) st (fp_postq ra' Ft s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 FPv a1 a2 (Z_to_bv 64 w) (Z_to_bv 64 p) (Z_to_bv 64 fl) (Z_to_bv 64 t) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x252d4) fc None m (seg_rom usegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "p'0h04__x1h12Hah24__x2h37__arithh44__ffh57__sat12h67__sat13h77__sat14h87__sat15h97__sat16h:7__sat17h;7__sat18h<7__sat19h=7__sat20h>7__sat21h?8__varmaph@5__withA4__p1hB4__p2hC4__x3hD4__x4hE3FPChF2FthG2a1hH2a2hI2a7hJ2t0hK2t1hL2t2hM2t3hN2t4hO2t5hP2t6hQ1PhR4__x5hS2a3hT2a4hU2a5hV2a6hW3fc'hX1khY2m'hZ3ms'h[1zh\2Eqh]3FRMh^2H7h_2HSh`3Hflha2Hphb2Hthc3Htahd2Hwhe2Hyhf2MIhg3SSPhh2SThi1ahj2fchk2flhl1mhm1phn1rho3ra'hp2s'hq2s0hr2s1hs3s10ht3s11hu2s2hv2s3hw2s4hx2s5hy2s6hz2s7h{2s8h|2s9h}2sth~3st'i001ti011wi021yp%0p%1p&0p;1p;2p;4p;8p;3p;Ip;Op;7p;6p;?p;Lp;Bp;:g007ej15Tg008Jj1UTg008hj1eTg00U>j1BTg004?k20?Tg00>Ak10>Tg03JKj2kTg03S8j4fTg05UTj8}Tg026gj2>Tg013Gj1;Tg01e2j2^Tg01ijj2gTg00dZj24Tg01h6k10=Tg00A_j21Tg00COj2=Tg025Mj2aTg01ACk101Tg05OLj2WTg044]j2YTg05VYj1]Tg01mBj2[Tg01mjj3TTg00Qcj1`Tg00RBj2STg00STj2_Tg00Emj1yTg00T@j3ITg007Ek10FTg00FMj2\Tg01Bkk10ETg00Fkk10DTg00GIk10CTg00H4j2NTg01eoj3xTg00Iej1wTg01Clj3lTg00HWj2vTg00JGk20<Tg00@Gj2RTg00Jik20;Tg00;Lj3<Tg00KUk308Tg00L4k407Tg00C3j2JTg01?fj2OTg027Qk204Tg009Kj23Tg05WIlIcmL02Tg058GlOLTg0599k103Tg05:2j7KTg002Tj6sTg05XNl?rmB00Tg00QIj2jTg05@4j1qTg04bfj3oTg04cZj3tTg03n1j2iTg0158j20Tg05RVm:05Tg00Lfk106Tg05Daj4~Tg00Rkk309Tg00T`k40:Tg00I:j4pTg00WXj7uTg01CIj3|Tg00X`j7{Tg00YDk80@Tg04ZQk70ATg00X<j6zTg00Uck70BTf0R0#5#5p=2g00;fR1P1f1R2P0Cfp=VA<120p=ZA<120$06p=@%B0#Bp=Hf2R31J20'=p=9g00[2R4/10p=6%50#;p=A%50#Bp=:%B0#5p=7g00j;R5P3P2P0C~p=P1J40p=MB09120p=GP1P3P2P0H0:p=Q1v10p=CP1P2g00_jP0Cpp=nP2g00[PR6g00[oR7P7g00\OR8P0g00\oR9Fup=mP3P6P7P7P8P1P2g00`QP0CpP9Fup=8A|120p=DP3P6P7P7P8P2P0F{p=Xf3R9P6P7P7P8P3P2P0L0@p=?1120,j3p=Ff4R:P5P1P9P3P2P0K0Ap=bP2P6P7P7P8P0Ezp=hP3P6P7P7P8P2P0K0Bp=d1=20,=3p=Eg00<DR6#5R;#5S00#5R<#2R=#5R>#UR?#eR@%B;RA#US0100?@RB%U=#eRC%U<#e$0>\@RDp,2StREPEp,2FpRFp,1BRGp,2BSRHp,4SINKRIp,5TOPOKS02p,5OUTFPS031k11RJ/k1RK/k1P1PKP1PJP11V:9P3CfP2CfP0CfG}PIf7RKf6RLO2fKRM,>?%;;RN%;>RO'^RPfJRQ,>?RR'g'4,ZL%;AS04,@R%B6S05#BRR#H#;RS,^NRT$0=S06/1KRU%;6S07,1K'=%5AS08#5RV#;RW,^NRX99UK%6KRU%;=R=,^NRY79K%5>#AR>99UKf8S09/a=Q05#5S0:#2#:#;RU'@f?S0;p,2loRZp,1qR[%7<#2#2$01R\'4R]3Pf@R^p,6canaryR_'WfAR`,Y5fCRa#]1[N=S0<%MNRb%6=%MY[[S0=%6NRcg01WWRdATN=2UW1S0>%6Y\d^1cS0?%BA#HRA#;Re,[NS0@%6e1^NeRf#M[\bS0AATNe2VdX1cS0B%6f\d^1cS0C1[NWS0D%6W%MX[\bS0EATNW2VdX1cS0F%6X\d^1cS0G1[NOS0H%6O%MP[\bS0IATNO2VdX1cS0J%6P\d^1cS0K1[NSS0L%6S%MT[\bS0MATNS2VdX1cS0N%6T\d^1cS0Og00_>Rcg00b3Rd#`RT#`S0P,S1S0Q1S1TS0R1S1dS0S'G'Gg00bRS0T'_%ycRd3I&0FcS0U1\13&0E1S0V7Q2S0W&0D1S0X&0C1RT1N16RS%CNRN%UA5x1S0Y'n,mTS0Z%w7R7PT%56#H#7#7#2#2#2#2#2#AS0[#C1N1;R;58TS0\P7PT%5V#7#2#2#AS0]#CS0^9l1S98T;P71v14%C\S0_,DSS0`58TQ0`Ax1N?'n,mT5XTC?C?C?20<T8S0aP0P3g00^^R8g00a8RN'R20;03=<8NdB08142H07S0bb4b?b@X01X211J0fS0cQ0[/13Q0],O3,19149\R4#6?94P[[[^01^21P0PZP[p,3QHIS0dp,3GLOS0ep,2LOS0fO5b3b5b6b7b8b9b:b;b<b=b>-04]13?]R4,>?RN/Z]f=R8f]RVP4p,2gpRAp,2tpRbf\ROf[RWfZRefYRgfXRh13?FRifWRjfVRk13?`S0g13?^S0hQ0;,3?S0if>S0j,3?S0kfURlfTS0lfSRmfRRnfQRofPS0mfOS0nfNS0ofMS0pfLS0qPMPQfIRpfHS0rfGS0sfFRqfERrfDRsPaPZP_OUPIPsPaO21>?hS0t1>?j,gP'4,ZaA<@iiS0u13?sS0vQ0v5<@Rt1>?OQ04'@Q06/1pRuQ07,1p'=A9upX%6pRu?9pYA9up>1aQ=/@UAPoZNg05YVS0w,ON,1Zg05TS/1ZS0x1JNfQ02PNO11Wk_1Y5j%]g%:R#2#AS0y,4FS0z/1ZS0{?FNF14GHS0|/1ZS0}?FNGPEQ03PgPhPjPkPlO5PePEPFPGPHPIftS0~P4PAPbfpS10foS11fkRRfjRufiRvfhRwfgRxffRyfeRzfdR{fcR|fbS12PVPZP_PWMIcQ0~P4PAPbfsS13frS14fqS15Q10Q11PifnS16fmS1713?hS1813?jS1913?kS1:13?lflS1;PRPuPvPwPxPyPzP{P|Q12faS1<f`S1=f_R}f^R~MOLPV%26#7#7#:#:#7#7#7#A,3?S1>PO%w@S1?PW&035S1@FKDb[[[[[[[[[[[[[[[[\t\t\t[[[[P1PNPIPqPrO21>?e1>?gS1A,gP'4,ZrQ0u13?qRt=<@tRt1>?~Q04'@Q06/1MS1BQ07,1M'=Q1B?9MX%6MS1B?9MYQ1B?9M>Q0q/a=/@UAPmZ8Q0jQ0w'O,1ZQ0x1J^fQ02P`O11Wh_1Y5g%]WQ0{?FrFQ0}?FqGPEQ03PWPePgPhPjO5POPEPFPGPHPIfvS1BP4PAPbQ14Q15Q17Q1;PRPuPvPwPxPyPzP{P}PZP_PVMIcQ1BP4PAPbfuS1BQ0~Q13Q14Q15PiQ10Q1113?e13?gS1CQ18Q19Q16Q17Q1;PRPuPvPwPxPyPzP{P|Q12Q1<Q1=MOLP}Q1>P~Q1?PVQ1@FKDb[[[[[[[[[[[[[[[[\t\t\t[[[[X[1P0P]P2EsPIPrPsO2Q1AQ0t,gP'4,ZsQ0u13?rRP=<@PRt1>?VQ04'@Q06/1QS06Q07,1Q'=Q06?9QX%6QRX?9QYA9XQ>1aM=/@UAPnZ]Q0w,O],1ZRUQ0x1J]fR=Q02P]O1RX1Wj_1Y5h%]eQ0{?F]FS0{Q0}?F]GS0}PEQ03PePgPhPjPkO5PWPEPFPGPHPIQ1BP4PAPbQ15Q10Q1;PRPuPvPwPxPyPzP{P|P~PZP_POMIcQ1BP4PAPbQ0~Q13Q14Q15Q10PiQ11Q16Q1CQ18Q19Q1:Q17Q1;PRPuPvPwPxPyPzP{P|Q12Q1<Q1=P}MOLP~Q1>PVQ1?POQ1@FKDb[[[[[[[[[[[[[[[[\t\t\t[[[[PEP5P1Q03PsPafBRtP`P^O5PrPEPFPGPHPIP}P4PAPbPWPePkPlQ0lPmPnPoQ0mQ0nQ0oQ0pQ0rPZP_PqMIcP}Q0rPWPePkPlQ0lPmPnPoQ0mQ0nQ0oQ0pPqM?rP}P4PAPbP~PVPOPWPePiPgPh13?aR>13?tRYQ0gQ0hPjPkPlQ0lPmPnPoQ0mQ0nQ0oQ0pQ0qPMPQPpMOLQ0rQ1>Q0sQ1?PqQ1@FKP0Q0jP81R@i1R@>1R@YQ0g,R@Q0h,R@f<S0gf;S0uf:S0xf9S1<Q09PKPLQ0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0LQ0MQ0NQ0OQ0HQ0IQ0JQ0KPdQ0UQ0WQ0XPTQ0^9l1;98TSP7Q0_,D;Q00#B#2#:#2#2#ARY#C5l198TSC?Q0aQ0bb4b?b@X01X21Q0],O2,10143\/OY,12[^01^21P0P[PZQ0fO3b3b5b6b7b8b9b:b;b<b=b>PUeQ0eQ0@Q0AQ0BQ0CQ0<Q0=Q0>Q0?Q0DQ0EQ0FQ0GQ0LQ0MQ0NQ0OQ0HQ0IQ0JQ0KPdQ0U1\12RUQ0XPTQ0ZP7Q0`Q0Y'n,mTC?Q0aQ0bb4b?b@X01Q0c142\/Jf[^01P0P[Q0dO2b3b5b6b7b8b9b:b;b<b=b>P=ep,3TOKP]P[Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0LQ0MQ0NQ0OQ0HQ0IQ0JQ0KPdQ0UPUQ0XQ0`=8TSQ0aQ0bb4b?b@X01140\/10^01P0P[O1b3b5b6b7b8b9b:b;b<b=b>p,2TQO4PXef5RXP:P9Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0LQ0MQ0NQ0OQ0HQ0IQ0JQ0Kp-0RUQ0P#`R=,S1RfQ0QQ0R'G'GQ0T'_%`=,S1Q0S,Gf'GQ0T'_=Icd5IcQ0UQ0V1\1:7Q31\19S0R7Q2Q0XPTQ05,N1R=Q0:,N1RY58TP7PT1hTLQ0y#C,DSS0:%56#H#:#H#:#7#2#7#2#AS05#C58T5XT%;<R>#CS0P,DY=8TS1hTKRY5XT5dTP7PTQ0\P7Q0:=8T;Q0_,D==8TS5dTC?C?C?Q0aQ0bb4b?b@X01X21XC1XD1XAUWB1139Q0y,42Q05'1,=X14:>/12/=L'jQ0[/19Q0y,49/1:14X\S0y;F9[[[^01^21^C1^D1^AU^BUP0Q0zp,2VAR\'1%:6#:#2#7#7#:#7#2#A/1Fp,2APS0[P[PZPFp,3HAPS05p,5SEP_FQ0eO9b3b5b6b7b8b9b:b;b<b=b>Q0{eQ0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0LQ0MQ0NQ0OQ0HQ0IQ0JQ0KQ0QQ0S'G,GfQ0T'_=IcdQ0U1\1XQ0V7Q:Q0V7Q3Q0R7Q2Q0XPTQ00,N1Rd1N1<R<58TP7PT1DS;=8T=R=9XTYQ0P,D<=8TSQ09,hT5XT5dTP7Q0_,Dd=8TS9dT=C?C?Q0aQ0bb4b?b@X01X21XC1XD1XR1XAUXBU119:1423/19,=L14X>/12/=K'j1439/1:Q0y;F3[[^01^21^C1^D1^R1^AU^BUP0Q0|/1\%56#H#:#H#:#7#2#H#2#A/1GQ0[P[PZPHPGQ05p,5SEP_BO9b3b5b6b7b8b9b:b;b<b=b>Q0}eOGg04[FR[PEPFPGPHPIQ12P4PAPbP~PVPgPhPjPkPlQ0lPmPnPoQ0mPMPZP_PpP3P2P0NL02RVP1PNQ1BP4PAPbP^Q0;Q0jQ15Q10PPP8Q0gQ0uQ0xQ1<Q09PKQ1;PRPuPvPwPxPyPzP{P|PLPXP:P9MOLP3Q1B#qP2Q1?P0Q1@FK9<[a1VZ`Q0z,VFQ0|,VG%yJ5IJ5IJRG5IJ?oO0At5O01Y50RF%]2RPQ01#eRNQ01/>0Q08#;'@RH1i:2R6Q1=/i25<@[]XAP0Z`PIP0PsO21W0_R_3E3E3E3EXYD,0DXWC,0CXFB,0BXP@,0@XO@,0@XN@,0@XM@,0@XI@,0@XV@,0@XU@,0@XT@,0@XS@,0@XH@,0@XG@,0@XL@,0@XK@,0@XJ@,0@X[1P0P]PLEsQ0~P4PAPbP^Q0;Q0jQ10Q11Q0vP8Q0gQ0uQ0xQ1<Q09PKPRPuPvPwPxPyPzP{P|Q12PLPXP:P9MOLP3Q0~#qP2Q1?P0Q1@FK9<[t1VZ]=IJG?oW0At5W01i}29<@6\H^XNAP0Z]PIP0PaO2;E_5EP7EF3EXYD,0DXWC,0CXFB,0BXP@,0@XO@,0@XN@,0@XM@,0@XI@,0@XV@,0@XU@,0@XT@,0@XS@,0@XH@,0@XG@,0@XL@,0@XK@,0@XJ@,0@P0bQWQWZX~EXn1P|Q0qP}P~PePgPhPjPkPlQ0lPmPnPoPQP9P3P2NB00\V^Z[^pE^i1eN:05bEbEb\PEQ03P`P^Q0;Q0jP8O5PtPOPrPhPjPmPnPoQ0mQ0nQ0oQ0pQ0qPMPQPaM?rPOP4PAPbPWPePgPhPjPiPkPlQ0hQ0iQ0k13?8Q0lPmPnPoQ0mQ0nQ0oQ0pQ0qPMPQPpQ0rQ0sPqMOLPrQ1>PsQ1?PaQ1@FKDbeW]WfWgWhWcWbW`WaWdW^WeW_WEZ001Xk1Xm1Z011Z021W}WlWjWFXP@XO@XN@XM@Xt@Xs@X|@X{@Xz@Xy@Xx@Xw@Xv@Xu@XI@XH@XG@Xr@Xq@XL@XK@XJ@Woo"). Qed.

  Lemma conv_type_dbl : forall t, conv_type t = Some T_DBL -> (69 <= t <= 103)%Z /\ Z.lor t 32 <> 97%Z.
  Proof.
    clear. intros t CT. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in CT.
    repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [try discriminate CT|] end; try discriminate CT.
    repeat match goal with E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
      subst; (split; [lia | discriminate]).
  Qed.

  (* [comment removed for export] *)
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 156792 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 228064 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  (* [comment removed for export] *)
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call usegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [usegs usegs] in *; fold usegs in *.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition S_EXIT : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 apv] ->
      frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
      evt usegs (POST r st)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x25078) fc None m (seg_rom usegs)).

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
         evt usegs Q
           (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (2147483647 - cnt')) (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) (Z_to_bv 64 n) (Z_to_bv 64 (A + i)) x24 x25 (Z_to_bv 64 n) x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x243c4) fc None m (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt i)) x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 cnt') x20 x21 x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24368) fc None m (seg_rom usegs)).

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
         evt usegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 c') (Z_to_bv 64 (A + k')) a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 32)
                    x18 x19 x20 x21 x22 x23 (Z_to_bv 64 FL) x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x2447c) fc None m (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 w3 (Z_to_bv 64 (A + p + k)) x15 (Z_to_bv 64 1) (Z_to_bv 64 32)
                 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24458) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_WLOOP : Prop :=
    forall (x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (pos acc w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
      is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (w, s2) -> s2 <> [] ->
      (forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
         (pos < k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
         evt usegs Q
           (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
                    x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x245ac) fc None m (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) x12 (Z_to_bv 64 (A + pos)) x14 x15 x16 x17
                 x18 x19 x20 x21 (Z_to_bv 64 acc) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24510) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_WIDTH : Prop :=
    forall (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k1 w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= k1 < zlength fmt)%Z ->
      getint (sfx k1) 0 = Some (w, s2) -> s2 <> [] ->
      (forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
         (k1 <= k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
         evt usegs Q
           (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
                    x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x245ac) fc None m (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x244c4) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_PLOOP : Prop :=
    forall (x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (pos acc p : Z) (s3 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
      is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (p, s3) -> s3 <> [] ->
      (forall (k3 : Z) (a1 a3 a4 : word),
         (pos < k3 < zlength fmt)%Z -> s3 = sfx k3 -> is_digit (znth fmt k3) = false -> (0 <= p <= INT_MAX)%Z ->
         evt usegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x246e4) fc None m (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) (Z_to_bv 64 (A + pos)) x13 x14 x15 (Z_to_bv 64 10) (Z_to_bv 64 8)
                 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 acc) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24670) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_PREC : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k2 k3 p : Z) (xp : bool) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= k2 < zlength fmt)%Z ->
      ( (znth fmt k2 <> 46 /\ p = -1 /\ xp = false /\ k3 = k2)
        \/ (znth fmt k2 = 46 /\ xp = true /\ k2 + 1 < zlength fmt /\ znth fmt (k2 + 1) <> 42
            /\ getint (sfx (k2 + 1)) 0 = Some (p, sfx k3) /\ k2 + 1 <= k3 < zlength fmt) )%Z ->
      (forall (a1 a3 a4 : word),
         (-1 <= p <= INT_MAX)%Z ->
         evt usegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x246e4) fc None m (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 (Z_to_bv 64 (A + k2)) x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x245ac) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_STATE : Prop :=
    forall (x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k3 ty : Z),
      let _ := ctx_all in
      finv m -> (0 <= k3 < zlength fmt)%Z -> conv_type (znth fmt k3) = Some ty ->
      (forall (a2 a3 : word),
         evt usegs Q
           (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 ty) a2 a3 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 (Z_to_bv 64 (A + k3 + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 0) x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x24764) fc None m (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (A + k3)) x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x246e4) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_DIR : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (i : Z) (d : dir) (rest : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= i)%Z -> (i + 1 <= zlength fmt)%Z ->
      parse_dir (sfx (i + 1)) = Some (d, rest) ->
      (forall (k4 : Z) (a2 a3 a4 t1 : word),
         (i + 1 < k4 <= zlength fmt)%Z -> rest = sfx k4 -> znth fmt (k4 - 1) = d_t d ->
         (0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
         evt usegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                    (Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) a2 a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 (Z_to_bv 64 (A + k4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x24764) fc None m (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x243e8) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition S_END : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 apv] ->
      frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
      evt usegs (POST r st)
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) FPv x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24f20) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_HEAD (fuel : nat) : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i cnt l k : Z) (args : list parg)
           (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i)%Z -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l <= INT_MAX)%Z ->
      implM usegs (printf_loop OUT OUTFP fuel (sfx i) args (cnt + l)) st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 cnt) FPv (Z_to_bv 64 (A + i)) x22 x23 x24 x25 (Z_to_bv 64 l) x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x2434c) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_CONV : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (d : dir) (a : parg) (args : list parg)
           (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) (a :: args) ->
      match a with PA_g dd =>
        fpcall_stmt Fp B BS SINK TOPOK OUTFP
          (f128_of_d dd, d_w d, d_p d, (if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD))%Z, d_t d)
      | _ => True end ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (1 <= i4 <= zlength fmt)%Z -> znth fmt (i4 - 1) = d_t d -> conv_type (d_t d) = Some (d_ty d) ->
      (0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
      ((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z ->
      (0 <= c <= INT_MAX)%Z ->
      implM usegs (cnt' <- conv OUT OUTFP c d a ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) x12 x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24764) fc None m (seg_rom usegs)).

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
      rw_cells usegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at usegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> body_loc BA (zlength body) -> (BA + zlength body < 2^64)%Z -> (zlength body <= INT_MAX)%Z ->
      (forall m', mem_inv usegs m' -> bytes_at usegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 172032)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      implM usegs (cnt' <- conv_tail OUT c fl w p prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 (Z_to_bv 64 (BA + zlength body)) x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24be8) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition tregs (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 t3 t4 t5 t6 : word) (i4 c w BA wq pq : Z) : bvmap 5 word :=
    mkR xra SPv gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 a4 a5 a6 a7
        s2 (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) s8 s9 (Z_to_bv 64 wq) (Z_to_bv 64 pq) t3 t4 t5 t6.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Definition tinv (m : word -> option byte) (st : St) (k i4 : Z) (args : list parg) (fuel : nat)
      (PFXA fl n pl pq BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte) : Prop :=
    finv m
    /\ rw_cells usegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) (Z_to_bv 64 (Z.land fl 73728)) (Z_to_bv 64 n) (Z_to_bv 64 pl) (Z_to_bv 64 (pl + pq)) (Z_to_bv 64 0) alo ahi j128)
    /\ rw_cells usegs m (q + -392) [CB 24 digs]
    /\ rw_cells usegs m (q + -368) [CB 256 pad]
    /\ SINK m st /\ rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] /\ (0 <= k)%Z
    /\ args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args
    /\ Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args)
    /\ bytes_at usegs m BA (zb body) /\ Forall (fun c => 0 <= c < 256)%Z body /\ body_loc BA n /\ (BA + n < 2^64)%Z /\ n = zlength body
    /\ (forall m', mem_inv usegs m' -> bytes_at usegs m' PFXA (zb prefix)) /\ Forall (fun c => 0 <= c < 256)%Z prefix
    /\ (0 <= PFXA)%Z /\ (PFXA + pl <= 172032)%Z /\ pl = zlength prefix /\ (pl <= 2)%Z
    /\ (0 <= i4 <= zlength fmt)%Z /\ (0 <= fl < 131072)%Z /\ (0 <= n <= INT_MAX)%Z /\ (n <= pq)%Z /\ (pl + pq <= INT_MAX)%Z.

  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
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
      implM usegs (mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x24e04) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_T5 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM usegs (OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x24de8) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_T4 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM usegs (mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x24d64) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_T3 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM usegs (mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x24cdc) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_T2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM usegs (OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x24cc0) fc None m (seg_rom usegs)).

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
      implM usegs (mpad OUT 32 wq (pl + pq) fl ;;; OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x24c40) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_INTC2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p argi : Z) (prefix body : list Z) (BA PFXA : Z)
           (s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at usegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
      (forall m', mem_inv usegs m' -> bytes_at usegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 172032)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      (0 <= argi < 2^64)%Z ->
      implM usegs (cnt' <- (if ((argi =? 0) && (p =? 0))%Z then conv_tail OUT c fl w p prefix []
                            else conv_tail OUT c fl w (Z.max p (zlength body + (if (argi =? 0)%Z then 1 else 0))) prefix body) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24bb0) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_INTC : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) (BA PFXA : Z)
           (s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at usegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
      (forall m', mem_inv usegs m' -> bytes_at usegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 172032)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= argi < 2^64)%Z ->
      implM usegs (cnt' <- conv_int OUT c fl w p xp argi prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24b98) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition dloop_post (x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Ft : bvmap 5 word) (fc : bv 32) (x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (a2 a3 : word) (xq : Z) (W : list Z) (m' : word -> option byte),
      ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xq) (Z_to_bv 64 (q + -392 + (j - zlength W))) a2 a3
                    (Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
                    x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength W))) x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x24b80) fc None m' (seg_rom usegs)
      /\ munch [(q + -392, q + -368)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rw_cells usegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength W)) ds ++ zb W ++ skipn (Z.to_nat j) ds)]
      /\ (1 <= xq <= 9)%Z /\ dec_digits x = (48 + xq)%Z :: W /\ (zlength W + 1 <= j)%Z.
  Definition S_DLOOP : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x j : Z) (ds : list byte),
      let _ := ctx_all in
      mem_inv usegs m -> rw_cells usegs m (q + -392) [CB 24 ds] ->
      (10 <= x < 2^64)%Z -> (zlength (dec_digits x) <= j <= 24)%Z -> x11 = Z_to_bv 64 (q + -392 + j) ->
      evt usegs (dloop_post x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc x j ds m)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) x11 x12 x13
                 (Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24b48) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_FMTU2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (x d jj : Z) (W prefix : list Z) (PFXA : Z)
           (pfx s2s za plp ahi : word) (j128 pre pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 (pre ++ zb W)] -> zlength pre = jj -> (1 <= jj)%Z ->
      ((d = 0 /\ W = [] /\ dec_digits x = []) \/ (1 <= d <= 9 /\ dec_digits x = (48 + d) :: W))%Z ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (forall m', mem_inv usegs m' -> bytes_at usegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 172032)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= x < 2^64)%Z ->
      implM usegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 d) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 PFXA)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 (q + -392 + jj)) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24b80) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_FMTU : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (x : Z) (prefix : list Z) (PFXA : Z)
           (pfx s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (forall m', mem_inv usegs m' -> bytes_at usegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 172032)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= x < 2^64)%Z ->
      implM usegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 x) x11 x12 x13 (Z_to_bv 64 10) x15 x16 (Z_to_bv 64 PFXA)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24b38) fc None m (seg_rom usegs)).

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
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (i mod 2^64)) ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (-2^31 <= i < 2^31)%Z ->
      implM usegs (cnt' <- (let '(argi, prefix) :=
                               (if INTMAX_MAX <? i mod 2^64 then ((- (i mod 2^64)) mod 2^64, [45])
                                else if negb (Z.land fl MARK_POS =? 0) then (i mod 2^64, [43])
                                else if negb (Z.land fl PAD_POS =? 0) then (i mod 2^64, [32])
                                else (i mod 2^64, []))%Z in
                            conv_int OUT c fl w p xp argi prefix (dec_digits argi)) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x24834) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_CV_U : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (u : Z)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= u < 2^32)%Z ->
      implM usegs (cnt' <- conv_int OUT c fl w p xp u [] (dec_digits u) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x2496c) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition xloop_post (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Ft : bvmap 5 word) (fc : bv 32) (l x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (a2 a3 : word) (m' : word -> option byte),
      let H := hex_digits l x in
      ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 l) a2 a3 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength H))) x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x24a24) fc None m' (seg_rom usegs)
      /\ munch [(q + -392, q + -368)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rw_cells usegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength H)) ds ++ zb H ++ skipn (Z.to_nat j) ds)]
      /\ (zlength H <= j)%Z.
  Definition S_XLOOP : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l x j : Z) (ds : list byte),
      let _ := ctx_all in
      mem_inv usegs m -> rw_cells usegs m (q + -392) [CB 24 ds] ->
      (0 < x < 2^64)%Z -> (l = 0 \/ l = 32)%Z -> (zlength (hex_digits l x) <= j <= 24)%Z -> x23 = Z_to_bv 64 (q + -392 + j) ->
      evt usegs (xloop_post x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc l x j ds m)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) (Z_to_bv 64 l) x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x249fc) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_CV_X : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (u t : Z)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= u < 2^32)%Z -> (t = 120 \/ t = 88)%Z ->
      implM usegs (cnt' <- conv_int OUT c fl w p xp u
                              (if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0) then (if t =? 120 then [48; 120] else [48; 88]) else [])%Z
                              (hex_digits (Z.land t 32) u) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x249e4) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_CV_S : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p fl10 : Z) (xp : bool) (P : Z) (s : list Z) (slack : list byte)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 P) ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      bytes_at usegs m P (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256)%Z s ->
      ((- (P + zlength s + 1)) mod 8 <= zlength slack)%Z -> (0 < P)%Z ->
      (P + zlength s + 1 + zlength slack <= lo \/ q <= P)%Z ->
      (P + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= P)%Z ->
      (P + zlength s + 1 + zlength slack <= B \/ B + BS <= P)%Z ->
      (P + zlength s + 1 <= 2^47)%Z ->                              (* [comment removed for export] *)
      (fl10 = Z.land fl (Z.lnot 65536))%Z ->
      implM usegs (cnt' <- (if (p <? 0) && (INT_MAX <=? zlength s) then munr
                            else conv_tail OUT c (Z.land fl (Z.lnot ZERO_PAD)) w (if p <? 0 then zlength s else Z.min (zlength s) p) []
                                           (firstn (Z.to_nat (if p <? 0 then zlength s else Z.min (zlength s) p)) s))%Z ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 fl10) x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x2487c) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_CV_FP : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (y t : Z)
           (pfx s2s za pl plp : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= y < 2^128)%Z -> conv_type t = Some T_DBL ->
      implM usegs (cnt' <- (if xp && (p <? 0) then munr
                            else if (1 <? w) || (2^20 <=? p) then munr
                            else r <- OUTFP y w p fl t ;; if (r <? 0) || (INT_MAX - c <? r) then munr else mret (c + r))%Z ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x247e4) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition POST1 : Z -> machine_state -> Prop :=
    fun r ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               F (ret_pc ra) fc0 None m' (seg_rom usegs)
      /\ munch [(lo, q)] m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
      /\ stk usegs m' lo q
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition S_EXIT1 : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m -> munch [(lo, q)] m0 m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      (0 <= r < 2^64)%Z ->
      evt usegs (POST1 r)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25078) fc0 None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_P1 : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m -> munch [(lo, q)] m0 m ->
      rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells usegs m (q + -392) [CB 24 digs] ->
      rw_cells usegs m (q + -368) [CB 256 pad] ->
      pass1_ok fmt = true ->
      evt usegs (POST1 0)
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 A) x22 x23 x24 x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2434c) fc0 None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition S_PRO : Prop :=
    forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (f : Z) (Q : machine_state -> Prop),
      let _ := ctx_all in
      stk usegs m0 lo q -> mem_inv usegs m0 -> bytes_at usegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      (0 <= f < 2^64)%Z ->
      (forall (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte) (a0 a1 a2 a3 : word),
         finv m -> munch [(q + -544, q)]%Z m0 m ->
         rw_cells usegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
         rw_cells usegs m (q + -392) [CB 24 digs] ->
         rw_cells usegs m (q + -368) [CB 256 pad] ->
         evt usegs Q
           (MS (mkR ra SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 nlt x15 x16 x17
                    s2e (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 A) s6e s7e s8e s9e (Z_to_bv 64 0) s11e x28 x29 x30 x31)
               F (Z_to_bv 64 0x2434c) fc0 None m (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 f) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x2429c) fc0 None m0 (seg_rom usegs)).

End PrintfCore.
