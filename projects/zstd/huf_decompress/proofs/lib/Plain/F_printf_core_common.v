(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_memset F_memcpy F_memchr F_strnlen Stdio_kit F_syscalls StdioFiles.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import Printf_zfacts F_printf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_printf_core_common () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib3Lib3Arr@upd_firstn_skipnC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List:firstn_mapI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00C46Stdlib5Lists4List7map_appC47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes:option_mapK47Corelib4Init5Logic2eq01C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List=nth_error_mapC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notC46Stdlib5Lists4List=nth_error_nthI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_NoneC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec6Prelim4znthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leI47Corelib4Init9Datatypes4bool00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C46Stdlib5Lists4List6nth_okK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesc59OSSVerify5KrLib5PlainDF_printf_core_common>znth_nth_errorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common<nth_error_zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr9u8ro_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List6nth_InC47Corelib4Init5Logic5proj1C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4xorbC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9lxor_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z02C47Corelib4Init3Nat3addC59OSSVerify5KrLib3Lib3Arr?nth_error_splitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib5Lists7ListDef5skipnC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib4Init3Nat3subC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appC46Stdlib5Lists4List9app_assocC35stdpp7tactics<f_equal_helpC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_1_rC56Stdlib6ZArith4Znat5Z2Nat7inj_addc59OSSVerify5KrLib5PlainDF_printf_core_common3sfxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib5Lists4List;skipn_skipnC47Corelib4Init5Logic8iff_reflC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith6BinInt1Z;lt_ge_casesc59OSSVerify5KrLib5PlainDF_printf_core_common8sfx_consC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos6to_natC47Corelib4Init5Logic7f_equalC57Corelib7BinNums6PosDef3Pos7compareC47Corelib4Init9Datatypes7CompOppK47Corelib4Init5Logic3and01c59OSSVerify5KrLib5PlainDF_printf_core_common7sfx_nilC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib6Common<Printf_model7lit_runC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes3orbC47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z8eqb_specK46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib5PlainDF_printf_core_common>lit_run_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common9sfx_skipnC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat9ltb_spec0C46Stdlib5Lists4List?nth_error_skipnC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib5Lists4List@nth_error_firstnc59OSSVerify5KrLib5PlainDF_printf_core_common>lit_run_firstnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common:lit_run_inC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z3oppC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z>div_unique_posC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7div_divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z3lorC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model:digits_auxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common<digits_aux_SC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z7pow_0_rC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z9div_smallC59OSSVerify5KrLib6Common<Printf_model:dec_digitsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lt_transc59OSSVerify5KrLib5PlainDF_printf_core_common?digits_aux_fuelC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8f_equal2c59OSSVerify5KrLib5PlainDF_printf_core_common>digits_aux_accC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_commonAdigits_aux_lengthC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=length_firstnC47Corelib4Init3Nat3minC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List=firstn_firstnC46Stdlib5Lists4List:firstn_appC56Stdlib6ZArith4Znat5Nat2Z7inj_minC59OSSVerify5KrLib6Common<Printf_model:hex_digitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model7XDIGITSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC59OSSVerify5KrLib5Plain=Printf_zfacts>Zrange_forallbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common;hexchar_ok0C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib5PlainDF_printf_core_common<hexchar_ok32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common=hexchar_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6wrap64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat:wrap64_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat4lo64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat4hi64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib3Lib5Bytes;lor_lt_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5mk128C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec>Z_shiftr_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat8is_neg64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5sra63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5shl64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat<wrap64_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common=shr64_range64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec;Z_lor_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib6Common9SoftFloat5add64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat<clz64_mirrorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5sub64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6sext32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common;mk128_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegC59OSSVerify5KrLib3Lib8PropExec<Z_lxor_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common;sra63_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Bytes<land_lt_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat9f128_of_dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat6INF_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat;IMPLICIT_HIC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC59OSSVerify5KrLib6Common;SFW1_lemmas:swrap32_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge=Z_to_bv_mod64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4zx32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_diagC56Stdlib6ZArith6BinInt1Z:land_assocC59OSSVerify5KrLib6Common<F_fmt_fp_libCbytes_le_to_Z_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib6Common<F_fmt_fp_libBZ_to_le_bytes_to_ZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common<le8_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;printf_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib6Common<Printf_model9parse_dirC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4convC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model3dir00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8fp_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_flC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lnotC59OSSVerify5KrLib6Common<Printf_model3d_wC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib6Common<Printf_model3d_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8LEFT_ADJC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8ZERO_PADC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5PlainDF_printf_core_common;In_firstn_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common:In_skipn_wC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List9skipn_mapC46Stdlib5Lists4List<firstn_skipnC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat5min_lI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5Plain=Printf_zfacts?parse_dir_shapeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8is_digitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;parse_flagsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_xpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model9conv_typeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_tyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model6getintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Printf_zfactsAgetint_some_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9Stdio_kitBrw_cells_bytes_at'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@bytes_at_ov_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib5Plain9F_pop_arg;firstn4_le8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8firstn_0C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getc59OSSVerify5KrLib5PlainDF_printf_core_common3FokC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common4POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4mpadC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib5PlainDF_printf_core_common;Forall_znthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image@ro_bytes_b_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;ro_bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Printf_zfacts7STATES0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Printf_zfacts?conv_type_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common=states0_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common;zbytes_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Printf_zfacts<states0_convC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common6PFXSTRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common9pfx_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common<bytes_at_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common8zb_skipnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common9zb_firstnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common=xdigits_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common3JT1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common9jt1_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idc59OSSVerify5KrLib5PlainDF_printf_core_common9zb_lengthC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01c59OSSVerify5KrLib5PlainDF_printf_core_common<jt1_read_litC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib6Common<Printf_model5T_DBLC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib6Common<Printf_model5T_PTRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model5T_INTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model6T_UINTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;SFW1_lemmas<zb_land_pow2C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool3eqbc59OSSVerify5KrLib5PlainDF_printf_core_common<nzmask_bits'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1Z9lnot_specC56Stdlib6ZArith8Zbitwise1Z?sub_land_same_lC56Stdlib6ZArith6BinInt1Z7lxor_eqC56Stdlib6ZArith6BinInt1Z>lxor_nilpotentc59OSSVerify5KrLib5PlainDF_printf_core_common?land_lxor_distrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface?sink_frame_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface6arg_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K59OSSVerify5KrLib6Common<Printf_model4parg02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface7args_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common8arg_ok_WC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common8lo_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common:lo_cells14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5Plain9F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9F_pop_arg=va_area_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_SomeC59OSSVerify5KrLib5Plain9F_pop_arg<pop_arg_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9F_pop_arg<pop_arg_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common4FokdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9F_pop_arg:pop_arg_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9F_pop_arg:pop_arg_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun9memchr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9F_strnlen<strnlen_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9F_strnlen<strnlen_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun;strnlen_resC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffc59OSSVerify5KrLib5PlainDF_printf_core_common6u8_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC59OSSVerify5KrLib5Plain>F_printf_iface8out_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common9out_postqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface8out_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface9OUT_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles;GLOBALS_TOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface;fpcall_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface;fpcall_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainDF_printf_core_common8fp_postqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9Stdio_kit<FMT_FP_DEPTHC1?~~~~~~~~~~~~~~~".
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
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM psegs c s Q ms) | _ => idtac end.

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
  bytes_at psegs m A (zb l) -> (0 <= i < zlength l)%Z -> a = wa (A + i) ->
  ov_read_bytes psegs m a 1 = Some [Z_to_bv 8 (znth l i)].
Proof.
  intros m A l i a HB Hi ->.
  eapply (u8ro_read psegs m A (zb l) i); [exact HB | | lia | reflexivity].
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

Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells psegs m A [CB n bs] -> length bs = n.
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
Lemma cb8_c8_in : forall m A pre post bs, rw_cells psegs m A (pre ++ CB 8 bs :: post) -> rw_cells psegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
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
  bytes_at psegs m A l -> (k <= length l)%nat ->
  bytes_at psegs m (A + Z.of_nat k) (firstn n (skipn k l)).
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
  rw_cells psegs m A (pre ++ C8 w :: post) -> a = wa (A + Z.of_nat (cells_size pre)) ->
  ov_read_bytes psegs m a 4 = Some (le4 w).
Proof.
  intros m A pre w post a H ->.
  apply (proj1 (rw_cells_app psegs m A pre (C8 w :: post))) in H. destruct H as [_ H].
  pose proof (rw_cells_bytes_at' _ _ _ _ H) as Hb. cbn [cells_bytes cbytes] in Hb.
  pose proof (bytes_at_ov_read psegs m _ _ 0 4 Hb) as R. rewrite Z.add_0_r in R.
  rewrite R. 2:{ cbn [skipn]. rewrite length_app, length_le8. lia. }
  change (skipn 0 (le8 w ++ cells_bytes post)) with (le8 w ++ cells_bytes post).
  rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r, firstn4_le8. reflexivity.
Qed.

Lemma bytes_at_nil : forall m a, (0 <= a)%Z -> (a <= 2^64)%Z -> bytes_at psegs m a [].
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
  Hypothesis HA : (A + zlength fmt <= 155648)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((156856 <= Fp /\ Fp + 232 <= 359072) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((359080 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
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
               Ft (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ munch W m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
      /\ frm0 fc' /\ Fok Ft
      /\ stk psegs m' lo q
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ rw_cells psegs m' AP [C8 apv]
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
    mem_inv psegs m /\ munch W m0 m /\ wmono psegs m0 m
    /\ rw_cells psegs m (q + -112) hi_cells
    /\ stk psegs m lo (q + -544)
    /\ bytes_at psegs m A (zb fmt)
    /\ va_area m VA slots
    /\ rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 canary].
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
  Lemma states0_bytes : forall m, mem_inv psegs m -> bytes_at psegs m 0x10910 (zb STATES0).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h07__arithh14__ffh28__varmaph35__with42MIh51mp;1p;2p;4p;3p;8p;7p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej11Tg008Jj16Tg008hj17Tg00>Aj1QTg044]j2OTg00U>j12Tg013Gj13Tg00:1j1ATg00Emj1@Tg007Ej1?Tg01Bkj1=Tg00Fkj1<Tg00GIj1PTg00HWj24Tg00I:j4;Tg00JGj2NTg00@Gj2KTg00Jij2ETg00;Lj39Tg00KUj3DTg00L4j4CTg00A_j25Tg01CIj3BTg01eoj3FTg00dZj28Tg01e2j2GTg00:lj2HTg00N^j1ITg045Qj3JTg046Jj4>Tg047Ij8LTg00WXj7MTf0R0#1#1p=0f1R1g00[Pg00[oR2P2g00\OR2P0g00\oFMp=:g00<DR3#1R4#0R5#1#0R6#6R7#7%65#7R5#Q[g00j;R8/O0P8P1%03#0#2#0#2#1#0#2#0#0#3R9g048A#AR:P0g00_>R;#@R<%?;R;g00;fR=#=R>%<=R?%P=R@P=g00[2RA,4=g00`QRB14=9RCC;':1N@2R2P0f2RDg00^^REg00a8RF'KRG1E0D=9EFdAD=A1CCR1b1b2b315A9P0b0P<P;P>P?P=%23#2#1#2#1#3R3,4=9B=CPB%34R4,4==F=7C;,:@P2P1b1b2b31893%36,G4R4'5P0b01H5:#I,89/54eP8P:P9PGAJ89:=9EFdC>GLW4W5o"). Qed.
  (* [comment removed for export] *)
  Lemma states0_read : forall m t ty, mem_inv psegs m -> conv_type t = Some ty ->
    ov_read_bytes psegs m (wa (t + 67856 + -65)) 1 = Some [Z_to_bv 8 ty].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h04__x1h17__arithh24__ffh38__varmaph45__with52tyh62CTh72MIh81Rh91mh:1tp;1p;2p;3p;4p;8p;6p;7p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej10Tg008Jj1?Tg008hj1ETg00>Aj1;Tg044]j2XTg03bMj1UTg00?Aj2BTg00;Lj37Tg049Aj3LTg00U>j11Tg013Gj18Tg00A_j25Tg00COj2>Tg01?fj2=Tg00VGj2YTg007Ej1FTg00dZj23Tg01ACj1VTg00e7R0j1DTg00Qcj1TTg00efj4STg009Kj2QTg00Emj1ATg00T@j3PTg04:Ij2OTg00FMj2NTg00Fkj1MTg00GIj1KTg00HWj24Tg00H4j2JTg00Iej1ITg01Clj3HTg00I:j4:Tg00YDj8GTg00JGj2RTg00@Gj2CTg00Jij2bTg00KUj3aTg00L4j4`Tg00C3j2_Tg01CIj3<Tg01FIj8^Tg04;Vj8ZTg04<aj3[Tg002Tj6\Tg00WXj7WTg00X`j7]Tf0R1#0#0p=2g00;fR2f1R3g00`QP1C:p=9P3g00[PR4g00[oR5P5g00\OR6P1g00\oFWp=6f2R7P4P5P5P6P3P1F]p=@g00<DR8#0#2R9#2R:#0#?#ER;%?9R9#ER<#;[g00j;R=/X7%;2%U71B2337f3R>?L71%1:R:#8R?/5>%18#1R@#1#0#1#0#8RA,5>'>P2g048ARBf4RC/=?RD'Y%F<RE#;P=f6f5R=%28#2#1#2#1#0#2#1#2#2#8RF'3%V:R:'3#Dg00b3#TCS1Q91%A<5P<,BE37X52P=PFPBPD13CF/3:RB#D1O=7g00_>RE#AR<%FERE1N23R9%M2RG%K2RHP4P5P5P6142?R41J28R8'9,6H142A,98,6H5@H%I5g00[2R5,42AH284R4'9,6HP2P4g00_j%0@#1#0#8R@,42C:,6H5@HGG1RH6R6P1P7g00^^RIg00a8RJ'C1b17=7IJdAa253C`RJb2b3b4X0215?1151A'>1=3?RA,551_A@'>[^02P1P=P3O2b1P2P;P0P0PB13FDP;\2/C0P<PEP9PGP2142FRG9<28142:5<2g00c>A<2G4C:,6HP6PJb2b3b4X02131F/3:1=1?,3F572^02P1P=O1b1G^GZP>A[C>3E\b8W6W7X52X:2W9o"). Qed.

  (* [comment removed for export] *)
  Definition PFXSTR : list Z := [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z.
  Lemma pfx_bytes : forall m, mem_inv psegs m -> bytes_at psegs m 66200 (zb PFXSTR).
  Proof.
    clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  Qed.
  Lemma pfx_sub : forall m k n, mem_inv psegs m -> (k + n <= 9)%nat ->
    bytes_at psegs m (66200 + Z.of_nat k) (zb (firstn n (skipn k PFXSTR))).
  Proof.
    clear. intros m k n MI Hk. rewrite zb_firstn, zb_skipn. apply bytes_at_sub; [apply pfx_bytes; exact MI|]. cbn. lia.
  Qed.
  Lemma xdigits_bytes : forall m, mem_inv psegs m -> bytes_at psegs m 68320 (zb XDIGITS).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h07__arithh14__ffh28__varmaph35__with42MIh51mp;1p;2p;4p;3p;8p;7p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej10Tg008Jj16Tg008hj17Tg00>Aj1QTg044]j2OTg00U>j12Tg013Gj13Tg00:1j1ATg00Emj1@Tg007Ej1?Tg01Bkj1=Tg00Fkj1<Tg00GIj1PTg00HWj24Tg00I:j4;Tg00JGj2NTg00@Gj2KTg00Jij2ETg00;Lj39Tg00KUj3DTg00L4j4CTg00A_j25Tg01CIj3BTg01eoj3FTg00dZj28Tg01e2j2GTg00:lj2HTg00N^j1ITg045Qj3JTg046Jj4>Tg047Ij8LTg00WXj7MTf0R0#0#0p=1f1R1g00[Pg00[oR2P2g00\OR2P0g00\oFMp=:g00<DR3#0R4#1R5#0R6#1R7#6R8#7%65#7R5#Q[g00j;R9/O0P9P1%13#1#2#0#2#0#2#2#2#0#1#1#3R3g02UT#AR:P0g00_>R;#@R<%?;R;g00;fR=#=R>%<=R?%P=R@P=g00[2RA,4=g00`QRB14=3RCC;':1N@2R2P0f2RDg00^^REg00a8RF'KRG1E0D=9EFdAD=A1CCR1b1b2b315A3P0b0P<P;P>P?P=%36R6,4=9B=CPB%34R4,4==F=8C;,:@P2P1b1b2b31836%37,G4R4'5P0b01H5:#I,83/54eP9P:P3PGAJ93:=9EFdC>GLW4W5o"). Qed.
  Lemma xdigits_read : forall m v, mem_inv psegs m -> (0 <= v < 16)%Z ->
    ov_read_bytes psegs m (wa (68320 + v)) 1 = Some [Z_to_bv 8 (znth XDIGITS v)].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h04__x1h12Hvh22MIh37__arithh44__ffh58__varmaph65__with71mh81vp;1p;2p;4p;7p;8p;3p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej10Tg008Jj18Tg008hj1<Tg00>Aj1QTg044]j2LTg00A_j26Tg013Gj17Tg00C3j25Tg00COj2:Tg00U>j12Tg00dZj2>Tg00e7j1=Tg04CRj2PTg00Emj1OTg007Ej1NTg00FMj2KTg00Fkj1HTg00GIj1GTg00HWj29Tg00H4j2ETg00I:j44Tg00X`j7DTg00Iej1CTg00YDj8BTg00JGj2FTg00@Gj23Tg00Jij2ATg00;Lj3ITg00KUj3JTg00L4j4@Tg04;Vj8?Tg00WXj7MTf0R0#0#0p=1f1R1g00[PR2g00[oR3P3g00\OR4P0g00\oFMp=;g00<DR5#0#1R6#0R7#1#8#<R8%86#<#Q[g00;fR6g00j;/L1g00[2R9/61%77R7,51':R:f3R;%15#1#2#0#2#0#2#2#2#0#1#1#7R<g02UTf2R=1><=#=R<1P;1g00_>R>#O%N>1K61%H6%G6R>P2P3P3P4P>P2P3P3P4P61969g00`Q1E65R5C4,;>P6P5g00_j1967C4,;>FDR5%C3P5GB1F>4P0P=g00^^R>g00a8R4'31A0==I>4dAJ691C@b4b5b6X0616901507':P:[^06P0P;P1O2b3138<G?W1W2W8W7o"). Qed.

  (* [comment removed for export] *)
  Definition JT1 : list Z := [160; 255; 0; 0; 32; 0; 1; 0; 64; 1; 1; 0; 32; 0; 1; 0; 160; 255; 0; 0; 160; 255; 0; 0; 160; 255; 0; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 4; 2; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 160; 1; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 160; 255; 0; 0; 32; 0; 1; 0; 96; 1; 1; 0; 240; 255; 0; 0; 160; 255; 0; 0; 160; 255; 0; 0; 160; 255; 0; 0; 32; 0; 1; 0; 240; 255; 0; 0; 32; 0; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 76; 0; 1; 0; 236; 0; 1; 0; 152; 0; 1; 0; 140; 1; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 56; 0; 1; 0; 32; 0; 1; 0; 40; 1; 1; 0; 32; 0; 1; 0; 32; 0; 1; 0; 160; 1; 1; 0]%Z.
  Lemma jt1_bytes : forall m, mem_inv psegs m -> bytes_at psegs m 67528 (zb JT1).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h07__arithh14__ffh28__varmaph35__with42MIh51mp;1p;2p;4p;3p;8p;7p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej12Tg008Jj16Tg008hj17Tg00>Aj1QTg044]j2OTg00U>j11Tg013Gj13Tg00:1j1ATg00Emj1@Tg007Ej1?Tg01Bkj1=Tg00Fkj1<Tg00GIj1PTg00HWj24Tg00I:j4;Tg00JGj2NTg00@Gj2KTg00Jij2ETg00;Lj39Tg00KUj3DTg00L4j4CTg00A_j25Tg01CIj3BTg01eoj3FTg00dZj28Tg01e2j2GTg00:lj2HTg00N^j1ITg045Qj3JTg046Jj4>Tg047Ij8LTg00WXj7MTf0R0#2#2p=0f1R1g00[Pg00[oR2P2g00\OR2P0g00\oFMp=:g00<DR3#2R4#0R5#2#0R6#6R7#7%65#7R5#Q[g00j;R8/O0P8P1%23#0#0#1#1#1#1#1#0#1#2#0#3R9g04D_#AR:P0g00_>R;#@R<%?;R;g00;fR=#=R>%<=R?%P=R@P=g00[2RA,4=g00`QRB14=9RCC;':1N@2R2P0f2RDg00^^REg00a8RF'KRG1E0D=9EFdAD=A1CCR1b1b2b315A9P0b0P<P;P>P?P=%13#1#2#0#0#3R3,4=9B=CPB%34R4,4==F=7C;,:@P2P1b1b2b31893%36,G4R4'5P0b01H5:#I,89/54eP8P:P9PGAJ89:=9EFdC>GLW4W5o"). Qed.
  Lemma jt1_read_lit : forall m (t : Z) bs, mem_inv psegs m -> (65 <= t <= 120)%Z ->
    firstn 4 (skipn (Z.to_nat (4 * (t - 65))) (zb JT1)) = bs ->
    ov_read_bytes psegs m (wa (67528 + 4 * (t - 65))) 4 = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h04__p1h14__x1h21Rh37__arithh44__ffh54__p2h64__p3h78__varmaph85__with94__x2h:2bsh;1xh<1Hh=2H0h>2Hth?2MIh@1mhA1nhB1thC1zhD2z0p&0p;1p;2p;3p;4p;7p;6p;8p;<p;Bp103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej13Tg008Jj1UTg008hj1OTg00>Aj1]Tg007Ej1YTg044]j2oTg00U>j12Tg013Gj1@Tg00A_R0j24Tg00COj28Tg01?fj26Tg01ijj27Tg00EMR1j1ATg00:1k101Tg016ij3=Tg01[Hj3?Tg00;Lj31Tg00dZR2j2<Tg00e7j1ETg00efj4CTg00?Aj2DTg04Ebj2gTg03iOj7fTg013ej2BTg00:lj2[Tg00MaR3j29Tg00N^R4j1bTg00RBj2TTg00Rkj3STg00STj2aTg01nNj2PTg00Emj1`Tg00T@j3NTg00FMj2QTg00Fkj1_Tg00GIj1^Tg00HWj2>Tg00H4j2MTg00Iek102Tg01Clj3\Tg01o:j3ZTg00JGk200Tg00@Gj2FTg00Jij2|Tg00KUj3{Tg00L4j4yTg04Fkj2xTg002Tj6XTg00O>j2KTg00Pgj2kTg00C3j2VTg00QIj2WTg01Bkj1jTg00T`j4iTg00I:j4LTg00Ucj7hTg01CIj3qTg00lbj4rTg04GIj1sTg0030j6tTg00Qcj10Tg00WXj7wTg00X<j6eTg00X`j7dTg00YDj8zTg00Yhl<cTg01JUlB}Tg00ZMl<~Tf0R5#3#3p=5%05#0p=Rg00;fR6f1R7g00`QP5CLp=IP7g00[PR8g00[oR9P9g00\OR:P5g00\oFwp=;P7P8P9P9P:P5Eep=Hf2R;P8P9P9P:P7P5Fdp=Gf3R<P8P9P9P:P;P7P5Gzp=J%05#0#0#0p=v%05#0#0#0#0#0#0#0p=u%05#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=p%05#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=:P6g00<iR=P6P6P1f4R1P4P<g00]OP;P7P5M<cp=nP=P=P=P6P6P6g01GkP4P4P4P2g01K_f5R2P1P<P;P7P5MB}p=mP=P6P3P4P0g00^<P2P1P<P;P7P5M<~p=lg00<DR0#3R4#3R3#3R>#5R?#3#U#O%U>#OR>#][%Y>R@g00j;RA/o;%2?#@R?/4;%20#2RB#2#3#5#@RC,4;RD'8g00b3RE#RRF#RRG%@3R316<?'7#Ag04D_RH$01RI5=>5?>=1@;P@161?,73#ARJ==>I9?>G%]@RKPAf6RL%30#5#5#2#2#2#2#2#5#2#3#5#@RM162?,73RN'<#EPGCC1D@531X:@PAP2PMPIPJPG1g2;Ff1BJG1[>IRJ'9PAPL%ANRO#bRP,<M#EPGCCA=>OI9?>G,D@51K[P6PP16L?,73RP#ARQ/BGRR/9JPAf81<M7#EPGCCf7RS/6?,73RT#ARU==>I9?>G,D@51K[XC6P5PNp-0RVg00_>RW1T6ERE1T6FRF9S6Eg00bR'aRX'P%`WRY3N%YWRZ1Q67%_6R[%^6R\1>6?R]1M60R0'I,;\1H\<5G\&029R^g00[2R_,>6R`1>63RaA\60]5Z6'I,;\CJ200\:RbP5P;g00^^Rcg00a8Rd'F1|5;=1cddA{6_7CyRdb4b7b8X16W014?5/87167?,73Rc,4_[^16^0VP514LCPLP<O3b3,xNEX1BOG/9JPAPS1<MP#EPGCCA=>QI9?>G,D@51K[P5P=1[6HRK1BUG/95XA=%vG#u#p#:#:#:#:#:#:R=,9R1K_PRU/<3R@%3B#5#5#@RB'4PRP@PQPUP5X;61K_5X;6PPPP1F6PDnPGP31F63EmP=PB1F6BEl1k_P1V_PA16UP'814P_A16U_'8'W1K_TP6AS6FE/PX=NWYPZP61Q6;P7%j6CiP[P\P\P8P9P9P:1H\1P6P0g00c>R11M64R4=\6]9Z6aCL,;\5G\1H\2P6P0P1P`CL,;\5G\FhP^P\1H\L1>6C,I4,;\5G\P^Aq60a1>6B'I,;\CJCJPbPdb4b7b8X16X96X0VX5VX6VA165c,8;A165_,8<'W182D1<;3/4B[[^16^96^0V^5V^6VP5f9RV,4?16V?,73R3/4_1V_3PVP7P;PLO7b3bDb=Cr19RKePJ%sHEtO1b2b2P<P5EXW<W>W?W:XB6W@o"). Qed.
  Lemma jt1_read_s : forall m t, mem_inv psegs m -> t = 115%Z -> ov_read_bytes psegs m (wa (67528 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 56; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h01th11Hh22MIh37__arithh44__ffh58__varmaph65__with71mp;1p;2p;3p;4p;7p;6p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej11Tg008Jj1@Tg008hj1?Tg00>Aj1FTg044]j2UTg013Gj12Tg00;Lj36Tg007Ej1=Tg00U>j15Tg01?fj2ATg01ijj2CTg00dZj2[Tg00e7j1VTg00Qcj17Tg00efj4TTg009Kj2:Tg00Emj1BTg00T@j33Tg00?Aj2QTg01Bkj1PTg00Fkj1OTg00GIj1NTg00HWj28Tg00I:j4>Tg00X`j7MTg00JGj2LTg00@Gj2DTg00Jij2KTg00KUj3JTg00L4j4ITg00A_j2ETg00COj2HTg04HRj29Tg04IEj3;Tg00EMj1GTg00:1j1RTg016ij3STg01[Hj3ZTg04Ihj6YTg0030j6XTg00WXj7WTf0R0#1#1p=0%50#5p=4f1R1g00[PR2g00[oR3P3g00\OR4P0g00\oFWp=<g00<DR5#0R6#1R7#0R8#1#@#?%@7R7#?R9#F[g00;fR:g00j;R;/U1%45R<#0#4#2R=96:1P:P=%=9R>#FP;f4%15#0#0#5#4#4#0#5#1#0#2%26R6%58#2R8,A0'C'[#Vg00b3#7#7#7#7R;CT%45#1#0#2,:7g00[2R?,:7R@%25RA,:7%B9RB939@539539539R@,Q>36X0:f3P=P@P1g00_>RC#B%=C%P:%O:%N:RCP2P3P3P4P:18:8g00`QR318:=R2C>,<CP:P2P3%5<#1#0#2R<,8:C>,<CFM1LC4P0f2RCg00^^R4g00a8R3'D1K0C=643dAJ:?1CIb4b5b61E8=1E=<'HP0b3%45#1#0#2%45#1#0#2,975;7197?9;7?R?197A9;7AA39?B539539539,D>1A=8,C6#Gg04D_#R5S99Z9;=6>@dEYPCP0EXW1W2W0W7o"). Qed.
  Lemma jt1_read_d : forall m t, mem_inv psegs m -> (t = 100 \/ t = 105)%Z -> ov_read_bytes psegs m (wa (67528 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 240; Z_to_bv 8 255; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h01Hh17__arithh24__ffh38__varmaph45__with51th62MIh71mp;1p;2p;4p;3p;6p;7p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej13Tg008Jj1GTg008hj1MTg00>Aj1QTg044]j2[Tg00U>j11Tg013Gj12Tg00QIR0j2VTg007Ej1DTg01?fj2<Tg01ijj2=Tg00dZj2JTg00e7j1LTg00Qcj1;Tg00efj4KTg009Kj2@Tg00Emj1ITg00T@j34Tg00?Aj2ZTg00;Lj36Tg01Bkj1YTg00Fkj1XTg00GIj1WTg00HWj29Tg00JGj2UTg00@Gj2ETg00Jij2TTg00KUj3STg00L4j4RTg00A_j2>Tg00COj2CTg04HRj2ATg04IEj3?Tg00EMj1BTg00:1j1_Tg016ij3PTg01[Hj3OTg04Ihj6NTg0030j6HTg00I:j4^Tg00WXj7]Tg00X`j7\Tf0R1#3#3p=0g00;fR2f1R3;61p=7%11#1p=5P2P3g00`QP1C^p=:P3g00[PR4g00[oR5P5g00\OR6P1g00\oF]p=8f2R7P4P5P5P6P3P1F\p=Fg00<DR5#0R4#3R8#0R9#3#G#M%G8R8#MR:#Q[g00j;R;/[3%15R<#3R=#3#1#0#2R>,73%1=#0#1#2R=,73'VP0177>177=%D:R0#QR?P;f4R@%35#0#0#1#5#5#0#1#3#0#2RA%24R4f3RB%19#2R9'<'='J#Lg00b3#;#;#;#;RCCK%15#5#0#0#2,@8%5<R<#5#5#2RD,@8g00[2RE,@8RF%I:RG94:F54:54:54:RF,Z0RH36P117B>P2P>P;f61<19,=4,JA#LPCCK=6?HX52RHf5R?P>PFPBg00_>RA#IR;%DARA%Y2RI%X2RJ%W2RK1929RL192>RM':,8K%3<#0#2R<,92RN,:M,8K3F1UK6R6P1P7g00^^RMg00a8RO'E1T17=6MOdAS2E3CRR3b2b3b41>9>1>><'CP1b1%15#5#0#0#2%15#5#0#0#2,A85?81A8D9?8D1A8E9?8EREA4:EG54:54:54:,E0RE1<>9,=4#Bg04D_#_R>5P:9O:C=60FdENP@P1EHW0P1O117B=P2P=PHP?P=PFPBP;PAPIPJ192=RJ,:L,8K1:JN,8K5FKP6P3b2b3b41>9=1>=<'CP1b1PE1<=9,=4#B=P:>9O:C=60FdENP@P1EHW0P1O1n200100000021100011000W0W6X52W7o"). Qed.
  Lemma jt1_read_u : forall m t, mem_inv psegs m -> t = 117%Z -> ov_read_bytes psegs m (wa (67528 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 40; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h01th11Hh22MIh37__arithh44__ffh58__varmaph65__with71mp;1p;2p;3p;4p;7p;6p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej10Tg008Jj1@Tg008hj1ATg00>Aj1ETg044]j2UTg00U>j11Tg013Gj13Tg00;Lj35Tg007Ej1<Tg01?fj2;Tg01ijj2BTg00dZj2FTg00e7j1ZTg00Qcj16Tg00efj4VTg009Kj2:Tg00Emj1CTg00T@j34Tg00?Aj2QTg01Bkj1PTg00Fkj1OTg00GIj1NTg00HWj27Tg00I:j4?Tg00X`j7MTg00JGj2LTg00@Gj2=Tg00Jij2JTg00KUj3KTg00L4j4ITg00A_j2DTg00COj2HTg04HRj28Tg04IEj39Tg00EMj1GTg00:1j1RTg016ij3STg01[Hj3TTg04Ihj6YTg0030j6XTg00WXj7WTf0R0#0#0p=2f1R1g00[PR2g00[oR3P3g00\OR4P0g00\oFWp=>g00<DR5#2R6#0R7#2R8#0#@#A%@7R7#AR9#E[g00;fR:g00j;R;/U1%15#1R<#0#1#0#1#3R=95:1P:P=%<9R>#EP;f4%05#2#2#1#1#1#1#1#2#1#0#2#3%36R6%18#3R8,;0'B'F#Zg00b3#6#6#6#6R;CV%05#1#0#2#3,:7%35R?,:7R@g00[2RA,:7%C9RB549949@549549R@,Q>35X0:f3P=P@P1g00_>RC#C%<C%P:%O:%N:RCP2P3P3P4P:17:8g00`QR317:=R2C?,>CP:P2P3%1<#0#2#3R<,7:C?,>CFM1LC4P0f2RCg00^^R4g00a8R3'=1J0C=543dAK:A1CIb4b5b61D8=1D=<'HP0b3%05#1#0#2#3%05#1#0#2#3,87597187?997?R?187A997A=49B949?549549,=>1;=8,B6#Gg04D_#R5S99T9;=5>@dEYPCP0EXW1W2W0W7o"). Qed.
  Lemma jt1_read_x : forall m t, mem_inv psegs m -> (t = 120 \/ t = 88)%Z -> ov_read_bytes psegs m (wa (67528 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 160; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "h01Hh17__arithh24__ffh38__varmaph45__with51th62MIh71mp;1p;2p;4p;3p;6p;7p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej10Tg008Jj1GTg008hj1BTg00>Aj1KTg044]j2[Tg00U>j11Tg013Gj13Tg00QIR0j2VTg007Ej1CTg01?fj27Tg01ijj29Tg00dZj2PTg00e7j1HTg00Qcj18Tg00efj4LTg009Kj2>Tg00Emj1ITg00T@j34Tg00?Aj2ZTg00;Lj35Tg01Bkj1YTg00Fkj1XTg00GIj1WTg00HWj2=Tg00JGj2UTg00@Gj2JTg00Jij2TTg00KUj3STg00L4j4RTg00A_j2<Tg00COj2ATg04HRj2?Tg04IEj3@Tg00EMj1ETg00:1j1QTg016ij3OTg01[Hj3NTg04Ihj6FTg0030j6MTg00I:j4^Tg00WXj7]Tg00X`j7\Tf0R1#0#0p=2g00;fR2f1R3;51p=6P2P3g00`QP1C^p=:P3g00[PR4g00[oR5P5g00\OR6P1g00\oF]p=;f2R7P4P5P5P6P3P1F\p=Dg00<DR5#0R4#0R8#0R9#2R:#0#G#B%G9R9#BR;#K[g00j;R</[3%15#1#1#0#2#3R=,63%14#1#0#2#3R4,63'VP0167=1674%C;R0#KR>P<f4R?%05#2#2#1#1#1#1#1#2#1#0#2#3R@%38R8f3RA%1:#3R:'7'9'P#Hg00b3#8#8#8#8RBCL%05#1#0#2#2#3,>9%35RC,>9RDg00[2RE,>9%I;RF54;94;D54;54;RD,Z0RG35P116A=P2P=P<f6171:,98,P@#HPBCL=5>GX52RGf5R>P=PDPAg00_>R@#IR<%C@R@%Y2RH%X2RI%W2RJ1=2:RK1=2=RL':,;J1:LL,;J3D1UJ6R6P1P7g00^^RMg00a8RN'J1T17=5MNdAS2E3CRR3b2b3b41<:=1<=='AP1b1%05#1#0#2#2#3%05#1#0#2#2#3,?95@91?9C9@9CRC1?9E9@9E=4;F94;C54;54;,J0RC17=:,98#Eg04D_#QRF5O;9N;B=50DdEFP?P1EMW0P1O116A4P2P4PGP>P4PDPAP<P@PHPI1=24RI,:K,;J1:IL,;J5DJP6P3b2b3b41<:41<4='AP1b1PC174:,98#E=O;F9N;B=50DdEFP?P1EMW0P1O1n200100000021100011000W0W6X52W7o"). Qed.
  Lemma jt1_read_fp : forall m t, mem_inv psegs m -> conv_type t = Some T_DBL -> ov_read_bytes psegs m (wa (67528 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 160; Z_to_bv 8 255; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "p'0h05Heqb2h11Hh24Heqbh35Heqb0h45Heqb1h52CTh67__arithh74__ffh88__varmaph95__with:1th;1bi001bh<1eh=1mh>2b1h?2b2h@1nhA2MIi011oi021pi031zp%0p;1p;2p;3p;6p;4p;7p;9p103o^p6051002R0p1003Np4p710p8P0p1040bp4p710p8g007ej18Tg008Jj1cTg008hj1`Tg00>AR0j1^Tg044]j2tTg03bMj1oTg00?Aj2QTg00;Lj31Tg00U>j14Tg01Ylj20Tg00@Gj2_Tg013Gj1RTg00Iej1mTg007Ej1eTg00Qcj1VTg009Kj2]Tg00Emj1bTg00T@j3DTg002Tj6UTg01T`j2TTg00QIR1j2ETg04K4j2iTg04KTj2{Tg01Bkj1yTg00Fkj1xTg00GIj1uTg00JGj2sTg00Jij2rTg00KUj3qTg00L4j4pTg00A_j2:Tg00COR2j2OTg04HRj2ZTg04IEj3XTg00EMj1LTg00:1j1nTg016ij3NTg01[Hj3KTg04Ihj6MTg01ZIj23Tg01?fj2\Tg01ijj2YTg00dZj2dTg00e7j1fTg00efj4gTg00HWj2lTg00I:j4kTg00WXj7jTg00X`j7vTg0030l9wTf0R3#8#8p=9%83#4p=H%43#Rp==g00^^R4f1R5;13p=F%83#Rp=?f3R6f2R7'01053'3p=5f5R8f4R9'01067'31053'3p=>f7R:f6R;'01089'3/36/37/35/33p=A%43#4p=[g00j;R<P;1\67,Y9,d8#fP5Cg=1:3p=@g00a8R=9143p=2g012gR>9143p=<1353=14=p=a1096,38/37/35/33p=h1096/37/35/33p=W1053,37=14=p=C1053=14=p=6g00;fR??153p=B1053,37=14>p=71\53,Y7,d6#fp=zP<P6P7P5Cg=193p=S1l?3p=GP7g00[PR>g00[oR@P@g00\ORAP?P5g00`QP3Ckg00\oFjp=;P7P>P@P@PAP5P3Fvp=I1\53,Y7p=PP?P:P;P8P9P6P7P5P3M9wp=Jg00<DR@#8R>#8RB#8RC#9RD#8#c#`%cCRE#`RF#^[1t<5%^?R<%o5g04L4,Q?31%4@RG#4RH#8RI#H#=RJ,07P41_43RK106J/F3P4108J/F3P4P<P5%=B,Q?RLP4P<P;%8GRG#HRM#8RN#?ROP;%4G#9#=RGC5RP%4>R>#?,Q?RQP4P<P;%4I#8#=RIP;%4HRH#9#?RRP;%4>R>#9#?RSE>%R>,Q?R>P4P<P;%=NRNP;%4MRT#?RU%=TRT,0;%4CRC#8#=RV,0;%4CRC#?RW,0;%=CRC,0;GA%RM,Q?RM%m?R;n0100000020000n0100000020000n0100000020000n0100000020000=1<M%eFRX#^RYf8RZ%9@#9#H#[#[#8#H#9#?R[%RBRBP:%=DRDg00b3#V#V#V#VR\%H@#9#9#?,]E%4H#[#=RH,]Eg00[2R],]ER^%bFR_9DF^5DF5DF5DFR^,QXR`G@Ra]5]2P5109JR9#2A1<LMP<PLP0P?p-0RLP3P?PLP3g01X3Rbg04M2RcPLP3PcPLP3PbPcPLP3PbPcPLP3PbPbg01WWRdn011020003100001000000Pbn011020003101021010200Pbn011020003101021010200PbPbn011020003101021010200Pbn011030003001010210102Pbn10110100021010300X<<g01XPRePMP3EUPb1Ta3b1W5W2%<9P4P<P8POP8PGC5PQP4P<P8PIP8PRP8PSE>P>P4P<P8PNP8PU108T108V108W108CGAPMP;n0100000020000n0100000020000n0100000020000=1<MPPP4PKP:POP:PGC5/F3P4f9R:POP:PGC5/F3P4P<P5PQP4P<f:RPPIPPPRPPPSE>R8P>P4P<PPPNPPPU10PT10PV10PW10PCGAPMP;n0100000020000n0100000020000n0100000020000=1<MPYf<RPP[PBf;R9PDP\P`G@Ra]5]3P5PZPOPZPGC5RZ#2A1<QMP<PQP0P?PLP3P?PLP3PbPcPLP3PbPdPbn011020003100001000000Pbn011030003001010210102Pbn10110100021010300X<<PePMP3EUPb1Ta3b1W5W3%<ZP4P<P:PIP:PRP:PSE>P>P4P<P:PNP:PU10:T10:V10:W10:CGAPMP;n0100000020000n0100000020000=1<MP8P4PKP9PIP9PRP9PSE>/F3P4f=R8PIP8PRP8PSE>/F3P4P<P5P>P4P<f>R:PNP:PU10:T10:V10:W10:CGAR:PMP;n0100000020000n0100000020000=1<MPYf@RZP[PBf?RaPDP\P`G@RQ]5]4P5PPPIPPPRPPPSE>RP#2A1<>MP<P>P0P?PLP3P?PLP3PbPcPLP3PcPLP3PdPbPbn011020003100001000000PbPbn011020003101021010200Pbn011030003001010210102Pbn10110100021010300X<<PePMP3EUPb1TQ3b1W5W4%<PP4P<P8PNP8PU108T108V108W108CGAPMP;n0100000020000=1<MP:P4PKPaPNPaPU10aT10aV10aW10aCGA/F3P4fARKPNPKPU10KT10KV10KW10KCGA/F3P4P<P5PMP;n0100000020000=1<MPYfDRKP[PBfCR:PDP\P`G@R8]5]0P5PZPNPZPU10ZT10ZV10ZW10ZCGARZ#2A1<MMP21a53%27RP%25RQ'E[Rc%23,EQ1a75RQ[%26/EP\Q1i53P5n2001000000120000000X?4X>4RQPc^?4^>4RcP310:NP:PU10:T10:V10:WEhRP10:CR>P7O3%2P%2>'EP1PKPN10KU10KT10KVDW?CKW16KCPYfFP[PBfERKPDP\P`G@P3PKPN10KU10KT10KVDW?CKWPQPcP3fGR>PN10>U10>T10>VDWRP10>WRfP5O3%2P%2f'EP1fHRfPNPfPUPfPTE>?CfV16fWPYfJS00P[PBfIRPPDP\P`G@P3PPPNPPPUPPPTE>?CPVPQPcP3fKRgPNPgPUPgPTE>Rh10gVRiP5O3%2h%2i'EP1fLRiPNPiPUC5?CiT16iVPYfNRhP[PBfMRjPDP\P`G@P3PjPNPjPUC5?CjTPQPcP3fORkPNPkPUC5Rl10kTRmP5O3%2l%2m'EP1fPRm/0N?CmU16mTPYfRRlP[PBfQRnPDP\P`G@P310nN?CnUPQPcP3fSRc/0NRQ10cURoP5O3%2Q%2o'EP1fTR1/6N161UPYfVRoP[PBfURQPDP\P`G@P316QNP216531B75[R21B531675Rp[1B67\p1{53P5n2001000000120000000X=?X@?RpP2^=?^@?R2P3fWRqPNP5O31BqNPN103J#<Rr105O?75GRsP7PIP7PRC5?77SRtPYf]P[PBP6PDCzR6P\P`DS]4]3]2X:?R[10NJ#<10NO?7NGPNPIPNPRC5?7NSf\RuPNP^fZRvg00_>Rw#bRx%ewRw%y?Ry%x?Rz%u?R{%GDR|%GNR}5;{%GRR~9;{}3I1s{ARAP3P71_4=1r37#2dAq?]5CpR=b7b8b91:DN1:NR'OP3b6%H@#9#9#?%H@#9#9#?,ZE5XE1ZEH9XEH1ZE]9XE]R]ADF]_5DF5DF5DF,_XR]APBND#Lg04D_#nRN5NF9KF\=1X^dEMW4W3W2fXR_P3PcPkPgGJb0b1W0P3O116QUPpP2P3PqPUP5O31BqUPUP[10UJ#<10UO?7UGPUPIPUPRC5?7USPuPUP^PvPxPwPyPz%GURv9;{|A;{v~5I{PAP=b7b8b91:DU1:UR'OP3b6P]APBUD#L=NFN9KF\=1X^dEMW4W3W2P_P3PcPkPgGJb0b1W0P3O1n200100000021100011000b0b1W0P3O116nTPpP2P3PcPTP5O31BcTPTPYfYP6P\P`DS^4t^3s^2rX:?10TJ#<10TO?7TGPTPIPTPRC5?7TSP_PTP^PoPxPwPyPz%GTRo9;{|A;{o~5I{PAP=b7b8b91:DT1:TR'OP3b6P]APBTD#L=NFN9KF\=1X^dEMW4W3W2P1P3PkPgP>GJb0b1W0P3O1n200100000021100011000b0b1W0P3O116jVPpP2P3PkPVP5O31BkVPVPYPQP6P\P`DS^4t^3s^2rX:?10VJ#<10VO?7VGPVPIPVPRC5?7VSP1PVP^PlPxPwPyPz%GVRl9;{|A;{l~5I{PAP=b7b8b91:DV1:VR'OP3b6P]APBVD#L=NFN9KF\=1X^dEMW4W3W2PmP3PgP>P:GJb0b1W0P3O1n200100000021100011000b0b1W0P3O116PWPpP2P3PgPWP5O31BgWPWPYPnP6P\P`DS^4t^3s^2rX:?10WJ#<10WO?7WGPWPIPWPRC5?7WSPmPWP^PhPxPwPyPz%GWRh9;{|A;{h~5I{PAP=b7b8b91:DW1:WR'OP3b6P]APBWD#L=NFN9KF\=1X^dEMW4W3W2PiP3P>P:PaGJb0b1W0P3O1n200100000021100011000b0b1W0P3O116KCPpP2P3P>PCP5O31B>CPCPYPjP6P\P`DS^4t^3s^2rX:?10CJ#<10CO?7CGPCPIPCPRC5?7CSPiPCP^Q00PxPwPyPz%GCRz9;{|A;{z~5I{PAP=b7b8b91:DC1:CR'OP3b6P]APBCD#L=NFN9KF\=1X^dEMW4W3W2PfP3P:PaP9GJb0b1W0P3O1n200100000021100011000b0b1W5W0%<ZA1<;MP<P;P0P?PLP3PbPdn10110100021000000X<<PePMP3EUPb1T83b1W5W0n0110001020101P3P7O2b0b;W5W4n0110001020101P3P7O2b4b;W5W3n0110001020101P3P7O2b3b;W5W2n0110001020101P3P7O2b2b;W5WAX:?W=o"). Qed.

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
  Lemma implM_eq_ms : forall {X} (c : M St X) s Q ms ms', ms = ms' -> implM psegs c s Q ms' -> implM psegs c s Q ms.
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
    SINK m st -> munch Wc m m' -> wmono psegs m m' ->
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
    rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
    rw_cells psegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) /\
    rw_cells psegs m (q + -544 + 112) [C8 alo; C8 ahi] /\ rw_cells psegs m (q + -544 + 128) [CB 24 j128].
  Proof.
    clear. intros. unfold lo_cells in H.
    apply (proj1 (rw_cells_app psegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add app] in H2.
    change (Z.of_nat 112) with 112%Z in H2.
    apply (proj1 (rw_cells_app psegs m _ [_;_] _)) in H2. destruct H2 as [H2 H3]. cbn [cells_size csize Nat.add app] in H3.
    change (Z.of_nat 16) with 16%Z in H3.
    split; [exact H1|]. split; [exact H2|]. replace (q + -544 + 128)%Z with (q + -544 + 112 + 16)%Z by lia. exact H3.
  Qed.
  Lemma lo_join : forall m pfx s2s za pl plp l10n alo ahi j128,
    rw_cells psegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) ->
    rw_cells psegs m (q + -544 + 112) [C8 alo; C8 ahi] -> rw_cells psegs m (q + -544 + 128) [CB 24 j128] ->
    rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128).
  Proof.
    clear. intros. unfold lo_cells.
    apply (proj2 (rw_cells_app psegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)). split; [exact H|]. cbn [cells_size csize Nat.add app].
    change (Z.of_nat 112) with 112%Z.
    apply (proj2 (rw_cells_app psegs m _ [_;_] _)). cbn [cells_size csize Nat.add app]. change (Z.of_nat 16) with 16%Z. split; [exact H0|].
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
    rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] ->
    va_area m VA slots -> nth_error slots (Z.to_nat k) = Some slot -> (0 <= k)%Z ->
    rw_cells psegs m (q + -544 + 112) [C8 x; C8 y] ->
    stk psegs m lo (q + -544) ->
    mem_inv psegs m ->
    (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL)%Z ->
    evt psegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft' m',
                 ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          Ft' (ret_pc ra') fc None m' (seg_rom psegs)
                 /\ munch [(q + -544 - 16, q + -544); (AP, AP + 8); (q + -544 + 112, q + -544 + 112 + 16)]%Z m m'
                 /\ wmono psegs m m' /\ mem_inv psegs m'
                 /\ stk psegs m' lo (q + -544)
                 /\ rw_cells psegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (k + 1)))]
                 /\ rw_cells psegs m' (q + -544 + 112) [C8 (F_pop_arg.pop_arg_lo ty slot); C8 (F_pop_arg.pop_arg_hi ty slot y)]
                 /\ Fokd Ft Ft')
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 ty) (Z_to_bv 64 AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x21050) fc None m (seg_rom psegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "p'0h02m'h11kh23Ft'h33t6'h43t5'h53t4'h63t3'h73a7'h83a6'h93a5'h:3a4'h;3a3'h<2Fth=3a2'h>3a1'h?3a0'h@2t6hA3t2'hB3t1'hC2t5hD3t0'hE2t4hF2t3hG1HhH2a7hI4__x1hJ2a6hK2a5hL4__x2hM2a4hN2a3hO2a2hP2a1hQ1zhR7__sat13hS7__sat14hT7__sat15hU4cstrhV5cstr0hW7__arithhX4__ffhY8__varmaphZ5__with[2a0h\4__p1h]2t2h^3H12h_3IL0h`7__sat16ha2t1hb3z12hc4__x3hd2t0he3ms'hf2Hahg1Phh7__sat12hi1xi001xhj1Ahk4__p2hl4__p3hm4__x4hn4__x5ho3a0vhp1lhq1nhr3APChs4APC'ht4ARGChu5ARGC'hv2Eahw2Ephx2Eqhy2H0hz2HFh{2Hkh|2ILh}2MIh~3MI'i012MUi023NTHi032STi043ST'i053ST1i063ST2i072TYi083VAAi094VAA'i0:2VBi0;2WMi0<1ai0=1ei0>2fci0?1mi0@1oi0A3ra'i0B2s0i0C2s1i0D3s10i0E3s11i0F2s2i0G2s3i0H2s4i0I2s5i0J2s6i0K2s7i0L2s8i0M2s9i0N4sloti0O2tyi0P1yp%0p%1p%2p&0p&1p;1p;2p;3p;Op;7p;4p;6p;Kp;ip;Lp;5p;:p;8p;<p103o^p6051002p104e@p4p710p8g007ej1ITg008Jj1|Tg008hk104Tg00U>j1JTg004?k20~Tg00>AS00k10>Tg01ACk10kTg00dZj2?Tg013Gj1VTg00Emk10MTg057Kj3qTg00EMR0k102Tg00>ck301Tg00?Ak20<Tg00;Lj3ATg03C\j1HTg00QIj2RTg009Kj2NTg058GlO1Tg00Iek106Tg0599k10iTg03JKk20eTg01?fj2]Tg00T@j3>Tg0158R1j20Tg05:2j73Tg05:dk30@Tg01ijj2zTg05;Uk417Tg00:lj2{Tg00N^R2k10[Tg01e2k20XTg00A_j29Tg00COS01j24Tg00PBk10]Tg01mBk20\Tg00C3R3j2TTg01mjk30WTg007Ek10VTg00FMj2~Tg01Bkk10tTg00Fkk10sTg00GIk10rTg00H4j2uTg01Clj3}Tg00JGk20oTg00@Gj2rTg00Jik20nTg00KUk30mTg00L4k40lTg05<Wk70jTg00Qcj1pTg00RBk20UTg00STk20ETg01eok30TTg00HWk20STg027Qk20DTg026gk207Tg021mk20hTg022Vk30gTg01o:k30fTg00Lfj1yTg00lJR4j2wTg05=Ok30dTg002Tk603Tg01T`k20cTg0030k60CTg05>2mK0bmL0`Tg00O[k40PTg00Pgk20OTg05?3mi0aTg05@4j1;Tg03n1k20ATg04bfj3LTg05@jk20;Tg04j]k518Tg04kAk315Tg05Anm:13Tg05C3k810Tg01S>j4lTg04m>k40ITg05Ckk60}Tg02G^j4KTg05Dak40ZTg044]k20|Tg03S8k40{Tg05ESk30YTg05FRk200Tg04cZk30HTg00T`k40zTg00I:k40GTg01CIk30yTg00WXk70JTg00X`k70xTg00YDk80=Tg00Rkk30wTg00X<k611Tg00O>k212Tg00Yhm<0vTg00ZMm<0uTg00Uck714Tf0R5#I#Ip>0?%I5#I#I#Ip=_g00;fR6f1R7;A5p=ff2R81z75'?p>0Bg00j;R9f4R:f3R;g02NRR<1N87#H;>5CKp>0Kg00[2R=/95p=EA><75p>0qP9P;P8A><75CKp>0pP9P8P7P5H0Zp=C20|95p=Uf6R>f5R?%;:P;P8P7P5F3p=:P6P6P7P5H0{p=`1?75,z8,?;,N:p=5B0Y;87#H=><5p=2P9P>P?200:;#H=><8CK20;75'4p==P9P:P;%H8=><7CK/45p=6B0H9:;1475,48'4p=7g04[FS02?A?:AL;87/45'4p=8P9P:P;%H7=><59><8CKp>0^P6P8P7P5H0zp=X20S65p=kP6P7g00`QR@P5H0Gp=tB0y675p=OP8g00[PS03g00[oS04Q04g00\OS05P6P7P@P5H0Gg00\oR@K0Jp=BP8Q03Q04Q04Q05P7P5K0xp=aP:Q03Q04Q04Q05P;Q03Q04Q04Q05P8P@K0JP7P5L0=p=sP9P;P8P7H0Z/45p>0F20U65p=oB0w675p=vP6P7g00_jP5H0Gp>0:P7Q03Q04Q04Q05P5P@K0Jp>09P;Q03Q04Q04Q05P8P7P5L0=p>08P>Q03Q04Q04Q05P?P:P;Q03Q04Q04Q05P8P7P5L0=L0=p=iP7Q03Q04Q04Q05P5J11p>05P6P:P;P8P7P5J0Cp=M212=5p=hP6g00<iR@P6P6P0P:P2P;g00]OP8P7P5N<0vp>0RP@P6P4P2P3g00nCP?P:P;P8P7P5N<0up>0Q1975,R8p=\P8Q03Q04Q04Q05P7P5K14p=gQ02f7R3P>P?P:P;P8P7P5F33Ap=nB0H975p=GP9P3P>1?87,z;,?:,N?#H=><5CKp=Q20087#H=><5p=xP9P8P7P5CKp=^20A759A;8p=<1475,48p>0NAL;87/45,4:p=e1?87,z;,?:,N?#H=><5p=SP9P:P;P8CK1475'4p>1:1475,48,4;,4:p=mP9P;P8P7CK/45p>0LP9P>P?200:;#H=><8CK1475'4p=@P9P3P>200?:#HB0Y;87#H=><55><CKp=Z20;75,48,4;,4:,4?p=dQ02?A:;1475,48'4p=F1475,48,4;,4:,4?p=c20A;820A755A:p=DAq;87/45p=PP9P?P:200;8#H=><7CK/45p=[P9P;P8P7CK/45,4:,4?p=WAL?:;B0H987/45'4p=jQ02?A87/45p=YP9P:P;P8CK20;75'4p>0_Q02?A75p>191475,48,4;p>16P>P?P:P;P8P7P5H0IH0Ip=bg00<DR2#IR4$0?R0#IRA#IRB#IRC#|RD$04RE%J4RF#|S0600~ERG%|B$04%|0$04$0>\ERBp,1qS07%J0#I#_$0kRH'?RI%J2S08#JS09#_#VRJ'?RK,f?PKf8RLp,2APRMPDp,2VARN%V0RO<0B>&0M<R<I0Kf9RPp,5slotsRQ7qNS0:&0>ERR&02L:01EQ20<E>3A%EPf<RSPK%H3%H>RT00q<H0pf=RUp,2loRV;CIf>RW#Ug04MWRX9A6Sg04NURY9A6Sg04OSRZ9A6Sg04L4R[9A6S'R'R'RQ02fAR\fmS0;1NDIR]p,2gpR^p,2tpR_f@R`f?RaPWfiS0<fhRbPUPSf;Rcf:RdPPPLP3P>fbS0=faS0>f`S0?f_S0@f^S0Af]S0Bf\S0Cf[S0DfZS0EfYS0FP?P:P;P8MO1P7Q0;fSS0G&06EReP5&0i9RfF:20e66Rg%VARA,]IRh/`IRi1?MOS0H,`M1?KAS0I,`K&0MgS0J5>gS0K5>g3>RjfRS0LP5Q0LP5%U5RkAC5VIRlP5PMPDPNPOfPS0M%V2RmD5P<P5PKfOS0NfNS0OQ0NQ0OfLS0PP<C2fTS0QP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWeS0RQ0DP]P^P_Q0EQ0FfXS0SfWS0TfVS0U1NDL1NDUS0V1NDMS0WfUS0XQ0QQ0GQ0LfQRnQ0MQ0NQ0OfMS0YQ0PfKS0ZfJRofIS0[fHS0\fGRpfFS0]fES0^fDS0_fCS0`MO1fBS0a%_2#J#I#_#J#I#J#_#V,NDS0bP\PeP`PfF360@9[[[[[[[[Xo6P3PMPD1zO?S0c,?NP<I0KAqLNQS0d&023:01EQ20<E?5AR%ELPcPKPTP?P<I0^ACSVI%UUS0eAA6cXAA6cYAA6cZAA6c['R'R'RPaPNPQP>H17%ENS0f1{EQS0g$0[S0h:0BNOR[%V4RZ%VCRC+0XRY'9'4P9P`PVPhPIP;p,3fmt,{6RX$0]S0i&0[X#ES0jQ0g$0]S0kQ0h#ES0l%JF#J#JRX#VRT-0\ZS0m1T=ZRq%ET20XZTRr,T=[[S0n%EZRsg01WWS0oB0WZT7UWfS0pQ0o%Er[^fsS0q20\ZCS0r%EC1T=Y[\qS0sQ0oB0WZC7UXfsS0tQ0o%EY[^fsS0ug00_>Rs$0MS0v&0VsS0w1~68S0x&0t6RC7X7Rq&0s6S0y&0r6RTPT1u62Rt1u64S0z%IFS0{$0?#J$0?#_#VRF#kR45}6'tQ04$06S0|Q0z%kHS0}'OS0~%kARu5}6S109BTtQ10Q0~5BT5aTDsQ05-0oTS11P5P8g00^^Rvg00a8Rw'r20n58=AvwdB0m6=7H0lS12bXbYbZXI6XL61]7FS13,951?8HRw/]AS14,97Q14/9w'4[^I6^L6P5Q07PVp,2LOS15O3bWS16bhbRbSbTbVbUK0jP`PVPhAC`hIS17H0FQ01AC\VhAC\hIS18Q02P\foS19P]P^P_P`PaPWfkRvfjS1:PUPSPcPdPPPLP3P>fdS1;fcS1<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DP?P:P;P8MO1P7Q19Q0XPeP5PfF:PjQ0QP5Q0QP5PkPlP5PMPDPNPOQ0LPmD5P<P5PKPnQ0MPnQ0MQ0OP<C2Q0UP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWeQ0BP]P^P_Q0CQ0DQ0EQ0FQ0S1NDKS1=1NDaQ0WQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZPoQ0[Q0\PpQ0]Q0^MO1Q0_Q0bQ0`PeQ0aPfF360@9P5Q0`?CVhQ0_?ChIQ0iQ0jQ0kQ0lQ0mQ0nQ0pQ0qQ0rQ0sQ0tQ0ug00b3Rx#pRy#pS1>#o%oy20U6xS1?'v'vS1@g00bRRx+0EQ0v5>sS1AQ0wPqQ0yPT%kZRZ%|X60T6-0:t-09TRXQ0|PT%I2#J#J$0?#J#_#_#_#VR2#kQ0z5BTS1BQ0|PTQ0zA}6t45BTS1CQ0|20S6=RyQ0},OtRz5BTB0T6ZDRZ-0:z-09T5aTH08FiQ11Q12bXbYbZXI6XL61T5rS1D1928Rr1]8F,9;R{1?;HR|#E1T|Y'4[[[^I6^L6P5PVQ07p,3QHIp,3GLOS1EQ15O5S1FbWbhbRbSbTbVbU-0DI207D]R}/fIQ0iQ0jQ0kQ0lQ0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ1AQ0wPqQ0yPTPXQ0|PTQ1BQ0|PTQ1CQ0|%kJS1G,OzRX9BTy20:XZ-09T5aTH08FiQ11Q12bXbYbZXI6XL6Q1D1?|JR~#E1T~Y'4\{\r[^I6^L6Q1FbWbhbRbSbTbVbU-0DKQ1=-07DRr/fKQ0iQ0jQ0kQ0lQ0mQ0nQ0pQ0qQ0rQ0sQ0tQ0up-0R{Q1>#pS1>#oQ1@'v00Ex20h6OQ1>#pS1>#pS1@#p#o60g6Q1@#oQ1>#oQ1?'v'v'v00ExQ0v5>s5>sQ0w1~6??X?C9XC81~6:9XC;7X7Q0yPTPTQ0{,u6S1?,tyQ0|PT205T3S1>Q09,u6Rs%kORxQ1?60f6'O=BTZ5aTQ0|PT1Otx=BTsQ0|PTPTQ08,u6S08/ttQ0|PTQ1BQ0|PTQ0zQ08=}645BTQ0|ABTytS1?20:tZ-09T5aTFiDsFiDsQ11Q12bXbYbZXI6XL6Xc6Xm6Xn6W\%E:Q0c,?:/9Y,4>1?8ORZ/9?19?;192?1]3F,9>%E>1T>Y'4[[[[[[^I6^L6^c6^m6^n6^\{P5Q0fQ0hPNQ07PVPMP?PWp,3HVAS0fp,3HAPS0cQ1EQ15O<bWbhbRbSbTbVbU-0DMQ0W-07DRY/fMg00aXp4p710RF&0V5RyQ01&0>8B01875&0683A#y1{;8,w7[R41{87,w5&0>;B01;87&06;3A#yRs[1{:;,w8\sB0d875P7n2001000000120000000Xq@WpWjP4^q@^py^jFP5PEPQ&02pRFPRQ0^-0<ERyAAR5e#yZ0@RAARyeRyPRQ0]-0<EQ00PEP{P5Q0og01X3R@n10110@00021000000Z0=Rg01XPPeP5J03P@20c@5byWG%yyeB01EQFPaJ0CO4bGQ0]$02Q0g'wP9Q1;P]P^P_Q0?Q0@Q0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0ZPoPrPYPNPQPpQ0]Q0^Q0`Q0[NK0bQ02P\fvS00P]P^P_P`PaPWfrS09fqS1@PUPSPcPdPPPLP3P>PvQ1:Q0<PbfgS1FffS1DfeS1HQ1;Q1<Q0=P?P:P;P8MO1P7Q00Q0CPeP5PfF:PjQ0DP5Q0DP5PkPlP5PMPDPNPOQ0FPmD5P<P5PKQ0SQ0TQ0SQ0TQ0XP<C2Q0BP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWeQ1;P]P^P_Q1<Q0=Q0>Q0?Q0@Q1=Q0],NDRyQ0WQ0AQ0BQ0CQ0DQ0EQ0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PMO1Q0ZQ0bPoPeQ0[PfF3Q1;P]P^P_Q1<Q0=Q0>Q0?Q0@Q1=PyQ0WQ0AQ0BQ0CQ0DQ0EQ0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZPoQ0[PNPQPpQ0]Q0^Q0_Q0`PMPoP5PDQ0\:0BNOP<I0KXQ6P\PYP7DMP`PaQ0g,wF%hpQ0h'TR@PF%h5Xi6S1IPpO1P5Xi6S1JQ1IPpPp1r6pI0RQ0gQ0hQ0h,r6S1KJ0QP5H0PRFP@Q0iQ0jQ0kQ0l20O=oRR1T=o%hoR4/fo'419o=AA64='4'RR4Q0Z#hRsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0w1~67S1LQ0yPTQ1?Q0|Q1?H08Q11Q12bXbYbZXI6%E5%E7[^I6P5PnQ0\O2bWbRbSbTb`bbb^bVbUb_PKPoP5Q0^#HQ0_P<I0^XQ6PUPrP8DMPI1]5AS1?=Co5XQ6P:P}P;DMPc1rEyPdPI19A5XQ6PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ1AQ0wPqQ0yPTQ1BQ0|PTQ1CQ0|ABTuzFiQ11Q12bXbYbZXI6XL61927Q13,9819Aw[[^I6^L6P5PVQ07Q1EQ15O4bWbRbSbTb`bbb^bVbUb_P}P;DMPI195YXQ6PM19I5XQ6R2PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wPqQ0yPTPTQ0z,ttQ0|Q0z9BTzDsQ11Q12bXbYbZXI6XL619571?7H/98[^I6^L6P5PMQ07Q0cO3bWbRbSbTb`bbb^bVbUb_PYP7DMP}P;DMPI195rXQ6PKP2PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wQ1LQ0yABTzXQ11Q12bXbYbZXI61?5HRH1?HJ'9^I6P5Q07O1bWbRbSbTb`bbb^bVbUb_PrP8DMP}P;DMPK1?YORH/951?5ARX;\YXQ6PM1?5ORz/9KQ0I;\5XQ6PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wPqQ0yPTPTQ0z/ttQ0|205T:RqQ0~Q1G'OS0~/Ou=BTt5gTDsQ11Q12bXbYbZXI6XL6X\{19751?wJS1L/?A=\;7[^I6^L6^\{P5Q0H/9KQ07PMQ0cO4bWbRbSbTb`bbb^bVbUb_PYP7DMPrP8DMPIQ1?,9[?\5NXQ6PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ1AQ0w1~6;S1??X;C?X;CQ0x7X7S15Q0yPT1u60R0/Ox=BTtRwQ0|PTQ08=BT0R0Q0|205T?S1EQ08Q0}'ORJ=BTt5gTFiQ11Q12bXbYbZXI6XL6Xc6X\{19Z5R2198;RyA\?|8[[^I6^L6^c6^\{P519[hPMQ07PNQ0fQ0cO6bWbRbSbTb`bbb^bVbUb_P}P;DMPM19[5R|?\zNXQ6PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wQ0x9XC7Q0yPTQ08/Ox=BTtRxQ0|AgTqxH08Q11Q12bXbYbZXI6XL6X\{1?7O/95A\;Z7[^I6^L6^\{P519[MPMPNQ0fO4bWbRbSbTb`bbb^bVbUb_PYP7DMPKA\|XNXQ6PFP@Q0iQ0jQ0kQ0lPRP4PsP6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ1AQ0wQ15Q0yPTPwQ0|PTP0Q0|Q1EQ1G,OJ/Ou=BTt5gTFiQ11Q12bXbYbZXI6XL6Xc6X\{1?~A=\?8\y\2^I6^L6^c6^\{P519[KPMQ07PNQ0fQ0cO6bWbRbSbTb`bbb^bVbUb_PrP8DMNi0aQ02Q1HP]P^P_Q0>Q0?Q0EQ0FQ0SQ0TQ0UQ0XQ0QQ0GQ0LPnQ0PQ0ZPrPYPNPQQ0\PpQ0]Q0_PoP5NL0`S0fP6P}Q0`fxR}P]P^P_P`PaPWftR[fsS1GPUPSPcPdPPPLP3P>Q0;flS15PvQ1:Q0<PbQ1FQ1DQ1HQ1;P?P:P;P8MO1P7%;}Q0APeP5PfGnR21]\ARy/`\1`YHRH1?rA,`rQ0J5>g5>gR~5>gQ0BP5Q0B/G5RuP5PyP\P5PYPDPNPOQ0DPmP<GQRyQ0EQ0FQ0EQ0FQ0TP<C23xRJ9^5rAq5NQR0Q06$04RwQ060075Q0{#V'f#yRsPE20A;7R4Q0>P7C<[]1'4RR40NH0F80NkDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EXQ6P5PIP?J03Q0afwR@P]P^P_P`PaPWQ1GQ09PUPSPcPdPPPLP3P>Q15PvQ1:Q0<PbQ1FQ1DQ1HQ1;Q1<P?P:P;P8MO1P7%;@Q0BPeP5PfGnS0{A>gi~Q0CP5Q0C/G5S06PkAC5hIR~PDPNPOQ0EPmP<ESS1A9^5YP5PrQ0FQ0SQ0FQ0SQ0UP<C23xS0}P0PEP4Q0?P7C<\s^1wI1:DmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EP6PrQ0_fyS13P]P^P_P`PaPWfuS1CP[PUPSPcPdPPPLP3P>fnS1BQ0;Q15PvQ1:Q0<PbQ1FQ1DQ1HP?P:P;P8MO1P7Q13#;Q0@PeP5PfGnRr1?\A,`\Q0J5>g9>gH9>giQ0AP5Q0A/G5RAPkP~PDPNPOQ0CPmP<ESRF9^5YP5P\Q0DQ0EQ0DQ0EQ0SP<C23xR|PEP4Q0=P7C<\s^1w,40RXH0LDmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EXQ6P5PKP?J03P2Q0K9>gH9>giQ0BP5PuPkP~PyP5PKPJPRH0LDmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EP6PYQ0^fzRYP]P^P_P`PaPWQ00Q1CPUPSPcPdPPPLP3P>Q19Q1BQ0;Q15PvQ1:Q0<PbQ1FQ1DP?P:P;P8MO1P7%;YQ0?PeP5PfGnRR1?\O,`\Q0K5>g9>giQ0@P5Q0@/G5RiPkP~PDPNPOQ0BPmP<ESRg9^5\P5PKQ0CQ0DQ0CQ0DQ0FP<C2P0PEP4Q1<P7C<\s^1wF@RJDmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EXQ6P5PMP?J03PrPjQ0AP5PAPkP~A^5MFP5PKP|PXH0LDmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdE,0EP1PEPRPjQ0@P5PiPkP~A^5MgPJDmDeX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EXdEQ0]f{RJP]P^P_P`PaPWP@Q00PUPSPcPdPPPLP3P>fpS0KQ19Q1BQ0;Q15PvQ1:Q0<PbQ1FP?P:P;P8MO1P7PJQ0>PeP5PfF:PjQ0?P5Q0?P5PkPlP5PMPDPNPOQ0APmD5P<P5PKQ0BQ0CQ0BQ0CQ0EP<C2Q0=P7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Ppf|S0JP]P^P_P`PaPWP}P@PUPSPcPdPPPLP3P>Q1@Q0KQ19Q1BQ0;Q15PvQ1:Q0<PbP?P:P;P8MO1P7Q0JQ0=PeP5PfF:PjQ0>P5Q0>P5PkP~P5PMPDPNPOQ0@PmD5P<P5PKQ0AQ0BQ0AQ0BQ0DP<C2P0PEP4Q1HP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaE,0EP1PEQ0\f}RgP]P^P_P\PaPWQ13P}PUPSPcPdPPPLP3P>Q09Q1@Q0KQ19Q1BQ0;Q15PvQ1:Q0<P?P:P;P8MO1P7PgQ1<PeP5PfF:PjQ0=P5Q0=P5PkP~P5PMPDPNPOQ0?PmD5P<P5PKQ0@Q0AQ0@Q0AQ0CP<C2P0PEP4Q1DP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EXaEPop+01@RiP]P^P_P`PaPWPJPYPUPSPcPdPPPLP3P>P[Q1GQ09Q1@Q0KQ19Q1BQ0;Q15PvP?P:P;P8MO1P7%;iRRQ1HPeP5PfF3Q1;=Lj5RXQ1;/G5R|PkPlP5PMPDPNPOQ0=PmP<GQRFP5PKQ0>Q0?Q0>Q0?Q0AP<GZRAQ1DP7EdDFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5PoPiP]P^P_Q0`PaPWPJPYPUPSPcPdPPPLP3P>P[Q1GQ09Q1@Q0KQ19Q1BQ0;Q15PvP?P:P;P8MO1P7PRQ1HPeP5PfF3PXP|PkP~PFPAP0PEP4PbP7C<\s^1wEcDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]E,0EP1PEQ0Zp+01ARAP]P^P_Q0_P`PWQ0JPJPUPSPcPdPPPLP3P>Q1CP[Q1GQ09Q1@Q0KQ19Q1BQ0;Q15P?P:P;P8MO1P7PAQ1DPeP5PfF:PjQ1HP5Q1HP5PkP~P5PMPDPNPOQ1<PmD5P<P5PKQ0=Q0>Q0=Q0>Q0@P<C2P0PEP4Q0<P7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EX]EQ0Op+01DRFP]P^P_P`PaPWPif~S1MPUPSPcPdPPPLP3P>P}P@Q00Q1CP[Q1GQ09Q1@Q0KQ19P?P:P;P8MO1P7%;FR|Q0<PeP5PfF3ALjb5RX1Gb5RRPkPlP5PMPDPNPOQ1DPmP<GQRrP5PKQ1HQ1;Q1HQ1;Q0=P<GZRyQ1:P7EdDFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0Yp+01CRuP]P^P_Q0]Q0aPWQ1MPgPUPSPcPdPPPLP3P>P@Q00Q1CP[Q1GQ09Q1@Q0KQ19Q1BP?P:P;P8MO1P7PuPbPeP5PfF:PjQ1FP5Q1FP5PkP~P5PMPDPNPOQ1HPmD5P<P5PKQ1;Q1<Q1;Q1<Q0>P<C2P0PEP4PvP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[E,0EP1PEQ0OPFP]P^P_PpQ0`PaPiQ1MPUPSPcPdPPPLP3P>P}P@Q00Q1CP[Q1GQ09Q1@Q0KQ19P?P:P;P8MO1P7P|Q0<PeP5PfF3PXPRPkP~PrPyP0PEP4Q15P7C<\s^1wEcDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EX[EQ0Lp+01HRyP]P^P_P`PaPWPFPuPUPSPcPdPPPLP3P>Q0JPJPYQ13P}P@Q00Q1CP[Q1GP?P:P;P8MO1P7PyQ0;PeP5PfF:PjQ15P5Q15P5PkPlP5PMPDPNPOQ1:PmD5P<P5PKQ0<PbQ0<PbQ1DP<C2Q1BP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0Mp+01FS1NP]P^P_Q0[Q0^P\p+01BS1OPAPUPSPcPdPPPLP3P>PYQ13P}P@Q00Q1CP[Q1GQ09Q1@P?P:P;P8MO1P7Q1NPvPeP5PfF:PjQ1:P5Q1:P5PkP~P5PMPDPNPOPbPmD5P<P5PKQ1FQ1DQ1FQ1DQ1;P<C2P0PEP4Q1BP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPE,0EP1PEPnp+01GRrP]P^P_PoQ0]Q0aPuQ1OPWPSPcPdPPPLP3P>PJPYQ13P}P@Q00Q1CP[Q1GQ09P?P:P;P8MO1P7PrQ15PeP5PfF:PjPvP5PvP5PkP~P5PMPDPNPOQ0<PmD5P<P5PKPbQ1FPbQ1FQ1HP<C2P0PEP4Q19P7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EXPEQ0Up+01LRRP]P^P_P`PaPWPyPrPUPSPcPdPPPLP3P>PAPiQ1MPgQ0JPJPYQ13P}P@P?P:P;P8MO1P7%;RRXQ1@PeP5PfF3Q0K=Lj5R|Q0K/G5RHPkPlP5PMPDPNPOQ1BPmP<GQR2P5PKQ0;Q15Q0;Q15Q1:P<GZRZQ09P7EdDFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0Gp+01IRxP]P^P_Q0PQ0\Q0_p+01ES1PPFP`PSPcPdPPPLP3P>PgQ0JPJPYQ13P}P@Q00Q1CP[P?P:P;P8MO1P7PxQ1BPeP5PfF:PjQ0;P5Q0;P5PkP~P5PMPDPNPOPvPmD5P<P5PKQ1:Q0<Q1:Q0<Q1FP<C2P0PEP4Q1@P7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOE,0EP1PEQ0Qp+01JRqP]P^P_Q0YQ0[Q0^Q1NQ1PP\PUPcPdPPPLP3P>Q1MPgQ0JPJPYQ13P}P@Q00Q1CP?P:P;P8MO1P7PqQ19PeP5PfF:PjQ1BP5Q1BP5PkP~P5PMPDPNPOQ15PmD5P<P5PKPvQ1:PvQ1:PbP<C2P0PEP4Q09P7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EXOEQ0Ep+01PRCP]P^P_P`PaPWPRp+01KS1QPUPSPcPdPPPLP3P>Q1PPFPuQ1OPAPiQ1MPgQ0JPJP?P:P;P8MO1P7%;CS1RQ1CPeP5PfF3ALj[5S1S1G[5S1TPkPlP5PMPDPNPOQ09PmP<GQS1UP5PKQ1@Q0KQ1@Q0KQ1BP<GZRzQ00P7EdDFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0UPRP]P^P_Q0NQ0ZPpPyPrQ0`PaPcPdPPPLP3P>PAPiQ1MPgQ0JPJPYQ13P}P@P?P:P;P8MO1P7PXQ1@PeP5PfF3P|PHPkP~P2PZP0PEP4P[P7C<\s^1wEcDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNE,0EP1PEQ0Tp+01MRZP]P^P_Q0MQ0PQ0\PxPyQ0_P`PSPdPPPLP3P>Q1OPAPiQ1MPgQ0JPJPYQ13P}P?P:P;P8MO1P7PZQ09PeP5PfF:PjQ1@P5Q1@P5PkP~P5PMPDPNPOQ19PmD5P<P5PKQ1BQ0;Q1BQ0;PvP<C2P0PEP4Q1CP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EXNEQ0Ap+01TS1VP]P^P_P`PaPWPCp+01OR2PUPSPcPdPPPLP3P>PxPyPrQ1NQ1PPFPuQ1OPAPiP?P:P;P8MO1P7Q1VQ13PeP5PfF:PjP}P5P}P5PkPlP5PMPDPNPOQ00PmD5P<P5PKQ1CP[Q1CP[Q09P<C2PYP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0FP2P]P^P_Q0LQ0OPoQ1QPqQ0]Q0aPWPdPPPLP3P>PFPuQ1OPAPiQ1MPgQ0JPJPYP?P:P;P8MO1P7P2P[PeP5PfF:PjQ1GP5Q1GP5PkP~P5PMPDPNPOQ1@PmD5P<P5PKQ0KQ19Q0KQ19Q0;P<C2P0PEP4P@P7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXME,0EP1PEQ0EPCP]P^P_Q0GQ0NQ0ZPRQ1QPpQ0`PaPcPPPLP3P>Q1PPFPuQ1OPAPiQ1MPgQ0JPJP?P:P;P8MO1P7Q1RQ1CPeP5PfF3Q1SQ1TPkP~Q1UPzP0PEP4P}P7C<\s^1wEcDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EXMEQ0=p+01XS1UP]P^P_P`PaPWQ1Vp+01SRzPUPSPcPdPPPLP3P>PZPRQ1QPqPxPyPrQ1NQ1PPFP?P:P;P8MO1P7Q1U#;S1TPgPeP5PfF3Q0J=Lj5S1SQ0J/G5S1RPkPlP5PMPDPNPOPYPmP<GQS1WP5PKQ13P}Q13P}Q00P<GZS1XQ1MP7EdDFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0Cp+01RS1YP]P^P_Q0XPnQ0Yp+01NRHPZQ0[Q0^P\PUPPPLP3P>PrQ1NQ1PPFPuQ1OPAPiQ1MPgP?P:P;P8MO1P7Q1YP@PeP5PfF:PjQ00P5Q00P5PkP~P5PMPDPNPOP[PmD5P<P5PKQ1GQ09Q1GQ09Q0KP<C2P0PEP4PYP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKE,0EP1PEQ0BPzP]P^P_Q0UQ0LQ0OP2PHPoQ0]Q0aPWPdPLP3P>PyPrQ1NQ1PPFPuQ1OPAPiQ1MP?P:P;P8MO1P7PzP}PeP5PfF:PjP@P5P@P5PkP~P5PMPDPNPOQ1CPmD5P<P5PKP[Q1GP[Q1GQ1@P<C2P0PEP4PJP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EXKEQ1Dp+01\S1ZP]P^P_P`PaPWQ1Up+01WR|PUPSPcPdPPPLP3P>p+01QS1[PCP2PHPZPRQ1QPqPxPyP?P:P;P8MO1P7Q1Z#;S1\Q1OPeP5PfF3ALjA5S1]1GA5S1^PkPlP5PMPDPNPOQ1MPmP<GQS1_P5PKPgQ0JPgQ0JPYP<GZS1`PuP7EdDFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0@p+01US1aP]P^P_Q0SQ0QQ0MQ1[PCQ0PQ0\Q0_P`PSPLP3P>PqPxPyPrQ1NQ1PPFPuQ1OPAP?P:P;P8MO1P7Q1aPYPeP5PfF:PjQ13P5Q13P5PkP~P5PMPDPNPOP@PmD5P<P5PKQ00Q1CQ00Q1CQ1GP<C2P0PEP4PgP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJE,0EP1PEQ0?p+01VRXP]P^P_Q0FQ0XPnQ1YQ1[Q0YQ0[Q0^P\PUPPP3P>Q1QPqPxPyPrQ1NQ1PPFPuQ1OP?P:P;P8MO1P7PXPJPeP5PfF:PjPYP5PYP5PkP~P5PMPDPNPOP}PmD5P<P5PKP@Q00P@Q00P[P<C2P0PEP4Q1MP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EXJEQ1:p+01`S1bP]P^P_P`PaPWQ1Zp+01[S1cPUPSPcPdPPPLP3P>Q1aQ1VPzQ1YQ1[PCP2PHPZPRP?P:P;P8MO1P7Q1bQ1NPeP5PfF:PjQ1PP5Q1PP5PkPlP5PMPDPNPOPuPmD5P<P5PKQ1OPAQ1OPAQ1MP<C2PrP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0=Q1UP]P^P_Q0DQ0TQ0GQ1VPzQ0NQ0ZPpQ0`PaPcP3P>PZPRQ1QPqPxPyPrQ1NQ1PPFP?P:P;P8MO1P7Q1TPgPeP5PfF3Q1SQ1RPkP~Q1WQ1XP0PEP4PAP7C<\s^1wEcDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHE,0EP1PEQ1<p+01YS1XP]P^P_Q0CQ0SQ0QQ1aQ1VQ0MQ0PQ0\Q0_P`PSPLP>PHPZPRQ1QPqPxPyPrQ1NQ1PP?P:P;P8MO1P7Q1XQ1MPeP5PfF:PjPgP5PgP5PkP~P5PMPDPNPOPJPmD5P<P5PKPYQ13PYQ13P@P<C2P0PEP4Q1OP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EXHEQ1Bp+01dS1WP]P^P_P`PaPWQ1bp+01_S1RPUPSPcPdPPPLP3P>Q1XQ1UP|PXQ1aQ1VPzQ1YQ1[PCP?P:P;P8MO1P7Q1W#;S1SPqPeP5PfF3ALjx5S1T1Gx5S1dPkPlP5PMPDPNPOPrPmP<GQS1eP5PKQ1NQ1PQ1NQ1PPuP<GZS1fQ1QP7EdDFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1HQ1cP]P^P_Q0AQ0EQ0UP|PXQ0LQ0OPoQ0]Q0aPWPdP>PCP2PHPZPRQ1QPqPxPyPrP?P:P;P8MO1P7Q1cPAPeP5PfF:PjPiP5PiP5PkP~P5PMPDPNPOPgPmD5P<P5PKQ0JPJQ0JPJQ13P<C2P0PEP4PFP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFE,0EP1PEQ1DQ1ZP]P^P_Q0@Q0DQ0TQ1UP|Q0GQ0NQ0ZPpQ0`PaPcP3Q1[PCP2PHPZPRQ1QPqPxPyP?P:P;P8MO1P7Q1\Q1OPeP5PfF3Q1]Q1^PkP~Q1_Q1`P0PEP4Q1PP7C<\s^1wEcDFX0B,0BX<G,0GX@E,0EXCE,0EXEE,0EXFEQ09p+01hS1`P]P^P_P`PaPWQ1Wp+01cS1_PUPSPcPdPPPLP3P>p+01]S1^Q1ZQ1cp+01ZS1]Q1XQ1UP|PXQ1aQ1VP?P:P;P8MO1P7Q1`#;S1\PHPeP5PfF3ALjZ5S1g1GZ5S1hPkPlP5PMPDPNPOQ1QPmP<GQS1iP5PKPqPxPqPxPrP<GZS1jP2P7EdDFX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Pbp+01^S1kP]P^P_Q0>Q0BQ0FQ1]Q1XQ0XPnQ0YQ0[Q0^P\PUPPPzQ1YQ1[PCP2PHPZPRQ1QPqP?P:P;P8MO1P7Q1kPFPeP5PfF:PjPuP5PuP5PkP~P5PMPDPNPOPAPmD5P<P5PKPiQ1MPiQ1MQ0JP<C2P0PEP4PrP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEE,0EP1PEQ0<Q1RP]P^P_Q0=Q0AQ0EQ1cQ1]Q0UQ0LQ0OPoQ0]Q0aPWPdQ1VPzQ1YQ1[PCP2PHPZPRQ1QP>P:P;P8MO1P7Q1RQ1PPeP5PfF:PjPFP5PFP5PkP~P5PMPDPNPOQ1OPmD5P<P5PKPAPiPAPiPgP<C2P0PEP4PyP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EXEEQ00p+01lS1lP]P^P_P`PaPWQ1`p+01gS1mPUPSPcPdPPPLP3P>p+01aS1nQ1bQ1RQ1kQ1^Q1ZQ1cQ1]Q1XQ1UP?P:P;P8MO1P7Q1lQ1YPeP5PfF:PjQ1[P5Q1[P5PkPlP5PMPDPNPOP2PmD5P<P5PKPHPZPHPZQ1QP<C2PzP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5PvQ1nP]P^P_Q1;Q0?Q0CQ1^Q1ZQ0SQ0QQ0MQ0PQ0\Q0_P`PSPXQ1aQ1VPzQ1YQ1[PCP2PHPZPLP:P;P8MO1P7Q1nPrPeP5PfF:PjQ1NP5Q1NP5PkP~P5PMPDPNPOPFPmD5P<P5PKPuQ1OPuQ1OPiP<C2P0PEP4PqP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCE,0EP1PEQ15p+01bS1oP]P^P_Q1HQ0>Q0BQ1kQ1^Q0FQ0XPnQ0YQ0[Q0^P\PUP|PXQ1aQ1VPzQ1YQ1[PCP2PHPPP?P;P8MO1P7Q1oPyPeP5PfF:PjPrP5PrP5PkP~P5PMPDPNPOQ1PPmD5P<P5PKPFPuPFPuPAP<C2P0PEP4Q1QP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@E,0EXCEPYp+020S1pP]P^P_P`PaPWQ1lp+01kS1qPUPSPcPdPPPLP3P>p+01eS1rQ1WQ1_Q1oQ1nQ1bQ1RQ1kQ1^Q1ZP?P:P;P8MO1P7Q1p#;S1sPXPeP5PfF3PjQ1aP5Q1aP5PkPlP5PMPDPNPOPzPmD5P<P5PKQ1YQ1[Q1YQ1[P2P<C2P|P7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1BQ1WP]P^P_Q1FQ1<Q0@Q1bQ1RQ0DQ0TQ0GQ0NQ0ZPpQ0`PaQ1XQ1UP|PXQ1aQ1VPzQ1YQ1[PCPcP3P;P8MO1P7Q1SPqPeP5PfF3Q1TQ1dPkP~Q1eQ1fP0PEP4PZP7C<\s^1wEcDFX0B,0BX<G,0GX@E,0EP1PEQ19Q1rP]P^P_PbQ1;Q0?Q1nQ1bQ0CQ0SQ0QQ0MQ0PQ0\Q0_P`Q1]Q1XQ1UP|PXQ1aQ1VPzQ1YQ1[PSPLP:P8MO1P7Q1rQ1QPeP5PfF:PjPqP5PqP5PkP~P5PMPDPNPOPyPmD5P<P5PKPrQ1NPrQ1NPFP<C2P0PEP4PHP7C<\s^1wF@D6D7E8X0B,0BX<G,0GX@EQ1Mp+024S1fP]P^P_P`PaPWQ1pp+01oS1ePUPSPcPdPPPLP3P>p+01iS1dQ1`Q1mp+01fS1TQ1rQ1WQ1_Q1oQ1nQ1bP?P:P;P8MO1P7Q1fQ1]PeP5PfF:PjQ1XP5Q1XP5PkPlP5PMPDPNPOP|PmD5P<P5PKPXQ1aPXQ1aPzP<C2Q1cP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1@Q1mP]P^P_Q1:Q1DQ0=Q1_Q1oQ0AQ0EQ0UQ0LQ0OPoQ0]Q0aQ1ZQ1cQ1]Q1XQ1UP|PXQ1aQ1VPzPWPdP>P8MO1P7Q1mPZPeP5PfF:PjPRP5PRP5PkP~P5PMPDPNPOPqPmD5P<P5PKPxPyPxPyQ1NP<C2P0PEP4PCP7C<\s^1wF@D6D7E8X0B,0BX<G,0GP1PGQ09Q1`P]P^P_PvQ1FQ1<Q1WQ1_Q0@Q0DQ0TQ0GQ0NQ0ZPpQ0`Q1^Q1ZQ1cQ1]Q1XQ1UP|PXQ1aQ1VPaPcP3P;MO1P7Q1\PHPeP5PfF3Q1gQ1hPkP~Q1iQ1jP0PEP4Q1[P7C<\s^1wEcDFX0B,0BX<GPup+028S1jP]P^P_P`PaPWQ1fp+023S1iPUPSPcPdPPPLP3P>p+01mS1hQ1lQ1qp+01jS1gQ1dQ1`Q1mQ1TQ1rQ1WP?P:P;P8MO1P7Q1jQ1kPeP5PfF:PjQ1^P5Q1^P5PkPlP5PMPDPNPOQ1cPmD5P<P5PKQ1]Q1XQ1]Q1XP|P<C2Q1RP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5P[Q1gP]P^P_Q0;Q0<Q1HQ1TQ1rQ0>Q0BQ0FQ0XPnQ0YQ0[Q0^Q1RQ1kQ1^Q1ZQ1cQ1]Q1XQ1UP|PXP\PUPPP?MO1P7Q1gPCPeP5PfF:PjP2P5P2P5PkP~P5PMPDPNPOPZPmD5P<P5PKPRQ1QPRQ1QPxP<C2P0PEP4PzP7C<\s^1wF@D6D7E8X0B,0BP1PBQ1CQ1qP]P^P_Q1BQ1:Q1DQ1mQ1TQ0=Q0AQ0EQ0UQ0LQ0OPoQ0]Q1bQ1RQ1kQ1^Q1ZQ1cQ1]Q1XQ1UP|Q0aPWPdP>MO1P8Q1qQ1[PeP5PfF:PjPCP5PCP5PkP~P5PMPDPNPOPHPmD5P<P5PKPZPRPZPRPqP<C2P0PEP:P7Q1VP7DD\s^1wF@D6D7E8X0BPrp+02<S1\P]P^P_P`PaPWQ1jp+027S1SPUPSPcPdPPPLP3P>p+021S1tQ1pQ1ep+01nS1uQ1hQ1lQ1qQ1gQ1dQ1`P?P:P;P8MO1P7Q1\Q1oPeP5PfF:PjQ1nP5Q1nP5PkPlP5PMPDPNPOQ1RPmD5P<P5PKQ1kQ1^Q1kQ1^Q1cP<C2Q1_P7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5P@Q1hP]P^P_Q0KQ15PbQ1dQ1`Q1;Q0?Q0CQ0SQ0QQ0MQ0PQ0\Q1oQ1nQ1bQ1RQ1kQ1^Q1ZQ1cQ1]Q1XQ0_P`PSPLMO1P:Q1hPzPeP5PfF:PjQ1YP5Q1YP5PkP~P5PMPDPNPOPCPmD5P<P5PKP2PHP2PHPRP<C2P0PEP>P7PXP7DD\s^1wF@D6D7E8Q01P}Q1uP]P^P_Q1@Q0;Q0<Q1gQ1dQ1HQ0>Q0BQ0FQ0XPnQ0YQ0[Q1_Q1oQ1nQ1bQ1RQ1kQ1^Q1ZQ1cQ1]Q0^P\PUPPMO1P?Q1u#;Q1VPeP7PfGnPjPzP7PzP7%U7AC7hIP7PMPDPNPOQ1[PmP<ESP7PKPCP2PCP2PZP<C2P7PNPQPEP3P7P|P7DD\s^1wCPE[EWEjQ1Qp+02@R0P]P^P_P`PaPWQ1\p+02;S1vPUPSPcPdPPPLP3P>p+025S1wQ1fQ1ip+022S1xQ1tQ1pQ1eQ1uQ1hQ1lP?P:P;P8MO1P7P0Q1TPeP5PfF:PjQ1rP5Q1rP5PkPlP5PMPDPNPOQ1_PmD5P<P5PKQ1oQ1nQ1oQ1nQ1RP<C2Q1mP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5PYQ1pP]P^P_Q1GQ19PvQ1lQ1qQ1FQ1<Q0@Q0DQ0TQ0GQ0NQ0ZQ1rQ1WQ1_Q1oQ1nQ1bQ1RQ1kQ1^Q1ZPpQ0`PaPcMO1P3Q1sPXPeP;PfGnQ02Q1tP]P^P_P[Q0KQ15Q1hQ1lPbQ1;Q0?Q0CQ0SQ0QQ0MQ0PQ1TQ1rQ1WQ1_Q1oQ1nQ1bQ1RQ1kQ1^Q0\Q0_P`PSMO1PLQ1tP|PeP:PfF:Q02ALj|?S1lP|P?%U?AC?hIP?PMPDPNPOQ1aPmD5P<P?PKQ1VPzQ1VPzQ1[P<C2P?PNPQPEPcP7Q1cP7DD\s^1wCPE[D6D7S1s'4Q0ap+02DR~P]P^P_P`PaPWP0p+02?S1yPUPSPcPdPPPLP3P>p+029S1zQ1jQ1Sp+026S1{Q1wQ1fQ1iQ1xQ1tQ1pP?P:P;P8MO1P7%;~S1|Q1gPeP5PfF3R1PjQ1dP5Q1dP5PkPlP5PMPDPNPOQ1mPmP<ESS1}P5PKQ1TQ1rQ1TQ1rQ1_P<C2Q1qP7F=EWEjR43YX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0E[WePjPXP:PXP:%U:AC:hIP:PMPDPNPOQ1VPmP<ESP:PKPzQ1YPzQ1YPCP<C2P:PNPQPEPdP7Q1]P7DD\s^1wCPE[EWEjQ01Q1lQ1sP~P]P^P_PyPFPiP0Q1yPJP@Q1GQ19PvQ1FQ1<Q0@Q1zQ1jQ1SQ1{Q1wQ1fQ1iQ1xQ1tQ1pQ0DQ0TQ0GQ0NMO1Q0ZQ1|Q1gPePpPfF3?Y14X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1X=Lj3Q1]PL%ULACLhIPLPMPDPNPOQ1UPmD5P<PLPKP|PXP|PXQ1VP<C2Q0dPEPWP7Q1kP7DD\s^1wF@D6D7Q01Q1c/GP%UPACPhIPPPMPDPNPOQ1XPmP<ESPPPKQ1UP|Q1UP|Q1aP<C2Q0:PEPaP7Q1RP7DD\s^1wF@EWp+02HR4P]P^P_PRPyPFP~p+02CS0:PiPJP@Q1GQ19PvQ1FQ1<p+02=S0dQ1\Q1vp+02:S1|Q1zQ1jQ1SQ1{Q1wQ1fQ0@Q0DQ0TQ0GMO1Q0N%;4R1Q1uPeQ0ZPfF3P4P]P^P_P`PaPWP~Q0:PUPSPcPdPPPLP3P>Q0dQ1\Q1vQ1|Q1zQ1jQ1SQ1{Q1wQ1fP?P:P;P8MO1P7P1Q1uPeP5PfF3PjQ1hP5Q1hP5PkPlP5PMPDPNPOQ1qPmD5P<P5PKQ1gQ1dQ1gQ1dQ1mP<C23xS1dQ1eP7I0_D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1^/Gc%USACShIPSPMPDPNPOQ1ZPmP<ESPSPKQ1cQ1]Q1cQ1]Q1UP<C2PSPNPQPEQ0aP7Q1oP7DD\s^1wCPE[EWQ01Q0ePUPhPIPUPMPDPNPOQ1^PmD5P<PUPKQ1ZQ1cQ1ZQ1cQ1XP<C2PUPNPQPEQ0`P7Q1_P7DD\s^1wCPE[D6H0Fp+02LR1P]P^P_PCPRPyP4p+02GS0ePFPiPJP@Q1GQ19PvQ1Fp+02AS1sP0Q1yp+02>S1lQ0dQ1\Q1vQ1|Q1zQ1jQ1<Q0@Q0DQ0TMO1Q0G%;1S1~Q1xPeQ0NPfF3P1P]P^P_P`PaPWP4Q0ePUPSPcPdPPPLP3P>Q1sP0Q1yQ1lQ0dQ1\Q1vQ1|Q1zQ1jP?P:P;P8MO1P7Q1~Q1xPeP5PfF3PjQ1tP5Q1tP5PkPlP5PMPDPNPOQ1ePmD5P<P5PKQ1uQ1hQ1uQ1hQ1qP<C2Q1iP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5%UaQ17P`PMPDPNPOQ1bPmP<GQP`PKQ1RQ1kQ1RQ1kQ1ZP<C23xP`PNPQPEQ0]P7Q1TP7DD\s^1wCPEWQ01Q18P\PMPDPNPOQ1nPmD5P<P\PKQ1bQ1RQ1bQ1RQ1^P<C2P\PNPQPEPpP7Q1mP7DD\s^1wCPE[D6p+02PS18P]P^P_Q1VPCPRP1p+02KS17PyPFPiPJP@Q1GQ19Pvp+02ES1~P~Q0:p+02BS20Q1sP0Q1yQ1lQ0dQ1\Q1FQ1<Q0@Q0DMO1S21Q0TQ18#;S22Q1{PeQ0GPfF3S23Q18P]P^P_P`PaPWP1Q17PUPSPcPdPPPLP3P>Q1~P~Q0:Q20Q1sP0Q1yQ1lQ0dQ1\P?P:P;P8MO1P7Q22Q1{PeP5PfF3PjQ1wP5Q1wP5PkPlP5PMPDPNPOQ1iPmP<ESP5PKQ1xQ1tQ1xQ1tQ1eP<C2Q1SP7F=EWEjS243YX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0`?ChIQ0_PMPDPNPOQ1WPmD5P<Q0_PKQ1_Q1oQ1_Q1oQ1bP<C2Q0_PNPQPEPoP7Q1gP7DD\s^1wCPE[D6Q01Q0^PMPDPNPOQ1rPmP<GQQ0^PKQ1WQ1_Q1WQ1_Q1nP<C2Q0^PNPQPEQ0ZP7Q1qP7DD\s^1wCPE[p+02TS1qP]P^P_Q1UQ1VPCQ18p+02OS1gPRPyPFPiPJP@Q1GQ19p+02IS25P4Q0ep+02FS26Q1~P~Q0:Q20Q1sP0PvQ1FQ1<Q0@MO1Q0DQ1q#;S27Q1|PeQ0TPfF3S28Q1qP]P^P_P`PaPWQ18Q1gPUPSPcPdPPPLP3P>Q25P4Q0eQ26Q1~P~Q0:Q20Q1sP0P?P:P;P8MO1P7Q27Q1|PeP5PfF3PjQ1zP5Q1zP5PkPlP5PMPDPNPOQ1SPmP<ESP5PKQ1{Q1wQ1{Q1wQ1iP<C2Q1vP7F=EWEjS293YX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q1}9^pMQ0\PKQ1mQ1TQ1mQ1TQ1WP<C2Q0\PNPQPEQ0OP7Q1uP7DD\s^1wCPE[Q01Q0[PKQ1`Q1mQ1`Q1mQ1rP<GZQ0[PNPQPEQ0NP7Q1eP7DD\s^1wCPp+02XS1rP]P^P_Q1ZQ1UQ1VQ1qp+02SS1mPCPRPyPFPiPJP@Q1Gp+02MS1`P1Q17p+02JS1WQ25P4Q0eQ26Q1~P~Q19PvQ1FQ1<MO1Q0@Q1r#;S1TQ1lPeQ0DPfF3S1}Q1rP]P^P_P`PaPWQ1qQ1mPUPSPcPdPPPLP3P>Q1`P1Q17Q1WQ25P4Q0eQ26Q1~P~P?P:P;P8MO1P7Q1TQ1lPeP5PfF3PjQ0dP5Q0dP5PkPlP5PMPDPNPOQ1vPmP<ESP5PKQ1|Q1zQ1|Q1zQ1SP<C2Q1yP7F=EWEjS2:3YX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0ZQ1d7^KQ0PPNPQPEQ0LP7Q1xP7DD\s^1wCPQ01Q0Y?qNQPEQ0GP7Q1iP7DD\s^1wp+02\S01P]P^P_Q1bQ1ZQ1UQ1rp+02WS1dQ1VPCPRPyPFPiPJP@p+02QS2;Q18Q1gp+02NS2<Q1`P1Q17Q1WQ25P4Q1GQ19PvQ1FMO1Q1<Q01#;S1<Q20PeQ0@PfF3S2=Q01P]P^P_P`PaPWQ1rQ1dPUPSPcPdPPPLP3P>Q2;Q18Q1gQ2<Q1`P1Q17Q1WQ25P4P?P:P;P8MO1P7Q1<Q20PeP5PfF3PjQ1sP5Q1sP5PkPlP5PMPDPNPOQ1yPmP<ESP5PKQ1lQ0dQ1lQ0dQ1vP<C2Q0:P7F=EWEjS2>3YX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EP5Q0N?qNQPEQ0UP7Q1{P7DD\s^1wPEp+02_RwP]P^P_Q1_Q1RQ1cp+02[Rsp+02ZS1_P|PzP2Q1QPrPuQ1MPYQ1qQ1mp+02RRQQ2;Q18Q1gQ2<Q1`P1Q17Q00Q09Q1BQ1:MO1Q1D%;wRvQ1~PeQ0=PfF3PwP]P^P_P`PaPWPsQ1_PUPSPcPdPPPLP3P>Q1qQ1mPQQ2;Q18Q1gQ2<Q1`P1Q17P?P:P;P8MO1P7PvQ1~PeP5PfF3PjP~P5P~P5PkPlP5PMPDPNPOQ20PmD5P<P5PKQ1sP0Q1sP0Q1lP<C2Q26P7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDEQ1YPEp+02^RvP]P^P_Q1oQ1kQ1]Q1_p+02YRwPXQ1YPHPqQ1NQ1OPgQ13Q1mPQQ2;Q18Q1gQ2<Q1`P1Q17Q1WQ1CQ1@Q0;Q0<MO1Q1H%;vS2?P~PeQ0>PfF3PvP]P^P_Q1oPaPWQ1_PwPUPSPcPdPPPLP3P>Q1mPQQ2;Q18Q1gQ2<Q1`P1Q17Q1WP?P:P;P8MO1P7Q2?P~PeP5PfF3PjQ0:P5Q0:P5PkPlP5PMPDPNPOQ1sPmD5P<P5PKP0Q1yP0Q1yQ0dP<C2Q1~P7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBEPHPEp+02]RvP]P^P_Q1nQ1^Q1XPwQ1rQ1aQ1[PZPxQ1PPAQ0JP}PQQ2;Q18Q1gQ2<Q1`P1Q17Q1WQ25P[Q0KQ15PbMO1Q1;%;vS2?Q0:PeQ0?PfF3PvP]P^P_Q1nQ1^PWPwQ1rPUPSPcPdPPPLP3P>PQQ2;Q18Q1gQ2<Q1`P1Q17Q1WQ25P?P:P;P8MO1P7Q2?Q0:PeP5PfF3PjQ20P5Q20P5PkPlP5PMPDPNPOP0PmD5P<P5PKQ1yQ1lQ1yQ1lQ1\P<C2P~P7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAEPqPEQ2=Q01P]P^P_Q1bQ1ZQ1UQ1rQ1dPUPSPcPdPPPLP3P>Q2;Q18Q1gQ2<Q1`P1Q17Q1WQ25P4P?P:P;P8MO1P7Q1<Q20PeP5PfF3Q2>3YX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?EQ1NPEPsP]P^P_Q1RQ1cP|Q1dp+02VRvPzP2Q1QPrPuQ1MPYQ00Q18Q1gQ2<Q1`P1Q17Q1WQ25P4Q0eQ09Q1BQ1:Q1DMO1Q0=%;sS2>Q1sPeQ0APfF3PsP]P^P_Q1RQ1cP|Q1dPvPzPSPcPdPPPLP3P>Q18Q1gQ2<Q1`P1Q17Q1WQ25P4Q0eP?P:P;P8MO1P7Q2>Q1sPeP5PfF3PjP0P5P0P5PkPlP5PMPDPNPOQ1lPmD5P<P5PKQ0dQ1\Q0dQ1\Q1|P<C2Q20P7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>EQ1OPEQ1_P]P^P_Q1kQ1]PXPvp+02URsQ1YPHPqQ1NQ1OPgQ13Q1CQ1gQ2<Q1`P1Q17Q1WQ25P4Q0eQ26Q1@Q0;Q0<Q1HMO1Q0>Q1_#;S2>P0PeQ0BPfF3Q1_P]P^P_Q1kQ1]PXPvPsQ1YPHPcPdPPPLP3P>Q1gQ2<Q1`P1Q17Q1WQ25P4Q0eQ26P?P:P;P8MO1P7Q2>P0PeP5PfF3PjQ1yP5Q1yP5PkPlP5PMPDPNPOQ0dPmD5P<P5PKQ1\Q1vQ1\Q1vQ1zP<C2Q1sP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=EPgPEPwP]P^P_Q1^Q1XQ1aPsQ1qQ1[PZPxQ1PPAQ0JP}P[Q2<Q1`P1Q17Q1WQ25P4Q0eQ26Q1~Q0KQ15PbQ1;MO1Q0?%;wS2>Q1yPeQ0CPfF3PwP]P^P_Q1^Q1XQ1aPsQ1qQ1[PZPxPdPPPLP3P>Q2<Q1`P1Q17Q1WQ25P4Q0eQ26Q1~P?P:P;P8MO1P7Q2>Q1yPeP5PfF3PjQ1lP5Q1lP5PkPlP5PMPDPNPOQ1\PmD5P<P5PKQ1vQ1|Q1vQ1|Q1jP<C2P0P7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;EQ13PEQ1}Q1rP]P^P_Q1ZQ1UQ1VQ1qQ1mPCPRPyPFPPPLP3P>Q1`P1Q17Q1WQ25P4Q0eQ26Q1~P~P?P:P;P8MO1P7Q1TQ1lPeP5PfF3Q2:3YX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:EQ1CPEQ1dP]P^P_Q1cP|PzQ1mPQP2Q1QPrPuQ1MPYQ00Q09P1Q17Q1WQ25P4Q0eQ26Q1~P~Q0:Q1BQ1:Q1DQ0=MO1Q0AQ1d#;RwQ0dPeQ0EPfF3Q1dP]P^P_Q1cP|PzQ1mPQP2Q1QPrPuQ1MPLP3P>P1Q17Q1WQ25P4Q0eQ26Q1~P~Q0:P?P:P;P8MO1P7PwQ0dPeP5PfF3PjQ1\P5Q1\P5PkPlP5PMPDPNPOQ1|PmD5P<P5PKQ1zQ1jQ1zQ1jQ1{P<C2Q1lP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9EQ1@PEPvP]P^P_Q1]PXQ1YPQQ2;PHPqQ1NQ1OPgQ13Q1CQ1@Q17Q1WQ25P4Q0eQ26Q1~P~Q0:Q20Q0;Q0<Q1HQ0>MO1Q0B%;vRwQ1\PeQ0FPfF3PvP]P^P_Q1]PXQ1YPQQ2;PHPqQ1NQ1OPgQ13P3P>Q17Q1WQ25P4Q0eQ26Q1~P~Q0:Q20P?P:P;P8MO1P7PwQ1\PeP5PfF3PjQ1vP5Q1vP5PkPlP5PMPDPNPOQ1zPmD5P<P5PKQ1jQ1SQ1jQ1SQ1wP<C2Q0dP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8EQ0;PEPsP]P^P_Q1XQ1aQ1[Q2;Q18PZPxQ1PPAQ0JP}P[Q0KQ1WQ25P4Q0eQ26Q1~P~Q0:Q20Q1sQ15PbQ1;Q0?MO1Q0C%;sRwQ1vPeQ0SPfF3PsP]P^P_Q1XQ1aQ1[Q2;Q18PZPxQ1PPAQ0JP}P[P>Q1WQ25P4Q0eQ26Q1~P~Q0:Q20Q1sP?P:P;P8MO1P7PwQ1vPeP5PfF3PjQ1|P5Q1|P5PkPlP5PMPDPNPOQ1jPmD5P<P5PKQ1SQ1{Q1SQ1{Q1fP<C2Q1\P7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7EQ0<PEQ28Q1qP]P^P_Q1UQ1VPCQ18Q1gPRPyPFPiPJP@Q1GQ19Q25P4Q0eQ26Q1~P~Q0:Q20Q1sP0P?P:P;P8MO1P7Q27Q1|PeP5PfF3Q293YX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6EQ1HPEQ1mP]P^P_P|PzP2Q1gQ2<Q1QPrPuQ1MPYQ00Q09Q1BP4Q0eQ26Q1~P~Q0:Q20Q1sP0Q1yQ1:Q1DQ0=Q0AMO1Q0EQ1m#;R@Q1zPeQ0UPfF3Q1mP]P^P_P|PzP2Q1gQ2<Q1QPrPuQ1MPYQ00Q09Q1BP4Q0eQ26Q1~P~Q0:Q20Q1sP0Q1yQ1:P:P;P8MO1P7P@Q1zPeP5PfF3PjQ1jP5Q1jP5PkPlP5PMPDPNPOQ1{PmD5P<P5PKQ1wQ1fQ1wQ1fQ1xP<C2Q1|P7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5EQ0>PEPQP]P^P_PXQ1YPHQ2<Q1`PqQ1NQ1OPgQ13Q1CQ1@Q0;Q0eQ26Q1~P~Q0:Q20Q1sP0Q1yQ1lQ0<Q1HQ0>Q0BMO1Q0F%;QR@Q1jPeQ0XPfF3PQP]P^P_PXQ1YPHQ2<Q1`PqQ1NQ1OPgQ13Q1CQ1@Q0;Q0eQ26Q1~P~Q0:Q20Q1sP0Q1yQ1lQ0<Q1HP;P8MO1P7P@Q1jPeP5PfF3PjQ1SP5Q1SP5PkPlP5PMPDPNPOQ1wPmD5P<P5PKQ1fQ1iQ1fQ1iQ1tP<C2Q1zP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4EQ0BPEQ2;P]P^P_Q1aQ1[PZQ1`P1PxQ1PPAQ0JP}P[Q0KQ15Q26Q1~P~Q0:Q20Q1sP0Q1yQ1lQ0dPbQ1;Q0?Q0CMO1Q0SQ2;#;R@Q1SPeQ0QPfF3Q2;P]P^P_Q1aQ1[PZQ1`P1PxQ1PPAQ0JP}P[Q0KQ15Q26Q1~P~Q0:Q20Q1sP0Q1yQ1lQ0dPbQ1;Q0?P8MO1P7P@Q1SPeP5PfF3PjQ1{P5Q1{P5PkPlP5PMPDPNPOQ1fPmD5P<P5PKQ1iQ1xQ1iQ1xQ1pP<C2Q1jP7F=D6D7E8X0B,0BX2G,0GX3EQ0FPGQ23Q21P7Q22Q1{PeP5PfF3Q243YX0B,0BX2GQ0XPBQ1gP]P^P_PzP2Q1QQ17Q1WPrPuQ1MPYQ00Q09Q1BQ1:P~Q0:Q20Q1sP0Q1yQ1lQ0dQ1\Q1vQ1DQ0=Q0AQ0EMO1R~Q0UQ1g#;RYQ1wPeQ0LPfF3P~Q0UPYQ1wPeP5PfF3PjQ1fP5Q1fP5PkPlP5PMPDPNPOQ1xPmD5P<P5PKQ1tQ1pQ1tQ1pQ1uP<C2Q1{Q0UF=D6D7E8X0BPnQ2<P]P^P_Q1YPHPqQ1WQ25Q1NQ1OPgQ13Q1CQ1@Q0;Q0<Q0:Q20Q1sP0Q1yQ1lQ0dQ1\Q1vQ1|Q1HQ0>Q0BQ0FMO1Q0XQ2<Q1fPePnPfF:R00190Q1i=LjnRgQ1i/GnRq%UnRHACnVIRYPnPMPDPNPOQ1tPmP<GQR~PnPKQ1pQ1eQ1pQ1eQ1hP<GZRuQ1wQ0X+0;Rr'4R2'4Rz'4R@'4R['4R}'4Q02/r0PgP}Q0[PqP[Q0^PHP@P\PYPzP9PnPVPhPIP9PjQ1iPnPVPhQ1RQ0[Q0^Q1t$02RzQ0g'wQ1t#hQ0h'TRYPzQ1IQ1tO1Q1JQ1IQ1tQ1tQ1t,r6I0RQ0gQ0hQ1KJ0QQ1]H0PRzPYQ0iQ0jQ0kQ0lQ1f-0O=R@Q1f,T=Q1f#hRHQ1f'f'4Q1f/9=AA6H='4'RRHQ1w#hR=P6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ0vQ0wQ0xQ1?7X7Q0yPTPTQ0zQ08'tQ0|Q10=}6t,OtRtQ105BTQ1E5gTQ089BTt205T>5gTQ0~9BTtQ1>5gTPTQ03Q04Q04Q05I185aT5aT5aTDsQ11Q12bXbYbZXI6XL6Xc6X\{Xk{Xl{1978Q14/]7,?7RTQ14'9/R:19T;/R?Q1L,9T/R>Q0oH16[^I6^L6^c6^\{^k{^l{P5Q0I/9VQ0H/9V19IVPMQ07PVQ0cO7bWbRbSbTb`bbb^bVbUb_1]hV:15jVeN:13PUPzPYQ0iQ0jQ0kQ0lP@PHP=P6Q0mQ0nQ0pQ0qQ0rQ0sQ0tQ0uQ16bRbSbTb`bbb^bVbUb_L10P~P2PPPuPrP?P5ClClClClClClClH0IFbFbFbFbFbFbFbFbWzY09P7P5O2n2001000010121000000WGWuP7P5O2n2001000010121000000WGWsP7P5O2n2001000010121000000WGY04P7P5O2n2001000010121000000WGW~P7P5O2n2001000010121000000WGY0;P7P5O2n2001000010121000000WGY01P7P5O2n2001000010121000000WGPJP5J0CWGP7P5O2n2011000010121000000WGX0BP7P5O2n2011000010121100000WGX2GP7P5O2n2011000010121100000WGX3EP7P5O2n2011000010121100000WGX4EP7P5O2n2011000010121100000WGX5EP7P5O2n2011000010121100000WGX6EP7P5O2n2011000010121100000WGX7EP7P5O2n2011000010121100000WGX8EP7P5O2n2011000010121100000WGX9EP7P5O2n2011000010121100000WGX:EP7P5O2n2011000010121100000WGX;EP7P5O2n2011000010121100000WGX=EP7P5O2n2011000010121100000WGX>EP7P5O2n2011000010121100000WGX?EP7P5O2n2011000010121100000WGXAEP7P5O2n2011000010121100000WGXBEP7P5O2n2011000010121100000WGXDEP7P5O2n2011000010121100000bgbgbgWgWeQ02Q0fQ0{PjQ0CP5Q06PkPlQ1A9^5MP5PKQ0}Q0AP7I0_DmDeX0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0E[]eeJ0}b|bwbvbxY06Y05P7P5O2n2001000010121000000c0<Q0RQ0DP]P^P_Q0EQ0FQ0SQ0TQ0UQ1=Q0VQ0WQ0XQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZPoQ0[Q0\PpQ0]Q0^Q0_Q0`MO1Q0aQ0bP\PeP`PfF360@9ec0:Q02P\Q15P]P^P_P`PaPWPbQ1FPUPSPcPdPPPLP3P>Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0SP?P:P;P8MO1P7Q15Q0LPeP5PfF:PjPnP5PnP5PkPlP5PMPDPNPOQ0NPmD5P<P5PKQ0OQ0YQ0OQ0YQ0ZP<C2Q0GP7F=D6D7E8X0B,0BX2G,0GX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX=E,0EX>E,0EX?E,0EXAE,0EXBE,0EXDE,0EWeQ0EP]P^P_Q0FQ0SQ0TQ0UQ0XQ1=1NDSQ0WQ0QQ0GQ0LPnQ0MQ0NQ0OQ0YQ0PQ0ZPoQ0[Q0\PpQ0]Q0^Q0_Q0`Q0aMO1P\Q0bP`PePaPfF360@9eY07W}Y03WtW{Y02Y08WrP>P5DMWGZ0PEXiEZ0NEZ0O6X16Xo6Y0?Y0>W<X@EXCEXEEXFEZ0EEZ0DEZ0MEZ0LEZ0KEZ0JEZ0IEZ0HEZ0GEZ0FEXHEXJEXKEXMEXNEZ0CEZ0BEX]EXaEXdEY0Ao"). Qed.

  (* [comment removed for export] *)
  Lemma strnlen_callq : forall ra' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (P n : Z) (buf : list byte),
    stk psegs m lo (q + -544) ->
    bytes_at psegs m P buf ->
    memchr_ok P 0 n buf ->
    mem_inv psegs m ->
    (P + Z.of_nat (length buf) <= lo \/ q <= P)%Z -> (0 < P < 2^64)%Z -> (0 <= n < 2^64)%Z ->
    evt psegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          Ft (ret_pc ra') fc None m' (seg_rom psegs)
                 /\ munch [(q + -544 - 32, q + -544)]%Z m m'
                 /\ wmono psegs m m' /\ mem_inv psegs m'
                 /\ stk psegs m' lo (q + -544)
                 /\ bytes_at psegs m' P buf)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x24f2c) fc None m (seg_rom psegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "p'0h02m'h13a1'h23t6'h33t5'h43t4'h53t3'h63a7'h73a6'h82t6h93a5'h:3a4'h;2t5h<3a3'h=3a2'h>2t4h?3t2'h@2t3hA3t1'hB2a7hC3t0'hD2a6hE2a5hF1HhG2a4hH2a3hI2a2hJ4__x1hK2t2hL1zhM2t1hN2t0hO7__arithhP4__ffhQ7__sat12hR7__sat13hS7__sat14hT7__sat15hU8__varmaphV5__withW4__x2hX4cstrhY3ms'hZ2Hah[2PSh\4__p1h]4__x3h^4__x4h_2BBh`3BUFha4BUF'hb2Eahc2Enhd2Eqhe2Fthf2Hnhg2MIhh3MI'hi2MUhj2OKhk1Phl2P0hm3SEPhn2STho3ST'hp2WMhq3bufhr2fchs1mht1nhu3ra'hv2s0hw2s1hx3s10hy3s11hz2s2h{2s3h|2s4h}2s5h~2s6i002s7i012s8i022s9i031xp%0p%1p&0p;1p;2p;4p;5p;3p;Gp;Op;7p;6p;[p;Hp;8p103o^p6051002p104e@p4p710p8g007ej1@Tg008Jj1ZTg008hj1kTg00U>j1<Tg004?k20ITg00>Ak10CTg007Ej1xTg01ACk109Tg00dZj2DTg05GQj4oTg00:lj2LTg00N^j1KTg00A_j2;Tg00QIj2XTg013Gj1QTg01e2j2wTg00C3j2PTg00COS00j29Tg05HMk50<Tg00PBj1[Tg01mBj2rTg01mjj3qTg00Qcj1mTg00RBj2_Tg00Rkj3^Tg00STj2|Tg00Emj1{Tg00T@j3]Tg00FMj2\Tg01Bkk102Tg00T`j4fTg00Fkk101Tg00GIk10JTg00H4j2eTg00HWj2UTg01eok300Tg00Iej1~Tg01Clj3YTg01CIj3aTg00JGk20HTg00@Gj2}Tg00Jik20GTg00;Lj3RTg00KUk30FTg00L4k40ETg01?fj2ITg027Qj2lTg009Kj2?Tg026gj2ETg05IHmG0BmH0=Tg058GlO1Tg0599k10ATg03JKk20@Tg03S8j4uTg0158R0j20Tg05:2j73Tg00X<k60?Tg05JIm[0>Tg05@4j17Tg04bfj3FTg002Tj6gTg01S>j4WTg04m>j4hTg0030j6pTg05Ckk608Tg05:dk307Tg05Daj4vTg00cej4bTg044]k206Tg00I:j4yTg00WXj7zTg00X`k705Tg00YDk80DTg05KJk204Tg04cZj3nTg00Uck703Tf0R1#@#@p=M%<1#@p=s%@1#@#@#@p=Vg00j;S01f2R2f1R3P1Cvp=AQ01P2P3P1Cbp=NQ010061p=Cg00[2R4/P1p=T1;41p=>g00;fR5P3g00_jP1Cyp=dP3g00[PR6g00[oR7P7g00\OR8P1g00\oR9Fzp=cP2P6P7P7P8P5P3g00`QP1CyP9Fzp=BP2P6P7P7P8P3P1K05p=`f3R9P6P7P7P8P2P3P1L0Dp=G20431,?2p=2f6R:f5R;f4R<#7P9P2P3P1F3p=6Q01?n:;Q01P2P3P1Cb,99,9<'9p=4g04[FS02?R;<AF923/91'9p=5P5P<P9P2P3P1Epp=JP2P6P7P7P8P3P1K03p=tQ02f7R=P:P;P<P9P2P3P1F33Rp=jQ01?n31p=SQ01P9P2P3Cv/91p=i1931,92p=HQ01P2P3P1Cb,99,9<p=:Q02?R23/91p=8Q01P2P3P1Cb,99p>0;AF;<9Q01?n23/91'9p==Q02?R31p>0:P:P;P<P9P2P3P1ChChp=Og00<DR>#@R?#@S03#@R@#MRA#@RB#ZRC#kRD%<?RE#Z00ID%ZA#k%Z@#kRF$0C\DRG%xFp,2loRHp,1qRI%s@#V$09R@'DRJ5A9AN<93P<P4P9P2Co%C:1LF<#K,D:/;H1;I:'X%T=%Q?RK%QBRB'wRL,P=RM'9%>=/9MQ01f:RMf9RNP=P;I0<%>N1LF=#K,DN/;L'9f8RO,LFRP#[%KP#>%<E#<#<RP#QRQ,rKRR%TKRS%>Q1wKQRT#T[[RU%>KRVg01WWRWAqKQ3UWZRQ%>T\W^ZVRX1rKBRY%>B%TL[\SRSAqKB3VWXZVRB%>L\W^ZVRVg00_>RWg00b3RZ#mR[#mS04,_5S051_5[S061_5Z5^55^5g00bRS07'|%{WRZ3]%xWR[P51\52P3&025S08CfS09&015R\&0J5R]1e5>R^1U5KRK%ZP6005'd,c]%~7RPP]%@>#<#<#M#<#V#V#V#QR_,U51e5?R?5B]PPP]%@E#M#<#M#V#QRE,U5S0:9Y5^9B]?PP1U54R`1U5@S0;9a5^Ra5B]B005KCRK,da,c]5`]CGCGCG20H]8RaP1P2g00^^Rbg00a8Rc'}20G12=RbcdB0F543H0ERcbPbUbVXJ5XW51P1T1;_21I2E,;91D9@R_#>1P_L'9[[[^J5^W5P1PHPIp,3QHIp,3GLOp,2LOS0<O5bObQbRbSbTbX,lJ1?CJR_,ECS0==R5Jf;RT1LFNRb#[%Kb#>PRPUPQPXPYPSPBPVPZP[1\53S0>P\P]1d`^,c]S0?1d^K,c]RK5`]PPAB]`^=`]KRKCGPaPcbPbUbVXJ5%T1S0@1P1LR`'9%>31P3L'9Rb[^J5P1fAS0APNO2RdbObQbRbSbTbX'l1?CT,EC=R5TRe1LFMRf#[%Kf#>PRPUPQPXPYPSPBPVPZP[Q0>P\P]PKPPPKCGPaPcbPbUbVXJ5%>1/9`Pb[^J5PdbObQbRbSbTbX,lTPeQ01fZReP_p,2gpRdp,2tpRbfVS0BfUS0CfNS0DfMS0EfLR`fKS0FfJS0GfIS0HfHS0IfGS0JfFS0KfES0Lf@RKf?Rff=Rg,?CRhf<Ri,?CRjPTPHf>RkNG0BQ02PffjRlP_PdPbPkPgPiffRmfeS0MQ0F92C`PTPMPNPOP=P:P;f^Rnf]Rof\Rpf[RqPefYRrfXRsfWS0NQ0BQ0CP<P9P2P3MO1fPRtPlfORu%~DRvP1Q01$0ARwF620@55RxP5P5%QARA,IJS0OPJCu%{xS0P3]RyQ0DP1Q0DP1%C1RzAA1HJR{P1Q0EQ0FF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DWYPeP_PdPbPrPsQ0NQ0BQ0CPhPjfTR|fSS0QfRS0RfQR}PtPuQ0DQ0EP`Q0FQ0GQ0HQ0IQ0JQ0KQ0LfDS0SfCS0TfBS0UQ0AMO1PK%M>#<#M#<#<#<#<#M#s#<#<#M#Q,?CS0VPfPvPkPwF3PeP_PdPbPrPsQ0NQ0BQ0CPhPjP|Q0QQ0RP}PtPuQ0DQ0EP`Q0FQ0GQ0HQ0IQ0JQ0KQ0LQ0SQ0TQ0UQ0APKPfPkPTPHPJAAfH1XL5PMQ0=P2DJPgANf1iXL5PN1EChR~P3DJPgP1P4P~PiCoXL5PiPkP4P1PiCoXL5PO1ECjP1DJP~P3DJP=PJ1I1AS0W,;HXL51LFTRj#[S0X%Kj#>S0YPRPUPQPXPYPSPBPVPZP[Q09P\P]Q0:9Y5?9B]^PPQ0;9a5?1U5AS095Y59B]^CGPaPcbPbUbVXJ5XW51I3E,;11D2@/IA,;3[^J5^W5P1PIPHQ0<O3bObQbRbSbTbXQ0=P2DJPJ1?CkS0Z,ECRj1LFi#KR4'DQ0W';1;1j'XXL5Pg1D14Q0O';1;J1'XXL5Q0XQ0YPRPUPQPXPYPSPBPVQ04#m,_5Q05Q065^55^5Q07'|=]WZP[P5P51\5<P2Q08CfP31\59CfP\P]Aa5^?R?Q03,e5RW5B]%<>,e5R>=B]^5t]PPP]Q0:9Y5>9B]WPPQ0;9a5>R>Q095Y59B]?AB]>^5t]CGCGPaPcbPbUbVXJ5XW5X]5X^51D13/;91;21'X1I9E,;<1D291D<@R@/IA';1;@2'X[[^J5^W5^]5^^5P1PHPIQ0A,LF#KQ0TPiQ0<O6bObQbRbSbTbXP~P3DJQ0=P2DJPgQ0@XL5Q0XQ0YPRPUPQPXPYPSPBPVp-0RVPZP[Q0>P\P]Q0?P]P6P7P7P8P9J0?5`]PPQ0?CGPaPcbPbUbVXJ5W\Q0@/93%T3[^J5^\VP1Q0T/PLQ0TPTO3bObQbRbSbTbXP~P3DJN[0>Q02PqP_PdPbQ0NQ0BPuQ0DQ0EP`Q0FQ0GQ0HQ0IQ0JQ0KQ0APKQ0ZPhPiPHPfP1NH0=S0ZP5Q0=Q0AflRhP_PdPbPkPgPifhR~fgRLQ0D,?C,ECRVQ0E52CPTPMPNPOP=P:P;f`Rcf_RaPnPoPpPqPePrPsQ0NP<P9P2P3MO1Q0R%7hP}PvP1PwGjRPP5P51IfAPfCuQ0P5]x?Ft11St1RxP1PHPf1?Cu,ECRAQ0E5N1Ci7Hz3HX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DXL5P1PJP<EgfkR]P_PdPbPkPgPiPLPmQ0E,?C,EC=2C`PTPMPNPOP=P:P;PaPnPoPpPqPePrPsQ0NQ0BP<P9P2P3MO1P}%7]S0PPtPvP1PwF3AFyu1S0=1Su1S0@PzP{P1PVP`D:3H58KX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DP51?CK,ECRVQ0UfmR8P_PdPbPkPgPifiR7P~Q0D92CAPTPMPNPOP=P:P;faRAPcPaPnPoPpPqPePrPsP<P9P2P3MO1Q0Q%78R6Q0RPvP1PwF3AFy}1R\1S}1R[PzP{P1PfQ0DD:3H38X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DXL5P1PKP<EgAFyt1P{P1PuQ0EH0;9Hxz5HPX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DP5PVQ0TfnRVP_PdPbPkPgPiPlP7A2CfuPTPMPNPOP=P:P;fbS0?PAPcPaPnPoPpPqPePrP<P9P2P3MO1P|%7VRPQ0QPvP1PwF3PyQ0RP1Q0RP1PzP{P1P}PuD:E=Rx38X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DXL5P1PKP<EgQ0UP8P_PdPbPkPgPiP7P~Q0D92CuPTPMPNPOP=P:P;PAPcPaPnPoPpPqPePrPsP<P9P2P3MO1Q0QP6Q0RPvP1PwF3PzP{P1PtQ0DD:9H\[38X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXND,0DP0PDQ0TPVP_PdPbPkPgPiPlP7A2CtuPTPMPNPOP=P:P;Q0?PAPcPaPnPoPpPqPePrP<P9P2P3MO1P|PPQ0QPvP1PwF3;8xX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DXNDQ0SfoRxP_PdPbPkPgPiP]PlA2C}tPTPMPNPOP=P:P;fcS0>Q0?PAPcPaPnPoPpPqPeP<P9P2P3MO1Q0CPxP|PvP1PwF6PyQ0QP1Q0QP1PzP{P1Q0RPtF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0LfpRPP_PdPbPkPgPiPhP]Q0R=2C}PTPMPNPOP=P:P;fdR[Q0>Q0?PAPcPaPnPoPpPqP<P9P2P3MO1Q0BPPQ0CPvP1PwF6PyP|P1P|P1PzP{P1Q0QP}F4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMD,0DP0PDQ0KfqS0YP_PdPbPfPgPiP8PhQ0QQ0R52CPTPMPNPOP=P:P;Q0MP[Q0>Q0?PAPcPaPnPoPpP<P9P2P3MO1Q0NQ0YQ0BPvP1PwF6PyQ0CP1Q0CP1PzP{P1P|Q0RF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DXMDQ0IfsR\P_PdPbPkPgPiPxPVQ0C=2C|R6PTPMPNPOP=P:P;PLPmQ0MP[Q0>Q0?PAPcPaPnP<P9P2P3MO1Pr%7\RZPsPvP1PwF3PyQ0NP1Q0NP1PzP{P1Q0BP|D:E=RB38X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0IP\P_PdPbQ0APgPiPxPVP6PTPMPNPOP=P:P;PLPmQ0MP[Q0>Q0?PAPcPaPnP<P9P2P3MO1PrPZPsPvP1PwF3;8BX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKD,0DP0PDQ0HftRBP_PdPbQ0UPkPiPPPxQ0BQ0C52CPTPMPNPOP=P:P;P~PLPmQ0MP[Q0>Q0?PAPcPaP<P9P2P3MO1PePBPrPvP1PwF6PyPsP1PsP1PzP{P1Q0NQ0CF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DXKDfwRZP_PdPbPkPgPiP\frR6A2CrsRSPTPMPNPOP=P:P;P]PlP7P~PLPmQ0MP[Q0>Q0?P<P9P2P3MO1Po%7ZRYPpPvP1PwF3PyPqP1PqP1PzP{P1PePsD:E=RX58`X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0FfvRQP_PdPbQ0SPKPiP6Q0YQ0N92CsPTPMPNPOP=P:P;PlP7P~PLPmQ0MP[Q0>Q0?PAP<P9P2P3MO1PpPQPqPvP1PwF6PyPeP1PeP1PzP{P1PrQ0NF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1D,0DP0PDPZP_PdPbQ0LQ0APgP\P6PSPTPMPNPOP=P:P;P]PlP7P~PLPmQ0MP[Q0>Q0?P<P9P2P3MO1PoPYPpPvP1PwF3=8`XX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DX1DPtf{RXP_PdPbPkPgPiPZPQA2CopPTPMPNPOP=P:P;PxPVP8PhP]PlP7P~PLPmP<P9P2P3MO1PAPXPcPvP1PwF6PyPaP1PaP1PzP{P1PnPpF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0DfyRYP_PdPbQ0JQ0TPffuRSPBA2CqePTPMPNPOP=P:P;P8PhP]PlP7P~PLPmQ0MP[P<P9P2P3MO1PaPYPnPvP1PwF6PyPoP1PoP1PzP{P1PpPeF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXID,0DP0PDPufzRUP_PdPbQ0IQ0SPKPQPSA2CpqPiPMPNPOP=P:P;PVP8PhP]PlP7P~PLPmQ0MP<P9P2P3MO1PcPUPaPvP1PwF6PyPnP1PnP1PzP{P1PoPqF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DXIDp+01@RRP_PdPbPkPgPiPXPUA2CAcRFPTPMPNPOP=P:P;P\P6Q0YPPPxPVP8PhP]PlP<P9P2P3MO1Q0M%7RRIP[PvP1PwF3PyQ0>P1Q0>P1PzP{P1Q0?PcD:E=R@58|X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1P}f|REP_PdPbQ0GQ0KQ0UfxR>PZA2CnoPkPMPNPOP=P:P;PPPxPVP8PhP]PlP7P~PLP<P9P2P3MO1Q0?PEPAPvP1PwF6PyPcP1PcP1PzP{P1PaPoF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHD,0DP0PDQ0Rf}R^P_PdPbQ0FQ0JQ0TPYP>A2CanPfPTPNPOP=P:P;Q0YPPPxPVP8PhP]PlP7P~P<P9P2P3MO1Q0>P^Q0?PvP1PwF6PyPAP1PAP1PzP{P1PcPnF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DXHDp+01DR?P_PdPbPkPgPiPRf~RWQ0M=2C[S0XPTPMPNPOP=P:P;PZPQPSPBP\P6Q0YPPPxPVP<P9P2P3MO1P7%7?R4P~PvP1PwF3PyPLP1PLP1PzP{P1PmP[D:E=Rj58sX0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1PRP_PdPbQ0EQ0HQ0LPXPUPFQ0APgPNPOP=P:P;P\P6Q0YPPPxPVP8PhP]PlP<P9P2P3MO1Q0MPIP[PvP1PwF3=8|@X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGD,0DP0PDQ0Cp+01AR@P_PdPbQ0DQ0GQ0KPEPXQ0?=2CAQ0UPkPMPOP=P:P;PBP\P6Q0YPPPxPVP8PhP]P<P9P2P3MO1PmP@Q0MPvP1PwF6PyP[P1P[P1PzP{P1Q0>PAF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DXGDPpp+01HS0<P_PdPbPkPgPiP?p+01CS09A2C7~PTPMPNPOP=P:P;PXPUPYP>PZPQPSPBP\P6P<P9P2P3MO1P8Q0<PhPvP1PwF6PyP]P1P]P1PzP{P1PlP~F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0NQ09P_PdPbPtP`Q0IPWP^Q0>92C[Q0SPKPiPOP=P:P;PQPSPBP\P6Q0YPPPxPVP8P<P9P2P3MO1P~Q09PLPvP1PwF6PyPmP1PmP1PzP{P1Q0MQ0>F4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXED,0DP0PDP?P_PdPbP}Q0EQ0HPRPWQ0XQ0LQ0APgPNP=P:P;PZPQPSPBP\P6Q0YPPPxPVP<P9P2P3MO1P7P4P~PvP1PwF3=8sjX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DXEDp+01LS0XP_PdPbPkPgPiQ0<p+01GS0;A2C8hRjPTPMPNPOP=P:P;PRPWP^PEPXPUPYP>PZPQP<P9P2P3MO1Q0YQ0X#7R4PPPvP1PwF3PyPxP1PxP1PzP{P1PVPhD:E=RI58cX0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Pep+01FS0:P_PdPbQ0QPuQ0Fp+01BS03P@A2CLmQ0JQ0TPfPTP=P:P;PYP>PZPQPSPBP\P6Q0YPPP<P9P2P3MO1P]Q0:PlPvP1PwF6PyP7P1P7P1PzP{P1P~PmF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDD,0DP0PDPqQ0;P_PdPbP|PtP`Q09Q03A2C~LQ0IQ0SPKPiPOP:P;PUPYP>PZPQPSPBP\P6Q0YP<P9P2P3MO1PhQ0;P]PvP1PwF6PyPlP1PlP1PzP{P1P7PLF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DXDDp+01PS08P_PdPbPkPgPiQ0Xp+01KS07Q0Y=2CPS06PTPMPNPOP=P:P;P?Q09Q03P@PRPWP^PEPXPUP<P9P2P3MO1PSQ08#7S05PBPvP1PwF3PyP\P1P\P1PzP{P1P6PPD:E=RF58[X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Pop+01IS04P_PdPbQ0BQ0RQ0Dp+01ES0OP?A2Cl7Q0GQ0KQ0UPkPMP:P;PEPXPUPYP>PZPQPSPBP\P<P9P2P3MO1PVQ04P8PvP1PwF6PyPhP1PhP1PzP{P1P]P7F4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBD,0DP0PDPnp+01JS0WP_PdPbQ0NQ0QPuQ0:Q0OA2C]lQ0FQ0JQ0TPfPTP=P;P^PEPXPUPYP>PZPQPSPBP<P9P2P3MO1PxQ0WPVPvP1PwF6PyP8P1P8P1PzP{P1PhPlF4E5X0G,0GX8D,0DX;D,0DX>D,0DX@D,0DXBDP~p+01TS0[P_PdPbPkPgPiQ08p+01OS0\A2CSBPTPMPNPOP=P:P;Q0<Q0;Q0:Q0OP?Q09Q03P@PRPWP<P9P2P3MO1PYQ0[P>PvP1PwF6PyPZP1PZP1PzP{P1PQPBF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0XP_PdPbPrQ0CP}Q0<Q0;PjQ0EQ0HQ0LQ0APgPNP;PRPWP^PEPXPUPYP>PZPQP<P9P2P3MO1Q0YP4PPPvP1PwF3=8cIX0G,0GX8D,0DX;D,0DX>D,0DX@D,0DP0PDPAp+01MS0]P_PdPbPeQ0BQ0RQ04Q0<A2CV8Q0DQ0GQ0KQ0UPkPMP:P@PRPWP^PEPXPUPYP>PZP<P9P2P3MO1P6Q0]Q0YPvP1PwF6PyPPP1PPP1PzP{P1PxP8F4E5X0G,0GX8D,0DX;D,0DX>D,0DX@Dp+01XS0^P_PdPbPkPgPiQ0[p+01SS0_A2CY>S0`PTPMPNPOP=P:P;Q0XQ07Q0WQ04Q0<Q0;Q0:Q0OP?Q09P<P9P2P3MO1P^Q0^#7S0aPEPvP1PwF3PyPXP1PXP1PzP{P1PUP>D:E=RI58hX0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0>Q0\P_PdPbPpPsP|Q07Q0WA2CPxPtP`Q0IQ0SPKPiPOQ09Q03P@PRPWP^PEPXPUPYP<P9P2P3MO1PBQ0\P\PvP1PwF6PyP6P1P6P1PzP{P1Q0YPxF4E5X0G,0GX8D,0DX;D,0DX>D,0DP0PDQ08P_PdPbPoPrQ0CQ0XQ07Q06P}Q0EQ0HQ0LQ0APgPNP?Q09Q03P@PRPWP^PEPXPUP;P9P2P3MO1PSQ05PBPvP1PwF3=8[FX0G,0GX8D,0DX;D,0DX>DPPp+01\S05P_PdPbPkPgPiQ0^p+01WS06A2C^ES0bPTPMPNPOP=P:P;Q08Q0\p+01NS0cQ0]Q0XQ07Q0WQ04Q0<Q0;P<P9P2P3MO1Q03Q05#7S0dP@PvP1PwF3PyPRP1PRP1PzP{P1PWPEF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Pmp+01RS0eP_PdPbPaPqQ0NQ0cQ0]A2C\6Q0QPuQ0FQ0JQ0TPfPTQ0:Q0OP?Q09Q03P@PRPWP^PEP=P9P2P3MO1PZQ0ePQPvP1PwF6PyPSP1PSP1PzP{P1PBP6F4E5X0G,0GX8D,0DX;D,0DP0PDPLQ0_P_PdPbPcPpPsQ0\Q0cA2CB\P|PtP`Q0IQ0SPKPiQ0;Q0:Q0OP?Q09Q03P@PRPWP^POP<P2P3MO1P>Q0_PZPvP1PwF6PyPQP1PQP1PzP{P1PSP\F4E5X0G,0GX8D,0DX;DPBp+01`RFP_PdPbPkPgPiQ05p+01[S0fQ03=2C@PTPMPNPOP=P:P;Q0[Q0_Q0ep+01QS0gQ08Q0\Q0cQ0]Q0XQ07P<P9P2P3MO1Q0:PFQ0OPvP1PwF6PyP?P1P?P1PzP{P1Q09P@F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1P7p+01US0hP_PdPbQ0?PnPeQ0gQ08A2CQSQ0BQ0RQ0DQ0GQ0KQ0UPkQ04Q0<Q0;Q0:Q0OP?Q09Q03P@PRPMP:P2P3MO1PUQ0hPYPvP1PwF6PyP>P1P>P1PzP{P1PZPSF4E5X0G,0GX8D,0DP0PDPlp+01VS0iP_PdPbQ0>PaPqQ0eQ0gA2CZQQ0NQ0QPuQ0FQ0JQ0TPfQ0WQ04Q0<Q0;Q0:Q0OP?Q09Q03P@PTP=P9P3MO1PXQ0iPUPvP1PwF6PyPYP1PYP1PzP{P1P>PQF4E5X0G,0GX8DP>p+01dR4P_PdPbPkPgPiPFp+01_RjQ0:Q0O52CPTPMPNPOP=P:P;Q0^Q06Q0iQ0hQ0[Q0_Q0eQ0gQ08Q0\P<P9P2P3MO1Q0WP4Q04PvP1PwF6PyQ0<P1Q0<P1PzP{P1Q0;Q0OF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0^P_PdPbQ0MPAPoQ0[Q0_Q0`PrQ0CP}Q0EQ0HQ0LQ0AQ0XQ07Q0WQ04Q0<Q0;Q0:Q0OP?Q09PgPNP;P3MO1P^Q0aPEPvP1PwF3=8hIX0G,0GP0PGP8p+01YS0aP_PdPbPmQ0?PnQ0hQ0[A2CUYPeQ0BQ0RQ0DQ0GQ0KQ0UQ0]Q0XQ07Q0WQ04Q0<Q0;Q0:Q0OP?PkPMP:P2MO1PWQ0aP^PvP1PwF6PyPEP1PEP1PzP{P1PXPYF4E5X0GPEp+01hR0P_PdPbPkPgPiP4p+01cRIQ0WQ0452CPTPMPNPOP=P:P;Q05Q0fp+01ZS0`Q0aQ0^Q06Q0iQ0hQ0[Q0_P<P9P2P3MO1Q0cP0Q0]PvP1PwF6PyQ0XP1Q0XP1PzP{P1Q07Q04F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1PxQ0fP_PdPbP~P[PcQ06Q0iA2CEXPpPsP|PtP`Q0IQ0SQ0\Q0cQ0]Q0XQ07Q0WQ04Q0<Q0;Q0:PKPiPOP<MO1P@Q0fPRPvP1PwF6PyPWP1PWP1PzP{P1P^PXF4E5Q00PPQ05P_PdPbP7Q0MPAQ0^Q06Q0bPoPrQ0CP}Q0EQ0HQ0LQ08Q0\Q0cQ0]Q0XQ07Q0WQ04Q0<Q0;Q0APgPNP;MO1Q03Q0dP@PvP3PwGjPyPRP3PRP3%C3AA3HJP3PWPED:E=P@p+01lS0dP_PdPbPkPgPiP0p+01gS0bQ0cQ0]52CPTPMPNPOP=P:P;PFPjp+01^S0jp+01]S0kQ05Q0fQ0`Q0aQ0^Q06P<P9P2P3MO1Q0eQ0dQ0gPvP1PwF6PyQ08P1Q08P1PzP{P1Q0\Q0]F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1P6Q0jP_PdPbP]PLQ0>Q0`Q0aA2CRWPaPqQ0NQ0QPuQ0FQ0JQ0eQ0gQ08Q0\Q0cQ0]Q0XQ07Q0WQ04Q0TPfPTP=MO1P?Q0j#7Q09PvP9PwGjQ02PjP_PdPbPhP~P[Q0fQ0`A2C@RPcPpPsP|PtP`Q0IQ0_Q0eQ0gQ08Q0\Q0cQ0]Q0XQ07Q0WQ0SPKPiPOMO1Q0OPjP?PvP<PwF6Q02AFy?;S0lP?P;%C;AA;HJP;Q09P@F4S0m'9p+020S0nP_PdPbPkPgPiQ0dp+01kS0oQ0eQ0g52CS0pPTPMPNPOP=P:P;P4PIp+01bS0qp+01aS0rPFPjQ0jQ0kQ05Q0fP<P9P2P3MO1Q0iQ0n#7S0sQ0hPvP1PwF3S0tPyQ0[P1Q0[P1PzP{P1Q0_Q0gD:E=S0u58KX0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0D[WYPyQ09P<Q09P<%C<AA<HJP<Q03PRD:E=Q00Q0lQ0mQ0nP_PdPbP^PYPSQ0dQ0oQ0pQ0YP8P7Q0MPAPoPrP4PIQ0qQ0rPFPjQ0jQ0kQ05Q0fQ0CP}Q0EQ0HMO1Q0iQ0sQ0hPvQ0LPwF3S0sQ0tQ0u38X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0:=Fy=Q0;PO%COAAOHJPOQ0:P?F4Q00Q0</SN%CNAANHJPNQ0;Q0OD:p+024S0uP_PdPbQ03P^PYQ0np+01oS0tQ0iQ0h52CS0pPSQ0YP8P7Q0MPAPoP0Q0bp+01fS0mp+01eS0lP4PIQ0qQ0rPFPjPrQ0CP}Q0EMO1Q0`Q0u#7S0vQ0aPvQ0HPwF3S0wQ0uP_PdPbPkPgPiQ0nQ0tQ0pPTPMPNPOP=P:P;P0Q0bQ0mQ0lP4PIQ0qQ0rPFPjP<P9P2P3MO1Q0`Q0vQ0aPvP1PwF3PyQ0^P1Q0^P1PzP{P1Q06Q0hD:E=S0x38X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0W/ST%CiAAiHJPiQ0WQ0<D:Q00%CgPgPHPJQ07Q045NgCip+028S0yP_PdPbQ0:Q03P^Q0up+023S0zQ0`Q0a52CS0{PYPSQ0YP8P7Q0MPAQ0dQ0op+01jS0|p+01iS0}P0Q0bQ0mQ0lP4PIPoPrQ0CP}MO1Q0jQ0y#7S0~Q0kPvQ0EPwF3S10Q0yP_PdPbPkPgPiQ0uQ0zQ0{PTPMPNPOP=P:P;Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lP4PIP<P9P2P3MO1Q0jQ0~Q0kPvP1PwF3PyQ05P1Q05P1PzP{P1Q0fQ0aD:E=S1138X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1%CfPKPHPJQ0cQ0X5NKCiQ00Q0A?AHJQ0AQ0\Q0]3Np+02<S0\P_PdPbQ0WQ0:Q03Q0yp+027S00Q0jQ0k52CS0cP^PYPSQ0YP8P7Q0MQ0nQ0tp+01nS12p+01mS13Q0dQ0oQ0|Q0}P0Q0bPAPoPrQ0CMO1Q0qQ0\#7S14Q0rPvP}PwF3S15Q0\P_PdPbPkPgPiQ0yQ00Q0cPTPMPNPOP=P:P;Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}P0Q0bP<P9P2P3MO1Q0qQ14Q0rPvP1PwF3PyPFP1PFP1PzP{P1PjQ0kD:E=S1638X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DP1Q0T?AHJQ0SQ0eQ083NPDp+02?S08P_PdPbQ0]Q04Q0Op+02;S0]p+02:S17Q0r=2CFS18P@PEP>PBPPPhP~Q0zp+022S19p+021S1:Q0nQ0tQ12Q13Q0dQ0oQ0|P[PcPpPsMO1Q0lQ08#7S1;P4PvP|PwF3Q08P_PdPbPkPgPiQ0]Q17Q18PTPMPNPOP=P:P;Q0zQ19Q1:Q0nQ0tQ12Q13Q0dQ0oQ0|P<P9P2P3MO1Q0lQ1;P4PvP1PwF3PyPIP1PIP1PzP{P1Q0qPFF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCDP^PDp+02>S1;P_PdPbQ0XQ0<P?Q17p+029S18A2CFjS08PRPXPZP\PxP]PLQ19Q1:Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}Q0>PaPqQ0NMO1P4Q1;#7S1<PIPvQ0QPwF3Q1;P_PdPbQ0XPgPiQ17Q18Q08PTPMPNPOP=P:P;Q19Q1:Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}P<P9P2P3MO1P4Q1<PIPvP1PwF3PyQ0qP1Q0qP1PzP{P1Q0rPjF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXADPYPDp+02=S1<P_PdPbQ07Q0;Q09Q18Q0yQ0j92CjS08PWPUPQP6PVPlPmQ1:Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}P0Q0?PnPeQ0BMO1PIQ1<#7S0XQ0qPvQ0RPwF3Q1<P_PdPbQ07Q0;PiQ18Q0yQ08PTPMPNPOP=P:P;Q1:Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}P0P<P9P2P3MO1PIQ0XQ0qPvP1PwF3PyQ0rP1Q0rP1PzP{P1PFQ0jF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?DPSPDQ15Q0\P_PdPbQ0WQ0:Q03Q0yQ00Q0cPTPMPNPOP=P:P;Q0nQ0tQ12Q13Q0dQ0oQ0|Q0}P0Q0bP<P9P2P3MO1Q0qQ14Q0rPvP1PwF3Q1638X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1DQ0YPDQ0]P_PdPbQ04Q0OP@Q00p+026S16Q0kQ0552CS15PEP>PBPPPhP~P[Q0tQ12Q13Q0dQ0oQ0|Q0}P0Q0bQ0mPcPpPsP|MO1Q0rQ0]#7S14PFPvPtPwF3Q0]P_PdPbQ04Q0OP@Q00Q16Q15PEPMPNPOP=P:P;Q0tQ12Q13Q0dQ0oQ0|Q0}P0Q0bQ0mP<P9P2P3MO1Q0rQ14PFPvP1PwF3PyPjP1PjP1PzP{P1Q0jQ05F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=DP8PDQ17P_PdPbQ0<P?PRQ16p+025S14Q05Q0f52CS15PXPZP\PxP]PLQ0>Q12Q13Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lPaPqQ0NQ0QMO1PFQ17#7S04PjPvPuPwF3Q17P_PdPbQ0<P?PRQ16Q14Q15PXPZPNPOP=P:P;Q12Q13Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lP<P9P2P3MO1PFQ04PjPvP1PwF3PyQ0jP1Q0jP1PzP{P1Q0kQ0fF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<DP7PDQ18P_PdPbQ0;Q09PWQ14Q0uQ0fQ0`52CS04PUPQP6PVPlPmQ0?Q13Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lP4PnPeQ0BQ0RMO1PjQ18#7S15Q0jPvQ0DPwF3Q18P_PdPbQ0;Q09PWQ14Q0uQ04PUPQP6POP=P:P;Q13Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lP4P<P9P2P3MO1PjQ15Q0jPvP1PwF3PyQ0kP1Q0kP1PzP{P1Q05Q0`F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:DQ0MPDQ10Q0yP_PdPbQ0:Q03P^Q0uQ0zQ0{PYPSQ0YP8P=P:P;Q0dQ0oQ0|Q0}P0Q0bQ0mQ0lP4PIP<P9P2P3MO1Q0jQ0~Q0kPvP1PwF3Q1138X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9DPAPDQ00P_PdPbQ0OP@PEQ0zQ19Q0aQ0^52CS11P>PBPPPhP~P[PcQ0oQ0|Q0}P0Q0bQ0mQ0lP4PIQ0qPpPsP|PtMO1Q0kQ00#7S10Q05PvP`PwF3Q00P_PdPbQ0OP@PEQ0zQ19Q11P>PBPPPhP~P:P;Q0oQ0|Q0}P0Q0bQ0mQ0lP4PIQ0qP<P9P2P3MO1Q0kQ10Q05PvP1PwF3PyQ0fP1Q0fP1PzP{P1Q0`Q0^F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7DPoPDQ16P_PdPbP?PRPXQ19Q1:Q0^Q0652CS10PZP\PxP]PLQ0>PaQ0|Q0}P0Q0bQ0mQ0lP4PIQ0qQ0rPqQ0NQ0QPuMO1Q05Q16#7S0oQ0fPvQ0FPwF3Q16P_PdPbP?PRPXQ19Q1:Q10PZP\PxP]PLQ0>P;Q0|Q0}P0Q0bQ0mQ0lP4PIQ0qQ0rP<P9P2P3MO1Q05Q0oQ0fPvP1PwF3PyQ0`P1Q0`P1PzP{P1Q0aQ06F4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6DPrPDQ14P_PdPbQ09PWPUQ1:Q0nQ06Q0i52CS0oPQP6PVPlPmQ0?PnQ0}P0Q0bQ0mQ0lP4PIQ0qQ0rPFPeQ0BQ0RQ0DMO1Q0fQ14#7R?Q0`PvQ0GPwF3Q14P_PdPbQ09PWPUQ1:Q0nQ0oPQP6PVPlPmQ0?PnQ0}P0Q0bQ0mQ0lP4PIQ0qQ0rPFP<P9P2P3MO1Q0fP?Q0`PvP1PwF3PyQ0aP1Q0aP1PzP{P1Q0^Q0iF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5DQ0CPDQ0wQ0uP_PdPbQ03P^PYQ0nQ0tQ0pPSQ0YP8P7Q0MPAPoP0Q0bQ0mQ0lP4PIQ0qQ0rPFPjPrP9P2P3MO1Q0`Q0vQ0aPvP1PwF3Q0x38X0G,0GX2D,0DX3D,0DX4DP}PDQ0zP_PdPbP@PEP>Q0tQ12Q0hQ0[52CR0PBPPPhP~P[PcPpQ0bQ0mQ0lP4PIQ0qQ0rPFPjQ0jPsP|PtP`MO1Q0aQ0z#7R7Q0^PvQ0IPwF3Q0zP_PdPbP@PEP>Q0tQ12P0PBPPPhP~P[PcPpQ0bQ0mQ0lP4PIQ0qQ0rPFPjQ0jPsP|P2P3MO1Q0aP7Q0^PvP1PwF3PyQ06P1Q06P1PzP{P1Q0iQ0[F4E5X0G,0GX2D,0DX3DQ0EPDQ19P_PdPbPRPXPZQ12Q13Q0[Q0_52CR7P\PxP]PLQ0>PaPqQ0mQ0lP4PIQ0qQ0rPFPjQ0jQ0kQ0NQ0QPuQ0FMO1Q0^Q19#7RcQ06PvQ0JPwF3Q19P_PdPbPRPXPZQ12Q13P7P\PxP]PLQ0>PaPqQ0mQ0lP4PIQ0qQ0rPFPjQ0jQ0kQ0NQ0QPuP3MO1Q0^PcQ06PvP1PwF3PyQ0iP1Q0iP1PzP{P1Q0hQ0_F4E5X0G,0GX2DQ0HPGQ1:P_PdPbPWPUPQQ13Q0dQ0_Q0e52CP6PVPlPmQ0?PnPeQ0lP4PIQ0qQ0rPFPjQ0jQ0kQ05Q0BQ0RQ0DQ0GMO1RjQ06Q1:#7RFQ0iPvQ0KPwF3PjQ06PFQ0iPvP1PwF3PyQ0hP1Q0hP1PzP{P1Q0[Q0eF4E5X0GQ0LQ0sQ0s+0:Q0[Q0L5FyRFQ0[Q0L'SRjQ0L#CRIQ0L?AHJRJQ0LQ0_Q0g3NRH'9R4'9Rl'9RV'9Q02Q0s'}PFPVPgPjPlPNPIP4P;PJPHP3P1CWCWCWCWCWChFOFOFOFOFOFOFOWaWoP3P1O2n2001000010121000000WFWhP3P1O2n2001000010121000000WFWpP3P1O2n2001000010121000000WFWiP3P1O2n2001000010121000000WFP\P1EpWFP3P1O2n2001000010121000000WFX0GP3P1O2n2001000010121103000WFX2DP3P1O2n2011000010121103000WFX3DP3P1O2n2011000010121103000WFX4DP3P1O2n2011000010121103000WFX5DP3P1O2n2011000010121103000WFX6DP3P1O2n2011000010121103000WFX7DP3P1O2n2011000010121103000WFX9DP3P1O2n2011000010121103000WFX:DP3P1O2n2011000010121103000WFX<DP3P1O2n2011000010121103000WFX=DP3P1O2n2011000010121103000WFX1DP3P1O2n2011000010121103000WFX?DP3P1O2n2011000010121103000WFXADP3P1O2n2011000010121103000WFXCDP3P1O2n2011000010121103000b[b[b[W[WYQ02Q0ZP]P_PdPbPkPgPiPLPmQ0E=2C`PTPMPNPOP=P:P;PaPnPoPpPqPePrPsQ0NQ0BP<P9P2P3MO1P}Q0PPtPvP1PwF3Q0=Q0@PzP{P1Q0DP`D:3H58KX0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0D[]YeJ08bcbbbdb_Q01Q02PfPmP_PdPbPkPgPiQ0?PAQ0IQ0J52CPTPMPNPOP=P:P;PePrPsQ0NQ0BQ0CP|Q0QQ0RP}P<P9P2P3MO1P`PmQ0FPvP1PwF6PyQ0GP1Q0GP1PzP{P1Q0HQ0JF4E5X0G,0GX2D,0DX3D,0DX4D,0DX5D,0DX6D,0DX7D,0DX9D,0DX:D,0DX<D,0DX=D,0DX1D,0DX?D,0DXAD,0DXCD,0DWYQ0BP_PdPbQ0CP|Q0QQ0RP}1?CN1?COPtPuQ0DQ0EP`Q0FQ0GQ0HQ0IQ0JQ0KQ0LQ0SQ0TQ0UQ0APKPfPkPgMO1PiQ0VPTPvPMPwF3407eWfWlWmWgWjW`WnWqXt5Xk5WsWrWeX8DX;DX>DX@DXyDXxDZ02DZ01DZ00DX~DX}DX|DX{DXzDXBDXDDXEDXGDXHDXIDXwDXvDXKDXMDXNDWuo"). Qed.

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
               Ft (ret_pc ra') fc None m' (seg_rom psegs)
      /\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (q + -544)
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ bytes_at psegs m' S (zb bs).
  Lemma out_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (S L : Z) (bs : list Z),
    SINK m st -> bytes_at psegs m S (zb bs) -> Forall (fun c => 0 <= c < 256)%Z bs -> L = zlength bs ->
    stk psegs m lo (q + -544) -> ssp_cells m canary -> mem_inv psegs m ->
    (0 <= S)%Z -> (S < 2^64)%Z ->
    (S + zlength bs <= lo \/ q + -544 <= S)%Z -> (S + zlength bs <= Fp \/ Fp + 232 <= S)%Z -> (S + zlength bs <= B \/ B + BS <= S)%Z ->
    (zlength bs < 2^31)%Z ->
    (S + zlength bs <= 2^47)%Z ->                                   (* [comment removed for export] *)
    implM psegs (OUT bs) st (out_postq ra' Ft fc s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S bs m)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) FPv a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x1f9e4) fc None m (seg_rom psegs)).
Proof using BS0 GLO HAP HOUT LO QHI SEP_B SEP_F TOK TQ fmt slots.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "p'0h04__x1h14__x2h27__arithh34__ffh47__sat48h57__sat49h67__sat50h77__sat51h87__sat52h97__sat53h:8__varmaph;5__with<4cstrh=5cstr0h>5cstr1h?2Hah@2HOhA4__p1hB4__p2hC4__x3hD4__x4hE2a3hF2a4hG2a5hH2a6hI2a7hJ3ms'hK2t0hL2t1hM2t2hN2t3hO2t4hP2t5hQ2t6hR1zhS1LhT1PhU2SBhV4__x5hW1ahX2a0hY2a1hZ2a2h[2m'h\2s'h]2D1h^2D2h_2D3h`2Eqha2Eshb2Fthc1Hhd2HShe3HS0hf3HS1hg2LBhh2MIhi3RNGhj1Shk3S47hl3SRChm3SSPhn2STho2bshp1chq2fchr1mhs1nht3ra'hu2s0hv2s1hw3s10hx3s11hy2s2hz2s3h{2s4h|2s5h}2s6h~2s7i002s8i012s9i022sti033st'i041up%0p%1p&0p;1p;2p;3p;Bp;Op;7p;5p;6p;4p;Lp;Ep;:p;8p,2StR0p4p300g05NJR1p4p710p8g007ej19Tg008Jj1^Tg008hj1nTg00U>j1GTg004?k20MTg00>Ak10ETg007Ej1yTg00:1j1HTg013Gj1STg00C3j25Tg00COj2:Tg00k0j3aTg00;Lj3@Tg01ACk10KTg00dZj28Tg05OLj2RTg01e2j2oTg05PKlBflEwTg009Kj21Tg058GlOBTg00Iej1}Tg0599k105Tg05:2j7DTg05HMk501Tg00:lj2\Tg00N^j1ETg04GIk10NTg002Tj6kTg00PBj1bTg01mBj2sTg01mjj3rTg00Qcj1jTg00RBj2`Tg00STj2iTg00Emk100Tg00T@j3OTg00FMj2_Tg01Bkk10LTg00Fkk10JTg00GIk10ITg00H4j2YTg01eoj3|Tg01Clj3qTg00HWj2zTg00JGk20CTg00@Gj2pTg00Jik20BTg00KUk30ATg00L4k40@Tg00A_j22Tg01?fj2VTg027Qj2xTg026gj2=TP1k70=Tg05QTlL[lOlTg00QIj2]Tg05@4j1vTg03JKk20<Tg04bfj3uTg04cZj3tTg0158j20Tg05RVm:0;Tg0030k60:Tg00cek409Tg00B;k208Tg05Dak407Tg044]k20>Tg04ZQk70?Tg00Rkk306Tg00T`k40DTg00I:j4{Tg00WXj7~Tg01CIk304Tg00X`k70FTg00YDk803Tg00X<k60GTg00Uck70HTg03S8k402Tf0R1#9#9p=3g00j;R2f2R3f1R4P1H09p=Ig00[2R5/21p=6g00;fR60081p=4%G1#9p=QP2P3P4P1H07p=F20>21p=Tf3R7/231241']p=?%91#Gp=C%91#Sp=Jf4R8/87/231241']p=A%G1#Gp=;1834/21p=<P8P2g00[oR9P7P3P4P1K0?p=K1\61p=cB06641p=PP6P3P4P1H0Dp=Z1z61p=NP6P4g00_jP1C{p=hP4g00[PR:P9P9g00\OR;P1g00\oS00F~p=gP3P:P9P9P;P6P4g00`QP1C{Q00F~p=7B04641p=MP3P:P9P9P;P4P1K0Fp=XP7P:P9P9P;P3P4P1L03p=>1\61#E,14p=L1241,]3p=UP4P:P9P9P;P1J0Gp=mP3P:P9P9P;P4P1K0Hp=dP6P6P4P1H02p=e1:41,:3p=Wg00<DR:#9R<#9S01#9S02#3R=#9R>#^R?#nR@%G<RA#^00M@%^=#nQ02#^#nR=$0E\@S03%y6p,4SINKRBP8P7O2f5RC%H47I7%61%3>S04#S,51':Xp6S05=a63%479@68P6%48f9RDp,2loREp,1qS06Q02#Q#3#3$0KRF'8RG3Ff:RHp,6canaryRI'Rf;S07#T%6HQ07%S<RJ%S>R>'oRK'5f<S08%4H'8RLPEPGQ08C?f=S09Q07#4'8RMp,2FpRN%G:S0:#GRO#C#3#JS0;,8NRPQ09C?f>RQQ08#4RRp,1BRSp,2BSRT,8SRUPQDAQ09#4RV%;O#SRO,oJRW'5f@RX%4QS0<%GA#;RY#SRZ,oJR[3<P0p,3OUTS0=f?R\O1fBR]f^R^fER_fDS0>fZR`fYRafSRbfRRcfQRdfPRefORffNRgfMRhfLRifKRjfJRkfARlP\fCRmMBfP^11?GRnp,2gpRop,2tpRpf]Rqf\Rrf[RsP`Pa11?l11?H11?NRtfXRufWRvfVRwfURxfTRyPbPcPdPePfPgPhPiPjPkfIRzfHR{fGR|fFR}MOBP_%G:#;#;#3#;#;#3#Q#J,1?S0?Q0>%}@S0@Pm&052S0AFDDK[[[[[[[[[[XS6f8S0B?FEG1RDI%TH%6D15HKQ07%4DPEPGQ07DAPLPNPPQ08C?PMPSPUQ09C?15RWA<\V[P2P]PX%HQRVQ08I01%6X1\=V#E=<XK':g00<iRV%H\,\=%6]%E1=<]K':XsVP1%c\RV&0N\Ek%6l%EV=<lK':p,3fmt#cRV#bS0C%EV#6S0Dp,5slots,\@RV#bS0E%EV#6S0F%c]RV#b%EV#61sJZS0G155JRV%6Z155[[[S0H%6JR=g01WWRRArJZ4UW?S0I%6[\R^?=S0J1sJ>S0K%6>155K[\VS0LArJ>4VRX?=S0M%6K\R^?=S0N1sJOS0O%6O155W[\VS0PArJO4VRX?=S0Q%6W\R^?=S0Rg00_>R=g00b3RR#jRO#jS0S,`6S0T1`6OS0U1`6RS0V'P'Pg00bRS0W'i&00=S0X3O%y=S0Y1_63&0L6S0Z7Z4S0[&0J6S0\&0I6RR1Y6:RO%NJRJ%^Y5|6S0]'h,gRS0^%}9RYPR%9:#;#3#Q#3#3#3#3#3#JS0_#N1Y6<R<57RS0`PYPR%9A#3#Q#3#3#JS0a#NS0b9q6O97R<PY1z65RA%NFS0c,MOS0d57RQ0dA|6J?RJ'h,gR5XRC>C>C>20CR;S0eP1P3g00^^R;g00a8RV'p20B13=@;VdB0A654H0@S0fb3b:b;X06X16151[S0gQ0_/23Q0a,V3,27187FR5#6155K':[[[^06^16P1PEQ06p,3QHIS0hp,3GLOS0ip,2LOS0jO5b2b4b5b6b7b8b9b>b=b<,xG1=?nR5=@6GQ0CQ0DQ0EQ0F%cmRV#b%EVRV#6Q0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0XQ0Y1_64S0kQ0\PR1hOJ,gRRJPYPRA7RAORAPYAXRAJC>C>Q0eQ0fb3b:b;X06151K%64%63153K':[[^06P1PhP]PmO3b2b4b5b6b7b8b9b>b=b<,xm11?m,=?=@6mp,4HOUTP0PNPSPTPBp,5TOPOKS0lQ0=K0=P1fbS0mPnPoPpfaS0nf`S0of_RKP^Pq11?_11?VPtPrPsP`PaPuPvPwPxPyPbPcPdPePfPgPhPiPjPkPzP{P|P}PmPEPIOVPBP|P}O211?},=?Q0>#H5I{Q05=a6_%4}S0p/5W1L?|%4|S0q,1?5@@A@@ttS0rAFhE5g05SPS0s,V5,2Eg05TS/2ES0t155[Q0lP5O11RcI%Tb12PES0u?U5N12UES0v?U5S11?y,=?RV%4cPEP5PVDA11?x,=?S0w%4b'8S0xPNPPQ0wC?11?w,=?S0y%4yS0z'8S0{PSPUQ0yC?11?v,=?S0|%4xS0}'8S0~/2[P0Q0=PwO1PaP0PNPSPTPBfuS10PnPoPpfqS11fpS12fjRVfiRAfhRJfgR;ffR>feRZfdRMfcRLQ0mQ0nPrPs11?uR~,=?S13PwPEPIP`ML[Q10PnPoPpftS14fsS15frS16Q11Q12P~1L?wPtfoS17fnS18fmS19flS1:fkR~PVPAPJP;P>PZPMPLQ0mQ0nQ0oPKP^PqMOBPrQ0?PsQ0@P`Q0AFDDK[[[[[[[[[[[[[[[[[[[P6P5PBPzP{O2S1;11?{S1<,=?%H}S1=5IkQ05=a6|S1>%4{S1?/5WS1@1L?z%4zS1A,1?5@@S1BQ0rf6S1C9FfEf7S1DQ0s'V,2EQ0t15D[Q0lPHO11RyIS1E%TxS1FQ0uQ09;UNQ0v?UQSQ0{PEP\Q0yC?Q0~PNPPQ0|C?Q13%4wS1G'8S1HPSPUQ13C?11?aS13,=?S1I%4vS1J;<[P0Q0=PuO1S1KPsP0PNPSPTPBfwS1LPnPoPpQ15Q16Q1:P~PVPAPJP;P>PZPMPLP^Pq11?`S1M,=?PuPEPIPrML[Q1LPnPoPpfvS1NQ10Q14Q15Q16Q1M1L?uPtQ11Q12Q17Q18Q19Q1:P~PVPAPJP;P>PZPMPLQ0mQ0nQ0oPKMOBP^Q0?PqQ0@PrQ0AFDS1MDK[[[[[[[[[[[[[[[[[[[XR6P1PGP7EkPBP{P|O211?|,=?S1O%H_5IzQ05=a6}Q0q/5W%c{S0q#ES1P,1?Q1?,1?5@@Q0rAFgEGQ0s,VG,2ES0sQ0t15G[S1?Q0lPGO1S0l1RbI%TyQ0u?UGNS0uQ0v?UGSS0vQ0xPEPGQ0wC?Q0{PNPPQ0yC?Q0~PSPUQ0|C?Q1H/2[P0Q0=PvO1P`P0PNPSPTPBQ1NPnPoPpQ16Q11P~PVPAPJP;P>PZPMPLQ0mPqPrQ1IPvPEPIPsML[Q1NPnPoPpQ10Q14Q15Q16Q11Q131L?vPtQ12Q17Q18Q19Q1:P~PVPAPJP;P>PZPMPLQ0mQ0nQ0oPKP^MOBPqQ0?PrQ0@PsQ0AFDDK[[[[[[[[[[[[[[[[[[[P6Q1OPBPkPzO2%H|9Ij4Q05=a6{Q1A/5W1L?k%4k,1?5@@Q0rAFeEGQ0sQ0tQ1?Q0l1RxI%TwQ0uQ0vP\Q0}PEPGP\DAPXQ1GPNPPPXDAPlQ1JPSPUPlDA%4u=<][P0Q0=PaO1PrP0PNPSPTPBfxRWPnPoPpQ14Q15Q19Q1:P~PVPAPJP;P>PZPMPKP^PmPaPEPIPqML[PWPnPoPpQ1LQ1NQ10Q14Q1511?s1L?aPtQ16Q11Q12Q17Q18Q19Q1:P~PVPAPJP;P>PZPMPLQ0mQ0nQ0oMOBPKQ0?P^Q0@PqQ0AFDDK[[[[[[[[[[[[[[[[[[[XR6P1P|P7EkQ1;Q1=9Ik{Q1>Q1@Q1BQ0rAFfEGQ0sQ0tQ1?Q0lQ1EQ1FQ0uQ0vPwQ0zPEPGPwDAPvQ0}PNPPPvDAPuQ1GPSPUPuDAQ1J=<a[P0Q1KPsP0PNPSPTPBQ1LPnPoPpQ15Q16Q1:P~PVPAPJP;P>PZPMPLP^PqP`PuPEPIPrML[Q1MDK[[[[[[[[[[[[[[[[[[[P0P2P9Q0=P}O1PzP0PNPSPTPBPZPnPoPpQ0nQ0oP`PaPuPvPwPxPyPbPcPdPiPjP{P}PEPIPkML[PZPiPjQ0nQ0oP`PaPuPvPwPxPyPbPcPdP{P}PkMBfPZPnPoPpPMPLQ0mQ0nQ0oQ1<1L?}PtPKP^PqPrPsP`PaPuPvPwPxPyPbPcPdPePfPgPhMOBPiQ0?PjQ0@PkQ0AFDP1P_Q0>PmPDQ0p,1?,p@1p@tPlQ0CQ0DQ0EQ0FQ0q#bS0qQ1P#6S1PQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0XQ0YQ0[Q0\PRQ0b9q6<97ROPYQ0c,M<Q04#9#JRW#N5q697ROC>Q0eQ0fb3b:b;X06X16Q0a,V4,21183F/VW,24[^06^16P1Q06PEQ0jO3b2b4b5b6b7b8b9b>b=b<Q0seQ0iQ0CQ0DQ0EQ0FQ0qQ1PQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0XQ0YQ0kQ0\PRQ0^PYQ0dQ0]'h,gRC>Q0eQ0fb3b:b;X06Q0g184F/5[[^06P1Q06Q0hO2b2b4b5b6b7b8b9b>b=b<Q1?ep,3TOKPGQ06Q0CQ0DQ0EQ0FQ0qQ1PQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0XQ0YQ0kQ0\Q0d=7ROQ0eQ0fb3b:b;X06A<1F1^06P1Q06O1b2b4b5b6b7b8b9b>b=b<p,2TQO4Q0lePXP\Q0CQ0DQ0EQ0FQ0qQ1PQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0Rp-0R[Q0S#jRW,`6S0SQ0TQ0U'P'PQ0W'i%jW,`6Q0SQ0V'P'PQ0W'iQ0X5O=5O=Q0YQ0Z1_687Z31_67S0U7Z4Q0\PRQ0:,Y6RWQ0:#9,Y6S0:57RPYPRQ1C,mRQ0;#N,MOS0l%9:#Q#;#;#C#C#C#3#3#JS0d#N57R5XRQ0:Q02#SS0k#NS1?'M=7ROQ1D,mRS0:5XR5dRPYPRQ0`PYQ0l=7R<Q0c,MW=7RO5dRC>C>C>Q0eQ0fb3b:b;X06X16XC6XD6XA[WB1237Q0;Q0d5<4,:CQ0k=<84Q1C':']Q0_/27P7Q0;P818CFS0;P7DA[[[^06^16^C6^D6^A[^B[P1p,2VAS0_,2P%3:#;#3#Q#C#C#;#3#J/2Np,2APS0dQ06PEPNp,3HAPS0lp,5SEP_FQ0iO9b2b4b5b6b7b8b9b>b=b<Q0ueQ0CQ0DQ0EQ0FQ0qQ1PQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0V'P'PQ0W'iQ0X5O=Q0Y1_6CQ0Z7Z8Q0Z7Z3Q0U7Z4Q0\PRQ01,Y6R=Q02,Y6RF57RPYPRQ0:1MO<=7RWRW5XRQ1?,MF=7ROQ0B,mR5XR5dRPYQ0c,M==7RO9dRWC>C>Q0eQ0fb3b:b;X06X16XC6XD6XV6XA[XB[1278Q1CA<437':Q0k=<C4Q1D':']P3P7P8Q0;P3DA[[^06^16^C6^D6^V6^A[^B[P1Q0_,2U%9:#Q#;#;#C#C#C#C#3#J/2SQ0dQ06PEPTPSQ0lp,5SEP_BO9b2b4b5b6b7b8b9b>b=b<Q0veQ08Q07PHQ0BOCP9g04[FR:P0PNPSPTPBPAPnPoPpPZPMP^PqPrPsP`PaPuPvPwPxPePfPiPkPEPIPgP3P4P1MOlPVPdPeP>PZPKP^PqPrPsP`PaPuPvPwPhPjPfP7P3P4MEw[]J^\0P1P0PNPSPTPBPJPnPoPpPMPLPqPrPsP`PaPuPvPwPxPyPfPgPjPzPEPIPhQ00P4P1MOlP6P5Q03Q03fzR5PnPoPpP\PQQ09Q1NQ10Q08Q07PHPDQ0BQ1DQ1CPCQ17Q18Q19Q1:P~PVPAPJP;P>P8P7P3P4MOBQ0n%v5Q0oQ0@P1Q0AFD9@:]20<66R51eEX1eNP1eSU&0055O55O5RU3O?uK1At2K1%T1RPAF1EXPBP1PmO21R1IR[%Hs9I1q':3W3W3WW['0XQ@,0@XP@,0@XO@,0@XN@,0@XI@,0@XH@,0@XG@,0@XF@,0@XE@,0@XZ@,0@XY@,0@XX@,0@XM@,0@XL@,0@XK@,0@XR6P1PGPDEkQ03Q03fyRWPnPoPpP\PQQ09Q10Q14Q08Q07PHPDQ0BQ1DQ1CPCQ18Q19Q1:P~PVPAPJP;P>PZP8P7P3P4MOBQ0o%vWPKQ0@P1Q0AFD9@:l1eEG=O5U?u^1At2^1AF1EGPBP1P]O2%H`9I1r,:[3W7WP3WW['0XQ@,0@XP@,0@XO@,0@XN@,0@XI@,0@XH@,0@XG@,0@XF@,0@XE@,0@XZ@,0@XY@,0@XX@,0@XM@,0@XL@,0@XK@,0@P1bTWTXJ:Z030n01104000101XW9P0PNPSPTPBPJPnPoPpPMPLPqPrPsP`PaPuPvPwPxPyPfPgPjPzPEPIPhP3P4P1MOlPAPePfPZPMP^PqPrPsP`PaPuPvPwPxPiPkPgP7P3P4MEw[^J:^\0^W9eN:0;b@b@b@b@bab`P0Q0=PXO1PmPKP}P_PsP`PyPbPcPdPePfPgPhPiPjP]PXQ0>MBfPKPnPoPpP^PqPrPsP`11?]%4X,1?PtPaPuPvPwPxPyPbPcPdPePfPgPhPiPjPkPzP{P|MOBP}Q0?P_Q0@Q0>Q0AFDDKebUbUP0Q0=PQO1PlPqQ0>PmPaPuPcPdPePfPgPhPiPjPkPzPXPQP]MBfPqPnPoPpPrPsP`PaPu11?XQ0<,1?PtPvPwPxPyPbPcPdPePfPgPhPiPjPkPzP{P|P}P_MOBQ0>Q0?PmQ0@P]Q0AFDDKeWkWgW_W^W]WfWeWhWmWnPCP1J0:WcWiWlWdWoXS6Xj6Z020WrWqWbXQ@XP@XO@XN@Xx@Xw@Z01@Z00@X~@X}@X|@X{@Xz@Xy@XI@XH@XG@XF@XE@Xv@Xu@XM@XL@XK@Wto"). Qed.

  (* [comment removed for export] *)
  Definition fp_postq (ra' : word) (Ft : bvmap 5 word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (m : word -> option byte) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
      ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft' (ret_pc ra') fc' None m' (seg_rom psegs)
      /\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ frm0 fc' /\ Fokd Ft Ft'
      /\ stk psegs m' lo (q + -544)
      /\ SINK m' st'
      /\ ssp_cells m' canary.
  Lemma fp_callq : forall ra' t0 t1 t2 s0 s1 (a1 a2 a7 : word) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (y w p fl t : Z),
    fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
    SINK m st -> y = (bv_unsigned a1 + 2^64 * bv_unsigned a2)%Z -> bv_unsigned a7 <> 5%Z ->
    (-2^31 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
    stk psegs m lo (q + -544) -> ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
    implM psegs (OUTFP y w p fl t) st (fp_postq ra' Ft s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 FPv a1 a2 (Z_to_bv 64 w) (Z_to_bv 64 p) (Z_to_bv 64 fl) (Z_to_bv 64 t) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x21258) fc None m (seg_rom psegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_common ()) ["PrintfCore"] "p'0h04__x1h12Hah24__x2h37__arithh44__ffh57__sat12h67__sat13h77__sat14h87__sat15h97__sat16h:7__sat17h;7__sat18h<7__sat19h=7__sat20h>7__sat21h?8__varmaph@5__withA4__p1hB4__p2hC4__x3hD4__x4hE3FPChF2FthG2a1hH2a2hI2a7hJ2t0hK2t1hL2t2hM2t3hN2t4hO2t5hP2t6hQ1PhR4__x5hS2a3hT2a4hU2a5hV2a6hW3fc'hX1khY2m'hZ3ms'h[1zh\2Eqh]3FRMh^2H7h_2HSh`3Hflha2Hphb2Hthc3Htahd2Hwhe2Hyhf2MIhg3SSPhh2SThi1ahj2fchk2flhl1mhm1phn1rho3ra'hp2s'hq2s0hr2s1hs3s10ht3s11hu2s2hv2s3hw2s4hx2s5hy2s6hz2s7h{2s8h|2s9h}2sth~3st'i001ti011wi021yp%0p%1p&0p;1p;2p;4p;8p;3p;Ip;Op;7p;6p;?p;Lp;Bp;:g007ej12Tg008Jj1WTg008hj1eTg00U>j1ATg004?k20BTg00>Ak10@Tg03JKj2lTg03S8j4gTg05UTk801Tg026gj2<Tg013Gj17Tg01e2j2]Tg01ijj2fTg00dZj24Tg01h6k10?Tg00A_j20Tg00COj2:Tg025Mj2aTg01ACk104Tg05OLj2XTg044]j2ZTg05VYj1^Tg01mBj2UTg01mjj3TTg00Qcj1_Tg00RBj2STg00STj2hTg00Emj1zTg00T@j3ITg007Ek10HTg00FMj2\Tg01Bkk10GTg00Fkk10FTg00GIk10ETg00H4j2PTg01eoj3yTg00Iej1xTg01Clj3mTg00HWj2wTg00JGk20>Tg00@Gj2QTg00Jik20=Tg00;Lj3;Tg00KUk30<Tg00L4k409Tg00C3j2KTg01?fj2OTg027Qk208Tg009Kj23Tg05WIlIdmL05Tg058GlOLTg0599k106Tg05:2j7JTg002Tj6tTg05XNl?rmB03Tg00QIj2jTg05@4j1qTg04bfj3pTg04cZj3sTg03n1j2kTg0158j21Tg05RVm:02Tg00Lfk10:Tg05Dak40;Tg00Rkk300Tg00T`j4~Tg00I:j4uTg00WXj7vTg01CIj3}Tg00X`k70ATg00YDj8|Tg04ZQk70CTg00X<k60DTg00Ucj7{Tf0R0#2#2p==g00;fR1P1f1R2P0Cgp=VA;120p=[A;120$0:p=@%A0#Ap=?f2R31K20':p=9g00[2R4/00p=5%20#7p>07%20#Ap=8%A0#2p=C%20#2#2#2p=cg00j;R5P3P2P0H0;p=N1K40p=MB00120p=BP1P3P2P0C~p=R1w10p=FP1P2g00_jP0Cup=oP2g00[PR6g00[oR7P7g00\OR8P0g00\oR9Fvp=n%20#2#2#7p=HP3P6P7P7P8P1P2g00`QP0CuP9Fvp=6A}120p=EP3P6P7P7P8P2P0K0Ap=Yf3R9P6P7P7P8P3P2P0G|p=>1020,j3p=Gf4R:P5P1P9P3P2P0K0Cp=`P2P6P7P7P8P0J0Dp=iP3P6P7P7P8P2P0F{p=b1:20,:3p=Dg00<DR6#2R;#2S00#2R<#=R=#2R>#WR?#eR@%A;RA#WS0100B@RB%W=#eRC%W<#e$0@\@RDp,2StREPEp,2FpRFp,1BRGp,2BSRHp,4SINKRIp,5TOPOKS02p,5OUTFPS031l11RJ/l1RK/l1P1PKP1PJP11V:9P3CgP2CgP0CgL01PIf7RKf6RLO2fKRM,<?%7;RN%7>RO']RPfJRQ,<?RR'f'4,[L%7AS04,@R%A6S05#ARR#?#7RS,]NRT$0?S06/0KRU%76S07,0K':%2AS08#2RV#7RW,]NRX99UK%5KRU%7=R=,]NRY79K%2>$07R>99UKf8S09/a=Q05#2S0:#=#8#7RU'@f?S0;p,2loRZp,1qR[%C<#c$04R\'4R]3Nf@R^p,6canaryR_'XfAR`,Z5fCRa#^1UN=S0<%MNRb%5=%MY[[S0=%5NRcg01WWRdATN=2UW1S0>%5Y\d^1cS0?%AA#?RA#7Re,UNS0@%5e1]NeRf#M[\bS0AATNe2VdX1cS0B%5f\d^1cS0C1UNWS0D%5W%MX[\bS0EATNW2VdX1cS0F%5X\d^1cS0G1UNOS0H%5O%MP[\bS0IATNO2VdX1cS0J%5P\d^1cS0K1UNSS0L%5S%MT[\bS0MATNS2VdX1cS0N%5T\d^1cS0Og00_>Rcg00b3Rd#_RT#_S0P,S1S0Q1S1TS0R1S1dS0S'B'Bg00bRS0T'h%zcRd3I&0HcS0U1\13&0G1S0V7R2S0W&0F1S0X&0E1RT1P16RS%FNRN%WA5y1S0Y'o,nTS0Z%x7R7PT%26#?#=#C#c#c#HS0[#F1P1;R;56TS0\P7PT%2V#C#=#HS0]#FS0^9m1S96T;P71w14%F\S0_,ESS0`56TQ0`Ay1N?'o,nT5YTC>C>C>20>T8S0aP0P3g00^^R8g00a8RN'Q20=03=;8NdB0<142H09S0bb4b?b@X01X211K0fS0cQ0[/03Q0],O3,09149\R4#5?94P[[[^01^21P0PZP[p,3QHIS0dp,3GLOS0ep,2LOS0fO5b3b5b6b7b8b9b:b;b<b=b>-08]13?]R4,<?RN/[]f=R8f]RVP4p,2gpRAp,2tpRbf\ROf[RWfZRefYRgfXRh13?FRifWRjfVRk13?`S0g13?^S0hQ0;,3?S0if>S0j,3?S0kfURlfTS0lfSRmfRRnfQRofPS0mfOS0nfNS0ofMS0pfLS0qPMPQfIRpfHS0rfGS0sfFRqfERrfDRsPaPZP_OUPIPsPaO21<?hS0t1<?j,fP'4,[aA;@iiS0u13?sS0vQ0v5;@Rt1<?OQ04'@Q06/0pRuQ07,0p':A9upX%5pRu?9pYA9up>1aQ=/@UANoZNg05YVS0w,ON,0Zg05TS/0ZS0x1KNfQ02PNO11Xk_1Z5j%^g%8R#HS0y,4FS0z/0ZS0{?GNF14GHS0|/0ZS0}?GNGPEQ03PgPhPjPkPlO5PePEPFPGPHPIftS0~P4PAPbfpS10foS11fkRRfjRufiRvfhRwfgRxffRyfeRzfdR{fcR|fbS12PVPZP_PWMIdQ0~P4PAPbfsS13frS14fqS15Q10Q11PifnS16fmS1713?hS1813?jS1913?kS1:13?lflS1;PRPuPvPwPxPyPzP{P|Q12faS1<f`S1=f_R}f^R~MOLPV%c6#C#8#=#C#?#H,3?S1>PO%x@S1?PW&065S1@FJD`[[[[[[[[[[[[[[[[\t\t\t[[[[P1PNPIPqPrO21<?e1<?gS1A,fP'4,[rQ0u13?qRt=;@tRt1<?~Q04'@Q06/0MS1BQ07,0M':Q1B?9MX%5MS1B?9MYQ1B?9M>Q0q/a=/@UANmZ8Q0jQ0w'O,0ZQ0x1K^fQ02P`O11Xh_1Z5g%^WQ0{?GrFQ0}?GqGPEQ03PWPePgPhPjO5POPEPFPGPHPIfvS1BP4PAPbQ14Q15Q17Q1;PRPuPvPwPxPyPzP{P}PZP_PVMIdQ1BP4PAPbfuS1BQ0~Q13Q14Q15PiQ10Q1113?e13?gS1CQ18Q19Q16Q17Q1;PRPuPvPwPxPyPzP{P|Q12Q1<Q1=MOLP}Q1>P~Q1?PVQ1@FJD`[[[[[[[[[[[[[[[[\t\t\t[[[[X[1P0P]P2EtPIPrPsO2Q1AQ0t,fP'4,[sQ0u13?rRP=;@PRt1<?VQ04'@Q06/0QS06Q07,0Q':Q06?9QX%5QRX?9QYA9XQ>1aM=/@UANnZ]Q0w,O],0ZRUQ0x1K]fR=Q02P]O1RX1Xj_1Z5h%^eQ0{?G]FS0{Q0}?G]GS0}PEQ03PePgPhPjPkO5PWPEPFPGPHPIQ1BP4PAPbQ15Q10Q1;PRPuPvPwPxPyPzP{P|P~PZP_POMIdQ1BP4PAPbQ0~Q13Q14Q15Q10PiQ11Q16Q1CQ18Q19Q1:Q17Q1;PRPuPvPwPxPyPzP{P|Q12Q1<Q1=P}MOLP~Q1>PVQ1?POQ1@FJD`[[[[[[[[[[[[[[[[\t\t\t[[[[PEP5P1Q03PsPafBRtP`P^O5PrPEPFPGPHPIP}P4PAPbPWPePkPlQ0lPmPnPoQ0mQ0nQ0oQ0pQ0rPZP_PqMIdP}Q0rPWPePkPlQ0lPmPnPoQ0mQ0nQ0oQ0pPqM?rP}P4PAPbP~PVPOPWPePiPgPh13?aR>13?tRYQ0gQ0hPjPkPlQ0lPmPnPoQ0mQ0nQ0oQ0pQ0qPMPQPpMOLQ0rQ1>Q0sQ1?PqQ1@FJP0Q0jP81Q@i1Q@>1Q@YQ0g,Q@Q0h,Q@f<S0gf;S0uf:S0xf9S1<Q09PKPLQ0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0LQ0MQ0NQ0OQ0HQ0IQ0JQ0KPdQ0UQ0WQ0XPTQ0^9m1;96TSP7Q0_,E;Q00#A#=#8#=#HRY#F5m196TSC>Q0aQ0bb4b?b@X01X21Q0],O2,00143\/OY,02[^01^21P0P[PZQ0fO3b3b5b6b7b8b9b:b;b<b=b>PUeQ0eQ0@Q0AQ0BQ0CQ0<Q0=Q0>Q0?Q0DQ0EQ0FQ0GQ0LQ0MQ0NQ0OQ0HQ0IQ0JQ0KPdQ0U1\12RUQ0XPTQ0ZP7Q0`Q0Y'o,nTC>Q0aQ0bb4b?b@X01Q0c142\/Kf[^01P0P[Q0dO2b3b5b6b7b8b9b:b;b<b=b>P=ep,3TOKP]P[Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0LQ0MQ0NQ0OQ0HQ0IQ0JQ0KPdQ0UPUQ0XQ0`=6TSQ0aQ0bb4b?b@X01140\/00^01P0P[O1b3b5b6b7b8b9b:b;b<b=b>p,2TQO4PXef5RXP:P9Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0LQ0MQ0NQ0OQ0HQ0IQ0JQ0Kp-0RUQ0P#_R=,S1RfQ0QQ0R'B'BQ0T'h%_=,S1Q0S,Bf'BQ0T'h=Icd5IcQ0UQ0V1\1:7R31\19S0R7R2Q0XPTQ05,P1R=Q0:,P1RY56TP7PT1iTLQ0y#F,ESS0:%26#C#?#?#8#8#8#=#HS05#F56T5YT%7<R>#FS0P,EY=6TS1iTKRY5YT5bTP7PTQ0\P7Q0:=6T;Q0_,E==6TS5bTC>C>C>Q0aQ0bb4b?b@X01X21XC1XD1XAUWB1039Q0y,42Q05'0,:X14:>/02/:L'jQ0[/09Q0y,49/0:14X\S0y;G9[[[^01^21^C1^D1^AU^BUP0Q0zp,2VAR\'0%=6#?#=#C#8#8#?#H/0Fp,2APS0[P[PZPFp,3HAPS05p,5SEP_FQ0eO9b3b5b6b7b8b9b:b;b<b=b>Q0{eQ0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0LQ0MQ0NQ0OQ0HQ0IQ0JQ0KQ0QQ0S'B,BfQ0T'h=IcdQ0U1\1XQ0V7R:Q0V7R3Q0R7R2Q0XPTQ00,P1Rd1P1<R<56TP7PT1ES;=6T=R=9YTYQ0P,E<=6TSQ09,iT5YT5bTP7Q0_,Ed=6TS9bT=C>C>Q0aQ0bb4b?b@X01X21XC1XD1XR1XAUXBU109:1423/09,:L14X>/02/:K'j1439/0:Q0y;G3[[^01^21^C1^D1^R1^AU^BUP0Q0|/0\%26#C#?#?#8#8#8#8#H/0GQ0[P[PZPHPGQ05p,5SEP_BO9b3b5b6b7b8b9b:b;b<b=b>Q0}eOGg04[FR[PEPFPGPHPIQ12P4PAPbP~PVPgPhPjPkPlQ0lPmPnPoQ0mPMPZP_PpP3P2P0NL05RVP1PNQ1BP4PAPbP^Q0;Q0jQ15Q10PPP8Q0gQ0uQ0xQ1<Q09PKQ1;PRPuPvPwPxPyPzP{P|PLPXP:P9MOLP3Q1B#qP2Q1?P0Q1@FJ9;[a1VZ`Q0z,VFQ0|,VG%zJ5IJ5IJRG5IJ?pO0As5O01Z50RF%^2RPQ01#eRNQ01/<0Q08#7'@RH1k:2R6Q1=/k25;@[]XAN0Z`PIP0PsO21X0_R_3D3D3D3DXYD,1DXWC,1CXFB,1BXP@,1@XO@,1@XN@,1@XM@,1@XI@,1@XV@,1@XU@,1@XT@,1@XS@,1@XH@,1@XG@,1@XL@,1@XK@,1@XJ@,1@X[1P0P]PLEtQ0~P4PAPbP^Q0;Q0jQ10Q11Q0vP8Q0gQ0uQ0xQ1<Q09PKPRPuPvPwPxPyPzP{P|Q12PLPXP:P9MOLP3Q0~#qP2Q1?P0Q1@FJ9;[t1VZ]=IJG?pW0As5W01k}29;@6\H^XNAN0Z]PIP0PaO2;D_5DP7DF3DXYD,1DXWC,1CXFB,1BXP@,1@XO@,1@XN@,1@XM@,1@XI@,1@XV@,1@XU@,1@XT@,1@XS@,1@XH@,1@XG@,1@XL@,1@XK@,1@XJ@,1@P0bQWQWZX~EXn1P|Q0qP}P~PePgPhPjPkPlQ0lPmPnPoPQP9P3P2NB03\V^Z[^pE^i1eN:02bEbEb\PEQ03P`P^Q0;Q0jP8O5PtPOPrPhPjPmPnPoQ0mQ0nQ0oQ0pQ0qPMPQPaM?rPOP4PAPbPWPePgPhPjPiPkPlQ0hQ0iQ0k13?8Q0lPmPnPoQ0mQ0nQ0oQ0pQ0qPMPQPpQ0rQ0sPqMOLPrQ1>PsQ1?PaQ1@FJD`eW]WfWgWhWcWbW`WaWdW^WeW_WEZ001Xk1Xm1Z011Z021W}WlWjWFXP@XO@XN@XM@Xt@Xs@X|@X{@Xz@Xy@Xx@Xw@Xv@Xu@XI@XH@XG@Xr@Xq@XL@XK@XJ@Woo"). Qed.

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
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [psegs psegs] in *; fold psegs in *.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition S_EXIT : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 apv] ->
      frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
      evt psegs (POST r st)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20ffc) fc None m (seg_rom psegs)).

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
         evt psegs Q
           (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (2147483647 - cnt')) (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) (Z_to_bv 64 n) (Z_to_bv 64 (A + i)) x24 x25 (Z_to_bv 64 n) x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x20348) fc None m (seg_rom psegs))) ->
      evt psegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt i)) x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 cnt') x20 x21 x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x202ec) fc None m (seg_rom psegs)).

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
         evt psegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 c') (Z_to_bv 64 (A + k')) a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 32)
                    x18 x19 x20 x21 x22 x23 (Z_to_bv 64 FL) x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x20400) fc None m (seg_rom psegs))) ->
      evt psegs Q
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 w3 (Z_to_bv 64 (A + p + k)) x15 (Z_to_bv 64 1) (Z_to_bv 64 32)
                 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x203dc) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_WLOOP : Prop :=
    forall (x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (pos acc w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
      is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (w, s2) -> s2 <> [] ->
      (forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
         (pos < k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
         evt psegs Q
           (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
                    x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x20530) fc None m (seg_rom psegs))) ->
      evt psegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) x12 (Z_to_bv 64 (A + pos)) x14 x15 x16 x17
                 x18 x19 x20 x21 (Z_to_bv 64 acc) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20494) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_WIDTH : Prop :=
    forall (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k1 w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= k1 < zlength fmt)%Z ->
      getint (sfx k1) 0 = Some (w, s2) -> s2 <> [] ->
      (forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
         (k1 <= k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
         evt psegs Q
           (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
                    x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x20530) fc None m (seg_rom psegs))) ->
      evt psegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20448) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_PLOOP : Prop :=
    forall (x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (pos acc p : Z) (s3 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
      is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (p, s3) -> s3 <> [] ->
      (forall (k3 : Z) (a1 a3 a4 : word),
         (pos < k3 < zlength fmt)%Z -> s3 = sfx k3 -> is_digit (znth fmt k3) = false -> (0 <= p <= INT_MAX)%Z ->
         evt psegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x20668) fc None m (seg_rom psegs))) ->
      evt psegs Q
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) (Z_to_bv 64 (A + pos)) x13 x14 x15 (Z_to_bv 64 10) (Z_to_bv 64 8)
                 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 acc) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x205f4) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_PREC : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k2 k3 p : Z) (xp : bool) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= k2 < zlength fmt)%Z ->
      ( (znth fmt k2 <> 46 /\ p = -1 /\ xp = false /\ k3 = k2)
        \/ (znth fmt k2 = 46 /\ xp = true /\ k2 + 1 < zlength fmt /\ znth fmt (k2 + 1) <> 42
            /\ getint (sfx (k2 + 1)) 0 = Some (p, sfx k3) /\ k2 + 1 <= k3 < zlength fmt) )%Z ->
      (forall (a1 a3 a4 : word),
         (-1 <= p <= INT_MAX)%Z ->
         evt psegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x20668) fc None m (seg_rom psegs))) ->
      evt psegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 (Z_to_bv 64 (A + k2)) x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20530) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_STATE : Prop :=
    forall (x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k3 ty : Z),
      let _ := ctx_all in
      finv m -> (0 <= k3 < zlength fmt)%Z -> conv_type (znth fmt k3) = Some ty ->
      (forall (a2 a3 : word),
         evt psegs Q
           (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 ty) a2 a3 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 (Z_to_bv 64 (A + k3 + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 0) x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x206e8) fc None m (seg_rom psegs))) ->
      evt psegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (A + k3)) x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20668) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_DIR : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (i : Z) (d : dir) (rest : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= i)%Z -> (i + 1 <= zlength fmt)%Z ->
      parse_dir (sfx (i + 1)) = Some (d, rest) ->
      (forall (k4 : Z) (a2 a3 a4 t1 : word),
         (i + 1 < k4 <= zlength fmt)%Z -> rest = sfx k4 -> znth fmt (k4 - 1) = d_t d ->
         (0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
         evt psegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                    (Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) a2 a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 (Z_to_bv 64 (A + k4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x206e8) fc None m (seg_rom psegs))) ->
      evt psegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x2036c) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition S_END : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 apv] ->
      frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
      evt psegs (POST r st)
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) FPv x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20ea4) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_HEAD (fuel : nat) : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i cnt l k : Z) (args : list parg)
           (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i)%Z -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l <= INT_MAX)%Z ->
      implM psegs (printf_loop OUT OUTFP fuel (sfx i) args (cnt + l)) st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 cnt) FPv (Z_to_bv 64 (A + i)) x22 x23 x24 x25 (Z_to_bv 64 l) x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x202d0) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_CONV : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (d : dir) (a : parg) (args : list parg)
           (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
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
      implM psegs (cnt' <- conv OUT OUTFP c d a ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) x12 x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x206e8) fc None m (seg_rom psegs)).

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
      rw_cells psegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at psegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> body_loc BA (zlength body) -> (BA + zlength body < 2^64)%Z -> (zlength body <= INT_MAX)%Z ->
      (forall m', mem_inv psegs m' -> bytes_at psegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 155648)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      implM psegs (cnt' <- conv_tail OUT c fl w p prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 (Z_to_bv 64 (BA + zlength body)) x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20b6c) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition tregs (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 t3 t4 t5 t6 : word) (i4 c w BA wq pq : Z) : bvmap 5 word :=
    mkR xra SPv gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 a4 a5 a6 a7
        s2 (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) s8 s9 (Z_to_bv 64 wq) (Z_to_bv 64 pq) t3 t4 t5 t6.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Definition tinv (m : word -> option byte) (st : St) (k i4 : Z) (args : list parg) (fuel : nat)
      (PFXA fl n pl pq BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte) : Prop :=
    finv m
    /\ rw_cells psegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) (Z_to_bv 64 (Z.land fl 73728)) (Z_to_bv 64 n) (Z_to_bv 64 pl) (Z_to_bv 64 (pl + pq)) (Z_to_bv 64 0) alo ahi j128)
    /\ rw_cells psegs m (q + -392) [CB 24 digs]
    /\ rw_cells psegs m (q + -368) [CB 256 pad]
    /\ SINK m st /\ rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] /\ (0 <= k)%Z
    /\ args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args
    /\ Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args)
    /\ bytes_at psegs m BA (zb body) /\ Forall (fun c => 0 <= c < 256)%Z body /\ body_loc BA n /\ (BA + n < 2^64)%Z /\ n = zlength body
    /\ (forall m', mem_inv psegs m' -> bytes_at psegs m' PFXA (zb prefix)) /\ Forall (fun c => 0 <= c < 256)%Z prefix
    /\ (0 <= PFXA)%Z /\ (PFXA + pl <= 155648)%Z /\ pl = zlength prefix /\ (pl <= 2)%Z
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
      implM psegs (mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x20d88) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_T5 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM psegs (OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x20d6c) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_T4 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM psegs (mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x20ce8) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_T3 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM psegs (mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x20c60) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_T2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM psegs (OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x20c44) fc None m (seg_rom psegs)).

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
      implM psegs (mpad OUT 32 wq (pl + pq) fl ;;; OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x20bc4) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_INTC2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p argi : Z) (prefix body : list Z) (BA PFXA : Z)
           (s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at psegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
      (forall m', mem_inv psegs m' -> bytes_at psegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 155648)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      (0 <= argi < 2^64)%Z ->
      implM psegs (cnt' <- (if ((argi =? 0) && (p =? 0))%Z then conv_tail OUT c fl w p prefix []
                            else conv_tail OUT c fl w (Z.max p (zlength body + (if (argi =? 0)%Z then 1 else 0))) prefix body) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20b34) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_INTC : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) (BA PFXA : Z)
           (s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at psegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
      (forall m', mem_inv psegs m' -> bytes_at psegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 155648)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= argi < 2^64)%Z ->
      implM psegs (cnt' <- conv_int OUT c fl w p xp argi prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20b1c) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition dloop_post (x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Ft : bvmap 5 word) (fc : bv 32) (x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (a2 a3 : word) (xq : Z) (W : list Z) (m' : word -> option byte),
      ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xq) (Z_to_bv 64 (q + -392 + (j - zlength W))) a2 a3
                    (Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
                    x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength W))) x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x20b04) fc None m' (seg_rom psegs)
      /\ munch [(q + -392, q + -368)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rw_cells psegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength W)) ds ++ zb W ++ skipn (Z.to_nat j) ds)]
      /\ (1 <= xq <= 9)%Z /\ dec_digits x = (48 + xq)%Z :: W /\ (zlength W + 1 <= j)%Z.
  Definition S_DLOOP : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x j : Z) (ds : list byte),
      let _ := ctx_all in
      mem_inv psegs m -> rw_cells psegs m (q + -392) [CB 24 ds] ->
      (10 <= x < 2^64)%Z -> (zlength (dec_digits x) <= j <= 24)%Z -> x11 = Z_to_bv 64 (q + -392 + j) ->
      evt psegs (dloop_post x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc x j ds m)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) x11 x12 x13
                 (Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20acc) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_FMTU2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (x d jj : Z) (W prefix : list Z) (PFXA : Z)
           (pfx s2s za plp ahi : word) (j128 pre pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 (pre ++ zb W)] -> zlength pre = jj -> (1 <= jj)%Z ->
      ((d = 0 /\ W = [] /\ dec_digits x = []) \/ (1 <= d <= 9 /\ dec_digits x = (48 + d) :: W))%Z ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (forall m', mem_inv psegs m' -> bytes_at psegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 155648)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= x < 2^64)%Z ->
      implM psegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 d) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 PFXA)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 (q + -392 + jj)) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20b04) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_FMTU : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (x : Z) (prefix : list Z) (PFXA : Z)
           (pfx s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (forall m', mem_inv psegs m' -> bytes_at psegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 155648)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= x < 2^64)%Z ->
      implM psegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 x) x11 x12 x13 (Z_to_bv 64 10) x15 x16 (Z_to_bv 64 PFXA)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20abc) fc None m (seg_rom psegs)).

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
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (i mod 2^64)) ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (-2^31 <= i < 2^31)%Z ->
      implM psegs (cnt' <- (let '(argi, prefix) :=
                               (if INTMAX_MAX <? i mod 2^64 then ((- (i mod 2^64)) mod 2^64, [45])
                                else if negb (Z.land fl MARK_POS =? 0) then (i mod 2^64, [43])
                                else if negb (Z.land fl PAD_POS =? 0) then (i mod 2^64, [32])
                                else (i mod 2^64, []))%Z in
                            conv_int OUT c fl w p xp argi prefix (dec_digits argi)) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x207b8) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_CV_U : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (u : Z)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= u < 2^32)%Z ->
      implM psegs (cnt' <- conv_int OUT c fl w p xp u [] (dec_digits u) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x208f0) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition xloop_post (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Ft : bvmap 5 word) (fc : bv 32) (l x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (a2 a3 : word) (m' : word -> option byte),
      let H := hex_digits l x in
      ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 l) a2 a3 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength H))) x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x209a8) fc None m' (seg_rom psegs)
      /\ munch [(q + -392, q + -368)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rw_cells psegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength H)) ds ++ zb H ++ skipn (Z.to_nat j) ds)]
      /\ (zlength H <= j)%Z.
  Definition S_XLOOP : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l x j : Z) (ds : list byte),
      let _ := ctx_all in
      mem_inv psegs m -> rw_cells psegs m (q + -392) [CB 24 ds] ->
      (0 < x < 2^64)%Z -> (l = 0 \/ l = 32)%Z -> (zlength (hex_digits l x) <= j <= 24)%Z -> x23 = Z_to_bv 64 (q + -392 + j) ->
      evt psegs (xloop_post x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc l x j ds m)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) (Z_to_bv 64 l) x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20980) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_CV_X : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (u t : Z)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= u < 2^32)%Z -> (t = 120 \/ t = 88)%Z ->
      implM psegs (cnt' <- conv_int OUT c fl w p xp u
                              (if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0) then (if t =? 120 then [48; 120] else [48; 88]) else [])%Z
                              (hex_digits (Z.land t 32) u) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20968) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_CV_S : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p fl10 : Z) (xp : bool) (P : Z) (s : list Z) (slack : list byte)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 P) ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      bytes_at psegs m P (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256)%Z s ->
      ((- (P + zlength s + 1)) mod 8 <= zlength slack)%Z -> (0 < P)%Z ->
      (P + zlength s + 1 + zlength slack <= lo \/ q <= P)%Z ->
      (P + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= P)%Z ->
      (P + zlength s + 1 + zlength slack <= B \/ B + BS <= P)%Z ->
      (P + zlength s + 1 <= 2^47)%Z ->                              (* [comment removed for export] *)
      (fl10 = Z.land fl (Z.lnot 65536))%Z ->
      implM psegs (cnt' <- (if (p <? 0) && (INT_MAX <=? zlength s) then munr
                            else conv_tail OUT c (Z.land fl (Z.lnot ZERO_PAD)) w (if p <? 0 then zlength s else Z.min (zlength s) p) []
                                           (firstn (Z.to_nat (if p <? 0 then zlength s else Z.min (zlength s) p)) s))%Z ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 fl10) x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20800) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_CV_FP : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (y t : Z)
           (pfx s2s za pl plp : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= y < 2^128)%Z -> conv_type t = Some T_DBL ->
      implM psegs (cnt' <- (if xp && (p <? 0) then munr
                            else if (1 <? w) || (2^20 <=? p) then munr
                            else r <- OUTFP y w p fl t ;; if (r <? 0) || (INT_MAX - c <? r) then munr else mret (c + r))%Z ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x20768) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition POST1 : Z -> machine_state -> Prop :=
    fun r ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               F (ret_pc ra) fc0 None m' (seg_rom psegs)
      /\ munch [(lo, q)] m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
      /\ stk psegs m' lo q
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition S_EXIT1 : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m -> munch [(lo, q)] m0 m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      (0 <= r < 2^64)%Z ->
      evt psegs (POST1 r)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x20ffc) fc0 None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_P1 : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m -> munch [(lo, q)] m0 m ->
      rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells psegs m (q + -392) [CB 24 digs] ->
      rw_cells psegs m (q + -368) [CB 256 pad] ->
      pass1_ok fmt = true ->
      evt psegs (POST1 0)
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 A) x22 x23 x24 x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x202d0) fc0 None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition S_PRO : Prop :=
    forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (f : Z) (Q : machine_state -> Prop),
      let _ := ctx_all in
      stk psegs m0 lo q -> mem_inv psegs m0 -> bytes_at psegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      (0 <= f < 2^64)%Z ->
      (forall (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte) (a0 a1 a2 a3 : word),
         finv m -> munch [(q + -544, q)]%Z m0 m ->
         rw_cells psegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
         rw_cells psegs m (q + -392) [CB 24 digs] ->
         rw_cells psegs m (q + -368) [CB 256 pad] ->
         evt psegs Q
           (MS (mkR ra SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 nlt x15 x16 x17
                    s2e (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 A) s6e s7e s8e s9e (Z_to_bv 64 0) s11e x28 x29 x30 x31)
               F (Z_to_bv 64 0x202d0) fc0 None m (seg_rom psegs))) ->
      evt psegs Q
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 f) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x20220) fc0 None m0 (seg_rom psegs)).

End PrintfCore.
