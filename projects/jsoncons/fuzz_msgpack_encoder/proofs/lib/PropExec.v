(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed alu_ori, alu_sltiu, alu_xori and 73 more; added entry_stack_image_block, entry_stack_image_no_wrap, la_rseq_launch_auxv and 1 more; removed build_stack_bytes_within_span. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.PlacementSearch.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PropExec () := "C47Corelib7Program6Basics4flipC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics5Riscv7PreludeBbvmap_get_set_sameC4ELinuxProcessSemantics5Riscv7PreludeCbvmap_get_set_otherC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv3Sem5is_x0K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib7Numbers7BinNums1Z00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z8eqb_reflC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1N00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes3nat01K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z7testbitC45stdpp7numbers1ZGbounded_iff_bits_nonnegC47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums1Z01C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z;land_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C47Corelib4Init9Datatypes4andbK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05c49OSSVerify5KrLib8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_specc49OSSVerify5KrLib8PropExecAZ_bounded_by_bitsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegK46Stdlib9micromega6VarMap1t03C47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z4lxorC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z;lxor_nonnegK46Stdlib9micromega5Tauto8GFormula09C47Corelib4Init9Datatypes4xorbC56Stdlib6ZArith6BinInt1Z9lxor_specC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z;le_lt_transC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions?bv_half_modulusC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr03C35stdpp7tactics<f_equal_helpC45stdpp9bitvector;definitionsCbv_wrap_add_idemp_lC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z8add_commc49OSSVerify5KrLib8PropExecDbv_swrap_add_idemp_lC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions=bv_swrap_wrapI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesc49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;memory_readC45stdpp9bitvector;definitions6bv_addc49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z:shiftl_0_lC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC45stdpp9bitvector;definitions:bv_extractC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitionsCbv_extract_unsignedK47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv7Prelude4sextc49OSSVerify5KrLib8PropExec4v_lbC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>bv_sign_extendC45stdpp9bitvector;definitionsGbv_sign_extend_unsignedc49OSSVerify5KrLib8PropExec=b_extract8_idC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec9le_word_1C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec4v_lhC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z=shiftl_nonnegC47Corelib4Init9Datatypes8list_indC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses;rew_iff_revc49OSSVerify5KrLib8PropExecDbytes_le_to_Z_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z;shiftl_specC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z:shiftl_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z9lor_assocC56Stdlib6ZArith6BinInt1Z=shiftl_shiftlC56Stdlib6ZArith6BinInt1Z:shiftl_lorC56Stdlib6ZArith6BinInt1Z8lor_commC45stdpp9bitvector;definitions9bv_concatC56Stdlib6NArith6BinNat1N3addC45stdpp9bitvector;definitionsBbv_concat_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le2c49OSSVerify5KrLib8PropExec<bytes_le_appC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec8le2_specC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le4c49OSSVerify5KrLib8PropExec8le4_specC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le8C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00c49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C45stdpp9bitvector;definitions@bv_wrap_in_rangec49OSSVerify5KrLib8PropExec>bv_swrap_congrC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecDbv_swrap_add_swrap_lC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCbv_wrap_add_idemp_rC45stdpp9bitvector;definitions?bv_add_unsignedc49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64c49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec<wrap64_rangeC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec<Z_land_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC45stdpp9bitvector;definitions6bv_andC45stdpp9bitvector;definitions?bv_and_unsignedK4ELinuxProcessSemantics5Riscv5Instr5aluop0:c49OSSVerify5KrLib8PropExec5v_oriC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec;Z_lor_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_orC45stdpp9bitvector;definitions>bv_or_unsignedK4ELinuxProcessSemantics5Riscv5Instr5aluop09c49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec<Z_lxor_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_xorC45stdpp9bitvector;definitions?bv_xor_unsignedK4ELinuxProcessSemantics5Riscv5Instr5aluop06C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6NArith6BinNat1N2leC45stdpp9bitvector;definitionsEbv_sign_extend_signedC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsc49OSSVerify5KrLib8PropExec6v_sltiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr5aluop04C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuc49OSSVerify5KrLib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05c49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec5v_sltC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec5v_xorC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextc49OSSVerify5KrLib8PropExec8u6_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions=Z_to_bv_smallC45stdpp9bitvector;definitions>bv_zero_extendC45stdpp9bitvector;definitionsGbv_zero_extend_unsignedc49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec;shamt6_maskC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_shiftlC45stdpp9bitvector;definitionsBbv_shiftl_unsignedK4ELinuxProcessSemantics5Riscv5Instr5aluop03c49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec>Z_shiftr_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_shiftrC45stdpp9bitvector;definitionsBbv_shiftr_unsignedK4ELinuxProcessSemantics5Riscv5Instr5aluop07c49OSSVerify5KrLib8PropExec6v_sraiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_ashiftrC45stdpp9bitvector;definitionsCbv_ashiftr_unsignedK4ELinuxProcessSemantics5Riscv5Instr5aluop08c49OSSVerify5KrLib8PropExec5v_sllC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec=regamt64_maskC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec5v_srlC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extc49OSSVerify5KrLib8PropExec5v_sraC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C45stdpp9bitvector;definitionsAbv_extract_signedc49OSSVerify5KrLib8PropExec8u5_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C46Stdlib6ZArith:Znumtheory<Zmod_div_modc49OSSVerify5KrLib8PropExec=bv_wrap32_modC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec>low32_unsignedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu32c49OSSVerify5KrLib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecDbv_swrap_add_idemp_rC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec>bv_swrap_wrap'C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec?sext32_unsignedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c49OSSVerify5KrLib8PropExec7v_slliwC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z?mul_mod_idemp_lC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2c49OSSVerify5KrLib8PropExec;shamt5_maskC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7v_srliwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7v_sraiwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec<low32_signedC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6v_addwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6v_subwC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivBZminus_mod_idemp_rC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC45stdpp9bitvector;definitions6bv_subC45stdpp9bitvector;definitions?bv_sub_unsignedK4ELinuxProcessSemantics5Riscv5Instr5aluop02c49OSSVerify5KrLib8PropExec6v_sllwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec=regamt32_maskC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6v_srlwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6v_srawC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec5v_mulC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6v_mulhC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec8v_mulhsuC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7v_mulhuC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec5v_divC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec5v_remC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divc49OSSVerify5KrLib8PropExec6v_mulwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?mul_mod_idemp_rC45stdpp9bitvector;definitions6bv_mulC45stdpp9bitvector;definitions?bv_mul_unsignedK4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions8bv_quotsC56Stdlib6ZArith6BinInt1Z4quotC45stdpp9bitvector;definitionsAbv_quots_unsignedc49OSSVerify5KrLib8PropExec7div0_32C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6v_divwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop05C45stdpp9bitvector;definitions7bv_remsC56Stdlib6ZArith6BinInt1Z3remC45stdpp9bitvector;definitions@bv_rems_unsignedc49OSSVerify5KrLib8PropExec6v_remwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop07C45stdpp9bitvector;definitions7bv_divuc49OSSVerify5KrLib8PropExec7v_divuwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop06C45stdpp9bitvector;definitions7bv_moduc49OSSVerify5KrLib8PropExec7v_remuwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop08C45stdpp9bitvector;definitionsEbv_half_modulus_twiceC45stdpp9bitvector;definitions>bv_modulus_posC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullc49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions>bv_swrap_smallc49OSSVerify5KrLib8PropExec;bv_swrap_hiC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec5b_luiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1ZBmod_pow2_bits_highC56Stdlib6ZArith6BinInt1Z9bits_inj'c49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notc49OSSVerify5KrLib8PropExec8jalr_tgtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lnotc49OSSVerify5KrLib8PropExec>Z_land_m2_wrapC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions?bv_not_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr08K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportc49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalc49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setc49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec=bv_eqb0_is_x0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5instr0;K4ELinuxProcessSemantics5Riscv5Instr5instr0<K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0BI4ELinuxProcessSemantics5Riscv5Instr5mulop00K4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv5Instr5instr05c49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenI4ELinuxProcessSemantics5Riscv5Instr;branch_cond00c49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec>step_opimm_genC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7alu_oriC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec9alu_sltiuC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec8alu_sltiC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecAstep_shiftimm_genC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec8alu_sraiC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec;step_op_genC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7alu_subC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7alu_sltC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7alu_andC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6alu_orC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7alu_xorC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7alu_sllC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7alu_srlC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7alu_sraC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec@step_opimm32_genC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7w_slliwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecCstep_shiftimm32_genC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7w_srliwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7w_sraiwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6w_addwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec=step_op32_genC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6w_subwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6w_sllwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6w_srlwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6w_srawC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec5m_mulC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec<step_mul_genC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6m_mulhC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop02c49OSSVerify5KrLib8PropExec8m_mulhsuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop03c49OSSVerify5KrLib8PropExec7m_mulhuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop04c49OSSVerify5KrLib8PropExec5m_divC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec5m_remC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6w_mulwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec>step_mul32_genC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6w_divwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7w_divuwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6w_remwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec7w_remuwC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec4c_eqC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecBstep_branch_tk_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c49OSSVerify5KrLib8PropExecBstep_branch_ft_genC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c49OSSVerify5KrLib8PropExec5c_ltsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04c49OSSVerify5KrLib8PropExec5c_ltuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5instr01K4ELinuxProcessSemantics5Riscv5Instr5instr02c49OSSVerify5KrLib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03c49OSSVerify5KrLib8PropExec7is_x0_0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04c49OSSVerify5KrLib8PropExec6b_jalrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06c49OSSVerify5KrLib8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize01c49OSSVerify5KrLib8PropExec8b_lb_valC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec8b_lh_valC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec9le_word_vC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize02c49OSSVerify5KrLib8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecCbytes_le_to_Z_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffc49OSSVerify5KrLib8PropExec8b_lw_valC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03C45stdpp9bitvector;definitionsCbv_wrap_bv_unsignedK4ELinuxProcessSemantics5Riscv5Instr5msize04C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordc49OSSVerify5KrLib8PropExec?bv_signed_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltc49OSSVerify5KrLib8PropExec<bv_signed_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_gec49OSSVerify5KrLib8PropExec;c_lts_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retc49OSSVerify5KrLib8PropExec?errno_ret_rangeC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec;c_lts_neg_0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_getc49OSSVerify5KrLib8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem2w0C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z7mod_1_rC46Stdlib4Bool4Bool;orb_false_rC56Stdlib6ZArith6BinInt1Z=testbit_neg_rC56Stdlib6ZArith6BinInt1Z;shiftr_specC46Stdlib4Bool4Bool;orb_false_lc49OSSVerify5KrLib8PropExec<bv_wrap8_modC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=shiftr_nonnegc49OSSVerify5KrLib8PropExec@bytes_le_Z_to_leC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc49OSSVerify5KrLib8PropExec:bytes_le_NC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8c49OSSVerify5KrLib8PropExec>n_to_le_8_specC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC46Stdlib5Lists4List9nth_errorC47Corelib4Init5Peano2ltI47Corelib4Init5Logic2ex00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltc49OSSVerify5KrLib8PropExecDnth_error_skipn_consC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List6nth_okC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_lec49OSSVerify5KrLib8PropExec6u_add1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega5Tauto4kind02C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List8flat_mapC47Corelib4Init3Nat3mulc49OSSVerify5KrLib8PropExec@length_n_to_le_8C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesc49OSSVerify5KrLib8PropExecCtotal_arg_bytes_natC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordc49OSSVerify5KrLib8PropExec<len_word_natC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecAnat_to_word_mergeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions<bv_add_assocC35stdpp4base7assoc_LC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<string_addrsC47Corelib4Init9Datatypes3fstc49OSSVerify5KrLib8PropExec:word_add_0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecEnat_to_word_add_mergeC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec9word1_natC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecJstring_addrs_fst_structureC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout=at_random_ptrC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout:auxv_bytesC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesC47Corelib5Lists7ListDef6repeatC56Stdlib6ZArith6BinInt1Z<eq_decidablec49OSSVerify5KrLib8PropExecAtotal_arg_bytes_ZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutFlength_at_random_bytesc49OSSVerify5KrLib8PropExecFlength_flatten_stringsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAlength_auxv_bytesc49OSSVerify5KrLib8PropExecGlength_string_addrs_fstC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecClength_flat_map_le8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthc49OSSVerify5KrLib8PropExecAstring_addrs_pairC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_spanC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9auxv_sizeI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List:firstn_allC47Corelib4Init3Nat3subC46Stdlib5Lists4List9app_nil_rC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_appC46Stdlib5Lists4List7skipn_0C46Stdlib5Lists4List9skipn_allC46Stdlib5Lists4List9skipn_appc49OSSVerify5KrLib8PropExec9rdn_stackC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?entry_block_topC4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem3RunKstack_to_mem_image_in_blockc49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec>read_at_offsetC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecBrdn_image_in_blockC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec?bsb_argc_prefixC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExecDread_at_offset_imageC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<firstn_skipnC47Corelib5Lists7ListDef3nthC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses:impl_morphC46Stdlib5Lists4List@firstn_length_leC46Stdlib5Lists4List=nth_error_nthC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsc49OSSVerify5KrLib8PropExecMbuild_stack_bytes_within_spanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0023?PlacementSearchBpage_round_up_Z_leC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run>entry_page_topC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyc49OSSVerify5KrLib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8PropExec3fx0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizec49OSSVerify5KrLib8PropExec=wrap_above_spC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Class FPState := mkFP { fp_regs : bvmap 5 word; fp_csr : bv 32 }.
Definition fx0 : FPState := mkFP bvmap_empty (Z_to_bv 32 0).

Definition mkst `{fx : FPState} (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition getr (regs : bvmap 5 word) (r : reg) : word :=
  if bv_eqb r 0 then Z_to_bv 64 0 else reg_get regs r.
Definition regupd (regs : bvmap 5 word) (r : reg) (v : word) : bvmap 5 word :=
  bvmap_set r v regs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_eqb0_is_x0 : forall r : reg, bv_eqb r 0 = is_x0 r.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01rp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj15Tg006Gj14Tg006lj10Tg007Jj11Tg007mj13Tg008Uj22Tg008o#5#4#0#1g009Tf0#3'2W0o"). Qed.

Lemma is_x0_0 : is_x0 0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g008Uj20Tg009Tg00:4'0o"). Qed.

Lemma bv_wrap64_mod : forall z : Z, bv_wrap 64 z = (z mod 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg00:Tj11Tg00;2j23Tg00;Oj22Tg008Uj24Tg00;oR0f0g008o#0R1#1%01#0#0#0#0#1'3'2,40W0o"). Qed.

Lemma bv_wrap32_mod : forall z : Z, bv_wrap 32 z = (z mod 2^32)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg00:Tj11Tg00;2j23Tg00;Oj22Tg008Uj24Tg00;oR0f0g008o#0R1#1%01#0#0#0#1'3'2,40W0o"). Qed.

Lemma bv_eqb_refl : forall {n} (a : bv n), bv_eqb a a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11np;1p;2p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g007Jj14Tg00<Mj23Tg00=7j10Tg00=Yj31Tg00>Fj32Tg00>`f0R0#4f1R1/30#0g009TA1100g00:432eW0W1o"). Qed.

Lemma bv_eqb_neq : forall {n} (a b : bv n), a <> b -> bv_eqb a b = false.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01nh11Hh22b1h32b2h41xh51yh63Hneh72Huh81ah91bp;1p;3p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g007Jj12Tg00>Fj30Tg00?>j13Tg00?Wj25Tg00@4j28Tg00<Mj21Tg00@Uj37Tg00=Yj36Tg009Tf0R0g00A930p=4g00>`R1%20R2f1R3#2R4f2R5#2?030R6#3g00;oR7g00AYR81530#4A0753#3R9[A0730#31553#4[R:f3R;/55#4\91830P0n2001000000120000000X57W4P:^57^47P0f4R:/1;R911:5R<A079<R<P5P811;511;3507R8\611531150507%2;?053[R7%2:?0;5\8A7530P0n2001000000120000000X34X22X01P7^34^22^01P0f6f5P:P3O4b1O1W7%3<eO3b1A6;53#4eW6W9W8W0o"). Qed.

(* [comment removed for export] *)
Lemma arg_reg_0 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g007Jj10Tg00>Fj31Tg00<Mj22Tg00@Uj34Tg005bj13Tg006Gj1<Tg006lj1;Tg00:Tj15Tg00B4j16Tg00BTj27Tg00C1j28Tg00CWj39Tg008Uj2:Tg00>`R0f0R1#0R2f1R3#0R4g00AYf2R5#0?131g00;oR6f3R7/25127331R8[12531251516%07?153[R9f4#0?175\8A4531P1n2001000000120000000W1W0W2P9^14^02^20P1g008o#3#<R1#;R0%31#5R1g00D:#6'7,80g00DY9901R11201,:6O4b3o"). Qed.
Lemma arg_reg_1 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g007Jj10Tg00>Fj32Tg00<Mj21Tg00@Uj36Tg005bj15Tg006Gj14Tg006lj1<Tg00:Tj13Tg00E5j1;Tg00B4j1:Tg00BTj27Tg00C1j28Tg00CWj39Tg008Uj2=Tg00>`R0f0R1#0R2f1R3#0R4g00AYf2R5#0?231g00;oR6f3R7/15117332R8[11531151526%07?253[R9f4#0?275\8A6531P1n2001000000120000000W1W0W2P9^14^02^20P1g008o#5#4R1#<R0%51#3g00D:#;#:'7,80%41#3g00DY590R11101,=6O4b3o"). Qed.
Lemma arg_reg_2 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g007Jj10Tg00>Fj31Tg00<Mj22Tg00@Uj37Tg005bj13Tg006Gj16Tg006lj1<Tg00:Tj15Tg00E5j14Tg00B4j1;Tg00BTj28Tg00C1j29Tg00CWj3:Tg008Uj2=Tg00>`R0f0R1#0R2f1R3#0R4g00AYf2R5#0?131g00;oR6f3R7/25127331R8[12531251516%07?153[R9f4#0?175\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g008oR1#3#6R0#<R2%30#5g00D:#4#4#;'8,92%61#3#3#5g00DY5:2R11221,=6O4b3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_testbit_high : forall n a k, (0 <= n)%Z -> (0 <= a < 2^n)%Z -> (n <= k)%Z ->
  Z.testbit a k = false.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01lh11Hh23Ha1h33Ha2h42Hkh52Hnh61ah71kh81np;2p;1p;4p;6p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g00ETj20Tg005bj1:Tg00:Tj18Tg00;2j21Tg00F0j22Tg00AYR0j29Tg00FLj24Tg00Fmj47Tg00GWj66Tg00>Fj35Tg009Tf0R1g00A935p=3g00;oR2g00H2R3f2R4'0R5g008o#:#8R6f3R7'1,24,95P01037f4R0,16,27f5R5/071450#3[P11035f6R5f7R3,16'2f8R0/05f9R7,16,20f;R8/01f1R9,48#3[^02[f:R8/011489#3[^021168,27[P7P0P5P4C7P9P3P1E6W4W3W2P9P1O2n2001000000120000000W1W5X72X62W8o"). Qed.

Lemma Z_bounded_by_bits : forall n a, (0 <= n)%Z -> (0 <= a)%Z ->
  (forall k, (n <= k)%Z -> Z.testbit a k = false) -> (a < 2^n)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01lh12Hah22Hbh32Hnh41ah51kh61np;2p;1p;4p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g00ETj20Tg00FLj22Tg005bj15Tg00:Tj19Tg00;2j24Tg00F0j23Tg00Fmj48Tg00HPj47Tg00>Fj36Tg009Tf0R0g00A936p=1g00;oR1g00H2f1R2'0R3f4R4/001242#1[^51f3R5g008o#5#9R6/44'3f6R7/001272#1[^01[f5R7/001272#1[^011467,34[P4P5f2P2C8P0C7W2X13W3X41W6o"). Qed.

Lemma Z_land_range : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b)%Z ->
  (0 <= Z.land a b < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01Hh14__x1h22H0h36__sat0h46__sat1h51bh67__arithh74__ffh88__varmaph95__with:2Hah;1ah<4__p1h=2Hbh>2Hkh?1kp;1p;2p;3p;6p;7p;4p;5p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210P1p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj12Tg00:Tj1>Tg00;2j2ETg00F0j21Tg00AYR1j2:Tg00Hkj26Tg00IIj24Tg00Icj2HTg00JHj2FTg00K0j3DTg00KTj1CTg00L4j1BTg00LTj2\Tg00M2j1VTg00MPj1UTg00N;j2<Tg00N^j2TTg00OAj1QTg00Ocj6PTg00PGj7MTg00Pkj2LTg008Uj2=Tg00QMj2GTg00>Fj39Tg00R9j3ITg00RXj4JTg00SJj1KTg00ETj28Tg00FLj27Tg00Shj2?Tg006lj1NTg00TFj3OTg00Tij4@Tg00UTj7RTg00V8j6STP0j6ATg00W4j3[Tg00WWj5ZTg00XVj4YTg00Y1j7WTg00YUj8XTg00H2R0f0R2'8p=0g00;oR3f1R4g00Z9P2C@p=;P4g00Z`R5g00[?R6P6g00[_R7P2g00\?FWp=5f3R8P5P6P6P7f2R9P4P2GXp=3%04R:g008oR;#2R<#>R=%2<#2#2#2#2R<#>R>'ER?,14':1689R@#0RA11@?P11642#0%09RB/4:RC[%02RD,4:1694#0[REPA\C1H42P2n2001000000120000000X53X;3PE^53^;3P2f4REP81F=>RC110=%0>RA110?[[RF%0=RGg00\_RHAD=>4UW:RI%0?\H^:GRGP1f6RH#0RJ11H?f7RH#0RK/4JPEf8RJ#0RLf9RM/1?p-0RNg00];RO#CRP%BORO1\34RQ%V3RR%U3RS1<30RT1T3;R;';,5SRU%Q6RVPSP5P6P6P7PUPSP5P6P6P7P8EPFMC31LS7RWP2P9g009TRXg00:4RY'=1G29=9XYdAI304CJR0b7b8b9X13W<14:9\D^13^<NP2f:RN#0f;P9O3b6W2W0P4P2O2n2001000000120000000b3b4O3b0RDP>P@PCPFPIPGP1f5R@#011@?PAP811J?R8PPPO%K3PR1<3>RY,;T,5SPWP0b7b8b9PAP2b6RTW2X0KP4P2O2n2001000000120000000b3b4PD18>2RDPX17@4RZ17E4'?g00A9R[99X2X5XPXP[17@9,?2=9X[X5X1=X[PZP>P@P4PCPFPIPGP1PK11H?RZPAP@%0MRM11N?RNPTW2W0P4P2O2n2001000000120000000b3b4PCPFPIPGP1PKPZ1:L8P@PPPOPQPRPSP3P;g00]g1<3=%N<5O3C@,5SR<PVPSPUPVPSP5P6P6P7PUP<FRC3C3PWP0b7b8b9X13112?119?,:B\:[^13P2f<P4P9O3b6X2NX0MP4P2O2n2001000000121000000b3b4PCPFPIPGP1PKPZ18>EP@PPPOPQPRPS1;Y;,5SRSPVPSC3PWP0b7b8b9X1318>4\D^13P2PJPHO2b6X2NX0MP4P2O2n2001000000120000000b3b4ESEA16@E/74A[@E4EAW>X?3DZCYX=:W:X53X;3o"). Qed.

Lemma Z_lor_range : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  (0 <= Z.lor a b < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01Hh12H0h22H1h32H2h46__sat0h56__sat1h64__x1h71bh87__arithh94__ffh:8__varmaph;5__with<2Hah=1ah>4__x2h?2Hbh@2HkhA1kp;1p;2p;3p;4p;6p;5p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210P1p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg00:Tj1@Tg00;2j2ITg00F0j21Tg00AYR1j22Tg00^Nj28Tg00^kj2RTg00JHj2NTg00K0j3LTg00KTj1HTg00L4j1GTg00LTj2ETg00SJj1\Tg00_Oj4VTg00M2j1UTg00MPj1TTg00N;j2<Tg00N^j2CTg00OAj1STg00Pkj2QTg008Uj2?Tg00QMj2MTg00>Fj3>Tg00R9j3KTg00RXj4JTg00ETj24Tg00FLj27Tg00_mj2:Tg006lj1OTg00TFj3PTg00Tij4DTg00V8j6BTP0j6;Tg00`Jj3FTg00WWj5[Tg00XVj4ZTg00Y1j7YTg00UTj7WTg00YUj8XTg00H2R0f0R2'4p=0g00;oR3f1R4g00Z9P2CDp=9P4g00Z`R5g00[?R6P6g00[_R7P2g00\?FYp=6f2R8P5P6P6P7P4P2FWp=Af3R9P5P6P6P7P8P4P2GXp=5g009TR5g00A9R:7>2p==%04R;g008oR<#3R=#@R>%3=#3#3#3#3R?#@R@'IRA,14'2RB1898RC#0RD11CAP11842#0%08RE/2;RF[%02,2;1884#0[RGPD\F1R42P2n2001000000120000000X73X=3PG^73^=3P2f4RGP91N>@RF110>%0@RD110A[[RH%0>RIg00\_RJAL>@4UW<RK%0A\J^<IRIP1f5RJ#011JAf7RL#0RMf6RN#0RO'2P9f8RP/1ARQP1f:RR#0RS11RAf;RR#0RT/2SPPf<RS#0RUf=RV/1Ag00];RW#HRX%GWRWP31E38P4%\3RYCV%U3RZ%T3R[1<30R\1C3='9,6[R=%S6R6P[1C3<R<,9\,6[R]P6AA[]=C5C51Q[7R7P2P8g00:4R=,?51M28=>5=dAK304CJR0b9b:b;X63X>3%09,2E\;\;^63^>3P2f>R9f?R=PNP8O4b8W3W2P4P2O2n2001000000120000000W1X0MP4P2O2n2001000000121000000b4b5O3b0R^P@PCPFPHPKPIP1%0G11GAPDP811LARCP1f9R_#011_AR`PDPL11SARLPXPWPYPZ1<3@RY,9\,6[P7P0b9b:b;PDP2b8R\W3X2TP4P2O2n2001000000120000000W1X0OP4P2O2n2001000000120000000b4b5P^14@2R^P517J4Ra17G4Rb':%=2X75P5P:17J8,:2#=X75P5P:1::2#=X751?5:PbP@PGP4PFPHPKPIP1PO11NARbPDPG%0PR:P1PT11RAR5PDP_%0VRV119AR9P\W3W2P4P2O2n2001000000120000000X1`W0P4P2O2n2001000000120000000b4b5R\PFPHPKPIP1POPb12MCPGP1PTP512T5P_PXPW1E34RCPZP[P3P<g00]g1<3>%O?5P3CD,6[R?P6P[P]P6AA[]?C5C5P7P0b9b:b;X63R?112A118A,2E\;[^63R;P2P=PJPNO3b8X39X2VP4P2O2n2001000000121000000X1`X0:P4P2O2n2001000000121000000b4b5PFPHPKPIP1POPb14@GPGP1PTP514@PP_PXPWPCPZP[19Y<,6[R[P6P[C5P7P0b9b:b;X6314@4\^^63P2PSPRO2b8X39X2VP4P2O2n2001000000120000000X1`X0:P4P2O2n2001000000120000000b4b5RREBE;PaP@PJP4P\PFPHPKPIP1POPb12:QPGP1PTP512ULP_P?P;P2f@P4P8O3b8X39X2VP4P2O2n2001000000121000000X1`X0:P4P2O2n2001000000121000000b4b5PREBE;18JG/74AFJG4E;W@XA3D[CZX?BW<X73X=3o"). Qed.

Lemma Z_lxor_range : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  (0 <= Z.lxor a b < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01Hh12H0h22H1h32H2h46__sat0h56__sat1h64__x1h71bh87__arithh94__ffh:8__varmaph;5__with<2Hah=1ah>4__x2h?2Hbh@2HkhA1kp;1p;2p;3p;4p;7p;6p;5p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210P1p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj12Tg00:Tj1ATg00;2j2ITg00F0j21Tg00AYR1j23Tg00`lj29Tg00aJj27Tg00acj2OTg00JHj2LTg00K0j3HTg00KTj1GTg00L4j1FTg00LTj2ETg00SJj1[Tg00_Oj4WTg00M2j1VTg00MPj1UTg00N;j2=Tg00N^j2BTg00OAj1STg00bHj7RTg00Pkj2NTg008Uj2@Tg00QMj2MTg00>Fj3?Tg00R9j3KTg00RXj4JTg00ETj26Tg00FLj28Tg00blj2;Tg006lj1PTg00TFj3QTg00Tij4DTg00UTj7TTg00V8j6CTP0j6>Tg00cJj3]Tg00WWj5\Tg00XVj4ZTg00Y1j7YTg00YUj8XTg00H2R0f0R2'6p=0g00;oR3f1R4g00Z9P2CDp=:P4g00Z`R5g00[?R6P6g00[_R7P2g00\?FYp=4f3R8P5P6P6P7f2R9P4P2GXp=5g009TR:g00A9R;7?2p=<%04R<g008oR=#2R>#AR?%2>#2#2#2#2R@#ARA'IRB,14'3RC1989RD#0RE11DBP11942#0%09RF/7<RG[%02,7<1994#0[RHPE\G1O42P2n2001000000120000000X73X=3PH^73^=3P2f4RHP81L?ARG110?%0ARE110B[[RI%0?RJg00\_RKAH?A4UW<RL%0B\K^<JRJP1f5RK#011KBf7RM#0RNf6RO#0RP'7P8f8RQ/1BRRP1f:RS#0RT11SBf;RS#0RU/7TPQf<RT#0RVf=RW/1Bg00];RX#GRY%FXRXP31E39P4%[3RZCW%V3R[%U3R\1=30R]1B3>':,4\R>%S6R^P\1B3=R=,:],4\R_P^P\P5P6P6P7P_P>FRC5C51N\7R>P2P9g00:4R`,@:1M29=?:`dAK304CJR0b9b:b;X63X>3%08,7F\<\<^63^>3P2f>R8f?R`POP9O4b8W3W2P4P2O2n2001000000120000000W1X0NP4P2O2n2001000000121000000b4b5O3b0RaPAPDPGPIPLPJP1%0H11HBPEP911MBRDP1f9Rb#011bBRcPEPM11TBRMPYPXPZP[1=3ARZ,:],4\P>P0b9b:b;PEP2b8R]W3X2UP4P2O2n2001000000120000000W1X0PP4P2O2n2001000000120000000b4b5Pa16A2RaP:18K4Rd18H4Re';%<2X7:P:P;18K9,;2#<X7:P:P;1;;2#<X7:1@:;PePAPHP4PGPIPLPJP1PP11OBRePEPH%0QR;P1PU11SBR:PEPb%0WRW118BR8P]W3W2P4P2O2n2001000000120000000X1cW0P4P2O2n2001000000120000000b4b5R]PGPIPLPJP1PPPe13NDPHP1PUP:13U:PbPYPX1E34RDP[P\P3P=g00]g1=3?%P@5Q3CD,4\R@P^P\P_P^P\P5P6P6P7P_P@FTC5C5P>P0b9b:b;X63R@112B119B,3F\<[^63R<P2P`PKPOO3b8X38X2WP4P2O2n2001000000121000000X1cX0;P4P2O2n2001000000121000000b4b5PGPIPLPJP1PPPe16AHPHP1PUP:16AQPbPYPXPDP[P\1:Z=,4\R\P^P\C5P>P0b9b:b;X6316A4\a^63P2PTPSO2b8X38X2WP4P2O2n2001000000120000000X1cX0;P4P2O2n2001000000120000000b4b5RSECE>PdPAPKP4P]PGPIPLPJP1PPPe13;RPHP1PUP:13VMPbP@P<P2f@P4P9O3b8X38X2WP4P2O2n2001000000121000000X1cX0;P4P2O2n2001000000121000000b4b5PSECE>19KH/84A]KH4E>W@XA3D\CZX?CW<X73X=3o"). Qed.

Lemma Z_shiftr_range : forall a k : Z, (0 <= a < 2^64)%Z -> (0 <= k)%Z ->
  (0 <= Z.shiftr a k < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h06__sat1h14__x1h22H0h37__arithh46__sat0h52Hah64__ffh78__varmaph85__with92H1h:6__sat2h;6__sat3h<1Hh=1ah>4__x2h?2Hkh@1khA1zp;1p;2p;3p;4p;5p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210P1p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg00:Tj1=Tg00;2j28Tg00F0j26Tg00AYR1j2JTg00cmj2CTg00JHj2Aj4QTg00K0j3@Tg00KTj1LTg00L4j1KTg00SJj1lTg00M2j1kTg00MPj1fTg00N;j2ITg00Pkj2ZTg008Uj2XTg00QMj2WTg00>Fj3VTg00R9j3UTg00RXj4TTg00LTj2FTg00N^j2GTg00OAj1PTg00dJj4MTg00dkj2DTg00ETj2>Tg00eHj2BTg00f1j2ETg00fRj4RTg00g3j2STg00E5j1?Tg00g\j2;Tg00hEj39Tg00hnj2jTg00iZj3iTg00_Oj4eTg00j:j5dTg006lj1bTg00TFj3^Tg00j^j3]Tg00kAj5_Tg00kmj5\Tg00XVj4`Tg00lRj2aTg00m2j3[TP0j6cTg00Tij4HTg00Y1j7YTg00YUj8gTg00m[j3hTg00H2R0f0R2'>p=1%02#0#0#0p=N1602p=4g00;oR3f1R4g00]gP2CHp=<P4g00Z`R5g00[?R6P6g00[_R7P2g00\?FYp=5P3P4g00Z9P2CHp=:f3R8P5P6P6P7f2R9P4P2Ggp=3%02#0p=O%02#0#0#0#0#0#0#0p=7Ah342p=2%14R:g008oR;#0R<#=R=%0<#NR>#=R?'8R@,64RA'JP318=9RB,C8%12RC162@RD'JXA3P=P91A=?RE%4=RF%1?%4@[[RG%1=RHg00\_RIA@=?4UW5R?%1@\IRJ^5HRKP1f5RL#1RM16L@RNPFP8f7RO#1RPf8RQ/6@RRg00];RS#LRT%KSRU%l3RV%k3RW%f3RX1I30RY1I3=RZ'<'5R[1ZX7R\P2P9g009TR]g00:4R^'X1W29=V]^dAU304CTR^b6b7b8PFP2b3W2W<P4P2O2n2001000000120000000b4b0P2CQ%4Bf4RB18=8R]'CR_#116_@PBP]PEPGP?PK1A=LR`f6Ra#118=O#4[\FRbA@=Q4VIX5HRc18=QRd#1\I^5HRIP1%1QRePRf9Rf#1Paf:Rg#1Rhf;/6@RiPaP2PgO2X=FRjf<,8=#4^=FRkPTPU1F34RlPWPX1G3;Rm,:Y,5XRn%P6RoPnC3P\P^b6b7b8X13RpP:\C^13RCP2f>RqP8O2b3b0W9W2P4P2O2n2001000000120000000b4b0b:b;PEPGP?PKP`PbPcPIP1PePR%4dPaPjPkPTPUPlPWPX1<Ym,5XRrPoPrC3P\P^b6b7b8X13%42%44[^13P2f=,8=RrPgO2b3b0X9iX2hP4P2O2n2001000000120000000b4b0b:b;RsCMP_PBP@PBP]PBPsPEPGP?PKP`PbPcPIP1PePR1Ddf,>fPaPjPk%O>#7#7#7#7#7#7#7#=,B3RdP3%=;,E3P;1E30CR,S3g00D:R0#?R;#?Rs,;3R]'2'2%?s,;3Rs1;3;R;,2]=93;R;'21B3=1;30R0,2s'2120;,2d1200,2d593593593593g00nD'j=iSTPUP31F39P4PVCePWPXPXP[Po1G3<R<,<Y,5XR[C3PoPXPX1:YZ,5XPoPXPXP5P6P6P7DdPo%b>9^3ZRZ,:Y,5XC3C3PoPXP[PoPXPnPoA]3<m,:m,5XC3C3C3C3P\P^b6b7b8X13X>3%49\FPJ\H%48%181DLB,>B[[[[^13^>3P2PrPqP4PQPgP8O6b3b0X9iX2hP4P2O2n2001000000121000000b4b0b:b;D_PEPGP?PKP`PbPcPIP1PePR16f@PaPjPkPTPUPlPWPX1<mZ,5XRXPoPXC3P\P^b6b7b8X13PA\D^13P2PqP9O2b3b0X9iX2hP4P2O2n2001000000120000000b4b0b:b;D\C`b<1a89PEPGP?PKP1PMPNPMP8PpPCP2PfPOO2b3X2RX<PP4P2O2n2001000000120000000b4b09[89EcX?:W5X@3X=3o"). Qed.

(* [comment removed for export] *)
Lemma bv_swrap_add_idemp_l : forall n x y,
  bv_swrap n (bv_wrap n x + y) = bv_swrap n (x + y).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h07__arithh14__x1h24__x2h34__x3h41zh51Hh64__ffh78__varmaph85__with91nh:1xh;1yp;2p;1p;4p;3p;7p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR1p4p710p8P0g002FR0p4p710R2p8p1002dp4p7210P2p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g00o0j21j1@Tg00BTj20Tg00oVj15Tg010DR2j18Tg008Uj24Tg00KTj1ITg00L4j1CTg00LTj29Tg00_Oj4>Tg00M2j1=Tg00MPj1<Tg00N^j27Tg005bj1;Tg006Gj1KTg010aj33Tg00Tij4JTg00Y1j7HTg00Pkj2GTg00QMj2DTg00>Fj32Tg00R9j3BTg00RXj4ATg011Dj86Tg011aj3?TP0j6ETP1j6FTg012Sj2:Tg00>`g00;oR1P1P1f2R0f1R3,10R4f0R5'0R6%50R7'0R8'1R9#81035R:/07,10R;#8P7P7P1P1\1R<P2P2P9P;P<\1/42g00];R2#I%C2P11910P3f3R2,91C>%=1%<1R;g00Z`g00[?R9P9g00[_R9P1g008oR=,71R>%;=,71R?%K=,71R=531531g013:A31>?=31=CJg00\?FH1G;9P5P0g009TR9g00:4R;'41D50=29;dg00H2=B13CAb6b7b8X11X21X31R;1030,051053/00521^11^21^31R9P5%52R=P31120R?O3b01057,04=218P1103=R8,0?R4f4R>/151020%5>R@'0,1>R>521X41P11008RA,12A215>X41P1P1%@2R>P>PA1003/0=14<>P;P9P5P@P0P2O3b0G61124A?208EE10?3/0=P5EFb5G61417G61:061:0:521eX;1W:W9o"). Qed.

Lemma bv_swrap_add_idemp_r : forall n x y,
  bv_swrap n (x + bv_wrap n y) = bv_swrap n (x + y).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11nh21xh31yp;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210P1p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g00o0j27Tg00BTj21Tg012Sj20Tg00>Fj33Tg008Uj26Tg013aj24TP0j62Tg014Cj35Tg00>`g00;oR0P0f2R1f0R2'7R3f1R4'1R5f3R6/021114,06R6530X00R7P01124R8,01A3026X00P01142R6P71016,60P81424E21015A5124E211431443E2X30W2W1o"). Qed.

Lemma bv_swrap_wrap' : forall n z, bv_swrap n (bv_wrap n z) = bv_swrap n z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01nh11zp;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210P0p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g015Ej20Tg00>`g00;of1f0'0W1W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zsig (x : word) : Z := bv_signed x.

Definition v_addi (x : word) (imm : Z) : word := Z_to_bv 64 (bv_unsigned x + imm).
Definition v_add (x y : word) : word := Z_to_bv 64 (bv_unsigned x + bv_unsigned y).
Definition v_sub (x y : word) : word := Z_to_bv 64 (bv_unsigned x - bv_unsigned y).
Definition v_mul (x y : word) : word := Z_to_bv 64 (bv_unsigned x * bv_unsigned y).
Definition v_andi (x : word) (imm : Z) : word := Z_to_bv 64 (Z.land (bv_unsigned x) (bv_wrap 64 imm)).
Definition v_ori (x : word) (imm : Z) : word := Z_to_bv 64 (Z.lor (bv_unsigned x) (bv_wrap 64 imm)).
Definition v_xori (x : word) (imm : Z) : word := Z_to_bv 64 (Z.lxor (bv_unsigned x) (bv_wrap 64 imm)).
Definition v_and (x y : word) : word := Z_to_bv 64 (Z.land (bv_unsigned x) (bv_unsigned y)).
Definition v_or (x y : word) : word := Z_to_bv 64 (Z.lor (bv_unsigned x) (bv_unsigned y)).
Definition v_xor (x y : word) : word := Z_to_bv 64 (Z.lxor (bv_unsigned x) (bv_unsigned y)).

Definition c_eq (x y : word) : bool := bv_eqb x y.
Definition c_lts (x y : word) : bool := bv_lts x y.
Definition c_ltu (x y : word) : bool := bv_ltu x y.

Definition btgt (pc : word) (imm : Z) : word := v_addi pc imm.

(* [comment removed for export] *)
Definition v_slti (x : word) (imm : Z) : word :=
  if (zsig x <? imm)%Z then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_sltiu (x : word) (imm : Z) : word :=
  if (bv_unsigned x <? bv_wrap 64 imm)%Z then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_slt (x y : word) : word := if c_lts x y then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_sltu (x y : word) : word := if c_ltu x y then Z_to_bv 64 1 else Z_to_bv 64 0.

(* [comment removed for export] *)
Definition v_slli (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftl (bv_unsigned x) sh).
Definition v_srli (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftr (bv_unsigned x) sh).
Definition v_srai (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftr (bv_signed x) sh).

(* [comment removed for export] *)
Definition v_sll (x y : word) : word :=
  Z_to_bv 64 (Z.shiftl (bv_unsigned x) (bv_unsigned y mod 64)).
Definition v_srl (x y : word) : word :=
  Z_to_bv 64 (Z.shiftr (bv_unsigned x) (bv_unsigned y mod 64)).
Definition v_sra (x y : word) : word :=
  Z_to_bv 64 (Z.shiftr (bv_signed x) (bv_unsigned y mod 64)).

(* [comment removed for export] *)
Definition v_lui (imm : Z) : word := Z_to_bv 64 imm.
Definition v_auipc (pc : word) (imm : Z) : word := Z_to_bv 64 (imm + bv_unsigned pc).

(* [comment removed for export] *)
Definition v_addiw (x : word) (imm : Z) : word :=
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned x + imm)).
Definition v_slliw (x : word) (sh : Z) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned x) sh)).
Definition v_srliw (x : word) (sh : Z) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned x)) sh)).
Definition v_sraiw (x : word) (sh : Z) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned x)) sh)).
Definition v_addw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned x + bv_unsigned y)).
Definition v_subw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned x - bv_unsigned y)).
Definition v_sllw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned x) (bv_unsigned y mod 32))).
Definition v_srlw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned x)) (bv_unsigned y mod 32))).
Definition v_sraw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned x)) (bv_unsigned y mod 32))).

(* [comment removed for export] *)
Definition v_mulh (x y : word) : word :=
  Z_to_bv 64 (Z.shiftr (bv_signed x * bv_signed y) 64).
Definition v_mulhsu (x y : word) : word :=
  Z_to_bv 64 (Z.shiftr (bv_signed x * bv_unsigned y) 64).
Definition v_mulhu (x y : word) : word :=
  Z_to_bv 64 (Z.shiftr (bv_unsigned x * bv_unsigned y) 64).
Definition v_mulw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned x * bv_unsigned y)).

(* [comment removed for export] *)
Definition v_div (x y : word) : word :=
  if (bv_unsigned y =? 0)%Z then Z_to_bv 64 (-1)
  else Z_to_bv 64 (Z.quot (zsig x) (zsig y)).
Definition v_rem (x y : word) : word :=
  if (bv_unsigned y =? 0)%Z then x
  else Z_to_bv 64 (Z.rem (zsig x) (zsig y)).
Definition v_divw (x y : word) : word :=
  if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (-1)
  else Z_to_bv 64 (bv_swrap 32 (Z.quot (bv_swrap 32 (bv_unsigned x)) (bv_swrap 32 (bv_unsigned y)))).
Definition v_remw (x y : word) : word :=
  if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (bv_swrap 32 (bv_unsigned x))
  else Z_to_bv 64 (bv_swrap 32 (Z.rem (bv_swrap 32 (bv_unsigned x)) (bv_swrap 32 (bv_unsigned y)))).
Definition v_divuw (x y : word) : word :=
  if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (-1)
  else Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 (bv_unsigned x) / bv_wrap 32 (bv_unsigned y))).
Definition v_remuw (x y : word) : word :=
  if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (bv_swrap 32 (bv_unsigned x))
  else Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 (bv_unsigned x) mod bv_wrap 32 (bv_unsigned y))).

(* [comment removed for export] *)
Definition v_lb (b : byte) : word := Z_to_bv 64 (bv_signed b).
Definition v_lh (v : word) : word := Z_to_bv 64 (bv_swrap 16 (bv_unsigned v)).
Definition v_lw (v : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned v)).

(* [comment removed for export] *)
Definition jalr_tgtZ (x : word) (imm : Z) : Z := Z.land (bv_unsigned x + imm) (-2).
Definition jalr_tgt (x : word) (imm : Z) : word := Z_to_bv 64 (jalr_tgtZ x imm).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition seg_rom (segs : list Segment) : word -> option byte :=
  fun addr => match memory_read segs addr 1 with Some (b :: _) => Some b | _ => None end.

Fixpoint rdn (segs : list Segment) (mem : word -> option byte) (a : word) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' =>
    match (match mem a with Some b => Some b | None => seg_rom segs a end) with
    | Some b => match rdn segs mem (a+1) n' with Some rest => Some (b :: rest) | None => None end
    | None => None
    end
  end.

(* [comment removed for export] *)
Lemma ov_rdn : forall segs (mem : word -> option byte) n a,
  ov_read_bytes segs mem a n = rdn segs mem a n.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "p'0h01oi001oh11ah21bi011bh31nh42IHh51li021lh63memh72n'h84resti034resth94segsi042l0i051xp;1p;4p;3p;2p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g00L4R1j1<Tg005bj14Tg006lj18Tg007Jj1:Tg0178R2j1>Tg017Zj42Tg018_j40Tg00>Fj31Tg008Uj26Tg019Pj25Tg01:2j37Tg00OAj1;Tg00:Tj1?Tg00CWj3CTg01;5j33Tg00iZj39TP0j6=Tg01;Zj2BTg00E5j1ATg01<Oj4@Tg01=0#<g008oR0#4#4#4R3#4#4#4#8R4#:R5%83#:R3#>R6[g01=oR7%<3R8#>R9f4R:f3R;f0R<f1R=C2P:P;P<P=C031^15R>X37P;f2R?P<g00D:C0,69X15P:P<O1R@P6P2P3P2P3P9P2P3P6P<153<RAP2P8P6f7RB%80RC77?P1P3P6P<%;3RD153=n10110200020020101104REPDn10110500021010200n10110500021010100RFP2P8P9f8RGPB%?0g00DY5C4R0934;RHf5RIC2RJA93=<,58RK%;8RLn10110500021010300PLn10110500021010100P2P3P9PFP2P8P9PGPBPHPIC0RBPKPLn10110500021010300RFPLn10110500021010100519P<P9PBP2P8P9P<A93?<,58RBPLn10110500021010300P2P8P9f9RMPGA34:0RNf6ROC0RPPBPLn10110500021010300519X09169FPJP:PHO1E=X23P<O1A7O=CP9P2P8P2P3P9P2P8P6P<PEPDn10110500021010200RHP2P8P9PMPGPNPOC2PKPLn10110500021010300PLn10110500021010100P2P3P9PHP2P8P9PPPKPLn10110500021010300PLn10110500021010100519P<P1P3P2P3P9PEP2P8P9f;R1f:RPA34O0RHPGC2PKPLn10110500021010300PLn10110500021010100P2P3P9PEP2P8P9P1PPPHPGC0PKPLn10110500021010300PLn10110500021010100519P<169LRHP9f=RNf<RJA34G0RGPPC0RFP2P8P9P<A93;<,58RQPLn10110500021010300P2P8P9f>PNA34M0P1C0PQPLn10110500021010300519X09P2P8P9PFPBPLn10110500021010300,69PNPJPGPPC2PMPGO1E=X88X23P=P<O2n10110201020021101102X58P<O1PHn10110001021110200b0n10110001021110101b0P2P3P9P2P3P6P@PAP2P8P6A7I<CPEPDn10110500021010200n10110500021010100P2P8P9POPIA34=0R0P;C2PKPLn10110500021010300PLn10110500021010100P2P3P9P2P3P6P@PA1BI<n10110500021010100P2P8P9POPIP0P;C0PKPLn10110500021010300PLn10110500021010100519ePIP:P<%A?R?C2PIP:P<P?C0519eX15X4>X77P<C@W3W6W9o"). Qed.

(* [comment removed for export] *)
Lemma le_word_1 : forall b : byte, le_bytes_to_word [b] = Z_to_bv 64 (bv_unsigned b).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11bp;1p;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006lj16Tg007Jj14Tg00<Mj25Tg00^Nj27Tg00C1j21Tg00>Fj32Tg008Uj2<Tg01>Nj1;TP0j63Tg00:Tj18Tg01>oj29Tg01?Oj1:Tg00KTj1@Tg00iZj3?Tg01@3j1>Tg01A0j1=Tg008o#0#0#0R0#6R1#4R2g00;oR3g00H2R4%00#0#0#6R5#4R6f1,51R7f0R8'7,151157R732X03P31518R11158=267X031151R3,<61714%;1E3%80R0,94%:0E3%@29?28R8#>,15=263e%=8=263eW1o"). Qed.

Lemma le_word_v : forall bs (v : word),
  bytes_le_to_Z bs = bv_unsigned v -> le_bytes_to_word bs = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02Hvh12bsh21vh31zp;1p;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006lj15Tg007Jj12Tg00L4j16Tg01@3j14Tg00<Mj23Tg00>Fj31Tg00C1j2:Tg01B0j29TP0j68Tg01A0j17Tg008o#0#0#0R0#5#2#6%00#0#0#5R0#2R1g00;oR2f1R3#4f0R4,3031P213031:04f2R5511X321903%45P4E8%75=113eW0W2W1o"). Qed.

Lemma b_extract8_id : forall b : byte, bv_extract 0 8 (Z_to_bv 64 (bv_unsigned b)) = b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h04__x1h11zh21Hh32H0h42Hah57__arithh64__ffh78__varmaph85__with92b1h:2b2h;1nh<2Hbh=6__sat0h>6__sat1h?1bp;1p;3p;2p;4p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1BTg007Jj14Tg00>Fj36Tg00<Mj20Tg00@Uj3VTg00C1j2MTg01Bbj4ITg01CKj1GTg00lRj2?Tg00o0j27Tg01Cij2CTg01D\j1]Tg00F0j21Tg00AYR1j28Tg00:Tj1>Tg00KTj1WTg00L4j1UTg00LTj2TTg00M2j1OTg00MPj1LTg00N^j2KTg00N;j2=Tg00Tij4<Tg00OAj1HTg00Pkj2JTg008Uj2FTg00QMj2ETg00R9j3NTg00RXj4DTg01EEj3ATg00JHj2PTg00;2j2QTg00K0j3RTg00TFj3STP0j6:Tg01F1j1_Tg01FUj2^Tg01GDj4\Tg00ETj2[Tg00Y1j7YTg00UTj7XTg00YUj8ZTg00;oR0f1R2f0R336p=5g00H2R4/[3p=2P2g00Z`R5g00[?R6P6g00[_R7P3g00\?FYp=;f2R8P5P6P6P7P2P3FXp=@f3R9P5P6P6P7P8P2P3GZp=9g008oR5#3R:#3#3R;#BR<#4g00>`R=%43R>%42R?P1%48?62310981092'5R@[10821083'5%49?682[RAf4RB#4?698\@AV823P3n2001000000120000000W:W9W;PA^:?^9>^;=P3P<%3;#3#3R;#BR=g01H6R>P<10<2R?,M=RACIR@P2P010=ARC%G>RD'?,7<10<8RE,53X10P017=?RF1?3D,7</5EX10P0PF17<3RD/5EX101C<2%2?%]<,1?'8P0PE10<9R9,5DX10P1%2E%3;#3#>RD,1E%29119D'8P310<BRB#2R9f5,0<RG/1Dg00];RH#WRI%UHRH1T02RJ%O0RK%L0RLP01K05R5g00]gRM1=0DC<,;LRN%H6R6PLP01=04g00Z9P5C<,;LROP6A@LONC9C91JL7R7P3P8g009TRPg00:4RQ'F1E38=6PQdAN042CDRQb6b7b8X00113DRP%22RR%28RS118D'8[[^00P3f7,0<RTP2P8O3b5W3W2P2P3O2n20010000001210000009A<E17=E%>:R:%>;R;'P114:%2;1Q:;RU,14[[%2:RVg00\_RWAR:;2UW4%2U\W^4VP1P911BD%2G11GU'8P8f6,0<#211TDPIPHPJPKPLPNP6PLPOP6P0P5PM1=0:=S0=C<,;L9@LOC9C9P7PQb6b7b8X00118U,8S\R\P^00P3f9,0<P2P8O3b5W3W2P2P3O2n2001000000121000000b=b>9A=EE:b<1?F4%_FE:PC1^=?E:10<@P=P>P<PAC\E:O4b2W?o"). Qed.

(* [comment removed for export] *)
Lemma b_lb_val : forall b : byte, sext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = v_lb b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01bh12b1h22b2h31nh41zh51Hp;1p;2p;4p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1:Tg007Jj12Tg00<Mj20Tg00C1j26Tg01Bbj49Tg01HTj35Tg01I?j1=Tg00>Fj31Tg00@Uj3<Tg01J1j27Tg00o0j28Tg008Uj2;Tg01FUj2ETP0j64Tg01JYj3DTg01KFj3CTg01L<j1BTg00KTj1?Tg00iZj3>Tg01A0j1@Tg01M7j1ATg008o#3#3#3R0#:R1#2R2%30#3#3#:R0#2R3f0R4,01,60R5P0g01H6R6P1P4C99510f1R7#=R8513X03P2P4A5104=138X02g00>`R3%24R9%27R:g00AYf2R;#2?174g00;oR<f3R=/0;10=731R>[10;710;451<%2=?1;7[R?f4#2?1=;\>A<;74P4n2001000000120000000W2W1W3P?^2:^19^33P4P0A5107R3P8P<1717R9,80R:171;R;,60,0091<4X4<P<P:180;=1<4X4<1;<:1609,001E09E4AD107,00AC107E41003100851<eO4b5P0P6P1P5C9%B4E4%?29>24#@%A4E4W0o"). Qed.

Lemma b_lh_val : forall v : word, sext 64 (bv_extract 0 16 v) = v_lh v.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51vp;1p;3p;2p;4p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1;Tg007Jj12Tg00>Fj35Tg00<Mj20Tg00@Uj3CTg01Bbj49Tg01HTj3>Tg01Mnj1=Tg01J1j28Tg00o0j24j1ITg012Sj27Tg00C1j2<Tg008Uj2HTg01CKj1GTg00lRj2:Tg015Ej2FTg01F1j1BTP0j66Tg01GDj4ATg011Dj8@Tg01FUj2?Tg01JYj3DTg01KFj3ETg00;oR0f1R1f0R235p=1g008o#3#3#3#3R3#3#3#;R4#2g00>`R5%22R6%21R7g00AYf2R8#2?512f3R9/081091'1R:[10811082'1%29?581[R;f4#2?598\:AC812P2n2001000000120000000W2W1W3P;^27^16^35P2P4%;3R3P4g01H6R5P3P1C9R67>4R7%=1R;P01836R:,441048,73R9,<4,04,12X00P01041R<,73R=,44P4P5P3P8C9,83,44/12X00P0P0%I4R8P8P:P=P0\0/H8P0%G5,:<,431732/19X00P0P<1432,73/19X001F3<g00H2,:<%B<E61036P4P5P3P1CAE611:=eG@1<4=,041?4=E6AD346,04AE346E61047104;'1eO4b4W5o"). Qed.

Lemma b_lw_val : forall v : word, sext 64 (bv_extract 0 32 v) = v_lw v.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51vp;1p;3p;2p;4p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1;Tg007Jj12Tg00>Fj35Tg00<Mj20Tg00@Uj3CTg01Bbj49Tg01HTj3>Tg01N`j1=Tg01J1j28Tg00o0j24j1ITg012Sj27Tg00C1j2<Tg008Uj2HTg01CKj1GTg00lRj2:Tg015Ej2FTg01F1j1BTP0j66Tg01GDj4ATg011Dj8@Tg01FUj2?Tg01JYj3DTg01KFj3ETg00;oR0f1R1f0R235p=1g008o#3#3#3#3#3R3#3#;R4#2g00>`R5%22R6%21R7g00AYf2R8#2?512f3R9/081091'1R:[10811082'1%29?581[R;f4#2?598\:AC812P2n2001000000120000000W2W1W3P;^27^16^35P2P4%;3R3P4g01H6R5P3P1C9R67>4R7%=1R;P01836R:,441048,73R9,<4,04,12X00P01041R<,73R=,44P4P5P3P8C9,83,44/12X00P0P0%I4R8P8P:P=P0\0/H8P0%G5,:<,431732/19X00P0P<1432,73/19X001F3<g00H2,:<%B<E61036P4P5P3P1CAE611:=eG@1<4=,041?4=E6AD346,04AE346E61047104;'1eO4b4W5o"). Qed.

Lemma rdn_length : forall segs mem n a bs,
  rdn segs mem a n = Some bs -> length bs = n.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "p'0h01Hh12H0h21Eh32H1h42bsh51oi001oh61ah71eh81li011lh91nh:2H2h;2IHh<1bi021bh=3memh>4segsi034resti041xp;1p;4p;2p;3p;6p;8p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR2p4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R3P0p8P3p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g00L4j1?Tg005bj18Tg006lj1@Tg007Jj1=Tg0178R0j1ATg018_j44Tg019Pj21Tg00>FR3j30TP1j23Tg00KTj1BTg01ORj6<Tg008Uj29TP2j6:j7DTg00E5R2j17Tg01;Zj2ITg00:Tj1HTg00CWj3GTg01;5j36Tg00iZj32Tg00OAj1FTg011Dj8ETg01Ooj2>Tg01<Oj4CTg01=oR1f1R4f0R530p=5g00D:R69015p=;g01=0#?g008oR7#8#8#8R8#8#8#8#@R9#=R:%@8#=R8#AR;[%?8R<%A<R=f5R>f4R?P4f2R@C411<5RA301384f3RB'5[]4^6:RCX91P?PBP4P6C4=0=AP3P=%B8RD,1<RE11<BRF90=4138?RG#;[P511<4RH90=E11<@RI90=EP=P<P0P<P<P5P5PDn10110000021010100X7=PEPFP5E<A0<DBA0<D?P5A0<D>P<PD1385RD#;X8<1916f6R6P5E:b:W3P5O1b3W1P5O1W1n2002100000000101A0=5I138B#;[X5=PHO1P519=IO1b1W0X4<X6:P6P>P4%7BC4=0=AP0P8P;P6P@O11185f7RH/I@n10110400021010200P;P0P8P0P8P=P5P0P<P=f:R;f9RE%H7g00DYR75G9RJ969>PHC4A2845,1<%F<RKn10110400021010300RLPKn10110400021010200=0=F%7H,5GRG]0P511<?90=Lf;RLP;A696Jf8RMC4P=19=5f<RNPLA69HJPEC4=0=5P0P<f>ROf=RPA69EJPLC4=0=5P0P<P=P4A2865,1<PKn1011040002101030011<ERQ50=138;%7P'5RR]0]2P4f?RSPOA69;JPNC4=0=AA2864,1<11<;50=P3P=A28H@,1<R311<PRT90=4138OfA#7'5[P511<LRU90=3A28MB,1<11<NRB50=P=P<P0P<P<P5P5A28;>R3n10110000021010100X7=A28E?R?,1<PTP5E<A0<?PA0<3OP5A28L6=0<SP<A28NHRSfDRL#7R6,5DX8<P<PSA28PMRD,1<=0=AA28OE,38fE#7'5]0X4<11<SRS=0=SP1P1P2P2138MPLP1\1/92fCfB=69JPMPHO3GE138D/56eW0f@R6P4P>FDP6P5E:b:W3P5O1b3W1P5O1W1n2002100000000101A0=5B138P%76'5[X5=PUO1P519=BO1b1W0W2X8<P5O1PPPNA69MJP;C4=0=K11<M90=KP=PKP0P<p-0P5g01PNR0g00\_n10110000021000000X7=RMP7PQP5E:P01>R5b1W0W2n10110000021110100P5P@O2b2b5W0X<8P5O1A0=KIP=PKPMP7PFP5E:P01>G5b1W0n10110000021110200P4O1b5W0X4<X6:X;CX91P5CCX91W=W>o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_nonneg : forall bs, (0 <= bytes_le_to_Z bs)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01Hh11ah21bh32bsh47__arithh54__ffh68__varmaph75__with84__x1h91nh:2H0h;2IHp;1p;2p;4p;3p;8p;5p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj14Tg006lj1UTg007Jj1ETg00L4j1:Tg01@3j12Tg00KTj19Tg00SJj1DTg00M2j1BTg00MPj1ATg00N;j2@Tg00Tij4;Tg00Pkj2TTg008Uj2STg00QMj2RTg00>Fj3OTg00R9j3NTg00RXj4KTg00ETj28Tg00^Nj25Tg00AYR0j27Tg00^kj2CTg00<Mj21Tg00:Tj1FTg01>oj23Tg01Cij2GTg01D\j1HTg00F0j26Tg00LTj2ITg00N^j2JTg00OAj1?Tg00YUj8LTg01Pkj2MTg00XVj4>Tg00iZj3PTg01QRj5QTg00Y1j7=Tg00H2R1f0R2'8p=0f1R3g00Z`R4g00[?R5P5g00[_R6P2g00\?F=p=<g008oR7#4#4#4R8#UR9#ER:#:R;P:%22#0R<X3;g00];R=#9R>%:=R=g00;oR?#D%B?R@%A?RAP?1@?1RBg00Z9RCPBC;'<1TA6RDP2f2REg009TRFg00:4RG'S1R2E=OFGdAN?13CKRGb5b6b71811P2b4%9:#2#0eP01532#0%0ER1%03RF'7RH[%02RI,7F15E3#0[RJf3RK/5E#0\H1C32P2n2001000000120000000X2?X1?PJ^2?^1?P2119KRJ%2E%F8R8'3RH%0JRL%0H1G9K%H9RH,6J,7LP0f4,19RL#016LHf5,19#0P2f6,19#0f7,19/6HP>P=1I?3P@PAP4P5P5P6P?PBPC1J?7C;,<ARA%?5PAGLPDPGb5b6b7X8?PF\I^8?P2f9,19PEO2b4W:W0P3P2O2n2001000000120000000b0P01332#0P1[13E3#0\FRF13KE#0\11M32P2n2001000000120000000X9?X1?PF^9?^1?P2%2KP8PEO3b0C>O3b0AP:E3#2#0eX;<X3;X2:P2DQW3o"). Qed.

Lemma bytes_le_to_Z_bound : forall bs,
  (bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h04__x1h12Hah22H0h37__arithh46__sat0h56__sat1h62H1h74__ffh88__varmaph95__with:4cstrh;4__x2h<3Hk0h=1bh>1xh?1ah@1nhA2bshB1mhC1yhD1HhE2HbhF2HkhG2IHhH6__sat2hI6__sat3hJ1kp%0p&0p;1p;2p;3p;4p;<p;6p;5p;Bp;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g005bj1=Tg006lk10>Tg007Jj1|Tg00L4j1]Tg01@3j16Tg00:Tj1ITP1j27Tg00;2R1j23Tg00F0R2j22Tg00B4R3j1:Tg00dkR4j21Tg01R4j1kTg008Uj2MTg00JHj2@Tg00K0j3?Tg00KTj1`Tg00SJj1xTg00M2j1vTg00MPj1uTg00N;j2ETg00TFj3^Tg00Pkj2qTg00QMj2pTg00>Fj3\Tg00R9j3oTg00RXj4nTg01RRj4[Tg01S=j1mTg01Cij2lTg00<Mj24Tg01D\k10=Tg00AYR5j2BTg00E5R6j1GTg01>oj2ATg00^Nj2DTg00BTj2CTg00ETR7j28Tg01T?j1JTg00g\j2VTg00hEj3XTg00hnj2cTg01Tdk208Tg00iZj3UTg00LTj2bTg00N^j2ZTg00OAk105Tg010aj3aTg00j^j3TTg00^kk203Tg01Pkj2{Tg00XVj4zTg00FLj2FTg00_mj2STg010Dj2OTg01UPl<PTg01V5j4yTg00_Oj4RTg01V\j3wTg00V8j6hTP0j6KTg00eHj2}Tg00m[j3~Tg006Gk100Tg01W?k401Tg00`Jk302Tg00WWj5tTg01QRj5sTg01Wdk404Tg01XGl<NTg01XllBYTg00Tij4dTg00Y1j7eTg00YUj8rTg00UTk70:Tf1R0f0R8#:'1p=>g00H2R9/28p=9g00;oR:P:g01YRP8H04p=j1M:8p=<g01=oR;P:P:P:P3P3f3R<f2R=P0g00D:R>P9P8M<Np>0;P:P:P:P:P:P:P4P8P0P=P4P<f4R?f5R@f6RAf7RBP9f8RCMBYp>09P:P:P:P:P:P:P1P8P0P=P1P<P?P@PAPBPCf9R1MBYp>07P:P:P2P@P2P?P9P9P<P=P0P8M<Pp>061898p=0P:P0g00]gP8Cdp=LP0g00Z`R2g00[?RDPDg00[_REP8g00\?RFFep=HP;P;P:P:P6P3P3P<g01Z6P=P0P8M<Np=iP;P:P:P:P3P3P@P?P<P=P0P8M<Np=gP:P:P:P:P:P:P4P8P0P=P4P<P?P@PAPBPCP1MBYp=fP:P:P7P@P7P?P9P9P<P=P0P8M<Pp>0<1708#:p=WP=P2PDPDPEP:P0g00Z9P8CdPFFep=;P<P2PDPDPEP=P0P8Grp=5g009TRFg00A9R47\8p=QP=P2PDPDPEP0P8K0:p=_g008oR2#=R3#=#=R6$0>RG#|RH#]RIPH%68%I3RJ%I6RK17H8'>'3'2RLXAI%:>RM,1KRN,3JRO#9RP11K9RQ,3JRR#9RSP8X>:RT1208#kXC:X>:1M:9RUPOPRPTPTPT1308#j#<XB:X@:PJPJ%<JPNPQPTPTPT1108#j#<XB:X@:RNPKPK%<KROPMPTPT%:8#<X>;R;PUH0;N909N:07J061@JQ%9JRM%0QPS[[%0JRSg00\_RVA?JQ0UW1%0R\V^1Sg00];RR#`RQ%]RRW%x:RX%v:RY%u:RZ1E:9R[1E:JR\g01H65^:'L'H1qZEREP8P=g00:4R],MF1p8==\F]dAo:90CnR]b7b8b913J9#9P8b3b4b5C[PPe%`HRP#617HP,>K,3J'2e%m0%60#01lG<14G<RP#0&0=G,2P'B17H<RP#GR9#:R^,1KR_14G?%6</AK'D%0_%:PR`%I2Ra'CRb,1KRc#0PT1808#kXC:X>:S00PUP_PcPTPTPTPNPKPKPOP^PbPTPTP;P9Pb1C8aRbX>:R9PPP`%<`CiEgM:fJ0<%JP%0`17H?R`#:RP,1K,@J17H@R^#:Rc,1KR_#017HARU#:Rd,1KRe,3J#9[\M1WHBRf,1KRg=?J0VVX1S13JgRh#0\V^1SP514GBRi#0%=6#=#=#=#=#IR6,2i1Cfa,1K#0P<14G1Rf#0Rif:Rj,4GRk/26Rl1V:>Rm%G>R>#G,V:Rn9X:mg00nDRo'c+08=URQS01PW1b:0RpPYPZ1Z:2R29;Z[Rq&05DRD1E:KRr1E:aRs9a:25T:Rt9;Z[C5PEP]b7b8b9X0:%08Ru1C0a,1K#0[^0:P8f;Rv,WHRwPBO2b3W6W2P0P8O2n2001000000120000000b4b5b:C[P51D08#0%0=Rx%00Ry'BRz[1Byu1D=0#0[R{1D<=#0\z20308P8n2001000000120000000X=:X?:P{^=:^?:P814G@R{%6?/AKRz%0{%0z%J`%0P1@J_%0e%9h[\M17HC,>KRh=?J0VVX1S13JhRP#0\V^1SP514GCRz#012z6PiP?%0kRk14GvR?/26PQPWPpPYPZPqPDPqC5PEP]b7b8b9X0:RzPy\u^0:R{P8f=R|,4GR}P=O2b3W6W2P0P8O2n2001000000120000000b4b5b:P51A08#0Px[1A=0#0\yR~1A<=#0\x1{08P8n2001000000120000000X@:X?:P~^@:^?:P8%6@R~PK%J^%0c1@Je%0g%9P[\M17H1,>KRP=?J0VVX1S13JPRe#0\V^1SP5Pi12f6%61#0P@%0?f<R?,4GR@/26S02PzP{P8%6|PvO2b3W6W2P0P8O2n2001000000120000000b4b5b:O3b2CzO3b2%G`,>K/88PF14GAR`/F0Rv1A~KR{/F0Rz'S%Q8X=FPFP4%6A/AK/F=,S8#QX=FPF1O0KR1,F~Rf1S48#QX=FRiPFP4Pi1MF4PfP_P~P1%G^R1#:R_,1KRf/801Cca,1K/80R4P:P:P7PTP7Q00PfPTP9PcO1RfO1R7,1KPTPTPTPNPKPKPOP_P7PTPTP;P1PfP9P^Pc%<cCiEgM:fP0P0%<0M<PP8CyRcP4%JURU%0dRd1@JgRg%0h%9e[\MRe17Hj,>KRh=?J0VVX1SR^13JhR9#0\V^1SRfP5PkPl%0hR1PA%0@R@12}6R;Q01PWPpPYPZPqPDAT:r2RT9;Z[C5PEP]b7b8b9X0:11K0R7#0\u^0:P8f>R_,WHROPBO2b3W6W2P0P8O2n2001000000120000000b4b5b:b<PcP4PUPdPgPeP^PfP5PkPl%6jRN#012N9'BPAPQPWP:1b:=RNP0PXCRR9PYPZPqPDPZ1Z:3RF,L2,HZRiPDA_ZqiC5C5PEP]b7b8b9X0:X;:120=12=<,Bx[\u^0:^;:P811KO,3J%6_P?P|O4b3X6;X2@P0P8O2n2001000000120000000b4b5b:b<PcP4PUPdPgPeP^PfP5PkPl1OAK,8hPAPQPWP9PYPZA;ZtFPDAw:Fr9;ZTC5PEP]b7b8b9X0:X;:11Kb/801O=K,87[^0:^;:P8PjPOPCO3b3X6;X2@P0P8O2n2001000000120000000b4b5b:b<EhEKPzP~PKP0PcP4PUPdPgPeP^PfP5PkPl%0APA1}:K=~:n1V:>=X:m5X:/co=URQRRPWP:PXP0P:PNP=PXCRCRRNPYPZ&003,Z:R39;Z[RoPDPZAa:3s9T:r=;Z2R3PDPqC5C5PEP]b7b8b9X0:X;:1C=a,1K/80RaPx[\y^0:^;:P8POPjPBPCO4RBb3X6;X2@P0P8O2n2001000000121000000b4b5b:b<H01EKPvPKP`P0PcP4PUPdPgPeP^PfP5PkPl%0KRvPAPQPWPXPYA;Z[rPEP]b7b8b9PvP8b3X6;X2@P0P8O2n2001000000120000000b4b5b:b<PcP4PUPd1@JK13JKR[#9\v\MA?JK0VVX1S%0[\V^1S1@JP11Kw,3J#9\1\M17H?,>KR?=?J0VVX1S13J?#0\V^1SP5P@Q02%0}12}['BPC14G_#0f?,4G/26PQPWPpPYPZ1E:6,L2,HZPDPZPqPDA^:\G,L2,HZ9_ZqC5C5PEP]b7b8b9X0:128612=[,Bx\y[^0:P8fA,4GP0P=O3b3W6W2P0P8O2n2001000000121000000b4b5bHbIb:b<PcP4PUPdPgPeP^PfP5PkPl18KAPAPRPWPNPYPZPoPDPZP3PDA;Zr2C5C5PEP]b7b8b9X0:X;:18K=\a\y^0:^;:PBb3X6;X2@P0P8O2n2001000000121000000b4b5b:b<EhEK1D`{/F0B02`{0EKWFXJ:DtbEbDAUH=0R=#617H=,>K,3J'2eXGLXAIX=HP8DsWAo"). Qed.

Lemma bytes_le_app : forall xs ys,
  bytes_le_to_Z (xs ++ ys) =
  Z.lor (bytes_le_to_Z xs) (Z.shiftl (bytes_le_to_Z ys) (8 * Z.of_nat (length xs))).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11xh24__x1h32xsh42ysh57__arithh64__ffh78__varmaph85__with94cstrh:2IHh;1mh<1nh=1yp;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g005bj1@Tg006lj1pTg007Jj1\Tg00L4j1BTg01ZZj39Tg01@3j14Tg00:Tj1KTP1j27Tg00B4R1j15Tg00dkR2j23Tg01>oj21j1ZTg00^Nj20j1[Tg01[7j1oTg01[Xj1hTg01\<j1dTP0j6FTg00KTj1ETg00<Mj2CTg00E5R0j1<Tg00BTj2:Tg008Uj2;Tg00>Fj1Yj3JTg01R4j1XTg01Wdj4WTg01UPl<RTg01T?j1QTg00ETj2=Tg00LTj2OTg00M2j1PTg00MPj1NTg00N;j2>Tg00N^j2TTg00j^j3MTg010aj3LTg00Tij4?Tg00Pkj2nTg00QMj2mTg00R9j3lTg00RXj4kTg01RRj4gTg011Dj8ITg01\]j3fTg00g\j2GTg00hEj3cTg00hnj2bTg01Tdj2aTg00iZj3HTg00OAj1eTg00YUj8`Tg01]@j4_Tg01]gj3iTg01QRj5^Tg01XGl<DTg01XllBjTg00Y1j7]Tg00;oR3f1R4f0R53Jp=21;35p=8P3f4R6f3R7f2R8P4P5EFp=6g01=oR9P9P3P3P0P1P1P7g01Z6P8P4P5M<Dp=VP9P3P3P3P1P1f5R1P6P7P8P4P5M<Dp=UP3P3P3P3P3P3P2P5P4P8P2P7P6P1f6f7f8f9MBjp=SP4g00Z`R1g00[?R2P2g00[_R0P5g00\?F]p=Ag008oR:#@#@#@R;#pR<#\R=#BR>P=A9=45#4%44R?%45R@%K;R;17=4#5'3'1'0'2^4>RAX3>P3g00H2RB11?5,0B,2?X03P@10B5,2?X03P@12?5X03%8@10B@%o@D611@B%h@D613;B%d;EF%E=RC=9=5#4%4C17=C#5,3;,1@'0'2eX4>%48RC17=8RD#5RE,3;RF,1@RG'0RH1C<6RI115;'0%47/1;RJ,0I17=7#<#5,3;,1?'0R?'2X0311C;RK11G;RL'010I5/2?X031:F;RM,1@RN10J5,0I/2?X031C<7R</0KRI/0N125?X03P3P3%[IRIPIPN%<DR?#5RJ,3;RO,1@P3\3RP/;IP3P3%Z@RIPIPMPO1;PI12MO%K:RI,:ERP,3;RQ,2MP3P3%Y3RRP5X13RSPR1245#XX=3X13PMPM%8MPOPQPSPSPSP3P3g01YR1345CW#8X;3X<3P;P;%8;PJPPPSPS%55#8X19P?PP1:5IRPX13PDPE%8ECVEUM:SM<R%QDRD1=BEREg00];R?#ER9%B?RS1O34RJ%P3RQ%N3ROP31>3;RM1T3:R:5M3RR=L3Mg013:1>3I9L3:9M3MC?'A1nO0RMP5P8g009TRIg00:4RT';1m58=JITdAl3B4CkRTb6b7b8X2313;5/:;13;P'2^23P517=6#5R6O1b5b9CgGIGI10KN,0<Af<KND6PLP@PFP;PDPEg00D:RE,G3RD%<E#<,G39c3Dg00nD'b'a=H?9PSPJPQPOP1P2P2P0P31>3BR0g00Z9R1P:C?,AO%e2P3P0P1PRC?,AOG`PMPTb6b7b8X231=B513;4,=B[^23P5P6P4O2b5b9C_D611H;AiCG;D6A9=85#4P4P5O1D6AH=78R8=9=5#4%4817=8#5,3;,1@'0'2eX4>X:AX3>X1=P5D^W3o"). Qed.

Lemma le2_spec : forall b1 b0, bv_unsigned (le2 b1 b0) = bytes_le_to_Z [b0; b1].
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b0h22b1p;1p;2p;3p;6p;5p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj15Tg006lj18Tg007Jj1<Tg00<Mj23Tg01CKj1DTg01>oj20Tg00^Nj21Tg00KTj1;Tg00iZj34Tg01@3j17Tg00>Fj32Tg00:Tj19Tg01^Kj2:Tg01>Nj1CTP0j66Tg01?Oj1BTg01^mj5@Tg01_Uj2?Tg008Uj2>Tg01`2j6=Tg01`cj2ATg008o#5#5#5R0#8R1#<R2g00;oR3f1R4,31R5%D1R6'0f0R7,31R8'1R9f2R:%;2R;5429424#79237X03P3g00H2R<131:R:/06/15R611:7%90R:'0,15523X03P3P5107:,159236X03105:/:8115<%C5E610<:%B:E6A424;9427#7R;9239e%50#8R0P0P1P1P4P7D@'3P1P0P1P4P7g00>`1?11'>E=E61A47,30=23;eX12W2o"). Qed.

Lemma le4_spec : forall b3 b2 b1 b0,
  bv_unsigned (le4 b3 b2 b1 b0) = bytes_le_to_Z [b0; b1; b2; b3].
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b0h22b1h32b2h42b3p;1p;2p;3p;6p;5p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g005bj15Tg006lj19Tg007Jj1ATg01`cj28Tg00<Mj26Tg01CKj1JTg01>oj24Tg00^Nj23Tg00KTj1?Tg00iZj30Tg01@3j11Tg00:Tj1>TP1j2KTg00B4j1=Tg00dkj2<Tg00E5j1;Tg01^Kj2ITg01ZZj3HTg01aVj2BTP0j67Tg01bPj2:Tg01^mj5@Tg01_Uj2CTg008Uj2DTg01`2j6ETg01cFj4FTg00>Fj3GTg00;oR0f1R1f0R23Gp=2g008o#5#5#5R3#9#AR4P0%53R5#9R6f3R7f2R8'8R9'6R:%J6R;'41812R<,66R='3f4%?4R>5049047R?90489041#1R@,22X00P0A047>9048RA#1RB142;1881,66'3/2@X00P0A041>9042RC#1RD%1?/4;R?/32/2@X00P0%>3R31K4C#='<,4B,3DR@A048>9041#1,3?/22X00g00D:#;#;#=,<3,4B/ID14B;/3D/2@eAH4CA#11BCAE7P=1:12E7P:1:78E7%55#9R5P5P6P6P9P<D@'6P6P5P6P9P<g00>`1C66'DEEE7P7P8P1P2CF,65A041A9042#1'2eX14X24X34W4o"). Qed.

Lemma le8_spec : forall b7 b6 b5 b4 b3 b2 b1 b0,
  bv_unsigned (le8 b7 b6 b5 b4 b3 b2 b1 b0) = bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7].
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b0h22b1h32b2h42b3h52b4h62b5h72b6h82b7p;1p;4p;2p;3p;6p;5p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g005bj12Tg006lj1:Tg007Jj1CTg01cFj49Tg00<Mj26Tg01CKj1KTg01>oj24Tg00^Nj23Tg00KTj1ATg01@3j11Tg00:Tj1?TP1j2LTg00B4j1>Tg00dkj2=Tg00E5j18Tg01^Kj2JTg01ZZj3ITg01aVj2HTP0j67Tg01d9j4;Tg01^mj5BTg01_Uj2DTg008Uj2ETg01`2j6FTg01doj8GTg00iZj3<Tg00>Fj3@Tf4R0f3R1f2R2f1R3f0R43<3<p=0g00;oR5?@34p=5g008o#2#2#2R6#:#CR7P5%26#2R8#:R9f7R:f6R;f5R<P0C9R='6R>%K9R?'4P1P2P3P4C9R@,69RA'3P7P3P7P2P7P1P7P0P7P<P7P;P7P:P7f8%A7RBD0D0RCD0D0#1RD,54X05P5P7P0P7P<P7P;P7P:PBD0D0RE#1RF144?P0P1P2P3C9,69'3/5DX05P5P7P4P7P3P7P2P7P1PBD0D0RG#1RH%1C/4?RC/34/5DX05P5%?6R61L7G#>'=,4F,3HRDP7P3P7P2P7P1P7P0PBD0D0#1,3C/54X05g00D:#8#8#8#8#>,=6,4F/JH14F?/3H/5DeAI7GE#11HGEE7PAP1P2P3P4C;E7P>P:P;P<P0C;E7%28#:R8P8P9P9P=P@DB'6P9P8P9P=P@g00>`1D99'EEFE7P:P;P<P0P1P2P3P4GG,68P7P4P7P3P7P2P7P1PED0D0#1'5eX17X27X37X47X57X67X77W8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ok_mkst_eq : forall (r1 r2 : bvmap 5 word) (p1 p2 : word) (m1 m2 ro : word -> option byte),
  r1 = r2 -> p1 = p2 -> (forall a, m1 a = m2 a) ->
  MachineOk (mkst r1 p1 m1 ro) = MachineOk (mkst r2 p2 m2 ro).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02Hmh11ah22m1h32p1h42r1h52Emh62Hph72Hrh82m2h92p2h:2r2h;2rop;1p;2p;3p;5p;7p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj11Tg006Gj1=Tg006lj14Tg007Jj15TP2j2<Tg0178j1;Tg00>Fj30Tg01ebj59Tg01fdj18Tg01glj53Tg01h^j22Tg008Uj27TP0j7:j66Tg008o#1R0#=#4%10#1R0#1#1#1#4#5R2'<R1%40#5#;R0\2R3f6R4f5R5501f4R69025P5f0R7O1P6P7O1500^12P2P0P5P6P7D9A0356P1f9R6g01ifR8#8R9p,2fxR:P7P6f7R;P5D3,28P:f:R<f8R=P4P5D3,28R>30X41P2P;P:P<P7P;P5D3,28=09>X32P3P5f1R5P7O1P;P7O1500^12P:f;R?P6P5P4D3,28P:P?P6P;P4D3,28509]0X23P4P7O1R8=008^12179>W0P4P7P5F:P=f2E6P<f3E6b5W0W6W7X;3X83W2X92X32X:1W4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_range : forall x : word, (0 <= bv_unsigned x < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01xp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj13Tg007Jj12Tg01Cij21Tg008o#0#0#0#0#0#0#3R0#2f0,10W0o"). Qed.

Lemma u8_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01bp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj13Tg007Jj12Tg01Cij21Tg008o#0#0#0#3R0#2f0,10W0o"). Qed.

Lemma u6_range : forall s : bv 6, (0 <= bv_unsigned s < 64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01sp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g006Gj14Tg005bj13Tg006lj10Tg007Jj11Tg01Cij22Tg008o#4#3#0R0#1f0,20W0o"). Qed.

Lemma u5_range : forall s : bv 5, (0 <= bv_unsigned s < 32)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01sp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj14Tg006Gj13Tg006lj10Tg007Jj11Tg01Cij22Tg008o#4#3#0R0#1f0,20W0o"). Qed.

Lemma wrap64_range : forall z, (0 <= bv_wrap 64 z < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj12Tg01jmj21Tg00;og008o#0#0#0#0#0#0#2f0'1W0o"). Qed.

(* [comment removed for export] *)
Lemma bv_swrap_congr : forall n x y,
  bv_wrap n x = bv_wrap n y -> bv_swrap n x = bv_swrap n y.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11Hh21nh31xh41yp;2p;3p;1p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR1p4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g00o0j20Tg00>Fj32Tg00oVj16Tg00BTj21Tg010DR2j19Tg008Uj23Tg011aj38TP0j65TP1j6:Tg011Dj87Tg012Sj24Tg00>`g00;oR1f2R0f1R3'0f0R4,00521P1P1f3R5%65R6,10'0R7#91136,05R8#9P6P6P1P1\1R9P2P2P7P8P9\1/32P11050R2/16,05f4R9%69R:,10'0R;9214X01R<P11053R=114:,09=21;X01P1P8P<131811=6,05A8536E5P2P4E5P7A8506E:G71316G714501453521eW1X41W3W2o"). Qed.

Lemma bv_swrap_add_swrap_l : forall n x y,
  bv_swrap n (bv_swrap n x + y) = bv_swrap n (x + y).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with71zh81Hh91nh:1xh;1yp;2p;1p;4p;3p;8p;6p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR1p4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g012Sj2OTg00BTj20Tg00KTj1BTg00L4j1>Tg00LTj28Tg00_Oj4MTg00M2j1ETg00MPj1ATg00N^j25Tg005bj1?Tg006Gj1=Tg01V\j36Tg010aj34Tg00Tij4<Tg00Pkj2NTg008Uj2:Tg00QMj2LTg00>Fj39Tg00R9j3DTg00RXj4CTg010Dj22Tg00oVj17Tg00o0j21j1@Tg011Dj8FTg011aj3GTP0j6HTP1j6ITg01k\j4JTg00Y1j7KTf1R1g00Z`g00[?R0P0g00[_R0f0R2g00\?FKp=;g00;oR3?912p=3g00>`f2R41O41/02R51012R6g00];R7#BR8%>7R7P31834P1f3R9,83CMR:%E3R;%A3R<P3g008oR=,53R>%?=,53R?%==,53R=563543g013:R@A63>==43?C<';1N<0R0P2P4g009TRAg00:4RB':1L24=9ABdg00H2=D31CCRBb4b5b6X03X13X231214,021224/01'3^03^13^23P2%79RAP1104ARC,19RDO3b3%74RE,01,14RF122E'012FE/02'3P3121ARF,0DREf4RG/121094,1GRH'3X73P310CFRI,19132HX73P3P3%@9RHPHPI1041P3\3/:HP8P7P:P;P3A43>?A63=?543P@A43>=C<,;<P0PBb4b5b6X03X13X2310211241'01024'3^03^13^23P2P4%7GP9O3b3GF119EAG9CFEH12DA/01P2EIb811451146'3eCJX;3X:3W9o"). Qed.

Lemma bv_swrap_add_swrap_r : forall n x y,
  bv_swrap n (x + bv_swrap n y) = bv_swrap n (x + y).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11nh21xh31yp;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g012Sj20Tg00BTj21Tg00>Fj33Tg008Uj25Tg013aj24TP0j62Tg01lXj36Tg00>`g00;oR0P0f2R1f0R2'0R3f1R4'1R5f3R6/021114,06R6530X00R7P01124R8,01A3026X00P01142R6P71016,50P81424E21015A6124E211431443E2X30W2W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma b_addsext : forall (a : word) {n} (imm : bv n),
  a + sext 64 imm = v_addi a (bv_signed imm).
Proof.
intros. apply bv_eq. unfold v_addi, sext.
rewrite bv_add_unsigned, bv_sign_extend_unsigned, Z_to_bv_unsigned.
apply bv_wrap_add_idemp_r.
Qed.

Lemma b_npc4 : forall p : word, p + Z_to_bv 64 4 = v_addi p 4.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51pp;1p;3p;2p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1@Tg007Jj11Tg00>Fj36Tg00<Mj20Tg00@Uj3=Tg00:Tj1<Tg00C1j27Tg01;5j3;Tg01mZj2:Tg00BTj25Tg00o0j24Tg01nNj3?Tg01FUj29TP0j68Tg01o@j3>Tg00;oR0f1R1f0R236p=2g008o#3#3R3#3#3#3#3#@R4#1g00>`R5%12R6%11R7g00AYf2R8#1?612f3R9/081091'2R:[10811082'2%19?681[R;f4#1?698\:A=812P2n2001000000120000000W2W1W3P;^27^16^35P2P4%<3R3,74R59;41R61:13R7P01041R;1045R:'5,441048R8/53,74,04R9,22X00P01443R<1582,44/29X00P015;3R9,44158<,44/22X00A?4;31749,041949E8P:1943E81046R6A>415E81047,26eO4b4W5o"). Qed.

Lemma alu_addi : forall (a : word) {n} (imm : bv n),
  alu64 ALU_ADD a (sext 64 imm) = v_addi a (bv_signed imm).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah13immh21np;1p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj13Tg007Jj11Tg01onj32Tg008o#0#0#0#0#0#0#3#1g00>`f0R0#1f2f1;20W1W2W0o"). Qed.

Lemma alu_andi : forall (a : word) {n} (imm : bv n),
  alu64 ALU_AND a (sext 64 imm) = v_andi a (bv_signed imm).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11nh21Hh32b1h42b2h51ah63immp;1p;3p;2p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1LTg007Jj12Tg00>Fj35Tg00<Mj20Tg00@Uj3ETg01HTj3@Tg020ej3>Tg01J1j28Tg021Mj2<Tg00Hkj26Tg00o0j24Tg00C1j2;Tg022Aj1KTg00ETj2:Tg00:Tj19Tg00;2j2JTg00F0j2ITg0238j1DTg0242j4BTg01EEj3ATg024lj4?Tg01FUj2CTP0j67Tg01JYj3FTg01KFj3GTg025Hj3HTg025mj3=Tg00;oR0f1R1f0R235p=1g008o#3R3#3#3#3#3#3R4#LR5#2g00>`R6%22R7%21R8g00AYR9f2R:#2?512f3R;/0:10;1'1R<[10:110:2'1%2;?5:1[R=f4R>#2?5;:\<AE:12P2n2001000000120000000W4X37X16P=^48^37^16P2P5g026[A@:51R67>;R718:1R8,<;R=P0105;R<1056'6R?105>R>18;:R@,45'6RA,;5,05RB,12X00P01458R816>2/1BX00P016<8RB,45R>11A2X00P0P>PBP<P8%K;P9g00H2R91452R8':R<%93%94'J,I81451,:9%D2P1n2001000000120000000X00P<^00P2P@O1b2CB9A5BC?1;5B,05R@1C5BE7AF:51,05AG:51E711?@eAH5;6,05A=5;6E71057105='1eO4b2W6W1W5o"). Qed.

Lemma alu_ori : forall (a : word) {n} (imm : bv n),
  alu64 ALU_OR a (sext 64 imm) = v_ori a (bv_signed imm).
Proof.
intros. apply bv_eq. unfold v_ori.
change (alu64 ALU_OR a (sext 64 imm)) with (bv_or a (sext 64 imm)).
rewrite bv_or_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
rewrite Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
apply Z_lor_range; [apply u64_range | apply wrap64_range].
Qed.

Lemma alu_xori : forall (a : word) {n} (imm : bv n),
  alu64 ALU_XOR a (sext 64 imm) = v_xori a (bv_signed imm).
Proof.
intros. apply bv_eq. unfold v_xori.
change (alu64 ALU_XOR a (sext 64 imm)) with (bv_xor a (sext 64 imm)).
rewrite bv_xor_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
rewrite Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
apply Z_lxor_range; [apply u64_range | apply wrap64_range].
Qed.

Lemma alu_slti : forall (a : word) (imm : bv 12),
  alu64 ALU_SLT a (sext 64 imm) = v_slti a (bv_signed imm).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h07__arithh14__ffh28__varmaph35__with41ah53immh61zp;1p;2p;3p;4p;7p;6p;<p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006lj19Tg007Jj18Tg006Gj1=Tg01J1j21Tg02>]j24Tg00:Tj15Tg00C1j26Tg00>Fj33Tg008Uj22Tg01JYj3<Tg02?:R1j2;Tg00ETR2j2:Tg00KTj1PTg00L4j1OTg00SJj1ITg00M2j1HTg00MPj1ETg00N;j27Tg00Tij4CTg00Y1j7BTg00Pkj2ATg00QMj2@Tg00R9j3DTg00RXj4?Tg01RRj4FTg02?Vj4GTP0j6>Tg01HTj3JTg02@Jj3KTg020ej3LTg02A7j2MTg01UPl<NTg00>`g00;oR0P1g01CKP2g02Akf5f4f3f2R2f1R1f0R3M<Np=Qg008oR4#0#0#0#0#0#0R5#9R6#8R7%=4#0#0R8#9R9#8P01193R:g009TR;P71162R</43%54,66R4g00H2R=,66R>n0100000020000P;P71191,4<P4P>n0100000020000537X60P;P71161/4:P4P>n0100000020000R<,27A<963,16P9P6P31;96%58R8%55R5':R?P9P81208P6P51205EQg00];R@#P%O@%I0%H0%E0R@g00Z`g00[?RAPAg00[_RAP01708g00Z91705CCg00\?FB1A@AP3P2g00:4RA,2;1@32=3;AdAD0=1C?b1b2b3P?P3b0CFCGE>P;P7AJ963R99K61P4P>n0100000020000=37<eg02BK?L191M1:537eW5W4o"). Qed.

Lemma alu_sltiu : forall (a : word) {n} (imm : bv n),
  alu64 ALU_SLTU a (sext 64 imm) = v_sltiu a (bv_signed imm).
Proof.
intros. unfold v_sltiu.
change (alu64 ALU_SLTU a (sext 64 imm))
with (if bv_ltu a (sext 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0).
unfold bv_ltu, sext.
rewrite bv_sign_extend_unsigned.
reflexivity.
Qed.

Lemma alu_add : forall a b : word, alu64 ALU_ADD a b = v_add a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11bp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg02EEj21Tg008Uj23Tg008o#0#0#0#0#0#0#4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_sub : forall a b : word, alu64 ALU_SUB a b = v_sub a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11bp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg02F8j21Tg008Uj23Tg008o#0#0#0#0#0#0#4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_slt : forall a b : word, alu64 ALU_SLT a b = v_slt a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11bp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg02Fkj21Tg008Uj23Tg008o#0#0#0#0#0#0#4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_sltu : forall a b : word, alu64 ALU_SLTU a b = v_sltu a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11bp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg02G^j21Tg008Uj23Tg008o#0#0#0#0#0#0#4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_and : forall a b : word, alu64 ALU_AND a b = v_and a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01Hh12b1h22b2h31nh41xh51zh61ah71bp;1p;3p;2p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj12Tg006lj1FTg007Jj13Tg00>Fj31Tg00<Mj20Tg00@Uj3CTg020ej3=Tg02HRj2<Tg00Hkj25Tg00C1j27Tg00o0j2:Tg022Aj14Tg00ETj26Tg00:Tj19Tg00;2j2ETg00F0j2DTg0242j4BTg01EEj3@Tg024lj4>Tg01FUj2?TP0j68Tg025Hj3ATg025mj3;Tg008o#2R0#2#2#2#2#2R1#FR2#3R3g00>`R4f0R5#3R6f1R7#3R8g00AYR9f2R:#3?175g00;oR;f3R</0:10<731R=[10:710:551;%3<?1:7[R>f4#3?1<:\=AC:75P5n2001000000120000000W2W1W3P>^28^16^34P5P2g026[?=:7R41<:7R6P;102:R81027R>'5R=102</58R<,72,0291;5X5;P;1:2=R?A1;<5X5;P;P?P=P8P>%4:P9g00H2R91025R8'6R?%90%91'E,D8169>%45P7n2001000000120000000X43P?^43P5P:O1b0CB9@2=C>172=,021?2=E8AA2:7,02A;2:7E81024102651;eO4b0X73W6o"). Qed.

Lemma alu_or : forall a b : word, alu64 ALU_OR a b = v_or a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02b1h12b2h21nh31zh41Hh51ah61bp;1p;3p;2p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1BTg007Jj12Tg00>Fj31Tg00<Mj20Tg00@Uj3<Tg020ej3;Tg02IEj29Tg00^Nj25Tg00C1j24Tg00o0j28Tg022Aj16Tg028:j4:Tg01EEj3ATg024lj4@Tg01FUj2?TP0j67Tg0293j3=Tg029Wj3>Tg008o#3#3#3#3#3#3#BR0#2R1g00>`R2f0R3#2R4f1R5#2R6g00AYf2R7#2?153g00;oR8f3R9/07109531R:[10751073518%29?175[R;f4#2?197\:A<753P3n2001000000120000000W1W0W2P;^16^04^22P3P0g02:D?;75R21975R4P81007R61005R;'5R:1009/56R9,40,009183X38P8180:R<A1893X38P8P<P:P6P;%67%65C:9A0:C@140:,001?0:E7A=075,00A>075E710021004518eO4b4X61W5o"). Qed.

Lemma alu_xor : forall a b : word, alu64 ALU_XOR a b = v_xor a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02b1h12b2h21nh31zh41Hh51ah61bp;1p;3p;2p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1BTg007Jj12Tg00>Fj31Tg00<Mj20Tg00@Uj3<Tg020ej3;Tg02J7j29Tg00`lj25Tg00C1j24Tg00o0j28Tg022Aj16Tg02;dj4:Tg01EEj3ATg024lj4@Tg01FUj2?TP0j67Tg02<^j3=Tg02=Cj3>Tg008o#3#3#3#3#3#3#BR0#2R1g00>`R2f0R3#2R4f1R5#2R6g00AYf2R7#2?153g00;oR8f3R9/07109531R:[10751073518%29?175[R;f4#2?197\:A<753P3n2001000000120000000W1W0W2P;^16^04^22P3P0g02>1?;75R21975R4P81007R61005R;'5R:1009/56R9,40,009183X38P8180:R<A1893X38P8P<P:P6P;%67%65C:9A0:C@140:,001?0:E7A=075,00A>075E710021004518eO4b4X61W5o"). Qed.

(* [comment removed for export] *)
Lemma shamt6_mask : forall s : bv 6,
  bv_unsigned (bv_and (zext 64 s) (Z_to_bv 64 63)) = bv_unsigned s.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h07__arithh14__ffh28__varmaph35__with41zh52Hah66__sat0h76__sat1h81sp;1p;3p;2p;4p;6p;7p;<p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g006Gj13Tg005bj10Tg006lj1=Tg007Jj1CTg02Jjj3_Tg00<Mj22Tg00:Tj16Tg00C1j2GTg00Hkj29Tg00>Fj34Tg00;2j2>Tg00;Oj2ATg02KUj1@Tg02LKj3^Tg02Lnj1UTg00KTj1TTg00L4j1MTg00SJj1LTg00M2j1KTg00MPj1JTg00N;j25Tg00Pkj2FTg008Uj2:Tg00QMj2ETg00R9j3HTg00RXj4ITg00ETR1j21Tg02MLj3DTP0j68Tg00JHj2BTg00F0j2<Tg00K0j3NTg00TFj3OTg00Tij4?Tg00UTj7PTg00AYj2QTg02Moj3RTg02N[j3STg02?:R0j2]Tg01RRj4[Tg02OHj4VTg025Hj3WTg025mj3XTg00Y1j7YTg01UPl<ZTg00;oR2f1R3g00Z9f0R4C?p=;P3g00Z`R5g00[?R6P6g00[_R7P4g00\?FYp=7g00>`P2P0g01CKP1g02Akf5f4f3f2R1P3P4M<Zp=\g008oR0#3R8#0R9#=R:#CP2%00R0#0#0#0#0#0R;#=R<A_:<4R='2%38#3#3#3#6R8,G<R>,2<R?'9R@12:3RA9424X42RBP212:4RC194?=42AX42P2P819A4=42AX42P2%60R0%69R9'>RA,ACPB%@49^CA%U9,9Cg00];RA#TRB%MARA%L2RD%K2RE%J2RFg00H2RG,52RH1529RI';'71FF7RJP4P1g009TRKg00:4RL':1E41=4KLdAH2G3CIRLb1b2b311G9P4b09DC9E8P?%6;R;,B01<G011G;1>0;R?,<G[[11G0RKg00\_R1AN0;3UW511G?\1^5KPBPAPDPEPFP5P6P6P71528R7,;H,7FP2P7g00]g1520=O2<C?,7FFPPJPLb1b2b311G81<8?'QP4b0b6b79R<8E8AS:<4,2<P:P<P41]:<119;R8P:P91:29P<P;1:2;E\PBPAPDPE152;,;I,7FPJPLb1b2b3P8P4b0C[CVE8A42@CeAW<=>,2<AX<=>E8W8o"). Qed.

Lemma regamt64_mask : forall b : word,
  bv_unsigned (bv_and b (Z_to_bv 64 63)) = (bv_unsigned b mod 64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02Hah17__arithh24__ffh38__varmaph45__with51zh66__sat0h76__sat1h81bp;1p;2p;3p;4p;6p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006lj1UTg007Jj1HTg00<Mj25Tg006Gj12Tg00:Tj13Tg00C1j2JTg00Hkj29Tg00;Oj2<Tg00>Fj37Tg00;2j2=Tg008Uj2>Tg02Lnj1?Tg00KTj1TTg00L4j1STg00SJj1RTg00M2j1MTg00MPj1LTg00N;j24Tg00Tij4;Tg00Pkj2ITg00QMj2GTg00R9j3FTg00RXj4ETg00ETj21Tg02MLj3DTP0j66Tg00JHj2CTg00F0j2:Tg00K0j3KTg00TFj3BTg00UTj7ATg00AYj2NTg02Moj3@Tg025Hj3OTg025mj3PTg00Y1j7QTf1R0g00Z`R1g00[?R2P2g00[_R3f0R4g00\?FQp=8g008oR5#0R6#0#0#0#0#0R7#UR8#Hg00;oR91584R:%25R5#2#2#2#2#3R;,J8R<,58R='91580R>%37R7'<R?9794X59R@P9P;19>4=79?X59P9%36R6%05#3R5'=,<:P@1<:7,>9%?5,9:g00];R@#TR?%S@R@%R9R>%M9RA%L9RBP9g00H2RC,49RDg00Z9RE1495C;'81IB3RFP4f2RGg009TRHg00:4RI'>1G4G=7HIdAF9C0CERIb2b3b411C5P4b19D:5E6P=1C671:C611C71=67R=,:C[[11C6R5g00\_R:AK670UW011C=\:^05P?P@P>PAPBP1P2P2P3P9PDPE149;REC;,8BP9PEg00]g1496=B98C;,8BFAPFPIb2b3b411C;1:;='NP4b1b6b79@8;E6AO84<,58AP84<E6W8o"). Qed.

Lemma alu_slli : forall (a : word) (s : bv 6),
  alu64 ALU_SLL a (zext 64 s) = v_slli a (bv_unsigned s).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj11Tg006lj1;Tg007Jj12Tg006Gj15Tg00>Fj37Tg00<Mj20Tg00@Uj3@Tg02Jjj3:Tg020ej3?Tg02P>j2>Tg00:Tj1=Tg00C1j28Tg025Hj3<Tg01>oj26Tg00o0j24Tg008Uj2ETg02Q2j1DTP0j69Tg01FUj2CTg02Qkj3BTg02RSj3ATg00;oR0f1R1f0R237p=3g008oR3#1#1#1#1#1#1#;R4#2%53R3#1#;R5#2g00>`R6%22R7%21R8g00AYf2R9#2?712f3R:/0910:1'3R;[10911092'3%2:?791[R<f4#2?7:9\;A@912P2n2001000000120000000W2W1W3P<^28^17^36P2P4g02SDA:541R67?9R71051R8,>9R<P01049R;%53#5#5#5#=,84R39<46R6,04R='6,44104:R:1059'6R>,84,04,32X00P016;8R;,44R?A:549=<43,04,6:,44/32X00P0P816:2,44144>'3X001E0?P=%D1E9184;,041C4;E9AB496,04AA496E91047104<'3eO4b4W6W5o"). Qed.

Lemma alu_srli : forall (a : word) (s : bv 6),
  alu64 ALU_SRL a (zext 64 s) = v_srli a (bv_unsigned s).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01sh11zh21Hh32b1h42b2h51nh61ap;1p;3p;2p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj12Tg006lj1:Tg007Jj11Tg006Gj14Tg00>Fj36Tg00<Mj20Tg00@Uj3CTg02Jjj3;Tg020ej3@Tg02T0j2?Tg00:Tj19Tg00C1j27Tg025Hj3>Tg00lRj25Tg00o0j2=Tg022Aj1KTg00ETj2<Tg00F0j2JTg02KUj1ITg02Tdj4HTg01EEj3ETg024lj4BTg02Q2j1DTP0j68Tg01FUj2ATg02U`j3FTg02VHj3GTg00;oR0f1R1f0R236p=3g008oR3#2#2#2#2#2#2R4#:R5#1%43R3#2#:R6#1R7g00>`R8%12R9%11R:g00AYR;f2R<#1?612f3R=/0<10=1'3R>[10<110<2'3%1=?6<1[R?f4#1?6=<\>AC<12P2n2001000000120000000W4W3W5P?^4:^39^58P2P5g02W9A;651R87@<R91061R:,?<R?P0105<R>%43#4#4#4#9,75R39>58R8,05R@'5105=R=106<'5RA,75,05,32X10P015>:RB,=5RCA;65<=>53,05,5=/32X10P0P:15=21=5A'3X10P0PCPBP>P:%K<P;g00H2R;1062R6'<R>%94,J61<;:%I2P1n2001000000120000000X07P>^07P2P<O1b2CH9E5BCBP@%D1E8175B,051A5BE8AF5<8,05AG5<8E81059105?'3eO4b2W0W6o"). Qed.

Lemma alu_srai : forall (a : word) (s : bv 6),
  alu64 ALU_SRA a (zext 64 s) = v_srai a (bv_unsigned s).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj11Tg006lj1<Tg007Jj12Tg006Gj14Tg00>Fj37Tg00<Mj20Tg00@Uj3BTg02Jjj3;Tg020ej3@Tg02Wej2?Tg01J1j2:Tg00:Tj1>Tg00C1j29Tg025Hj3=Tg00lRj26Tg00o0j25Tg008Uj2FTg02Q2j1ETP0j68Tg01FUj2DTg02XYj3CTg02YBj3ATg00;oR0f1R1f0R237p=3g008oR3#1#1#1#1#1#1#<R4#2%43R3#1#<R5#2g00>`R6%22R7%21R8g00AYf2R9#2?712f3R:/0910:1'3R;[10911092'3%2:?791[R<f4#2?7:9\;AB912P2n2001000000120000000W2W1W3P<^28^17^36P2P4g02Z4A;541R67@9R71051R8,?9R<P01:49R;%43#4#4#4#>,94R39=46R6,04R='6,541:4:R:1059'6R>,94,04,32X00P016;8R;,54R?A;549==43,04,6:,54/32X00P0P816:2,54154>'3X001F0?P=%E1E8194;,041D4;E8AC496,04AA496E81047104<'3eO4b4W6W5o"). Qed.

Lemma alu_sll : forall a b : word, alu64 ALU_SLL a b = v_sll a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj12Tg006lj1ETg007Jj11Tg00>Fj37Tg00<Mj20Tg00@Uj3?Tg020ej3>Tg02Z`j2=Tg006Gj15Tg00:Tj1;Tg00C1j28Tg025Hj3:Tg01>oj26Tg00o0j24Tg00;Oj2<Tg008Uj2DTg02[Sj1CTP0j69Tg01FUj2@Tg02Qkj3ATg02RSj3BTg00;oR0f1R1f0R237p=3g008oR3#2#2#2#2#2#2R4#ER5#1R6g00>`R7%12R8%11R9g00AYf2R:#1?712f3R;/0:10;1'3R<[10:110:2'3%1;?7:1[R=f4#1?7;:\<A?:12P2n2001000000120000000W2W1W3P=^29^18^37P2P5g02SD?>:1R71=:1R8P0105:R9%53#5#5#5#5#;,85R39:51R=,05R<'6,45105;R;%;4R4,<9'6R>,85,05,32X00P01051/<4R4,69R9,45R?A:5:3,05,6;,45/32X00P0P416;2,45145>'3X001D0?P<%C1E91859,051@59E9AA5:=,05AB5:=E910571058'3eO4b4X66W5o"). Qed.

Lemma alu_srl : forall a b : word, alu64 ALU_SRL a b = v_srl a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01Hh11zh27__arithh34__ffh48__varmaph55__with64__x1h72b1h82b2h91nh:2H0h;2H1h<2H2h=2H3h>2H4h?2H5h@6__sat0hA1ahB1bhC1qhD1rp;1p;3p;2p;4p;8p;6p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj17Tg006lj1iTg007Jj16Tg00>Fj34Tg00<Mj20Tg00@Uj3UTg020ej3NTg02\Nj2MTg006Gj18Tg00:Tj1?Tg00C1j2<Tg025Hj3BTg00lRj29Tg00;Oj25Tg00o0j2CTg022Aj1YTg00KTj1WTg00L4j1VTg00SJj1TTg00M2j1RTg00MPj1QTg00N;j2ATg00Tij4@Tg00Pkj2LTg008Uj2KTg00QMj2JTg00R9j3HTg00RXj4ITg00F0j23Tg02]Aj3Gj2hTg00AYR1j2:Tg02]hj2FTg02^Yj2OTg00?>j1PTg00cmj2;Tg00dkj2ETg00BTj2STg02_:j2gTg00ETj2DTg02_aj2fTg02`Gj2eTg00LTj2`Tg00N^j2ZTg00OAj1[Tg00YUj8\Tg02Tdj4XTg01EEj3]Tg024lj4^Tg02[Sj1_TP0j6=Tg01FUj2aTg02U`j3bTg02VHj3cTg00Y1j7dTg00;oR0f1R2f0R334p=1P2g00Z`R4g00[?R5P5g00[_R6P3g00\?Fdp=>g00H2R7/D3p=2g008oR8#7#7#7#7#7#7R9#iR:#6R;g00>`R<%63R=%62R>P1f2R?#6?423f3R@/0?10@2'1RA[10?210?3'1%6@?4?2[RBf4RC#6?4@?\AAU?23P3n2001000000120000000W8W7W9PB^8>^7=^9<P3P:g02W9?N?2R<1M?2R=P010:?R>%88#8#8#8#8#?,<:RB9B:2RA,0:RD'910:@RE%?9R9,5>'9RF,<:,0:,13X10P010:2RG/59RH,9>RI,C:RJAB:?B,0:,9E/13X10P0PH19E31C:F'1X10P0PJPIP>PH%Y?g00];RJ#WRF%VJRJ%T0%R0RB%Q0RKP01A07RLg00]g1A09C@'>1LK6RMP3P?g009TRNg00:4RO'K1J3?=4NOdAH072CIROb3b4b51379RNP3b29GG9%2H13H9':1F>9%2>%2910:CRC/59R>#2[[1OE9A4097RE#P1;C9,E9/S>,1C[1hC9f5RC,0:R>/59RH#213H9':\N1g>91397f6,0:R>/59RN,391DN7':[1f>9f7,0:R>/;9=407\E1e>9f8R>,0:R7/59/17\E1;79P0f9,0:/59P0P1%23R11339%22R7P>%2?13@9PFPJ1`02PBPKP4P5P5P6P0PLg00Z91Z08C@,>KRK%[5PKG\PMPOb3b4b5X60P7\1^60P3PCP?O2b2W?W0P2P3O2n2001000000120000000bDbCb>b=b<b;b:b@b0CX9]:IC^PD%_2E=1<:I,0:1a:IE=Ab:?A,0:Ac:?AE=10:<10:='1eO4b0XB;WAo"). Qed.

Lemma alu_sra : forall a b : word, alu64 ALU_SRA a b = v_sra a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj12Tg006lj1FTg007Jj11Tg00>Fj37Tg00<Mj20Tg00@Uj3CTg020ej3@Tg02`mj2>Tg01J1j2;Tg006Gj15Tg00:Tj1:Tg00C1j28Tg025Hj3=Tg00lRj26Tg00o0j24Tg00;Oj2<Tg008Uj2ETg02[Sj1DTP0j69Tg01FUj2BTg02XYj3ATg02YBj3?Tg00;oR0f1R1f0R237p=3g008oR3#2#2#2#2#2#2R4#FR5#1R6g00>`R7%12R8%11R9g00AYf2R:#1?712f3R;/0:10;1'3R<[10:110:2'3%1;?7:1[R=f4#1?7;:\<AC:12P2n2001000000120000000W2W1W3P=^29^18^37P2P5g02Z4?@:1R71>:1R8P01;5:R9%53#5#5#5#5#:,85R39=51R=,05R<'6,451;5;R;105:%:4R4'<'6R>,85,05,32X00P01051/<4R4,69R9,45R?A=5:3,05,6;,45/32X00P0P416;2,45145>'3X001E0?P<%D1E91859,051B59E9AA5:=,05A?5:=E910571058'3eO4b4X66W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma low32_unsigned : forall a : word,
  bv_unsigned (low32 a) = bv_wrap 32 (bv_unsigned a).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11ap;1p;2p;3p;6p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006lj16Tg007Jj1;Tg00<Mj21Tg01CKj1=Tg00lRj25Tg00o0j22Tg00>Fj33Tg008Uj2:Tg01F1j18TP0j64Tg01Bbj47Tg01GDj49Tg02a`j1<Tg008o#0#0#0#0#0R0#0#6R1#;g00;oR2%60R0f0R3,11R4g01H6R5#='5'2f1,11,20R69323X02P2P41203=326X021204R6,:2g00H2,54%84E4P1P5P0P3C7,10P1P5P0P3C9E4%<3,10=326eW1o"). Qed.

Lemma low32_signed : forall a : word,
  bv_signed (low32 a) = bv_swrap 32 (bv_unsigned a).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11ap;1p;2p;3p;6p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006lj17Tg007Jj1;Tg00<Mj23Tg01CKj1>Tg00lRj26Tg012Sj21Tg00>Fj32Tg008Uj2:Tg01F1j19TP0j65Tg01Bbj48Tg01J1j24Tg02bHj4=Tg02a`j1<Tg008o#0#0#0#0#0R0#0#7R1#;g00;oR2%70R0f0R3,31R4g01H6R5#>'6'1f1,31,10R69223X02P2P41103=226X021104R6,:2g00H2,64%94E5P1P5P0P3C8,40P1P5P0P3C=E5%<3,40=226eW1o"). Qed.

(* [comment removed for export] *)
Lemma shamt5_mask : forall s : bv 5,
  bv_unsigned (bv_and (zext 32 s) (Z_to_bv 32 31)) = bv_unsigned s.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h07__arithh14__ffh28__varmaph35__with41zh52Hah66__sat0h76__sat1h81sp;1p;3p;2p;4p;6p;7p;<p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj12Tg006Gj13Tg006lj1=Tg007Jj1CTg02Jjj3_Tg00<Mj21Tg00:Tj16Tg00C1j2GTg00Hkj29Tg00>Fj34Tg00;2j2>Tg00;Oj2ATg02c8j1@Tg02LKj3^Tg02Lnj1UTg00KTj1TTg00L4j1MTg00SJj1LTg00M2j1KTg00MPj1JTg00N;j25Tg00Pkj2FTg008Uj2:Tg00QMj2ETg00R9j3HTg00RXj4ITg00ETR1j20Tg02MLj3DTP0j68Tg00JHj2BTg00F0j2<Tg00K0j3NTg00TFj3OTg00Tij4?Tg00UTj7PTg00AYj2QTg02Moj3RTg02N[j3STg02?:R0j2]Tg01RRj4[Tg02OHj4VTg025Hj3WTg025mj3XTg00Y1j7YTg01UPl<ZTg00;oR2f1R3g00Z9f0R4C?p=;P3g00Z`R5g00[?R6P6g00[_R7P4g00\?FYp=7g00>`P2P0g01CKP1g02Akf5f4f3f2R1P3P4M<Zp=\g008oR0#2R8#3R9#=R:#CP2%28#2#2#2R;#=R<A_:<4R='1%30#3#3#3#6R0,G<R>,1<R?'9R@11:3RA9424X42RBP211:4RC194?=42AX42P2P019A4=42AX42P2%68R8%69R9'>RA,ACPB%@49^CA%U9,9Cg00];RA#TRB%MARA%L2RD%K2RE%J2RFg00H2RG,52RH1529RI';'71FF7RJP4P1g009TRKg00:4RL':1E41=4KLdAH2G3CIRLb1b2b310G9P4b09DC9E8P?%6;R;,B81<G810G;1>8;R?,<G[[10G8RKg00\_R1AN8;3UW510G?\1^5KPBPAPDPEPFP5P6P6P71520R7,;H,7FP2P7g00]g1528=O2<C?,7FFPPJPLb1b2b310G01<0?'QP4b0b6b79R<0E8AS:<4,1<P:P<P41]:<109;R0P:P91:29P<P;1:2;E\PBPAPDPE152;,;I,7FPJPLb1b2b3P0P4b0C[CVE8A42@CeAW<=>,1<AX<=>E8W8o"). Qed.

Lemma regamt32_mask : forall b : word,
  bv_unsigned (bv_and (low32 b) (Z_to_bv 32 31)) = (bv_unsigned b mod 32)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12Hah27__arithh34__ffh48__varmaph55__with66__sat0h76__sat1h81bp;1p;2p;3p;4p;6p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj11Tg006lj1?Tg007Jj1PTg02a`j1ITg00<Mj26Tg006Gj10Tg00:Tj17Tg00C1j2OTg00Hkj29Tg00;Oj23Tg00>Fj34Tg00o0j2DTg00;2j2>Tg00JHj2ETg00F0j2:Tg00K0j3CTg00KTj1WTg00L4j1VTg00SJj1UTg00M2j1TTg00MPj1RTg00N;j2;Tg00TFj3BTg00Pkj2MTg008Uj2@Tg00QMj2LTg00R9j3KTg00RXj4JTg00dkj2ATg02cnj4HTg02dHj6NTg024lj4GTg02e0j1QTP0j65Tg02Lnj1FTg00Tij4=Tg02MLj3STg00UTj7_Tg00AYj2^Tg02Moj3]Tg02ekj1\Tg025Hj3[Tg025mj3YTg00ETj2XTg00Y1j7ZTg00H2R0f0R1'Xp=2g00;oR2f1R3g00]gP1C=p=<P3g00Z`R4g00[?R5P5g00[_R6P1g00\?FZp=8g008oR7#1R8#1#1#1#1R9#1#?R:#PP2%?9R;%I1R<'6R=%07R7#0#0#0#7R>,O;R?,6;R@'916:3RA%79R9'3RB9421X02RCP216:1R:,D;RD191@=42BX02P2P>1D;A/91=42BX02P2%78RA%08R8#7RE'>RF,3DPCP21>A9RC,3:RG131F=42BX02P213:913GFPFPCP:1EAE1:0ARG%2ERB1:0FRH[[%2ARIg00\_RJACAE3UW1%2F\J^1Ig00];RK#WRL%VKRK%U2RM%T2RN%R2RO1;20RP1;2ARQ%?85B2'<'81MO6R8P1f2RRg009TRSg00:4RT'@1L1R=4STdAK203CJRTb3b4b5PHP1b2b6b71EA9RH%291:0CR0[\GRGACA93VJX1IR9%2C\J^1IRIPLPKPMPNAB2Q;RQ,<P,8OP8PTb3b4b5P0P1b2b6b7P21A1F942CX02%17#0#0#7,>ARA1AAF,@2CHENCGPD%Q:E5%FE,9DPLPKPMPNP2PPg00Z9R:1;2EC=,8OP8PTb3b4b5PBP1b29SDEE5P@PHPGP9PIPLPKPMPNPOP4P5P5P6P2PPP:1;2>R2C=,8O1<2Q,8OF_P8PTb3b4b5%2>1:>C'^P1b2b6b79];>E5P=%\1E5A[;<?,6;AY;<?E5W8o"). Qed.

(* [comment removed for export] *)
Lemma sext32_unsigned : forall v : bv 32,
  bv_unsigned (sext 64 v) = bv_wrap 64 (bv_swrap 32 (bv_unsigned v)).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01vh11zp;1p;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006lj15Tg007Jj1<Tg01J1j26Tg00o0j22Tg00<Mj21Tg012Sj24Tg00>Fj33Tg008Uj2;Tg01JYj3:Tg01KFj37TP0j68Tg01HTj39Tg008o#0#0#0#0#0R0#5R1#<g00;oR2%00#5R0f0R3,61'2f1,11,41,209323X121113,41,20R4,;2A:103,10A7103E8A9103,10=324eW0o"). Qed.

Lemma w_addiw : forall (a : word) (imm : bv 12),
  sext 64 (alu32 ALU_ADD (low32 a) (sext 32 imm)) = v_addiw a (bv_signed imm).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah63immp;1p;3p;2p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj15Tg006lj1:Tg007Jj17Tg006Gj1BTg00>Fj38Tg00<Mj20Tg00@Uj3JTg02a`j1<Tg01HTj39Tg02fgj3=Tg01J1j2;Tg02gOj2@Tg012Sj21Tg00o0j22j1OTg00BTj26Tg00C1j2?Tg008Uj2>Tg02hDj3NTg014Cj3MTg02iFj2ITg01JYj3HTg01KFj3ETg02ekj1DTg01;5j3FTg01o@j3GTg011Dj8CTg01FUj2KTg02jBj1LTP0j6ATg00;oR0f1R1f0R238p=3P0f4R3f3R4f2R5P1P2EAp=4g008oR6#5#5#5#5#5R7#5#:R8#7%B6#5#5#:R6#7g00>`R9%72R:%71R;g00AY%75?81210451041'3R<[10511052'3%74?851[R=%73?845\<AJ512P2n2001000000120000000W2W1W3P=^2;^1:^39P2P8%:7R7g02k?R9%<5R:A9671R;3=R=798R<1;61R3,@5R>107=,17R?,281084R@1;65'6,17RA,?8,08,32X001085RB/63,17RC,28%<4A9675R45=9,07,17,28/32X00P0P0%O8R9P9P?PCP0\0/>9107:R9107;R?'6,271172/3AX00127BRD1074,62,27,17/3AX001273R4127@/62,27,17/3AX0016D4R@,17RE132AX00RA16B4,17R2PAPCPA1>0CP2AN7B3D4PEAM7B4D4127@,171I7@D4AH671,07AE671D416D?,27,17/3CeP9%D5D4AF7:;,07AG7:;D4GC1?8C,081K8CD4108<R<%L=D4108>,3<eO4b4W6W5o"). Qed.

Lemma w_slliw : forall (a : word) (s : bv 5),
  sext 64 (alu32 ALU_SLL (low32 a) (zext 32 s)) = v_slliw a (bv_unsigned s).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11sh21Hh32Hah42b1h52b2h61nh77__arithh84__ffh96__sat0h:6__sat1h;8__varmaph<5__with=1ap;1p;3p;2p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj1:Tg006lj1BTg007Jj15Tg006Gj1<Tg00>Fj37Tg00<Mj20Tg00@Uj3XTg02a`j1FTg02Jjj3ETg02fgj3CTg01HTj3JTg02kkj2ITg012Sj24Tg00o0j21j1[Tg01>oj29Tg00C1j2@Tg008Uj2HTg00:Tj1?Tg025Hj3YTg00;2j2=Tg00dkj28Tg00;Oj26Tg00JHj2WTg00F0j2>Tg00ETj2;Tg00K0j3VTg00KTj1UTg00L4j1TTg00SJj1MTg00M2j1LTg00MPj1KTg00N;j2DTg00TFj3NTg00Tij4OTg00Y1j7PTg02l`j6QTg00Pkj2RTg00QMj2STg00R9j3hTg00RXj4gTg02mDj4fTg02e0j1ATg02c8j1eTg02mmj3GTg01k\j4cTg02iFj2bTg02ekj1]Tg02nVj1\Tg02Qkj3^Tg02RSj3_Tg011Dj8`Tg01FUj2aTg02jBj1ZTP0j6dTg00;oR0f1R1f0R237p=2P0f4R3f3R4f2R5P1P2Edp=3g008oR6#:R7#:#:#:#:R8#:#BR9#5%<7#BR:#5R;g00>`R<%52R=%51R>g00AYR?%55?71210451041'2R@[10511052'2%54?751[RA%53?745\@AX512P2n2001000000120000000W5W4W6PA^5>^4=^6<P2P9%B8R<g02SDR=%F5R>AE:<1RA3CR@7J9R310:1RB,I5RC10<@,4<RD,191094RE10:5RF'9RG,4<RH,@9,09,22X001095RI/9BRJ,4<RK,19%F4R4AE:<55C=,0<,4<,19/22X00P0P0%[9R=P=PDPKP0\0/H=10<>R=%<6#<#<#<#?,@<9Y<ARA,0<R6'9,1<14<2/2HX00PB10<4/92,1<,4</2HX0011<IR4192F,1<,4</2HX00194BRD,4<122HX00P<PDPJ%?7R7/=BRH,84RL11<2RM11<G'2X0018IHRG11<E1=7FRF'8,1</2MX00%?8R8,=7RM,6L18EF,1<RN,22X0016IM182F/6M/2NX0016GM16EM/8F/6M/22X00PIPHPM1W78g00H2RH/>71;H81>HM[[1;H7RFg00\_REAV781UW31;HM\E^3Fg00];RF#U%TF%M0%L0%K0RFg00Z`REg00[?RNPNg00[_ROPFPEPNPNPOP01D07=N0<g013:1D0HCOg00\?FPEQ1RFOP2P5g009TROg00:4RF'H1S25=7OFdAh0H1Cgb8b;b<A70MHg01PN[P2b7b9b:Cf11<G%AGD3P4%AID311<L%ALD3PJP?10:2R:,;HR?1>:81;HB%e2P1n2001000000120000000X1;P?^1;P2P5O1b2R29GIBD3PDAG4B2D3Cc11<D,4<1b<DD3P=%]5D3P6%\1D3A^<>A,0<A_<>AD3G`1@9K,091a9KD31093R3%Z@D3109C,23eO4b2W1W=o"). Qed.

Lemma w_srliw : forall (a : word) (s : bv 5),
  sext 64 (alu32 ALU_SRL (low32 a) (zext 32 s)) = v_srliw a (bv_unsigned s).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj14Tg006lj1:Tg007Jj12Tg006Gj15Tg00>Fj39Tg00<Mj20Tg00@Uj3ETg02a`j1=Tg02Jjj3>Tg02fgj3<Tg01HTj3ATg02oOj2@Tg012Sj23Tg00o0j26j1LTg00lRj28Tg00C1j2;Tg008Uj2?Tg00:Tj1KTg025Hj3JTg02ekj1ITP0j67Tg02nVj1DTg02U`j3FTg02VHj3CTg011Dj8GTg01FUj2HTg02jBj1BTg00;oR0f1R1f0R239p=1g008oR3#4R4#4#4#4#4R5#4#:R6#2%54#:R4#2g00>`R7%22R8%21R9g00AYf2R:#2?912f3R;/0:10;1'1R<[10:110:2'1%2;?9:1[R=f4#2?9;:\<AE:12P2n2001000000120000000W2W1W3P=^29^18^37P2P6%:5R5g02W9R7%=:R8A>451R93<R=7A6R<1041R>,@:R?P0105=,35R@,66106;,65104:RA'8,35RB,;6,06,12X00P0106:,65RC/8>,35RD,66%=;R;A>45:5<7,05,35,66/12X00P0P0%L6R7P7P@PDP0\0/?7P01058R7%53#5#5#5#K,;59J59R9,05R3'81352/1BX00P0P>105;/82,35/1BX00P0PC182A,35/1BX001?0DP7%I:E7P3%D1E7AF589,05AC589E7GG1;6D,061H6DE7106<R<%B=E7106?,1<eO4b4W6W5o"). Qed.

Lemma w_sraiw : forall (a : word) (s : bv 5),
  sext 64 (alu32 ALU_SRA (low32 a) (zext 32 s)) = v_sraiw a (bv_unsigned s).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj15Tg006lj1:Tg007Jj14Tg006Gj18Tg00>Fj39Tg00<Mj20Tg00@Uj3JTg02a`j1=Tg02Jjj3?Tg02fgj3<Tg01HTj3BTg030Dj2ATg012Sj21Tg00o0j23j1OTg00lRj27Tg00C1j2;Tg008Uj2@Tg01J1j2>Tg00:Tj1NTg025Hj3MTg02iFj2ITg0319j1HTg02nVj1ETg02XYj3FTg02YBj3GTg011Dj8DTg01FUj2KTg02jBj1LTP0j6CTg00;oR0f1R1f0R239p=2P0f4R3f3R4f2R5P1P2ECp=6g008oR6#5R7#5#5#5#5R8#5#:R9#4%87#:R7#4g00>`R:%42R;%41R<g00AY%45?91210451041'2R=[10511052'2%44?951[R>%43?945\=AJ512P2n2001000000120000000W2W1W3P>^2<^1;^3:P2P9%:8R8g02Z4R:%=5R;A?781R<3<R>7B9R=1071R3,A5R?108>,18R@,391094,181075RA'7,18RB,;9,09,22X001095,18RC/73RD,18RE,39%=4R4A?7855<:,08,18,39/22X00P0P0%O9R:P:P@PEP0\0/@:1>8;R:%86#8#8#8#N,;89M8<R<,08R6'7,381182/2BX00P31>84/72,38,18/2BX00PC172A,38,18/2BX00PE122BX001@0E138D,181I8DD6P:%H5D6P6%E1D6AF8;<,08AG8;<D6GD1;9E,091K9ED6109=R=%L>D6109?,2=eO4b4W6W5o"). Qed.

Lemma w_addw : forall a b : word,
  sext 64 (alu32 ALU_ADD (low32 a) (low32 b)) = v_addw a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj16Tg006lj1>Tg007Jj17Tg00>Fj38Tg00<Mj20Tg00@Uj3ITg02a`j19Tg02fgj3:Tg01HTj3@Tg0323j2?Tg012Sj22Tg00o0j21j1KTg00BTj25Tg00C1j2=Tg008Uj2;Tg02hDj3JTg014Cj3HTg02iFj2ETg02ekj1<Tg01;5j3CTg01o@j3BTg011Dj8DTg01FUj2ATg02jBj1FTP0j6GTg00;oR0f1R1f0R238p=3P0f4R3f3R4f2R5P1P2EGp=4g008o#6#6#6#6#6R6#6#>R7#7R8g00>`R9%72R:%71R;g00AY%75?81210451041'3R<[10511052'3%74?851[R=%73?845\<AI512P2n2001000000120000000W2W1W3P=^2;^1:^39P2P7%>6R6g02k?R9%95R:%91R;3:R=7@7R<1?51R3106=,26R>,171074R?1075R@'5,26RA,=7,07,32X001071RB,5@,26RC,17%94=:9:,06,26,17/32X00P0P0%K7R9P9P>PCP0\0/;9106:R9106;R>'5,161262/3AX00116@R41529,16,26/3AX00116BRD116?/52,16,26/3AX00154DR4,26R?132AX00RA15@D,26R2PAPCPA1;0CP2AJ6@BD4P?AH6@DD41164,261E64D4P>%<1D4P9%<5D4AC6:;,06AB6:;D4GD1=7C,071A7CD4107<R<%F=D41073,3<eO4b4X68W5o"). Qed.

Lemma w_subw : forall a b : word,
  sext 64 (alu32 ALU_SUB (low32 a) (low32 b)) = v_subw a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;4p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj18Tg006lj1ATg007Jj17Tg00>Fj39Tg00<Mj20Tg00@Uj3NTg02a`j1;Tg02fgj3?Tg01HTj3DTg032gj2CTg012Sj26Tg00o0j23j1PTg010Dj25Tg00C1j2@Tg008Uj2=Tg00:Tj1>Tg00;2j2OTg00;Oj24Tg033[j3MTg034Cj3GTg02e0j1:Tg01k\j4FTg02iFj2ETg02ekj1<Tg034kj3HTg035Pj3ITg011Dj8JTg01FUj2KTg02jBj1BTP0j6LTg00;oR0f1R1f0R239p=1P0f4R3f3R4f2R5P1P2ELp=2g008o#8R6#8#8#8#8R7#8#AR8#7R9g00>`R:%72R;%71R<g00AY%75?91210451041'1R=[10511052'1%74?951[R>%73?945\=AN512P2n2001000000120000000W2W1W3P>^2<^1;^3:P2P8%A7R:g036>R;%;5R<%;1R>3?R=7D8R31C51R?10:=,6:R@,381084RA1085RB'5RC,6:RD,@8,08,12X001081RE,5BRF,6:RG,38%;4=?;<,0:,6:,38/12X00P0P0%P8R;P;P@PGP0\0/=;10:<R;10:>R@'5,3:16:2/1DX0013:BR4152;,3:,6:/1DX0013:ERH13:A/52,3:,6:/1DX00154HRI,6:112DX00P:PIPF%>6%>7'OR7,4I13:CR6,12X0014B7RD1524/47/16X0014E7RJ14A7RA/52/47/16X0014F7R615AD/47/12X0015BJ/47RA14C7,12X00R2P6P21=06PAAMBE7D215DJ/47AGBJ7D213:F%:FD2PH%:ED2P4%:BD213:IRB%:ID2CF16:B1E:ID2P@%<1D2P;%<5D2AH:<>,0:AI:<>D2GJ1@8G,081K8GD21083R3%B=D2108?,13eO4b4X69W5o"). Qed.

Lemma w_sllw : forall a b : word,
  sext 64 (alu32 ALU_SLL (low32 a) (low32 b)) = v_sllw a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11Hh27__arithh34__ffh48__varmaph55__with62H0h72H1h82H2h92H3h:2H4h;2H5h<2Hah=6__sat0h>4__x1h?2b1h@2b2hA1nhB1qhC1rhD6__sat1hE6__sat2hF1ahG1bp;1p;3p;2p;4p;6p;8p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj1<Tg006lj1TTg007Jj1;Tg00>Fj3:Tg00<Mj20Tg00@Uj3fTg02a`j1GTg02fgj3KTg01HTj3\Tg036jj2YTg012Sj27Tg00o0j23j1vTg00:Tj1ITg00;Oj22Tg01>oj28Tg00C1j2ETg008Uj2MTg006Gj1?Tg025Hj3dTg00KTj1cTg00L4j1bTg00SJj1_Tg00M2j1^Tg00MPj1]Tg00N;j2CTg00Tij4FTg00Pkj2[Tg00QMj2ZTg00R9j3XTg00RXj4WTg00F0j25Tg02]Aj3Vj2JTg00AYR1j2>Tg00;2j2ATg00dkj29Tg02]hj2UTg00JHj2xTg00K0j3wTg02^Yj2STg00?>j1RTg00cmj2=Tg00BTj2QTg02_:j2LTg00ETj2DTg02_aj2PTg02`Gj2OTg00TFj3uTg02l`j6tTg02mDj4oTg02e0j1HTg00LTj2iTg00N^j2eTg00OAj1gTg00YUj8hTg02mmj3NTg01k\j4jTg02iFj2kTg02ekj1lTg037^j1mTg02Qkj3nTg02RSj3aTg011Dj8`Tg01FUj2pTg02jBj1qTg00Y1j7rTP0j6sTg00;oR0f1R2f0R33:p=1P2g00Z`R4g00[?R5P5g00[_R6P3g00\?Frp=Bg00H2R7/D3p=6A:037p=@P0f4R8f3R9f2R:P2P3Esp=4g008oR;#<R<#<#<#<#<R=#<#TR>#;R?g00>`R@%;3RA%;2RBP1%;:?:23109:1092'1RC[10:210:3'1%;9?::2[RD%;8?:9:\CAf:23P3n2001000000120000000W@W?WAPD^@B^?A^A@P3P>%T=R@g02SDRA%G:RB%G2RD3KRC7\>RE1Y:2RF10@C,7@RG,3>10>9RH10>:RI%I=R='2RJ'8RK,7@RL,E>,0>,13X0010>2RM/2=RN,8IRO,7@RP,3>%G9RQ=KAB,0@,7@,3>/13X00P0P0%v>RAPAPGPPP0\0/MA10@BRA%?;#?#?#?#I,E@9d@DRD,0@RG'8,3@17@3/1LX00PN10@Q/83,3@,7@/1LX0013@IRQ183J,3@,7@/1LX0018QNRQ,7@113LX00P@PQPOg00];RO#cRL%bORO%_0RR%^0RS%]0RTP01C07RUg00]g1C0=CF'B1[T6RVP3P:g009TRWg00:4RX'M1Z3:=:WXdAX072CWRXb3b4b5157=RWP3b29VM=%6N15N='>13@HRN%I<R</AJRM'9RY13@3RZ10>8R812H=R['8,3@'1X0019HMR\13@81A<[R['9,3@/1ZX001A<=RZ,2Y198[,3@R],13X0012HZ193[/2Z/1]X0012\Z128Z/9[/2Z/13X00PHPMPZ1UI=RM%6I%6=RI128=R[#6[[R]1x<=157<157Z\I[%6<RIg00\_R^Aw<=2UW<%6Z\^^<If5RI,0>R^/S=%@=R_#RR`f6,0>Ra1=a=,9=12a=Rb'Q'1[1Ja=f7,0>Rc/2=Rd#615d='>\W1Lc=15=7Rdf8Re,0>Rf/2=Rg,5=1Dg7'>[1Pf=f9,0>Rh/==#@\_1Oh=f:Ri,0>Rj/2=/1j\_1=j=P0f;,0>/2=P0P1%63Rj153=Rk%@ZRZ#RPi%6:Ri159=R9PLPOPRPSPTP4P5P5P6P01C0<=u0@g013:PUCF,BTEtPVPXb3b4b5g01PN\ZP3b2W;W1P2P3O2n2001000000120000000bCbBb:b9b8b7b6b=bDbECo13@\%H\D4PN%HHD413@Y%HYD4PKPMP]1SH=1=8=,9=/Q[,18\`1J8=12^=R8#6158='>\W1L^=15=b1Db7'>\d1Pa=1=c=#@\_1Oc=11gf\_1=f=P012h=P0P1PjPk%62RkPePLPO1i02PSPTP4P5P5P6P0PUg00Z91e0;CF,BTRT%g5PTGhPVPXb3b4b5X>0Pk\j^>0P3PIP:O2b2X;9X1iP2P3O2n2001000000120000000bCbBb:b9b8b7b6b=R39NHJD418NJANNJ3D4b1Cj13@Q,7@1k@QD4PA%l:D4PG%m2D4An@BD,0@Aa@BDD4G`1E>P,0>1p>PD410>ERE%qCD410>F,1EeO4b1XG?WFo"). Qed.

Lemma w_srlw : forall a b : word,
  sext 64 (alu32 ALU_SRL (low32 a) (low32 b)) = v_srlw a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1>Tg007Jj14Tg00>Fj38Tg00<Mj20Tg00@Uj3KTg02a`j1;Tg02fgj3=Tg01HTj3BTg038Yj2ATg012Sj22Tg00o0j27j1LTg00:Tj1@Tg00;Oj2?Tg00lRj26Tg00C1j2:Tg008Uj2<Tg006Gj19Tg025Hj3JTg02ekj1ITP0j65Tg037^j1ETg02U`j3DTg02VHj3CTg011Dj8FTg01FUj2GTg02jBj1HTg00;oR0f1R1f0R238p=1g008oR3#3#3#3#3#3R4#3#>R5#4R6g00>`R7%42R8%41R9g00AYf2R:#4?812f3R;/0:10;1'1R<[10:110:2'1%4;?8:1[R=f4#4?8;:\<AK:12P2n2001000000120000000W2W1W3P=^29^18^37P2P5%>4R7g02W9R8%;:R9%;1R=3=R<7B5R>1A:1R?P0107<,27R@,75105;,77105:RA%@4R4'?RB'6,27RC,:5,05,12X00P0177ARA1051/?4R4'6,27RD,75%;;R;==89,07,27,75/12X00P0P0%L5R8P8P@PDP0\0/<8P01079R8%93#9#9#9#@,:79J7=R=,07R3'61272/1CX00P0P4107;/62,27/1CX00P0PA162B,27/1CX001<0DP8%I:E5P3%E1E5AD79=,07AC79=E5GF1:5D,051G5DE5105>R>%H<E5105?,1>eO4b4X66W5o"). Qed.

Lemma w_sraw : forall a b : word,
  sext 64 (alu32 ALU_SRA (low32 a) (low32 b)) = v_sraw a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj15Tg006lj1=Tg007Jj14Tg00>Fj38Tg00<Mj20Tg00@Uj3NTg02a`j1:Tg02fgj3?Tg01HTj3DTg039Mj2CTg012Sj21Tg00o0j23j1OTg00:Tj1ATg00;Oj2@Tg00lRj27Tg00C1j2;Tg008Uj2>Tg01J1j2<Tg006Gj19Tg025Hj3MTg02iFj2GTg0319j1FTg037^j1ETg02XYj3HTg02YBj3ITg011Dj8JTg01FUj2KTg02jBj1LTP0j6BTg00;oR0f1R1f0R238p=2P0f4R3f3R4f2R5P1P2EBp=6g008oR6#5#5#5#5#5R7#5#=R8#4R9g00>`R:%42R;%41R<g00AY%45?81210451041'2R=[10511052'2%44?851[R>%43?845\=AN512P2n2001000000120000000W2W1W3P>^2<^1;^3:P2P8%=7R:g02Z4R;%:5R<%:1R>3?R=7D8R31C51R?10:=,1:R@,381084,1:1085RA%A7R7'@RB'7,1:RC,;8,08,22X0011:ARA1081/@7R7'7RD,1:RE,38%:4R4=?;<,0:,1:,38/22X00P0P0%O8R;P;P@PEP0\0/>;1<:<R;%96#9#9#9#A,;:9M:>R>,0:R6'7,3:11:2/2CX00P71<:4/72,3:,1:/2CX00PA172B,3:,1:/2CX00PE122CX001>0E13:D,1:1G:DD6P;%F5D6P6%E1D6AH:<>,0:AI:<>D6GJ1;8E,081K8ED61083R3%L=D6108?,23eO4b4X69W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_mul : forall a b : word, mul_div M_MUL a b = v_mul a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11bp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg03:Aj21Tg008Uj23Tg008o#0#0#0#0#0#0#4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_mulh : forall a b : word, mul_div M_MULH a b = v_mulh a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11bp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg03;4j21Tg008Uj23Tg008o#0#0#0#0#0#0#4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_mulhsu : forall a b : word, mul_div M_MULHSU a b = v_mulhsu a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11bp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg03;hj21Tg008Uj23Tg008o#0#0#0#0#0#0#4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_mulhu : forall a b : word, mul_div M_MULHU a b = v_mulhu a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11bp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg03<^j21Tg008Uj23Tg008o#0#0#0#0#0#0#4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_div : forall a b : word, mul_div M_DIV a b = v_div a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11bp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg03=Sj21Tg008Uj23Tg008o#0#0#0#0#0#0#4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_rem : forall a b : word, mul_div M_REM a b = v_rem a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11bp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg03>Fj21Tg008Uj23Tg008o#0#0#0#0#0#0#4#2R0f1f0'1,30X10W0o"). Qed.

Lemma w_mulw : forall a b : word,
  sext 64 (mul_div M_MUL (low32 a) (low32 b)) = v_mulw a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12Hah22b1h32b2h41nh51Hh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__with<1ah=1bp;1p;3p;2p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj19Tg006lj1DTg007Jj17Tg00>Fj38Tg00<Mj20Tg00@Uj3WTg02a`j1;Tg03?9j4?Tg01HTj3JTg03?cj2HTg012Sj26Tg00o0j22j1^Tg00dkj24Tg00C1j2CTg008Uj2=Tg00:Tj1ATg00;2j2XTg00;Oj25Tg00JHj2VTg00F0j2@Tg00ETj2<Tg00K0j3UTg00KTj1TTg00L4j1RTg00SJj1QTg00M2j1NTg00MPj1ITg00N;j2>Tg00TFj3KTg00Tij4GTg00Y1j7LTg02l`j6MTg00Pkj2FTg00QMj2OTg00R9j3PTg00RXj4ETg03@Wj4STg02mDj4bTg02e0j1:Tg01k\j4aTg02iFj2`Tg02ekj1BTg03A@j3_Tg03Aej3]Tg011Dj8\Tg01FUj2[Tg02jBj1ZTP0j6YTg00;oR0f1R1f0R238p=1P0f4R3f3R4f2R5P1P2EYp=3g008o#9R6#9#9#9#9R7#9#DR8#7R9g00>`R:%72R;%71R<g00AY%75?81210451041'1R=[10511052'1%74?851[R>%73?845\=AW512P2n2001000000120000000W3W2W4P>^3<^2;^4:P2P8%D7R:P:g03BSR;%;5R<%;1R>C?R=7J8R31H51R?10:=,6:R@,281084RA1085RB'4RC,6:RD,C8,08,12X001081RE,4BRF,6:RG,28P:P;%;4P<C?,0:,6:,28/12X00P0P0%^8R4P4P@PGP0\0/=410:<R410:>R@'4,2:16:2/1DX0012:BR;1424,2:,6:/1DX0012:ERH12:A/42,2:,6:/1DX0014;HRI,6:112DX00P:PIPF%A6R6%A7R7'XRD,5I12:CRJ,12X0015BDRK142;/5D/1JX0015EDRL15ADRA/42/5D/1JX0015FDRJ14AK/5D/12X0014BL/5DRA15CD,12X00RCPJPC1=0JPAPBPEPD1V67g00H2RA/@61<A71@AD[[1<A6RJg00\_RCAU671UW11<AD\C^1Jg00];RJ#T%RJ%Q0%N0%I0RJg00Z`RCg00[?R7P7g00[_RMPJPCP7P7PMP01>06=K0:g013:1>0ACGg00\?FLEM1FJMP2P5g009TRMg00:4RJ'=1O25=8MJdAP0A1CEb7b:b;A80DAg01PN[P2b6b8b9R2CSD314KL/5DPBPLPDP2CbD312:F%:FD3PH%:ED3P;%:BD312:IRB%:ID3Ca16:B1`:ID3P@%B1D3P4%B5D3A_:<>,0:A]:<>D3G\1C8G,081[8GD31083R3%Z=D3108?,13eO4b5X=9W<o"). Qed.

(* [comment removed for export] *)
Lemma div0_32 : forall b : word,
  (bv_unsigned (low32 b) =? 0)%Z = (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01bh11zp;1p;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006lj13Tg007Jj19Tg00<Mj21Tg00o0j24Tg00?Wj22Tg00>Fj3:Tg008Uj28Tg02a`j17Tg02ekj16TP0j65Tg008o#0#0#0#0#0R0#0#3R1#9g00;oR2%30R0f0R3,11'4R4g009TR5g00H2R6,23f1,11,40/263:X121246,85%73,10%63E5W0o"). Qed.

Lemma w_divw : forall a b : word,
  sext 64 (mul_div M_DIV (low32 a) (low32 b)) = v_divw a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "p'0h01zh11Hh21bi001bh32b1h42b2h51nh61ah72b0i014div0p;1p;2p;3p;8p;6p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj18Tg006lj1BTg007Jj13Tg00<Mj20Tg00o0j26j1LTg00?Wj2=Tg03C?j1KTg00C1j2:Tg02a`j1;Tg03C]j3<Tg01HTj39Tg012Sj21Tg03DDj27Tg00>Fj34Tg00@Uj3MTg008Uj2>Tg01J1j2ATg0319j1?Tg02iFj2JTg03Dbj3GTg011Dj8FTg01FUj2ETg02jBj1DTg03ERj1HTP0j6@Tg03?9j4CTg03FGj2ITg00;oR0f1R1f0R234p=2P0f4R3f3R4f2R5P1P2E@p=5g008oR6#8#8#8#8#8R7#8#BR8#3R9g009TR:%B7R71082'6g00H2R;'=R<P:%37R=P2%K6R6,:7R>%;5R?%;1R@5<7n01101000200009978P:P91081RA,67/=;1:86R61085,17RB117A'7,17,:8n0100000020000549X2:P<P:P:P:P=P2P>%;4R==<7?R<n01101000200009978P:P9P2P61084,17R:/7B,17RA,:8RCn0100000020000549P2g00>`RD%32RE%31RFg00AY%35?41210451041'2RG[10511052'2%34?451[RH%33?445\GAM512P2n2001000000120000000W4W3W5RGPH^4F^3E^5DRDP2P8A978>P61086,>0O4b1PGPDP2P8A978<RDPC107<RG,17R6,681083,17R>/7:,17RE,:8,08,22X00168A%;3=<7=,07,17,68/22X00P0P0%L8R3P3P6PAP0\0/>31A7=R31A7?R6'7RF,67RH1172/2EX00117F122EX00P:1723,17/2EX00PB17>2,17/2EX001>0AP6%?5D5P3%?4D5117H1J7FD5PGAG7=?D5GF108C1E8AD5108D%D<D5O4b1n0110000020001b7%;2R<,07/=;%H2E@P7g03G;P@P<CC99781I12549eX29W6o"). Qed.

Lemma w_remw : forall a b : word,
  sext 64 (mul_div M_REM (low32 a) (low32 b)) = v_remw a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "p'0h01zh11Hh21bi001bh32b1h42b2h51nh61ah72b0i014div0p;1p;2p;3p;8p;6p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj19Tg006lj1ETg007Jj16Tg00<Mj20Tg00o0j22j1KTg00?Wj2=Tg02a`j1;Tg03Ggj3<Tg01HTj3:Tg012Sj21Tg00C1j27Tg03HMj28Tg00>Fj35Tg00@Uj3MTg008Uj2>Tg02iFj2CTg02ekj1LTg01FUj2BTg02jBj1ATg01J1j2@Tg0319j1?Tg03Hjj3ITg011Dj8HTg03ERj1GTP0j6DTg03?9j4FTg03IYj2JTg00;oR0f1R1f0R235p=3P0f4R3f3R4f2R5P1P2EDp=4g008o#9#9#9#9#9R6#9#ER7#6R8g009TR9%E6R61072'2g00H2R:'=R;P9%66R<P2%;5R=%;1R>9<6=n01101000200009:67P9P81071R?,26/=:1075,16R@,77116?,8@,16,77n0100000020000558X29P;P9P9P9P<P2%;4R<A<6<=R;n01101000200009:67P9P8P21074R9,16R?,77RA18?@,16RB,77RCn0100000020000558P2g00>`RD%62RE%61RFg00AY%65?51210451041'3RG[10511052'3%64?551[RH%63?545\GAM512P2n2001000000120000000W4W3W5RGPH^4F^3E^5DRDP2P7A:67<REPA106<RF,16,271073,16RH,77,07,32X00127?RI%;3R3,06,16,27/32X001269RJ1162RK,27127HRL'3X00P?1272/3LX001>0I116J1C69D4PF%L4D4107A1B7?D4107E%A<D4O4b1PGPDP2P7A:67;RDPC106;RG,16RE,2718H?,16RA,77,07,32X00127BA<63<,06,16,27/32X00P0P0%K7R3P3PEPBP0\0/>31@6<R31@6=RE'8RF,26R913KAX00116F132AX00P?1823,16/3AX00P@18H2,16/3AX001>0BPE%?5D4P3%?4D411691C6FD4PGAI6<=D4GH107C1B7BD4107D%A;D4O4b1n0110000020101b7%;2R;,06/=:%G2EDP6g03JMP>P;CF9:671J12558eX28W6o"). Qed.

Lemma w_divuw : forall a b : word,
  sext 64 (mul_div M_DIVU (low32 a) (low32 b)) = v_divuw a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "p'0h01Hh11bi001bh22b1h32b2h41nh51zh61ah72b0i014div0p;1p;2p;3p;6p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj14Tg006lj1>Tg007Jj13Tg00<Mj20Tg00o0j22Tg00?Wj2<Tg03C?j1?Tg00C1j27Tg02a`j16Tg03K9j3:Tg01HTj35Tg00cmj29Tg012Sj28Tg00>Fj31Tg00@Uj3ETg008Uj2=Tg01FUj2DTP0j6;Tg02jBj1CTg03ERj1@Tg03?9j4ATg03K_j2BTg008oR0#4#4#4#4#4R1#4#>R2#3R3g009TR4%>1R1f0R5,02'2g00H2R6'<R7P4%31R8P5%?0R0,71R9f2R:#6R;f1R<#6R=5:1n01101000200009512P4P3102<,21R>/<61720R0102:,21R?/9>,81,72n0100000020000513X14P7P4P4P4P8P5P9f3R8#6R7=:1;R;n01101000200009512P4P3P5P01028,21R4/9?,81R?,72R>n0100000020000513P5g00>`R@%35RA%3<RBg00AY%3:?1<5g00;oRC108:108<31RD[10:<10:551C%38?1:<[REf4RF#3?18:\DAE:<5P5n2001000000120000000W3W2W4R:PE^3B^2A^4@R@P5P2A5129P01020,=CO4b0P:P@P5P2A512;R@P>PC101;,81,22102F,21/94,81,72,0291C5X5CPC122?R4%6F=:17,01,81,22=1C5X5C1=C4102>1D2?E;102@%C;E;O4b0n0110000020001b7%65R;,01/<6%@5E;P1g03LTP=P;CA95121B<5513eX13W6o"). Qed.

Lemma w_remuw : forall a b : word,
  sext 64 (mul_div M_REMU (low32 a) (low32 b)) = v_remuw a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "p'0h01zh11Hh21bi001bh32b1h42b2h51nh61ah72b0i014div0p;1p;2p;3p;6p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj18Tg006lj1BTg007Jj15Tg00<Mj20Tg00o0j21Tg00?Wj2<Tg02a`j1:Tg03M@j3=Tg01HTj39Tg012Sj22Tg00C1j26Tg00;Oj2;Tg00>Fj34Tg00@Uj3HTg008Uj2ATg02iFj2GTg02ekj1FTg01FUj2?Tg02jBj1>Tg03ERj1ETP0j6@Tg03?9j4DTg03Mfj2CTg00;oR0f1R1f0R234p=3P0f4R3f3R4f2R5P1P2E@p=7g008o#8#8#8#8#8R6#8#BR7#5R8g009TR9%B6R61072'1g00H2R:'<R;P9%56R<P2%:5R=%:1R>9=6=n01101000200009967P9P81071,16R?/<:1075R@,26,67116@R@/;?,26,67n0100000020000548X29P;P9P9P9P<P2%:4R<A=6<=R=n01101000200009967P9P8P21074R9,26R;,67R?1169RA/;@,26R@,67RBn0100000020000548P2g00>`RC%52RD%51REg00AY%55?41210451041'3RF[10511052'3%54?451[RG%53?445\FAH512P2n2001000000120000000W4W3W5R5PG^4E^3D^5CRCP2P7A967<RDP?106<RE,26,171073RG,26RF,67,07,32X00117;RH%:3R3,06,26,17/32X00PA1262,17117FRF'3X00P;1172/3FX001A0H126A1G69D7PE%F4D7107?1?7;D7107D%><D7O4b1P5PCP2P7A967=RCPB106=,26,17116G/;A,26,67,07,32X00117@RAA=63<,06,26,17/32X001A0A107B1?7@D7107C%>=D7O4b1n0110000020101b7%:2R=,06/<:%E2E@P6g03N[P>P=CD99671C12548eX28W6o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_swrap_hi : forall n z, n <> 0%N ->
  (bv_half_modulus n <= z)%Z -> (z < bv_modulus n)%Z ->
  bv_swrap n z = (z - bv_modulus n)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h04__x1h14__x2h24__x3h33Hn0h47__arithh54__ffh68__varmaph75__with84cstrh91zh:4__x4h;1Hh<3Hhih=3Hloh>2Hnh?4Hposh@3HtwhA1nhB1xhC1yp;1p;2p;3p;4p;6p;7p;<p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR1p4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g00?>j1<Tg00oVj15Tg00ETj29Tg01D\j14Tg00F0j2;Tg03OGj2gTg00BTj22Tg03P;j1]Tg01CKR2j17Tg00>Fj1Mj3:Tg03Phj2uTg03QIj3tTg008Uj2>Tg03Qfj3RTg01V5j4UTg03ROj1QTg00KTj1dTg00L4j1cTg00LTj2CTg00_Oj4FTg00M2j1_Tg00MPj1^Tg00N^j2=Tg005bj1OTg010aj3ETg006Gj1\Tg01V\j3DTg00:Tj1[Tg00N;j2NTg00j^j3ZTg00Pkj2YTg00QMj2XTg00R9j3WTg00RXj4vTg010Dj20Tg00dkj2LTg00;Oj2JTg00E5j1ATg00g\j2@Tg03C?j1sTg00f1j2rTg03S2j3qTg00hnj2VTg01Tdj2pTg00iZj3STg00SJj1oTg00OAj1jTg02l`j6iTg00UTj7fTg00AYj2hTg02LKj3eTP0j6PTg03S[j3kTP1j6lTg012Sj2mTg01UPl<nTg00Tij4KTg00Y1j7bTg00hEj3aTg00YUj8`Tg00>`R1f0R0g01H6R33:p=Ig00;oR4f1R5;:0p=3g00H2R69:40p=BP1P4f6R7P2f5R2f4R8f3R9f2R:P5P3P6P0M<np=TP4P5g013:P0CKp=?P5g00Z`R3g00[?R;P;g00[_R<P0g00\?Fbp=1Aa450p=8P4P5g00Z9P0CKp=GP4P5g00]gP0CKp=HP9P3P;P;P<P:P5P0G`p=6%I5#<%5:/95%49,;:1g8:%58R=/2=%48R='3%]2%42,;6%I7R>#<%77R?#BR@#<RA%M1RB%M4RC%75%70'3A:1501u503tXC1XB1RDP7P?1>4?1>46R?FT9R>@P8CUPAf7RA#Q%7AR@,96g00];R>#dRE%c>RFP41C4:P51C49RGCFRH%_4RI%^4RJg008oRK,=4RL%OKRM,=4RN5E4RO%\K,=4RP5D4RQ%[KRR,N4=Z4P5E4/?O'11YJ<ROP0P:g009TRSg00:4RT'>1X0:=:STdAW465CvRTb5b6b7X04X14X241205RS/0:RU1LR:'2/3S^04^14^24P0f9RS#4%5Sf8RVO3b4b8b3%57,22RW%47RX'01LRX'2/3WP4%5A,27RW%4ARX'0RY1LRX'2RZ%4VR[,J0%5VR\'010A[R['3X94P41JYXR]100\/3[X94R[P4PYP[%IAR[#<%B@R\#<R^PBPCPDPAP@1>4@P?FT9R[\P2CUR\P^%QVR[%7V,96R?PEPFPHPIAD4QNAD4LP'?,1JPOPTb5b6b7X04X14X2410U5100:'3^04^14^24P0f:RU#4RH%5UR@PSO3b4b8b3P]P\P^P[P?g00D:R?#AR[#A#AR^#A,@4R\%sK,r41@4^R^5q4RK'81@4?R?1@4[R[,8^,8\'8g00nDR\'V'p18[?,8K/V\=S>E5S>PFP4P41C48P:%o4CFP5PGCFPIPJ1N46RI%OM,=4RM'G,1J%j;RGPJPJP3P;P;P<1?MI,1JEiPGPJ1HIP,1JPGPJAE4NN/?P,1JPGPJ1HLP,1JPGPJ1GNL,1JPGPJP3P;P;P<1GIQ,1J1HQP,1JFfC6C6C6C6C6C6POPTb5b6b7X04X14X24X:41969%B8g01PN[1;681288/321;871972127A/0VRT,961;TV'h[[[[[[^04^14^24^:4P0%7UPHP@PSP5P:P8P2P7PAO:b4b8b39eYXEP1JZXAkYRXEPPWP0Elb;b?b@1m89109='3eW<W=W>X94XA1o"). Qed.

Lemma b_lui : forall imm : bv 20,
  sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = v_lui (Z.shiftl (bv_signed imm) 12).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "p'0h04__x1h11Hh22H0h32Hah47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__with:1zh;6__sat2h<6__sat3h=6__sat4h>6__sat5h?6__sat6h@6__sat7hA1xhB2b1hC2b2hD1ni001nhE3HgehF3HlthG2HrhH1ehI3immhJ1ohK1yp%0p&0p;1p;3p;2p;5p;4p;6p;8p;7p;<p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR1p4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g005bj1DTg006Gj1?Tg006lj1@Tg007Jj1GTg00>Fj3;Tg00<Mj20Tg00@Uj3sTg00C1j2TTg01^mj5XTg01HTj3jTg01J1j2VTg00:Tj1<Tg01>oj2ETg03T@k10;Tg012Sj26Tg00o0j2Rj1}Tg008Uj2=Tg01CKR2j1_Tg00^Nj2PTg01Cij2vTg01D\j1`Tg00F0j21Tg00AYR3j2ATg00;2j2FTg00dkj25Tg03U3j2mTg00ETR4j24Tg00IIR5j2kTg00JHj2HTg00K0j3ITg03UXj1WTg00KTj1iTg00L4j1hTg00LTj2gTg00M2j1fTg00MPk10=Tg00N^k20<Tg00N;j2UTg00TFj3KTg00OAk10:Tg03V5j2eTg00Pkk204Tg00QMk203Tg00R9k302Tg00RXk401Tg03VXj3bTg00g\j2MTg00E5j1aTg00hEj3OTg00hnj2NTg01Tdj2yTg00eHj2xTg00m[j3YTg00iZj3LTg00j^j3^Tg010Dj2:Tg01V\j3]Tg00Tij4QTg01Ooj2uTg00?>j1ZTg03WEj5dTg00SJj1tTg02mmj3[Tg01R4j1wTg01RRj4{Tg01>Nj1qTg02Moj3|TP0j6cTg01_Uj2pTg01`2j6~Tg011Dk800Tg01FUj2oTg02jBj1nTg00Y1k705Tg00UTk706Tg00YUk807TP1k608Tg01XGl<lTg01UPm<09Tf0R1#D#Dp=Cg00;oR0f1R6;;1p=3g00H2R7/41p=21171p=BP0P6g00]gP1CQp=JP6g00Z`R8g00[?R9P9g00[_R:P1g00\?K05p=7P0P6g00Z9P1CQp=>f2R;P8P9P9P:P6P1K06p=Sf3R<P8P9P9P:P;P6P1L07p=9P0f4R8P<P;P6P1Ecp=8g00>`R=P;P6g00DYg01H6R>P1J08p=\P=P0P0P0P2P2f5R2P8P<P;P6P1M<lp=rP0P0P4P2P4P8P7P7P<P;P6P1N<09p=zg008oR4#DR?#?#CR@#@RA#G%G1RB%G6RCP3%G;?;6110<;10<6'3RD[10;610;1'3%G<?;;6[RE%G8?;<;\DAs;61P1n2001000000120000000WCWBXD=PE^CC^BB^D=P1%D?RB#D#CRC#DRE#@RD%@CRFPFPA%?4RG#CRH#@RIP61TI7RJDXRK7jDS001VA6%<HRH'ERL$0;S0110FKS02,6FRM,RD1VA;/EHRN,TD,0D,31X:01RDLPFPAPIP;PJDX,0F,6F,RD/31X:0P0P0%}DROPOPMPLP0\0/=O10A6RO%_IRM'ERP10IJS03'P16F1RQ/3NX:0RRP0P710A;RS/EMS04/P1,6F/3NX:0PPPR1vA6%2O%`AS05,1O'A%<?R?/FMRO,5S10A<R<,6A/EH,3QX:016ASRQ1F?HRR'515<O,6F/31X:0%?B#?RB#<RO,F?RN,mS11SN14NS'kP511<N14N<10A8R8/5R,6F16A8/5R'3P1118N10A2R2/5RR<f6,0AR5,6A/5R,31X:0S06P2155RS07151RRT'3X:01=0<16A2S08%<@R@,H?RU%B?RV%2@1F?@RW#B[[RX%2?RYg00\_RZAI?@6UW3R@%2W\Z^3YR[1H?OR\%2O%BN[\VR]AI?O6VZX3YRO%2N\Z^3YR^P3f9S09,0AR_#2S0:11_WS0;%WNR_f:,0AR`'411`N'Af7Raf;Rb,0A#2Rcf<,0A/1WRdg00];Re#iRf%heRg1g06Rh%f0Ri&0=0Rj20<04R41U0?Rk%@B5K0RB'J,7jRl&0:9R9Pj1U07Rm/>4,7jS0<P91e0B/>4,7j=SjlC9C9204j:R:P1P;g009TRng00:4Ro'=2031;=;nodB02076H01Rob5b8b9X00111NS0=%26Rn14_;11;N'A[[^00P1f>,0AR_Q09P;O3b4W2W1P6P1O2n2001000000121000000b6b7b;b<9bA2D816F<S0>1H?HRp%2HRq%BRS0?[\VRrAI?H6VZX3YRs%2R\Z^3YRtPUPXP@P[%?G#?#?RG#<Ru,H?S0@%2u1F?uRv#B[\VS0AAI?u6VZX3YS0B%2v\Z^3YS0CP\P]POP^P3f=S0D,0ARu#2Rw11uWRu%WvRx15_RRy'411yv'APbf?,0A#2Rzf@,0A/1WR{g00D:R|,M0R}%a|S0E#a,M0R|9O0}g00nDR~'N'yS0F%CE#C#C#<,x0S0G=Y0|=O0}/N~=Lef5LePgPhPiPjPlP9PjQ0<P9%@G9K0kRG,e0AK0kIRl9^04R|'>,7j1J|G,7j5SjC9C9P:Pob5b8b9X00Q0=15;RRE,4x11Ev'A\n[^00P1fB,0ARnQ0DP;O3b4W2W1P6P1O2n2001000000121000000b6b7b;b<b=b>b?b@9bF<D8WFP1O114N8%`FRE,:<Q06Q05,:2Q07/:E/3TX:0PpPrPsPt%<CRC,H?S07%2C1F?CRE#B[\VRVAI?C6VZX3YRC%2E\Z^3YRYPUPXP@P[P\P]POP^P3PwPu1:yE1:_W/5R'3PbPfPgPhPiP0AK0kFR?9]0|g013:AK0kARk9]04=^0lCQ,7jP:Pob5b8b9X001:TE1:1W/5R'3^00P1PnO1b4X2{X1zP6P1O2n2001000000121000000b6b7b;b<b=b>b?b@Q08PAP2A;=A>R2P=p-0P1g01PNRTPZn0110000020010000XH=RZ=\A1PT1uT1Rxb2W1%Z2ePUPXP@P[P\P]POP^P3Q0:Q0;14N`PaPfPgPhPiPj1>B4,7jRBP9PBC9P:Pob5b8b9X0014N1R214N6[^00P1P_Q09O2b4X2dX1cP6P1O2n2001000000120000000b6b7b;b<PUPXP@P[P\P]POP^P3Q0:Q0;11`WPaPfPgPhPiPj1J4k,7jRkP9PkC9P:Pob5b8b9X00111WR4116W[^00P1P_P6O2b4X2dX1cP6P1O2n2001000000120000000b6b7b;b<DdD8Q0>PFP<A;=F>R>A\FZ1PTPxb2W1%Z>ePpPrPsPtPUPXP@P[Q0@Q0AQ0BQ0CP\P]POP^P3PwPu14vyPbQ0F=LefPgPhPiPjPBP91>G|,7jC9P:Pob5b8b9X00156RRR,4v\2^00P1PnQ0DO2b4X2{X1zP6P1O2n2001000000121000000b6b7b;b<b=b>b?b@PpPrPsPtQ07PVPCPYPUPXP@P[P\P]POP^P3PwPu11yEPbQ0GQ0E,M05Y0=O0}/N~=LefPgPhPiPjPkP91J|?,7jC9P:Pob5b8b9X0011RE\4^00P1PnP6O2b4X2{X1zP6P1O2n2001000000121000000b6b7b;b<b=b>b?b@DdD8WEP1O1n200100000021100011000bJ1EQHPUPXP@P[P3%28118WPqP;%2510Aa/1WPfPg%t0RWPi1U0H,>m,7jP:Pob5b8b9PqP1b4W2W1P6P1O2n2001000000120000000b6b7Ra9[QHD8Q04%2MPqP1XA0Rq1461#wXK0XA01=07PMPHPqPq%_1,=0XA=PIPH1=0HErEzPaC{9[SMD8bG16FP/3Le1PP7%qPD8Q03PpPrPsPtPfPgPWPi1>mm,7j1Jml,7j5SjP:Pob5b8b91477Q0?'AP1b4b6b79|I7EcQ02PAPFPIP6PJ1pAI,==E~D8L001TDL,0D1oDLD8Q00,0DRL%nKD8Q01,0D,3LeO4b1WIo"). Qed.

Lemma b_auipc : forall (p : word) (imm : bv 20),
  p + sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = v_auipc p (Z.shiftl (bv_signed imm) 12).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh14__x1h24__x2h32b1h42b2h51nh61Hh77__arithh84__ffh98__varmaph:5__with;1bh<3immh=1pp;1p;2p;3p;4p;7p;8p;6p;5p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj11Tg006lj19Tg007Jj15Tg006Gj1ATg01J1j2<Tg00:Tj1VTg01>oj2;Tg03T@j1?Tg01;5j3:Tg03X>j2GTg00>Fj36Tg00<Mj20Tg00@Uj3YTg00C1j28Tg00BTj22Tg00o0j23j1UTg008Uj2BTg00KTj1STg00L4j1RTg00LTj2QTg00SJj1NTg00_Oj4MTg00M2j1LTg00MPj1HTg00N^j2=Tg010aj3>Tg00Tij4ITg00Y1j7JTg00Pkj2KTg00QMj2FTg00R9j3ETg00RXj4OTg011Dj8DTg01nNj3PTP0j67Tg01FUj2@Tg01o@j3CTg01^mj5TTg01HTj3XTg03Y3j1WTg00;oR0f1R1f0R236p=4g008oR3#1R4#1#1#1#1R5#1#9R6#5R7%A4#1#1#9R8#5P71<82%A3#1#1R9#VR:';#?f2R;=:621<81/;:R<,G;R=567X;7g00>`R7%52R>%51R?g00AY%5;?612f3R@/0;10@1'4RA[10;110;2'4%5@?6;1[RBf4#5?6@;\AAY;12P2n2001000000120000000W4W3W5PB^4?^3>^57P2P6%?<9:6;R7P=P0106;R>186<R?,06RB'2,361<8;/;:R:106@R@'2RA,86,06RC,42X00P0136<RD12@2,36/4CX00P012<>RC,36136:,2@,36/42X00P012><RE,36136A,42X00P0P0%U6RAPAPEPCP0\0/BAg00];RA#S%RAP01Q0;P1%N0CM%L0%H0RAg00Z`g00[?REPEg00[_REP01=03R31=04R45>0g013:A>043CIg00\?FJ1KAEP2P;g009TREg00:4RA'B1F2;=6EAdg00H2RA=E01COb8b9b:X10X2012211212'4^10^20P2P:P@O2b7GD12>D,36AP6><E7186C,061@6CE7PB1@6<E7A:6;?,06AC6;?E71067106='4eO4b6%95R5P5P8%99R9P2189ADT7X6%W2E7W<W=o"). Qed.

Lemma Z_land_m2_wrap : forall z,
  Z.land (bv_wrap 64 z) (bv_wrap 64 (-2)) = bv_wrap 64 (Z.land z (-2)).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01bh14__x1h21zh37__arithh44__ffh58__varmaph65__with73Hgeh82Hkh93Hlth:1kh;1op;1p;2p;3p;6p;4p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj17Tg00:Tj1ETg00;2j2PTg00;Oj21Tg006lj1[Tg03C?j1UTg00o0j29Tg00Hkj22Tg00>Fj38Tg00ETj26Tg00FLj20Tg00Shj24Tg03U3j2ZTg00F0j2:Tg00IIR1j2VTg008Uj2DTg00W4j3CTP0j63Tg00KTj1TTg00L4j1STg00LTj2RTg00M2j1OTg00MPj1NTg00N^j2LTg00N;j2ATg00Tij4;Tg00OAj1JTg00Pkj2KTg00QMj2ITg00R9j3HTg00RXj4MTg03Yfj4?Tg03ZQj1GTg00UTj7QTg00AYj2FTg03[1j4=Tg03[]j3YTg03\@j1@Tg00Y1j7XTg00YUj8WTg009TR0f1R2f0R338p=5P2g00Z`R4g00[?R5P5g00[_R6P3g00\?FXp=<f3R7P4P5P5P6f2R8P2P3GWp=BP0g00A9R9P7P8P2P3E3p=>g00;oR:P:g008oR;#7R<#E%7<#7#7#7#7R=#ER>'PR?,13R@%[=R=%U<R<'9RA,23122<,9=RB58:X2:P:11<?RC112?RD/23=8:BX2:P:123<RB/1?RE12DC=8:3X2:12@Cg00H2R@/63P0118?RD/0210C2'4127</1?/08,53X001Z2>1:2>RF16>2RG'VP11:8>16>8f4R1/1?/0710C7'4121</1?/07'5P31:7>P0f5RH/01RI10CH,43f6RJ/2</1?/0HRK'5X00RLP010<1RM10JHRJ/43/5KX00P012H<RN/01RO10<H,4J/53X00RJP014IMRMPJ1D0MPOACH<1E311N?/01ROPNP>P1g00];RM#TRJ%SMRM1R:2RI%O:RP%N:RQP:1L:;R;g00]g1A:>RRC;,<QRS%J5RTPSCB1KQ6RSP3P8g00:4RU,D01I38=80UdAH:@2CMRUb4b5b6X1:1:3>PF[^1:P3PHP2O2RFb3R8C?E310C1RVP<P>P1P8C?E311H?/01R?PHP>P1P8C?E3W9P3O116>7PL1493/5KX001499/53X00%G9POPNP>P1PJPMPIPPPQP:PRg00Z9RPP;C;,<QR;PTPQP4P5P5P6P:1A:@PPPRC;,<QP;FQCBPSPUb4b5b6X1:16>316@>/FG[^1:PFb3RFC=C>PVP<P>P1PFC=C>P?PHP>P1PFC=C>W7P3O1n200100000021100011000b;12DC/02ACDC2E3W8X::7YE19=B%@BE3PA%@<E319=3%@3E3W2o"). Qed.

Lemma b_jalr : forall (a : word) (imm : bv 12),
  bv_and (a + sext 64 imm) (bv_not (Z_to_bv 64 1)) = jalr_tgt a (bv_signed imm).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bh73immp;1p;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj11Tg006lj1?Tg007Jj14Tg006Gj1ATg01J1j2<Tg01mZj2=Tg00:Tj1ITg00C1j28Tg03];j2BTg025Hj3:Tg03]`j2@Tg00>Fj37Tg00<Mj20Tg00@Uj3KTg00BTj2>Tg00Hkj25Tg03C?j1JTg03^Vj19Tg00o0j23Tg03_4j1HTg01FUj2;TP0j66Tg03`0j2DTg025mj3CTg01HTj3ETg01;5j3FTg01onj3GTg00;oR0f1R1f0R237p=2g008oR3#1R4#1#1#1#1#1#?R5#4R6%A3#1#1#?R7#4P61<72,=1%I3R3,85R8,B5R99:52f2R:1<71R;'@R<576X66g00>`R6%42R=%41R>g00AY%4:?712f3R?/0:10?1'2R@[10:110:2'2%4??7:1[RAf4#4?7?:\@AK:12P2n2001000000120000000W2W1W3PA^2>^1=^36P2P51=:;=:59R6P<P0105:/>;R;,85R=,05R>1059RA'5105?1<7:'>R:%J4R4'5,85,05R?,22X00P01058R@#9,35RB185:,05/52/2?X00P0135;152B/2?X00P01353RB135:R:%92,35'5/2?X00P015;4R4,35%9B,35,5:/22X00%H;1854,051;54E6P@1;53E6P>1;5;E6PA1D58E6A:5=9,05AC5=9E61056105<'2eO4b4AE7529F51AG172E6W7W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP1.

Ltac step_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
  rewrite ?bv_eqb0_is_x0.

Section WithFP2.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_opimm_gen : forall segs regs pc mem rom w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                  (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_shiftimm_gen : forall segs regs pc mem rom w op rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
                  (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_op_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_opimm32_gen : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
                  (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_shiftimm32_gen : forall segs regs pc mem rom w op rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
                  (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_op32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                  (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_mul_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_mul32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                  (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_branch_tk_gen : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p'0h02Hch11bi001bh21oh37Hdecodeh46Hecallh56Hfetchh61ci011ch73immh83memh92pch:4regsh;3romh<3rs1h=3rs2h>4segsh?1wi021wi036c_fcsri047c_fregsi054c_pci066c_regsi076c_resvi081ii093iszi0:2m'i0;1pi0<1ri0=6reporti0>3st'i0?1xp%0p;1p;2p;3p;4p;5p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR1p4p710p8P0g002FR0p4p710R2p8g002dR3p4p7210R4P2p8P4g0161R4p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g00L4j1}Tg005bj1<Tg006Gj1MTg006lj1ETg007Jj1?TP3j2{Tg0178R3j1NTg03`^j2UTg019Pj2BTg00>Fj30Tg03a`j1]Tg03b`R2j2\Tg03c@j1QTg04P[j4kTg00:Tj1jTg03d]j4RTg03n1j2iTg01fdR5j1fTP4j1cTg01glj5:Tg03e=j3VTg03fIj1JTg03gGj3aTg03hLj3hTg03iRj3`Tg00KTj1mTg03jWj1_Tg03k_j1^Tg03lgj2STg01J1j2@Tg04QGj2FTg03oWj1HTg040Vj19Tg041Vj1ITg00CWj3[Tg042Wj2lTg043Uj1GTg044Tj1;Tg045Sj1PTg046Qj83Tg00C1j2ZTg047Xj5OTg048Aj3YTg048hj3XTg04:3j2TTg04;7j1|Tg04;`j1zTg04<Jj1yTg00OAj1xTg04=1j1vTg04=Zj1uTg04>Cj2gTg04?Jj1eTg00=Yj3dTg04Alj21Tg007mj1=Tg04D:j1tTP1j6bTg04@Cj1sTg04A8j1rTg04R9j34Tg01HTj3CTg01;5j36Tg01mZj2qTg008Uj2pTg01onj3oTP0j6DTg04E5j1nTg04F2j2wTg04Fnj3KTg01h^j2WTg009TR0f2R1f1R4f0R634g00:4R730p=5g01ifR8?K46,W1p=A1W86p=>g04H5R9f6R:f5R;f4R<f3R=P1P4DOP6CRp=2AK146,T=p=8AK146,g=9K8<,W;p=7P0P7P=P1P4P6EDp=Lg01=0#}g008oR7#<R>#M#ER?%<>R>#<R@#<#<RA#<#ERB#?RC'{RD%E@#?#N\CRE%EA#?RAg04Rh%??S00Q00%M7#<#M#ER7#?%NARFf9RGf7RH'U1BA<30%];g00A9RI500g04IJRJg00;oRK'\RL#NRM%Q:PJPKP;P<P=P1Ck%j>R>CR,BL30f;RN/i;1iN<55:PFf8RO,BA%f8RPP3PA%c8RQ#fRRP6f?RSp,2fxRTf>RUf=RVf<RWPND:;V6RXP3PAPRPTPVPWPNf:RYD:RZ#JR[=aUWPXP3PAPRAhU[WPXP5P8PRA`U[Wg04J6#mRX9AQ6S01%_QR\%^QR]n10110?00031010>0000n10110?00021010200n10110?00021010200n10110?00021010200,S8PTPV1@7;,FWPNPYD:#>R^30X2FP0PIP5PQPPP0PRP6%HZ%9Z%IZ%M@#jg00DYR@5[?,lZ,BC%GZ%;ZP[%PZG3=AQXP3PLPR%QGP2PJPKPRP6P51\9ER[#cS02PRfARI1ZB6S03PTf@RFPSPUPVD:R_#H%9_%I_%;_%G_DO7Y4%J_3XP2P9PEPR1T[6S04%|4S05%z4S06%y4S07%xCR_%v4S08%u4S09P6PTfCR`fBRaPIPFD:#PG31g[1Rb5AQn200110?00012010110:P\P]n10110?00031010=0000n200110;000120108109RcP0PR%eGP\P]n0100000020000Rdn10110?00021110;00n01000000200011T86#>Re%_8Rf%^8Rgn10110<00031010=0000=0P^X10PMPJPKPHP:P;P<CkS0:P>CR,BLP5PQPPP3PLPRP6PcPdn10110?00021110;00PePfPgn10110<00031010=0000=0P^X2MP0g00H2RM=[?@R@9d?:R^P0PCP61ZBMRM11VHRdn0100000020000P0PCP^PM11V:Rcn010000002000055OX10P6%=:Rh%t:RiEbP0PCPhPM11W:n0100000020000P0PCAd?;@PM11W;n010000002000055HP0P^P0PC%=OR^PM11UOn0100000020000P0PCP6PM11UHn010000002000055GX10P6PhPiEbP0PC%=HPMPdn0100000020000P0PCPhPMPcn010000002000055OP^P0P0P0PCP6PM11FYn0100000020000P0PC%=GS0;PM11FGn010000002000055NP5PQPPP2P9PEPRP[P[PEPIPI%sTRcPFP_P_%rTRhPSPUG3Rd#9P0PCP0PCP4PM11INRHn0100000020000P0PC%=YPM11IYRin010000002000054WAC7BG96BF1ZB>R>96BFn0100000020000%;dP_PSF2PXC8PQP9PDP4P<n01101000150106104105103107RdP9PDP4P=n01101000150106104105103107RDP9PCP4P1n01101000150106104105103107R;P_P9%NCP4P6n01101000150106104105103107R@P9PAP4P4n01101000150106104105103107R?P6PFG3P[P[PEP`P`PcPaP_P_PhPIPFG3R:#9RjP0PCP0PCP=PM11`VRkn0100000020000P0PC%=WPM11`WRln010000002000054UAC7BN96BaRmA6Ba>Rnn0100000020000%;:R:P_PIF2PXE7n200110?00012110110:PePfPgn10110<00031010=0000PIPc1@7G,FFP_P_PhPSPUG3#>50P]0P6P0PCP^PM11SOn0100000020000R^95YMQ0;P0P0P0PCP6PM11aNRon0100000020000Rp95VMP5PQPPP2P9PEPRP[P[PEP`PjP0PCP0PCP4PMPln0100000020000Rl94UMPmPnn0100000020000P:P_PIF2PXC8PQPdPDP;P_P@P?P6PaG3RqP[P[PEfERrPrPcfDRsP_P_PhP`PaG3Rt#9RuP0PCP0PCP=PM11rUn0100000020000Rv94FMAC7BV96BsRwA6Bs>Rxn0100000020000%;tRtP_P`F2PXE7n200110?00012110110:PePfPgn10110<00031010=0000P`Pc1@7N,FaP_P_PhPIPFG3#>Ry50P]0P6A5WMMP5PQPPP2P9PEPRP[P[PEP`PjP0PCP6PmPnn0100000020000P:P_PIF2PXC8PQPqP[P[PEPrPuP0PCP1PwPxn0100000020000PtP_P`F2PXE7n200110?00012110110:PePfPgn10110<00031010=0000=0PyX10RzPC1@7YR{,qIP5PQPPP2P9PEPRP[P[PEP`PjP6P:P_PIF2PXC8PQPqP[P[PEPrPuP1PtP_P`F2PXE7n200110?00012110110:PePfPgn10110<00031010=0000=0PyX1CPaPc1FI{P_P_PhPFPSG3#>R{,pPAC7BY96BIR|AoI7YEDP5PQPPP2P9PEPRP[P[PEPaPaPcPIP_P_PhPFPSG3R}#9R~P|%;}R}P_PFF2PXC8PQPdPDP;P_P@P?P6PIG3R?P[P[PEPsPsPcP`P_P_PhPaPIG3Rh#9RcAC7BW96B`R@%;hRhP_PaF2PXE7n200110?00012110110:PePfPgn10110<00031010=0000=0P{eR;A4VMMRDP6CLP5PQPPP2P9PEPRP[P[PEPaP~P0PCPDP|A6BI>RDn0100000020000P}P_PFF2PXC8PQP?P[P[PEPsPcP0PCA4SMMP@A6B`>RBn0100000020000PhP_PaF2PXE7n200110?00012110110:PePfPgn10110<00031010=0000=0P{eW0A5WMiPzP;A4VMoRdP6CLP5PQPPP2P9PEPRP[P[PEPaP~P0PCPdP|PDn0100000020000P}P_PFF2PXC8PQP?P[P[PEPsPcP0PC11sVRd94SMP@PBn0100000020000PhP_PaF2PXE7n200110?00012110110:PePfPgn10110<00031010=0000=0P{eW0n0110001020101P4O1b1W011SG=5Y^Q0;P0P011aWR^=5VpP5PQPPP2P9PEPRP[P[PEP`PjP0PCA4UklPmPnn0100000020000P:P_PIF2PXC8PQPqP[P[PEPrPuP0PC11rS=4FvPwPxn0100000020000PtP_P`F2PXE7n200110?00012110110:PePfPgn10110<00031010=0000=0Py]0P6A5WHMPzP;A4V^MRyP6CLP5PQPPP2P9PEPRP[P[PEPaP~P0PCPyP|PDn0100000020000P}P_PFF2PXC8PQP?P[P[PEPsPcP0PC11sURy=4SMP@PBn0100000020000PhP_PaF2PXE7n200110?00012110110:PePfPgn10110<00031010=0000=0P{eW0A5WHiPzP;A4V^oR^P6CLP5PQPPP2P9PEPRP[P[PEPaP~P0PCP^P|PDn0100000020000P}P_PFF2PXC8PQP?P[P[PEPsPcP0PCA4SydP@PBn0100000020000PhP_PaF2PXE7n200110?00012110110:PePfPgn10110<00031010=0000=0P{eW0n0110001020101P4O1b1W0n0110001020101P4O1b1b0b0P5PQPPP5Q02PRQ0:PTPWPNPYPGD:R{#H%9{%I{%;{%G{DO5Y>%J{R>5XVP2P9PEPRQ04Q05Q06Q07P_Q08Q09P6PTPSPUPVPWD:RX#PG3=AQbn200110?00012010110:P\P]n10110?00031010=0000PePfPgn10110<00031010=0000PTPW1@7<,FNPYPGD:#>RG50Pe%QORYP4EDP5PQPPP3PLPRPYP2PJPKPRP6P5Q02PRQ03%HX%9X%IX%;X%GXDO7Y4%JX5XFP2P9PEPRQ04Q05Q06Q07P_Q08Q09P6PTPaPIPFPSD:#PG3=AQbn200110?00012010110:P\P]n10110?00031010=0000n200110;000120108109P0PR%eOP\P]n0100000020000n10110?00021110;00PePfPgn10110<00031010=0000=0PGe%]OP1EDAVV{O,S8=0PGROePOe1UVNP=EDP3PAPR%n{R=,UVAVUZ6RZP3PAPRAaV>=PZP3PAPRAhV>=PZP5P8PRA`V>=Q01P\P]n10110?00031010>0000n10110?00021010200n10110?00021010200n10110?00021010200,S8=0PGe1wV{=0PGeW0W3W4W5W7W=W<W6W?X;EW8X9CW:W>o"). Qed.

Lemma step_branch_ft_gen : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p'0h02Hch11bi001bh21oh37Hdecodeh46Hecallh56Hfetchh61ci011ch73immh83memh92pch:4regsh;3romh<3rs1h=3rs2h>4segsh?1wi021wi036c_fcsri047c_fregsi054c_pci066c_regsi076c_resvi081ii093iszi0:2m'i0;1pi0<1ri0=6reporti0>3st'i0?1xp%0p;1p;2p;3p;4p;5p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR1p4p710p8P0g002FR0p4p710R2p8g002dR3p4p7210R4P2p8P4g0161R4p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g00L4j1|Tg005bj1<Tg006Gj1JTg006lj1BTg007Jj1ETP3j2zTg0178R3j1NTg03`^j2STg019Pj2ATg00>Fj30Tg03a`j1\Tg03b`R2j2ZTg03c@j1YTg04P[j4jTg00:Tj1iTg03d]j4UTg03n1j2gTg01fdR5j1cTP4j1aTg01glj59Tg03e=j3RTg03fIj1ITg03gGj3hTg03hLj3`Tg03iRj3_Tg00KTj1mTg03jWj1^Tg03k_j1]Tg03lgj2PTg01mZj2?Tg03oWj1GTg040Vj1:Tg041Vj1HTg00CWj3[Tg042Wj2kTg043Uj1FTg044Tj1;Tg045Sj1OTg046Qj84Tg00C1j2XTg047Xj5MTg048Aj3WTg048hj3VTg04:3j2QTg04;7j1{Tg04;`j1yTg04<Jj1xTg00OAj1wTg04=1j1uTg04=Zj1tTg04>Cj2fTg04?Jj1eTg00=Yj3dTg04Alj22Tg007mj1>Tg04D:j1sTP1j6bTg04@Cj1rTg04A8j1qTg04R9j33Tg01HTj3CTg01;5j36Tg008Uj2pTg04CFj1oTP0j6LTg04E5j1nTg04F2j2vTg04Fnj3KTg01h^j2TTg009TR0f0R1g00A9R430p=lf2R6f1R7;31=004p=5g01ifR8?K71,T6p=@1T81p==g04H5R9f6R:f5R;f4R<f3R=P6P7DMP1CUp=1AK671,Q=p=7AK671,f=9K8<,T;p=8P0P4P=P6P7P1ELp=Dg01=0#|g008oR4#<R>#J#BR?%<>R>#<R@#<#<RA#<#BRB#ERC'zRD%B@#E#N\CRE%BA#ERAg04Rh%E?S00Q00%J4#<#J#BR4#E%NARFf9RGf7RH'S1AA<30%\;#lg04IJRIg00;oRJ'ZRK#NRL%Y:PIPJP;P<P=P6Cj%i>R>CU,AK30f;RM/g;1gM<55:PFf8RN,AA%c8ROP3PA%a8RP#cRQP1f?RRp,2fxRSf>RTf=RUf<RVPMD9;R1RWP3PAPQPSPUPVPMf:RXD9RY#IRZ=hTVPWP3PAPQA`TZVPWP5P8PQA_TZVg04J6#mRW9@P1S01%^PR[%]PR\n10110?00031010>0000n10110?00021010200n10110?00021010200n10110?00021010200,P8PSPU1?V>PMPXD9#=R]30X2FP5PPPOP0PQP1%GY%:Y%HY%J@#ig00DYR@5[?,kY,AC%FY%;YPZ%OYG4=@PWP3PKPQ%YGP2PIPJPQP1P51Z9ERZ#aS02PQfARF1XB1S03PSf@R^PRPTPUD9R_#G%:_%H_%;_%F_DM7W7%I_3VP2P9PEPQ1QZ1S04%{7S05%y7S06%x7S07%wCR_%u7S08%t7S09P1PSfCR`fBRaPFP^D9#OG41fZ6Rb5@Pn200110?00012010110:P[P\n10110?00031010=0000n200110;000120108109RcP0PQ%eGP[P\n0100000020000Rdn10110?00021110;00n01000000200011Q81#=Re%^8Rf%]8Rgn10110<00031010=0000=0O]X10PLPIPJPHP:P;P<CjS0:P>CU,AKP5PPPOP3PKPQP1PcPdn10110?00021110;00PePfPgn10110<00031010=0000=0O]X2LP0g00H2RL=[?@R@9d?:R]P0PCP11XBLRL12UHRdn0100000020000P0PCP]PL12U:Rcn010000002000055NX10P1%>:Rh%s:RiEbP0PCPhPL12V:n0100000020000P0PCAd?;@PL12V;n010000002000055HP0P]P0PC%>NR]PL12TNn0100000020000P0PCP1PL12THn010000002000055GX10P1PhPiEbP0PC%>HPLPdn0100000020000P0PCPhPLPcn010000002000055NP]P0P0P0PCP1PL12^Xn0100000020000P0PC%>GS0;PL12^Gn010000002000055MP5PPPOP2P9PEPQPZPZPEPFPF%rSRcP^P_P_%qSRhPRPTG4Rd#:P0PCP0PCP7PL12FMRHn0100000020000P0PC%>XPL12FXRin010000002000053VAC4BG96B^1XB>R;96B^n0100000020000%;dP_PRF1PWC7PPP9PDP7P<n01101000150106104105103107R<P9PDP7P=n01101000150106104105103107RDP9PCP7P6n01101000150106104105103107RdP_P9%NCP7P1n01101000150106104105103107R@P9PAP7P7n01101000150106104105103107R?P1P^G4PZPZPEP`P`PcPaP_P_PhPFP^G4R:#:RjP0PCP0PCP=PL12`URkn0100000020000P0PC%>VPL12`VRln010000002000053TAC4BM96BaRmA6Ba;Rnn0100000020000%;:R:P_PFF1PWE8n200110?00012110110:PePfPgn10110<00031010=0000PFPc1?^>P_P_PhPRPTG4#=50O]0P1P0PCP]PL12RNn0100000020000R]95XLQ0;P0P0P0PCP1PL12aMRon0100000020000Rp95ULP5PPPOP2P9PEPQPZPZPEP`PjP0PCP0PCP7PLPln0100000020000Rl93TLPmPnn0100000020000P:P_PFF1PWC7PPP<PDPdP_P@P?P1PaG4RqPZPZPEfERrPrPcfDRsP_P_PhP`PaG4Rt#:RuP0PCP0PCP=PL12rTn0100000020000Rv93^LAC4BU96BsRwA6Bs;Rxn0100000020000%;tRtP_P`F1PWE8n200110?00012110110:PePfPgn10110<00031010=0000P`Pc1?a>P_P_PhPFP^G4#=Ry50O]0P1A5VLLP5PPPOP2P9PEPQPZPZPEP`PjP0PCP1PmPnn0100000020000P:P_PFF1PWC7PPPqPZPZPEPrPuP0PCP6PwPxn0100000020000PtP_P`F1PWE8n200110?00012110110:PePfPgn10110<00031010=0000=0OyX10RzPC1?F>R{P5PPPOP2P9PEPQPZPZPEP`PjP1P:P_PFF1PWC7PPPqPZPZPEPrPuP6PtP_P`F1PWE8n200110?00012110110:PePfPgn10110<00031010=0000=0OyX1CPaPcP{P_P_PhP^PRG4#=R{,pOA6BF;R|%oFELP5PPPOP2P9PEPQPZPZPEPaPaPcPFP_P_PhP^PRG4R}#:R~P|%;}R}P_P^F1PWC7PPP<PDPdP_P@P?P1PFG4R?PZPZPEPsPsPcP`P_P_PhPaPFG4Rh#:RcA6B`;R@%;hRhP_PaF1PWE8n200110?00012110110:PePfPgn10110<00031010=0000=0O{eRdA3ULLRDP1CDP5PPPOP2P9PEPQPZPZPEPaP~P0PCPDAC4BX96BFRDP|n0100000020000P}P_P^F1PWC7PPP?PZPZPEPsPcP0PCA3RLLAC4BV96B`RBP@n0100000020000PhP_PaF1PWE8n200110?00012110110:PePfPgn10110<00031010=0000=0O{eW0A5VLiPzPdA3ULoR4P1CDP5PPPOP2P9PEPQPZPZPEPaP~P0PCP4PDP|n0100000020000P}P_P^F1PWC7PPP?PZPZPEPsPcP0PC12sUR493RLPBP@n0100000020000PhP_PaF1PWE8n200110?00012110110:PePfPgn10110<00031010=0000=0O{eW0n0110001020101P7O1b1W012RG=5X]Q0;P0P012aVR]=5UpP5PPPOP2P9PEPQPZPZPEP`PjP0PCA3TklPmPnn0100000020000P:P_PFF1PWC7PPPqPZPZPEPrPuP0PC12rR=3^vPwPxn0100000020000PtP_P`F1PWE8n200110?00012110110:PePfPgn10110<00031010=0000=0Oy]0P1A5VHLPzPdA3U]LRyP1CDP5PPPOP2P9PEPQPZPZPEPaP~P0PCPyPDP|n0100000020000P}P_P^F1PWC7PPP?PZPZPEPsPcP0PC12sTRy=3RLPBP@n0100000020000PhP_PaF1PWE8n200110?00012110110:PePfPgn10110<00031010=0000=0O{eW0A5VHiPzPdA3U]oR]P1CDP5PPPOP2P9PEPQPZPZPEPaP~P0PCP]PDP|n0100000020000P}P_P^F1PWC7PPP?PZPZPEPsPcP0PCA3Ry4PBP@n0100000020000PhP_PaF1PWE8n200110?00012110110:PePfPgn10110<00031010=0000=0O{eW0n0110001020101P7O1b1W0n0110001020101P7O1b1b0b0P5PPPOP5Q02PQQ0:PSPVPMPXPGD9R{#G%:{%H{%;{%F{DM5W;%I{R;5VUP2P9PEPQQ04Q05Q06Q07P_Q08Q09P1PSPRPTPUPVD9RW#OG4=@Pbn200110?00012010110:P[P\n10110?00031010=0000PePfPgn10110<00031010=0000PSPV1?M>PXPGD9#=RG50Oe%YNRXP7ELP5PPPOP3PKPQPXP2PIPJPQP1P5Q02PQQ03%GW%:W%HW%;W%FWDM7W7%IW5V^P2P9PEPQQ04Q05Q06Q07P_Q08Q09P1PSPaPFP^PRD9#OG4=@Pbn200110?00012010110:P[P\n10110?00031010=0000n200110;000120108109P0PQ%eNP[P\n0100000020000n10110?00021110;00PePfPgn10110<00031010=0000=0OGe%\NP6CDARU{N,P8=0OGRNePNe1SUMP=ELP3PAPQ%n{R=,SUARTY1RYP3PAPQAhU;=PYP3PAPQA`U;=PYP5P8PQA_U;=Q01P[P\n10110?00031010>0000n10110?00021010200n10110?00021010200n10110?00021010200,P8=0OGe1vU{=0OGeW0W3W4W5W7W=W<W6W?X;EW8X9CW:W>o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_addi : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_addi. reflexivity.
Qed.

Lemma step_andi : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_andi (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_andi. reflexivity.
Qed.

Lemma step_ori : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_OR rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_ori (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_ori. reflexivity.
Qed.

Lemma step_xori : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_XOR rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_xori (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_xori. reflexivity.
Qed.

Lemma step_sltiu : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_SLTU rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sltiu (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_sltiu. reflexivity.
Qed.

Lemma step_slti : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_SLT rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slti (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_slti. reflexivity.
Qed.

Lemma step_slli : forall segs regs pc mem rom w rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slli (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm_gen by eassumption.
rewrite alu_slli. reflexivity.
Qed.

Lemma step_srli : forall segs regs pc mem rom w rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srli (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm_gen by eassumption.
rewrite alu_srli. reflexivity.
Qed.

Lemma step_srai : forall segs regs pc mem rom w rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRA rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srai (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm_gen by eassumption.
rewrite alu_srai. reflexivity.
Qed.

Lemma step_add : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_add. reflexivity.
Qed.

Lemma step_sub : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sub (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_sub. reflexivity.
Qed.

Lemma step_slt : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLT rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slt (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_slt. reflexivity.
Qed.

Lemma step_sltu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLTU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sltu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_sltu. reflexivity.
Qed.

Lemma step_and : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_and (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_and. reflexivity.
Qed.

Lemma step_or : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_or (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_or. reflexivity.
Qed.

Lemma step_xor : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_XOR rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_xor (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_xor. reflexivity.
Qed.

Lemma step_sll : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sll (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_sll. reflexivity.
Qed.

Lemma step_srl : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SRL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srl (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_srl. reflexivity.
Qed.

Lemma step_sra : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SRA rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sra (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_sra. reflexivity.
Qed.

Lemma step_addiw : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addiw (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm32_gen by eassumption.
rewrite w_addiw. reflexivity.
Qed.

Lemma step_slliw : forall segs regs pc mem rom w rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 ALU_SLL rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slliw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm32_gen by eassumption.
rewrite w_slliw. reflexivity.
Qed.

Lemma step_srliw : forall segs regs pc mem rom w rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 ALU_SRL rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srliw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm32_gen by eassumption.
rewrite w_srliw. reflexivity.
Qed.

Lemma step_sraiw : forall segs regs pc mem rom w rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 ALU_SRA rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sraiw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm32_gen by eassumption.
rewrite w_sraiw. reflexivity.
Qed.

Lemma step_addw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_ADD rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op32_gen by eassumption.
rewrite w_addw. reflexivity.
Qed.

Lemma step_subw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_subw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op32_gen by eassumption.
rewrite w_subw. reflexivity.
Qed.

Lemma step_sllw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SLL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sllw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op32_gen by eassumption.
rewrite w_sllw. reflexivity.
Qed.

Lemma step_srlw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SRL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srlw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op32_gen by eassumption.
rewrite w_srlw. reflexivity.
Qed.

Lemma step_sraw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SRA rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sraw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op32_gen by eassumption.
rewrite w_sraw. reflexivity.
Qed.

Lemma step_mul : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MUL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mul (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_mul. reflexivity.
Qed.

Lemma step_mulh : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULH rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulh (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_mulh. reflexivity.
Qed.

Lemma step_mulhsu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULHSU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulhsu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_mulhsu. reflexivity.
Qed.

Lemma step_mulhu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULHU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulhu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_mulhu. reflexivity.
Qed.

Lemma step_div : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_DIV rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_div (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_div. reflexivity.
Qed.

Lemma step_rem : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_REM rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_rem (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_rem. reflexivity.
Qed.

Lemma step_mulw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 M_MUL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul32_gen by eassumption.
rewrite w_mulw. reflexivity.
Qed.

Lemma step_divw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 M_DIV rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_divw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul32_gen by eassumption.
rewrite w_divw. reflexivity.
Qed.

Lemma step_divuw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 M_DIVU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_divuw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul32_gen by eassumption.
rewrite w_divuw. reflexivity.
Qed.

Lemma step_remw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 M_REM rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_remw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul32_gen by eassumption.
rewrite w_remw. reflexivity.
Qed.

Lemma step_remuw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 M_REMU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_remuw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul32_gen by eassumption.
rewrite w_remuw. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_beq_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh43immh53memh62pch74regsh83romh93rs1h:3rs2h;4segsh<1wp;1p;2p;3p;4p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8g002dR1p4p7210R2P0p8P2p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g00L4j1BTg005bj10Tg006Gj14Tg006lj11Tg007Jj12TP1j2<Tg0178j15Tg03`^j2;Tg019Pj26Tg00>Fj33Tg03a`j18Tg03b`j29Tg03c@j1:Tg04P[j4ATg00:Tj1@Tg03d]j4?Tg03n1j27Tg05=Pj2=Tg05>Bl>>Tg01=0#Bg008oR1#0R0#4#1R2%00R0#0R3#0#0R4#0#1#2R5'<%13#2#5\5R3%14#2R4%22R2%41#0#4#1#2%54f8R1f6R6';f3R7,6433g009TR4f4R8#8g00A933g04IJR9g00;oR:'9R;#5f5R<#:P9P:g05?BR:P8P7f2R9CA%@0C?,6;33f:R;/7<17;8'=g00:4534f<f;P;f9P1f7P:P6P<P8P7P9f1f0M>>W0W1W2W3W4X:2W9W<X83W5X65W7W;o"). Qed.

Lemma step_beq_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh43immh53memh62pch74regsh83romh93rs1h:3rs2h;4segsh<1wp;1p;2p;3p;4p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8g002dR1p4p7210R2P0p8P2p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g00L4j1BTg005bj10Tg006Gj14Tg006lj11Tg007Jj12TP1j2<Tg0178j15Tg03`^j2;Tg019Pj26Tg00>Fj33Tg03a`j18Tg03b`j29Tg03c@j1:Tg04P[j4ATg00:Tj1@Tg03d]j4?Tg03n1j27Tg05=Pj2=Tg05@4l>>Tg01=0#Bg008oR1#0R0#4#1R2%00R0#0R3#0#0R4#0#1#2R5'<%13#2#5\5R3%14#2R4%22R2%41#0#4#1#2%54f8R1f6R6';f3R7,6433g009TR4f4R8#8g00A9R933g04IJR:g00;oR;'9R<#5f5R=#:P:P;g05?BR;P8P7f2R:CA%@0C?,6<33f:R</7=17<8'==349f<f;P<f9P1f7P;P6P=P8P7P:f1f0M>>W0W1W2W3W4X:2W9W<X83W5X65W7W;o"). Qed.

(* [comment removed for export] *)
Lemma step_bne_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh41bh53immh63memh72pch84regsh93romh:3rs1h;3rs2h<4segsh=1wp;1p;2p;3p;4p;6p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g00L4j1GTg005bj10Tg006Gj16Tg006lj12Tg007Jj13TP2j2@Tg0178j15Tg03`^j2<Tg019Pj27Tg00>Fj31Tg03a`j18Tg03b`j29Tg03c@j1:Tg04P[j4FTg00:Tj1ETg03d]j4DTg03n1j24Tg05=Pj2?Tg05A4j1>Tg008Uj2=Tg00=Yj3ATP0j6BTg04R9j3;Tg05>Bl>CTg01=0#Gg008oR0#0R2#6#2R1%02R2#0R3#0#0R4#0#2R5#3R6'@%23#3#5\6R3%24#3R4%31R1%60#0#6#2#3%54f8R0f6R7'<f3R8,7431g009TR4f4R9#8g00A9R:31g04IJR;g00;oR<'9R=#5f5R>#:P;P<g05ARR<P9P8f2R;CF%E2CD,7=31f:R=/4>14=9'?=14:f<f;R2P=f9P0f7P<P7P>P9P8P;f1P4P:f0R:#>g00:4R;514X441=4;1427R7142>R25A5P:EBA;<72=14;eM>CW0W1W2W3W5X;1W:W=X93W6X76W8W<o"). Qed.

Lemma step_bne_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh41bh53immh63memh72pch84regsh93romh:3rs1h;3rs2h<4segsh=1wp;1p;2p;3p;4p;6p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g00L4j1HTg005bj10Tg006Gj17Tg006lj11Tg007Jj12TP2j2@Tg0178j16Tg03`^j2<Tg019Pj28Tg00>Fj33Tg03a`j19Tg03b`j2:Tg03c@j1GTg04P[j4FTg00:Tj1ETg03d]j4?Tg03n1j24Tg05=Pj2>Tg05A4j1=Tg008Uj2ATg00=Yj3BTP0j6;Tg04R9j3CTg05@4l>DTg009TR0f0R2g00A9R133p=5g01=0#Hg008oR3#0R4#7#1R5%04R4#0R6#0#0R7#0#1R8#2R9'@%16#2#6\9R6%17#2R7%25R5%73#0#7#1#2%67f8R3f6R:'<f3R;,8733f4R7#9#5g04IJR<g00;oR=':R>#6f5R?#GP<P=g05ARR=P7P;f2R<CF%E4C?,8>33f:R>/4?14>7'>g00:4R4530f<f;R@P>f9P3f7P=P:P?P7P;P<f1P0P4%=2#5X401A0114@:R:14@?R@5B8P2E;AC=:@#5eM>DW0W1W2W3W5X;5W:W=X96W6X79W8W<o"). Qed.

(* [comment removed for export] *)
Lemma step_blt_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LT rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh43immh53memh62pch74regsh83romh93rs1h:3rs2h;4segsh<1wp;1p;2p;3p;4p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8g002dR1p4p7210R2P0p8P2p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g00L4j1BTg005bj10Tg006Gj14Tg006lj11Tg007Jj12TP1j2<Tg0178j15Tg03`^j2;Tg019Pj26Tg00>Fj33Tg03a`j18Tg03b`j29Tg03c@j1:Tg04P[j4ATg00:Tj1@Tg03d]j4?Tg03n1j27Tg05BDj2=Tg05>Bl>>Tg01=0#Bg008oR1#0R0#4#1R2%00R0#0R3#0#0R4#0#1#2R5'<%13#2#5\5R3%14#2R4%22R2%41#0#4#1#2%54f8R1f6R6';f3R7,6433g009TR4f4R8#8g00A933g04IJR9g00;oR:'9R;#5f5R<#:P9P:g05C7R:P8P7f2R9CA%@0C?,6;33f:R;/7<17;8'=g00:4534f<f;P;f9P1f7P:P6P<P8P7P9f1f0M>>W0W1W2W3W4X:2W9W<X83W5X65W7W;o"). Qed.

Lemma step_blt_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LT rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh43immh53memh62pch74regsh83romh93rs1h:3rs2h;4segsh<1wp;1p;2p;3p;4p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8g002dR1p4p7210R2P0p8P2p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g00L4j1BTg005bj10Tg006Gj14Tg006lj11Tg007Jj12TP1j2<Tg0178j15Tg03`^j2;Tg019Pj26Tg00>Fj33Tg03a`j18Tg03b`j29Tg03c@j1:Tg04P[j4ATg00:Tj1@Tg03d]j4?Tg03n1j27Tg05BDj2=Tg05@4l>>Tg01=0#Bg008oR1#0R0#4#1R2%00R0#0R3#0#0R4#0#1#2R5'<%13#2#5\5R3%14#2R4%22R2%41#0#4#1#2%54f8R1f6R6';f3R7,6433g009TR4f4R8#8g00A9R933g04IJR:g00;oR;'9R<#5f5R=#:P:P;g05C7R;P8P7f2R:CA%@0C?,6<33f:R</7=17<8'==349f<f;P<f9P1f7P;P6P=P8P7P:f1f0M>>W0W1W2W3W4X:2W9W<X83W5X65W7W;o"). Qed.

(* [comment removed for export] *)
Lemma step_bge_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GE rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh41bh53immh63memh72pch84regsh93romh:3rs1h;3rs2h<4segsh=1wp;1p;2p;3p;4p;6p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g00L4j1GTg005bj10Tg006Gj16Tg006lj12Tg007Jj13TP2j2@Tg0178j15Tg03`^j2<Tg019Pj27Tg00>Fj31Tg03a`j18Tg03b`j29Tg03c@j1:Tg04P[j4FTg00:Tj1ETg03d]j4DTg03n1j24Tg05BDj2?Tg05A4j1>Tg008Uj2=Tg02@Jj3ATP0j6BTg04R9j3;Tg05>Bl>CTg01=0#Gg008oR0#0R2#6#2R1%02R2#0R3#0#0R4#0#2R5#3R6'@%23#3#5\6R3%24#3R4%31R1%60#0#6#2#3%54f8R0f6R7'<f3R8,7431g009TR4f4R9#8g00A9R:31g04IJR;g00;oR<'9R=#5f5R>#:P;P<g05CiR<P9P8f2R;CF%E2CD,7=31f:R=/4>14=9'?=14:f<f;R2P=f9P0f7P<P7P>P9P8P;f1P4P:f0R:#>g00:4R;514X441=4;1427R7142>R25A5P:EBA;<72=14;eM>CW0W1W2W3W5X;1W:W=X93W6X76W8W<o"). Qed.

Lemma step_bge_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GE rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh41bh53immh63memh72pch84regsh93romh:3rs1h;3rs2h<4segsh=1wp;1p;2p;3p;4p;6p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g00L4j1HTg005bj10Tg006Gj17Tg006lj11Tg007Jj12TP2j2@Tg0178j16Tg03`^j2<Tg019Pj28Tg00>Fj33Tg03a`j19Tg03b`j2:Tg03c@j1GTg04P[j4FTg00:Tj1ETg03d]j4?Tg03n1j24Tg05BDj2>Tg05A4j1=Tg008Uj2ATg02@Jj3BTP0j6;Tg04R9j3CTg05@4l>DTg009TR0f0R2g00A9R133p=5g01=0#Hg008oR3#0R4#7#1R5%04R4#0R6#0#0R7#0#1R8#2R9'@%16#2#6\9R6%17#2R7%25R5%73#0#7#1#2%67f8R3f6R:'<f3R;,8733f4R7#9#5g04IJR<g00;oR=':R>#6f5R?#GP<P=g05CiR=P7P;f2R<CF%E4C?,8>33f:R>/4?14>7'>g00:4R4530f<f;R@P>f9P3f7P=P:P?P7P;P<f1P0P4%=2#5X401A0114@:R:14@?R@5B8P2E;AC=:@#5eM>DW0W1W2W3W5X;5W:W=X96W6X79W8W<o"). Qed.

Lemma step_bltu_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LTU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh43immh53memh62pch74regsh83romh93rs1h:3rs2h;4segsh<1wp;1p;2p;3p;4p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8g002dR1p4p7210R2P0p8P2p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g00L4j1BTg005bj10Tg006Gj14Tg006lj11Tg007Jj12TP1j2<Tg0178j15Tg03`^j2;Tg019Pj26Tg00>Fj33Tg03a`j18Tg03b`j29Tg03c@j1:Tg04P[j4ATg00:Tj1@Tg03d]j4?Tg03n1j27Tg05D[j2=Tg05>Bl>>Tg01=0#Bg008oR1#0R0#4#1R2%00R0#0R3#0#0R4#0#1#2R5'<%13#2#5\5R3%14#2R4%22R2%41#0#4#1#2%54f8R1f6R6';f3R7,6433g009TR4f4R8#8g00A933g04IJR9g00;oR:'9R;#5f5R<#:P9P:g05ENR:P8P7f2R9CA%@0C?,6;33f:R;/7<17;8'=g00:4534f<f;P;f9P1f7P:P6P<P8P7P9f1f0M>>W0W1W2W3W4X:2W9W<X83W5X65W7W;o"). Qed.

Lemma step_bltu_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LTU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh43immh53memh62pch74regsh83romh93rs1h:3rs2h;4segsh<1wp;1p;2p;3p;4p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8g002dR1p4p7210R2P0p8P2p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g00L4j1BTg005bj10Tg006Gj14Tg006lj11Tg007Jj12TP1j2<Tg0178j15Tg03`^j2;Tg019Pj26Tg00>Fj33Tg03a`j18Tg03b`j29Tg03c@j1:Tg04P[j4ATg00:Tj1@Tg03d]j4?Tg03n1j27Tg05D[j2=Tg05@4l>>Tg01=0#Bg008oR1#0R0#4#1R2%00R0#0R3#0#0R4#0#1#2R5'<%13#2#5\5R3%14#2R4%22R2%41#0#4#1#2%54f8R1f6R6';f3R7,6433g009TR4f4R8#8g00A9R933g04IJR:g00;oR;'9R<#5f5R=#:P:P;g05ENR;P8P7f2R:CA%@0C?,6<33f:R</7=17<8'==349f<f;P<f9P1f7P;P6P=P8P7P:f1f0M>>W0W1W2W3W4X:2W9W<X83W5X65W7W;o"). Qed.

(* [comment removed for export] *)
Lemma step_bgeu_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GEU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh41bh53immh63memh72pch84regsh93romh:3rs1h;3rs2h<4segsh=1wp;1p;2p;3p;4p;6p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g00L4j1GTg005bj10Tg006Gj16Tg006lj12Tg007Jj13TP2j2@Tg0178j15Tg03`^j2<Tg019Pj27Tg00>Fj31Tg03a`j18Tg03b`j29Tg03c@j1:Tg04P[j4FTg00:Tj1ETg03d]j4DTg03n1j24Tg05D[j2?Tg05A4j1>Tg008Uj2=Tg02C7j3ATP0j6BTg04R9j3;Tg05>Bl>CTg01=0#Gg008oR0#0R2#6#2R1%02R2#0R3#0#0R4#0#2R5#3R6'@%23#3#5\6R3%24#3R4%31R1%60#0#6#2#3%54f8R0f6R7'<f3R8,7431g009TR4f4R9#8g00A9R:31g04IJR;g00;oR<'9R=#5f5R>#:P;P<g05F@R<P9P8f2R;CF%E2CD,7=31f:R=/4>14=9'?=14:f<f;R2P=f9P0f7P<P7P>P9P8P;f1P4P:f0R:#>g00:4R;514X441=4;1427R7142>R25A5P:EBA;<72=14;eM>CW0W1W2W3W5X;1W:W=X93W6X76W8W<o"). Qed.

Lemma step_bgeu_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GEU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hch12Hdh22Heh32Hfh41bh53immh63memh72pch84regsh93romh:3rs1h;3rs2h<4segsh=1wp;1p;2p;3p;4p;6p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g00L4j1HTg005bj10Tg006Gj17Tg006lj11Tg007Jj12TP2j2@Tg0178j16Tg03`^j2<Tg019Pj28Tg00>Fj33Tg03a`j19Tg03b`j2:Tg03c@j1GTg04P[j4FTg00:Tj1ETg03d]j4?Tg03n1j24Tg05D[j2>Tg05A4j1=Tg008Uj2ATg02C7j3BTP0j6;Tg04R9j3CTg05@4l>DTg009TR0f0R2g00A9R133p=5g01=0#Hg008oR3#0R4#7#1R5%04R4#0R6#0#0R7#0#1R8#2R9'@%16#2#6\9R6%17#2R7%25R5%73#0#7#1#2%67f8R3f6R:'<f3R;,8733f4R7#9#5g04IJR<g00;oR=':R>#6f5R?#GP<P=g05F@R=P7P;f2R<CF%E4C?,8>33f:R>/4?14>7'>g00:4R4530f<f;R@P>f9P3f7P=P:P?P7P;P<f1P0P4%=2#5X401A0114@:R:14@?R@5B8P2E;AC=:@#5eM>DW0W1W2W3W5X;5W:W=X96W6X79W8W<o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_lui : forall segs regs pc mem rom w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12))) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

Lemma step_auipc : forall segs regs pc mem rom w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12))) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

Lemma step_jal_x0 : forall segs regs pc mem rom w (imm : bv 21),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal 0 imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p'0h01bh11oh27Hdecodeh36Hecallh46Hfetchh53immh63memh72pch84regsh93romh:4segsh;1wi001wi011ci026c_fcsri037c_fregsi044c_pci056c_regsi066c_resvi071ii083iszi092m'i0:1pi0;1ri0<6reporti0=3st'i0>1xp;1p;2p;3p;4p;5p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3g0161R3p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g00L4j1sTg005bj18Tg006Gj1KTg006lj1<Tg007Jj1FTP2j2nTg0178R2j1ATg03`^j2NTg019Pj2=Tg00>Fj30Tg03a`j1STg03b`R1j2QTg03c@j1ITg00CWj3aTg05I?j2_Tg00:Tj1^Tg03d]j4MTg01fdR4j1\TP3j1[Tg01glj53Tg03e=j3LTg03fIj1HTg03gGj3YTg03hLj3XTg03iRj3WTg00KTj1cTg03jWj1VTg03k_j1UTg03lgj2JTg01J1j2TTg04QGj2RTg01h^j2;Tg03oWj1GTg040Vj16Tg041Vj1@Tg042Wj2bTg043Uj1BTg044Tj15Tg045Sj1ETg046Qj81Tg00C1j2`Tg047Xj52Tg048Aj3PTg048hj3OTg04:3j2>Tg04;7j1rTg04;`j1qTg04<Jj1pTg00OAj1mTg04=1j1lTg04=Zj1kTg04>Cj2CTg04?Jj1]Tg04@Cj1iTg04A8j1hTg01HTj3DTg01;5j39Tg04BVj5ZTg04Fnj37Tg01mZj2gTg008Uj2fTg01onj3jTP0j6?Tg007mj1eTg04E5j1oTg04F2j2dTf2R0g01ifR3f1R5f0R637';p=4g04H5R7P0P5P6CMp=:g01=0#sg008o#8R8#KR9#<R:%88R8#8R;#8#8R<#8#<R=#FR>'nR?%<;#F#A\>R@%<<#FR<%89#K#<R9#F%A<RAf6RBf4RC'N1=<530g009TRD%S0g00A9RE30g04IJRFg00;oRG'QRH#ARIf3RJ#IPFPGg00H2g00DYRK5a:RL/_0%^8R8CM,=H30PA1=<C%\3RMP2P<%[3RN#\ROP6f;RPp,2fxRQf:RRf9RSf8RTf7RUD3;L6RVP2P<POPQPSPTPUPBD3RW#HRX=YRTPVP2P<POAXRXTPVP4P3POAWRXTg04J6#cRV94N6RY%VNRZ%UNR[n10110>00031010=0000n10110>00021010000n10110>00021010000n10110>00021010000,J3PQPS1T9C,RTR\PUPBD3,;3R]30X1APDPEP4PNPMPDPOP6%GW%6W%@W%K;#^=a:K,bW,=>%BW%5WPX%EWG1=4NVP2PHPOf5RX#IP1PFPGPOP6P41Q7@RK#[R;POf=RE1`=6RAPQf<R^PPPRPSD3R_#G%6_%@_%5_%B_D27P5%H_3OP1P7P@PO1>K6R_%r5R`%q5Ra%p5Rb%m>Rc%l5Rd%k5ReP6PQf?f>RfPEP^D3#EG11CK0Rg54Nn200110>000120101109PZP[n10110>00031010<0000n200110:000120107108RhPDPO%]XPZP[n0100000020000Rin10110>00021110:00n01000000200011>36,;3Rj%V3Rk%U3Rln10110;00031010<0000=0M]X0DPIPFPG1_LJRmP8CM,=HP4PNPMP2PHPOP6PhPin10110>00021110:00PjPkPln10110;00031010<0000=0M]X1IPDg00:4P4PNPMP1P7P@POPDP7P6PSPS%iQRIPTPcPc%hQR]PUPBG1Ri#6RhAD9=C99=TRn%5iRiPcD2P:P>PL1`=8R899=TPSDZPhPnPiPcD2n0100000020000=:@U=7KV,>KP7P?P5PCn01101000150105103104102106RnP7P?P5PJn01101000150105103104102106R?P7P>P5P0n01101000150105103104102106RoPcP7%A>P5P6n01101000150105103104102106RpP7P<P5P5n01101000150105103104102106RqP6PTG1RrPDP7P0PPPPPIPRPcPcP]PSPTG1Rs#6RtAD9=B99=RRu%5sRsPcD2P:P>PLA9=R8PPDZPtPuPsPcD2n0100000020000=:@S=7KV,CK54Nn200110>000121101109PjPkPln10110;00031010<0000PSPIP\PcPcP]PUPBG1,;3R\50MX0DP>1T9JRu,gUP4PNPMP1P7P@POPSPhP6PiPcD2=:@U=7KV,>KPPPtP0PsPcD2=:@S=7KV,CK94Nrn200110>000121101109PjPkPln10110;00031010<0000=0M\X0>PTPI1RUuRuPcPcP]PBPXG1,;3R\,fMAD9=J99=URrAjU9JE?P4PNPMP1P7P@POPTPTPIPUPcPcP]PBPXG1RJ#6Pr%5JPcD2=:@B=7KV,>KPnP?PoPcPpPqP6PUG1PRPRPIPSPcPcP]PTPUG1R]#6AD9=X99=S%5]PcD2=:@T=7KV,CK54Nn200110>000121101109PjPkPln10110;00031010<0000=0M\e%eLg05IkE?P4PNPMP4P;POPQPTPUPBPXD3RL#G%6L%@L%5L%BLD29P8m%HLR85OSP1P7P@POP_P`PaPbPcPdPeP6PQPPPRPSPTD3Rm#EG1=4Ngn200110>000120101109PZP[n10110>00031010<0000PjPkPln10110;00031010<0000PQPTPuPBPXD3,;3RX50Me%ICRBP6E?P4PNPMP2PHPOPBP1PFPGPOP6P4P;PO%Gm%6m%@m%5m%BmD29PA5%Hm5O^P1P7P@POP_P`PaPbPcPdPeP6PQPfPEP^PPD3#EG1=4Ngn200110>000120101109PZP[n10110>00031010<0000n200110:000120107108PDPO%]CPZP[n0100000020000n10110>00021110:00PjPkPln10110;00031010<0000=0MXe%SCP5E?ALSLC,J3=0MXRCePCe1NSUP0E?P2P<PO%oLR0,NSALRW6RWP2P<POAYS80PWP2P<POAXS80PWP4P3POAWS80PYPZP[n10110>00031010=0000n10110>00021010000n10110>00021010000n10110>00021010000,J3=0MXe1dSL=0MXeW2W3W4W5W;X9@W6X7>W8W:o"). Qed.

(* [comment removed for export] *)
Lemma step_jalr_gen : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                  (jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_jalr, ?b_npc4; reflexivity.
Qed.

Lemma step_ecall : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
               ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p'0h06Hecallh16Hfetchh21bh33memh41oh52pch64regsh73romh84segsh91wi001wi011ci021ii033iszi042m'i051pi061ri076reporti083st'i091xp;1p;2p;3p;5p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3g0161R3p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g00L4j1hTg005bj13Tg006Gj1ITg006lj16Tg007Jj1CTP2j2[Tg0178R2j1MTg03`^j2<Tg019Pj22Tg00>Fj30Tg03a`j1FTg01fdR1j1ETP3j1DTg01glj55Tg03e=j3?Tg03fIj1=Tg03gGj3OTg03hLj3NTg03iRj3QTg00KTj1WTg04Fnj37Tg01h^j21Tg03jWj1LTg03k_j1KTg03lgj29Tg04@Cj1VTg00:Tj1UTg00CWj3TTg03n1j2GTg00OAj1STg04A8j1RTg046Qj84Tg03oWj18Tg040Vj1BTg041Vj1@Tg042Wj2JTg043Uj1;Tg044Tj1ATg045Sj1:Tg03b`R3j2HTg03c@j1gTg00C1j2fTg047Xj5eTg048Aj3cTg048hj3bTg04:3j2>Tg04;7j1`Tg04;`j1_Tg04<Jj1\Tg04=1j1ZTg04=Zj1]Tg04>Cj2^Tg04?Jj1YTg008Uj2aTP0j6PTg04E5j1XTg04F2j2dTg01=0#hg008o#3R0#I#6R4%30#3R0#3#3R5#3#6R6#CR7'[%60#C#M\7R8%65#CR5%M5R9f5R:f3R;'<f0R<,2530g009TR=f1R>#Fg00:4R?30P9f2R@,25g01ifRA#ERBP2P5%DARC#ERDP<f9REp,2fxRFf8RGf7RHf6RIP:D5;?<RJP2P5PDPFPHPIP:f4RKD5RL#=RM=OGIPJP2P5PDANGMIPJP1PAPDAQGMIg04J6#WRJ97A<,1CRN%LCRO%KCRPn1011090003101080000n10110900021010000n10110900021010000n10110900021010000,9APH%VFRQPI%I0#Ug00DY5T4R4,GH,27%S7R0%RFRRP:PKG4,1ARS30X49P=P?P1PCPBP=PDP<%8L%BL%@L1JL4,27%;L%ALPM%:LG4=7AJ,1CP2g04IJRMg00;oR?'HPD%g;P3PMP?PDP<P1g04H5R?/H8RM#DPDf;R91f6<PFf:R6PEPGPHD5RE#8%BE%@E%AE%;EDe7c>%=E3bP3P?P8PD1>M<%`>%_>%\>P0%Z>%]>P<PFf=f<P9P6D5#:G41^M@57A,1Cn2001109000120101104POPPn1011090003101070000n2001105000120102103P=PD%Y;POPPn0100000020000n10110900021110500n01000000200011>A<,1A%LA%KAn1011060003101070000=0BSX2=PIPQP:1GI4,27P0PRPKP;G4,1ARR,aBPFPIP:PKP;D5R;#8%B;%@;1J;4,27%;;%A;%=;R4%:;G4=7AJ,>A,1A=0BRe%F@P<EPA?H;@,9A=0BRR@eP@e1<H:P>EPP2P5PD%X;R>,<HA?GL<RLP2P5PDAOH4>PLP2P5PDANH4>PLP1PAPDAQH4>PNPOPPn1011090003101080000n10110900021010000n10110900021010000n10110900021010000,9A=0BRe1dH;=0BReW0W1W9X78W3X57W6W8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_lbu : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned b))) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
assert (Hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b)).
{ rewrite le_word_1, b_extract8_id. apply bv_eq.
unfold zext. rewrite bv_zero_extend_unsigned by lia.
rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
pose proof (u8_range b). change (bv_modulus 64) with (2^64)%Z. lia. }
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.

Lemma step_lb : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lb b)) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite b_lb_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.

Lemma step_lh : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lh v)) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lh_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.

Lemma step_lhu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : zext 64 (bv_extract 0 16 v) = v).
{ pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
pose proof (bytes_le_to_Z_bound bs) as Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
apply bv_eq. unfold zext.
rewrite bv_zero_extend_unsigned by lia.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_small.
change (bv_modulus 16) with 65536%Z.
change (2 ^ (8 * Z.of_nat 2))%Z with 65536%Z in Hb. lia. }
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.

Lemma step_lw : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v)) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.

Lemma step_lwu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : zext 64 (bv_extract 0 32 v) = v).
{ pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
pose proof (bytes_le_to_Z_bound bs) as Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
apply bv_eq. unfold zext.
rewrite bv_zero_extend_unsigned by lia.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_small.
change (bv_modulus 32) with 4294967296%Z.
change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb. lia. }
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.

Lemma step_ld : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : bv_extract 0 64 v = v).
{ apply bv_eq.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_bv_unsigned. }
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma two64_pos : (0 < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg00:Tj14Tg00JHj2:Tg00F0j22Tg00ETj21Tg00;2j2<Tg00K0j3;Tg00KTj19Tg00L4j17Tg00SJj16Tg00M2j15Tg00MPj18Tg00N;j23Tg006lj1FTg00TFj3ETg00Tij4DTg00Y1j7=Tg00Pkj2>Tg008Uj2?Tg00QMj2@Tg00>Fj3ATg00R9j3BTg00RXj4CTg008o#0R0#4R1%00#0#0#0#0R0#4R2':g00H2R3/2111321<12R4,23R5[[1131R6g00\_R7f1R89;12UW01134\7^06g00];R6#9%76g00;oR6#6%56%86R7g00Z`g00[?R4P4g00[_R4P61363g00]g1361%F05E6CDg00\?F=1>74f0R4f2R7g009TR0g00:4R1'?1@47=A01dAB638CCb2b5b6P5P4b1b3b4o"). Qed.

Lemma v_addi_nneg : forall x imm, (0 <= imm)%Z -> (bv_unsigned x + imm < 2^64)%Z ->
  bv_unsigned (v_addi x imm) = (bv_unsigned x + imm)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h01Hh12Hah24__x1h34__x2h42H0h52Hih62Hsh77__arithh84__ffh96__sat0h:6__sat1h;8__varmaph<5__with=3immh>1xh?1zp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1cTg007Jj1NTg00<Mj21Tg00BTj24Tg00:Tj1?Tg00;2j2MTg00F0j22Tg00o0j2FTg00>Fj3:Tg00;Oj2CTg022Aj1BTg00AYR1j2;Tg00JHj2^Tg00K0j3XTg00E5j17Tg00g\j29Tg00hEj3@Tg00hnj2UTg00KTj1TTg00iZj3QTg00L4j1LTg00LTj2KTg00SJj1JTg00_Oj4ITg00M2j1HTg00MPj1GTg00N;j2=Tg00N^j2>Tg00OAj1ETg010aj3DTg00TFj3OTg00Tij4<Tg00UTj7PTg00Pkj2RTg008Uj2STg00QMj2bTg00R9j3aTg00RXj4`Tg02LKj3]Tg03\@j1\TP0j6ATg00C1j2YTg01FUj2ZTg01mZj2[Tg00ETj2WTg00Y1j7VTg00YUj8_Tg00H2R0f0R2'Wp=0g00;oR3f1R4g00Z9P2C<p=8P4g00Z`R5g00[?R6P6g00[_R7P2g00\?FVp=5f3R8P5P6P6P7f2R9P4P2G_p=6g008oR:#3R;#3#3#3#3#3R<#cR=#N%02R>11=9/44%?;R?%?<R<'MR@'2P311=8RA/49RB,F=RCf4RD,1=/489:32X?3REP31CB@PE%B8%0A12A@';1^?<120?%0<120@[[%0?RAg00\_REAX?<4UW1%0@\E^1AP1f6R1,1=RA#012A@f7,1=/41R1#0121@';P9f8R1,1=#0f9RA,1=/2@g00];REg00D:R<#7RF#7#7,93193F193<5@35@3g00nD'U%TE3Q%LEP31K39P4%J3CI%H3%G3RE1=30R<1>3:R:'8,5E%E6RFPEP31>3;R;9D3:R:g00]g1=3?=O3=C<,5ER?PFPE18<;,5EPFPEP5P6P6P718<:,5EP?FPC6C6C61RE7P2P9g009TREg00:4R7'S1b29=:E7dAa304C`b8b;b<X23X331449/2@%08148DRD#012D@';[[\>^23^33P2f:f;,1=P9P1PAO5b7W4W0P4P2O2n2001000000121000000b9b:b09]B@PC%\BEA1Y=B,1=1Z=BEA1[89,1==:3BeW6W5X=3W>o"). Qed.

Lemma v_addi_0 : forall x : word, v_addi x 0 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02b1h12b2h21nh31zh41Hh51xp;1p;3p;2p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1=Tg007Jj12Tg00>Fj31Tg00<Mj20Tg00@Uj3;Tg01mZj2:Tg00BTj28Tg00o0j24Tg05VOj27Tg05Wmj16TP0j65Tg00C1j29Tg01FUj2<Tg008o#3#3#3#3#3#3#=R0#2g00>`R1f0R2#2R3f1R4#2R5g00AYf2R6#2?142g00;oR7f3R8/06108431R9[10641062517%28?164[R:f4#2?186\9A;642P2n2001000000120000000W1W0W2P:^15^03^21P2P0g00H2R1,:4R3P4P71004R5/81R1,401006R69172X37P7P51402=176X371704P1%65E51901,001<01E51003=175eO4b4W5o"). Qed.

Lemma v_add_small : forall x y : word, (bv_unsigned x + bv_unsigned y < 2^64)%Z ->
  bv_unsigned (v_add x y) = (bv_unsigned x + bv_unsigned y)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02H0h12H1h22Hah34__x1h44__x2h51Hh62H2h72H3h87__arithh94__ffh:6__sat2h;6__sat3h<8__varmaph=5__with>1xh?1yh@1zp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj14Tg006lj1cTg007Jj1MTg00<Mj20Tg00BTj23Tg00:Tj1ATg00;2j2UTg00F0j21Tg00o0j2ITg00>Fj38Tg00;Oj2ETg022Aj1CTg00AYR1j26Tg00JHj2^Tg00K0j3XTg00E5j1;Tg00g\j2:Tg00hEj3?Tg00hnj2TTg00KTj1RTg00iZj3QTg00L4j1LTg00LTj2KTg00SJj1JTg00_Oj4HTg00M2j1FTg00MPj1GTg00N;j2<Tg00N^j2=Tg00OAj1DTg010aj3NTg00TFj3OTg00Tij4>Tg00UTj7PTg00Pkj2BTg008Uj2STg00QMj2bTg00R9j3aTg00RXj4`Tg02LKj3]Tg03\@j1\TP0j6@Tg00C1j2YTg01FUj2ZTg02EEj2[Tg00ETj2WTg00Y1j7VTg00YUj8_Tg00H2R0f0R2'Wp=2g00;oR3f1R4g00Z9P2C>p=9P4g00Z`R5g00[?R6P6g00[_R7P2g00\?FVp=5f3R8P5P6P6P7f2R9P4P2G_p=7g008oR:#4R;#4#4#4#4#4R<#cR=#MR>10=4R?10=2'3%A;R@%A<R<'URA'1P310=9RB/3?R?,I=RC10=8/3B9832X@3RDP31E?APD%C9RD%2B11BA'6RBPDPB1^@<110@%2<110A[[%2@RBg00\_RDAX@<4UW2%2A\D^2BP1f5,0=RB#211BAf7RB,0=RDf6R<,0='3RE#211EA'6P9%2Df8,0=/1AP1f:,0=R1#2111Af;,0=/31R1#2111A'6PBf<,0=#2f=RB,0=/1Ag00];R1g00D:RD#;#;RE#;,:31:3E1:3D5?35?3g00nD'T%R13Q%L1P31K39P4%J3CH%F3%G3R11<30RD1=3;R;'9,51%D6REP11=3:R:,9D,51PEP1P3AN3:;R:g00]g1<3@=O3=C>,51R@PEP1P5P6P6P719D:,51P@FPC7C7C71B17P2P9g009TR1g00:4R7'S1b29=817dAa304C`b9b<b=X33X43%24R01398/1Af4,38R8#2118A'6[\0[^33^43P2f>,0=f?,0=P<P9PBO5b8W7W0P4P2O2n2001000000121000000W6W1P4P2O2n2001000000121000000b:b;b1b09]?APC%\?E@1Y=?,0=1Z=?E@1[94,0==83?eW5X?>W>o"). Qed.

Lemma v_sub_small : forall x y : word, (bv_unsigned y <= bv_unsigned x)%Z ->
  bv_unsigned (v_sub x y) = (bv_unsigned x - bv_unsigned y)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02H0h12H1h22Hah34__x1h44__x2h51Hh62H2h72H3h87__arithh94__ffh:6__sat2h;6__sat3h<8__varmaph=5__with>1xh?1yh@1zp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1cTg007Jj1OTg00<Mj20Tg00ETj2=Tg010Dj24Tg00o0j2UTg00>Fj38Tg00:Tj1?Tg00;2j2GTg00;Oj2FTg022Aj1DTg00F0j22Tg00AYR1j26Tg00JHj2XTg00K0j3WTg00E5j1;Tg00g\j2<Tg00hEj3ATg00hnj2TTg00KTj1RTg00iZj3NTg00L4j1MTg00LTj2LTg00SJj1KTg00_Oj4JTg00M2j1ITg00MPj1HTg00N;j2>Tg00N^j2@Tg00OAj1ETg00TFj3PTg00Tij4:Tg01V\j3QTg00UTj7CTg00Pkj2STg008Uj2bTg00QMj2aTg00R9j3`Tg00RXj4]Tg02LKj3\Tg03\@j1YTP0j6BTg00C1j2ZTg01FUj2[Tg02F8j2VTg00Y1j7^Tg00YUj8_Tg00H2R0f0R2'=p=1g00;oR3f1R4g00Z9P2C:p=7P4g00Z`R5g00[?R6P6g00[_R7P2g00\?F^p=5f3R8P5P6P6P7f2R9P4P2G_p=9g008oR:#3R;#3#3#3#3#3R<#cR=#OR>10=210=4R?'=P310=9R@/4?R?,U=RA10=8/4@9832X@3RBP3%?;RC%?<R<'GRD,F?PB%D9RB%1@12@D'6R@PBP@1XC<120C%1<120D[[%1CR@g00\_RBAWC<4UW2%1D\B^2@P1f5,0=R@#112@Df7R@,0=RBf6R<,0='4RE#112ED'6P9%1Bf8,0=/2DP1f:,0=R1#1121Df;,0=/41R1#1121D'6P@f<,0=#1f=R@,0=/2Dg00];R1g00D:RB#;#;RE#;,<31<3E1<3B5A35A3g00nD'T%R13N%M1P31L39P4%K3CJ%I3%H3R11>30RB1@3;R;'7,51%E6REP1P31@3:R:g00]gRF1>3C=P3=RCC:,51PEP117;:,51PEP1P5P6P6P7AQ3:;R:,7B,51P3P:PFPCC:,51FCC9C9C91S17P2P9g009TR1g00:4R7'b1a29=817dA`304C]b9b<b=X33X43%14124D1=89f4,48R8#1128D'6[[[^33^43P2f>,0=f?,0=P<P4P@O5b8W7W0P4P2O2n2001000000121000000W6W1P4P2O2n2001000000121000000b:b;b1b09\?DPA%Y?EB1Z=?,0=1[=?EB1V94,0==83?eW5X?>W>o"). Qed.

Lemma v_slli_3 : forall x : word, (8 * bv_unsigned x < 2^64)%Z ->
  bv_unsigned (v_slli x 3) = (8 * bv_unsigned x)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h04__x1h11Hh27__arithh34__ffh47__sat10h56__sat9h68__varmaph75__with81zh92H0h:2Hah;2H8h<1xp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj16Tg006lj1gTg007Jj1PTg00:Tj19Tg00<Mj21Tg00dkj20Tg00;2j2ATg00F0j23Tg006Gj1LTg01>oj2HTg00o0j2GTg00;Oj2=Tg022Aj1fTg00AYR1j2<Tg00JHj2YTg00K0j3WTg00KTj1VTg00L4j1UTg00LTj2TTg00M2j1QTg00MPj1OTg00N^j2NTg00N;j27Tg00j^j3?Tg00Tij48Tg00Pkj2ITg008Uj2JTg00QMj2KTg00>Fj3@Tg00R9j3FTg00RXj4MTg00g\j2BTg00E5j1;Tg00hEj3ETg00hnj2DTg01Tdj2RTg00iZj3STg00OAj1eTg00TFj3dTg00UTj7]Tg02LKj3\TP0j6:Tg00SJj1ZTg02mmj3[Tg03\@j1XTg00C1j2^Tg01FUj2_Tg02P>j2`Tg00ETj2aTg00Y1j7bTg00YUj8cTg00;oR0f1R2f0R33@p=4g00H2R4/a3p=2P2g00Z`R5g00[?R6P6g00[_R7P3g00\?Fbp=5P0P2g00Z9P3C8p=>f3R8P5P6P6P7f2R9P2P3Gcp=Cg008oR:#6R;#6#6R<#6#6#6R=#gR>#P%9<R<11>3'0%9;R;%9=R='AR?'3P011>2R@%L:#9RA'HRB,G>RC11>9RD,0<RE,43X80RFP01=B?PFP01A;A,0@1=3?/4EX80%f2%2@13@?'<P010D<RD11>8,0<,43X801Y;=R8134;%2=134?[[RE%2;RFg00\_RGAW;=2UW:R=%2?\G^:FRFP1f4,1>RG#2RH13G?RGf5,1>RI/0<RJ10<I'4P9f6,1>#2RIf7,1>/3?RKg00];RL#VRM%ULRN1T02RO%Q0RP%O0RQP01N0:R:170<RR5?0RSg013:A?0R:RRC8'51IQ7RTP3P9g009TRUg00:4RV'J1K39=@UVdAF042CMRVb3b6b7X00103<10<3'4^00P3f9,1>RUO1b2W9W1P2P3O2n2001000000120000000b5b41=D?P8PEP=PFP1PHPG%2J13J?'<P9g00D:RJ,B0RG%;J#;#;,B09E0Gg00nD'D'R=SLMPNPOPPPQ1704R4/>:,5Q%e6R:PQP0PRg00]gRR170;=d0>R;C8,5QP:PQP5P6P6P71>4S,5QP0PSPRP;C8,5QF]CCCCPTPVb3b6b7X00%2310<2/3?109<R;#213;?'<[[^00P3PUP9f8O3b2X9KX1IP2P3O2n2001000000121000000b5b49\D?E:b1PBP8PEP=PFPMPN%Z0PP170A,>4,5QPTPVb3b6b7%2AP3b2b5b49[@AE:PC%XBE:1^>B,1>1_>BE:1`2A,1>10<@'4eW;W<o"). Qed.

Lemma v_addi_0_1 : v_addi (Z_to_bv 64 0) 1 = Z_to_bv 64 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g007Jj11Tg00>Fj33Tg00<Mj22Tg00@Uj35Tg005bj10Tg006lj19Tg00C1j24Tg00:Tj18Tg01mZj27Tg008Uj26Tg00>`R0f0R1#1R2f1R3#1R4g00AYf2R5#1?331g00;oR6f3R7/25127333R8[12531251536%17?353[R9f4#1?375\8A5531P1n2001000000120000000W1W0W2P9^14^02^20P1g008oR1#0#0#0#0#0#0#9R0g00H2,40%81R1'71401R11201,66O4b3o"). Qed.

Lemma v_addi_0_64 : v_addi (Z_to_bv 64 0) 64 = Z_to_bv 64 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g007Jj11Tg00>Fj33Tg00<Mj22Tg00@Uj35Tg005bj10Tg006lj19Tg00C1j24Tg00:Tj18Tg01mZj27Tg008Uj26Tg00>`R0f0R1#1R2f1R3#1R4g00AYf2R5#1?331g00;oR6f3R7/25127333R8[12531251536%17?353[R9f4#1?375\8A5531P1n2001000000120000000W1W0W2P9^14^02^20P1g008o#0#0#0#0#0#0R1#9R0g00H2,40%81R1'71401R11201,66O4b3o"). Qed.

Lemma v_addi_Sj : forall j : nat, (Z.of_nat j + 1 < 2^64)%Z ->
  v_addi (nat_to_word j) 1 = nat_to_word (S j).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h01xh11zh24__x1h32b1h42b2h51nh61Hh72_Hh87__arithh94__ffh:8__varmaph;5__with<4cstrh=1jh>1yp;1p;2p;3p;<p;4p;7p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g00B4R1j13Tg00:Tj1<Tg00BTj25Tg005bj14Tg00;2j2]Tg00F0j2XTg007Jj17Tg00>Fj36j1VTg00<Mj21Tg00@Uj3CTg006lj1ATg05XNj1=Tg01mZj2\Tg00E5R2j1>Tg00C1j2:Tg00o0j22j1WTg008Uj28Tg01R4j1UTg01UPl<ITg01T?j1HTg00ETj2ETg00KTj1FTg00L4j1GTg00LTj2DTg00M2j1KTg00MPj1LTg00N^j2BTg00N;j2MTg010aj3NTg00Tij4OTg00Y1j7PTg00Pkj2QTg00QMj2@Tg00R9j3RTg00RXj4STg01RRj4[Tg011Dj8ZTg011aj3YTP0j69Tg01FUj2;Tg01XGl<?Tg00;oR0f1R3f0R436p=0g01=oR5P5P0P0P2P1P1f3R2g01Z6f2R6P3P4M<?p=TP5P0P0P0P1P1f5f4R1P2P6P3P4M<?p=J%34R7g008oR8#<R9'5%48R:#<%4:#4#4#4#4R:#<']'Xg00>`R;%74R<%73R=g00AY%76?63411261123'0R>[11631164'0%72?663[R?%71?626\>AC634P4n2001000000120000000W4W3W5P?^4=^3<^5;P4%A:R:%=6/\9R;%>6R<#=R=P0%36R?,::,1:R>/59R@,2:%>2#3RA,::,1:RB,04X10P012:?RC1549RD,2:/0BX10P0%3<RB,2:%32,2:/59,2:/04X10P015?9R2,2:12:A,04X10P0P0%W:RAPAP2PBP0\0/8A102B1022P0P0%V0RAP4X00REPA1034#UX>0X00P2P21802PBP2PEPE1807X05P<P2PDX00P6P?180?CTEJM<I%H6g00H2R2/E?g00];R<#F%G<1D03%K0%L0R<g00Z`g00[?R7P7g00[_R7P01B081M095N0R8g013:P8COg00\?FP1Q<7P4P6g009TR7g00:4R<'81@46=67<dAR023CSb9b:b;X2010DD^20P4%31O1b8b<C[GZ15C9,2:AY:?9E91::B,1:1;:BE9P>1;:?E91::@,1:1;:@E911:;11:='0eO4b6W7X=5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_signed_small : forall x : word, (bv_unsigned x < 2^63)%Z ->
  bv_signed x = bv_unsigned x.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hah11Hh24__x1h32H0h42Hxh57__arithh64__ffh76__sat0h86__sat1h96__sat2h:6__sat3h;8__varmaph<5__with=1xp;1p;2p;3p;4p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj13Tg006lj1@Tg007Jj1KTg00<Mj22Tg00:Tj19Tg006Gj14Tg00;2j2>Tg00F0j20Tg022Aj1ITg00AYR0j25Tg00JHj2;Tg00K0j3?Tg03UXj1VTg00ETj28Tg00KTj1UTg00L4j1TTg00LTj2STg00M2j1QTg00MPj1NTg00N;j2:Tg00N^j2MTg00Tij46Tg00OAj1JTg00TFj3HTg03V5j2FTg00UTj7GTg00Pkj2ETg008Uj2LTg00QMj2DTg00>Fj3<Tg00R9j3CTg00RXj4BTg03VXj3OTg01J1j2PTg00Y1j7ATg00YUj8RTg00H2R1f0R2'8p=1f1R3g00Z`R4g00[?R5P5g00[_R6P2g00\?FAp=7f3P4P5P5P6f2R7P3P2GRp==g008oR8#3R9#3#3#3#3#3R:#@R;#K12;2%99R9%48#4#4#4#4R<#9R='>R>'012;3R?%I3%1?%9:R:,>9R@,0?'51;9=1019RA%1=101>[[%19RBg00\_RCA?9=3UW0%1>\C^0B1;9:%1:101@[\AA?9:3VCX0B%1@\C^0BP0f6,2;R0#1100@%V>R0f7,2;RB'810B>'5f4f8,2;#1f9,2;/0@g00;oR@g00];RB#U%TB1S@3%Q@%N@RBP@1:@1g00Z9RC1M@8R8C6,7B%J5R:PBP@P8g00]g1:@9%@<5H@R<C6,7BR9P:PBP4P5P5P6P@1F@<PCP8C6,7BP9FGC=C=1EB6P2P7g009TRBg00:4R6'L1D27=<B6dAC@13CBb6b;b<W2%12103>1807107>'5[[^2@P2f;,2;P7f:O3b5W3W1P3P2O2n2001000000121000000b7b8b9b:b15O;1P;3=<@?eW4W=o"). Qed.

Lemma bv_signed_hi : forall x : word, (2^63 <= bv_unsigned x)%Z ->
  bv_signed x = (bv_unsigned x - 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p'0h01xh11Hh22Hah34__x1h42H0h52Hxh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__with<1eh=1zi001np;1p;2p;3p;6p;4p;7p;8p;5p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR1p4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g005bj11Tg006lj1:Tg007Jj1BTg00:Tj16Tg006Gj12Tg00;2j28Tg00<Mj23Tg00ETj20Tg01D\j1@Tg010Dj27Tg00>Fj34Tg008Uj29Tg012Sj2;TP1j6VTg01Ooj2UTg00?>j1TTg00JHj2OTg00F0j25Tg00K0j3NTg00KTj1LTg00L4j1KTg00LTj2HTg00M2j1ATg00MPj1CTg00N;j2DTg00TFj3ETg00N^j2FTg00Tij4GTg00Y1j7?Tg00OAj1ITg00YUj8JTg00Pkj2>Tg00QMj2=Tg00R9j3MTg00RXj4<Tg022Aj1PTg03WEj5QTP0j6RTg01J1j2STg008oR0#1R1#1#1#1#1#1R2#:R3#BR4%61R1%20#2#2#2#2R5#6R6'8R7f0R8,33R9'0g00;oR:f1R;,33R<%@3'7f2R=,33%62,81R2'794:8X=:17<2R>,9:1;3<P3P<g00>`R?g01H6R@743RAP?P3P?p-0P8g01PNRBg00\_RCn0110000020010000X<?g00DYP@P8EVPB1UB8b4W1%TAe1O16g00H2RA/5110A615A7[[10A1RBAN16;VCW210A7\C^2Bg00];RB#L%KB1H:;%A:%C:RBg00Z`RCg00[?R6P6g00[_R@PBPCP6P6P@P:1D:1%:55E:g00Z91F:0CGg00\?F?R0%I6P0GJ1>B@P8P=g009TR@g00:4RB'91=8==4@BdAM:A;C<b7b:b;X3:1078107;[^3:P8f4,33f3O2b6b8b9g00AY10A91592R915<2%P8P8n2001000000120000000X04P9^04P8P=O1b1DQER1S3;=4:>eW5W0o"). Qed.

Lemma c_lts_small : forall x y : word,
  (bv_unsigned x < 2^63)%Z -> (bv_unsigned y < 2^63)%Z ->
  c_lts x y = bv_ltu x y.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h01zh12Hxh22Hyh31xh41yp;1p;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006lj1?Tg007Jj1;Tg00<Mj22Tg00:Tj17Tg006Gj11Tg00;2j2<Tg00F0j2:Tg01J1j26Tg02>]j23Tg00>Fj34Tg008Uj29Tg05YIj25TP0j68Tg05BDj2>Tg02C7j3=Tg008oR0#0R1#0#0#0#0#0#?R2#;R3f1R4,22%71%10#1#1#1#1#7'<':R0g00;oR1f3R5,22R6g009TR7f0R81625R9'3f4,22R:/36R;34X01P1f2R<,22R=13:8=47;X01136=,97162<15<8E8P91554E81>5<A=25<547eX20W1X43W3o"). Qed.

(* [comment removed for export] *)
Lemma c_lts_neg_0 : forall x : word, (2^63 <= bv_unsigned x)%Z ->
  c_lts x (Z_to_bv 64 0) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hah11Hh24__x1h31mh41nh52H0h62Hxh77__arithh84__ffh96__sat0h:6__sat1h;6__sat2h<6__sat3h=8__varmaph>5__with?1xh@1zp;1p;2p;3p;4p;8p;6p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj14Tg006lj1ZTg007Jj1HTg00:Tj18Tg006Gj15Tg00;2j29Tg00<Mj21Tg00ETj2<Tg010Dj26Tg02>]j27Tg00F0j20Tg05ZFj2@Tg022Aj1YTg00AYR1j2UTg00JHj2?Tg00K0j3>Tg00KTj1OTg00L4j1MTg00LTj2LTg00M2j1KTg00MPj1GTg00N^j2FTg00N;j2;Tg00TFj3ETg00Tij4:Tg00OAj1DTg01V\j3ITg00YUj8JTg00Pkj2CTg008Uj2BTg00QMj2NTg00R9j3ATg00RXj4PTg01J1j2QTg05Zfj2RTP0j6STg00C1j2TTg05BDj2XTg00>Fj3WTg00Y1j7VTg009TR0f0R2g00:4R33Wp=3g00H2R4/<2p=2f1R5g00Z`R6g00[?R7P7g00[_R8P2g00\?FVp==g008oR9#4R:#4#4#4#4#4R;#ZR<#H%8:R:%59#5#5#5#5#8R='9R>11<2'<g00;oR?11<5%8;R;,9:R@'61724#3X@?P11752#3f2RA/05RB[105217A5#3[RCf3/7A#3\B1@52P2n2001000000120000000X3?X4?PC^3?^4?P211<ARC/6@P4%YA%2C10C@'U1?:=104:RC%2=104>[[%2:RBg00\_RDA>:=5UW0%2>\D^0B1?:;%2;104@[\CA>:;5VDX0B%2@\D^0BP1f7,1<R1#2101@f8,1</6@/04f4f9,1<#2f:,1</0@g00];R1#O%M11L?5%K?%G?R1P6P7P7P8P?1F?9R9g00]gR61;?:=E?<R:C:,=1%D7P?AI?9:P61;?4C:,=1GJ1C18P2PA1B031N2A#3dAA?45CPb8b=b>X2?102@165@/04[^2?P2f<,1<P5O2b7W5W1P5P2O2n2001000000120000000b9b:b;b<b1O3b11Q<51R52ES1T<4,X5#3eW6W?o"). Qed.

Lemma c_lts_pos_0 : forall x : word, (bv_unsigned x < 2^63)%Z ->
  c_lts x (Z_to_bv 64 0) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hah11Hh21xh34__x1h41yh52H0h62Hxh77__arithh84__ffh96__sat0h:6__sat1h;6__sat2h<6__sat3h=8__varmaph>5__with?1zp;1p;2p;3p;4p;7p;8p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj13Tg006lj1VTg007Jj1DTg00<Mj21Tg00:Tj18Tg006Gj15Tg00;2j2:Tg00F0j22Tg02>]j26Tg00ETj27Tg05[`j2>Tg022Aj1=Tg00AYR1j2UTg00JHj2<Tg00K0j3;Tg00KTj1TTg00L4j1STg00LTj2MTg00M2j1LTg00MPj1KTg00N;j2CTg00N^j2ETg00Tij4FTg00Y1j7BTg00OAj1GTg00YUj8HTg00Pkj2ATg008Uj2ITg00QMj2JTg00>Fj39Tg00R9j3@Tg00RXj4?Tg01J1j2NTg05YIj2OTP0j6PTg00C1j2QTg05BDj2RTg009TR0f0R2g00A939p=4g00H2R3/72p=0g008oR4#3R5#3#3#3#3#3R6#VR7#D1172%85R5%54#5#5#5#5#8R8':R9'2g00;oR:f1R;,171623#4X?:P116;2#4f2R<,7;R=[172;16<;#4[R>f3/6<#4\=1>;2P2n2001000000120000000X4:X2:P>^4:^2:P2117<R>P3%=<%0>%86R6,:5R=,2>'U1<581235R>%081239[[%05R?g00\_R@A;58;UW0%09\@^0?1<56%06123=[\>A;56;V@X0?%0=\@^0?P1f7,17R1#0121=f8,17#0f4f9,17#0f:,17/2=g00];R=#T%S=1M:;%L:%K:R=g00Z`R1g00[?R?P?g00[_R@P=P1P?P?P@P:1C:3g00Z91E:4CFg00\?FBR4%G?P4GH1A=@P2P<g00:4R@,I01J2<=90@dA@:3;C?b8b=b>X3:%02%0;[^3:P2f<,17P<O2b7W5W1P;P2O2n2001000000120000000b9b:b;b<b1O3b11N7;1O;2EP1Q73,R;#4eW6W2o"). Qed.

(* [comment removed for export] *)
Lemma c_lts_0_pos : forall n : word,
  (1 <= bv_unsigned n)%Z -> (bv_unsigned n < 2^63)%Z ->
  c_lts (Z_to_bv 64 0) n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h04__x1h17__arithh24__ffh36__sat3h46__sat4h58__varmaph65__with71nh82Hah91mh:1Hh;2H1h<2H2h=1bp;1p;2p;3p;4p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj11Tg006lj1=Tg007Jj1FTg00:Tj17Tg00<Mj23Tg00ETj24Tg006Gj15Tg00;2j2ETg00F0j20Tg00C1j2BTg02C7j3ATg02>]j2:Tg05ZFj2XTg00JHj2VTg00K0j3UTg00KTj1RTg00L4j1QTg00LTj2NTg00M2j1HTg00MPj1GTg00N;j28Tg00N^j2DTg00Tij4;Tg00OAj1CTg00Pkj2ITg008Uj2JTg00QMj2KTg00R9j3@Tg00RXj4LTg05BDj2MTg00SJj1?Tg00TFj3OTg05\@j4PTP0j6>Tg00>Fj3STg00Y1j7TTg00YUj8WTg009TR0f0R1g00:4R23Sp=2f1R3g00Z`R4g00[?R5P5g00[_R6P1g00\?FTp=6g00;oR7P3g00]gP1C;p=9f3R8P4P5P5P6f2R4P3P1GWp=<g008oR9#1R:#1#1#1#1#1#=R;#F%79R<13;1'413;3%7:R:%59#5#5#5#5R=#7R>'ER?'0P0g00H2R@,B;RA=A;4RB%21X=0g00AY1:31#21043RC[10311:43#2[RD1:84#2\C1X31P1n2001000000120000000X97X77PD^97^77P113;A13;81V:>RD10@:14@>10@?RC[[RE14@:RFg00\_RGAU:>3UW8R>14@?\G^8FRFg00];RG#RRH%QGRG1N73RI%H7RJ%G7RKP7187<g00Z91D79R9C;,6K%C5R5187@RL/99,6KC<1IK6R6P1P41J021K14#2dA@7@3CLR2b2b5b6X0714<110@3[^07P1f6,3;f5R@O2b1b3b4O3b:%2Be1MA4PAP4PDPEP>PFPHPG%?7PJ187:%==5O7R=,9L,6KP6P2b2b5b6PCP1b1b3b4PDPEP>PFPHPGPIPJPK199=,6KRKP5PKC<P6P2b2b5b6X07101?103?[^07P113;@P8O2b1b3b4CPE>W<W;W7o"). Qed.

Lemma errno_ret_range : forall e, (1 <= e)%Z -> (e <= 4095)%Z ->
  (2^63 <= bv_unsigned (errno_ret e))%Z /\ (bv_unsigned (errno_ret e) < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h04__x1h12Hah27__arithh34__ffh46__sat3h56__sat4h68__varmaph75__with81zh91Hh:2H1h;2H2h<6__sat5h=6__sat6h>1ep;1p;2p;3p;4p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR1p4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g00:Tj16Tg00ETj20Tg006Gj1>Tg005bj12Tg006lj1FTg03UXj1?Tg00o0j2VTg00;2j2CTg00F0j21Tg00AYj28Tg00;Oj29Tg00JHj2DTg00K0j3GTg00KTj1cTg00L4j1[Tg00LTj2YTg00M2j1XTg00MPj1WTg00N;j25Tg00TFj3ETg00N^j2UTg01V\j3TTg03C?j1STg00j^j3RTg010aj3QTg03V5j2PTg00Tij4=Tg00Pkj2NTg008Uj2MTg00QMj2LTg00>Fj3@Tg00R9j3KTg00RXj4OTg010Dj2BTg00dkj2JTg00BTj2ATg00OAj1fTg02LKj3eTP0j6;Tg03S[j3dTP1j6bTg03\@j1]Tg00C1j2\Tg00<Mj2HTg01FUj2ZTg05]9j1^Tg00Y1j7_Tg00UTj7`Tg00YUj8aTf0R1#>#>p=7g00H2R0/01p=3f1R2g00Z`R3g00[?R4P4g00[_R5P1g00\?F_p=4g00;oR6P2g00Z9P1C=p=<f2R7P3P4P4P5P2P1F`p=If3R8P3P4P4P5P7P2P1Gap=:g008oR3#6R9/01%>3#7#7R:#7#7#7#6R;,02P6%23R<#2#2#2#2#2R=#FR>%?7R?'VR@%6<R<%6:RA'CRB/01%6=R=,C<RC,11'8X86RDP619?CPD1D<=RE110<RF%3=110C[[RG%3<RHg00\_RIAG<=2UW1R=%3C\I^1HRJg00];RK#cRL%[KRK1Y62RM%X6RN%W6ROP6156<RP=E6>RQ1U63RR5T6RS%S3R3,56=R6Q5Q6g013:1P6RC='41NO5R5P1P7g009TRTg00:4RU'M1L17=@TUdAK602CORUb3b6b7X061BC11J3CRT'A%?15@6^06P1f5RVO1b2b4b51BC7RW/AT=@6?P61BC8RX/ATRT191CRY,0B11YC'8X86P619XCRYPDP6PXPD1D<A%3A110B[\FAG<A2VIX1H%3B\I^1HPEPGP=PJPLPKPMPNPO156;,<R,4ORH%f4R4PO1569/<R,4ORRP4%F:9E6P/<S,4OP6PSg00]gPQC=,4ORQ5IOC:C:P5PUb3b6b7X06101;R;1092R910BW11WCR2'8[[^06P1f8f6RPf7O3b2b4b5b<b=PYPEPGP=PJPLPKPMPNPOPHP4POPRP41560/<S,4O=IOQC:C:P5PUb3b6b7X06%3W/82\9\;^06P1PPf4PVO3b2b4b59eXCE;19TCAdX3CE;%?8P1Ebb9P@%]?E;1\>?,H>1Z>?E;%^7,H>R>,0B11>C'8eW;W:X>6o"). Qed.

Lemma errno_ret_signed : forall e, (1 <= e)%Z -> (e <= 4095)%Z ->
  bv_signed (errno_ret e) = (- e)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h01zh14__x1h21Hh32Hah42H0h52H3h62H4h72H5h83Hhih93Hloh:7__arithh;4__ffh<6__sat3h=6__sat4h>6__sat5h?6__sat6h@6__sat7hA8__varmaphB5__withC1qhD1rhE2H1hF2H2hG1ahH1ep;1p;2p;3p;6p;4p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR1p4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g00:Tj1BTg00ETj24Tg006Gj1GTg05^1j3rTg005bj19Tg00;2j2VTg006lj1^Tg05]9j1;Tg00<Mj27Tg00F0j21Tg00AYR2j2:Tg01J1j2JTg03UXj10Tg010Dj26Tg00o0j2CTg00C1j2TTg01FUj2STP1j6?Tg00;Oj23Tg03\@j1WTg00JHj2RTg00K0j3QTg02]hj2OTg02^Yj2NTg00?>j1]Tg00cmj2=Tg00dkj2ETg00BTj28Tg02]Aj2MTg02_:j2LTg02_aj2KTg02`Gj2PTg00KTj1\Tg00L4j1[Tg00LTj2ZTg00M2j1YTg00MPj1qTg00N;j2@Tg00TFj3pTg00N^j2oTg01V\j3XTg03C?j1nTg00j^j3jTg010aj3iTg03V5j2hTg00Tij4DTg00Pkj2gTg008Uj2fTg00QMj2eTg00>Fj3ITg00R9j3cTg00RXj4dTg00OAj1bTg00UTj7aTg02LKj3`TP0j6ATg03S[j3kTg05Zfj2_Tg00Y1j7lTg00YUj8mTf0R0#G#Gp=>g00;oR1f1R3;I0p=2g00H2R4/40p=5AI104p=FP3g00Z`R5g00[?R6P6g00[_R7P0g00\?Flp=<P1P3g00Z9P0CDp=Hf3R8P5P6P6P7f2R9P3P0Gmp=Ug008oR:#BR;/40%G:#>#>R<#>#>#>#BR=,43Ar930%9:R>#BR?%B<R<'VR@%9>#9#9#9#9R>#^RA%;9'7RB'4%B>R>,V?RC,1B':P2%;8,7AR8,4@118Cf4R8#;,JA%08'2P0f5#;,7A,4@f6#;,7A/1CP1f7R8#;R2,7A/6CRBf8#0RD,20X01P1%08R8,CARE160CRF/2DX01P11TA8,7ARG110CX01RHP0PE1SA8RIE?11ECP11TAD,7A14@0X01REP91CADRJ1SADE?14@JP1f9#0RJ/3CRDf:#0RK,2FX01P11CAJRLPHP3PD%WJRJE?11DCP11CAKPEP313KCRE%WKE?14@E1R?<RE114?RK%5<114@[[RD%5?RHg00\_RMAQ?<3UW3R<%5@\M^3HR@f=RN#0RO/OC%5O%5CROf?#0/3C#5[[1R?>RP%5>114CRQ[\KRKAQ?>3VMX3HR>PO\M^3HRHf@#0RM/NC%FCRR#]RSfA#0RT1=TC,EC13TC'8'2[1MTCfB#0RU/3CRV#511VC':\Q1LUC11C4RWfC#0RX/3CRY,1C14Y4':[1KXCfD#0RZ/=C#F\R1PZCfE#0R[/3C/2[\R1=[CR\P1fF#0R]/3CR^P1g00];R_#\R`%[_R_1Z13Ra%Y1Rb%q1RcP11@1?=p1AR?1o1:Rd5X1Re%n:R:,@1=j1?5i1Rfg013:Rg1h1dCD'<1gc7RhP0P9g009TRig00:4Rj'f1e09=IijdAc143CdRjb;bAbBX1116C0Ri1E:CRk'8Rl%00'2^11P0fHRmO1b:bDbCb7b6b5b4b2b<b=b>b?b@f;Rn,6C/8k%0n'2P1f<Rn,6CRo/8kRp130C/6C/20X01P113oCRq16CN/8k,2FX01RFP1PoPFPEPDP<P@f>#0RF/OCRk%5F13MC#5\O[ROPPPKP>PH1NTCRT1=UC,EC/8V,2U\SRS1MUCRU%5Y11YC':\QRQ1LXCRX13ZCRY,1C14Y4':\WRW1KZCRZ%F\\RR\1P[CR[12^]\RRR1=]CR]P1fGR^#0/3CRYP1P`P_PaPbP1AX1e?PgPfCD,<cPhPjb;bAbBX1116iC/2l^11P0fIRlO1b:bDbCb7b6b5b4b2b<b=b>b?b@PqPEPDP<P@PkPOPPPKP>PHPTPSPUPQPXPWPZP\P[PRP]P1PYP1P`P_PaPbPc1@1=,Hd,<c%b6RbPc1@1;/Hd,<cPbPcP5P6P6P71@14/He,<cP1Peg00]gP?CD,<cFaCUCUPhPjb;bAbBX11140=14;316C9R9#5119C':[[^11P0PlP^PmO3b:bDbCb7b6b5b4b2b<b=b>b?b@9`oCEA13pCAko:CEA%0nP0E?b2b9b8PLPJEAb9b8PGPIEA12B8e1JA21_23EAW8W9P3P0O2n2001000000121000000bGWFWEXH1o"). Qed.

Lemma c_lts_errno : forall e, (1 <= e)%Z -> (e <= 4095)%Z ->
  c_lts (errno_ret e) (Z_to_bv 64 0) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02H1h12H2h23Hloh32_Hh41ah51ep;1p;2p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g00:Tj13Tg00ETj24Tg006Gj17Tg05^1j3?Tg005bj11Tg00;2j28Tg006lj1;Tg05]9j10Tg00<Mj25Tg00F0j26Tg00AYR0j29Tg00C1j2:Tg05BDj2>Tg00>Fj3=Tg05^nj2<Tf0R1#7#7p=2g00;og008oR2#3/41f1R3%72#2#2R4#2#2#2#3'4f2R5??31%12R2#3R6%34'8R4%12#1#1#1#1R2#;R7%05'5R5'4%32,86R6,65'9P0f3#0,57R0,441606g009Tf4#0g00H2,:7'>g00:43=P1f5#0,57,44f6#0,57/66f7#0/<3W3W2P3P1O2n2001000000120000000b4W1W0W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma c_eq_small : forall x y : word, c_eq x y = bv_eqb x y.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h01xh11yp;1p;3p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg00=Yj31Tg008Uj23Tg008o#0#0#0#0#0#0#4R0#2R1g009Tf1f0510'3X11W0o"). Qed.

Lemma c_ltu_small : forall x y : word, c_ltu x y = bv_ltu x y.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h01xh11yp;1p;3p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj14Tg007Jj12Tg02C7j31Tg008Uj23Tg008o#0#0#0#0#0#0#4R0#2R1g009Tf1f0510'3X11W0o"). Qed.

Lemma c_eq_0_false : forall x : word, bv_unsigned x <> 0%Z ->
  c_eq x (Z_to_bv 64 0) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h01xh11yh21Hh33Hnzp;1p;2p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj1:Tg007Jj19Tg00<Mj23Tg00>Fj32Tg00?>j15Tg00?Wj24Tg00@4j28Tg00C1j27Tg05=Pj26Tg009Tf0R0g00A932p=1g008o#0#0#0#0#0#0#:R1#9g00;oR21310g00H2R332#5g00AYf1R4/40#1f2R5=224#5R6[A2240#51454#1[R7f3/45#1\61840P0n2001000000120000000X12X02P7^12^02P013151713R3,31P4O3b21643#1eW3W0o"). Qed.

(* [comment removed for export] *)
Lemma c_eq_0_of_u : forall x : word, bv_unsigned x = 0%Z ->
  c_eq x (Z_to_bv 64 0) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h02Hxh11xh21zp;1p;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006lj19Tg007Jj13Tg00<Mj21Tg00>Fj32Tg00C1j28Tg00?Wj27Tg008Uj24TP0j65Tg05=Pj26Tg008o#0#0#0#0#0#0#9R0#3g00;oR1f0R2,10g00H2R332P1P3g009TR41803R3,10,72g00:4R532X211445f1R1,10P2E51613=245eW0W1o"). Qed.

Lemma c_eq_0_true : c_eq (Z_to_bv 64 0) (Z_to_bv 64 0) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g008Uj20Tg009Tg00:4'0o"). Qed.

Lemma c_eq_neq : forall x y : word, bv_unsigned x <> bv_unsigned y ->
  c_eq x y = false.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h01xh11yh21Hh33Hnep;1p;2p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj19Tg007Jj18Tg00<Mj21Tg00>Fj33Tg00?>j15Tg00?Wj24Tg00@4j27Tg05=Pj26Tg009Tf0R0g00A933p=2g008o#0#0#0#0#0#0#9R1#8R2g00;oR3f1R4,11111033#5g00AY1440#2f2R5=334#5R6[A3340#51454#2[R7f3R8/45#2\61740P0n2001000000120000000X13X03P7^13^03P011181115P4O3b21654#2eW3X12W0o"). Qed.

Lemma c_eq_refl : forall x : word, c_eq x x = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h01xp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj13Tg007Jj12Tg05_gj21Tg008o#0#0#0#0#0#0#3R0#2f0,10W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_same : forall regs (r : reg) v, r <> 0 -> getr (regupd regs r v) r = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p'0h01Hh11bh21oh31rh44regsh51vi001vi011xp;1p;2p;3p;5p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8g003PR3p4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006Gj1CTg006lj13Tg007Jj15TP2j2BTg00CWj3<Tg00>Fj31Tg00?>j19Tg00C1j28Tg04BVj54Tg05``j42Tg0178R2j17Tg019Pj2:Tg008Uj2ATP3j5@TP0j66Tg00=Yj3=Tg05aPj4>Tg03ncj3?Tg03n1j2;Tg008o#0R0#C#3R3%00#0#0#0#0#3R0#5R1'B%53R4f1R5g00H2R6g00DY5<3R7514#9g009TR4g00A9P4P1f0R81806P2P1P1P3P1f3R6P3P1P6f2R0f4D4C2P8g05bHR9n10110100021010000n0100000020000=110X14%71R41:15P2P1P1P8P8P9n10110100021010000=110X241A15P3P1P0P3P1P0P5P6D4C2P3P1P0P5P6D@E6A=307P3P0P7P8C>E6A?605/;0=115eW0X51W3W4o"). Qed.

Lemma getr_other : forall regs (r : reg) v r', r' <> r ->
  getr (regupd regs r v) r' = getr regs r'.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p'0h01Hh12H0h23Heqh31bi001bh41oh51rh62r'h74regsh81vi011vi021xp;1p;2p;3p;5p;4p;7p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8p1003Pp4p7210P1p8g004IR3p4p7210P1p8p1005Cp4p710P1p8g005bj11Tg006Gj1CTg006lj14Tg007Jj13TP2j2BTg00>Fj30Tg00?>j17Tg00CWj3;Tg00=Yj3:Tg00C1j29Tg04BVj55Tg05``j42Tg008Uj26Tg0178R2j1ATg024lj4@Tg01Ooj2?TP3j7<TP0j6=Tg03ncj3>Tg03n1j28Tg008o#1R0#C#4R3%10#1#1#1#1#4R0#3R1'B%33R4f0R5f2R6504#7f1R7g00H2R8g00DY5;35:3g009TR9P9P9P1P51908R8P2P1P1P3P1f3R0P3P1f5R:f4R;f6R<D5C2P5g05bHR=n10110200021010100n0100000020000P9P1P5P8P2P1P1P3P1P0P<C2P5P=n10110200021010100R<n0100000020000501P51618%A1R8P3P1P6P:C2R9P2P1P1P5P5P=n10110200021010100=01<X48P2P1P1P9P5P=n10110200021010100,61P3P1P6P3P1P;P0P:D5C2P3P1P;P6P0P:A04;6R3P4P:P0P5C@A040:g01PNP0P5O1'?b2W1%73eF<E=n0110000020001b3A>;06/8718;7501eW0X64X81W5W7o"). Qed.

Lemma getr_nz : forall regs (r : reg), r <> 0 -> getr regs r = reg_get regs r.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "h01Hh11bh21rh34regsp;1p;2p;3p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006Gj1>Tg006lj12Tg007Jj14TP2j2=Tg00CWj3:Tg00>Fj31Tg00?>j17Tg00C1j26Tg04Alj23Tg008Uj25Tg00=Yj38Tg05aPj49TP0j6<Tg03n1j2;Tg008o#0R0#>#2R2%00#0#0#0#0#2R0#4R1'=%42R3f0R4g00H2R5g00DY5:2R6513#7g009TR3g00A9P3P1P41605f3f2R5'3R0n0100000020000=110X13f1R3,35R0,51A8236P2P3P6P4C9E<1;53=110eW0W2W3o"). Qed.

Lemma regupd_other : forall regs (r : reg) v r', r' <> r ->
  reg_get (regupd regs r v) r' = reg_get regs r'.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p'0h01Hh12H0h23Heqh31oh41rh52r'h64regsh71vi001vi011xp;1p;2p;3p;4p;5p;7p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8p1003Pp4p7210P1p8g004IR3p4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006Gj1@Tg006lj13Tg007Jj14TP2j2?Tg00>Fj31Tg00?>j15Tg0178R2j1;Tg05``j42Tg008Uj2:Tg04BVj57Tg024lj48Tg01Ooj29TP3j7>TP0j6=Tg03ncj3<Tg04Alj26Tg008o#0R0#@#3R3%00#0#0#0#0#3#4R0'?%43R1f0R4f2R5511#5%;0R6P3P0f1R7f4R8C2R9P2P0P0P4P4g05bHR:n10110100021010000P2P0P0P3P0P5f5C2P4P:n10110100021010000510X36P2P0P0P9P4P:n10110100021010000,:0P3P0P7P3P0f3R:P5P8D7C2P3P0P:P7P5P8A11:7R3P1P8P5P4C8A1158g01PNP5P4O1'9b2W1%53eF>E=A<8:5/671687510eW0X51X70W4W6o"). Qed.

Lemma regupd_same : forall regs (r : reg) v, reg_get (regupd regs r v) r = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p'0h01oh11rh24regsh31vi001vi011xp;1p;2p;3p;5p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8g002dR2p4p7210R3P1p8P3p10161p4p710p8g003PR3p4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj10Tg006Gj1>Tg006lj12Tg007Jj13TP2j2=Tg0178R2j1:Tg019Pj27Tg00>Fj31Tg008Uj25Tg04BVj56Tg05``j44TP3j58TP0j69Tg03ncj3<Tg04Alj2;Tg008o#0R0#>#2R3%00#0#0#0#0#2#3R0'=%33%:0R1f0R4,70P2P0P0P4P4g05bHn10110100021010000f1R2510X011504P3P0P2P3P0P2P4f2R1D6C4P3P0P2P4P1D8E9A<124/;2=104eX30W1W2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP2.
Ltac split_value_ifs :=
  repeat match goal with
  | |- context [if ?b then _ else _] =>
      lazymatch type of b with
      | bool =>
          lazymatch b with
          | true => fail
          | false => fail
          | _ => destruct b
          end
      end
  end.

Section WithFP3.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_single : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01bp;1p;2p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj18Tg007Jj12Tg00<Mj21Tg01>Nj17Tg00KTj16Tg00iZj33Tg01@3j14Tg00>Fj35Tg008o#0#0#0#8R0#2R1f0R2,10R0#7g00;o%619312#4;50eW0o"). Qed.

Lemma bv_wrap8_mod : forall z : Z, bv_wrap 8 z = (z mod 2^8)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01zp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg00:Tj11Tg00;2j23Tg00;Oj22Tg008Uj24Tg00;oR0f0g008o#0R1#1%01#0#1'3'2,40W0o"). Qed.

Lemma bytes_le_Z_to_le : forall k z, (0 <= z)%Z ->
  bytes_le_to_Z (Z_to_le_bytes k z) = (z mod 2^(8 * Z.of_nat k))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h61bh71zh81xh91Hh:1kh;1nh<3Hi8h=3Hikh>2Hzh?1ah@1ohA2HihB2IHhC4cstrhD1ihE1mhF1yp&0p;2p;1p;3p;6p;4p;<p;8p;Bp;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0g001jR1p4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p1005Cp4p710P2p8g05bmj2NTg01@3j1JTg005bj1YTg00:Tj1ZTg00>Fj3Fj1xTg008Uj2>Tg00;Oj2BTg05cjj1kTP0j6DTg00lRj25Tg00B4R0j1ATg00dkR2j21Tg006lk10=Tg00C1j2eTg00<Mj2dTg01>oj2LTg00^Nj2GTg00E5R3j1HTg00o0k201Tg00;2j2STg00BTj20Tg01R4j1vTg01Wdj4uTg01UPl<pTg01T?j1gTg00KTj1lTg00L4j1jTg00LTj2]Tg00M2j1iTg00MPj1hTg00N;j2QTg00N^j2\Tg00j^j3[Tg010aj3PTg00Tij4OTg00Pkk20BTg00QMk20ATg00R9k30@Tg00RXk40?Tg01RRk40>Tg00FLj23j1wTg00_mj2CTg010Dj2@Tg03U3j2cTg00F0j26Tg00ETj29Tg00IIR4j2bTg05dKk10<Tg00OAk10;Tg01V\j3aTg05djk30:Tg00g\j2VTg00eHk200Tg00m[j3~Tg00hEj3UTg00hnj2`Tg00iZj3_Tg00SJj1}Tg00_Oj4yTg03Yfj4MTg011Dj8zTg05eQj4{Tg01Tdj2|Tg00AYR5j2TTg03[1j4WTg05f6k102Tg01W?j4sTg00`Jk303Tg03[]k304TP1k605Tg05fUk106Tg01FUk207Tg05gOk208Tg01<Ok409Tg01XGl<^Tg01XllBoTg00Y1j7fTg00YUj8nTg00UTj7mTg00H2R1f0R6'9p=4f1R7%A6'1p==f2R81S76'Bp=:g00;oR9?F76p=8g01=oR:P:P9P9P3P0P0f3R3g01Z6P8P7P6M<^p=tP:P9P9P9P0P0f5R0f4R;P3P8P7P6M<^p=rP9P9P9P9P9P9P2P6P7P8P2P3P;P0f6R2f7R<f8R=f9R>MBop=qP7g00Z`R?g00[?R@P@g00[_RAP6g00\?RBFfp=E1S87,B3/36p=7g009TRC?F76p=;1B87/36p=XP9P7g00]gP6COp=KP3P?P@P@PAP8P7P6Gnp=2PCg00A9RDP3P8P7P6EDp=IP8P?P@P@PAP9P7g00Z9P6COPBFfp=<PCP;P3P8P7P6EDp=?P8P?P@P@PAP7P6Fmp=R%46R?1N87#Jg008oRB#YRE#ZRF%YE#YRG#ZRH/=85:7'8[^79RIX::P9P1AF916X791>91%ZBRJ,B7%k7EDg00D:RK/N7#J1=HK9:7F'8eX>?X79P9157HRL%A3RM,1HRN7:F&0=GRG1eG8'd1L6H'G%H;,=HRO9:8FRP'8X79P9201G7RQ158H%A;RR,1HRS7:F/LH,G6/8PX79RPP91SFHRT,B7PP10NHRN%H3RP#ARU,1HRV'8RW10MJRX,1HRY,8NP9P9%x9RZP6X89R[PZ1876#vXF9X89PNPN1>9NPVPYP[P[P[P9P9g01YR1176Cu,>9XE9X;9PHPH1>9HPUPXP[P[%A6,>9X8:PPPX106JRXX89P3PM1>9MCtErM:qM<p%g3%4Mg00];RM#lR[%jMRU1]97RY%i9RN%h9RZP91Q9HR\1\9BRB5[9R]=P9\R^g013:R_1Q9J9P9B9[9\CO'E20BZARAP6P8g00:4RJ,>C20A68=FCJdB0@917H0?RJb2b3b4X0911H6/0HR`11HX'8^09P6%A0RXO1b1bCH0>PWP910SH1B3T153H11HXRX7:F/LH'GRSA:3F6'8X79%g;%4R10XH9:3F1B0TRX/37150H1=H<7:FRR/LHRW/37Ra'CP2PF1=H=/0HP8C7Rb,;6X6C1@7HRc,3RAX2T8/C6/;bX6C1c7H167HRb19H7Rd'bP4168H19H8AX<T315<HPF1=H>Re1@3HRfC7'CP<PF10eHP3C7';P6163H13=;Re15>HPFf;Rg#ARh,1HRi1@0HC7Rj,C6P>PF10iHRiP0C7Rk';X6CRlPe13>0Rm/Cj/;6X6C1Cm6/;mX6C&0<e15=Hf:Re,=HRm7:FRj1@;HRn'3RoP[PUPYPNPZ1KB\,EZRp&0;@R@Aa9B\Rq1Q91Rr'K,EZC2PAPJb2b3b4X09166HRs16c1[^09P6P0P7O2R1b1:0:jnCIP=PF10mHRmP;C7P=PmP;%HKRn#H,V9Rj2009H1V9n5~91V9KRK5U95U9g00nDRn'`=_M[PUP91]98P7%}9CyRtPNPZPpP@PZ1\9ERE9<ZrP@A[9\ERu=P9\,KB,EZRvC2C2PAPJb2b3b4X09X59%48Rw11H3/0H,68[\s^09^59P6PhP0P7P2O4b1CMD?AX=T;RTP=PHP;P[PUPYPNPZPpP@PpC2PAPJb2b3b4X09Pb\s^09P1b1CMD?W<P6O119H3PlPo1;6kX6C1c;m16;m19m;'bP4160i19i015eHPFf<Ri,=HR01@2HC7PePF100HR0P2C7';P6162015gHRe1@<HR4'3RmPiPFf>#ARk,1H/0HP=C7,;6X6CRl104HRs,3gPl13g<1@=H/0H,3i/;6X6CP9PC%wgRiPiPsP<PC\9/>iP[PUPYPNP9AP9q\P_PBCO,EZPAPJb2b3b4X091@6H/0H/86^09P6P=O1b1GzPgPFf=,=HR_/0HRiP<C7RsPgPiP<P[PUPtPNPZPvP@PvC2PAPJb2b3b4X09X5911H7/0H,66Rb11H8Rp/0HRh,67[^09^59P6PkP=P7O3Rxb1CMD?PmPgPHP4P[PUPYPNPZA<Z\BRmP@A<ZrqC2PAPJb2b3b4X0919H6Ry%4c[^09P6P=P;O2b1C{D?PePFP_P4C7RzPeP_P4P[PUPtPNPZPvP@1Kqu,EZC2PAPJb2b3b4X09X5916cp\b^09^59Pxb1CMD?W=P6O11902PlAFCD6X6C1>CDPsPgPiP<AU9Kj/`n,|K=_M[RMPUPtPNPZA<Z^ERKP@PZA<ZrBRBP@A<Zr^=RZKC2C2PAPJb2b3b4X09X5919`7R`%47R^%4h19h3'T[[^09^59P6P=PkP7P>O4R>b1CWCIPzPeP_P4PMPUPtPNPZPKP@PZPBP@A<Zr]Aa9E\9<Z]5RZC2C2PAPJb2b3b4X09X59%4p19pf'T\^\`^09^59P>b1CWCIW=P6O1n200100000021100011000b@1CDo&02oD?PTP=PHP;P[PUPYPNPZPmP@A<Zr\=RZmC2PAPJb2b3b4X09%4H/Td\y^09P1b1CWCIW<P6O1n200100000021100011000b@PaPRPHP7P[PUPYPNPZPBP@PBC2PAPJb2b3b4X09RJP^\?^09RAP6P8P7O2b1CsD?1GXW/37B03XW7D?XA?XD9604Sb9POP6J05b9PQ&067ED1eG7,dG207G7ED1N3L#JP8PLP51576#4Pw[1587#4\^R^1538#4\w20876P6n2001000000120000000X;9X?9P^^;9^?9P6P8PHPJPAP6P3P8O2b1O3b9O2ED1NP7#JA:7FV'8eX>?X79XBIX::P6H09X::o"). Qed.

Lemma bytes_le_N : forall k (v : word),
  bytes_le_to_Z (word_to_le_bytes k v) = (bv_unsigned v mod 2^(8 * Z.of_nat k))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01xh11Hh21kh31vp;1p;2p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj10Tg006lj1?Tg007Jj1;Tg00<Mj23Tg00ETj24Tg00:Tj11Tg00;2j22Tg00F0j2:Tg022Aj17Tg05h6j36Tg05i4j25Tg01@3j18Tg00B4j19Tg00dkj2>Tg00;Oj2=Tg00>Fj3<Tg01=og008o#0R0#0#0R1#0#0#0R2#?R3#;R4f1R5f0R6,33R7g00AYg00H2R8/47R9%10R0%12'2,:71335,48%76P5n2001000000120000000X04P9^04P6P5O1b136g00;o1556#8%11%95'>,20,=73<eW3W2o"). Qed.

(* [comment removed for export] *)
Lemma n_to_le_8_spec : forall v : word, word_le8 v = word_to_le_bytes 8 v.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01vp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R1P0p8P1p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p1005Cp4p710P0p8g005bj11Tg006lj13Tg007Jj12Tg00L4j14Tg00E5j10Tg05i4j26Tg008Uj25Tg008o#1#1#1R0#1#1#1#3#2%30#2#4g00D:#0#0#0#0#0#0#0#0f0'6'5W0o"). Qed.

Lemma bytes_le_n_to_le_8 : forall v : word, bytes_le_to_Z (word_le8 v) = bv_unsigned v.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01lh11vh21zp;1p;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R1p8p1002dp4p7210R2P1p8P2p10161p4p710p8p1003Pp4p7210P1p8p1004Ip4p7210P1p8p1005Cp4p710P1p8g005bj11Tg006lj19Tg007Jj14Tg00L4j1<Tg00E5j10Tg05i4j2@Tg01@3j18Tg00<Mj25Tg00>Fj36Tg00:Tj12Tg00B4j1;Tg00dkj2:Tg00;2j23Tg00;Oj2CTg022Aj1BTg02LKj3ATg05j<j2?TP0j67Tg05k4j1>Tg05klj1=Tg008o#1R0#1#1R1#1#1#1R2#9R3#4%91#4#<R4g00D:#0#0#0#0#0#0#0#0R5f0R6'@R7g00;oR8%86f1,53R936X04P81536R3%20R0%21%;5':'3'CA6869X28%22,30%B65A3%871?56E7%>6%=6E7W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_error_skipn_cons : forall {A} (bs : list A) d, (d < length bs)%nat ->
  exists b, nth_error bs d = Some b /\ skipn d bs = b :: skipn (S d) bs.
Proof.
intros A bs. induction bs as [|x bs IH]; intros d Hd; [cbn in Hd; lia|].
destruct d as [|d'].
- exists x. split; reflexivity.
- cbn [length] in Hd. destruct (IH d' ltac:(lia)) as [b [H1 H2]].
exists b. split; [exact H1|]. cbn [skipn]. exact H2.
Qed.

Lemma u_add1 : forall a : word, (bv_unsigned a + 1 < 2^64)%Z ->
  bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h02Hah11Hh24__x1h32H0h47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__with:1ah;1zp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710R1p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p105o8p6041000R3p1060:p4p710p8P3p101QRp4p710p8P3P1p8P3p1060Yp4p710p8p1005Cp4p710P2p8g005bj14Tg006lj1[Tg007Jj1ETg00<Mj20Tg00:Tj19Tg00BTj23Tg00;2j2LTg00F0j22Tg00CWj3CTg00o0j2:Tg00>Fj3<Tg00;Oj2?Tg022Aj1>Tg00AYR2j25Tg00JHj2VTg00K0j3UTg00KTj1TTg00L4j1RTg00LTj2KTg00M2j1JTg00MPj1HTg00N;j28Tg00N^j2DTg00Tij46Tg00OAj1FTg010aj3GTg00TFj3BTg00UTj7ITg00Pkj2ATg008Uj2@Tg00QMj2MTg00R9j3NTg00RXj4OTg02LKj3PTg03\@j1QTP0j6=Tg01;5j3STg01o@j3ZTg00ETj2YTg00Y1j7XTg00YUj8WTg00H2R0f0R3'Yp=1f1R1g00Z`R4g00[?R5P5g00[_R6P3g00\?FXp=7f3P4P5P5P6f2R7P1P3GWp=;g008oR8#4R9#4#4#4#4#4R:#[R;#E10;3%98R<'3%99R9%9:R:'LR='2g00;oR>10;1R?g00DY9C;<R@,0;'3,:;10;7/3<9<>3X;>RAP>13?<RB/?=PA%>1%1?12?='51V9:1209%1:120=[[%19R?g00\_RAAU9:1UW0%1=\A^0?P2f4,0;R2#1122=f5,0;/3<R2#1122='5P7f6,0;#1f7,0;/2=g00];R2#T%R21K>1%J>%H>R2P>18>0R?g00Z9RA1D>8R8C6,72%F5R:P2P>18><9G>8R8g00]g18>9=B>;C6,72R9P:P2P4P5P5P6P>P?PAP8C6,72P9FIC;C;1A26P3P7g009TR2g00:4R6'@1M37=<26dAN>01COb5b8b9X2>%13131</2=137<R<#112<='5[[^2>P3f9,0;P7f8O3b4W3W1P1P3O2n2001000000121000000b6b7b19PB=1:;B%QBE=AS;1@,0;AZ;1@E=W0W:o"). Qed.

(* [comment removed for export] *)
Lemma rdn_stack : forall segs sp bytes k addr,
  (bv_unsigned sp <= bv_unsigned addr)%Z ->
  (Z.to_nat (bv_unsigned addr - bv_unsigned sp) + k <= length bytes)%nat ->
  (bv_unsigned sp + Z.of_nat (length bytes) < 2^64)%Z ->
  rdn segs (stack_to_mem sp bytes) addr k =
  Some (firstn k (skipn (Z.to_nat (bv_unsigned addr - bv_unsigned sp)) bytes)).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "p'0h04__x1h14__x2h24__x3h35Hlen0h47__arithh54__ffh68__varmaph75__with84cstrh95cstr0h:4__p1h;6__sat3h<4__x4h=4__x5h>4addrh?1bi001bh@1nhA1HhB2H1hC2H2hD6__sat2hE6__sat4hF1mhG1xi011xhH2z1hI2z2hJ1khK2H3hL2HahM4HlenhN3HnwhO3HsphP4__p2hQ6__sat5hR4__x6hS4__x7hT1ohU2z3hV3HlehW3HlthX4HnthhY5HskiphZ3Hu1h[2IHh\5bytesh]1eh^1lh_4segsh`2spha1yi024restp%0p&0p;1p;2p;4p;3p;5p;<p;6p;Bp;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710R2p8P0p1000np4p7210p8p1001Mp4p710R0g001jR3p4p710p8P0g002FR0p4p710R4p8p1002dp4p7210R5P4p8P5p10161p4p710p8p1003Pp4p7210P4p8p1004Ip4p7210P4p8g05o8R5p6041000R6g060:R7p4p710p8P6p101QRp4p710p8P6P2p8P6g05mFR6p4p710p8p1005Cp4p710P4p8g00L4k102Tg005bj1ZTg006lk109Tg007Jk105Tg00<Mj20Tg00ETR4j29Tg0614j2KTP1j27Tg061KR1j2PTg00B4R2j11Tg00BTR8j23Tg00:Tj1zTg00;2k20fTg00F0R9j28Tg0178R:k10;Tg061ej2Yj3yTg018_j4ITg05lhj3CTg008Uj2qTg00>Fj35k104Tg00E5R;j14Tg010Dj22Tg062fR<j1@Tg05mdR=k20OTg01V5j4pTg01T?j1STg00JHk20eTg00K0k30`Tg00g\j2`Tg00KTk10]Tg00SJk10\Tg00M2k10[Tg00MPk10ZTg00N;k200Tg006Gj1~Tg00OAj1}Tg00N^k20:Tg00Pkk20YTg00QMk20XTg00R9k30WTg00RXk40UTg01RRj4{TP5k40TTP6j3HTg019Pj2OTg00AYR6j2NTg05n<R5k20STg01;Zj2eTg00CWk30PTg01;5j3ATg00iZj3GTP7j3dTg063Fj2FTg063ck20NTg02>]j2LTg05ZFk20MTg03C?k10LTg00f1k20KTg03S2j3oTg01V\j3jTg00j:k50ITg00TFk30HTg064Ck20GTg05TJk20FTg03QIk30ETg01UPl<tTP3k60DTP0j6lTg01<Ok40QTg0657k20RTg01XGm<0<Tg01XlmB0@Tg065Tk20VTg00IIk20?Tg00hEj3|Tg00hnk20>Tg00LTk20dTg00_Ok40cTg00Tij4gTg00Y1j7iTg010ak30bTg00YUk801Tg00Ock60_Tg00UTk70=Tg00PGk70aTg0666k60^Tf1R0f0R3'2#@p=;f4R7f3R>f2R??C033dp=R1O0395>?p=?Ad?03,O>p=rg00H2R@00R3p=6g00;oRA/q3p=:PAg01=oRBPAPAP<P7P2P>g066ZP?P0P3N<0<p=hPBPAP=P2P9g05nVf5R9P7P>P?P0P3M<tp>0J13?0/93p=JPBPBPAPAP;P2P2P>g01Z6P?P0P3N<0<p=bPBPBPBPAPAPAg067GP2P2P2P8g067gP9P7P>P?P0P3NB0@p=mPBPAP1P2P4g068JP9P7P>P?P0P3M<tp=f19@3p=<20V@3p=]18@7A5A>?'N190@A5A3@'N+0?p=M18@3p=sA|A03p=Eg00];R4g00nDR1-0>0;G3p=[20dA3p=_PAP?P0P3H0cp=>20:A3p=^P?g00Z`R8g00[?R;P;g00[_R=PAP0g00Z9R<P3Cgg00\?RCFip=BB0bA03p=DPAP0g00]gP3Cgp=XP0P8P;P;P=P3PCFip=Wf6RDP8P;P;P=P9P7P>P8P;P;P=P?P0P3L01L01p=Tg009TREg00:4S00753p==AC?039G7>p=UP>P8P;P;P=P?P0P3L01p=xP0P8P;P;P=P3J0_p=wP7P8P;P;P=P>P?P8P;P;P=PAP0g013:RFP3CgPCFiK0=p=QP?P8P;P;P=P0P3K0ap=k190@A5A3@'Np>06A5A?0,N>00?3p=vP0P8P;P;g068lS01P3PCFip>03P?P8P;P;P0P3J0^p=uA5A03p=VA|A039|A?p=\20>31p=aAG4039G4?p=nP?P8P;P;P=PAP0PFP3CgPCFip=cP?P8P;P;P=P0P3K0=p>07PAP0P<P3Cgp>08AG403p>0CA5A3@,N0p>0B193@p>0Ag01=0$02g008oR<#ZRC#ZS02#ZRF#Z#Z#ZR1$09RG$05RH&09F$05RF$02RI10G7RJ10G3RK'910G0RL10G9RM';/K?17F7RN'P10GDRO17F9RP#1'3%zCRQ%z1R1+0fRR'8&0;IRSf8RTf7RU/YDP>P7CIPIPFP7PF10G>RV10GURW';PDDRC?[[[^>HS03XJB19VK1;LJg00D:RX'K17F>'P%1N,3M/8RPIPFPX1;VO=CF9CrRN,qSPU1YD9P>PXCI=5SNeWNWMWOX>HQ0319MK1;LO%4>'K/PP17FD#1,3W/8RPFPU10GTRP,2VRV#@RL17FURN-0OL%6VRY%1NRZ'8PLPYP3XGAS04%63XGAR[PVPV%:VDhR\PNPZ%:ZR]J0J%49S05,KLR^/PN%19R_%z<R`'3=JYZRYP^P[PVO1RV133`XGAR^P_O1Ra'3PLPVP\Q05PaP^P9P_%:_CbEmPNPZP]EfP0CpPY17FTRY#S%1Y#<%SU%1U#<f;RY,0GR],2ORO#]PO%6ORZPOPOPZDMf<RZ,0GS06,2WRW#6PA20eQ1RO%sQ%<1%sR[[RN%<QR_g00\_RaB0`Q10UWLR1%<R\a^L_R_%4XRa#4S07,`AS081`AaS091`AXRX'ES0:'ES0;&0]4Ra'[S0<&024R4%_?S0=%_>S0>&0\AR\7>>7>0&0[ARV&0ZARb200A@Rc%~C#^S0?5BbS0@%};RdPb20:A<ReQ0?200A`Rf'DS0A'D%^CRC5BbPd1XeC,WbFT20Yb=R=P3P?Q00,qE20X3?#=dB0WA@0H0UR@b5b6b7X0AX1AX2A%<?13>`S0B=J0?18?>[[^0A^1A^2AP3f=Rg#1f?Rh,7F#1P>P9PUO5b4bDb;bHbBb9b8b3C{H0T&0;FRif9Rj,0GRk,;JRJ9HFT1OF3Rl35ACFJTPFP3PF%4JPTDU55I'NX?F-0SFP5PFf:R5,0GRJ,;MRM9HFj=5ilACFMjRmPFP3PF%4MPjDU55I'NX?FPSP:PFPSP:PFPiAy5j9Pl1eY9n10110100021010000P:PIPSPZ1YY5g00DY:0PG`RM9AGDPTCIAGF03,OIS0C%}IRnn10110100021010200Pnn10110100021010000PI%4U=dFmC?P3%@WRW9HFY=5ilACFWYPFP3PF%4WPYDU55I'NP6Pi10GgRW,;PRP9HFZPFP0C?ACFPZPFP0PF%4PPZDU55IPSP:PFPSP:PFPif>RP?ygjPl1ehjn10110100021010000P:PIPSf@Rm1YhPAAG5MPZCIQ0CPnn10110100021010200Pnn10110100021010000PIPF%4YPF10GPS0D,;kPgDRC?P3Pi10GhS0E,;J9HFPPFP>C?10GmRJ,;]R]=CFhPFP7PF%4]PhDU55IP61F03#=19?0R][19031F?0#=[Rk1F>?#=\]20N03P3n2001000000120000000XFAX@APk^FA^@AP3fBRk,0GR]PW12W]Ro#@Rp%4hRq'KRrfARs,7FRt'P%6o%1hRu/3`%1tRv3JRwPrP[PoO1RrP^PuO1Rx'3PpPrQ04P[PoPo%:oDhPqPxP^PhPu%:uCbEmPtPv%:vEfPYCpPw17FkRw#S%1wRY#<%Ss%1sRt#<fERu,0GRx,2JRJ#]PJ%6JRqPJPJPqDM10GsS0FfFS0G,0GRq'2Rr#6RpPAPOPNP1P_PaP4Q0=?>0\S0HPVPbABbeCS0IPdQ0ICxP=P@b5b6b7X0AX1A1930190?[^0A^1AP3PxfJS0J,0GS0KfDRyO3b4bDb;bHbBb9b8b3O3bAQ0FQ06'F#=PEQ00PSP:PFPSP:PFPiPEPiP3PEPiQ0DfCRz,0GS0L'2R{/LYS0M%@{R|9HFkS0N%}FR}n0100000020000P}n0100000020000Pl1eyPn10110100021010000P:PIPSPuPEPi1FxKPEPi12KxR~17FyS0O#1S0P'L%@~9HFyP}n0100000020000P}n0100000020000X>HAAGhMS0QPsCIQ0CPnn10110100021010200Pnn10110100021110000PIPF%4mR~PFP|PkDRC?X?EP61L03#=18?0R6[18031L?0#=[S0R1L>?#=\620M03P3n2001000000120000000XFAX@AQ0R^FA^@AP3P{PY1K|~S0R/Pw%6{%1mR6/3`;JYS0SQ0RP[P{O1S0RP^P6O1S0T'3P|Q0RQ04P[P{P{%:{DhP~Q0TP^PmP6%:6CbEmPwPY%:YEfPZCpS0TQ0S17FzRY#SS0R%1YRw#<S0U%SkS0V%1k#<S0W%]rS0XPrPpPrPrPpDMS0YfGS0Z,0GS0[,2]Rp#6S0\PAPOPNP1P_p-0R6Q07#4R~#4S07,`AR{&0L<-0KAR|1`A~R~5oAS0]Q0;'ES0^'EQ0^/[a'[P4%_7S0^?>?\%_9S0_?>>\7>0PVPbPb1wbUS0`PbQ02#^R\AjAeCS02DQPbQ02=BbcPbP\PcDQ5kbPdPbQ0@PdPbQ0A,D\%~<S0@#^R<5BbPdQ02/X<S02,WbCxFTP=P@b5b6b7X0AX1AX2AX<AX=AW:P9P>1230S0aQ0a006>Cv%<913D`=J9712>7/89[[[^0A^1A^2A^<A^=A^:6P3fKS0b,0GS0c,2q#sfHS0d#1P>Q0J,7F#1S0JQ0cPqP7P9PUO9b4bDb;bHbBb9b8b3O3bA1Lov#=PEQ00P:PFPSP:PFPiPEPiP3Q0E10GyS00'2Rv#@Ro9HFzP}n0100000020000Pl1euhS0En10110100021010000P:PIPSQ0GPEPi1FqKPEPi12KqRK17Fu#1'L%@K9HFuP}n0100000020000P}n0100000020000X>HAAGmMS0GPkCIQ0CPnn10110100021010200S0ePnn10110100021110000PIPF%4sR}ACFozS0fCrRK55SX?EPi1OFUP:PFPSP:PFPiP3PlQ0En10110100021010000Q0ePnn10110100021110000=5SKXTiQ0TQ0SQ0RQ0UQ0VQ0WQ0XQ0YQ0\PAPOPNP1P_Q0<P4Q0=Q0>7>0S0=PVPbQ02-03bPbP8P;P;Q01I0IR;5ubPdPb1DC<200AQ>0HAGRQ'X,WbPd1DefS01/XQ,WbFTP=P@b5b6b7X0AX1AX2AQ0a/L?#=13?>/8R13?`S0a/8R[[^0A^1A^2AP3Q0JQ0cPqPTPzO5b4bDb;bHbBb9b8b3-0GPAAGPM,0GQ0D/3`'VPSPIPFPsQ0Q,0GQ00'2Rq#@R8=CFzCrPSP:PIPSP3AGF53,OIPnn10110100021010200PIPF%4kS0DPF%@JS0cPyDRC?XTSPIPFPTPF%4oRJPzDUPSPFPkPFQ0G,0G/;xS0GPyDR9GFj,OIPIQ0D=dF3C?X^IA5BJ8S0J%6vRK/3`S02%6qRE'VPBPA&04BP2&04A%10%13'VA5B0320F0340EXaBXGBPJQ02P^PoPKQ04P[PvPv%:vDhRJCbP8PEQ04P[PqPq%:qDhS04M<t1Ko}Rq/PY13t`=JKwRKPqP[PvO1RvP^PtO1R['3PoPvPJP}P[P^PsPt%:tS02CbEmPYPw%:wS0<EfPgCpR^PKQ0O#SR[Q0P#<R}%SzRJ%1z#<RvAAGkM,0GQ0['2Ro#]S0PPo%6oRqPoPoPqDMS0OAAGzM,0GQ0d,0GS0d'2#6S0YPAQ00fIRq,0GS0X'2Ro#]S00Po%6oR2PoPoP2DMS0WQ0K,2x#6S0KPAPOPNP1P_Q07#4,`ARx9oA|?\~XQ089oA|R2Q095\{#aRoQ0]Q0:,E2S0:5\{#aAoA|{S09Q08/EX7\~R|,Ex#aS08%a|R|Q0]1E2X5\{Anooa'[3n3n'[P4Q0^Q0_7>?Q0>7>0PVPbPbAjA\<Ro,Xc,WbPbPePoDQABbocAcbecRo607b5kbPdPbPbQ0`PbPCQ0@#Z#^R{=jA<R2DQPbABb2cPbPCPcDQ5kbPdPb1D\f9cb{PdPb208<\-03b=ub;PdQ01=cbCFTFTP=P@b5b6b7X0AX1AX2AX<AX=AX:612>?R2P3P2P2P3DMPDP?129>R22062?Cv139`,VD1F9D#=137`/V9[[[[^0A^1A^2A^<A^=A^:6P3AAGqM,0GRqfN,0GR2'2RX#sS01PqQ0XP2P9P>P7PDP5PZO:b4bEbQbUbKbIbCb9b8b3C{Q0JPBQ0c#4S0cPSPFPzPFP3PuDR9GF5,OIPI%4zPFP5PF%@r#4PuDU5dFC?X@BPIPFQ0DPFPjPFQ0cPyDUCr,qSQ0GP3J0DbAQ0fP>ElPu1YyzQ0QPsCIPmQ0QP^PKP[P}PJPv%]pS0QPpQ0\PpPpQ0\DMS0\Q0LQ0d'2#6RpPAPOPNP1P_Q0:/[aP4Q0=PVPb1D<f9cbCPdPb208e<-03b=ub;PdQ0IFTP=P@b5b6b7X0AX1AX2AQ0a,V01F0>#=19?>[[^0A^1A^2AP3Q0[Q0Z=AGM,0GfL,0GR;PTP5O5b4b;bEbIbCb9b8b31K8sRu/PY13EtRr/9wPuPrP8PEQ04PsPtQ02EmPYPwQ0<EfP^PKP[P}PJPvQ0PQ0OQ0YPAQ00Q0WQ0KPAPOPNP1P_Q09Q0;7\~R~,Ex#aQ0800Ca,[~5n|P4Q0^%_D7>?Q0_%_U7>>7>0PVPbPbQ0?=jA\R|,Xc,WbPbQ0@#~#^R~P|DQPbABb|cPbP~PcDQ5kbPdPbPb1wbjPbPeAjA{\DQ1wb5>07bo5kbPdPb1DCf,D~=Bb<PdPbQ0A9cb{Pd1DeCRC=Bb<FTFTP=P@b5b6b7X0AX1AX2AX<AX=AXRAXSAX:6XP6127>R<PDP<P<PDDMPTP012D720Bj0CvQ0B=JT713U`,VTAJ79D[[[[^0A^1A^2A^<A^=A^RA^SA^:6^P6P3&0AXQ01P>PqQ0XP2fM,7F#1Q0b#1P9P7PDPjP5O=b4bEbQbUbKbIbCb9b8b3C{P^PKP[P}PJPvQ0QQ0\PpPAPOPNP1P_PaP4Q0HPVPb1XCQ,WbRbPdPbCxP=P@b5b6b7X0AX1A1330/8R130?/8R[^0A^1AP3Q0b,7F#1P;PyO3b4b;bEbIbCb9b8b3O4ElbZQ0NP>ElQ0MP3ElbW1F]WP3ElbVPSP:PFPSP:PFPiAysmZPl1ekZn10110100021010000P:PIPSPz1YksAAGgMPhCIQ0CPnn10110100021010200Pnn10110100021010000PIPF%4PPFQ06Q0F';PmDRC?eWYWXP0P3O2n2001000010121000000WAX?FP0P3O2n2001000010121101000b]PSPj1YTUP>Q05CIPIPFQ05PFPLPUDRC?eWNWMWOX>HW[XJBP3H0QXJBW\W`W_o"). Qed.

Lemma rdn_ext : forall segs k m1 m2 (a : word),
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k)%Z -> m1 x = m2 x) ->
  rdn segs m1 a k = rdn segs m2 a k.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "p'0h01xi001xh14__x1h24__x2h31ah42m1h52m2h64Hexth73Hnwh84Hnw0h92IHh:7__arithh;4__ffh<6__sat3h=6__sat4h>8__varmaph?5__with@4__x3hA4cstrhB1khC2HahD4__x4hE1ohF1yhG1HhH3Hu1hI2HxhJ3Hx0hK2k'hL1mhM1ni011nhN4segsi021bi034restp%0p&0p;1p;2p;3p;4p;6p;<p;Bp;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710R1p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p105o8p6041000R3p1060:p4p710p8P3p101QRp4p710p8P3P1p8P3p1060Yp4p710p8p1005Cp4p710P2p8g00L4j1ZTg005bj1FTg006lj1`Tg007Jj1^Tg0178R2j1fTg00<Mj23Tg00B4R3j11Tg00:Tj1TTg00;2j2lTg00ETR1j24Tg00BTR4j20Tg00>Fj35Tg018_j42Tg008Uj2KTg00E5R5j17Tg019Pj2dTg01;Zj2LTg00CWj3tTg01;5j3=Tg00iZj3[Tg00OAj1_Tg00F0R6j28Tg01R4j1GTg01Wdj4iTg01V5j4ITg01T?j1STg00JHj2hTg00K0j3gTg00g\j2MTg00hEj3OTg00hnj2eTg00KTk100Tg00LTj2\Tg00SJj1~Tg00_Oj4RTg00M2j1}Tg00MPj1|Tg00N;j2YTg00N^j2PTg00TFj3yTg00Pkj2xTg00QMj2wTg00R9j3vTg00RXj4bTg064Cj2sTg006Gj1rTg00Tij4NTg01RRj4XTg00AYS00j2>Tg069Lj6VTg03C?j1qTg00f1j2pTg03S2j3oTP0j6aTg022Aj1nTg01<Oj4uTg01XGl<]Tg01XllBmTg01UPl<cTg00Y1j7kTg010aj3zTg00YUj8{Tg00UTj7jTf2R0f1R7'0f0R8'4p=:1878,>0p=J1078,80p=D1407/>8p=?g00;oR9/K8p=6g01=oR:P:P9P9P5P3P3f3R5g01Z6P0P7P8M<]p=@P:P9P9P9P3P3f5R3f4R;P5P0P7P8M<]p=AP9P9P9P9P9P9P4P8P7P0P4P5P;P3f6R4f7R<f8R=f9R>MBmp=BP9P9P1P<P1P4P3P;P5P0P7P8M<cp=Hg00H2R1/48p=<P9P7g00Z9P8CNp=EP7g00Z`R?g00[?R@P@g00[_RAP8g00\?Fkp=9Az978p=;P9P7g00]gP8CNp=QP5P?P@P@PAP0P7P8G{p=CP9P9P6P<P6P4P3P;P5P0P7P8M<cp=WP0P?P@P@PAP7P8Fjp=Ug01=0#Zg008oR?#FR6#FRB#FRC#F#F#FRD#`RE#^RF%`C#^RC#fRG]0RH13E8RI%15RJ%T6RK%TDRD'lRL3:RM13E0RN/4IRO%13RP,0N7JIP3P7O1P;P7O155GRQ[^0FRR%ZCRS#fRTP<P;P0P3C2P<P5P0P3C235[[^3F^5H]4S01XB:g00D:RU#1RV=:ILRW10NV9JOIPQ[^0FRVP4P5P0PUC2,KTW6W7X3FX5HX4HQ01%7;RX#1RY=:IL%74RZ#1R[,0N9JOIPQ[^0FPGP5P0O1P2PCPTP2PCPGP81dC8R\1L>5R]n10110000021010200P2PSPTf:R^P4%T?R_g00DY5tER`9=E;RaP=C2A[C78,dSRb%_SRcn10110000021010300Pcn10110000021010200P2PCPTP2PCPGP;P5O1P\P]n10110000021010200P2PSPTP^P3PaP=C2PbPcn10110000021010300Pcn1011000002101020055TXEGP:f>RaP;P0P3C2PaP5P0P3C255T\R\M^3F^5H^4H13E;%77RM#1;:L13E4RR%75R]#1Rd9DIR7?IP>P7O1RRP=P7O1Re55G[^0FP2PCPTP2PCPGP<P4O1P\f<Rf/L4n10110000021010200RgP2PSPTf=RhP>A=E<`RiP;C2PbPcn10110000021010300Pcn10110000021010200P2PCPTPgP2PSPTPhP=PiP;C2PbPcn10110000021010300Pcn1011000002101020055T]6]7]9P4PhP;P0PUC2PhP5P0PUC255T\V\W^3F^5H^4H13E5RW%7URV#1Rg;:L13E3RjADIjg7?IP<P7O195Ge[^0FP2PCPTP2PCPGP4P3O1P\f;Re/L3n10110000021010200P2PSPTPfP<A=E4`PUC2PbPcn10110000021010300Pcn10110000021010200,KTW6W7W9A:IdL%73Rd#1Rg,0N9JOIPQ[^0Ff?RQP;P0PdC2PQP5P0PdC255T[[^3F^5H^4H%7M#1=:jL13E<Rj%7]RM#1RO,0jRk,8I7?IP^P7O1=5GR[^0F14kL10J_/0_=:jLRRP8X09Rl1478#GXF9X09RmPkPl108_X09RkPkPJO1RnO1RoO1Rp,0jPlPlPlP9P9g01YR1078Ci#6XL9XM9RqPjPj%6jPOPpPlPl%18#6X0:RpPMPoPkP]PnPkP5PJ%6JC@C@EAM:BPLPL%6LRJA59LLeGHP7CIPR%S;%1;RR#<1hKDRn181K%<D181L[[R]%<KRog00\_RMAgKD7UWCRD%<L\M^CoRog00];RM%7VRO,M91M9VRV1M9URU5O95O9g00nDRr'e&00MS023[Rs%ZMRtP91\90S03P7%~9S04CRS05%}9Ru%|9Rv1Y911P96R6'E,9vS06%_@R@Pv1P9?Rw1Y9_Rx,;6Ry/;xRz';1Y9K=y9ERK'E,9vP@1;wxS07/QK,9vCCCC1xvARAP8P0g009TR{g00:4R|'KS081w80=5{|dAv917S09Cbb;b>b?X19X29%<7R1100_R|/0_=:7L18|L[[^19^29P8%1=R{13EfP5P;O4b:b<b=bAb8,s<13Ei10j_559PTPaP>A=E=`RiPXC2P2PCPTP2PCPGP^P>O1P\1LQ>n10110000021010200R}P2PSPTP7PbPcn10110000021010300Pcn10110000021010200P2PCPTP}P2PSPTf@R}PeA=E^`R~PZC2PbPcn10110000021010300Pcn1011000002101020055TXETP2PCPTP2PCPGP>P=O1P\1La=n10110000021010200P2PSPTPQP^A=E>`RQPdC2PbPcn10110000021010300Pcn10110000021010200,KTPaP^PiPXC2P5P^P>Pi13EiRi/0YRc/4L10R_Rb,0iRd/4LPlPmPcPdPlPlPlPqPiPi%6iPYPbPlPlPpPXPbPkP;PR%6RC@RREAM:BPLPLPJGH13E=RY%7XRi#1Rd'0Rc/4L10b_RS,0YR2/4LR\PlPmPcP2PlPlPlPqPYPY%6YPdPSPlPlPpPiPSPkPXPbPRC@EAM:BPLPLPJGHP0CIP\%S3%<PPnP]PDPoPsPtP9Q03P71\95RPCRPuPv%r?,P9R\/;z/EK,9vP@PvP9Pwg013:Rz1;\xR\CN,9vP@1;wyRy/EK,9vCCCCPAP8P0Q08Q09CbRKb;b>b?X19X29X@9107_RR/0_=:0L105_Rb9597A:0bL[[^19^29^@9P813Eh%1>A=Eh`,3EP;P3O5b:b<b=bAb8CX13EQRQADIQg7?IP5P713E^R^13E7RI'4RQ%7ZRg#1Rh,0^R>,8IRb'>%14RX/0_RS/0_Ri,0^Rd,8IR2,>QPQPbPQP2%GQPl1878#GXF9X09RQPIPI%6IR2P>PdPlPlPlPqP^P^%6^PhPiPlPlPpPgPiPkPZPSPkP4PX%6XC@RXC@EAM:BGWEV13E~R~/4IR410~[Ri,8IRg'>10~SRh,8IRd,>4R>P4PgP4Pd%G4PlPQPIPIP2PiPhPlPlPlPqP~P~%6~P[PSPlPlPpPZPSPXEAM:BGWEVP8CIP>13EeRe%7<R>#7RX#1RS'0R[/4L%1<R~/0_Rh/0_Ri,0eR2/4LRIPlPmP[P2PlPlPlPqPePe%6ePSPiPlPlPpPXPiPkP>PhPkP<P~%6~C@R~C@EAM:BPLPLPJGHP3CIPI%S=RI%<{R{PnP]PDPo%7O,M9%q?,p9=o9V=O9U5O9/er=[MsPtP9P91\9;P0Q04CRP7PPCRPuPv1P9BRB/E6,9v1;B\,Q6,9v5UvP@PvP9PBPzQ07CN,9vP@1Ew6,9v1;\x,;w,Q6,9v5UvCCCCPAPKb;b>b?X19X29X@9XD9AD75|9?57A59;R10;_/0_9D509?05[[^19^29^@9^D9P8A=E}`,3E%1fRfPj13E}P3P=O6b:b<b=bAb8bJCXO2WIX0FO5EabHW6W7W9XK:P8O1n0110101020111101P3P7P8O3P;P0O1P8P0%n0%<N?JNL14WWRN%1>R},0WRE,8WR`'>10WhRR,8WR6,>NPNP`PNP6%GNPlPQPWPW%6WRQPEPRPlPlPlPqPWPWPQP}PhPlPlPpP>PhP~EAM:BR~GWEV14EL14RLRhPlPmPEPRP~PLPLPJGHP0CIPhPIP{PnP]PDPoQ00%<j18jL10f_9DYY9?YYP;Q02PtQ05PuPvQ06P@1Eww,9v1Qwy,9v5UvCCPAPKb;b>b?X19X29AD77|9?77\1^19^29P8%1aP^P3O3b:n2001000000120000000b<b=bAb8CXbGO2EaP=P;P0PZC2P=P5P0PZC255TeW6W7X3FX5HX4HW9XB:P8CuXB:WNo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma length_n_to_le_8 : forall v : word, length (word_le8 v) = 8%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01vp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710R1p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R2P0p8P2p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p105o8p6041000R2p1060:p4p710p8P2p101QRp4p710p8P2P1p8P2p1060Yp4p710p8p1005Cp4p710P0p8g005bj11Tg006lj14Tg007Jj12Tg00E5j10Tg008Uj23Tg008o#1#1#1#1#1#1#4#2g01=og00D:#0#0#0#0#0#0#0#0'3W0o"). Qed.

Lemma length_flat_map_le8 : forall l : list word, length (flat_map word_le8 l) = (8 * length l)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01lh11nh21xh34__x1h42IHh53IH0h67__arithh74__ffh88__varmaph95__with:4cstrh;5cstr0h<1yp;1p;4p;2p;3p;7p;6p;5p;Bp;<p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710R2p8P0p1000np4p7210p8g06:5R0p4p710R3p1001jp4p710p8P3g002FR3p4p710R4p8p1002dp4p7210R5P4p8P5p10161p4p710p8p1003Pp4p7210P4p8p1004Ip4p7210P4p8p105o8p6041000R5p1060:p4p710p8P5g01QRR6p4p710p8P5P2p8P5p1060Yp4p710p8p1005Cp4p710P4p8g005bj15Tg006lj1JTg007Jj1DTg00L4j1@Tg06:Tj4;TP1j20Tg00E5R1j11Tg06;1j24Tg00KTj1ATg008Uj27Tg05k4R4j1?Tg0614j28Tg00:Tj1KTg00B4R5j13Tg00dkR2j29Tg00BTR7j2:Tg00>Fj36j1FTg05TJj2YTg03QIj3XTg01V5j4UTg01T?j1BTg00ETj2GTg00LTj2RTg00M2j1QTg00MPj1OTg00N;j2>Tg00N^j2NTg00j^j3HTg010aj3=Tg00Tij4MTg00Y1j7PTg00Pkj2LTg00QMj2STg00R9j3TTg00RXj4bTg01RRj4aTg06;Hj1`TP3j6<Tg01ZZj3_TP0j3^Tg00iZj3]TP6j5\Tg01XllBITg01XGl<[Tg01UPl<ZTg01=oR6f1R0f0R336p=2P6P6P6g00;oR8P8P8g06<FP5P5P5P2g06<ff5R2f4R9f3R:f2R;P0P3MBIp=EP6P6P6P8P8P8g067GP5P5P5P7g067gP2P9P:P;P0P3MBIp=WP6P6P8P8P1P5P5P:g01Z6P;P0P3M<[p=VP6P8P3P5P0P;P:P9P2f6f7f8M<Zp=Cg008oR9#5#5#5R5#5#5#5#J#DR1#@R7P1%J5#DR<P1P<P4P3C;'0g00D:#1#1#1#1#1#1#1#1R=1013'4'2R>X07%A1,01,4=,76P6%?;R?,0<R@P1P<P4P0C;RA,0<RB'8101;RC#1,4=RD,23X16P61010RE,4=RF%?:,0</83/2DX16P6P=14=C,83/2DX1618=FRD%1ERG,4=RH'2%K5R5%3ERI,95RJ':RK%K9RL,:IRM,95RN568%F6RO%F8RP%30%3356812031Y033XX<6X26R6PDPKP=P51785RKPFPJP=P5PKPEPI178IRDEERQEWPHPNP=P5PKPGPM1:3LRMX28PEPIPDCVEEM9C12BF%3BRD=68JRIPOPPP6PBPD178DPFPJPQM9CP3CUPI%BCg00H2RI%3C'GP1P<P4P:C;,0<R:#B%3:,GIg00];R:#A%@:1R80%Q8%O8R:g00Z`g00[?RCPCg00[_RCP81>85RQ1N89R99H8Q5=8g013:1>8L9=899H8QCMg00\?FP1L:CP3P;g009TRCg00:4R:'71S3;=6C:dAT8I0Cbb7b8b9X381953,:5195M568^38P31012#3O1b6b;b:b5CaP@%`;E<PBP3E<A_<?A,0<A^<?AE<P1P<P4A]1;0R;C;,0<101;,4='2eX4>X07X21P3D\W0o"). Qed.

(* [comment removed for export] *)
Definition total_arg_bytes_nat (args : list (list byte)) : nat :=
  fold_right (fun a acc => length a + 1 + acc)%nat 0%nat args.

Lemma total_arg_bytes_Z : forall l,
  total_arg_bytes l = Z.of_nat (total_arg_bytes_nat l).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01xh11lh24__x1h34__x2h41ah53acch62IHh77__arithh84__ffh98__varmaph:5__with;4cstrh<5cstr0h=1yh>1zp;1p;2p;<p;4p;3p;7p;5p;6p;Bp-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710R2p8P0g000nR0p4p7210p8p1001Mp4p710R3p1001jp4p710p8P3g002FR3p4p710R4p8p1002dp4p7210R5P4p8P5p10161p4p710p8p1003Pp4p7210P4p8p1004Ip4p7210P4p8p105o8p6041000R5p1060:p4p710p8P5g01QRR6p4p710p8P5P2p8P5p1060Yp4p710p8p1005Cp4p710P4p8g005bj17Tg006lj1]Tg007Jj1NTg00L4j19Tg06=Ij1CTg06>Ej18Tg00B4R4j10Tg00KTj1=TP1j25Tg00E5j1ETg0614j23Tg00:Tj1ZTg00BTR1j21Tg00>Fj1Vj3@Tg01R4j1UTg01UPl<QTg01T?j1;Tg00ETj2?Tg00LTj2MTg00SJj1LTg00_Oj4KTg00M2j1JTg00MPj1ITg00N^j2<Tg00N;j2HTg010aj3>Tg00Tij4GTg00Y1j7FTg00Pkj2OTg008Uj2ATg00QMj2PTg00R9j3DTg00RXj4STg01RRj4TTP0j5:TP3j6\Tg00iZj3[TP6j5YTg01XllBWTg01XGl<XTg00;oR6f1R3f0R03@p=21A60p=4g01=oR5f2R2P3g00D:R7P0D:p=6P5P5P5P6P6P6g067GP4P4P4P1g067gf5R1f4R8f3R9P2P3P0MBWp=BP5P6P6P6P4P4P1P8P9P2P3P0M<Xp=Rg008oR4#7R:#7#7#]#NR;#9R<#9R=P<%C0%80#0'2R>X1=%=<#8#0#4P615;3R?%E7R7'3/30X55X4<R@=6<3RA#0RB15;9R9#0%Z4RC'1/101397A6<@2R9'3#0'2X>615;2RD#0RE/1CRF/1BRG13D7RH/3ARI#0RJ'212GGP6P6%V6RKP0X06RLPK1230#UX=6X06PGPG%4GPJPGPLPL%00#4X05PIPGPHPFPDPE%4EP7PC%4CEBPAPB%4BEBERM<Q%;Dg00H2RD/?E%;9%09,?Dg00];R9#=%99P61M62P3%L6CK%J6%I6R9g00Z`g00[?REPEg00[_REP61<641H6C5>61<6:5>6R:g013:P:CGg00\?FF1O9EP0P2g009TREg00:4R9'A1P02=@E9dAD6D3CSb8b9b:X26X36110C/13R9/29^26^36P0A6<@8#015;1#0O2b7b<b;CTP6P<%0?/1C/10X56X4<RCPDP3D:P0E\P6P<PCPDA[<23R2D:A6<@2#0'2e%C2%82#0'2eX6>X1=X0<P0DYW1o"). Qed.

Lemma length_flatten_strings : forall l, length (flatten_strings l) = total_arg_bytes_nat l.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01lh11nh24__x1h34__x2h41xh52IHh63IH0h77__arithh84__ffh98__varmaph:5__with;1ah<3acch=4cstrh>5cstr0h?5cstr1h@1shA1yp;1p;2p;3p;4p;7p;6p;5p;Bp;<p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710R2p8P0g000nR0p4p7210p8g06:5R3p4p710R4p1001jp4p710p8P4g002FR4p4p710R5p8p1002dp4p7210R6P5p8P6p10161p4p710p8p1003Pp4p7210P5p8p1004Ip4p7210P5p8p105o8p6041000R6p1060:p4p710p8P6g01QRR7p4p710p8P6P2p8P6p1060Yp4p710p8p1005Cp4p710P5p8g005bj1=Tg006lj1aTg007Jj1VTg00L4j1?Tg06?Fj1HTP1j20Tg06>Ej1<Tg00KTj1:Tg008Uj24Tg00C1j2LTg00iZj3FTg01ZZj38Tg06:Tj4@Tg0614j21Tg00E5j1YTg00B4R1j12Tg00:Tj1WTg00BTR5j27Tg00>Fj35j1ETg05TJj2UTg03QIj3TTg01V5j4QTg01T?j19Tg00ETj2;Tg00LTj2PTg00SJj1OTg00_Oj4KTg00M2j1MTg00MPj1NTg00N^j2ATg00N;j2JTg010aj3CTg00Tij4ITg00Y1j7RTg00Pkj2STg00QMj2`Tg00R9j3_Tg00RXj4^Tg01RRj4]TP3j3GTP4j6>TP7j5ZTP0j5[Tg01XllB\Tg01UPl<XTg01=oR0f1R7f0R435p=3P0f2R3P7g00D:R6P4D[p=6P0P0P0g00;oR2P2P2g067GP1P1P1P5g067gf5R5f4R8f3R9P3P7P4MB\p=DP0P2P4P1P7P3P9P8P5f6R5f7R1f8M<Xp=Bg008oR:#=R;#=#=#aR<#VR=#?R>#?R?P>%H4,0=%<4'3R@X0?%:>#<,40P0g00H2RA,L<%:=5F=R<98=3RB,0=RCP>P=A8=4<X@>RDP7C@RE,0=RF'110=9%Y6R6'110=7/16/14X<0X;>RG=6>3RH'1RI,34X10P0A6>G7RJA8=9<,0=/14/3IX10P010=3R910=<'1RK114H/3IX101196RI/1JRH/3H%29RL%W:RM'7RN%2JRO'7RP=52P%E0RQ%E2RR%27%2455213741U743TXA0X40R0PHPPPIPNP9PL142LP6PM142MEDPJPO142OR6EDRLPHPPPLM9B13FJ%2FRL=52ORPPQPRP0PFPL142LPJPOP6M9BP4CQPPP>P=PDP3C@,0=RP#9%2P,;A10=8RP#9%2P,;AA6>G8R8#9%28,;Ag00];R8#:%?8P21P23P7%O2CK%M2%N2R8g00Z`g00[?RPPPg00[_RPP21A2:1J2M5C21A2;5C2R;g013:P;CIg00\?FR1S8PP4P3g009TRPg00:4R8'41`43=5P8dA_2A7C^b8b9b:X22X32174M/77RM=52M^22^32P4A6>G5#210=1#2O2b7b?b>b=b6C]11KJ/3HePCAG=3<E>PFP4E>A8=BE,0=AG=BEE>P>P=PDAF>37R3C@,0=A6>G3'3e%H3,0=%<3'3eX5@X0?X4>P4DZW0o"). Qed.

Lemma len_word_nat : forall {A} (l : list A), len_word l = nat_to_word (length l).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01Ah11lp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710R2p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R3P0p8P3p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p105o8p6041000R3p1060:p4p710p8P3p101QRp4p710p8P3P2p8P3p1060Yp4p710p8p200R3p106@Jp4p710p8P3P2p8p1005Cp4p710P0p8g00L4j16Tg005bj10Tg006lj12Tg007Jj11TP1j25Tg05XNj14Tg008Uj23Tf0R1#6g008o#0#0#0#0#0#0#2#1f1/51#4'3W1X03o"). Qed.

Lemma word1_nat : (1 : word) = nat_to_word 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710R1p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0p1002Fp4p710R0p8p1002dp4p7210R2P0p8P2p10161p4p710p8p1003Pp4p7210P0p8p1004Ip4p7210P0p8p105o8p6041000R2p1060:p4p710p8P2p101QRp4p710p8P2P1p8P2p1060Yp4p710p8p106ABp6041000R2p106@Jp4p710p8P2P1p8p1005Cp4p710P0p8g007Jj12Tg00>Fj33Tg00<Mj21Tg00@Uj34Tg005bj10Tg006lj1:Tg00:Tj19Tg00CWj35Tg00E5j16Tg05XNj17Tg008Uj28Tg00>`R0f0R1#2R2f1R3#2R4g00AYf2R5#2?331g00;oR6f3R7/15117333R8[11531151536%27?353[R9f4#2?375\8A4531P1n2001000000120000000W1W0W2P9^14^02^20P1g008oR1#0#0#0#0#0#0#:R0%91g00DY550g00D:#6#7R11101,86O4b3o"). Qed.

Lemma word_add_0 : forall a : word, a + nat_to_word 0 = a.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01zh12b1h22b2h31nh41Hh51ap;1p;3p;2p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710R1p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p105o8p6041000R3p1060:p4p710p8P3p101QRp4p710p8P3P1p8P3p1060Yp4p710p8p106ABp6041000R3p106@Jp4p710p8P3P1p8p1005Cp4p710P2p8g005bj11Tg006lj1ATg007Jj12Tg00>Fj34Tg00<Mj20Tg00@Uj3<Tg05XNj1;Tg01;5j38Tg00B4j1:Tg00C1j29Tg00BTj26Tg00o0j25Tg05VOj2@Tg05Wmj1?TP0j67Tg01FUj2=Tg01o@j3>Tg00;oR0f1R2f0R134p=3g008o#1#1#1#1#1#1#AR3#2g00>`R4%21R5%22R6g00AYf2R7#2?421f3R8/071082'3R9[10721071'3%28?472[R:f4#2?487\9A<721P1n2001000000120000000W2W1W3P:^26^15^34P1P3g00D:R4#;9832R5P2P01032R6%:4R4,93R:,03R9'6,531037R7,31X00P015341671,53/37X00P0P61531/37X001@32g00H2,66%?6E7P91=34E7A832:,03A>32:E71035/36eO4b4W5o"). Qed.

Lemma nat_to_word_merge : forall m k : nat,
  nat_to_word m + nat_to_word k = nat_to_word (m + k).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01zh11xh24__x1h34__x2h42b1h52b2h61nh71Hh87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>1kh?1mh@1yp;1p;3p;2p;<p;4p;7p;8p;Bp;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710R1p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R2p8p1002dp4p7210R3P2p8P3p10161p4p710p8p1003Pp4p7210P2p8p1004Ip4p7210P2p8p105o8p6041000R3p1060:p4p710p8P3p101QRp4p710p8P3P1p8P3p1060Yp4p710p8p106ABp6041000R3p106@Jp4p710p8P3P1p8p1005Cp4p710P2p8g007Jj19Tg00>Fj38j1WTg00<Mj22Tg00@Uj3_Tg005bj16Tg006lj1RTg05XNj1;Tg01;5j3=Tg0614j2>Tg00B4R2j13Tg00C1j2:Tg00BTR1j24Tg00o0j20j1\Tg008Uj25Tg01R4j1VTg01UPl<NTg01T?j1ATg00ETj2?Tg00KTj1LTg00L4j1KTg00LTj2ITg00SJj1HTg00_Oj4GTg00M2j1FTg00MPj1JTg00N^j2@Tg010aj3ETg00Tij4DTg00Y1j7MTg00Pkj2CTg00QMj2OTg00R9j3PTg00RXj4BTg01RRj4STg011Dj8TTg01nNj3^Tg011aj3]Tg01FUj2<Tg01o@j3[Tg01XllBYTg01XGl<XTP0j6ZTg00;oR0f1R3f0R438p=1g01=oR5P5P5P0P0P0g067GP2P2P2P1g067gf5R1f4R6f3R7f2R8P3P4MBYp=UP5P0P0P0P2P2P1P6P7P8P3P4M<Xp=QP0P6P7P8P3P4EZp=7g00>`R2%94R9%93R:g00AY%98?83412781273'1R;[12831284'1%97?883[R<%96?878\;A_834P4n2001000000120000000W5W4W6P<^5:^49^62P4g008oR2#6R9#6#6#6#6#6#RR:%;8%;35=:R<1>83R;#;R=%38R>,::R?,2:R@%33RA,::RB,2:RC'4,0:1>78#3RD,::,2:RE,14X0010:>RF144@,0:/1EX0010:ARG%37RH,0:RI/44,0:/1EX00%3;RE,0:14IF,0:/14X0014>G,0:RI10:D,14X00RD14>ARJ,0:PDP0P0%\:RDPDPJPEP0\0/5D11JE11JJP0P0%W0RDP4X10RKPD1134#VX@0X10PJPJ150JPEPJPKPK%34,50X15P;PJP8P>150>P3PA150AEUEQM<N%A3g00H2RJ/?A%A71?JHg00];RH#L%KHP01I08P3%H0CG%F0%J0RHg00Z`g00[?R7P7g00[_R7P01@021@095E0R9g013:P9CDg00\?FM1CH7P4P8g009TR7g00:4RH'51O48=87HdAP0J3CBb9b:b;X20X301443R3/13^20^30P4%36%31O2b8b=b<CSGTPIA^:>AD714FG,0:A]:>GD71::E,2:1<:ED7PC1<:AD7P@1<:>D7A=:?B,2:A[:?BD712:<12:='1eO4b7X>5X?5o"). Qed.

Lemma nat_to_word_add_merge : forall (a : word) (m k : nat),
  a + nat_to_word m + nat_to_word k = a + nat_to_word (m + k).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01bh11ah21kh31mp;1p;3p;2p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710R1p8P0p1000np4p7210p8p1001Mp4p710R0g001jR2p4p710p8P0g002FR0p4p710R3p8p1002dp4p7210R4P3p8P4p10161p4p710p8p1003Pp4p7210P3p8p1004Ip4p7210P3p8p105o8p6041000R4p1060:p4p710p8P4p101QRp4p710p8P4P1p8P4p1060Yp4p710p8p106ABp6041000R4p106@Jp4p710p8P4P1p8p1005Cp4p710P3p8g005bj11Tg006lj1=Tg007Jj1;Tg05XNj12Tg01;5j30j15Tg0614j24Tg00>Fj33Tg008Uj2:Tg06B<j27TP0j66Tg06C;j18Tg06Cfj69TP2j6<Tg008o#1#1#1#1#1#1#=R2#;R0g01=oR3P0f2R1f1R4#2R5f0R6#2R7502R8502f3R91414#2502R:9306X00P01446#2R;A0296=30:X00A021;,:0P81746E6A0215=027P0%52%82P1P5P7E9E<X23W3W1o"). Qed.

Lemma string_addrs_fst_structure : forall strs (base : word),
  fst (string_addrs base strs) =
  match strs with
  | [] => []
  | s :: rest => base :: fst (string_addrs (base + len_word s + 1) rest)
  end.
Proof.
intros strs base. destruct strs as [|s rest]; [reflexivity|].
cbn [string_addrs].
destruct (string_addrs (base + len_word s + 1) rest) as [ptrs fin] eqn:E.
reflexivity.
Qed.

Lemma string_addrs_pair : forall strs (base : word),
  string_addrs base strs = (fst (string_addrs base strs), base + nat_to_word (total_arg_bytes_nat strs)).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "p'0h01bh14baseh24__x1h34__x2h44strsh52IHh67__arithh74__ffh88__varmaph95__with:1ah;3acch<4cstrh=5cstr0h>1ph?4resth@1shA1xi001xhB1yi015finali024ptrsp;1p;2p;3p;4p;6p;<p;7p;8p;5p;Bp-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710R2p8P0g000nR0p4p7210p8p1001Mp4p710R3p1001jp4p710p8P3g002FR3p4p710R4p8p1002dp4p7210R5P4p8P5p10161p4p710p8p1003Pp4p7210P4p8p1004Ip4p7210P4p8p105o8p6041000R5p1060:p4p710p8P5g01QRR6p4p710p8P5P2p8P5p1060Yp4p710p8g06ABR5p6041000R7g06@JR8p4p710p8P7P2p8p1005Cp4p710P4p8g005bj1;Tg006lj1LTg007Jj1HTg00L4j1=Tg03b`R4j2hTg06D;j2ATg06E<j3:Tg06>Ej19Tg03d]j42j3VTg00>Fj30j1FTg00KTj1DTg008Uj26Tg06EYj1gTP3j6<TP8j2^Tg01;5j31j2RTg00:Tj1XTg00CWj3WTg05XNR8j18Tg00iZj3@TP1j2?Tg00E5j1STg0614j25Tg00B4R1j17Tg00BTR3j24Tg05TJj2QTg03QIj3PTg01UPl<OTg01T?j1GTg00ETj2JTg00LTj2NTg00SJj1MTg00_Oj4TTg00M2j1UTg00MPj1fTg00N^j2ITg00N;j2eTg010aj3BTg00Tij4`Tg00Y1j7_Tg00Pkj2]Tg00QMj2\Tg00R9j3[Tg00RXj4ZTg01RRj4YTg011Dj8ETg06FQj3KTP5j2aTP6j5bTP0j5cTg01XllBdTf2R0f1R6f0R5#831p=3g01=oR2P0P6g00D:R7P5Dcp=CP2P2P2g00;oR9P9P9g067GP1P1P1P3g067gf5R3f4R:f3R;P0P6P5MBdp=>g008oR<#;R=#;#;R>#L#HR?#=R@#=RAP@%;>#;#;#LR>#HRB%=BRC/hBRD1A56REPCPBA:CBE%9693>5C230]1REX4APBP5PCPB%DBRFP6C2PCPBPFP5C2RF50DX0B16DFA3>57%g5E<%D@RF,A5RGPCPBA:CBG%9F93>5C250DeX1BPDPCPB1^?;RF91>5%X<RGg00DY5W>RH51>RI/A0RJ9:CBRK%90RL#8RM91>IRNC2P4PCPBPDP5PCPBA@B;6P5C2n2001100000120102101R4PCPBA:CB4A@@:;#993>6R4C250DX>DPBPDA@B5KRK9VCBROPOPNA@@;0RP#993>5RQPD\B/6OPB1??;RO#8RRA1>65=1>H%9;#8RS51>=0B4X0BPB%S7R7#8RT1??:93>6=1>5=1>S=0B4X0BPBA1>5RRR157LRS53>R:A0B54X0BR4PB15OS93>5RUP4PBPB1R>5R4P41??6/57/55X;2X:@RV=C@0RW,57RX,5ORY#8RZ15O7R[/5WR\#8PB\B/64P2PBP8P8PYP\PB\2/68A02Y\%7OR8%7WR4,4GR]'4R^148GR_/44R`509P2P9%F2P1%F9%76%75509A02651Q653PXB2XA2PYP^POP81698R^PXP]P7PG169GR]PWP41694RXE>E>P\P`P[P_POP8P^P7PGP]E>PWP4PXE>M<O%GOg00H2RX/J8AC@V;R8#G%78,JXg00];R8#D%=8P91N90P6%M9CT%U9%f9R8g00Z`g00[?R4P4g00[_R4P91I9<R<1e9GRW1I9=R=5B95B9g013:AB9<W=B9=C`g00\?F_1]84P5P0g009TR4g00:4R8'61\50=048dA[9X6CZb7b8b9X29X3914G6,45145G/46509^29^39P5AC@V3#7f6,??#7O2b6b=b<CYGEGEA1>5ZAC@VP93>550BeA0BUQeP:AK5OSE<A1>RT=1>MAKR7LE<PHg06GTE<PF1a?;E<GEPCPBPKPNC2RNPCPBA:CBNPQC250DePJP6PIO1E<1A5PRPPCPBA:CBPPQC250DeX1BX5EX?AX@@P5DbW4o"). Qed.

Lemma length_string_addrs_fst : forall strs (base : word),
  length (fst (string_addrs base strs)) = length strs.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h04baseh14strsh22IHh31lh41nh54resth61sp;1p;2p;3p;6p;5p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g000NR1p4p710R2p8P0p1000np4p7210p8p1001Mp4p710R0p1001jp4p710p8P0g002FR0p4p710R3p8p1002dp4p7210R4P3p8P4p10161p4p710p8p1003Pp4p7210P3p8p1004Ip4p7210P3p8p105o8p6041000R4p1060:p4p710p8P4g01QRR5p4p710p8P4P2p8P4p1060Yp4p710p8p106ABp6041000R4g06@JR6p4p710p8P4P2p8p1005Cp4p710P3p8g005bj11Tg006lj1<Tg007Jj1:Tg00L4j13Tg06D;j27Tg06E<j35TP1j20Tg00>Fj32Tg00KTj1?Tg008Uj29TP6j2>Tg01;5j38Tg00:Tj1=Tg00CWj3BTg00iZj34Tg00E5j16TP0j6;Tg06HKj2ATP5j5@Tg008oR5#1#1#1R0#<#:R6#3R1#3R3P1%10#1#1#<R0#:R2g01=oR4%32R7f0R8f1R9'7752,02101932]0R:X13%?1,01,94X02P7f3R;,>69808%=5g00DY5B0580R0f2R5'79572R69428R<1028f4=41;,01524X37P41015R=%68101;#6524X44%6=,941026P9P0O1E;102<A41;5R5,01524e178595721A58E;X02X2:X53X61P8D@W1o"). Qed.

(* [comment removed for export] *)
Lemma entry_stack_image_block : forall inp mbase ph entry (sp : word) draw,
  entry_stack_image inp mbase ph entry sp draw
  = build_stack_bytes (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
      (in_argv inp) (in_envp inp) (in_execfn inp)
      (in_uid inp) (in_gid inp) (in_hwcap inp) draw.
Proof. reflexivity. Qed.

Lemma la_rseq_launch_auxv : forall inp sp mbase,
  la_rseq (launch_auxv inp sp mbase) = kb_rseq (in_kernel inp).
Proof. reflexivity. Qed.

Lemma length_entry_stack_image_launch :
  forall v inp mbase ph entry (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
  = (bv_unsigned (ed_top draw) - bv_unsigned sp)%Z.
Proof.
  intros v inp mbase ph entry sp brk draw Hok.
  cbn [entry_launch_ok_va] in Hok.
  destruct Hok as (_ & (_ & _ & Hhi) & _).
  unfold entry_stack_image.
  rewrite length_build_stack_bytes, la_rseq_launch_auxv.
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Z.mod_pos_bound
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp)))
    16 ltac:(lia)) as Hm.
  unfold block_pad_len.
  rewrite !Nat2Z.inj_add.
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Lemma entry_stack_image_no_wrap :
  forall v inp mbase ph entry (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned sp
   + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
     < 2 ^ 64)%Z.
Proof.
  intros v inp mbase ph entry sp brk draw Hok.
  rewrite (length_entry_stack_image_launch v inp mbase ph entry sp brk draw Hok).
  pose proof (u64_range (ed_top draw)) as Hr. lia.
Qed.

Lemma bsb_argc_prefix :
  forall la ph entry (sp top : word) argv envp execfn uid gid hwcap draw,
  exists tl,
  build_stack_bytes la ph entry sp top argv envp execfn uid gid hwcap draw
  = word_le8 (len_word argv) ++ tl.
Proof.
  intros la ph entry sp top argv envp execfn uid gid hwcap draw.
  unfold build_stack_bytes. cbv zeta.
  rewrite (string_addrs_pair argv). cbv beta iota.
  rewrite (string_addrs_pair envp). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma read_at_offset : forall segs (sp : word) bytes pre mid post k,
  bytes = pre ++ mid ++ post -> length mid = k ->
  (bv_unsigned sp + Z.of_nat (length bytes) < 2^64)%Z ->
  rdn segs (stack_to_mem sp bytes) (sp + nat_to_word (length pre)) k = Some mid.
Proof.
  intros segs sp bytes pre mid post k Hb Hk Hnw.
  pose proof (u64_range sp) as Hsp64.
  assert (Hlenpre : (length pre <= length bytes)%nat)
    by (rewrite Hb, !length_app; lia).
  assert (Hu : bv_unsigned (sp + nat_to_word (length pre)) = (bv_unsigned sp + Z.of_nat (length pre))%Z).
  { unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    rewrite bv_wrap_add_idemp_r, bv_wrap64_mod.
    apply Z.mod_small. lia. }
  assert (Hsp : (bv_unsigned sp <= bv_unsigned (sp + nat_to_word (length pre)))%Z) by lia.
  assert (Hlen : (Z.to_nat (bv_unsigned (sp + nat_to_word (length pre)) - bv_unsigned sp) + k <= length bytes)%nat)
    by (rewrite Hu, Hb, !length_app; lia).
  rewrite (rdn_stack segs sp bytes k _ Hsp Hlen Hnw).
  rewrite Hu.
  replace (Z.to_nat (bv_unsigned sp + Z.of_nat (length pre) - bv_unsigned sp)) with (length pre) by lia.
  rewrite Hb, skipn_app, skipn_all, Nat.sub_diag.
  cbn [app]. rewrite skipn_O.
  rewrite firstn_app, <- Hk, firstn_all, Nat.sub_diag.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma rdn_image_in_block :
  forall segs inp mbase ph entry (sp : word) draw (a : word) n,
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw)) a n
  = rdn segs (stack_to_mem sp
        (build_stack_bytes (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
           (in_argv inp) (in_envp inp) (in_execfn inp)
           (in_uid inp) (in_gid inp) (in_hwcap inp) draw)) a n.
Proof. reflexivity. Qed.

Lemma read_at_offset_image :
  forall segs inp mbase ph entry (sp : word) draw pre mid post k,
  entry_stack_image inp mbase ph entry sp draw = pre ++ mid ++ post ->
  length mid = k ->
  (bv_unsigned sp
   + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
     < 2 ^ 64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (sp + nat_to_word (length pre)) k
  = Some mid.
Proof.
  intros segs inp mbase ph entry sp draw pre mid post k Hb Hk Hnw.
  exact (read_at_offset segs sp _ pre mid post k Hb Hk Hnw).
Qed.

Lemma read_argc : forall inp mbase ph entry segs (sp : word) draw,
  (bv_unsigned sp
   + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
     < 2 ^ 64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      sp 8%nat
  = Some (word_le8 (len_word (in_argv inp))).
Proof.
  intros inp mbase ph entry segs sp draw Hnw.
  destruct (bsb_argc_prefix (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
              (in_argv inp) (in_envp inp) (in_execfn inp)
              (in_uid inp) (in_gid inp) (in_hwcap inp) draw) as [tl E].
  rewrite <- entry_stack_image_block in E.
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
                [] (word_le8 (len_word (in_argv inp))) tl 8%nat) as H.
  cbn [length] in H.
  rewrite word_add_0 in H.
  apply H; [exact E|reflexivity|exact Hnw].
Qed.

Lemma read_byte_at : forall segs (sp : word) bytes pre s post j,
  bytes = pre ++ s ++ post -> (j < length s)%nat ->
  (bv_unsigned sp + Z.of_nat (length bytes) < 2^64)%Z ->
  rdn segs (stack_to_mem sp bytes) (sp + nat_to_word (length pre + j)) 1%nat
  = Some [nth j s (Z_to_bv 8 0)].
Proof.
  intros segs sp bytes pre s post j Hb Hj Hnw.
  destruct (nth_error_skipn_cons s j Hj) as [b [Hnth Hskip]].
  assert (Hsj : s = firstn j s ++ b :: skipn (S j) s)
    by (rewrite <- Hskip; symmetry; apply firstn_skipn).
  pose proof (read_at_offset segs sp bytes (pre ++ firstn j s) [b] (skipn (S j) s ++ post) 1%nat) as H.
  rewrite length_app in H.
  rewrite firstn_length_le in H by lia.
  replace (nth j s (Z_to_bv 8 0)) with b by (symmetry; apply (nth_error_nth _ _ _ Hnth)).
  apply H; [|reflexivity|exact Hnw].
  rewrite Hb. rewrite Hsj at 1. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma read_byte_at_image :
  forall segs inp mbase ph entry (sp : word) draw pre s post j,
  entry_stack_image inp mbase ph entry sp draw = pre ++ s ++ post ->
  (j < length s)%nat ->
  (bv_unsigned sp
   + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
     < 2 ^ 64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (sp + nat_to_word (length pre + j)) 1%nat
  = Some [nth j s (Z_to_bv 8 0)].
Proof.
  intros segs inp mbase ph entry sp draw pre s post j Hb Hj Hnw.
  exact (read_byte_at segs sp _ pre s post j Hb Hj Hnw).
Qed.

Lemma nth_app0_bound : forall (a1 : list byte) j,
  (bv_unsigned (nth j (a1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) < 256)%Z.
Proof.
  intros a1 j. apply u8_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma entry_page_top_within_window :
  forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (entry_page_top draw <= va_stack_top v)%Z.
Proof.
  intros v inp mbase sp brk draw Hok.
  cbn [entry_launch_ok_va] in Hok.
  destruct Hok as ((_ & Htop & _) & _ & _).
  unfold entry_page_top. exact Htop.
Qed.

Definition wrap_mem (inp : ProcInput) (mbase : word) (ph : PhdrInfo)
    (entry sp : word) (draw : EntryDraw) : word -> option byte :=
  fun addr =>
    match stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw) addr with
    | Some b => Some b
    | None =>
      if andb (Z.leb (stack_window_lo (in_kernel inp) mbase draw)
                     (bv_unsigned addr))
              (Z.ltb (bv_unsigned addr) (bv_unsigned sp))
      then Some (Z_to_bv 8 0) else None
    end.

Lemma init_mkst : forall segs (pc : N) ph (sp mbase : word) draw inp,
  init_machine_state segs pc ph sp mbase draw inp =
  @mkst fx0 (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp)
       (Z_to_bv 64 (Z.of_N pc))
       (wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N pc)) sp draw)
       (seg_rom segs).
Proof. intros. reflexivity. Qed.

Lemma wrap_above_sp : forall inp mbase ph entry (sp : word) draw (x : word),
  (bv_unsigned sp <= bv_unsigned x)%Z ->
  wrap_mem inp mbase ph entry sp draw x
  = stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw) x.
Proof.
  intros inp mbase ph entry sp draw x Hx. unfold wrap_mem.
  destruct (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw) x)
    as [b|] eqn:E; [reflexivity|].
  assert (Hltf : Z.ltb (bv_unsigned x) (bv_unsigned sp) = false)
    by (apply Z.ltb_ge; lia).
  rewrite Hltf, andb_false_r. reflexivity.
Qed.

Lemma rdn_wrap_stack_above :
  forall segs inp mbase ph entry (sp : word) draw (a : word) n,
  (bv_unsigned sp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn segs (wrap_mem inp mbase ph entry sp draw) a n
  = rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw)) a n.
Proof.
  intros segs inp mbase ph entry sp draw a n Hsp Hnw.
  apply rdn_ext; [exact Hnw|].
  intros x Hx. apply wrap_above_sp. lia.
Qed.

End WithFP3.
