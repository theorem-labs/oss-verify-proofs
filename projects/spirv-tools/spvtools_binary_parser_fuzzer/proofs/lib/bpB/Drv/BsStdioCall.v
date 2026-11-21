(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the model's channel reader a premise of the stdio call; the recorded proofs replaced by the text proofs of boost-beast/http_request's As/AsStdioCall.v, at this binary's addresses). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BAgentLib BpecConsts BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BLibKnowFrame BHoare.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BazyRestrict BazySR.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BRefExitBase BRefStdioDefs BsLazyRun BsStdioWrite.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BsStdioCall () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indc69OSSVerify5KrLib3bpB3Drv;BsStdioCall3inrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib4Init5Logic3notC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes>Morphisms_Prop@not_iff_morphismC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismc69OSSVerify5KrLib3bpB3Drv;BsStdioCall8inr_specC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2eq01C47Corelib7Classes?RelationClasses?iff_equivalenceK47Corelib4Init9Datatypes4bool02C47Corelib7Classes?RelationClasses=iff_SymmetricI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib3bpB2HF9BSymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C79OSSVerify5KrLib3bpB2HF>BSymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF>BSymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF>BSymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF8BStoreOk9mem_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbI47Corelib4Init5Logic2or00c69OSSVerify5KrLib3bpB3Drv;BsStdioCall9inr_falseC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib4Bool4Bool:orb_true_rK46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib3bpB2HF=BLibKnowFrame8kn_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF=BLibKnowFrame=know_ok_frameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I79OSSVerify5KrLib3bpB2HF9BSymExec23SX23env00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpB2HF9BSymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpB2HF9BSymExec23SX24expr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01K47Corelib5Lists7ListDef6Forall02K47Corelib5Lists7ListDef6Forall01C46Stdlib5Lists4List8flat_mapI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List?Forall_flat_mapc69OSSVerify5KrLib3bpB3Drv;BsStdioCall9kimg_cut1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1K79OSSVerify5KrLib3bpB2HF9BSymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX26kentry02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib4Bool4Bool=orb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List:Forall_appC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07K79OSSVerify5KrLib3bpB2HF9BSymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX26kentry08C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall8kimg_cutC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF>BSymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall;Forall_one'C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00I79OSSVerify5KrLib3bpB2HF9BSymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib3bpB2HF9BAgentLib7u64_litC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX24expr01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF9BSymExec23SX26edenotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall6u_lit0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF9BSymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF9BSymExec23SX25a_offC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C79OSSVerify5KrLib3bpB2HF9BSymExec23SX29split_litC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7add_0_lK79OSSVerify5KrLib3bpB2HF9BSymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BPropExec5v_addC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_rC69OSSVerify5KrLib3bpB2HF9BPropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib3bpB2HF9BPropExec7alu_addC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX24expr05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX24expr06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX24expr07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpB2HF9BSymExec23SX24expr08C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic7f_equalK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I4ELinuxProcessSemantics5Riscv5Instr5aluop00I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics5Riscv5Instr5mulop00C69OSSVerify5KrLib3bpB2HF7BSymRun<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC69OSSVerify5KrLib3bpB2HF:BSymDriveX6kindexC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3subI47Corelib4Init5Peano2le00K47Corelib4Init5Peano2le01C46Stdlib5Lists4List9nth_errorC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes8list_indI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z9mod_smallC79OSSVerify5KrLib3bpB2HF9BSymExec23SX24ridxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK45stdpp9bitvector;definitions2bv01C46Stdlib9micromega;ZifyClasses9and_morphC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib5Lists7ListDef3nthc69OSSVerify5KrLib3bpB3Drv;BsStdioCall8ridx_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF9BSymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC79OSSVerify5KrLib3bpB2HF9BSymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC47Corelib4Init9Datatypes7nat_indC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List:length_seqC56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_mapC69OSSVerify5KrLib3bpB2HF9BSymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify5KrLib3bpB2HF>BSymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall:stdio_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall<lit_even_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF:BSymDriveX:is_kwr_covC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF9BSymExec23SX2:base_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF7BSymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF7BSymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib3bpB3Drv;BsStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BPropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BSymDrive9junk_valsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib3bpB2HF<BazyRestrictEsame_but_materializedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF6BazySR8hid_sameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC69OSSVerify5KrLib3bpB2HF<BazyRestrict8restrictC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z3addC57Corelib7BinNums6IntDef1Z3subC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula01c69OSSVerify5KrLib3bpB3Drv;BsStdioCall:sr_get_natC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BPropExec4getrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF>BSymExec2Sound4SX2S@base_range_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall?split_lit_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BPropExec9u64_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall;kindex_someC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF9BSymExec23SX28expr_eqbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF>BSymExec2Sound4SX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC69OSSVerify5KrLib3bpB2HF:BSymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc69OSSVerify5KrLib3bpB3Drv;BsStdioCall9flat_abs0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF9BSymExec23SX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF:BSymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC35stdpp7tactics<f_equal_helpK69OSSVerify5KrLib3bpB3Drv=BRefStdioDefs7sw_file01C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propC69OSSVerify5KrLib3bpB2HF6BHoare;ret_ok_evenC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpB3Drv=BRefStdioDefs7sw_post00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF7BSymRun>vals_app_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF7BSymRun9env_agreeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega5Tauto8GFormula02C69OSSVerify5KrLib3bpB2HF9BSymDrive?regs_after_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCallFlength_sr_after_call_jC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall=length_sr_updC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib3bpB2HF7BSymRun7vals_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BSymDrive>sr_vars_lt_nthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF7BSymRun<edenot_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF:BSymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall?nth_sr_upd_sameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall@nth_sr_upd_otherC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF:BSymDriveX;regs_ok_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF:BSymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall>kimg_cut_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall>split_lit_varsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall>know_ok_frame3C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF>BSymExec2Sound4SX2S;mkAlu_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB3Drv<BsStdioWrite>as_stdio_writeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02K79OSSVerify5KrLib3bpB2HF9BSymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BSymDrive5kreadC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF9BSymExec23SX25mkAluC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall5sc_wbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall5sc_wpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall4sc_sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall4sc_lC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall5sc_spC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BPropExec3rdnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01I69OSSVerify5KrLib3bpB2HF6BazySR4lzok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BPropExec4mkstC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall5sc_srC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall5sc_knC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall6sc_retC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpB2HF9BShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BShapeAlg6t_emitC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula0:C69OSSVerify5KrLib3bpB2HF9BSymDrive9kread_rdnC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib3bpB3Drv;BsStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpB2HF9BSymExec23SX25two64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall7SC_KEPTC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib3bpB2HF4Bcfg=hunspell_scfgC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K46Stdlib9micromega5Tauto4kind02I69OSSVerify5KrLib3bpB2HF9BPropExec3DFP00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib3bpB2HF9BShapeAlg4TSetC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Zc69OSSVerify5KrLib3bpB3Drv;BsStdioCall4sc_fC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall7sc_bufpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB3Drv;BsStdioCall8sc_bufszC1?~~~~~~~~~~~~~~~".
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition SC_KEPT : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Record stdio_res : Type := SCR_ {
  sc_f : Z;
  sc_fd : Z;
  sc_ret : Z;
  sc_wb : expr;
  sc_wp : expr;
  sc_bufp : expr;
  sc_bufsz : expr;
  sc_s : expr;
  sc_l : expr;
  sc_sp : expr;
  sc_sr : list expr;
  sc_kn : list kentry
}.

Definition lit_even_ret (e : expr) : option Z :=
  match e with
  | ELit r => if ((r mod 2 =? 0) && (0 <=? r) && (r <? two64))%bool then Some r else None
  | _ => None
  end.

Definition kimg_cut1 (a n : Z) (K : kentry) : list kentry :=
  match K with
  | KImg lo hi =>
      if (Z.leb hi a || Z.leb (a + n) lo)%bool then [K]
      else (if Z.ltb lo a then [KImg lo a] else []) ++ (if Z.ltb (a + n) hi then [KImg (a + n) hi] else [])
  | _ => [K]
  end.
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := List.flat_map (kimg_cut1 a n) k.

Definition stdio_call (nv : nat) (sr : list expr) (kn : list kentry) : option stdio_res :=
  match nth 10 sr (ELit 0), lit_even_ret (nth 1 sr (ELit 0)) with
  | ELit f, Some ret =>
    match kread RSEGS kn (ELit 0) (f + 120) 4, kread RSEGS kn (ELit 0) (f + 40) 8, kread RSEGS kn (ELit 0) (f + 56) 8,
          kread RSEGS kn (ELit 0) (f + 88) 8, kread RSEGS kn (ELit 0) (f + 96) 8,
          kread RSEGS kn (ELit 0) 0x185ed0 8, kread RSEGS kn (ELit 0) 0x6e5898 8 with
    | Some (ELit fd), Some wp, Some wb, Some bufp, Some bufsz, Some (ELit cg), Some _ =>
      let sp := nth 2 sr (ELit 0) in
      let '(qb, k0) := split_lit sp in
      let qk := (k0 - 112)%Z in
      match kindex (is_kwr_cov qb qk 112) kn 0, base_range kn qb with
      | Some _, Some (blo, bhi) =>
        if ((0x189920 <=? f) && (f + 232 <=? 0x189be8)
            && ((fd =? 1) || (fd =? 2)) && (cg mod two64 =? 0x6e5898)
            && (4294967296 + 112 <=? blo + k0) && (bhi + k0 <=? 0x800000000000)
            && expr_vars_lt nv bufp && expr_vars_lt nv bufsz
            && sr_vars_lt nv sr && kn_vars_lt nv kn && Nat.eqb (length sr) 32)%bool
        then
          let k0 := kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8 in
          let k1 := kn_frame k0 qb qk 112 in
          let k2 := kn_frame k1 (ELit 0) (f + 32) 16 in
          let k3 := kn_frame k2 (ELit 0) (f + 56) 8 in
          Some (SCR_ f fd ret wb wp bufp bufsz (nth 11 sr (ELit 0)) (nth 12 sr (ELit 0)) sp
                     (sr_upd (sr_after_call_j sr SC_KEPT nv) 10 (nth 12 sr (ELit 0)))
                     (KWord (SA (ELit 0) (f + 32)) 8 (mkAlu ALU_ADD bufp bufsz)
                      :: KWord (SA (ELit 0) (f + 40)) 8 bufp
                      :: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3))
        else None
      | _, _ => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _, _ => None
  end.

Definition inr (lo n : Z) (x : word) : bool := (Z.leb lo (bv_unsigned x) && Z.ltb (bv_unsigned x) (lo + n))%bool.

Lemma inr_spec : forall lo n x, inr lo n x = true <-> (lo <= bv_unsigned x < lo + n)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "h05lemmah11Bh21Hh32H0h42H1h52loh61nh71xp;1p;2p;3p;4p;6p;;p;5p;9p-1R0g0000R1p4p710p9P0p1000\p4p710p9P0p1001HR2p4p710p9P0P2p4p7210p9P0P2p4p73110p9P0g001fR0p4p710p9g002`j11Tg003Ej1KTg003cj1@Tg004Fj26Tg0050j2=Tg005Mj24Tg005jj2:Tg006Gj29Tg006eR2j22Tg007@R3j23Tg007Yj27Tg0085j25TP1j2JTg008Qj2ITg0092j3FTg009hj4;Tg00:[R1j6ETg00;Mj2CTg00;mj4BTg00<Tl;ATg00=Oj2?Tg00=oj4<Tg00>Jj5DTg00>gj3>Tg00?cj3GTP0l9HTg00@=f0R0g00@]3Gp=0p-0R4P3g00A=f5R5f4R6f3R7f2R8f1R9P0M9Hp=8g00AnR:g00BL#1#1#1#1#1#1#KR;#@16;0R<,=8R=1489R>,:<R?'9#0%0=R@%0?RA'2'316;9RB,=7RC1478RD,:BRE'9#0%0CRC%0ERE'2RFP0177BRG15BDRD'2RBPB1J4BRHE8W01I=?178<R?,3@PF12GERFPCPGP0PEPEP4P3g00C19F43RCPEC;EEPBPBPHE8W01C8<15<>R@,3APFPBP4P4^14P3P4P4P3P3CBP2P1PGP4P3PCPGC;PEPDP0M;APBPBPHE8W01?<>12?@R@PB[R?P?PGPDPB16;81467'516;7R;,751456,5;P9P0C<W4X3GP0DDX2@RGPGC<O2O2O2A>890#0/3@eW7X6:W5o"). Qed.

Lemma inr_false : forall lo n x, inr lo n x = false <-> ~ (lo <= bv_unsigned x < lo + n)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "p'0h01Hh13Heqh22H0h32H1h41eh51bi001bh65lemmah72loh81nh91xp;1p;3p;2p;6p;7p;4g002`j11Tg003Ej1ETg003cj1@Tg00>gj38Tg004Fj2<Tg007Yj2;Tg005Mj2:Tg0085j25Tg006ej26Tg007@R0j24Tg00Caj3?Tg00?cj30Tg00DSj12Tg00Dlj6DTg00EWj3CTg00FIj7BTg00GDj3ATg00HEj6=Tg00Haj27Tg00I@j29Tg00=oj4>Tg00@=R1f0R2g00@]R330p=3g00AnR4g00BL#1#1#1#1#1#1#ER5#@f2R6f1R7;82R8#31<52R9,;61:67,59'6'4p-0R9P0g00IZ9?90f3R:?867R;g00JLR<5011<57R5,;:1::6,55'6R5#2%3;R;#2P9P0g00JlP;P5P2ED9C5;FBW6AA672P8P1P1A012<%32#2'4P2A013<R8A0133R6#2R;[P8\;P7P8P1P3P1P9P2g00K\R5g00L8R0n0110000020000X41g00LUR:P<P2E=P01702R=b3b1X26P;eX081913P6P7P2O1,78b1X0;C>A01<<R;A01<3R8#2R7[P;\7P2P8P1P<P1P9P2P0P5n0110000020000X41P:P3P2E=P0P=b3b1X28P7eX0;191<X07C>n0110000020000b5O2W9X84W7o"). Qed.

Lemma know_ok_frame3 : forall E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3,
  know_ok RSEGS E M kn ->
  flat E (SA b1 o1) n1 -> flat E (SA b2 o2) n2 -> flat E (SA b3 o3) n3 ->
  (forall x : word,
     ~ (estart E (SA b1 o1) <= bv_unsigned x < estart E (SA b1 o1) + n1)%Z ->
     ~ (estart E (SA b2 o2) <= bv_unsigned x < estart E (SA b2 o2) + n2)%Z ->
     ~ (estart E (SA b3 o3) <= bv_unsigned x < estart E (SA b3 o3) + n3)%Z ->
     M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn b1 o1 n1) b2 o2 n2) b3 o3 n3).
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "p'0h01xh12Hxh22E3h31bi001bh42E2h51Hh64__x1h74__x2h84__x3h92loh:1nh;7__arithh<6heq_a1h=6heq_a2h>6heq_a3h?4__ffh@4__p1hA8__varmaphB5__withC1EhD2F1hE2F2hF2F3hG2G1hH2G2hI2G3hJ2HKhK2HghL4HouthM1MhN2M'hO2M1hP2M2hQ2O1hR2O2hS2O3hT2a1hU2a2hV2a3hW2b1hX2b2hY2b3hZ2knh[2n1h\2n2h]2n3h^2o1h_2o2h`2o3p%0p;1p;4p;2p;3p;6p;<p;7p;8p100M1p4p70p100M_p4p7210p8p100N;p4p710g00O<R0p4p710p8g002`j1>Tg003Ej1UTg003cj1PTg00OZj1]Tg00P<j1MTg00P\j4hTg00Qcj2GTg00Rdj3JTg004Fj27Tg00DSj16Tg00Shj2LTg00?cj32Tg00Tnj2ETg00>gj30Tg00Ulj23Tg0085j2?Tg005Mj2@Tg007Yj2BTg00VIj2CTg00I@j2;Tg00Vcj3_Tg00Wej1^Tg00XEj2NTg00Xcj4\Tg00YAj1[Tg00Y_j1ZTg00ZJj2HTg00Zmj1YTg00[Rj3RTg00\5j1WTg00\Wj6nTg00];j2mTg00]]j2lTg00^Ij3kTg00^hj4jTg00_Zj1TTP0j6gTg00GDj3fTg00`8j6eTg00HEj6dTg00`\j4QTg00a^l<KTg006eR0j2cTg00bej4STg00cPj7bTg00d4j7aTg00dXj7`Tg00e<j8iTf2R1f1R2f0R3'G'Lp=5f4R4f3R5'B1@23,?1'cp=4g00@=R6A0512;23p=8g00@]R79263p=:g00JLR89263p=<A2623p=Og00AnR9/;3p==A2923p=AP9P2g00e`P3CSp=DP2g00fGR:g00ffR;P;g00gFR<P3g00gfFbp=9P9P2g00hFP3CSp=FP1P:P;P;P<P2P3Fap=XP1P:P;P;P<P2P3F`p=VP5P:P;P;P<P1P2P3Gip=IA2123#6p=1g00hmg00BLR=#>R>#>#>R?#>#>#>#UR@#PRA%U?#PR?#]RB[PB^0ARCg00il#Mg00jnRDg00knREf<RFf;RGf9RHChf=RIf8RJ,GHRKf7RL3Jf>RMf6RN,GLf5RO3Jf?RP1GO4;J5fARQ?5IFRR17@3RSPSPRPGD4#6fBRRf:RT75GRU17@2RVPVPUPHD4#6fCRU/LKRK17@1RWPWPKPLD4#6PRP5O1PUP5O152B[[[^0Af@RK/EPA5RMIP9A5UFGP9fDRX?5THP9P6PBA01I3A02T3'3fERYP3O1RZPXP3O1n0100000020000X0APCP6PBA01G3fFR[P3O1PZn0100000020000X0APC1?SO1@OR/BS'CRCA0OK2P61;63RZPNPQP1P3C8P6PJPUP4P3C8P6PBA0JQOR\,32fLR]POO1R^fKR_POO1n0100000020000=2B^]4P2A0LR5R^#:P_P4O1,;BW4%<^A0LK4P6PZ1O\3P6PTPUPLP3C8P6PB1382fOR\PJO1R^fNR`PJO1n0100000020000=2B^]2P2A0HRNR^#:P`PLO1Ra,;BW2%<^P0A0123R^#<P5PVPVP5P1D4S00#6[RVP1PSPSP1P2D4Rb#6A0512Rc#<Rd[P4PWPWP4P5D4S01#6\dA_123P2n2001000000120000000X0AX:9X99RdPV^0A^:9^99RVP3PFfGRWPJP4O4PF17@JRePePFPWD4#6PdPVP3PIP[PTP5O4PI17@TRVPVPIP[D4#6PRPGfSRdfIRffHRg35Rh#=1AMhRheS02PhfTRifMRj;5]Rk#=1AKkRkeS03PkfURlfQRmfPRn35Ro#=1ARoRoeS04Pog00mLRp#^S05%MpRpP91N91P21N95C\Rq%[9Rr%Z9Rs1H9>R>1H9=Rt'D,9s%Y=,H9R=9R9tRu/F>,9s5Xs%W;RvPsP:P;P;P<1Ft>,9s1D>u,9s5VsEnCI1ms<RuP3P11;671l31#:dg00n8=k92CjRwb?bAbBX69X79X891?231@31/B2'CP2P1P1P2P5D4g00L8[[^69^79^89P3Pm17@PPXPMO4b;b<b=b>P1P3O4b2b5b4b5P6PB1388RxPaPjPLO1n0100000020000=2BaeW2n0110000020001P3O1b2b3W4n0110000020001P3O1b4b3P5P2O1PgP2O152BRaeW1X0APa\C^0APgP3O1%W?R?51BA0NQ2A0OM2'3P6P6P6PBP3P_P5O1fJRCP5O1n0100000020000=1B?P3P2PHP1P2O2n0110000020000b3P4P2O1Ra=1B?eW1X0A1EW1RyePy1?SN1@NQ/BS'CRyA0NP2P6PZPLPKP1P3C8P6PHPRP4P3C8P6PBP2P`POO1RzPjPOO1R{n0100000020000P6PBA0G[OR|/32PzP{n010000002000052B]2P2A0JQ5R}#:P6P7P6PBP3PzP{n010000002000092BzX36PjP4O1R{,;BA0TY4R~/37%T~EgW2%<}P~P6PZ1O|3P6PIPgPLP3C8PnPJO1R|P6PB1328PmPJO1P|n010000002000052B]4P2A0FWNR|#:P0%:^Q00[R^%:cRc\bQ01\cAf123P2n2001000000120000000X0AX:9X99RcP^^0A^:9^99R^P3PMPfPJP2O4PMPePePMPfD4Q02PhQ03PkQ04Pop-0RoQ05PpPqPrPs1F>t,9sAR9>=R=,Dt,9s5VsPvPs1Dt>,9s1F=t,9s5XsPvPsP:P;P;P<POEeCICIPuPwb?bAbBX69X79X89W@RwP2P3P3P2P1D41?211@15/B2'CPO[[^69^79^89^@oRoP3PlPIO1RuP6PB1378R<fVPIO1Pun010000002000052BP`PU17@IP4PFO6b;b<b=b>b4b5W4%<|P6PBPxPnPLO1P\PLO1n0100000020000,;BW4n0110000020100P3O1b4b3W2n0110000020001P3O1b2b3POP2O1R|92BaRaeW1X0APa\y^0APOP3O1=1B?A0LK2P6P6P6PBA0TY5Ry/33PjP5O1RaP]P5O1n0100000020000=1B?P6PBP2P`P4O1RuP{n0100000020000=1B?]1P3P6PBA0HX1R;/37P]P1O1R:P_P1O1Rsn0100000020000=1B?P613y7P6PBP3PuP{n0100000020000=1B?X36P3P7%TyEdA1Ba?P3b1W1P6PB13;8P:Psn0100000020000=1B?PyP6P6P6PB1338P\POO1R8Pzn0100000020000=1B?P\PNO1=1B?]1P3P6PBP<PuP{n0100000020000=1B?PMPOP3O2W1P6PBPxPuP{n0100000020000=1B?P3W1n0110000020000P2O1b3W1n0110000020000P2O1b3A1B|?eW1X0A1E45R|eP|1?SL1@LK/BS'CRSA0JQ2P6PZPHPRP1P3C8P6PGPXP4P3C8P6PBP2PnPOO1P8n010000002000092B8]2P2A0TU5R8#:PcP^P3PFPYPOP2O4PF17@OR@P@PFPYD4fR?5gWRF#=1AIFRFePFA5d]_Rd#=1APdRdePdA5in\Rn#=1AQnRnePnPwPoP3PiPTO1PlPTO152BPCPQPVP4PHO6b;b<b=b>b2b5W2%<81;BuW2n0110000020100P3O1b2b3P_P2O1PNP2O152BRueW1X0APu\S^0APNP3O1=1B?A0HR2P6P6P6PBP3P\P5O1P`P5O1n0100000020000=1B?P\P4O1=1B?]1P3P`P1O1=1B?PMP5P3O2W1PjP1O1=1B?P3W1n0110000020000P2O1b3W1X0A1EOCRAePAPEPjPNP_PCPfPgPWCQR_P[PYPXCQPUPRPQPEPjPLPNP_P[PYPXPEPjP]PLPCPfPgPWPKPPPOP4M<KPMP5P1M<KPIP2P3M<KbIbSbHbRbGbQbPbObVbUbTWKWLWFWEWDWJX]9X`9XYDX\9X_9XXDX[9X^9WWWZWNWMWCo"). Qed.

Lemma Forall_one' : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "h01Ah11Hh21Ph31xp;1p;2p;6p200R0g00nVR1p4p710p8g00Wej12Tg00o7j21TP1j60Tf0R1p-0[f1R2P2P1O1f3R3f2R4P2%23P11134E0W1W3W2X00o"). Qed.

Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "p'0h06__sat4h14__x1h23HKKh33Hinh41Hh54__x2h61ih71Ah81Ph97__arithh:4__ffh;6__sat3h<8__varmaph=5__with>4__x3h?1xh@2E1hA2E2hB3HaphC4__x4hD2a0hE1bi001bhF1dhG1mi011mhH1ni021nhI2n0hJ1BhK2HahL4Hap1hM4Hap2hN2HihO4__x5hP2b1hQ2b2hR1ei031ehS1fhT2hii042hihU1lhV2l1hW2l2hX2loi052lohY2lshZ1yh[1Eh\2H0h]2HKh^3Hhih_4Himgh`1Kha1Mhb1ai061ahc2a1i072a1hd2a2i082a2he1ki091khf2k0hg2n1i0:2n1hh2n2i0;2n2hi1vi0<1vhj1wi0=1wp%0p&0p;1p;4p;3p;5p;2p;6p;7p;8g002`j1LTg003Ej1lTg003cj1cTg00OZj1pTg00P<j1PTg00P\j4jTg00oXj4\Tg0105j33Tg010VR0j5wTg011:j2ok300Tg012<j3TTg012Sj3bTg0135k603Tg013Pj3]Tg014Rj2[Tg015Tj3ZTg016Vj2ETg0050j25Tg005Mj20Tg00Ulj2KTg00I@j2WTg00Wej1hTg005jj21Tg017Xj3DTg006eR1j2<Tg0185j2nTg0085j26Tg018Vj2mTg0196j1aTg019Tk20<Tg01:1k20;Tg00\5j1kTg00?cj3BTg007Yj2>Tg01:Wk40:Tg00=Ok209Tg01;6k206Tg01;^k305Tg01<Bk204Tg00XEj2MTg00YAk102Tg00Y_k101Tg01<cj2gTg00ZJj2NTg00];j2}Tg00]]j2|Tg00^Ij3{Tg00^hj4zTg01=Fj1STg01=ej2QTg01>Nj3XTg01?7j2eTg01?cj3YTg01@Cj1yTg00Zmj1dTg01@aj3xTg00=oj4OTg00o7j2vTg00[Rj3fTg01ADj2RTg01BFj3UTg01CHj2_Tg01DJj4^Tg01ELj3uTg01FMj3~j4tTg01GVj4sTg00bej4iTg00cPj7rTg00e<k807Tg00Xck408Tg00dXj7qTg00knR2f1R3f0R43~p=4g00ilR5f3R6f2R7@003433p=?AT534p=;A3534p=@P2P7P3P4Ctp=8P5P7P3P4Csp=Ag00@=R8?B34p=J1E73=Y54p=9g00@]R99B84p=Gg00JL9B84p=2g00n8R:/>4p=:1>671634'<p=C1>73/<4p=`g00AnR;P3g00hFP4Cip=FP3g00fGR<g00ffR=P=g00gFR>P4g00gfFrp=7P6P<P=P=P>P7P3P4L07p==P;P7P3P4H08p=HP;P3g00e`P4Cip=IP7P<P=P=P>P3P4Fqp=Vg00hmg00BLR<#LR?#LR@#LRA#L#L#LRB#lRC#c%lA#cRA#pRD[%P5REP2f4RFP6P7CjP0p4p710RGP0p4p7210R0p-0\4RH%P7RI%P6\6RJP1PFP6P4P3C\9367f5RKP7P4O193KFXFK;37RL[P3P4O193F6XFF=3F3PKPFP3P7C\93F6[RMf6RNPKP7P6C\93KF\LPFP6P7P3P4DwP4n2001000000120000000WSWYW8WJW7PM^SJ^YI^8H^J0^7GP4P5P514NKPF1o67g01HZp4p710RG%P3R0P1A3734ATF47PFP3O1[^?6RJ[AT643P6P3O1[^?7A3673RM[RLA3F67RO\JAb734P4n2001000000120000000WUX8HW7PL^U0^8H^7GP4P5f8RLf7RJ'4PKPFP4C?XF5PK1;4Nf9RP/4LRQ/@J1;4PRRf<RSf;RT;83RU[^?5[1;4Lf:RV=8T3[^?514VP/@L[Ab5QJPFP3P4J03A8PL3P5f=RQ/4SPVPPP7C?^2U^3RP7g01I7RRg01J8RUg00jnRVA]734f>RW';fARXf@RYA]67338fBRZ/4XR[A]F67R\;A4P[f?R]PWP\C?eW2W3WiWjWDP7P3P4O31[34/;S1[7398]W14Y]R\1[67R^;A4P\PQPSP^C?eW2W3XIVXDRP3P4O2AZ734/;WAZ67398XYAZF67R^=A[4P[P]PWP^C?eW2W3XfUXIVXDRP7P3P4O31E34/;S1E7398]W157Q10QS/56'KP81W84S00156W10WQ/5F'K/J4P815KY10Y]/5N'K/J4fDRUfCR^'4R_P8PEP3%h5R`99JNP8PE11JXA9JX`P`n0100000020000P8PE10XYRa/1NA9aN`P`n01000000200005D5n0100000020000'@]BP315F]10]W/5K'KRb#G14^Z1ENK;A6WB%2bP11K34#2%27Rb%23Rc'<[Rd%24,<c1K73#2Rc[%26/<b\c1n34P3n2001000000120000000XQ8XP8Pd^Q8^P8P415NXRN15aJRaP3O3%2N%2a'<P115JZ#210ZX/5L#2fFS01fERJ'4P8PE11P^A9P^`P`n0100000020000P8PE10^ZRa/1LA9aL`P`n01000000200005D5'@P415PU#210JU/5T#2P11534#21637S02[RP1643Ra1573#2RN[1676\N1m34P3n2001000000120000000XZ;X?;RNPP^Z;^?;RPP4PSfGRdP7O316dSPNPPP4fIRPfHRN'0RcP]P6O316]cP1%:Y%a?Rc%aBRB+0<RbPXP4P4PYCCfNRe20;C3RfO1%kARA5BD[^6;5`]fMRg,4eP8PEfKRh,1XA9Xh`P`n0100000020000P8PEfJRi,0hRj/1YA9jY`P`n01000000200005D5'@PQ%:ZPUP4P4P^CCfQRjPfO1=BDA[^6;9`ZbP11>^bPJP4P4PUCCfRRkPfO1=BDA[^6;14kjP8PEfORl,1JA9Jl`P`n0100000020000P8PE10leRm/1UA9mU`P`n01000000200005D5'@P41>JbPNP4P4PdCCfURdPfO1=BDA[^6;P1AD6349367A3F63,<ORO[A3674,<MADF7393F6[RMADK6793KF\OP6P7P3P4H0:P4n2001000000120000000XWIXV0X8HX7GPM^WI^V0^8H^7GP4P5fVRG/4dRHP8PEfSR0,1PRIA9P0`P`n0100000020000RMP8PE100kRO/1NS03A9ON`P`n0100000020000RO1@HM1@HOPIP8Q00fTRI,1i/J4P8fLRO/1G/J4fZRHfYRM'4S04P8PEP3fWRN=9g`P`n0100000020000'@]@P311hdRJ#GP11134#G1673[R116341173#GRm[1667\m20934P3n2001000000120000000XG;XH;S05P1^G;^H;S06P4PgPNP3O316gNf[R1/4HS07fXRm,EeRn%:e1>mbRoPlP4P4PMCCRlf\S08PfO1=BDAS09[^6;RA'<206cBRD16:cRf%:B16:b[Rp[Rq%:cRrg00K\RsB05cB3UWKRB%:b\s^KrRrP3g01JW204:c'WPfeO1RfPpg00mLRs#hRt%PsRu1M;3S0:&02;Rv&01;Rw1g;:Rx1N;<Ry'F,7wRz%k=R=PzC=1}w>R>P4P71W891|47#GdA{;:3CzR:b:b<b=X1;%:4%:3[^1;P4PkP]O2b9b0b;b0PoPAPDPqPBPrPfPpg01K=RA#SRo#SS0;,Q;1Q;o1Q;A5X;RA5X;g01K\Ro'e=YstR9Pu%y;Rz1M;7R{7H3PvPw%d<,N;R<,Iy,7wP=Pw1g;c=x;CRC,F<,7wP=1FyC,7wRCC=C=P>P:b:b<b=X1;X5;1>7bRcPc[\a^1;^5;P4PjQ08PUPTO4b9b0b;b0PLP3PDPqPBPrPfPpP9Pu1M;F?H7zRa1M;6Rc7H3PvPw1N;?R|,Fy,7wR}1N;@R@,I|,7w5VwP=Pw1I@<,7wP=1I|<,7wR~9Vw}S0<C=C=P>P:b:b<b=X1;X5;X>;XC;P4P3P3P6CC16F6P7P6P6PFCCR}[[^1;^5;^>;^C;P4f^S0=P0PKPIPFQ01O6b9b0b;b0O2XNlX6;COCOA81Hne3Ab@b4W@%2J14Mm,v5RJW@n0110000020100P4O1b@bEQ03P8Q0010I0/1P/J4P810Gd/1h/J4Q04P8PEP310NGRG?9O`P`n0100000020000'@]AP310dI/1iRi#GQ05Q06P4PGPOP3O316GOQ0710mNRN/EgRG%:N1>gbRg10MmP4P4PeCCReQ09[^6;Rm'<PDPqPBPrPfPpP9PuAH{3cPvPwAf;y|Rc,I<,7wP=Pw1Fx<,7wP=1Fxc,7wC=C=P>P:b:b<b=X1;X5;X>;1043,67%:61076#:[[^1;^5;^>;P4PkP1Q08PZP]O5b9b0b;b0PgPmPDPqPBPrPfPpPtPuQ0:PvPwPCP=PCC=P>P:b:b<b=X1;1>4b1>3b[^1;P4PjPTO2b9b0b;b0PLP3PDPqPBPrPfPpQ0;#S,Q;=X;A/eo=YstPu1M;K?H6z9Ha3PvPw%d?,N;9f;@R@/F|,7w=Vw~P=Pw1Iy@,7wP=Q0<C=C=P>P:b:b<b=X1;X5;X>;XC;XO;106FQ027`310FK,63P}[[^1;^5;^>;^C;^O;P4f]Q0=P0PKPIPFPUO7b9b0b;b0O2XNeX6;COCOA81HGe3AbAb4WA%2iPJWAn0110000020100P4O1bAbECOO5b4W_W^P3P4O2n2001000000121000000W4W\P3P4O2n2001000000121000000bMb4bLb4WMWLP3P4O2n2001000000121000000bBb4WBn0110000020001P4O1bBbEP\PQPS1E67C?eW2W3XT;XX;P3P4O21R34/;S1R7398]W1R67RJ=A\4P\PQPSPJC?eW2W3XG;XRVP3P4O2AU734/;WAU67398XYAUF67RJ=A[4P[P]PWPJC?eW2W3XT;XX;XRVP7P3P4O31_34/;S1_7398]W1_67R]=A\4P\PQPSP]C?eW2W3XI;XDRP3P4O2P6P7P3P4C^/;YPFP6P7P3C^98^ZPKPFP6P7C^R^=A_4P_PXPYP^C?eW2W3Xh;XdRXg;XcRP6P7P3P4O4n0110900083010610=10<2010610230106102109211051042010310130103105104201061024010710:10810;P3P4O2b2W3X`5O4b4O6b4P2PKPFAu673CjeW]XH;Xb;WeWaW[o"). Qed.

Lemma u_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "h02Hah16__sat1h21Eh37__arithh44__ffh56__sat0h68__varmaph75__witp;1p;2p;3p;4p;7g002`j10Tg0196j18Tg01;6j2?Tg0085j22Tg007Yj21Tg019Tj2MTg01;^j3CTg01<Bj2>Tg00I@j24Tg00Wej1<Tg00P<j1;Tg01@Cj1:Tg00YAj19Tg00Y_j1NTg01<cj27Tg00bej45Tg003Ej1LTg01@aj3KTg00dXj7BTg00];j2@Tg00]]j2ATg00?cj33Tg00^Ij3DTg00^hj4ETg006ej2=Tg01LHj2FTg01MEj1GTg01NEj2HTg004Fj2ITg00cPj7JTf1R0g00fGR1g00ffR2P2g00gFR3f0R4g00gfFJp=6g00hmg00n8R5g00BL#0R6#8R7%06#0#0#0#0R6#8R8'?1257R911581M78R:,25R;[R<[1157R=g00K\R>AC780UW0115:\>^0=P0g01JW1>57'4P9eO1P<g00mLR<#<%;<g00AnR<#:%9<%N<R9P1P2P2P3P<17<5R2g00hFP2C5,69P<P2g00e`17<7%L6R65K<C5,69FB1@93P4f2R9g00@=R3g00@]R7'41A49=337dAD<50CEb4b6b71155/=;P4b3b1b5b1'F%G5,H4,I6=3<5eW2o"). Qed.

Lemma flat_abs0 : forall E off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z ->
  flat E (SA (ELit 0) off) n.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "h02Hah16__sat2h24__x1h34__x2h41Eh52H0h63Hlth72Hnh83Hnwh97__arithh:4__ffh;6__sat1h<8__varmaph=5__with>1nh?3offh@1zp;2p;1p;3p;4p;6p;7p;8g005Mj22Tg002`j15Tg0196j1?Tg019Tj2^Tg007Yj26Tg0085j23Tg006ej21Tg01;6j2HTg01;^j3FTg01<Bj2ETg00I@j2>Tg00Wej1BTg00P<j1]Tg00XEj2UTg01@Cj1TTg00Xcj4QTg00YAj1PTg00Y_j1NTg00ZJj2=Tg01<cj2<Tg003Ej1JTg01@aj3ITg00bej4;Tg00\5j1GTg00[Rj3:Tg00];j2KTg00]]j2DTg00?cj3LTg00^Ij3MTg00^hj4CTg01MEj1OTg01NEj2@Tg004Fj2ATg01OEj1RTg00O<j6STg00Qcj2\Tg01PDj1[Tg01QDj1ZTg00Rdj3VTg00cPj7WTg00dXj7XTg00e<j8YTg00n8R0f0R1'6p=0f1R2g00fGR3g00ffR4P4g00gFR5P1g00gfFWp=4g00AnR6P2g00hFP1C;p=7f2R7P3P4P4P5P2P1FXp=9f3R8P3P4P4P5P7P2P1GYp=8g00hm%02R31287g00BLR9#5R:#?R;%5:#5#5#5#5R<#?R='^R>'6f4R?/3>P6P0f6R@,21RA#013A>f5RB#0RC12AB/6>'1'1'1X@61H;=130;RA%0=130>[RD[%0;REg00K\RFAF;=2UW0%0>\F^0EP2g01JW1E0;'>PAeO1PDg00mLRD#B%]DP61U67P2%T6CQ%P6%N6RDP61=69R9g00e`RA1<6;%J<R<5I6R;C;,4D%G4R4PD1=6:R:9:69/7;,4DP4PD1<60RE/7:,4DRFP4PD17E9,4DP4A:6E9R9,7E,4DP6P9PAP;C;,4DA:69:/7;,4D99DF59D59DC8C8C8C81KD5P1P7g00@=RDg00@]R5'>1D17=LD5dAM602CCb:b<b=X26X36131>1227/6>%08R8120?R7#0137>127B/6>,1C'1'1\8[[[^26^36P1f8f9P?PBP@f7O6b9b1b;b1%O0R0,@@,A<%R@ES1\0BR0#[,@@,A<%Z0'2R<#013<>%0?12<?/6>'1'1'1eAV@0?eW6W8X73W5X>6X?6W4o"). Qed.

Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "p'0h01Hh12H0h21bi001bh31ki011kh41zi021zh51ni031nh62opi042oph72e2h81ei051eh92e1h:4e2_1h;4e2_2h<2sxi062sxh=2Hah>7__arithh?4__ffh@6__sat1hA6__sat3hB8__varmaphC5__withD2b1i072b1hE2b2hF2e'hG2e0i082e0hH1ii091ihI2k0hJ2loi0:2lohK1EhL1GhM6__sat0hN6__sat2i0;1ai0<2b0i0=3op0i0>1pp%0p&0p;2p;1p;3p;4p;7p;6g01RCR0k20:Tg01Rck109Tg00?cj30Tg002`j1YTg003Ek100Tg01NEj23Tg004Fj2@Tg003cj1XTg01:1j2ATg01Sfj2tTg01TXj4pTg005Mj2?Tg01U4k108Tg01MEj1bTg00I@j2\Tg01UUj1wTg0196j1gTg01;6j2vTg0085j2jTg007Yj2[Tg019Tj2sTg01;^j3rTg01<Bj2qTg00Wej1oTg00P<j1nTg01@Cj1mTg00YAj1lTg00Y_j1kTg01<cj2fTg00bej4eTg01@ak307Tg00dXk706Tg00];k205Tg00]]k204Tg00^Ik303Tg00^hk402Tg006eR1k201Tg01LHj2~Tg00O<j6aTg00HEj6]Tg01V6j1OTg01W6j37Tg01X6j2}Tg01Y1j3|Tg01YUj2GTg01Z;j2ETg00\Wj6{Tg01Z[j4zTg01[Dj1`Tg01\Gj2_Tg01]6j3yTg01]^j2xTg01^[j3MTg01_[j3NTg01`[j3LTg01a[j4JTg01b[j4TTg01c[j4WTg01d;j6^Tg00cPj7uTg00jnR2g00AnR3f1R4f0R5CWp=5P3f4R6f3R7f2R8P4P5Eap=C1A459078p=cP2P3P5g00n8R9CWp=>f5R:1@84/?5,A7706p=4P6P3P7P8P4P5E^p=iA0345p==P6P2P7P8P4P5E^p=hA0245p=11345,@8p=B1?45,A8p=FP4g00fGR;g00ffR<P<g00gFR=P5g00gfFup=dP2P6P7P8P4P5E]p=6P2P3P4P9CW=085p=9P6P3P7P2P3P8P9CWP4P5E^p=8A0395p=<P6P2P7P2P3P8P9CWP4P5E^p=:P3P9P7P8P4P5E]p=;P2P3g01dXR>?745P9CWp=ZA7>45p=2A7>45,38p=Dg01eD?745p=Hg01f0?745p=Ig01f\?745p=Ug01gH?745p=Qg01h4?745p=Vg01h`?745p=Rg01iL?745p=Kg01j8?745p=Pg01jd?745p=Sg00hm20:23R?&098154530g00BL#YR@#Y#Y#Y#Y#YRA$00RB13:5RC'@RD%XBREf6RF/341AB5RG30X43PE1ABDPC1tBCCp1?D9RH&08DDCXF2PEPCPBPHCc^F2P2P2P?P5%b9RH/55RC%>4g01kPRDP?P8P2P?P51585RI%>6RJ%>FRKPKPKPKf7RK#>RLPLn0110<000810102101033010=10;1073010=10;1073010=10;1073010=10;1074010610:10310840106101109103%>7RLPLPLPLPLPLPLPLPLn01104000:00000000000000000000PLPLPLPJPJn01105000810102101033010410010<3010410;1003010410;1003010410;1004010610:10310840106101109103156750?PE13K4PBPB13K:P6E4]0P615:6RJ90?CP?P0P2P3P3P5P5n200110>000120105102S00X8?RC15H415F:RLP5Di1=4:P?P0P2P3P2P5P4n200110>000120105102S01X8?R015H815KFRMP4Dh11HKf8RN,1HPHf9RO,=:f=RP%bFRQ'3RRABBP4f:RS5FBRT50E[X221=6NP3P:PEPRPBPB13PHP5E4X33P3P9PE1ABFRRPB1?5FCcX43P:A0ERGX431AB:RG,\E1?9:%w:DC1AB9,@B%g@R@%gARA'vS021j9@RU1[9A1s@ARV,j9RW[RX[S031[9@RYg00K\RZAr@A4UW=S041[9V\Z^=YS05P4g01JW1q9@'\PUeO1S06PXg00mLRU#oS07%nUS08%m3S09%l3S0:%k3RUP;P<P<P=P31f39RYg00hFPYCe,dUP3PYg00e`1f3@>073BS0;Ce,dUK06205U=S0<P5P8g00@=R@g00@]RZ'\20458=0@ZdB03394H02S0=b?bBbC1[99001WP5b>b@bMb@,~9EaPEf<RW%b:RZ'3PBPB13WHP:E4ePOP5E]W0POP5D6W0P5O1b1P5O1b1W0X43P5O1g01J8RH%O5RA=9?JP?PC%O4RJPLP5D8%<:P?P0%O8RLPMP4D:11LK%O7RM/1N%O6R[%<OR\%OFR],3PR^=0ET[X22%<NPEP^PBPBP^P5E4X33PK%O:R^O1POP5C;W0POP5D6W0P5O1b1P5O1b1W0W5P5O1PDP?P8P2P?P5PIA7784RI#>A7:67RT#>R_P_P_P_A7F:6R_#>R`P`n0110<000810102101033010=10;1073010=10;1073010=10;1073010=10;1074010610:10310840106101109103A7845R`#>RaPaPaPaPaPaPaPaPan01104000:0000000000000000000015ONRa50?PDPDP?P5P2P?P81565A7467Rb#>A77F:#>RcPcPcPcA76KF#>RcPcn0110<000810102101033010=10;1073010=10;1073010=10;1073010=10;1074010610:10310840106101109103A7578#>RcPcPcPcPcPcPcPcPcn01104000:00000000000000000000f;Rc/5SRd50?PEf>Re/3bPBPB13eWPcE4]0P7P2P?P415751Z781Z:6RbPbPbPb1ZF:RbPbn0110<000810102101033010=10;1073010=10;1073010=10;1073010=10;1074010610:1031084010610110910315SORb50?P2P2P?P515:5Rf12:4Rg#>1ZK7RhPhPhPh1ZN6RhPhn0110<000810102101033010=10;1073010=10;1073010=10;1073010=10;1074010610:1031084010610110910315WcRh50?PEf?Ri/3gPBPB13iPPWE4]0P815PWRg90?fP?PC15F415ePRfP5Di1=4PP?P015K815ieRjP4Dh11Kif@Rk,1NPOfARl,=:fERm?DcQRQABBm4fBRn5FBRo50E[X221=6kP3P:PEPQPBABBmcRQ/?5CcX33PEfDRp/3SRq/}GRr1?QFRs,ABRt90E5X2Eg01l<Ru%X5Rv%X4RwP1%X8?0451@781@74'=R1[1@841@85'=%X7?084[Rx%X6?078\1A|845P5n2001000000120000000WEWDW5Px^Ew^Dv^5uP5PB1@BRRR,?QRu,ABRvPt1GBufFRw=BBWRx/?KR1,AB,@BRy,=5X431GBFRz1?x5R{,GB/=yX431GBsRy1GBK,?x,GB/=5X431?QzR|/EV1GB1R},=5X431EFVR~1E{V/=}X431EsVR}1EKV,?x/EV/=5X43P}1E1V,=5X431\3}1?Q~/EVPQPFPVQ02Q03Q04Q05Q06PXQ07Q08Q09Q0:PUP;P<P<P=P3Q0;g01lZPYCe,dUE{Q0<Q0=b?bBbCA03V9g00L8[P5b>bAbNbACzDCPy%`sDCPz%`FDC1GB|%`|DC1@Bt1_BsDCPR1_BFDC1@Bv1_BuDCO4b01@Bq=FB:Ru90EreAy>qG1xqGEaADpSZ=0EuePlP5E]W0PlP5D6W0P5O1b1P5O1b1W0X43P5O112:A=9?gP?PC12FJPfP5D8%<PRfP?P012KLRLPjP4D:11Li12NM/1k12O[%<lR[ADmc]R]=0Eo[X22%<kPEP]PBPBP]P5E4X33Pi12S^O1PlP5C;W0PlP5D6W0P5O1b1P5O1b1W0X5HP5O112O`15lkR`59?P?PC12SI15nlRIP5D8P[P?P0A7678,2cR^fCR]/5nRoP4D:11^]12WT/1p12P_%<mR_fIRTA7NKF7DiR^ABBT4=FBwRM50E[X22%<pRLPEP^PBPBP^P5E4X33P]A7KF:,2eO1PmP5C;W0PmP5D6W0P5O1b1P5O1b1W0X;2X:2X6DP8P4P5O3AM845R^,2O=9?`P?PCAM784Rj,2SPIP5D8P[P?P0AM678RJ,2cRAPoP4D:11A]AM:67RA,2W/1pAMF:6Ru,2PAMNKFRZ9DTiRq=0EM\_X22PEPqPBPBPqP5E4X33P]AMKF:Rq,2eO1PmP5C;X0LPmP5D6W0P5O1b1P5O1b1W0X;2X:2X6DP8P4P5O3g01mARGAN845R>,2O=9?`P?PCAN784Rr,2SPIP5D8P[P?P0AN678Rv,2cRRPoP4D:11R]AN:67RR,2W/1pANF:6Rs,2PANNKFRt9DTiR|=0EM\_X22PEP|PBPBP|P5E4X33P]ANKF:R|,2eO1PmP5C;X0LPmP5D6W0P5O1b1P5O1b1W0X;2X:2W6P8P4P5O3AL845Rz,2O=9?`P?PCAL784R`,2SPIP5D8P[P?P0AL678R[,2cRIPoP4D:11I]AL:67RI,2W/1pALF:6Ry,2PALNKFRV9DTiRT=0EM\_X22PEPTPBPBPTP5E4X33P]ALKF:RT,2eO1PmP5C;X0LPmP5D6W0P5O1b1P5O1b1W0X;2X:2X6GP8P4P5O3P7P8P4P5CJRL,2c=9?oP?PCP6P7P8P4CJR_,2W15p]RMP5D8%<]R9P?P0P:P6P7P8CJRU,2PRY15mpRpP4D:11YmPFP:P6P7CJRY,2e/1wPKPFP:P6CJR=,2ifGR<#<R;fKRXPOPNPKPFCJRQ7DlR~ABBX4fH5FBR}50E[X22%<wR1PEP~PBPBP~P5E4X33PmPNPKPFP:CJR~,2kO1P<P5C;W0P<P5D6W0P5O1b1P5O1b1W0X72X5HXJHX<@P7P8P4P5O4P7P8P4P5CTRx,2c=9?oP?PCP6P7P8P4CTRo,2WPMP5D8P9P?P0P:P6P7P8CTR9,2PRMPpP4D:11MmPFP:P6P7CTRM,2e/1wPKPFP:P6CTRw,2iPOPNPKPFCTRO9DXlRX=0E}\;X22PEPXPBPBPXP5E4X33PmPNPKPFP:CTRm,2kO1P<P5C;X01P<P5D6W0P5O1b1P5O1b1W0X5HXH3XIHX<@P7P8P4P5O4n01105000811102111033110410;1003110410;1003110410;1003110410;1004110610:10310541106101109103P5O1W01H84=9?bP?PC1H78PdP5D8%<SRSP?P01H67R<PhP4D:11<W1H:6/1P1HF:%<eR<1HNK,3nR1ABBn4=FBiRX50E[X22PEP1PBPBP1P5E4X33PW1HKFO1PeP5C;X0fPeP5D6W0P5O1b1P5O1b1W01I84=9?bP?PC1I78PdP5D8PSP?P01I67R1PhP4D:111W1I:6/1P1IF:1INK,3nR1=0EX\<X22PEP1PBPBP1P5E4X33PW1IKFO1PeP5C;X0fPeP5D6W0P5O1b1P5O1b1W01U84=9?bP?PC1U78PdP5D8PSP?P01U67R1PhP4D:111W1U:6/1P1UF:1UNK,3nR1=0EX\<X22PEP1PBPBP1P5E4X33PW1UKFO1PeP5C;X0fPeP5D6W0P5O1b1P5O1b1W01Q84=9?bP?PC1Q78PdP5D8PSP?P01Q67R1PhP4D:111W1Q:6/1P1QF:1QNK,3nR1=0EX\<X22PEP1PBPBP1P5E4X33PW1QKFO1PeP5C;X0fPeP5D6W0P5O1b1P5O1b1W01V84=9?bP?PC1V78PdP5D8PSP?P01V67R1PhP4D:111W1V:6/1P1VF:1VNK,3nR1=0EX\<X22PEP1PBPBP1P5E4X33PW1VKFO1PeP5C;X0fPeP5D6W0P5O1b1P5O1b1W01R84=9?bP?PC1R78PdP5D8PSP?P01R67R1PhP4D:111W1R:6/1P1RF:1RNK,3nR1=0EX\<X22PEP1PBPBP1P5E4X33PW1RKFO1PeP5C;X0fPeP5D6W0P5O1b1P5O1b1W01K84=9?bP?PC1K78PdP5D8PSP?P01K67R1PhP4D:111W1K:6/1P1KF:1KNK,3nR1=0EX\<X22PEP1PBPBP1P5E4X33PW1KKFO1PeP5C;X0fPeP5D6W0P5O1b1P5O1b1W01P84=9?bP?PC1P78PdP5D8PSP?P01P67R1PhP4D:111W1P:6/1P1PF:1PNK,3nR1=0EX\<X22PEP1PBPBP1P5E4X33PW1PKFO1PeP5C;X0fPeP5D6W0P5O1b1P5O1b1W01S84=9?bP?PC1S78PdP5D8PSP?P01S67RSPhP4D:11SW1S:6/1P1SF:1SNK,3nRn=0EX\<X22PEPnPBPBPnP5E4X33PW1SKFO1PeP5C;X0fPeP5D6W0P5O1b1P5O1b1W0n0110;000:01010101010101010101P5O1W0X72X92X6DP8P4P5O3A9?^aP?PCPjPbP5D8P\P?P0PJPdP4D:11Jc11AWPu13lZRZABBl4=FBeRu50E\fX22%<WRAPEPZPBPBPZP5E4X33PcPqO1PPP5C;W0PPP5D6W0P5O1b1P5O1b1W0X72X92X6DP8P4P5O3A9?>aP?PCPrPbP5D8P\P?P0PvPdP4D:11vc11RWPs13ltRt=0Eu\fX22PEPtPBPBPtP5E4X33PcP|O1PPP5C;X0APPP5D6W0P5O1b1P5O1b1W0X72X92X6GP8P4P5O3A9?zaP?PCP`PbP5D8P\P?P0P[PdP4D:11[c11IWPy13lVRV=0Eu\fX22PEPVPBPBPVP5E4X33PcPTO1PPP5C;X0APPP5D6W0P5O1b1P5O1b1W0X72X92X6GP8P4P5O3A9?LdP?Q00XG?P_PhP5D8%<cRcP?Q01XG?PUPgP4D:11UP11YeP=%<iR=13]QRQABB]4=FBkRk50E[X22PEPQPBPBPQP5E4X33PPP~O1PiP5C;X0<PiP5D6W0P5O1b1P5O1b1W0X82X5HXJHX<@P7P8P4P5O4A9?xdP?PCPoPhP5D8PcP?P0P9PgP4D:119P11MePw13]ORO=0Ek\=X22PEPOPBPBPOP5E4X33PPPmO1PiP5C;X0<PiP5D6W0P5O1b1P5O1b1W0X5HXH3XIHX<@P7P8P4P5O4n01105000811102101033110410;1003110410;1003110410;1003110410;1004110610:10310541106101109103P4O1bLW0X33X22X82WKo"). Qed.

Lemma split_lit_vars : forall n e b k, split_lit e = (b, k) -> expr_vars_lt n e = true -> expr_vars_lt n b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "p'0h01Hh12H0h22Hvh31bi001bh42opi012oph52n0h62e2h71ei021eh82e1h94e2_1h:4e2_2h;2sxi032sxh<2e0i042e0h=1ii051ih>2k0h?2loi062loh@1zi071zhA2_HhB1ki081khC1ni091ni0:1ai0;2b0i0<2b1i0=3op0i0>1pp;2p;1p;3p;4p;6g01RCR0j2ZTg01Rcj1YTg00?cj39Tg01MEj1STg00I@j2TTg01V6j1CTg01W6j36Tg01mmj2PTg01nmj3WTg006eR1j2UTg01^[j3GTg01_[j3HTg01`[j3ATg01a[j4JTg01b[j4KTg01c[j4MTg01d;j6OTg00HEj6XTg00jnR2g00AnR3f1R4f0R5CMp=3g00@=R61P45g00@]R739p=2P2P3P5g00n8R8CMp=:f4R9P3f3R:f2R;P4P5EOp=RA9345p=BP9P2P:P;P4P5EOp=QA9245p=0P2P9P:P;P4P5EXp=4P2P3P4P8CM=9;5p=8P9P3P:P2P3P;P8CMP4P5EOp=7A9385p=;P9P2P:P2P3P;P8CMP4P5EOp=5g01dXR<?645p=1P2P3A6<45P8CMp=NA6<45,P;=967p=<A9657p=Vg01eD?645p=@g01f0?645p=?g01f\?645p=Eg01gH?645p=>g01h4?645p=Ig01h`?645p=Lg01iL?645p==g01j8?645p=Dg01jd?645p=Fg01J8R<1Z23R=%Y;134539129:P2P2P=P5%S8R8/35R>%:4g01kPR?P=P;P2P=P513;5R@%:9RAf6RB#:RCPCPCPCf7RC#:RDPDn0110;000810107101093010=10:10<3010=10:10<3010=10:10<3010=10:10<4010310610910440103108105109%::RDPDPDPDPDPDPDPDPDn01101000:00000000000000000000PDPDPDPAPAn01102000810107101093010110010;3010110:1003010110:1003010110:1004010310610910440103108105109139:59=12C4f8RA/2B]2]0P9f5RD/39RE99=>%S4R>,2AP=P0P2P3P3P5P5n200110>000120102107RFX7=RG138;13CBRHP4DR1B;BP=P0P2P3P2P5P4n200110>000120102107R0X7=RI138:13ACRJP;DQ108Af9RK,08P8f:R8,BBf>RL/24RM[X321BDK1T67RNW0P8P5D4W0P5O1b1P5O1b1W2W0X@3P5O1%C5RO=8=E%C4RE,2AP=PG%C;RPPHP4D7%;BP=PI%C:RHPJP;D510HA%C9RJ/0K%CDRQ%;8RRPM[X32%;KP9W0P8P5D4W0P5O1b1P5O1b1W2W0X5<P5O1P?P=P;P2P=P5P@A6:;4R@#:A6D9:RM#:RSPSPSPSA6BD9RS#:RTPTn0110;000810107101093010=10:10<3010=10:10<3010=10:10<3010=10:10<4010310610910440103108105109A6;45RT#:RUPUPUPUPUPUPUPUPUn01101000:0000000000000000000013KARU59=f<RV/2@P?P?P=P5P2P=P:13D5A64D9RW#:A6:CB#:RXPXPXPXA69AC#:RXPXn0110;000810107101093010=10:10<3010=10:10<3010=10:10<3010=10:10<4010310610910440103108105109A659:#:RXPXPXPXPXPXPXPXPXn01101000:00000000000000000000f;RX,3VRY59=f?RZ/2Wf@RW/2L]2]0P9P2P=P;1395119:R[#:1NBDR\P\P\P\1NCBR\P\n0110;000810107101093010=10:10<3010=10:10<3010=10:10<3010=10:10<401031061091044010310810510913X8R\59=12L[P2P2P=P513C5R[11C4R]#:1NK:R^P^P^P^1N89R^P^n0110;000810107101093010=10:10<3010=10:10<3010=10:10<3010=10:10<4010310610910440103108105109f=R^,3LR_59=fAR`/2]fBR]/2W]2]0P913ZLRa99=[A<]A>P=PG13K;13`WR>P4DR1B;WP=PI138:13]`R[P;DQ108]fCRb,0XPVfDRc,BBfHRd/24Re[X321BDbfGRf/P^Rg?W79%VgA9677R7'UP112dLP7fIR1/2ZP5fJRg/2WP4XA7W2P4P5O2n2001000000120000000b2W0PcP5D4W0P5O1b1P5O1b1W2W0X@3P5O111CO=8=aA<]AEP=PG11KPP>P4D7%;WR>P=PI118HRHP[P;D510H]11XJ/0b11VQ%;cRQPe[X32%;bP9W0PcP5D4W0P5O1b1P5O1b1W2W0X5<P5O111XT13b]Rb58=fFRT?<V@P=PGA69:;,1^fER@/3cReP4D7PQP=PI11LMRM13T@R@P;D510MT11ZS/0fA6CBD,1W%;dfL/24[X32RS%;fP9W0RMPdP5D4W0P5O1b1P5O1b1W2W0X:2X92X4?P;P4P5O3AG;45RJ,1X=8=bAG:;4RH9<TVP=PGAG9:;R[,1^PeP4D7PQP=PIAGD9:R8,1LRPP@P;D510PTAGBD9RP,1Z/0fAGCBDRK,1WPSPMPdP5D4W0P5O1b1P5O1b1W2W0X:2X92X4?P;P4P5O3g01mAREAH;45Ra,1X=8=bAH:;4RO9<TVP=PGAH9:;R7,1^PeP4D7PQP=PIAHD9:Rh,1LRiP@P;D510iTAHBD9Ri,1Z/0fAHCBDRj,1WPSPMPdP5D4W0P5O1b1P5O1b1W2W0X:2X92W4P;P4P5O3AA;45Rk,1X=8=bAA:;4Rb9<TVP=PGAA9:;RX,1^PeP4D7PQP=PIAAD9:RQ,1LRlP@P;D510lTAABD9Rl,1Z/0fAACBDR@,1WPSPMPdP5D4W0P5O1b1P5O1b1W2W0X:2X92X4EP;P4P5O3P:P;P4P5CJRM,1^=8=eP9P:P;P4CJRS9<dLP=PGPDP9P:P;CJRm,1Z13fTRnP4D7%;TRTP=PIPBPDP9P:CJRo,1WRp13dfRfP;D510pdPCPBPDP9CJRp,1`/01PAPCPBPDCJRq,1]%;gfN/24[X32Rr%;1P9W0RsPgP5D4W0P5O1b1P5O1b1W2W0X62X5<X?<X;6P:P;P4P5O4P:P;P4P5CKRt,1^=8=eP9P:P;P4CKRe9<dLP=PGPDP9P:P;CKRu,1ZPnP4D7PTP=PIPBPDP9P:CKRT,1WRnPfP;D510ndPCPBPDP9CKRn,1`/01PAPCPBPDCKR1,1]PrPsPgP5D4W0P5O1b1P5O1b1W2W0X5<X=3X><X;6P:P;P4P5O4n01102000810107101093010110:1003010110:1003010110:1003010110:1004010310610910240103108105109P4P5O2W2W01@:;=8=\1@9:,2LP=PG1@D913^VRgP4D7%;VRsP=PI1@BDRrP_P;D510rL1@CB/0Z1@AC12c4\>X32R>%;ZRcP9W0RrPWP5D4W0P5O1b1P5O1b1W2W01?:;=8=\1?9:,2LP=PG1?D9PgP4D7PsP=PI1?BDR`P_P;D510`L1?CB/0Z1?ACP>PrPWP5D4W0P5O1b1P5O1b1W2W01E:;=8=\1E9:,2LP=PG1ED9PgP4D7PsP=PI1EBDR`P_P;D510`L1ECB/0Z1EACP>PrPWP5D4W0P5O1b1P5O1b1W2W01>:;=8=\1>9:,2LP=PG1>D9PgP4D7PsP=PI1>BDR`P_P;D510`L1>CB/0Z1>ACP>PrPWP5D4W0P5O1b1P5O1b1W2W01I:;=8=\1I9:,2LP=PG1ID9PgP4D7PsP=PI1IBDR`P_P;D510`L1ICB/0Z1IACP>PrPWP5D4W0P5O1b1P5O1b1W2W01L:;=8=\1L9:,2LP=PG1LD9PgP4D7PsP=PI1LBDR`P_P;D510`L1LCB/0Z1LACP>PrPWP5D4W0P5O1b1P5O1b1W2W01=:;=8=\1=9:,2LP=PG1=D9PgP4D7PsP=PI1=BDR`P_P;D510`L1=CB/0Z1=ACP>PrPWP5D4W0P5O1b1P5O1b1W2W01D:;=8=\1D9:,2LP=PG1DD9PgP4D7PsP=PI1DBDR`P_P;D510`L1DCB/0Z1DACP>PrPWP5D4W0P5O1b1P5O1b1W2W01F:;=8=\1F9:,2LP=PG1FD9PgP4D7PsP=PI1FBDRDP_P;D510DL1FCB/0Z1FACP>PrPWP5D4W0P5O1b1P5O1b1W2W0n0110:000:01000000000000000000P4P5O2W2W0X62X82X4?P;P4P5O3A8=JU12VHP=PGP[P\P4D7PRP=PIP8PYP;D5108V10P^PK%;L12]4[X32R]%;^P9W0R9PLP5D4W0P5O1b1P5O1b1W2W0X62X82X4?P;P4P5O3A8=aU12VOP=PGP7P\P4D7PRP=PIPhPYP;D510hV10i^PjP]P9PLP5D4W0P5O1b1P5O1b1W2W0X62X82X4EP;P4P5O3A8=kU12VbP=PGPXP\P4D7PRP=PIPQPYP;D510QV10l^P@P]P9PLP5D4W0P5O1b1P5O1b1W2W0X62X82X4EP;P4P5O3A8=M\12LSP=PFX<=PmPgP4D7PsP=P0X<=PoP_P;D510oL10pZPqP>PrPWP5D4W0P5O1b1P5O1b1W2W0X72X5<X?<X;6P:P;P4P5O4A8=t\12LeP=PGPuPgP4D7PsP=PIPTP_P;D510TL10nZP1P>PNX0cPWP5D4W0P5O1b1P5O1b1W2W0X5<X=3X><X;6P:P;P4P5O4n01102000810107101093110110:1003010110:1003010110:1003010110:1004010310610910240103108105109P4P5O2W2W0XB3X32X72WCo"). Qed.

Lemma kindex_some : forall p kn i j, kindex p kn i = Some j ->
  exists K, nth_error kn (j - i) = Some K /\ p K = true /\ (i <= j)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "p'0h01Kh11Hh22H0h31jh42HPh54__x1h64__x2h71ih81eh91ni001nh:4Hle0h;7__arithh<4__ffh=4__p1h>4__p2h?8__varmaph@5__withA4__x3hB4__x4hC4cstrhD5cstr0hE2knhF1xi011xhG2H1hH2H2hI3HP'hJ3HlehK2HnhL2IHhM2K'hN1bi021bhO1mhP1phQ4resthR1yhS2z1hT2z2i031op&0p;1p;3p;2p;6p;4p;<p;5p;Bp;7p;8g00P<j1pTg00OZR0j1oTg01oPj3BTg020Mj2DTg00?cj30j1]Tg020oj2=Tg021FR1j23Tg00Wej1^Tg00\5j1nTg00HEj6ZTg00Hak20=Tg00I@j2FTg01=FR2j11Tg01d;k600Tg006eR3j22Tg021`j1zTg00=oj4VTg022:j3TTg022XR4j2uTg0238j1tTg00O<j6sTg023]j4_Tg0247R5j15Tg0196j1qTg005Mj2:Tg024Wj29Tg0254k20?Tg025Wk30>Tg0264l<lTg007YR6j24Tg026Yj4kTg027@j1jTg027ej2iTg0085j2UTg00VIj2STg01=ej2HTg028Gk10<Tg028ek20;Tg029Fj3hTg01?7j2PTg01?cj3JTg00XEj2XTg01@Ck103Tg00Xcj4WTg00YAk102Tg00Y_j1~Tg00ZJj2LTg002`j1eTg00Zmj1{Tg01<cj2dTg00[Rj3cTg029oj3aTg00bej4\Tg00];j2yTg00]]j2|Tg00^Ij3}Tg00^hj4xTg02:Rj4gTg02;=k501Tg02;_R7j2wTg02<9j2vTg02<Vm<04Tg02=;mB05Tg01>Nk306Tg00`8k607Tg00cPk708Tg00dXk709Tg00d4k70:Tg00e<j8rTg00ilR8f0R9'Dp=Ef3R:f2R;f1R<5T8;09p=Rg00@=R=g00@]R>709p=612<9,2;p=`1w89p=;13<9,2;p=Cf5R?f4R@1=:;5T8;0</29p=7AJ8<9p=>AT8<9p=MA0=<>/29p=<A0:;</29p=Gg00n8RA/v9p=@g00AnRB?0<9p=Ag01J8RCPCPBPBP2P5P5P:g02=aP;P<P9N<04p=[PCPCPCPBPBPBP4P5P5P5f6R4g02>EP?P@P:P;P<P9NB05p=mPCPBP1P5P6g02>lP?P@P:P;P<P9M<lp=YA0B9Ap=NB06B<9p=?P<g00fGR6g00ffR1P1g00gFR2P9J07p=fPBP<g01lZP9C\p=OP<P6P1P1P2P9g00gfK08p=8P;P6P1P1P2P<P9K09p=QPBP<g00hFP9C\p=IP;P6P1P1P2P<P9K0:p=bP:P6P1P1P2P;P<P9Grp=KP=\8%p8R6P8%oCRDAB@;<1DC9RE30%o8RFP@1=;:%E9RGCRRHP4P9O1#6RI13:;RJ3`X08#;[^3C^7CXE6%^8RK=B:<=0DEPD%nCP0PCp-0RLP9g00L8RMg00K\n10110300021000000X8Dg00LU1DC<P9EZPMPFPKP:P@PGACI@:E7X08#;00=9b2W1X3CX7CAB?;<=0DEf7RIP9O1#6=`HJX08#;[^3C^7C1>@:=B4<=0DEPIP?O1P=1F=9f8REP4O1=0=9P=f:RJPEO1=0=9P=PDP<1DC4RHf;RK%14RM7BEn01000000200001DC?RN50DPF1>KJROPIPEPGf=RPP9O1#6RQ?CEIE7X08#;]1]4P<f9RRPIO1RS#61DC@RT90DNPDPCP0PCPCP9P9PIn10110300021010000X8DPHPNP9J00A0C4?A0CI4PCPEPFf<RN,>PP<PJPGf?RHP9O1#6R0?CJ<E7X08#;X3CP8PF1>NKRUPRPRPGf>RVP9O1#6RW13RRRX'2E7X08PKPCg01K=RYPF1MU9%ENPVPNO1/<XCGX9C%EKRX=0FXPPPKO1#6RZ13EER['2R\1FFXPZP[P:%zECVCVPFAT8OYPXP\CGe1uEE%tEEsC_PIP9EZW1P9O1b2W1W4g00JL90=S%1?9BJI=0DTPIPMP?P9O3PFPRP4%1IRMPGPNP9O113M4'<E7X08#;P7P8PFPJPI%1ER7PGACQ7IE7X08PFPUPEPRPGACWREE7X08#;P9PFPNPR%1JRWPGAC0WRE7P3PFPP%1KRW,=J%E<CRf@R0P<O113WJ'<PF1>0HPNPPPGfBRWP9O113PN'<E7X08#;P9PFPH%1P,=N%E:CRfCRNP@O1%1V/3P'<P3fDR3P?O1#6%1H/3VPF1>3NP0fARVPGfFRHP9O113V0'<E7X08#;P9PHPIO1#6%1W/3VP8PFfGRV/>HR01=N3RP'MPGfIRGP9O1133NRE'<CGX08PR%1NRR,=WRU#1R71=WNRQ50CRM%5WRT%5NRDg00BLRS#qR\':RO'9#@R[/:\RZ19TD#@R]'APCPB%]CP5%]B%5<%59'AA0C<920?<940>XRCXFCP7PZ1:9\RZXFBR7PUP[19<9#@XOBX9BR[PWPT1FBTRUPRPOP7PNPD1FBDR5C[R^FmC[PQP]P[PWPTPUPNPDP5FmM<l13RW14OTROPRP7PDO1P^PWPTPUEYP9CkPO%j3RO%53RU,4ARTPOPTfERT#5RO%5HRW'9R^,iA1UA^%@^RR/A^'214^A%NR'2'S%5VRR,9W#@PBfHRW#5R^/:\,9RR[,iA1UA[%@[R]/A['214[A%N]'2'S%5G/:\,9^#@PBg00mLR]%1YR[#1RQ#1#1R_#1,HB&0<S-0;BR`1HB_R_5hB1HBQRQ1HBYRY'?'?Ra'?g01K\Rb'P1HB[AhB`Q/?YRY'?,?_/Pb1?_Y/Pb1Pab%^]Rb5J]5J]5J]3J%p]R]PBPB1XB@P;&03BRaCWP<1XB:CW&02BRY%~BR_1f_41LBSRQ%eSR`#e,LBR[%{S,LBRS1dB\Rc5cBRd5aBRe'O,8_5Q_1dBARf,Ie,8_1OQf,8_5Q_5b_%n1R1P_PBPfg00e`AaB[SRSC\,8_1LB`R`/OS,8_5Q_1ISf,8_1f_I5Q_5b_P1P_1Id[,8_P1AcBQcRc/O`,8_CKCKCK1y_2R2P9P;1F=>1|9;#6dA}BA<CxR>b<b?b@X5BX6BXABXBBX=LX>L1:;\,9:R=,A9,2@14=A%N9'2'S19@:R=,UA1A;='214=A/24'S1:@\/4?1::\/A@[[[^5B^6B^AB^BB^=L^>LP9%N:fJRL#5R?fK#5R=/:\'9,UAP?P=P:P<P;P@PIO9b;bTbHbSbGbDbCb:CgPMPC%13RM,=NRI#1R@PF1>WV/M9PXPLPKO113T3'<CGX9CPFPHPI%EJRICRPGPJO1#6RJ/2ERGP4PJPEP;PE14UDP3PU1FBUREPNPDP5EY13MN1:U\/4DR\PMP7PUO1P7P3PUPEC[PNPDP5EYP<CkP\%jTRT14AOROPTPOPbP]PB1XB;P<PaCWPYP_1Ic`,8_P11IQ`,8_CKP2P>b<b?b@X5BX6B14Z<14<;[^5B^6BP9PRP^P:O3b;bDbCb:CgCVCVPF1M0@PIPGCGePPP9EZb2C_WJWIP<P9O2n2001000000121000000W2WKP<P9O2n2001000000121000000W2XM8P<P9O2n2001000000121101000b8W1W4n0110200020001P9P;O2b4bNW1X3CX7CWLXQ6X08P9I01WEWPo"). Qed.

Lemma ridx_lit : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "h04__x1h11xh23Hn0h37__arithh44__ffh54__p1h68__varmaph75__with84__x2h94cstrh:2H0h;2Hnh<1nh=1yh>1zh?2z0p;1p;2p;3p;<p;4p;6p;7p;8g01=Fj11Tg02?NR0j2GTg002`j16Tg00Zmj1qTg003Ej1_Tg0247R1j14Tg01YUj2WTg02?fR2j1BTg00?cj30j1DTg02<9j29Tg0254j2LTg025Wj3pTg00I@j2?Tg0264l<JTg0196j1]Tg0085R3j28Tg026Yj4YTg027@j1XTg007Yj27Tg027ej2VTg006ej25Tg00VIj2FTg01=ej2=Tg01>Nj3:Tg01?7j2CTg028Gj1UTg028ej2TTg029Fj3OTg00Wej1NTg01?cj3>Tg00P<j1MTg00XEj2ETg01@Cj1PTg00Xcj4QTg00YAj1RTg00Y_j1STg00`8j6oTg00ZJj2KTg00bej4<Tg01<cj2ITg00d4j7mTg00\5j1eTg00];j2^Tg00]]j2`Tg00^Ij3aTg00^hj4bTg02:Rj4cTg01Z;j2\Tg02@Fj3dTg00O<j6HTg01:1j2ZTg004Fj2fTg01\Gj2gTg02@ij1hTg02<Vl<iTg00cPj7jTg00dXj7kTg00e<j8lTf0R4#1#1#1#1p=2g00AnR5g01J8R6P5P5P2f4R2P1f3R7g02Agf2R8f1R9P4M<ip=nP6P5P0P1P3g02BTf5P2P7P8P9P4M<Jp=[P9g00fGR3g00ffR0P0g00gFR:P4g00gfFjp=3P8P3P0P0P:P9P4Fkp=AP5P9g00hFP4C<p=@P7P3P0P0P:P8P9P4Glp=;g01K=R;#1R<#1R=#1R>#1#2#2#2#2#2#2#2R?,G4P5g00BLR@#6RA#q#_RB%49RC'WRD%B4=068X>5REP5PCPE%BCRE=069g00n8RF/9CRG=05CP6P5%D6P1%D5%44905CA06941L943pX=6X16PEPGP4X1519F4X15PCPC1?5CRGDnP9PCPGM<J1G9?%6A#6#6#6#]RE,8CR1P9PCPGP?PE1?5EE[P4CYR?P1%X8RG%48,7FRH%47RI,VF18FI19FIRJ=05I'517IFA05JF'5'F%42RJ,9FP5p-0RIg00mLRK1=5=R=1=5<1=5;R;5:55:5g01K\R<'C1=5>%U@,T5=O5==:5;R;5:5/C<1C;<%NKR;5>K5>K3>%MKRKP51E58P9%P5CQ%R5R<%S5R=P=P3P0P0P:P=P3P0P0P:P2EoP51K5@R@g01lZR21K5ARAC<,3=R35A=1I5FR>,@A,3=P5P@P2P>C<,3=5A=Fm%e0R0P=1@>A,3=P0P3C;C;1^=:R:P4P8g00@=R3g00@]RA'?1`48=03AdAa5F9CbRAb4b6b7X05X85W5A0549,58179FA054F'5'F17F8R3A0587[[^05^85^5IP4f6#4RI,8FPIP9P8P7O5b3b?b:b9b2Cc1\CEP?P1PGPHP;PK1E59P<P=1@>@,3=R>P0P=P5P@g00e`1I5EC<,3=R@P0AA=>@C;C;P:PAb4b6b7X0517F4189E188E,53[[^05P4PJP9P8O3b3b9b29dCEEH%BD=069e1ZBCRD,fB1gBCEH%hD=069eW;X<6o"). Qed.

Lemma sr_get_nat : forall sr n, (0 < n < 32)%nat -> sr_get sr (Z_to_bv 5 (Z.of_nat n)) = nth n sr (ELit 0).
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "h04__x1h14__p1h23Hn0h37__arithh44__ffh58__varmaph65__with74cstrh81Hh91nh:1xh;1yh<1zh=2Hnh>3Hnzh?1bh@2srp;1p;2p;3p;6p;4p;<p;7p;8g00P<j1NTg02?NR0j26Tg006eR1j21Tg02C6j2@Tg00?cj30Tg00DSj17Tg02CSj2YTg002`j19Tg00Zmj1STg003Ej1QTg0247R2j15Tg01:1j2DTg004Fj2CTg02D4j3eTg01YUj2`Tg00I@j24Tg003cj1]Tg0085R3j22Tg0196j1ZTg02DWj6HTg026Yj4GTg027@j1FTg007Yj2ATg00Wej1XTg00XEj2WTg00YAj1VTg00Y_j1UTg01<cj2ETg00ZJj2RTg00bej4:Tg00`8j6PTg00\5j1OTg00\Wj6TTg00];j2lTg00]]j2kTg00^Ij3jTg00^hj4iTg00HEj6hTg01Z;j2fTg02@Fj3dTg00O<j6>Tg01\Gj2cTg02E@j3KTg01MEj1_Tg02@ij1MTg02Emj48Tg02:Rj4^Tg02FIj2aTg02GJj2bTg01=Fj1?Tg0264l<LTg00cPj7\Tg00dXj7[Tg00e<j8gTf0R4#?#?#?#?p=3g00@=R5g00JLR6704p==g01J8R7g00AnR8P0P2P3g02BTR9g01K=R:g00n8R;f3R<f2R=f1R>P4M<Lp=JP7P8P0P2P3P9f5R9f4R3P<P=P>P4M<Lp=IP>g00fGR2g00ffR0P0g00gFR?P4g00gfF\p=;P=P2P0P0P?P>P4F[p=<P<P2P0P0P?P=P>P4Ggp=Bg00jnR@#N16:4%3:#3#3#3#3#3#3#3RA,64'1P11@>4#=A08=>#7R1[A08>4#71@=>#=[RB1@<=#=\11Y>4P4n2001000000120000000X;8X:8PB^;8^:8P4g00BLRB#9R1#S#QRC%5=RD,DCRE'CRFg00LU9eC;RG,CCRHP81`CDRIA084H#7X<8RJP8PDPJ148HPG%]Ce,CC908;P8P;%53RJ=084#7X<816:<RK16<ARL'1%5<RM,2;RN%91#9#9#9#ZR1,2MRO'1RPPKPLPNPO148;ROP<PM148MRNCJP<PMPNPAP11481RNEIEHP=CGPP%F31A;Jp-0RJg00mLRP#XRL%NPRP1W8>RK%V8RQ%U8RRP81E8;RSg00e`RT1R8BRBC:,;RRUPRP2P0P0P?P<EPRV5<R%O0RWPRP2P0P0P?P8PBg01lZPSC:,;RETCB1lR?R?P4P=g00@]R0,451k4==050dAj8;>CiR0b4b5b6X08W112;4R2/1>A08>;g00L8[[^08^1JP4f6#5RX/21PXP=O3b3b7b2PHP4Ehb81fD116:=R:16=ARX'112;DRY12D1RZ'1R[P:PXPYPZPOP=PD148DROCJP=PDPOPAP1PNEIRNEHP>CGRAP[%F<RO1A;MRYPLPPPKPQPRP8PBPT1E81C:,;RRT9<RUPWP8PSg00hFPBC:,;R=<RTCBP?P0b4b5b6X081241RB,121A;>12>1R2'1[^08P4%59R9P=O2b3b7b29dD1E>A08IH#7ePF1cCDE>O3b8%5>,DCRD=KCG#=RFePFP5P6P5P@P4%_;R6P@1DCM#MP3P6C8n0100000020000P@P<P3P6C8RM50@X?5P7P=P@P4P3P6C8=0@MX97P@P=P<P6C8,4@%MEPXPZPNPAP[POPYPLPPPKPQPRA<RVTPWPTCBP?P0b4b5b6X08X1J11>BP2[^08^1JP412;9P9P=O3b3b7b2C^,a=E>AKCEGP4E>b>1b=DP@P>P=P6C850@eW=X97W@o"). Qed.

Lemma length_sr_upd : forall sr n e, (n < length sr)%nat -> length (sr_upd sr n e) = length sr.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "p'0h02Hnh11ni001nh24__x1h31eh43Hn0h57__arithh64__ffh74__p1h88__varmaph95__with:4__x2h;4cstrh<5cstr0h=2srh>1xh?2IHh@5cstr1hA1hhB1thC1yp;1p;2p;3p;<p;4p;6p;5p;7p;8g00P<j1ITg02?NR0j22Tg00Wej1MTg0247R1j11Tg00?cj39j1DTg0254j2VTg025Wj3STg00I@j23Tg0264l<ATg0085R2j28Tg026Yj4KTg027@j1:Tg01@Cj1ZTg00XEj2HTg00Xcj4GTg00YAj1YTg00Y_j1XTg01<cj2ETg00Zmj1WTg00ZJj2@Tg00bej4FTg00\5j1UTg00`8j6TTg00];j2RTg00]]j2QTg00^Ij3OTg00^hj4PTg02:Rj4CTg01?cj3;Tg01=FR3j15Tg0196j1dTg005Mj2=Tg00[Rj3LTg002`j1bTg00O<j6aTg02;=j5`Tg02HJj2JTg02Hjj3_Tg007Yj2]Tg00cPj7\Tg00e<j8^Tg02<Vl<[Tg00jnR4f0R5'Jp=0f2R6f1R7;_5,J4p=4g01J8R8?975p=6P8g00AnR9P0P1P2g02BTR:f3R;P6P7g01K=R<g00n8R=P5M<Ap=c1]=5p=7P7g00fGR>g00ffR?P?g00gFR@P5g00gfF\p=<P9P7g00e`P5CFp=?P;P>P?P?P@P6P7P5G^p=>P8P9P0P1P2P:f5R:f4R2P;P6P7P5M<Ap=BP8P8P9P9P3P1P1P;g02=aP6P7P5M<[p=N%I4R3P4%06,27A4;67%0;'6[^34^18R0X=3%M4RA#0RB,27A4A67RC/6B%1CRD%1BRE599P8P9%D8P1%D9%17R1%1559916751V753SXC8X>8PCPD139DPBPE139EM<A126<%16RD/8=RCP6PD139D139=CcP5CKPCA4A;6RC#:%1C#7%:2%12#7%:B%7Ep-0RBg00mLRC#MRF%ICRCP9%Z9RGP71H97CG%Y9RH%X9RIP91E9=RJg00hFg00BLRK#W,@9RLCF,<I%U?RMPI1?LJ,<IPMPIP>P?P?P@P;ETC>C>1RI@R@P5P6g00@=R?g00@]R>'31Q56=9?>dAO9=7CPR>b6b8b9X29W7%75187=P;[[^29^7BP5f7RBf6R=54A#1=99E%1BP6P2O4b5b@b<b;b4CCW0X34X18A;42;#0,27P8%0:#5RE,25A;4B=RA?47;%0A'6]0P6%02#5,2<138EA;4=:RE?4<6%0E'6eW0%55RE%0=#5'2P8%0BR<f8RA#0#5,6EX18%5<RE,38A4B72P=P7P2127<%1<R=,81P7P11391R?P<P=139=RLEB%57RJ/2E%dKRN,=11==N'8ROPJ1=5NRPX>9RQP1O1PQP7P1P?CNPEPQP=O1PQP<P=PLCNEBP5CKPO%:6%7Df9#0RD#:%1D#7PFPCP91H96P7PGCGPHPI1@9KRH1E9NRG5L9%bK,@9RK=L9G'?,<IPM1?HK,<IC>P@P>b6b8b9X29X:91=7N,8P1876[^29^:9P5f;#0#1%1:P;O3b5b<b;b4CCO3EaA;4ABRA?4J2%0A'6eW0X18P5O1n0110000020011100P5O1W0X34X18X?0XB3XA4P5D`W=o"). Qed.

Lemma nth_sr_upd_same : forall sr n e, (n < length sr)%nat -> nth n (sr_upd sr n e) (ELit 0) = e.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "p'0h02Hnh14__x1h21ni001nh31eh43Hn0h57__arithh64__ffh74__p1h88__varmaph95__with:4__x2h;4cstrh<2srh=2IHh>5cstr0h?1hh@1thA1xp;1p;2p;3p;4p;6p;5p;<p;7p;8g00P<j1JTg02?NR0j21Tg02Hjj37Tg01MEj1^Tg02Emj48Tg00?cj33Tg00Wej1CTg0247R1j12Tg0085R2j25Tg00I@j26Tg026Yj4BTg027@j1>Tg007Yj2:Tg00XEj2ITg00YAj1WTg00Y_j1VTg01<cj2FTg00ZJj2ETg00bej4DTg00\5j1TTg00`8j6STg00];j2RTg00]]j2QTg00^Ij3OTg00^hj4NTg01?cj39Tg01=FR3j14Tg0196j1MTg005Mj2<Tg01@Cj1PTg00Xcj4KTg00[Rj3HTg002`j1UTg02:Rj4]Tg02;=j5\Tg02HJj2[Tg0264l<GTg00cPj7ZTg00e<j8YTg02<Vl<XTg00jnR4f0R5'[p=0g01J8R6g00AnR7P0P1P2g02BTR8f3R9f2R:f1R;g01K=R<g00n8R=P5M<Gp=LP;g00fGR>g00ffR?P?g00gFR@P5g00gfFZp=;P7P;g00e`P5CDp==P9P>P?P?P@P:P;P5GYp=?P6P7P0P1P2P8f5R8f4R2P9P:P;P5M<Gp=@P6P6P7P7P3P1P1P9g02=aP:P;P5M<Xp=A%J4R1P4%0:,1;P4P:A79:;%^=R3C8=34;[^34^26R0X<1%C4RA#0,1;11:<%2:RB/5=RCP:PB167B167=CLP5CBPC%>9%29,:=p-0RCg00mLRD#CRE%JDRD1I7;%W7RF%V7RGP71F7=RHg00hFg00BLRI,E7RJCD,;G%T?RKPG1=JH,;GPKPGP>P?P?P@P9ESC?C?1RG@R@P5P:g00@=R?g00@]R>'61Q5:=3?>dAO7=;CNR>b6b8b9X17W71:=515;=P9[[^17^7CP5P4P8A7A82P3C8=342%28RAP;P:O4b5b;b4W0X34X26A9429#0,1;P6%08#4,15P4P;f7RCf6R?594?7;9P3C8=349]0P:%02#4,1<164:P4P<A94?8?7<:P3C8=34:eW0%45%0?#4'1P?P;P2%0CR?,1;%2;R<%2?R8'5P;P<167<RHP?P81678RLE@%4;RM%4?RN'1%MIRO,<<1<8O'5RPPM1<5ORQXA7RRP<O1PRP;P<PHCAPNPRP8O1PRP?P8PLCAE@P5CBPP%>:1:=Bf9#0RB#>%2B,:=PEPDP71I7:P;%P7CKPFPG1F7ORF9H7J%UI,E7RI=H7F'=,;GPK1=JI,;GC?P@P>b6b8b9X17X:71<;O,5Q15;:[^17^:7P5f;#0#2PAP9O3b5b>b;b4C]O3P4PMf8=94C?7M2P3C8=342eW0X26P5O1n0110000020011100P5O1W0X34X26X=0X@1X?4P5D\W<o"). Qed.

Lemma nth_sr_upd_other : forall sr n m e, n <> m -> nth m (sr_upd sr n e) (ELit 0) = nth m sr (ELit 0).
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "p'0h03Hneh11mh21ni001nh34Hne0h47__arithh51eh64__ffh74__p1h88__varmaph95__with:4__x1h;4__x2h<4cstrh=5cstr0h>2srh?1xh@2IHhA3IHnhB1hhC1thD1yp;1p;3p;2p;4p;6p;5p;<p;7p;8g00P<j1OTg01MEj1`Tg00DSj10Tg00Wej1UTg00?cj33j1LTg0247R0j18Tg0254j2sTg025Wj3lTg00I@j2:Tg02Ijj3@Tg026Yj4JTg01@Cj1aTg00YAj1_Tg00Y_j1]Tg01<cj2NTg00\5j1\Tg00`8j6[Tg00];j2ZTg00]]j2YTg00^Ij3XTg00^hj4WTg01=FR1j11Tg02Hjj3=Tg0196j1tTg005Mj2>Tg027@j1GTg007Yj2ETg01=ej2VTg028Gj1rTg028ej2qTg029Fj3kTg01>Nj3jTg01?7j2iTg01?cj3STg00XEj2hTg00Xcj4gTg00ZJj2QTg00[Rj3PTg002`j1eTg02:Rj4RTg00O<j6dTg02JSj6cTg02;=j5bTg02Emj4BTg0264l<TTg00bej4mTg00cPj7nTg00\Wj6oTg00e<j8^Tg02<Vl<pTg01J8R2f1R3f0R433#0p=4g00jnR5f2R6P3P4CBp=2P5f5R7f4R8f3R9;=6P3CB=354p=6A3234p=?g01K=R:=324p=AAS534p=5P5P9P6P3CB=354p=Cg00AnR;?334p=7P2P;P8P0P9P6P:g00n8R<P3P:P<P4M<Tp=fP;P3g01lZP4Cmp=FP3g00fGR=g00ffR>P>g00gFR?P4g00gfFnp=HP3P=P>P>P?P4Eop=IP9P=P>P>P?P6P3P4G^p=MP5P:P3P4CBp=9A3534p=;1:54p=<P2P;P4P0P3P6P9P8P7f6R@f7RAf8RBM<Tp=DP2P2P;P;P1P0P0P9g02=aP6P3P4M<pp=K%O5R0P51463R1P6P8P9P3%`<RCA268CE6[^55^12^22RDX>01?34RE#0P3%U5RFP6P8PCA23FCRGE6]0^12RHX22%A4#0RIP2P3157FPCPGCC^0IP3A32::RJ#0RKPKA3;<<RL#0RM%L2RN%L;RO%83RP%84'71s347lEXD2X?2RE1:;<RQPQDf9@JLP4CJRJPMp-0RQg00mLRR#URS%ORRT%a;RU%_;RV%];RW1N;<RX/FX,HW,IW%\>RXPWP=P>P>P?P6E[CM1ZW?R?P4P6g00@=R>g00@]R=':1Y46=3>=dAX;<3CWR=b6b8b9W7R>g00L8RY\LP3[^7QRQP415@F/9C19FCRL';P3O2b4b3W0%14RZ#A#0R[P2%13R\15BFPCA2\FCR]CC^0[P3%1:R^#A#0A2^FC#<W0%1ZR_#A#0%1\?2FC#<W0X12P4O1n0110000020010100P4O1W0X12P4O1n0110000020010100P4O1P3PFP:P9PCPGE6eW0X12%16R`/44RaP2%18Rb/44P3A=F7A,5CPCPGCC]0P3%19Rc=32:#0%<LW0%17/4ZP5PG1;4CX55P2%1A/4Z1;GC]0P3%1@RL/4^%<CRdW0%1B/4_PdW0X12P4O1n0110000020010100P4O1A=F@BRd=23CP7P31?@3R_#0%8@Re/7PRf#0PNPOPEP@Pe1:;eRgP3PP1:;PRhM9D9@_f1?L\Rf#0g00BLR_#tRi,>e1>PiRj'7#0Rk1>4iRlX?;RmPeO1RnPmPPO1Ro'7PNPOPEPLPnPmP@PePgCKP\PoPmP3PPPhCKRgM9D5@fP4CJPk%G6Rk%86,E<Rf%GB%8BRn,E<1V;^%r_,q;1V;:5k;5j;g01K\'i=SRSPTP;1h;6P3PUCgPVPW1Q;_RV1N;iRU5P;%e_,Q;R_=P;U'F,HW,IWPX1FV_,HW,IWCMP?P=b6b8b9X:;X;;R=1>3i,7lPY[1736PY[[^:;^;;RYP4%87Rlf:R?#8P9O3b4b=b<b3CRO2EdP\15CdPCP]CCeW0X12P4O1n0110000020011100P4O1P3PFPcP7PCPGE6eW0X12XAHX22P9P6P4EcX01X55X12X22P21449P815BARHP3P9PCA28HCE6]0P9%A6#0P2P3f9R6/5BRBP:P8PCA23BCE6^0IP9PJPMP>PQP41;7?P3O2b4b3A=H:9/9C19HC';eX0KA236C#<P\15?6R6P:P7PCA2\6CE6eX0[X12P4O1n0110000020010100P4O1W014Z8P2P3f;R[/5?RKPcP@PCA23KCE6^0aP7A32\:#0%<?A=6`7/9C196C';eW014cZP?P8P3PA1?83R?#0%88Rc/7PRZ#0PNPOPEP8Pc1:;cR;P3PPPhM9D9@?Z1?b\RZ#01>ci/7j#0RjPmPcO1Ri/7oPNPOPEPbPiPmP8PcP;CKP\PoPgM9D5@ZP4CJPjPkPf%G@1E<eP=PYP4PlPnP9O3b4b=b<b3CRO4P\f</5[R[PbPAPCA2\[CE6eW0X12P4O1n0110000020011100P4O1W0X22P4O1n0110000020111100P4O1X01X55X12X22X@DXC0XB5P4DbW>o"). Qed.

Lemma length_sr_after_call_j : forall sr kept nv, length (sr_after_call_j sr kept nv) = 32%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStdioCall ()) [] "h01ih14kepth21nh32nvh42srp;1p;2p;3p;6p;4g00P<j14Tg02K4j2;Tg02HJj22Tg00?cj35Tg00I@j2>Tg02KPj2<Tg00O<j63Tg02Koj1:Tg02LOj37Tg01MEj16Tg02Emj48Tg02Lkj29Tg01V6j1ATg00M_j4@Tg02MBj4?Tg02Maj3=Tg01=Fj11Tf0R0#1#1#1#1p=0g00jnR1#4g01J8R2#4P2g01K=R3%03#0#0#0#0#0#0#0R4';R5,22R6A5204X22R7P2P4P71>24P61<43E3P2P1g00@=P1%:0f2R3572P1P0f3g00n8#6C8f1R6/90#An0100000020000X02R7P5C@,21P2P1P7P5C?E3A=360,21=524eX32W1W4o"). Qed.

Theorem stdio_call_sound `{fx : DFP} :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z ->
  (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds mo) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_channel_reader mo = true ->
  lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x16cdd0) M (seg_rom RSEGS) ->
  K [] ->
  (forall R' M' msF' mo',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS) ->
     realizes RSEGS (mkCfg msF' mo') K) ->
  realizes RSEGS (mkCfg msF mo)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M L S Zr msF mo res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0x185ed0 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread RSEGS kn (ELit 0) 0x6e5898 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hwphi Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hrdr OK RS HKnil HCONT.
  set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
  set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
  set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
  apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
  apply andb_prop in Hcond as [Hf0 Hf232].
  apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
  (* [comment removed for export] *)
  assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
  { unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
    apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
  assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
  { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
  assert (R1 : getr R 1 = Z_to_bv 64 ret).
  { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
  assert (R10 : getr R 10 = Z_to_bv 64 f).
  { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    rewrite H10. reflexivity. }
  assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R11 : getr R 11 = s).
  { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R12 : getr R 12 = l).
  { replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
  set (sp := edenot E (nth 2 sr (ELit 0))) in *.
  pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
  pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
  assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
  { subst su. rewrite Hsqd. apply u64_lit. lia. }
  pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
  (* [comment removed for export] *)
  destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
  destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
  apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
  apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
  assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
  { unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
    replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C. apply flat_abs0; lia. }
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x185ed0 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x6e5898 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x16cdd0) with (0x16cdd0%bv : word) in RS by (apply bv_eq; reflexivity).
  eapply (as_stdio_write R M L S Zr msF mo su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
            pending extra K).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst'.
  - lia.
  - lia.
  - constructor.
    + rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rfd. cbn [edenot]. reflexivity.
    + exact Rbufp.
    + exact Rbufsz.
  - split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
  - apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
  - exact Hfdlk.
  - exact Hrdr.
  - exact OK.
  - exact RS.
  - lia.
  - lia.
  - exact Hlenp.
  - exact Hlene.
  - exact H30.
  - exact Dw.
  - exact Ds.
  - exact Hsl.
  - exact Rpend.
  - exact Rextra.
  - apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
  - exact HKnil.
  - (* [comment removed for export] *)
    intros R' M' msF' mo' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST OK' SB' HS' RS'.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply (HCONT R' M' msF' mo'); [ | | exact OK' | exact SB' | exact HS' | exact RS'].
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [(first [clear - Hfd12; lia | lia])|]);
            lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
              first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
            end.
        - unfold SC_KEPT. cbn [In]. lia. }
      apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
        [ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
      intros i Hi. rewrite length_sr_after_call_j in Hi.
      destruct (Nat.eq_dec i 10) as [->|Hne].
      * rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
        unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
        change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
        rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
        apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
      * rewrite nth_sr_upd_other by lia. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
      assert (HK3 : know_ok RSEGS E' M'
                (kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
                   (ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
      { assert (Eqb : edenot E' qb = edenot E qb).
        { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
          apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
        apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
        - unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
        - intros x N1 N2 N3. apply Pagree.
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. (first [clear - Hfd12 Hretv Hq N1; lia | lia]).
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
Qed.

Theorem stdio_call_sound_post `{fx : DFP} :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z ->
  (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds mo) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_channel_reader mo = true ->
  lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x16cdd0) M (seg_rom RSEGS) ->
  K [] ->
  (forall R' M' msF' mo',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     sw_post M su (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
     lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS) ->
     realizes RSEGS (mkCfg msF' mo') K) ->
  realizes RSEGS (mkCfg msF mo)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M L S Zr msF mo res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0x185ed0 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread RSEGS kn (ELit 0) 0x6e5898 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hwphi Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hrdr OK RS HKnil HCONT.
  set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
  set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
  set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
  apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
  apply andb_prop in Hcond as [Hf0 Hf232].
  apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
  (* [comment removed for export] *)
  assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
  { unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
    apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
  assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
  { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
  assert (R1 : getr R 1 = Z_to_bv 64 ret).
  { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
  assert (R10 : getr R 10 = Z_to_bv 64 f).
  { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    rewrite H10. reflexivity. }
  assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R11 : getr R 11 = s).
  { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R12 : getr R 12 = l).
  { replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
  set (sp := edenot E (nth 2 sr (ELit 0))) in *.
  pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
  pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
  assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
  { subst su. rewrite Hsqd. apply u64_lit. lia. }
  pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
  (* [comment removed for export] *)
  destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
  destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
  apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
  apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
  assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
  { unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
    replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C. apply flat_abs0; lia. }
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x185ed0 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x6e5898 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x16cdd0) with (0x16cdd0%bv : word) in RS by (apply bv_eq; reflexivity).
  eapply (as_stdio_write R M L S Zr msF mo su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
            pending extra K).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst'.
  - lia.
  - lia.
  - constructor.
    + rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rfd. cbn [edenot]. reflexivity.
    + exact Rbufp.
    + exact Rbufsz.
  - split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
  - apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
  - exact Hfdlk.
  - exact Hrdr.
  - exact OK.
  - exact RS.
  - lia.
  - lia.
  - exact Hlenp.
  - exact Hlene.
  - exact H30.
  - exact Dw.
  - exact Ds.
  - exact Hsl.
  - exact Rpend.
  - exact Rextra.
  - apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
  - exact HKnil.
  - (* [comment removed for export] *)
    intros R' M' msF' mo' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST OK' SB' HS' RS'.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply (HCONT R' M' msF' mo'); [ | | | exact OK' | exact SB' | exact HS' | exact RS'].
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [(first [clear - Hfd12; lia | lia])|]);
            lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
              first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
            end.
        - unfold SC_KEPT. cbn [In]. lia. }
      apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
        [ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
      intros i Hi. rewrite length_sr_after_call_j in Hi.
      destruct (Nat.eq_dec i 10) as [->|Hne].
      * rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
        unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
        change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
        rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
        apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
      * rewrite nth_sr_upd_other by lia. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
      assert (HK3 : know_ok RSEGS E' M'
                (kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
                   (ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
      { assert (Eqb : edenot E' qb = edenot E qb).
        { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
          apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
        apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
        - unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
        - intros x N1 N2 N3. apply Pagree.
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. (first [clear - Hfd12 Hretv Hq N1; lia | lia]).
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; (first [clear - Hf0 Hfd12 Hf232; lia | lia])|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
    + (* [comment removed for export] *) exact HPOST.
Qed.
