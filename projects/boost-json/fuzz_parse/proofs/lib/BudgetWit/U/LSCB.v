(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from U/LibStdioCall.v for the budget-premise witness: the same statements and proof scripts over BudgetWit.Rzb.realizes; only the name tables change. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the launch's channel reader. *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame Hoare.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefExitBase RefStdioDefs RefStdioWrite.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_LibStdioCallB () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indc89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall3inrC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib4Init5Logic3notC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes>Morphisms_Prop@not_iff_morphismC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismc89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall8inr_specC13~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2eq01C47Corelib7Classes?RelationClasses?iff_equivalenceK47Corelib4Init9Datatypes4bool02C47Corelib7Classes?RelationClasses=iff_SymmetricI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive;nth_map_seqC13~~~C47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S7know_okC13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX25saddr01C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S4flatC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S6estartC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib7StoreOk9mem_growsC13~~~C47Corelib4Init9Datatypes3orbI47Corelib4Init5Logic2or00c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall9inr_falseC13~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib4Bool4Bool:orb_true_rK46Stdlib9micromega5Tauto8GFormula03C79OSSVerify6Proofs:boost_json:fuzz_parse3lib<LibKnowFrame8kn_frameC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib<LibKnowFrame=know_ok_frameC13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX23env00C13~~~I89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry00C13~~~I89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr00C13~~~C79OSSVerify:boost_json:fuzz_parse6images5Ubsan1M?loaded_segmentsC13~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01K47Corelib5Lists7ListDef6Forall02K47Corelib5Lists7ListDef6Forall01C46Stdlib5Lists4List8flat_mapI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List?Forall_flat_mapc89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall9kimg_cut1C13~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry01C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry02C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry03C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry04C13~~~C47Corelib4Init9Datatypes3appC46Stdlib4Bool4Bool=orb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List:Forall_appC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd:and_elimF3C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry08C13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall8kimg_cutC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S9kentry_okC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall;Forall_one'C13~~~I46Stdlib5Lists4List6Exists00I89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX25saddr00C13~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8AgentLib7u64_litC13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr01C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26edenotC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall6u_lit0C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26a_baseC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX25a_offC13~~~I47Corelib4Init9Datatypes4prod00C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX29split_litC13~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7add_0_lK89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr02C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr03C13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec5v_addC13~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_rC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec=bv_wrap64_modC13~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec7alu_addC13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr05C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr06C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr07C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr08C13~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic7f_equalK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I4ELinuxProcessSemantics5Riscv5Instr5aluop00I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics5Riscv5Instr5mulop00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun<expr_vars_ltC13~~~C47Corelib4Init9Datatypes9andb_propC79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX6kindexC13~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3subI47Corelib4Init5Peano2le00K47Corelib4Init5Peano2le01C46Stdlib5Lists4List9nth_errorC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd9ex_elimF1C13~~~C47Corelib4Init9Datatypes8list_indI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z9mod_smallC89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24ridxC13~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK45stdpp9bitvector;definitions2bv01C46Stdlib9micromega;ZifyClasses9and_morphC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions4BvWfC47Corelib5Lists7ListDef3nthc89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall8ridx_litC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26sr_getC13~~~C47Corelib4Init9Datatypes6lengthC89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26sr_updC13~~~C46Stdlib9micromega;ZifyClasses9not_morphC47Corelib4Init9Datatypes7nat_indC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List:length_seqC56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_mapC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive?sr_after_call_jC13~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S7regs_okC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall:stdio_callC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall<lit_even_retC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX:is_kwr_covC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX2:base_rangeC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun:sr_vars_ltC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun:kn_vars_ltC13~~~k89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall9stdio_res01C13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive9junk_valsC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec7seg_romC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC57Corelib7BinNums6IntDef1Z3addC57Corelib7BinNums6IntDef1Z3subC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula01c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall:sr_get_natC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec4getrC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S@base_range_soundC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall?split_lit_denotC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec9u64_rangeC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall;kindex_someC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX28expr_eqbC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S;expr_eqb_eqC13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX<kwr_store_okC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall9flat_abs0C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26adenotC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX;adenot_lit0C13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC35stdpp7tactics<f_equal_helpK89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefStdioDefs7sw_file01C13~~~C46Stdlib4Bool4Bool8orb_propC79OSSVerify6Proofs:boost_json:fuzz_parse3lib5Hoare;ret_ok_evenC13~~~I89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefStdioDefs7sw_post00C13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun>vals_app_agreeC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun9env_agreeC13~~~C46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega5Tauto8GFormula02C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive?regs_after_callC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCallFlength_sr_after_call_jC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall=length_sr_updC13~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun7vals_evC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive>sr_vars_lt_nthC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun<edenot_agreeC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX=vals_ev_app_rC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall?nth_sr_upd_sameC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall@nth_sr_upd_otherC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX;regs_ok_extC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX<env_app_knowC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall>kimg_cut_soundC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall>split_lit_varsC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall>know_ok_frame3C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S;mkAlu_denotC13~~~C99OSSVerify6Proofs:boost_json:fuzz_parse3lib9BudgetWit1U4RSWB?ref_stdio_write13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX23env01C13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive5kreadC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX25mkAluC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall5sc_wbC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall5sc_wpC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall4sc_sC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall4sc_lC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall5sc_spC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec3rdnC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall5sc_fdC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyc89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall5sc_srC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall5sc_knC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall6sc_retC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec4mkstC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I89OSSVerify6Proofs:boost_json:fuzz_parse3lib9BudgetWit3Rzb8realizes00~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8ShapeAlg6t_emitC13~~~K46Stdlib9micromega5Tauto8GFormula0:C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive9kread_rdnC13~~~i89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall9stdio_res00C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX25two64C13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall7SC_KEPTC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib4Scfg=hunspell_scfgC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K46Stdlib9micromega5Tauto4kind02I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8ShapeAlg4TSetC13~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Zc89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall4sc_fC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall7sc_bufpC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<LibStdioCall8sc_bufszC13~~~".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04cons03nil06option37Corelib7Numbers7BinNumsj61Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~l34expr04None04bool04andb3h5LinuxProcessSemantics5Riscv5Instrqb5aluopqb5mulop04Somel35two6446Stdlib6ZArith6BinInt1Zud3eqbud3lebud3ltbud6modulol36kentryl35saddrud3addl34KImg03app03orb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcLibStdioCall4FPX1~~~~~~hk89kimg_cut136Stdlib5Lists4Listhpb8flat_mapj64Npos35stdpp9bitvectorbdefinitionshs12bvhs1bbv_unsigned04true37Corelib4Init5Logichv93andhv92eqhv93iffhk83inrud2leud2lt05falsehv93notl32SA79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~ik56estart69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLibKnowFrame~~~~~~ip48kn_frameik54flatik57know_ok69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~iv2floaded_segments69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~jjb9mem_growsl33envhk88kimg_cutl34ELitl36edenotud3pow04pair04prodl39split_liths17Z_to_bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~jsdcexpr_vars_lthv92ex37Corelib4Init3Natkhc3sub37Corelib4Init5Peanokj52le69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9SymDriveX~~~~~~kkf6kindexhpb9nth_errorkj52ltl34ridxud6of_nat37Corelib5Lists7ListDefkr83nthl36sr_get06lengthl36sr_upd69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~kv0fsr_after_call_j" s.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import LibStdioCall.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.Rzb OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.U.RSWB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* LPS 727298f3 port: statement and proof script of LibStdioCall.v [stdio_call_sound], over
   Rzb.realizes (the reader premise after fd_lookup, as there). *)
Theorem stdio_call_sound :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
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
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     Rzb.realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  Rzb.realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xe2ee8) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0xfbc78 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread RSEGS kn (ELit 0) 0x12ec38 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hwphi Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hrdr Hh Hlz HKnil HCONT.
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
  { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.sr_get_nat by exact Hn. reflexivity. }
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
  pose proof (OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
  assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
  { subst su. rewrite Hsqd. apply u64_lit. lia. }
  pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
  (* [comment removed for export] *)
  destruct (OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
  destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
  apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
  apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
  assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
  { unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
    replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C. apply OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.flat_abs0; lia. }
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0xfbc78 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x12ec38 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0xe2ee8) with (0xe2ee8%bv : word) by (apply bv_eq; reflexivity).
  eapply (ref_stdio_write R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
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
  - exact Hh.
  - exact Hlz.
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
    intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply HCONT.
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [lia|]);
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
        [ rewrite OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.length_sr_upd by (rewrite OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.length_sr_after_call_j; lia); reflexivity | | exact HRj ].
      intros i Hi. rewrite OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.length_sr_after_call_j in Hi.
      destruct (Nat.eq_dec i 10) as [->|Hne].
      * rewrite OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.nth_sr_upd_same by (rewrite OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.length_sr_after_call_j; lia).
        unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
        change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
        rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
        apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
      * rewrite OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.nth_sr_upd_other by lia. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.kimg_cut_sound, OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.kimg_cut_sound, HK').
      assert (HK3 : know_ok RSEGS E' M'
                (kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
                   (ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
      { assert (Eqb : edenot E' qb = edenot E qb).
        { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
          apply (OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
        apply (OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.know_ok_frame3 E' M M'); [exact HK0 | | apply OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.flat_abs0; lia | apply OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.flat_abs0; lia | | exact Pgrows].
        - unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
        - intros x N1 N2 N3. apply Pagree.
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.LibStdioCall.flat_abs0; lia|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
Qed.

End FPX1.
