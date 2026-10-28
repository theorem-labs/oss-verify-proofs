(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare RefMemcpyLib LibIface SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HWord HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_HEmpS () := "C46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C4ARocqVerifyHarness?AgentSubmission8PropExec=bv_wrap64_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions9bv_shiftrC45stdpp9bitvector;definitionsBbv_shiftr_unsignedC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5aluop07I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS9syms_sameC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sr_getC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28expr_eqbC4ARocqVerifyHarness?AgentSubmission7ZStores:forallb_InC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S;expr_eqb_eqC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC4ARocqVerifyHarness?AgentSubmission8PropExec4getrI5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit2gzC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3sh0K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr03C4ARocqVerifyHarness?AgentSubmission8LibIface3memK46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6nval24I5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5umapx00C47Corelib4Init5Logic3notI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_bseqC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind;BSEQ_boundAc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS4SENVC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4hmodc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS7senv_bcC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5u_hdrI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep3hdr00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6hdaddrC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7ZlengthC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell4C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7definedC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_hiC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_bl_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_bl_hiC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedK45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS8srl3_valC47Corelib4Init5Logic6eq_symK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01C56Stdlib6NArith6BinNat1N2leC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_mulC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond02C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS4KNBxC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_eqC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit:div8_boundC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9estart_shC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS7atLoopPC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6aonlyTI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z4of_NI47Corelib4Init9Datatypes6option00C4ARocqVerifyHarness?AgentSubmission8PropExec3rdnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic5proj1C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z;le_gt_casesC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics5Riscv3Sem<branch_takenC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6br_geuK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr04C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3sxwC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib9sextw_valc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS7atLoopMC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_addmC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell8I4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib9micromega;ZifyClasses5mkrelC4ARocqVerifyHarness?AgentSubmission8PropExec6v_addiC35stdpp7tactics<f_equal_helpK46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8v_addi_ZC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26adenotC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib=sc_read_cellwC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib7sc_flatC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS?syms_same_soundC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init5Logic4True01C56Stdlib6ZArith4Znat3N2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS4E_BBc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS3srBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8non_argTC46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init9Datatypes4bool02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS4E_NFc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS4E_LMc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS4E_LPI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI47Corelib4Init9Datatypes3nat00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS8SCR_B_b0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS7E_STOPSK47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS8SCR_B_q0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS7SCR_B_mK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS7SCR_B_pC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:in_app_iffC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_nodeC4ARocqVerifyHarness?AgentSubmission8LibIface4liveC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5apartC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_chainC47Corelib4Init9Datatypes8list_indC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5chainc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS8loop_resc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS6efoundC4ARocqVerifyHarness?AgentSubmission6CatSim<msteps_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit<aonlyT_transc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS7E_FOUNDc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS;node_factsEC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cellwC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib9br_ne_sxwC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib@sc_read_cell4_sxC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_neC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6br_ltuC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_remuC46Stdlib5Lists4List9app_assocC47Corelib4Init5Logic7and_indc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS=loop_res_consc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS3KNLc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS4srLMK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5mulop08C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind7land_1AC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_andc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS4srLPK4ELinuxProcessSemantics5Riscv5Instr5aluop0:C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5u_bktC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bucket_okC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5hdkeyC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind>in_split_entsAc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS7gz_subEC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4h_p1c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS8emp_blkBC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind=hdaddr_casesAc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS5loopMc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS5loopP".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition EMP : Z := 0xfa354.
Definition E_BB : Z := 0xfa46c.
Definition E_LP : Z := 0xfa4ec.
Definition E_LM : Z := 0xfa56c.
Definition E_NF : Z := 0xfa5ec.
Definition E_FOUND : Z := 0xfa940.
Definition E_STOPS : list Z := [E_BB; E_LP; E_LM; E_NF; E_FOUND].

Lemma srl3_val : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpS ()) [] "h01zh14__x1h27__arithh34__ffh48__varmaph55__with64__p1h76__sat0h86__sat1h91Hh:2Hah;2b1h<2b2h=1nh>2Hxh?1xp;1p;2p;3p;4p;6p;5p;7p;8p-1p10000p4p710p8p1000Gp4p710g000dR0p4p710p8g001@j16Tg001ej18Tg002Cj2GTg002`j23Tg003<R1j2@Tg003Wj1:Tg004:j3;Tg004Tj21Tg005>j3NTg005bj1LTg006@j2=Tg006fj1<Tg007Kj3jTg0083j2?Tg008Pj3aTg0095j25Tg009Uj2ATg00:;j29Tg00:[j2ETg00;5j2ZTg00;]j3YTg00<Aj1XTg00<aj1WTg00=Aj2VTg00=_j1UTg00>=j1TTg00>hj2>Tg00?Kj2PTg00?nj4CTg00@Yj6MTg00A=j1OTg00A_j2QTg00BAj2KTg00Bmj3RTg00CLj4STg00D>j1lTg00D\j4kTg00E=j3iTg00E`j3hTg00FCj2fTg00F`j5cTg00GLj4bTg00Ggj3JTg00HJj3`TP0j6_Tg00I3j1HTg00Inj2ITg00J]j3^Tg00KEj3]Tg00L6j2dTg00LRj7eTg00M6j7\Tg00MZj8[Tg00N>j6gTg00N\R0f0R2'dp=2g00O:R3f1R4;;2p=0P4g00OXR5g00P7R6P6g00PWR7P2g00Q7Fep=7f2R8P5P6P6P7P4P2F\p=Bf3R9P5P6P6P7P8P4P2G[p=DP3P4g00QWP2CCp=FP3f4R:P9P8P4P2Egp=4%22R;g00R>R<#6R=#8R>%6=#6R=#6#6#6R?#8R@'GRA,32RB'@RCg00RcRD%:2RE%:4RFP1%:8?;4211981194'0R1[11841182'0%:9?;84[RG%::?;98\1AN842P2n2001000000120000000W<W;W=PG^<F^;E^=DP2%L?R?g00SA1=?8RD%<<RE#8RF,=?RG3jR1%8=R=,?8RH,=?RI11?DRJ%<E#<#<#<#8,=?9a?GRG,1?RE'51?9=RK,=?,1?RL,02X031A?8RM152ERN/0LX031A?HRL1A?9/5E/02X03198ARO1A?K,0NX0319HA199A/5E/02X03P819KARP,0NX031E3F10FERNdPNP3PF15:21?:=RN/9ARQ'0X031G>F,?9102QX03PK10N2X031E3KPP%2K13KAP9P=1Z>@RP130>%2@130A[[RN%2>RQg00SmRRAY>@4UW:R@%2A\R^:QRQp-0RRg00TIRS#XRT%WSRS1V34RU%U3RV%T3RWP31>30RXg00U5RY1P3<R<CC,7WRZPWP5P6P6P7P9EMR55BW%O6R6PZCD1QW7R7P2P8g00U\R[g00V<R\'E1K28=;[\dAR304CSR\b3b4b5X13W61@;4%24R;[^13^6RP2f6R[/3AP[f5R]O3b2b7b8PTPS%l3R^PV1>3=R_,FX,7WP7P\b3b4b5130=P2b2R0CkP9P=PAP0PPPNP@PQPTPSPUPVPW1>3>=i3?R>,F<,7WR09BW5P6Ah3_>,F<,7WCDP7P\b3b4b5X13X6R1@4B1f=A,34[^13^6RP2%2[P[P]O3b2b7b8DcCb9JKAD4159FPTPSP^PVP3PXPY1>3FCC,7WP7P\b3b4b5%2FP2b29`9FD4PEP2E_b9POPPPNP@PQPTPSPUPVPWABWZ0R0P6P0CDP7P\b3b4b5X13134A,@;\C^13P2P]P:O2b2b7b89J8AD4PL%HHD4PM%H8D411?IRI1I?HD4PJ1I?8D4A^?DG,1?A]?DGD411?1/0IeO4b9W>X?3o"). Qed.

Definition syms_same (sr sr0 : list expr) (l : list reg) : bool :=
  forallb (fun r : reg => expr_eqb (sr_get sr r) (sr_get sr0 r)) l.
Lemma syms_same_sound : forall E sr0 sr R R' l,
  regs_ok E sr0 R -> regs_ok E sr R' -> syms_same sr sr0 l = true -> forall r, In r l -> getr R' r = getr R r.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpS ()) [] "h01Hh11bh21rh31Eh42H0h52H1h62Hkh72Hrh81Rh92R'h:1eh;1lh<2srh=3sr0p;1p;2p;3p;6g00<aj18Tg001@j11Tg006fj1>Tg005bj16Tg003Wj19Tg00V\j2@Tg00WHj37Tg00XGj3=Tg004:j32Tg00YGj3<Tg00Y^j20Tg00ZVj2;Tg00[Pj6:Tg00\Gj3ATg00]Jj23Tg00^Bj25Tg00:[j2?Tg00N>j64Tg00_4g00_kR0#8R1g00R>#1R2#>#6R3%12#1#1#1#1#6#9R2'@R4%93R3#8f5R5f4R6f2R737f6R8?767g00U\R9A=587g00V<R:32f0R;=<36P3f9R</0;f:R=/0;';X23R>P5f1R?P7P;E:P>P?O1=29:10<7R:10=7R7;A;A20:7P2f<R7f3R:,0=R9'315=6922;X12P2f;R=/0:R?,37R>f=R@10=6'3=22;X12P0P?13@;1076,3@522X:01?2>P9P;E415<:P8P:O1E4f8/5:P5P:O1E4b0b0W7X23W6W5W4W;X94W8X<1W=W3o"). Qed.
Ltac aonly_same HR HR' :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; refine (syms_same_sound _ _ _ _ _ non_argT HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true).

Lemma gz_subE : forall M a n b m, gz M a n -> a <= b -> b + m <= a + n -> gz M b m.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpS ()) [] "h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with74__x4h84__x5h91Hh:2H0h;3Habh<3Hbmh=2Hih>1Mh?1ah@1bhA1ihB1mhC1nhD1zp;3p;2p;1p;4p;6p;7p;8g00`cj3GTg00L6j21Tg00aZj20Tg002`j2=Tg003<j2@Tg00<Aj1WTg00<aj1UTg00=Aj27Tg00b7j48Tg00=_j1LTg00>=j1KTg00?Kj24Tg001@j1CTg00bUj3FTg006fj1DTg00?nj4:Tg00A_j2VTg00:[j2TTg00BAj2QTg004:j3?Tg00Bmj3PTg00CLj4OTg00c8j2<Tg00cUj2NTg00dMj19Tg00dlj25Tg00eUj36Tg00f>j2BTg00fjj3ATg00D>j1JTg00>hj2MTg00A=j1ITg000dj6HTg00gJj3RTg00LRj7STg00M6j7YTg00MZj8XTg00O:R0f1R1f0R23Rp=3P1g00OXR3g00P7R4P4g00PWR5P2g00Q7FSp=2P0P1g00U5P2C:p=;f2R6P3P4P4P5P1P2FYp=Ef3R7P3P4P4P5P6P1P2GXp=>g00gmf4R3?G7611361076f5R8/03'1g00N\R9/121=23'@g00TIR:#WR;%U:R<P01706P11707C8%L0R=%K0R>P0g00R>R?,40R@%C?RA,40RB=F0@%D?,40R?'3'3g00h^13B?C:'21V>5R5P2P6g00U\RCg00V<RD'T1Q26=?CDdAP091CORDb4b5b6X00X10X201<12/06,0210165?0^00^10^20P2P6f7RCf9REO3b3f8RFf6RG/<F/01'010G15?0P01<CE/06RH,0Ef;/N2XD0P8PHg00iERH#9RI#9RJ#9RK,50150J150HRH560560g00idRJ'B%9K,50150I=60H560/BJ=A:;5A:P<P0P01703P6%J0R<C8P1P01708P7P<C8C8P=P>1M09R=/;?,2>P0P?g00QWR<%DA,40R:C:,2>5E>%I4R4P>13@:%CA,40RA,3B';,2>P4P>1;B@,2>P4AF0@B/3?R?,;=,2>P0P?P<PAC:,2>5E>C>C>C>P5PDb4b5b6X00X10X20X70X8011961=63'@10181063'111761<73/08R1,191=1G'@[[[^00^10^20^70^80P2PCPEP7f:PFP6P3P8O8b3O210C6P2EHb:W=XA0AGC37eW<W;W9XB0X@0XC0X?0W>o"). Qed.

Lemma ck_align : forall M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 8 = 0 ->
  sc_denot ASEGS M E (SCBr false BC_NE (EAlu ALU_AND e (ELit 7)) (ELit 0)).
Proof.
  intros M E e a He Ha Hal. cbn [sc_denot]. cbn [edenot]. rewrite He.
  rewrite land7_val by lia. rewrite Hal. reflexivity.
Qed.

Lemma ck_null : forall M E e a, edenot E e = Z_to_bv 64 a -> 0 < a < 2 ^ 64 ->
  sc_denot ASEGS M E (SCBr false BC_EQ e (ELit 0)).
Proof.
  intros M E e a He Ha. cbn [sc_denot]. rewrite He. cbn [edenot]. rewrite br_eq by lia.
  destruct (Z.eqb_spec a 0); [lia | reflexivity].
Qed.

Lemma ck_wrap : forall M E e1 e2 a b, edenot E e2 = Z_to_bv 64 a -> edenot E e1 = Z_to_bv 64 b ->
  0 <= a <= b -> b < 2 ^ 64 ->
  sc_denot ASEGS M E (SCBr false BC_LTU e1 e2).
Proof.
  intros M E e1 e2 a b H2 H1 Hab Hb. cbn [sc_denot]. rewrite H1, H2. rewrite br_ltu by lia.
  destruct (Z.ltb_spec b a); [lia | reflexivity].
Qed.

Lemma ck_nullxor : forall M E e1 e2 a b, edenot E e2 = Z_to_bv 64 a -> edenot E e1 = Z_to_bv 64 b ->
  0 < a <= b -> b < 2 ^ 64 ->
  sc_denot ASEGS M E (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_SLTU (ELit 0) e2) (EAlu ALU_SLTU e1 (ELit 1))) (ELit 0)).
Proof.
  intros M E e1 e2 a b H2 H1 Hab Hb. cbn [sc_denot]. cbn [edenot]. rewrite H1, H2.
  rewrite !w_sltu by lia.
  replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite w_xor by lia. reflexivity.
Qed.

Lemma al8_16 : forall b, b mod 16 = 0 -> b mod 8 = 0.
Proof. intros b Hb. rewrite <- (Z.mod_mod_divide b 16 8 ltac:(exists 2; reflexivity)), Hb. reflexivity. Qed.
Lemma al8_k : forall b k, b mod 8 = 0 -> (8 * k + b) mod 8 = 0.
Proof. intros b k Hb. rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. exact Hb. Qed.
Lemma al8_k' : forall b k, b mod 8 = 0 -> (b + 8 * k) mod 8 = 0.
Proof. intros b k Hb. rewrite Z.mul_comm, Z.mod_add by lia. exact Hb. Qed.
Ltac al8 :=
  first [ assumption | apply al8_16; assumption | apply al8_k; al8 | apply al8_k'; al8
        | match goal with |- (?x + ?c) mod 8 = 0 => let k := eval compute in (c / 8) in
            replace (x + c) with (x + 8 * k) by lia; apply al8_k'; al8 end ].

Ltac sck_ev := evs; rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z by lia; first [reflexivity | f_equal; lia].
Ltac sck :=
  first [ eapply ck_align; [sck_ev | lia | al8]
        | eapply ck_nullxor; [sck_ev | sck_ev | lia | lia]
        | eapply ck_wrap; [sck_ev | sck_ev | lia | lia]
        | eapply ck_null; [sck_ev | lia] ].

Lemma in_split_entsS : forall (V : Type) (p : Z) (ents : list (Z * (Z * V))),
  In p (map fst ents) -> exists l1 k v l2, ents = l1 ++ (p, (k, v)) :: l2.
Proof.
  intros V p ents Hin. apply in_map_iff in Hin. destruct Hin as ([p' [k v]] & Hp & Hin). cbn in Hp. subst p'.
  apply in_split in Hin. destruct Hin as (l1 & l2 & He). exists l1, k, v, l2. exact He.
Qed.

Lemma hdaddr_casesS : forall (V : Type) (l2 : list (Z * (Z * V))),
  hdaddr l2 = 0 /\ l2 = [] \/ exists p k v l2', l2 = (p, (k, v)) :: l2' /\ hdaddr l2 = p.
Proof. intros V [|[p [k v]] l2']; [left; split; reflexivity | right]. exists p, k, v, l2'. split; reflexivity. Qed.

Lemma land_1S : forall k, Z.land k 1 = k mod 2.
Proof. intros k. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac In_nonarg := unfold non_argT; cbn [In]; repeat (first [left; reflexivity | right]).

Section EmpS.
  Context {fx : FPState}.
  Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface ASEGS L.
  Variable rom : word -> option byte.
  Variables (A : AS MI) (M : mem) (obj bl bc key : Z) (ents : list (Z * (Z * Z))).

  #[local] Abbreviation st R pc M := (@mkst fx R (Z_to_bv 64 pc) M rom).

  Definition SENV : Prop :=
    umapx MI 24 (nval24 ASEGS) A M obj bl bc ents /\ 0 <= key < 2 ^ 32
    /\ gz M obj 40 /\ (bc <> 0 -> gz M bl (8 * bc)) /\ (forall p k v, In (p, (k, v)) ents -> gz M p 24).

  Lemma senv_bc : SENV -> 0 <= bc <= 26339969.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpS ()) ["EmpS"] "h01Hh11Uh22_Hh31kh41ph51vp;1p;=p;2p;3p;4p;>g006fj10Tg001@j11Tg001ej13Tg00jPj1BTg00kHl=@Tg00L6j26Tg002Cj2<Tg002`j2;Tg003<R0j24Tg00`cj35Tg004:j39Tg00lAj1:Tg00FCj2ATg00lZj28Tg00m:j47Tg00YGj3?Tg00mZl>=Tg00nRj2>Tf0R1#1#1p=2g00oTP0p,2ACR0g010OR2p,1LR3p,2MIR4g00R>R5#0#2R6#1#3R7g00O:R8%B2R9p,1AR:p,1MR;p,3objR<p,2blR=p,2bcR>p,4entsR?M=@R@g00N\RAp,3keyRB'6%15R5#3%25RC#2#3'<,;B'4%05#1#2#395;<A98>A#:%3C/A>95;=[1888RC,88P8PCf2P8P8f1RCP1C7C7;??f3=5;7[^58^38^48'4'4'4R516A>%06#1#2#0#0#0#0#1#0#1#0#1#0#2#2#2#0#3,6>'4P1P0P2P3P4P7P8P9P:P;P<P=P>P?PCM>=,>>X25X1@PCP1O2n2001000000120000000W0o"). Qed.

  Definition efound (r : Z) : Prop := exists v, In (r, (key, v)) ents.

  Definition atE (R R' : bvmap 5 word) : Prop := aonlyT R R'.

  Definition srB : list expr :=
    srs sr_id [(8%bv, EVar 32); (19%bv, ELit SHBASE); (22%bv, EVar 33); (21%bv, EAlu ALU_SRL (EVar 32) (ELit 3));
               (20%bv, EVar 34); (24%bv, EVar 35); (11%bv, EVar 36)].
  Definition KNBx (scr : scripts) : list kentry := kn_fix 20 E_STOPS scr E_BB srB [] 50.
  Definition SCR_B_b0 := SCR [false; false; false; false; true] [EVar 40; EVar 41; EVar 42] [].
  Definition SCR_B_q0 := SCR [false; false; false; false; false; false; true] [EVar 40; EVar 41; EVar 42] [].
  Definition SCR_B_m := SCR [false; false; false; false; false; false; false; true] [EVar 40; EVar 41; EVar 42] [].
  Definition SCR_B_p := SCR [false; false; false; false; false; false; false; false] [EVar 40; EVar 41; EVar 42] [].

  Definition atLoopM (R R' : bvmap 5 word) (q : Z) : Prop :=
    aonlyT R R' /\ getr R' 10%bv = Z_to_bv 64 q /\ getr R' 12%bv = sxw key.
  Definition atLoopP (R R' : bvmap 5 word) (q : Z) : Prop :=
    aonlyT R R' /\ getr R' 10%bv = Z_to_bv 64 q /\ getr R' 12%bv = Z_to_bv 64 (bc - 1) /\ getr R' 13%bv = sxw key.

  Lemma emp_blkB : forall R (pw b q0 : Z), SENV ->
    getr R 8%bv = Z_to_bv 64 obj -> getr R 19%bv = Z_to_bv 64 SHBASE -> getr R 22%bv = Z_to_bv 64 key ->
    getr R 21%bv = Z_to_bv 64 (obj / 8) -> getr R 20%bv = Z_to_bv 64 bc -> getr R 24%bv = Z_to_bv 64 (hmod key bc) ->
    getr R 11%bv = Z_to_bv 64 pw -> 0 <= pw < 2 ^ 64 -> bc <> 0 ->
    cell8 ASEGS M (bl + 8 * hmod key bc) b -> 0 <= b -> b + 8 <= 2 ^ 47 -> (b <> 0 -> cell8 ASEGS M b q0) -> (b <> 0 -> gz M b 8) ->
    (b <> 0 -> b mod 8 = 0) ->
    exists R',
      ((b = 0 \/ q0 = 0) /\ msteps ASEGS (st R E_BB M) (st R' E_NF M) /\ aonlyT R R')
      \/ (b <> 0 /\ q0 <> 0 /\ 2 <= pw /\ msteps ASEGS (st R E_BB M) (st R' E_LM M) /\ atLoopM R R' q0)
      \/ (b <> 0 /\ q0 <> 0 /\ pw < 2 /\ msteps ASEGS (st R E_BB M) (st R' E_LP M) /\ atLoopP R R' q0).
  Proof.
    intros R pw b q0 SE H8 H19 H22 H21 H20 H24 H11 Hpw Hbc Hb Hb0 Hb1 Hq Hgb Hba.
    pose proof (senv_bc SE) as Hbcr.
    destruct SE as (U & Hkr & Hzo & Hzb & Hzn). specialize (Hzb Hbc).
    destruct (u_hdr U) as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef].
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_al U) as Hoa.
    pose proof (u_bl_lo U Hbc) as Hbl0. pose proof (u_bl_hi U) as Hbl1. pose proof (u_bl_al U) as Hbla.
    assert (Hh : 0 <= hmod key bc < bc) by (unfold hmod; apply Z.mod_pos_bound; lia).
    pose proof (proj1 Hb) as Hbr. pose proof (proj1 Hbl) as Hblr.
    set (h := hmod key bc) in *.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 h; Z_to_bv 64 pw;
                        Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 bl; Z_to_bv 64 b; Z_to_bv 64 q0]).
    assert (HR : regs_ok E srB R).
    { unfold srB. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | evs; first [assumption | rewrite srl3_val by lia; assumption]] |]).
      apply Forall_nil. }
    assert (Hrd_b : forall e, edenot E e = Z_to_bv 64 b ->
      sc_denot ASEGS M E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 35)) (EVar 40)) 0) 8 false e)).
    { intros e He. unfold cell8 in Hb. eapply (sc_read_cellw _ _ _ _ _ _ _ _ Hb); [cbn; lia| |exact He].
      evs. rewrite w_mul, w_add, v_addi_Z by lia. f_equal. lia. }
    assert (Hfl_b : sc_denot ASEGS M E (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 35)) (EVar 40)) 0) (ELit 8))).
    { eapply (sc_flat _ _ _ _ (8 * h + bl)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]. }
    destruct (Z.eq_dec b 0) as [Hbz|Hbnz].
    - assert (HK : know_ok ASEGS E M (KNBx SCR_B_b0)) by (kn_eval; know_tac).
      xrun HR HK 100%nat E_STOPS SCR_B_b0 50%N.
      { split_scs; first [ exact Hfl_b | apply Hrd_b; evs; reflexivity | sc_shdj | sc_fl | sc_br | sck
                         | match goal with H : cell8 _ _ _ _ |- _ => unfold cell8 in H; sc_rd H end ]. }
      exists R'. left. split; [left; exact Hbz|]. split; [exact Hms | aonly_same HR HR'].
    - specialize (Hq Hbnz). specialize (Hgb Hbnz). specialize (Hba Hbnz). pose proof (proj1 Hq) as Hqr.
      destruct (Z.eq_dec q0 0) as [Hqz|Hqnz].
      + assert (HK : know_ok ASEGS E M (KNBx SCR_B_q0)) by (kn_eval; know_tac).
        xrun HR HK 100%nat E_STOPS SCR_B_q0 50%N.
        { split_scs; first [ exact Hfl_b | apply Hrd_b; evs; reflexivity | sc_shdj | sc_fl | sc_br | sck
                           | match goal with H : cell8 _ _ _ _ |- _ => unfold cell8 in H; sc_rd H end ]. }
        exists R'. left. split; [right; exact Hqz|]. split; [exact Hms | aonly_same HR HR'].
      + destruct (Z.le_gt_cases 2 pw) as [Hw|Hw].
        * assert (HK : know_ok ASEGS E M (KNBx SCR_B_m)) by (kn_eval; know_tac).
          xrun HR HK 100%nat E_STOPS SCR_B_m 50%N.
          { split_scs; first [ exact Hfl_b | apply Hrd_b; evs; reflexivity | sc_shdj | sc_fl | sc_br | sck
                             | match goal with H : cell8 _ _ _ _ |- _ => unfold cell8 in H; sc_rd H end ]. }
          exists R'. right; left. split; [exact Hbnz|]. split; [exact Hqnz|]. split; [lia|]. split; [exact Hms|].
          unfold atLoopM. split; [aonly_same HR HR'|].
          rreg HR' 10%bv G10. rreg HR' 12%bv G12. split; [exact G10 | rewrite G12; apply sextw_val; lia].
        * assert (HK : know_ok ASEGS E M (KNBx SCR_B_p)) by (kn_eval; know_tac).
          xrun HR HK 100%nat E_STOPS SCR_B_p 50%N.
          { split_scs; first [ exact Hfl_b | apply Hrd_b; evs; reflexivity | sc_shdj | sc_fl | sc_br | sck
                             | match goal with H : cell8 _ _ _ _ |- _ => unfold cell8 in H; sc_rd H end ]. }
          exists R'. right; right. split; [exact Hbnz|]. split; [exact Hqnz|]. split; [lia|]. split; [exact Hms|].
          unfold atLoopP. split; [aonly_same HR HR'|].
          rreg HR' 10%bv G10. rreg HR' 12%bv G12. rreg HR' 13%bv G13.
          split; [exact G10|]. split; [rewrite G12; apply w_addm; lia | rewrite G13; apply sextw_val; lia].
  Qed.

  Definition srLM : list expr :=
    srs sr_id [(10%bv, EVar 32); (12%bv, EVar 33); (19%bv, ELit SHBASE); (22%bv, EVar 34); (20%bv, EVar 35); (24%bv, EVar 36)].
  Definition srLP : list expr :=
    srs sr_id [(10%bv, EVar 32); (12%bv, EVar 37); (13%bv, EVar 33); (19%bv, ELit SHBASE); (22%bv, EVar 34); (20%bv, EVar 35);
               (24%bv, EVar 36)].
  Definition KNL (pc : Z) (sr : list expr) (scr : scripts) : list kentry := kn_fix 20 E_STOPS scr pc sr [] 50.

  Lemma node_factsE : forall l1 p k v l2, SENV -> ents = l1 ++ (p, (k, v)) :: l2 ->
    0 < p /\ p + 24 <= 2 ^ 47 /\ cell8 ASEGS M (p + 8) k /\ cell4 ASEGS M (p + 16) k /\ 0 <= k < 2 ^ 32
    /\ cell8 ASEGS M p (hdaddr l2) /\ gz M p 24.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpS ()) ["EmpS"] "p'0h01Hh13Hchh24__x1h32Hah41ah51lh67__arithh74__ffh86__sat3h96__sat4h:6__sat5h;6__sat6h<8__varmaph=5__with>2l1h?1Ah@2_HhA3_H0hB3_H1hC1khD2l'hE1pi001phF1vhG2HehH2HhhI3HinhJ2HkhK3HkrhL3Hp0hM3Hp1hN2HzhO2IHhP1UhQ4entshR2kvhS2l2hT1qi011zp%0p&0p;2p;1p;=p;3p;4p;6p;Bp;5p;7p;>p;8g00lZS00j2_Tg00<aj1QTg006fj1KTg001@j18Tg001ej1CTg00jPk105j4lTg00kHl=|Tg002Cj2[Tg002`j2:Tg00`cj3ITg00lAj1dTg00FCk206Tg00YGj32Tg003<R0j20Tg004:j3=Tg02jDj3JTg01n]j2YTg02jaj4nTg00fjj3HTg00:[j2XTg01o7j3jTg025Fj3iTg00N>j6hTg02k@lBgTg02l8j5eTg02ljj43Tg00;5j2bTg00;]j3aTg00<Aj1`Tg00=Ak204Tg00=_k103Tg00>=k102Tg00>hj2TTg00?Kk201Tg00?nj4NTg00A=j1}Tg00A_j2{Tg00BAj2zTg00Bmj3yTg00CLj4xTg00gJj3wTg005bj1\Tg00E=j3ZTg00M6j7vTg02mal>rTg000dj6qTg023Fj3sTg028Aj3uTg02nZj6oTg00GLj4ETg00L6j2ATg00m:j4FTg016[j2]Tg02C<j4PTg00aZj2BTg018Lj4^Tg00:;j2mTg00LRj7~Tg00MZk800Tg02o<j4kTg00N\R1f1R2'Af0R3'0p=Gg00O:R4?=31p=fP4f3R5f2R6P4P4P2P3CFCFp=Uf7R7f6R8f5R9P4f4R:P5P4P4P6P2CFCF;H33Jp=6g010OR;P9P:1]45CPAI623'0p=9P;P71B89P:C^1A151:62'0/03'0p=1P;P:1B56P2CP/03p=51:1:1B56/A2/03'0p=7AH6239J:5p=pP4P4P2P3CFp=R1:13p=?1m23==41p=>P;P51B62P3CPp=;P;P7P8P9ClP:P5P6P2C3/03'0p=41023,06p=@1B56/A2/03p=W1B62/A3p=MP;P51B62P3C^p=V1A151:62'0/03p=cP;P6P21]43CPp=D1A13p=LP2g00OXR<g00P7R=P=g00PWR>P3g00Q7F~p=OP5P<P=P=P>P6P2P3L00p=SP;P4P2P3Ckp=<P4P5P6P2CF=H:3p=t1_44R?,_4R@#QRAg00oTP0p,2ACRBP;p,1LRCp,2MIRDg00R>RE#K#8#8#8#CRFP4&05;RGp,1ARHp,1MRIp,3objRJp,2blRKp,2bcRLp,4entsRMM=|RNp,3keyRO%8ERP#CRQ%8P#8RR#8RS#8RT#CRU'[RV,:O'GRO%KPRP#8#8#8#CRW9IIJRX%fL#dRY%CRRR006LRZ9IIK[R[P?P6P2P3CU=2@MAII5F[^F4^C4^E4R\'0R]'0R^'0R_P@P8P@P?P9P:P5P6G69=AMP8P8PF%KP#K#KRP#CR`,[QRaPIP8PRP9PIP8%CSRSP9P9P9PVPIP8P5PIP8PFE9G1D5D7[P3P0POP^P@f:RbP@P?f9Rcf8P7P8G69=AMPbPbPFPaPIPbPRPcPIPbPSPcPcPcPVPIPbP7PIPbPFE9G1D5D7[P3P0PXP]P@f>R7P@P?f=Rdf<f;RePbG69=AMP7P7PFPaPIP7PRPdPIP7PSPdPdPdPVPIP7PePIP7PFE9G1D5D7[P3P0P[P\P@fBReP@P?fARdf@f?RbP7G69=AMPePePFPaPIPePRPdPIPePSPdPdPdPVPIPePbPIPePFE9G1D5D7[P3P@fER7P@P?fDRffCRgPePdG69=AMPAP@fFRdP@P?P7PfPgCURhPeDpP?PdP7PfCURe=2@3XQAg000Gp4p710Ri%Q3Rj%Q2RkP0AJ5629253A2:25A2:26'YRl[A2536A2532'YAJ:5692:2[RmAJ9:59296\lP5P6P2P3CnP3n2001000000120000000X46WDW5W?Pm^46^Dk^5j^?iP3P@fGRiAH@egRjPeA2@eiA2@ejA=@eeA2@eg1X@e3j3iO5b0PMP3EhA2@hMPBP;PCPDPFP4PGPHPIPJPKPLPMPbPdP7PfP3MBg1RdFPBP;PCPDPHDeRb52?%?dPdPFPa1>dSPIPdPRP7C;PIPdPSP7P7P7PVPIPdPfPdPFPJPWPiPFPKPZC3\YG4G13@CW3@P01RiF=2?bPiPiPFPa1>iSPIPiPRPdC;PIPiPSPdPdPdPVPIPiP7PiPFPJPWfHRfPFPKPZC3\YG4G13@D7PfPfPFPaPIPfPRPiPIPfPSPiPiPiPVPIPfP7PIPfPFE9G1D5D7P3fIR7/RF=2?bfJRbPbPFPa1>bSPIPbPRP7C;PIPbPSP7P7P7PVPIPbPfPbPFPJPWfKRfPFPKPZC3\YG4G13@D7P0%?fPfPFPa1>fSPIPfPRPbC;PIPfPSPbPbPbPVPIPfP7PfPFPJPWfLRiPFPKPZC3\YG4G13@CWPiPiPFPaPIPiPRPfPIPiPSPfPfPfPVPIPiP7PIPiPFE9G1D5D7P3fMR7#?fNRfPFPa1>fSPIPfPRP7C;PIPfPSP7P7P7PVPIPfPiPfPFPJPWfORiPFPKPZC3\YG4G13@CWP0AMiFa1>iSPIPiPRPfC;PIPiPSPfPfPfPVPIPiP7PiPFPJPWfPRhPFPKPZC3\YG4G13@PhPhPFPaPIPhPRPiPIPhPSPiPiPiPVPIPhP7PIPhPFE9G1D5D7P3fQRe?MFafRRg/>SPIPgPRPeC;PIPgPSPePePePVPIPgPhPgPFPJPWfSRhPFPKPZC3\YG4G13@P01>hSPIPhPRPgPIPhPSPgPgPgPVPIPhPePhPFPJPWfTRgPFPKPZC3\YG4G1D5PgPgPFPaPIPgPRPhPIPgPSPhPhPhPVPIPgPePIPgPFE9G1D5D7P3fURe/>SPIfVRhPRPePIPhPSPePePePVPIPhPgPhPFPJPWfWRgPFPKPZC3\YG4G1D5P0PIPgPRPhC;PIPgPSPhPhPhPVPIPgPePgPFPJPWfXRhPFPKPZC3\YG4G1PhPhPFPaPIPhPRPgPIPhPSPgPgPgPVPIPhPePIPhPFE9G1D5D7P3PIfYRePRPhC;PIfZRgPSPePePePVPIPgPhPgPFPJPWf[RhPFPKPZC3\YG4G1P0PIPhPSPgCVPgPgPVPIPhPePhPFPJPWf\RgPFPKPZC3\YG4CcPgPgPFPaPIPgPRPhPIPgPSPhPhPhPVPIPgPePIPgPFE9G1D5D7P3PIf]RePSPgCVPePePVPIf^RhPgPhPFPJPWf_RjPFPKPZC3\YG4CcP01:hV,GhPIPjPePjPFPJPWf`RhPFPKPZC3\YG4PhPhPFPaPIPhPRPjPIPhPSPjPjPjPVPIPhPePIPhPFE9G1D5D7P31:hV,GhPIfbRePhPePFPJPWfcRWPFPKPZC3\YG4%?WAMWFaRYPIPWPRPeC;RRPIPWPSPeCVRS1:eV,GeRZADIWhS01AIIWFRj'0R0'0Rk'0Rm'0Rl'01bQURn%?QRo%LU%?V[[Rp%LQRqg00SmRrAaQU2UW3RU%LV\r^3qRs1bQ`Rt%L`%?a[\oRoAaQ`2VrX3qR`%La\r^3qRqg00TIRr#`Ru%QrRr20442Rv&034Rw&024RxP41T41Ryg00QWRz2014ERECN,OxR{%}=R|P{CS1{x>R{P3P6g00U\R}g00V<R~'X1z36==}~dAy412CxR1b7b<b=X24%?3%?2[^24P3fhR~PbO2b6b8b9b:b;PYPlPtPoP`PqPnPpPUPsPuPrPvPwPxP41T4F9w4Eg00U5Rl1T4QRQ%\P5Z4CN,OxRPP|PPCSP{P1b7b<b=X24AM3FaAM2Fa[^24P3P~PdO2b6b8b9b:b;PRPmPcPSPkP9PZP0PnPpPUPsPtPoP`PqPuPrPvPwPxPxP<P=P=P>P4PyPlPECN,OxP4PEPz%\T9Z4QCN,OxFvRxP|PxCSP{P1b7b<b=X241:3V,G31:2V,G2[^24P3fgRVP8O2b6b8b9b:b;Q01PjPAPM1<I3X5APBP;PCPDPFP4PGPHPIPJPKPLPMPgM>rP@fdRgP@P?PWPefaRMPhG6RhPfEq1<IhP@P@P3P@P?feRhPgPWPeG6,<IffRf=DIW]1X>AP@%`@P@P?PgPWPePMG6,<IADIhe1<Ie;s3W1Q00P4P?P@P3P@P?PVPfPhPgG6,<IADI~h]1P@AH@62P@P?P~PVPfPhG6,<IfiRg=DIf]1[^5AP3P@P3P@P?fjRfPgP~PVG6,<IfkRV=DI~]1P@P@P?P5P6P2DtP@P?PVPfPgP~G6,<IP2P@P6P@P?flPVPfPgG6Rg9DI:1<Ig;u3O1W1WOX>AXR?XT4P2P3O2n2001100000120101100X4@PhP3Eob1PiPWPePMP7O4CECECECECECEWBWKP2P3O2n2001000000121000000W0WJP2P3O2n2001000000121000000W0WHP2P3O2n2001000000121000000W0WAP2P3O2n2001000000121000000W0WMP2P3O2n2001000000121000000W0WLP2P3O2n2001000000121000000W0W@P2P3O2n2001000000121000000b4bIWGXN\XB[P2P3O2n2001000000121000000X0]XAXP2P3O2n2001000000121000000X0^X@OP2P3O2n2001000000121000000X0_XPNP2P3O2n2001000000121000000W0XSAXF4XC4XE4W>o"). Qed.

  Definition loop_res (R : bvmap 5 word) (pc : Z) : Prop :=
    exists R', (exists r, efound r /\ msteps ASEGS (st R pc M) (st R' E_FOUND M) /\ aonlyT R R' /\ getr R' 10%bv = Z_to_bv 64 r)
               \/ (msteps ASEGS (st R pc M) (st R' E_NF M) /\ aonlyT R R').

  Lemma loop_res_cons : forall R R1 pc pc1, msteps ASEGS (st R pc M) (st R1 pc1 M) -> aonlyT R R1 -> loop_res R1 pc1 -> loop_res R pc.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmpS ()) ["EmpS"] "p'0h01rh11Hh22R'h33Ha2h44Hms2h51Gh62Hah72Hfh83Hmsh91Rh:2R1h;2pch<3pc1i001xp;1p;2p;5p;3p;6p;4g001@j1<Tg006fj1QTg005bj1GTg003Wj1MTg00V\j2PTg006@j21Tg013aj50Tg01mbj22Tg0303j2;Tg0312j1BTg001ej1KTg01B`j3JTg01n]R0j2CTg003<R1j27Tg00^Bj2@Tg031oj6ITg032gj5HTg00GLj4>Tg01oQj4DTg01o7j3OTg025Fj3NTg02D3j3?Tg004:j3FTg014SR2j2LTg010OR3f5R4f4R5f3R6f2R7f1R8D0f0R93?p=81@78=F69p=31278/79p=51789,77p=4g00O:R:/L9p=:A?378/79p=6P4P51167P8P9D0p=9A?389p=AP5P6P7P8P9D09?34p==AF789,76p=Eg00R>#<R;#QR<#GR=%<;#<#<#<#<#GR;#MR>'PR?p,2fxR@P611;8RAp,1MRBp,3romRCP@P711;9RDPBPCD0E812561;57P2P?%B9REP@f7RF11;4RGPBPCP@P8g033h,1;RHPBPCD0RIE8P>P8%<<#Kg02S95J=R=PDC3R<95F834X0:#:P@f6RJ11;5RKPBPCD0P@P9g02\f,1;RLPBPCD0RM12J936'CX2?1;F4P9P@f9RNP;PFPBPCE9RO/AI12N8RP/7<54EX0:#:P@f8RQP;PJPBPCE912Q976M'CP0P@f:R011;QRRPBPCD0RSP@P7PHPBPCE=1207RTP>1@7=PDCE54EX0:#:P@P8PLPBPCD0=6OPf;RP/;NP9P@PP11;NROPBPCD0RUP@P6PHPBPCE=12P6RVP>1@6=PDCE54EX0:#:P2P:P@f<R211;0PBPCP@P5PHPBPCD0E8P>P5P=PDC3952554EX0:f=R5/;PRWP9P@f>RX11;2RYPBPCP@PJPHPBPCD0E812XJRZP>1@J=PDCE54EP1%B8P@f?RJ11;5R[PBPCD0R\P@PFPHPBPCD0P>PFP=PAC395JF36fARA/;JP9%B6P@fBR]P;f@R^PBPCE9R_P@P0PHPBPCD0P>P0P=PKC395]036P1P@fCR011;APBPCP@PPPHPBPCD0E8P>PPP=PGC3950PfERG/;0P9P@PG11;0PBPCP@P5PHPBPCD0E8fFP>PXP=PRC375XP1fGRR/2JP>PJP=POC3fIRO/;RP912OAP>P]P=PYC3P?P@fNRYfLRG,1;PBPCPIE8A5Y8<54EX0:#:P@fMRYP;fKRKPBPCE9R`12Y976M'CX2?P0P`P@fDR`PHPBPCE=P>P`P=PDC395Y`54EX0:R`#:P@PGP;fJPBPCE9RYP@P0PLPBPCD012G0Ra36P:P`P5%B5P@P0PHPBPCD0R`,AYRbP>P0P=P[C3R[,7aRc'7PNPbPcP3PYP@PKP;POPBPCE9P`fHP4EIPaP[PGPKP0PRP8DHP9C>C>C>CD3OCDW5W3P8P9O2n2001000000121000000W1W4P8P9O2n2001000000121000000W1W7P8P9O2n2001000000121000000W1X0:P8P9O2n2001000000121100000W1P9O1P@P7PLPBPCD0=6STP1PUP@P6PLPBPCE=PVPWP9P@P511;PPBPCP@P4PLPBPCD0E8P?1A_IA5]8<54EX0:#:P@PAP;PJPBPCE9R]12A976M'CX2?PFP]P@PQPHPBPCE=P>PQP=PDC395AQ54EX0:#:P@P^P;PXPBPCE9RXP@PFPLPBPCD0RC'ARB12^FRL'7PBPLP3PXP\PCP2P8EIP^PJPFPPP9DHC>3NCDX3ZW4P8P9O2n2001000000121000000W1P9O1n200100000021100011000W1X2?P8P9O2n2001000000121100000W1W6W8X<:X;:X:?W9o"). Qed.

  Ltac runL R vals sr scr pc :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    try unfold loop_res;
    pose (E := Eseed R vals);
    assert (HR : regs_ok E sr R) by
      (apply regs_ok_srs; [apply regs_ok_seed|];
       repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | evs; first [assumption | match goal with H : getr R 19%bv = _ |- _ => rewrite H; reflexivity end]] |]); apply Forall_nil);
    assert (HK : know_ok ASEGS E M (KNL pc sr scr)) by (kn_eval; know_tac);
    xrun HR HK 100%nat E_STOPS scr 50%N;
    [ split_scs; try sc_auto1; try sc_shdj; try sck;
      try (match goal with Hk : cell4 _ _ _ _ |- _ => unfold cell4 in Hk; sc_rd_sx Hk end);
      try (cbn [sc_denot]; evs; rewrite ?w_remu by lia; rewrite ?br_ne, ?br_eq, ?br_ltu, ?br_geu, ?br_ne_sxw by lia; bool_lia)
    | ].

  Ltac finL_nf :=
    match goal with HR : regs_ok _ _ ?R, HR' : regs_ok ?E' _ ?R', Hms : msteps _ _ (mkst _ _ _ _) |- _ =>
    let AO := fresh "AO" in assert (AO : aonlyT R R') by (aonly_same HR HR');
    exists R'; right; exact (conj Hms AO)
    end.

  Lemma loopM : forall l2 l1 p k v R, SENV ->
    ents = l1 ++ (p, (k, v)) :: l2 -> bc <> 0 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 12%bv = sxw key -> getr R 19%bv = Z_to_bv 64 SHBASE ->
    getr R 22%bv = Z_to_bv 64 key -> getr R 20%bv = Z_to_bv 64 bc -> getr R 24%bv = Z_to_bv 64 (hmod key bc) ->
    loop_res R E_LM.
  Proof.
    intros l2. induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R SE He Hbc H10 H12 H19 H22 H20 H24;
      pose proof (senv_bc SE) as Hbcr; pose proof SE as SE0; destruct SE0 as (U & Hkr0 & _);
      destruct (node_factsE l1 p k v _ SE He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx & Hgz); cbn [hdaddr] in Hnx;
      assert (Hpa : p mod 8 = 0) by (destruct (u_node U p k v) as (_ & _ & _ & Hm & _);
                                      [rewrite He; apply in_app_iff; right; left; reflexivity | apply al8_16; exact Hm]);
      pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      unfold hmod in *.
    - destruct (Z.eq_dec k key) as [->|Hne].
      + runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                Z_to_bv 64 0; Z_to_bv 64 key; sxw key] srLM (SCR [false; false; false] [EVar 40; EVar 41] []) E_LM.
        exists R'. left. exists p. split; [exists v; rewrite He; apply in_app_iff; right; left; reflexivity|].
        split; [exact Hms|]. split; [aonly_same HR HR'|]. rreg HR' 10%bv G. exact G.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                     Z_to_bv 64 0; Z_to_bv 64 k; Z_to_bv 64 0] srLM (SCR [false; true; true; false; false] [EVar 40; EVar 41] []) E_LM.
             finL_nf.
          -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                     Z_to_bv 64 0; Z_to_bv 64 k; Z_to_bv 64 0] srLM (SCR [false; true; false; false; false] [EVar 40; EVar 41] []) E_LM.
             finL_nf.
        * destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                     Z_to_bv 64 0; Z_to_bv 64 k] srLM (SCR [false; true; true; true] [EVar 40] []) E_LM.
             finL_nf.
          -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                     Z_to_bv 64 0; Z_to_bv 64 k] srLM (SCR [false; true; false; true] [EVar 40] []) E_LM.
             finL_nf.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_factsE _ p' k' v' _ SE He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                Z_to_bv 64 0; Z_to_bv 64 key; sxw key] srLM (SCR [false; false; false] [EVar 40; EVar 41] []) E_LM.
        exists R'. left. exists p. split; [exists v; rewrite He; apply in_app_iff; right; left; reflexivity|].
        split; [exact Hms|]. split; [aonly_same HR HR'|]. rreg HR' 10%bv G. exact G.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * assert (STEP : exists R1, msteps ASEGS (st R E_LM M) (st R1 E_LM M) /\ aonlyT R R1
                         /\ getr R1 10%bv = Z_to_bv 64 p' /\ getr R1 12%bv = sxw key).
          { destruct (Z.ltb_spec k bc).
            -- rewrite (Z.mod_small k bc) in Hc by lia.
               runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                       Z_to_bv 64 0; Z_to_bv 64 k; Z_to_bv 64 p'] srLM (SCR [false; true; true; false; true] [EVar 40; EVar 41] []) E_LM.
               exists R'. split; [exact Hms|]. split; [aonly_same HR HR'|].
               rreg HR' 10%bv G10. rreg HR' 12%bv G12. split; [exact G10 | exact G12].
            -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                       Z_to_bv 64 0; Z_to_bv 64 k; Z_to_bv 64 p'] srLM (SCR [false; true; false; false; true] [EVar 40; EVar 41] []) E_LM.
               exists R'. split; [exact Hms|]. split; [aonly_same HR HR'|].
               rreg HR' 10%bv G10. rreg HR' 12%bv G12. split; [exact G10 | exact G12]. }
          destruct STEP as (R1 & Hms1 & AO1 & G10 & G12).
          apply (loop_res_cons R R1 E_LM E_LM Hms1 AO1).
          apply (IH (l1 ++ [(p, (k, v))]) p' k' v' R1 SE He' Hbc G10 G12).
          all: rewrite AO1; [assumption | In_nonarg].
        * destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                     Z_to_bv 64 0; Z_to_bv 64 k] srLM (SCR [false; true; true; true] [EVar 40] []) E_LM.
             finL_nf.
          -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                     Z_to_bv 64 0; Z_to_bv 64 k] srLM (SCR [false; true; false; true] [EVar 40] []) E_LM.
             finL_nf.
  Qed.

  Ltac sc_land2 :=
    cbn [sc_denot]; evs; rewrite w_and by lia;
    match goal with |- context [Z.land ?k (?b - 1)] => replace (b - 1) with 1 by lia end;
    rewrite land_1S; rewrite ?br_ne by lia; bool_lia.

  Lemma loopP : forall l2 l1 p k v R, SENV ->
    ents = l1 ++ (p, (k, v)) :: l2 -> bc = 2 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 (bc - 1) -> getr R 13%bv = sxw key ->
    getr R 19%bv = Z_to_bv 64 SHBASE -> getr R 22%bv = Z_to_bv 64 key -> getr R 20%bv = Z_to_bv 64 bc ->
    getr R 24%bv = Z_to_bv 64 (hmod key bc) ->
    loop_res R E_LP.
  Proof.
    intros l2. induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R SE He Hbc2 H10 H12 H13 H19 H22 H20 H24;
      pose proof (senv_bc SE) as Hbcr; pose proof SE as SE0; destruct SE0 as (U & Hkr0 & _);
      destruct (node_factsE l1 p k v _ SE He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx & Hgz); cbn [hdaddr] in Hnx;
      assert (Hpa : p mod 8 = 0) by (destruct (u_node U p k v) as (_ & _ & _ & Hm & _);
                                      [rewrite He; apply in_app_iff; right; left; reflexivity | apply al8_16; exact Hm]);
      pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k 2 ltac:(lia)) as Hmk';
      unfold hmod in *.
    - destruct (Z.eq_dec k key) as [->|Hne].
      + runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 (bc - 1); Z_to_bv 64 0;
                Z_to_bv 64 0; Z_to_bv 64 key; sxw key] srLP (SCR [false; false; false] [EVar 40; EVar 41] []) E_LP.
        exists R'. left. exists p. split; [exists v; rewrite He; apply in_app_iff; right; left; reflexivity|].
        split; [exact Hms|]. split; [aonly_same HR HR'|]. rreg HR' 10%bv G. exact G.
      + destruct (Z.eq_dec (k mod 2) (key mod bc)) as [Hc|Hc].
        * runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 (bc - 1); Z_to_bv 64 0;
                  Z_to_bv 64 0; Z_to_bv 64 k; Z_to_bv 64 0] srLP (SCR [false; true; false; false] [EVar 40; EVar 41] []) E_LP.
          all: try sc_land2.
          finL_nf.
        * runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 (bc - 1); Z_to_bv 64 0;
                  Z_to_bv 64 0; Z_to_bv 64 k] srLP (SCR [false; true; true] [EVar 40] []) E_LP.
          all: try sc_land2.
          finL_nf.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_factsE _ p' k' v' _ SE He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 (bc - 1); Z_to_bv 64 0;
                Z_to_bv 64 0; Z_to_bv 64 key; sxw key] srLP (SCR [false; false; false] [EVar 40; EVar 41] []) E_LP.
        exists R'. left. exists p. split; [exists v; rewrite He; apply in_app_iff; right; left; reflexivity|].
        split; [exact Hms|]. split; [aonly_same HR HR'|]. rreg HR' 10%bv G. exact G.
      + destruct (Z.eq_dec (k mod 2) (key mod bc)) as [Hc|Hc].
        * assert (STEP : exists R1, msteps ASEGS (st R E_LP M) (st R1 E_LP M) /\ aonlyT R R1
                         /\ getr R1 10%bv = Z_to_bv 64 p' /\ getr R1 12%bv = Z_to_bv 64 (bc - 1) /\ getr R1 13%bv = sxw key).
          { runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 (bc - 1); Z_to_bv 64 0;
                    Z_to_bv 64 0; Z_to_bv 64 k; Z_to_bv 64 p'] srLP (SCR [false; true; false; true] [EVar 40; EVar 41] []) E_LP.
            all: try sc_land2.
            exists R'. split; [exact Hms|]. split; [aonly_same HR HR'|].
            rreg HR' 10%bv G10. rreg HR' 12%bv G12. rreg HR' 13%bv G13. split; [exact G10|]. split; [exact G12 | exact G13]. }
          destruct STEP as (R1 & Hms1 & AO1 & G10 & G12 & G13).
          apply (loop_res_cons R R1 E_LP E_LP Hms1 AO1).
          apply (IH (l1 ++ [(p, (k, v))]) p' k' v' R1 SE He' Hbc2 G10 G12 G13).
          all: rewrite AO1; [assumption | In_nonarg].
        * runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); Z_to_bv 64 (bc - 1); Z_to_bv 64 0;
                  Z_to_bv 64 0; Z_to_bv 64 k] srLP (SCR [false; true; true] [EVar 40] []) E_LP.
          all: try sc_land2.
          finL_nf.
  Qed.

  Lemma emp_from_bb : forall R (pw : Z), SENV -> bc <> 0 ->
    getr R 8%bv = Z_to_bv 64 obj -> getr R 19%bv = Z_to_bv 64 SHBASE -> getr R 22%bv = Z_to_bv 64 key ->
    getr R 21%bv = Z_to_bv 64 (obj / 8) -> getr R 20%bv = Z_to_bv 64 bc -> getr R 24%bv = Z_to_bv 64 (hmod key bc) ->
    getr R 11%bv = Z_to_bv 64 pw -> 0 <= pw < 2 ^ 64 -> (bc <> 2 -> 2 <= pw) -> (bc = 2 -> pw < 2) ->
    loop_res R E_BB.
  Proof.
    intros R pw SE Hbc H8 H19 H22 H21 H20 H24 H11 Hpw Hn2 H2.
    pose proof (senv_bc SE) as Hbcr. pose proof SE as SE0. destruct SE0 as (U & Hkr & Hzo & Hzb & Hzn).
    assert (Hh : 0 <= hmod key bc < bc) by (unfold hmod; apply Z.mod_pos_bound; lia).
    destruct (u_bkt U (hmod key bc) Hh) as (b & Hb & Hbok).
    destruct (u_hdr U) as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef].
    pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_al U) as Hoa. pose proof (u_obj_lo U) as Ho0.
    assert (KEY : forall q0, (b <> 0 -> cell8 ASEGS M b q0) -> (q0 = 0 \/ exists l1 k v l2, ents = l1 ++ (q0, (k, v)) :: l2) ->
                  0 <= b -> b + 8 <= 2 ^ 47 -> (b <> 0 -> gz M b 8) -> (b <> 0 -> b mod 8 = 0) -> loop_res R E_BB).
    { intros q0 Hq Hq0 Hb0 Hb1 Hgb Hba.
      destruct (emp_blkB R pw b q0 SE H8 H19 H22 H21 H20 H24 H11 Hpw Hbc Hb Hb0 Hb1 Hq Hgb Hba) as
        (R' & [(Hz & Hms & AO) | [(Hbnz & Hqnz & Hpw2 & Hms & AO & G10 & G12) | (Hbnz & Hqnz & Hpw2 & Hms & AO & G10 & G12 & G13)]]).
      - exists R'. right. exact (conj Hms AO).
      - destruct Hq0 as [Hq0|(l1 & k & v & l2 & He)]; [contradiction|].
        apply (loop_res_cons R R' E_BB E_LM Hms AO).
        apply (loopM l2 l1 q0 k v R' SE He Hbc G10 G12).
        all: rewrite AO; [assumption | In_nonarg].
      - destruct Hq0 as [Hq0|(l1 & k & v & l2 & He)]; [contradiction|].
        destruct (Z.eq_dec bc 2) as [E2|N2]; [|specialize (Hn2 N2); lia].
        apply (loop_res_cons R R' E_BB E_LP Hms AO).
        apply (loopP l2 l1 q0 k v R' SE He E2 G10 G12 G13).
        all: rewrite AO; [assumption | In_nonarg]. }
    destruct Hbok as [Hb0 | [Hin | (Hbo & Hne & Hi)]].
    - subst b. apply (KEY 0); [intros X; lia | left; reflexivity | lia | lia | intros X; lia | intros X; lia].
    - destruct (in_split_entsS _ b ents Hin) as (l1 & k & v & l2 & He).
      destruct (node_factsE l1 b k v l2 SE He) as (Hp0 & Hp1 & _ & _ & _ & Hnx & Hgz).
      destruct (u_node U b k v) as (_ & _ & _ & Hm & _); [rewrite He; apply in_app_iff; right; left; reflexivity|].
      apply (KEY (hdaddr l2)); [intros _; exact Hnx | | lia | lia | intros _; eapply gz_subE; [exact Hgz | lia | lia]
                                | intros _; apply al8_16; exact Hm].
      destruct (hdaddr_casesS _ l2) as [(Hz & _) | (p' & k' & v' & l2' & Hl2 & Hh2)]; [left; exact Hz|].
      right. exists (l1 ++ [(b, (k, v))]), k', v', l2'. rewrite Hh2, He, Hl2, <- app_assoc. reflexivity.
    - subst b. apply (KEY (hdaddr ents)); [intros _; exact Hp1c | | lia | lia | intros _; eapply gz_subE; [exact Hzo | lia | lia]
                                         | intros _; al8].
      destruct (hdaddr_casesS _ ents) as [(Hz & _) | (p' & k' & v' & l2' & Hl2 & Hh2)]; [left; exact Hz|].
      right. exists [], k', v', l2'. rewrite Hh2, Hl2. reflexivity.
  Qed.
End EmpS.
