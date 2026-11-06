(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ArgvEnv RefLayout SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Cls Require Import ClsTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymExecA SymExecASound Overlay S1BootDefs S1Boot S1StartInit_defs S1StartInit_eqs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1StartInit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Peano2ltK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08c59OSSVerify5KrLib3Drv;S1StartInit8all_regsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib8SymExec33SX24ridxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib=SymExec3Sound4SX2S:ridx_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26edenotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit<nth_all_regsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib=SymExec3Sound4SX2S>ridx_roundtripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26sr_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX23env00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega5Tauto4kind02K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib3Drv;S1StartInit:range_missC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7forallbC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes?andb_true_introC46Stdlib5Lists4List2InC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1C47Corelib4Init9Datatypes3orbI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool<orb_true_iffC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyc59OSSVerify5KrLib3Drv;S1StartInit:cells_missC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula05C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismK46Stdlib9micromega5Tauto8GFormula06C47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes9MorphismsDiff_impl_subrelationI47Corelib4Init5Logic4True00C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveC49OSSVerify5KrLib9StreamSim7wseg_okC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemscSrc_spirv_tools_spvtools_binary_parser_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib=SymExec3Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7StoreOk=store_ok_wsegC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC49OSSVerify5KrLib7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC46Stdlib9micromega;ZifyClasses6mkapp2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib3Drv;S1StartInit:wseg_ed000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_ee000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_ef000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_f0000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_f1000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_f2000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_f3000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_f4000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_f5000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_f6000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_f7000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_f8000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_f9000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_fa000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_fb000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_fc000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_fd000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_fe000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit:wseg_ff000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit;wseg_100000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit;wseg_101000C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesI47Corelib5Lists7ListDef6Forall00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib3Drv:S1BootDefs6envp_wC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1BootDefs6auxv_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1BootDefs4pn_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1BootDefs:progname_wC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC49OSSVerify5KrLib<RefMemcpyLib3LWvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1BootDefs6canaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv6S1Boot2D8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphc59OSSVerify5KrLib3Drv;S1StartInit8D8_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit6len_avC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit2E8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX22evC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01c59OSSVerify5KrLib3Drv;S1StartInit6alu_spC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7Overlay3runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Cls6ClsTac3bwdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8MemSplit3wfJC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib3Drv:S1BootDefs6argc_wC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs3spxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit7spx_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit@regs_ok_by_indexC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv6S1Boot2J8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8MemSplit4cmemC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1BootDefs5J_lsmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1BootDefs5J_auxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Drv:S1BootDefs8aux_baseC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7ZStores5zerosC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1BootDefs5rnd_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1BootDefs6argv_wC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8MemSplit:wfJ_wbytesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C49OSSVerify5KrLib7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8MemSplit6win_loC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8MemSplitAstore_ok_cmem_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26a_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S5elenZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S6estartC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00K47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib7SeqExec?rdn_wbytes_hit8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8MemSplit<rdn_cmem_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26adenotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7ArgvEnv5argcNC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit8rw_wviewC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_lC49OSSVerify5KrLib8MemSplit<cmem_at_dataC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1BootDefs6D_libcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8MemSplit=rdn_cmem_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1BootDefs8rd_guardC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib=SymExec3Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib8SymExec33SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint02K47Corelib4Init7Decimal4uint04K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintK59OSSVerify5KrLib8SymExec33SX27scripts01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX29sym_state01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3Drv8SymExecA3SXA9sym_execAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9scs_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Drv7Overlay8abs_runsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7Overlay:apply_runsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Cls6ClsTac@rdn_wbytes_out_ZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit=range_miss_ptC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit7D8_noneC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib3Drv=SymExecASound4SXAS:runA_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7Overlay;split_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1StartInit6sr_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs9init_runsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs3sr8C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC49OSSVerify5KrLib7CatExecBstack_max_size_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib3Drv@S1StartInit_defs8CXX_INITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs3kn8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs8init_scsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs8init_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs3SLOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs3SHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs4DLIMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs=init_split_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs7init_srC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib3Drv:S1BootDefs3RPHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?S1StartInit_eqs>init_run_shapeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs8init_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs4MAINC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26sentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint01C59OSSVerify5KrLib3Drv?S1StartInit_eqs;init_run_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@S1StartInit_defs<init_scs_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?S1StartInit_eqs<init_runs_eqC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S. Import SXA. Import SXAS.

Abbreviation SEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p'0h02Hnh11Hh22n0h31ni001nh44__p1h54__x1h62b1h72b2h83Hn0h97__arithh:4__ffh;8__varmaph<5__with=4cstrh>1xp%0p;1p;2p;3p;4p;6p;<p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002PR1p4p710p8P0P1p4p7210p8P0p1002mp4p710p8g003IR0j10Tg003hR1j21Tg004@j1>Tg004ej1QTg005Jj1cTg005hj1;Tg006Kj3[Tg006nR2j1=Tg007Nj2CTg0084j39Tg008Nj2<Tg0098j3MTg009\j4@Tg00:8j1JTg00:VR3j2ITg00;2j2?Tg00;Oj4YTg00<6j1XTg00<[j2FTg00=7j1VTg00=Wj1UTg00>7j2TTg00>Uj1PTg00?3j1OTg00?^j2BTg00@Aj2NTg00@dj4GTg00AOj1RTg00B1j6STg00BUj2bTg00C7j2DTg00CQj2aTg00D=j3`Tg00D\j4_Tg00ENl<KTg00F3l<^Tg00FXj7]Tg00G<j3ATg00G_j8\Tf4R4f3R5f2R6g00HCR7f1R8C@f0R939p=W%=9,C8p=4g00I@R:1<89'Dp=2f5R;P4P5P7P6C@%=9,C839p=3P6P8P7P9C@p=51?45/?6/?8/?9p=71D:9p=Hg00I^R<P<P:P:P0P2P2f6g00J=R=P;P4P<P<P:P:P0P2P2P5P=P6P8P9M<KM<Kp=6P<P:P1P2P3g00JaP;P4P5P6P8P9M<^p=ZP8g00KCR;g00KbR3P3g00LBR2P9g00LbF]p=EAA:45=A:6=A:8=A:9p=8P5P;P3P3P2P6P8P9G\p=L%09#0#0#0p=:g00MBR1#0R=#0R0#0R>#0R?#0R@#0RA#0RB#0RC#0RD#0RE#0RF#0RG#0RH#0RI#0RJ#0RK#0RL#0RM#0RN#0RO#0RP#0RQ#0RR#0RS#0RT#0RU#0RV#0RW#0RX#0RY#0RZ#0R[,19R\P<g00MaR]#>R^#Q#cR_#;R`P`P8g00NFRag00Nd5[_Rb%=8Rc,C_DW^0\P8111[g00O@R\%;9Rd%;8Reg00O^%;6?9891<561<5859:Rf[1<681<6959:%;5?968[Rg%;4?956\fAM689P9n2001000000120000000W7W6W3RfPg^7e^6d^3\R\P9P_P`P1P7PbC@14_1R112_1O4b1W0P<%09R1/1[P`P`%08R7PbP_P7E3]0P911=[PfP\P9P_A5`=b14_=R=12_=O4b1W0P<%01R1/1[P`P`%07R=PbP_P=E3]0P9110[PfP\P9P_A5`0b14_0R012_0O4b1W0P<%01R1/1[P`P`%0=R0PbP_P0E3]0P911>[PfP\P9P_A5`>b14_>R>12_>O4b1W0P<%01R1/1[P`P`%00R>PbP_P>E3]0P911?[PfP\P9P_A5`?b14_?R?12_?O4b1W0P<%01R1/1[P`P`%0>R?PbP_P?E3]0P911@[PfP\P9P_A5`@b14_@R@12_@O4b1W0P<%01R1/1[P`P`%0?R@PbP_P@E3]0P911A[PfP\P9P_A5`Ab14_ARA12_AO4b1W0P<%01R1/1[P`P`%0@RAPbP_PAE3]0P911B[PfP\P9P_A5`Bb14_BRB12_BO4b1W0P<%01R1/1[P`P`%0ARBPbP_PBE3]0P911C[PfP\P9P_A5`Cb14_CRC12_CO4b1W0P<%01R1/1[P`P`%0BRCPbP_PCE3]0P911D[PfP\P9P_A5`Db14_DRD12_DO4b1W0P<%01R1/1[P`P`%0CRDPbP_PDE3]0P911E[PfP\P9P_A5`Eb14_ERE12_EO4b1W0P<%01R1/1[P`P`%0DREPbP_PEE3]0P911F[PfP\P9P_A5`Fb14_FRF12_FO4b1W0P<%01R1/1[P`P`%0ERFPbP_PFE3]0P911G[PfP\P9P_A5`Gb14_GRG12_GO4b1W0P<%01R1/1[P`P`%0FRGPbP_PGE3]0P911H[PfP\P9P_A5`Hb14_HRH12_HO4b1W0P<%01R1/1[P`P`%0GRHPbP_PHE3]0P911I[PfP\P9P_A5`Ib14_IRI12_IO4b1W0P<%01R1/1[P`P`%0HRIPbP_PIE3]0P911J[PfP\P9P_A5`Jb14_JRJ12_JO4b1W0P<%01R1/1[P`P`%0IRJPbP_PJE3]0P911K[PfP\P9P_A5`Kb14_KRK12_KO4b1W0P<%01R1/1[P`P`%0JRKPbP_PKE3]0P911L[PfP\P9P_A5`Lb14_LRL12_LO4b1W0P<%01R1/1[P`P`%0KRLPbP_PLE3]0P911M[PfP\P9P_A5`Mb14_MRM12_MO4b1W0P<%01R1/1[P`P`%0LRMPbP_PME3]0P911N[PfP\P9P_A5`Nb14_NRN12_NO4b1W0P<%01R1/1[P`P`%0MRNPbP_PNE3]0P911O[PfP\P9P_A5`Ob14_ORO12_OO4b1W0P<%01R1/1[P`P`%0NROPbP_POE3]0P911P[PfP\P9P_A5`Pb14_PRP12_PO4b1W0P<%01R1/1[P`P`%0ORPPbP_PPE3]0P911Q[PfP\P9P_A5`Qb14_QRQ12_QO4b1W0P<%01R1/1[P`P`%0PRQPbP_PQE3]0P911R[PfP\P9P_A5`Rb14_RRR12_RO4b1W0P<%01R1/1[P`P`%0QRRPbP_PRE3]0P911S[PfP\P9P_A5`Sb14_SRS12_SO4b1W0P<%01R1/1[P`P`%0RRSPbP_PSE3]0P911T[PfP\P9P_A5`Tb14_TRT12_TO4b1W0P<%01R1/1[P`P`%0SRTPbP_PTE3]0P911U[PfP\P9P_A5`Ub14_URU12_UO4b1W0P<%01R1/1[P`P`%0TRUPbP_PUE3]0P911V[PfP\P9P_A5`Vb14_VRV12_VO4b1W0P<%01R1/1[P`P`%0URVPbP_PVE3]0P911W[PfP\P9P_A5`Wb14_WRW12_WO4b1W0P<%01R1/1[P`P`%0VRWPbP_PWE3]0P911X[PfP\P9P_A5`Xb14_XRX12_XO4b1W0P<%01R1/1[P`P`%0WRXPbP_PXE3]0P911Y[PfP\P9P_A5`Yb14_YRY12_YO4b1W0P<%01R1/1[P`P`%0XRYPbP_PYE3]0P911Z[PfP\P9P_A5`Zb14_ZRZ12_ZO4b1W0%01/1[%0YR1/1[Pc%J]RZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7%>^#>#>#>#JR^'IS00P11?9ZX>:R1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1PcO1S01O1S02O1S03O1R\O1RfO1RdO1ReO1RgO1RhO1RiO1RjO1RkO1RlO1RmO1RnO1RoO1RpO1RqO1RrO1RsO1RtO1RuO1RvO1RwO1RxO1RyO1RzO1R{O1R|O1R}O1R~O1P1PYP~P1PXP}P1PWP|P1PVP{P1PUPzP1PTPyP1PSPxP1PRPwP1PQPvP1PPPuP1POPtP1PNPsP1PMPrP1PLPqP1PKPpP1PJPoP1PIPnP1PHPmP1PGPlP1PFPkP1PEPjP1PDPiP1PCPhP1PBPgP1PAPeP1P@PdP1P?PfP1P>P\P1P0Q03P1P=Q02P1P7Q01P1P8Pc%HcF6F6F6F6F6F6F6F6F6F6F6F6F6F6F6F6P[P^%H^EZP9CYQ00%X6%=6,Fap-0R[g00P9Rc#V%Uc1T:8%P:%O:RcP:1B:ag00Pe1N:]R]CG,Ec%R3R1PcP:P]1B:ZR]P]P]P]D8P]P]P]P]D8P]P]P]P]D8P]P]P]P]D8P]P]P]P]D8P]P]P]P]D8P]P]P]P]D8P]P]P]P]D8g00QL1B:^CG,EcP1PcP;P3P3P2P5ESCLCL1bc2P9P6g00R3Rcg00RSR2'D1a96=9c2dA`:a8C_b:b;b<X5:W41Fa9P8PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7/I^P5[[^5:^4[P9P`P`%:4#:#:#:#:#:#:#:R`PbP_P`E3%=4P8P6O4b9b=b8W0X3<P9O1n0110001020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100P9O1W0X3<o"). Qed.

Lemma regs_ok_by_index : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i all_regs 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p'0h03Hr0h12Hxh21bi001bh32H0h44__x1h54__x2h62b1h72b2h81nh91rh:1Eh;1Hh<1Rh=7__arithh>4__ffh?8__varmaph@5__withA1ihB2srp;1p;2p;3p;4p;7p;5p;6p;8g00=Wj1GTg004@j16Tg004ej1[Tg005Jj1CTg005hj14Tg00S3j2`Tg003Ij12Tg003hj2QTg006Kj3KTg009\j41Tg00S_j1HTg00TWj38Tg00C7j2;Tg0084j30Tg00UDj1:Tg008Nj27Tg0098j3]Tg00V:j1\Tg00VXj2YTg00W9j2?Tg00Wbj3XTg00XKj3WTg00Y4j2VTg00=7j1UTg00Y`j3PTg00>7j2OTg00Z@j1NTg00Z^j4JTg00>Uj1LTg00?3j1MTg00@Aj2=Tg00@dj4ITg00FXj7>Tg00[<j5RTg00[`j6STg00AOj1TTg00G_j8iTg00BUj2hTg00CQj2gTg00D=j3fTg00D\j4eTg00\Dj2dTg007Nj2<Tg00\aj7aTg00]?j1DTg00^Aj2BTg006nj1FTg00_9j2_Tg00`:j6@Tg00`Vj1bTg00a\j2^Tg00bTj3cTg00cSj2ETf0R0#2#2p=Z%20#2#2#2p=5f4R1f3R2f2R3'Ef1R4/B030p=3g00R3R5g00RSR6700p=91E34=020p=Ag00dEg00e<R7#Gg00MaR8#6R9#[#CR:%69#6#6#6#6#CR;#4R<'`g00I^g00MBR=#2R>#2#Z#5#5#5#5#5#5#5,Q0P<P3%4:R?P4g00HCR@g00NFRAg00Nd5K:RBC1P1P7P4P2%HARCC1D3[]AA8:0BRDP51;50A8:4B=050P5A8:2B=050P<f6REP1f8RFP5P7P4PCP7%:1RGf7RHPCC1RIn0100000020000D3]0P4A8:3BRJ#9g00O@RK%40RL%44RMg00O^%43?040g00I@RN1723172430RO[1734173050N%42?034[RP%41?023\OA]340P0n2001000000120000000W7W6W8PP^7M^6L^8KP0P:P1PBg00P9RK%\8,YN1?N>5XN1?N=5WNg00f4'V%UK3P%GKPN1ON3P4%NNCJ%LN%MNRKg00KCR=g00KbR>P>g00LBRLPKP=P>P>PKP=P>P>g00f`RMPN1=N8g00g@1=N9CIR9g00LbR8F>PKP=P>P>PMDRES%T>PKP=P>P>PLP9P8F>Gi1hKLP0P31;561g03#9dAfNA4Ceb>b?b@X4NX5N1d04#9A0N43[^4N^5NP017:Bf5RN,7:P3O3b=O4b3A0?2BP?PB%9DP<PFP4f:RDPCD3]0X9?A8:BB#91<;A,;<P<PHPBf9RAPCD3eW0P1P0P4Fab3W0g00gg905JP1%:2RJ%D2O2P<PNP?PJP@PBC1PHP7PJPEPCC1D3P?P?PGP@PBC1P<PHP0P7%:NRBPFPCC1,BAR@CAX2?P0%FG,<:RJ%D1,_GE@P<PEPJPFPID3P?%FB,<:P<PFP0PDP7%:EPAPCC1D3X2?P0PN%bNE@P<PHPNP@CAP0b1b1b1W0n0110000020101P0O1b0b2P<P3P0P11^20D3eX9?Ac234eW;W<WBW:o"). Qed.

Lemma sr_val : forall E sr R (r : reg) e, regs_ok E sr R -> sr_get sr r = e -> getr R r = edenot E e.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "h01eh11Eh22HRh32Heh41Rh51bh61rh72srp;1p;2p;3p;6g00=Wj1<Tg004@j10Tg004ej18Tg005Jj15Tg005hj16Tg00S3j2;Tg00bTj3:Tg00a\j23Tg0084j32Tg00^Aj21Tg00C7j27Tg00\aj64Tg00cSj29Tg00dEg00e<R0#<g00Ma#0R1#8#5R2%01#0#0#0#0#5#6R1';%62f4R2f3R3f2R43:1324f1R5520P1f6R6f5/33R7'1f0R8f7R9/13R:521X51P0P41198=21:X001164,71P7P8E41923P5P3O1E4W3W2X00W6W4W7W1o"). Qed.

Definition D8_cells : list (Z * nat) :=
  [(1050088, 8%nat); (1181408, 8%nat); (1181416, 8%nat); (1181424, 8%nat); (1050096, 8%nat); (1050104, 8%nat); (1050112, 8%nat); (1050120, 8%nat); (1050128, 4%nat); (1050136, 4%nat); (1050216, 8%nat); (1050248, 8%nat); (1050280, 8%nat); (1050288, 8%nat); (1050312, 8%nat); (1181992, 4%nat); (1181993, 1%nat); (1181996, 4%nat); (1182008, 8%nat); (1182016, 8%nat); (1182024, 1%nat); (1182032, 8%nat); (1182048, 8%nat); (1182056, 8%nat); (1182072, 8%nat); (1182128, 8%nat)]%Z.

Definition cells_miss (cells : list (Z * nat)) (i : Z) : bool :=
  ((0 <=? i)%Z && (i + 1 <=? 2 ^ 64)%Z
   && forallb (fun c => (i + 1 <=? fst c)%Z || (fst c + Z.of_nat (snd c) <=? i)%Z) cells)%bool.

Definition range_miss (cells : list (Z * nat)) (lo hi : Z) : bool :=
  ((0 <=? lo)%Z && (hi <=? 2 ^ 64)%Z
   && forallb (fun c => (hi <=? fst c)%Z || (fst c + Z.of_nat (snd c) <=? lo)%Z) cells)%bool.

Lemma range_miss_pt : forall cells lo hi i, range_miss cells lo hi = true -> (lo <= i < hi)%Z ->
  cells_miss cells i = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "h01ch11Hh24__x1h34__x2h41xh52Hbh64__p1h72b1h82b2h95lemmah:1mh;1nh<1Ah=7__arithh>4__ffh?6__sat4h@6__sat5hA8__varmaphB5__withC2H1hD2H2hE2HahF4__x3hG4__x4hH4__x5hI1fhJ1lhK1BhL2H3hM2HchN2HihO5cellshP4cstrhQ2hihR1ihS2lohT1yp&0p;2p;1p;3p;4p;6p;8p;7p;=p;;g00hGk20=Tg00=Wj1TTg00hgj3zTg00<[j21Tg00:Vj2BTg00O^R0j2CTg004@j1>Tg00:8j1STg00ifj2kTg00jCj23Tg00j`j29Tg006nj1<Tg00;2j22Tg00k>j35Tg00kZj3]Tg00l=j2GTg00l]j2tTg00mEj3sTg003Ij1MTg00W9j2HTg00Y4j2UTg00=7j1lTg00Y`j3OTg00>7j2NTg00Z@j1jTg00Z^j4ETg00>Uj1iTg00?3j1hTg00@Aj2DTg00B1j6gTg00AOk10<Tg00?^j2VTg00BUk20;Tg00C7k20:Tg00CQk205Tg00D=k304Tg00D\k403Tg004ej1dTg00@dj4RTg005Jk100Tg00mij3~Tg00G<j3bTg00nLj4_Tg00ngj3XTg00oPj3ITg00ogj3^Tg010Jj6}Tg010ej2FTg011BR1j28Tg011\j2|Tg012<R2j2LTg012Uj4JTg000Sj4{Tg013<j2yTg013iR3j2xTg014Gj4wTg014ij8PTg015\j3uTg00<6j1rTg016Rj2qTg0084j3`Tg002Pj3pTg017Qk301Tg00XKk302Tg00FXj7fTg017nj7oTg00G_j8nTg018Rj4mTg019Em=06k707Tg01:4m;08Tg01:ok709Tg00R3R4f0R5g00RSR63`p=0g00NFR7/35p=:g00I@R8g00I^R9;p5p==B01895p=@f2R:f1R;'3/F5p=af3R</3:13;5'Fp=713;5=`46p=41175p=;B028;5p=AP:g00KCR=g00KbR>P>g00LBR?P8P;g00PeP5CRg00LbR@Ffp=6P:P=P>P>P?P;P5Fop=WP<P=P>P>P?P:P;P5Gnp=?P;P=P>P>P?P5P@Ffp=cp-0RAP;P2P5CJp=QPAf4RBP2P2P<P:P;P5GPp=ZPAP2P;P5Cmp=KP5P;P1g01;SRCP:P@P<PBf5RDf6REf7RFf8RGf9RHN=06p=[PAPAP2P2P5P2P3g01<DGPp=vP<P:P1PCP;P@P5K07p=ePAPFP2PEP1PDPBP<P:P;P5N;08p=YP:P=P>P>P?P;P5K09p=\20=89R9#TAz<:;#011<;1B;:'C%:BR1g00MaR@#>RC#SRI%>CRJ#>#>#>#>RK#SRL'kRM,3<'9RN%=5RO%@5#<,2ORP/3DRQ5aBX09=59DRR;];%0N%0R'CP0%:D13BM'9#0PDPOPPPEC7X09=59E#0%S@RR,2B/3M,9112DR?aOQX09=59F'9#0P5%:F13EM'9#0PGPOPPPHC7X09=59H#0%:HRQ13GMRG;];%0Q%0G'CP0f:RG#:#014HM12HR/3M,9Q12GRPOPPPGC7X09f<RG559'9#0P5%:G#014GMP014;511:;RQ[RH11;5R114:;RN[RS11<:\N1G;5RNP;n2001000000120000000X:8X;8RTPH^:8^;8RUP5P7f?RVP:O3%;VPTPUP5f@RUPMP<O311UM%:URT12UR/3MRU'9RVfARW/2RRXPOPPPWC7X09fC559RY%0V%0Y%0T%0UP0PHPS14<:\QPNP5n2001000000120000000X:8X;8RNPS^:8^;8RSP5P7PW1tILRW1B7I%;L1B7M[[RQ%;IRHg01=5RYAsIL;UWERL%;M\Y^EHRHg00P9RYg00MBRV#MRZ#MR[,H8R\1H8ZRZ1H8VRV'A'Ag00f4R]'U%lYR^3OR_%TYR`P81N8:RaP;%j8RbCE%i8Rc%h8Rd1D8CRe1D8@Rf56dPdP=P>P>P?PBEgR=5Wd&0<>R>Pd1V87Rg=6deP>A6dgfC?C?20;d?R?P5P:20:462055:#0dB0487;H03R7b>bAbBX28X38X6A1C1:%;:R1P1[[^28^38^6AP5fDR1fER6'BfFRgP1fBRhPEO5b=b?b@O3b1PNPSP5PXPMPWPQPLPHP_P`P8PbP;PaCEPcPdP8Pfg00QLRa%d@,D8R@CR,cd9Wd=P>Pd1V8I&00K5~8RK96d@P>1V8R9b8fRI=6dKC?C?P?P7b>bAbBX28X38X6A1B5;,C:11:M12:RRK/1M[[^28^38^6AP511g1P6P1PhPBO5b=b?b@O3b1C_9XTUg002mp4p710RUP4\5RT%T;RMP0A5:;5#0AIB5:PBP;O1#0[^4<R=[AI<5;P<P;O1#0[^4:A5<:;#0[R_A5B<:#0\=A^:;5P5n2001000000120000000WJWIW<P_^JM^IT^<UP5P912hRPOPPPhC7X09P1AI956P6POPPPgC7X09R6=59g#0fHR19I95P1POPPfIRhC7X09P;O1#0[^49[fGRU9I95PUPOPPP1C7X09P;O1#0[^49PgPOPPPUC7X09=59U#0[A^96gPGP;P5E}P6P;O1#0P01F;5#0%0:R6%0;RG'8RP[RO%05,8G1F:;#0RG[RT%0</86\G1|;5RGP;n2001000000120000000X84X74PO^84^74P5%=<R6,3gRg%@<#<,26/3UR6P;O3%0g%06'8P0POPT1F<:#0\PPGP5n2001000000120000000X84X74PT^84^74P512URR4%=DRT'3RG%@D#<,2TRP/3U%0G114T'LPA^KARG^<ARUPA\APAPAP2P2CJRO'QR0PAPAP2PAPAPAP3C{R6CJRg,QGRMPG1yA2R_POPgPAPAP2P2P_P2P6PAP21x5;XTAX4Ag01=QCwGPDZR6121RR=%=ERX'411=XP5%@E#<,2XRE/41R=P=g01>G9uA2RS/K=M:[W91G4T141T111TR4'LPUP0PAPAP2P3CJR3,QGR2PGP_POP3%v_DZR_14hX11hXRXP5fJRO,4ERUPU1KSUM:[W91G1TP;O214Ph,8411E1,L=PGPgPG\ARAP0PMP6Ce12hR%=FRR'1R61KS6%@FRF#<R6,2RRM/4h11MhP5GYW91GE111EOR1,LUPGP3PAP0P2P_Ce11ORRR1KSRfKRR,4M11MRP5GYW91GEOP5O218X1%rF%;6PWPQPLPH%M[R[#M,H8RH1H8[/AV'A/U]1A\Z,AH/U]=OY^5OYP`P8P81N8BP:PbCEP;P81N8DP<PbCECEPcPd%dC,D8RC=6deAb8e@R@1D8JRJ56d5\dP>PdA6dJfP8PfPaPCCR,cd5WdP>A6dIeA6d@f5\dC?C?P?P7b>bAbBX28X38XF8XG8XH811B;R712;:/1<'81B;D,C711K<12<B/1:'8[[^28^38^F8^G8^H8P5fNfOf;R<#@#<%=<fMPBPRO7b=b?b@bPb5O2b5O2O3b1b5b1b5WMX09O4b1C_3XbDb1bCb1WDWCP;P5O2n2001000000121000000b1WLW1P;P5O2n2001000000121000000b11qD:#0eWNW1XR8XQ8XS8WOo"). Qed.

Lemma wseg_ed000 : wseg_ok SEGS (Z_to_bv 64 0xed000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#4#3#3#4#3#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_ee000 : wseg_ok SEGS (Z_to_bv 64 0xee000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#4#3#3#3#4#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_ef000 : wseg_ok SEGS (Z_to_bv 64 0xef000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#4#3#3#3#3#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_f0000 : wseg_ok SEGS (Z_to_bv 64 0xf0000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2;Tg005Jj15Tg004ej14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg004@j12Tg003Ij11Tf0R0#2#2p=:%20#2#2#2p=3%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1';g01?mg00MaR2#:#3#5%42#4#4#3#3#3#3#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_f1000 : wseg_ok SEGS (Z_to_bv 64 0xf1000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#3#4#2#3#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_f2000 : wseg_ok SEGS (Z_to_bv 64 0xf2000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#3#2#3#4#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_f3000 : wseg_ok SEGS (Z_to_bv 64 0xf3000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj17Tg004ej13Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j35Tg004@j14Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#7%32#3#3#2#3#3#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=501do"). Qed.
Lemma wseg_f4000 : wseg_ok SEGS (Z_to_bv 64 0xf4000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2;Tg005Jj16Tg004ej14Tg004@j12Tg00:8j1:Tg007Nj29Tg01?7j38Tg0084j37Tg003Ij11Tf0R0#2#2p=5%20#2#2#2p=3%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1';g01?mg00MaR2#5#3#6%42#4#4#2#4#5#3#3#3#:'9g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#038=701do"). Qed.
Lemma wseg_f5000 : wseg_ok SEGS (Z_to_bv 64 0xf5000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#3#4#3#4#3#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_f6000 : wseg_ok SEGS (Z_to_bv 64 0xf6000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#3#4#3#3#4#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_f7000 : wseg_ok SEGS (Z_to_bv 64 0xf7000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#3#4#3#3#3#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_f8000 : wseg_ok SEGS (Z_to_bv 64 0xf8000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2;Tg005Jj16Tg004ej14Tg004@j12Tg00:8j1:Tg007Nj29Tg01?7j38Tg0084j37Tg003Ij11Tf0R0#2#2p=5%20#2#2#2p=3%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1';g01?mg00MaR2#5#3#6%42#4#4#4#2#5#3#3#3#:'9g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#038=701do"). Qed.
Lemma wseg_f9000 : wseg_ok SEGS (Z_to_bv 64 0xf9000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj17Tg004ej13Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j35Tg004@j14Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#7%32#3#3#3#2#3#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=501do"). Qed.
Lemma wseg_fa000 : wseg_ok SEGS (Z_to_bv 64 0xfa000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#3#3#4#3#4#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_fb000 : wseg_ok SEGS (Z_to_bv 64 0xfb000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#3#3#4#3#3#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_fc000 : wseg_ok SEGS (Z_to_bv 64 0xfc000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2;Tg005Jj16Tg004ej13Tg00:8j1:Tg007Nj29Tg01?7j38Tg0084j37Tg004@j12Tg003Ij11Tf0R0#2#2p=5%20#2#2#2p=4%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1';g01?mg00MaR2#5#4#6%32#3#3#3#3#5#4#4#4#:'9g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#038=701do"). Qed.
Lemma wseg_fd000 : wseg_ok SEGS (Z_to_bv 64 0xfd000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#3#3#3#4#3#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_fe000 : wseg_ok SEGS (Z_to_bv 64 0xfe000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg004ej13Tg004@j14Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j37Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#5%32#3#3#3#3#3#4#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wseg_ff000 : wseg_ok SEGS (Z_to_bv 64 0xff000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj17Tg004ej13Tg00:8j19Tg007Nj28Tg01?7j36Tg0084j35Tg004@j14Tg003Ij11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00MaR2#2#2#2#7%32#3#3#3#3#3#3#2#2#2#2#2#2#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=501do"). Qed.
Lemma wseg_100000 : wseg_ok SEGS (Z_to_bv 64 0x100000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj15Tg00:8j19Tg007Nj28Tg01?7j37Tg0084j36Tg004@j12Tg003Ij11Tf0R0#2#2p=4%20#2#2#2p=3%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00Ma#4#3R2#5%42#3#3#3#9'8g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#037=601do"). Qed.
Lemma wseg_101000 : wseg_ok SEGS (Z_to_bv 64 0x101000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) [] "p;2p;1p;3g00C7j2:Tg005Jj14Tg004@j13Tg004ej19Tg00:8j18Tg007Nj27Tg01?7j35Tg0084j36Tg003Ij11Tf0R0#3#3p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00R3R0g00RSR1':g01?mg00Ma#2#2#2R2#4%32#9#2#2#2#2#2#2#8'7g00MB#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#035=601do"). Qed.
Lemma wseg_102000 : wseg_ok SEGS (Z_to_bv 64 0x102000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_103000 : wseg_ok SEGS (Z_to_bv 64 0x103000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_104000 : wseg_ok SEGS (Z_to_bv 64 0x104000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_105000 : wseg_ok SEGS (Z_to_bv 64 0x105000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_106000 : wseg_ok SEGS (Z_to_bv 64 0x106000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_107000 : wseg_ok SEGS (Z_to_bv 64 0x107000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_108000 : wseg_ok SEGS (Z_to_bv 64 0x108000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_109000 : wseg_ok SEGS (Z_to_bv 64 0x109000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_10a000 : wseg_ok SEGS (Z_to_bv 64 0x10a000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_10b000 : wseg_ok SEGS (Z_to_bv 64 0x10b000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_10c000 : wseg_ok SEGS (Z_to_bv 64 0x10c000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_10d000 : wseg_ok SEGS (Z_to_bv 64 0x10d000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_10e000 : wseg_ok SEGS (Z_to_bv 64 0x10e000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_10f000 : wseg_ok SEGS (Z_to_bv 64 0x10f000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_110000 : wseg_ok SEGS (Z_to_bv 64 0x110000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_111000 : wseg_ok SEGS (Z_to_bv 64 0x111000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_112000 : wseg_ok SEGS (Z_to_bv 64 0x112000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_113000 : wseg_ok SEGS (Z_to_bv 64 0x113000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_114000 : wseg_ok SEGS (Z_to_bv 64 0x114000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_115000 : wseg_ok SEGS (Z_to_bv 64 0x115000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_116000 : wseg_ok SEGS (Z_to_bv 64 0x116000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_117000 : wseg_ok SEGS (Z_to_bv 64 0x117000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_118000 : wseg_ok SEGS (Z_to_bv 64 0x118000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_119000 : wseg_ok SEGS (Z_to_bv 64 0x119000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_11a000 : wseg_ok SEGS (Z_to_bv 64 0x11a000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_11b000 : wseg_ok SEGS (Z_to_bv 64 0x11b000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_11c000 : wseg_ok SEGS (Z_to_bv 64 0x11c000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_11d000 : wseg_ok SEGS (Z_to_bv 64 0x11d000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_11e000 : wseg_ok SEGS (Z_to_bv 64 0x11e000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_11f000 : wseg_ok SEGS (Z_to_bv 64 0x11f000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_120000 : wseg_ok SEGS (Z_to_bv 64 0x120000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_121000 : wseg_ok SEGS (Z_to_bv 64 0x121000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rw_wview : forall m (x : word), (0xee000 <= bv_unsigned x < 0x122000)%Z -> wview SEGS m x <> None.
Proof.
  intros m x Hx.
  assert (C : forall lo : Z, wseg_ok SEGS (Z_to_bv 64 lo) 4096 = true -> (0 <= lo)%Z -> (lo + 4096 <= 2 ^ 64)%Z ->
              (lo <= bv_unsigned x < lo + 4096)%Z -> wview SEGS m x <> None).
  { intros lo W H0 H1 Hr.
    apply (store_ok_all SEGS m 4096 (Z_to_bv 64 lo)); [rewrite u_small by lia; lia | | rewrite u_small by lia; lia].
    apply store_ok_wseg; exact W. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xef000%Z).
  { apply (C 0xee000%Z wseg_ee000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf0000%Z).
  { apply (C 0xef000%Z wseg_ef000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf1000%Z).
  { apply (C 0xf0000%Z wseg_f0000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf2000%Z).
  { apply (C 0xf1000%Z wseg_f1000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf3000%Z).
  { apply (C 0xf2000%Z wseg_f2000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf4000%Z).
  { apply (C 0xf3000%Z wseg_f3000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf5000%Z).
  { apply (C 0xf4000%Z wseg_f4000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf6000%Z).
  { apply (C 0xf5000%Z wseg_f5000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf7000%Z).
  { apply (C 0xf6000%Z wseg_f6000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf8000%Z).
  { apply (C 0xf7000%Z wseg_f7000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf9000%Z).
  { apply (C 0xf8000%Z wseg_f8000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xfa000%Z).
  { apply (C 0xf9000%Z wseg_f9000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xfb000%Z).
  { apply (C 0xfa000%Z wseg_fa000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xfc000%Z).
  { apply (C 0xfb000%Z wseg_fb000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xfd000%Z).
  { apply (C 0xfc000%Z wseg_fc000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xfe000%Z).
  { apply (C 0xfd000%Z wseg_fd000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xff000%Z).
  { apply (C 0xfe000%Z wseg_fe000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x100000%Z).
  { apply (C 0xff000%Z wseg_ff000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x101000%Z).
  { apply (C 0x100000%Z wseg_100000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x102000%Z).
  { apply (C 0x101000%Z wseg_101000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x103000%Z).
  { apply (C 0x102000%Z wseg_102000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x104000%Z).
  { apply (C 0x103000%Z wseg_103000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x105000%Z).
  { apply (C 0x104000%Z wseg_104000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x106000%Z).
  { apply (C 0x105000%Z wseg_105000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x107000%Z).
  { apply (C 0x106000%Z wseg_106000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x108000%Z).
  { apply (C 0x107000%Z wseg_107000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x109000%Z).
  { apply (C 0x108000%Z wseg_108000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10a000%Z).
  { apply (C 0x109000%Z wseg_109000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10b000%Z).
  { apply (C 0x10a000%Z wseg_10a000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10c000%Z).
  { apply (C 0x10b000%Z wseg_10b000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10d000%Z).
  { apply (C 0x10c000%Z wseg_10c000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10e000%Z).
  { apply (C 0x10d000%Z wseg_10d000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10f000%Z).
  { apply (C 0x10e000%Z wseg_10e000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x110000%Z).
  { apply (C 0x10f000%Z wseg_10f000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x111000%Z).
  { apply (C 0x110000%Z wseg_110000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x112000%Z).
  { apply (C 0x111000%Z wseg_111000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x113000%Z).
  { apply (C 0x112000%Z wseg_112000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x114000%Z).
  { apply (C 0x113000%Z wseg_113000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x115000%Z).
  { apply (C 0x114000%Z wseg_114000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x116000%Z).
  { apply (C 0x115000%Z wseg_115000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x117000%Z).
  { apply (C 0x116000%Z wseg_116000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x118000%Z).
  { apply (C 0x117000%Z wseg_117000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x119000%Z).
  { apply (C 0x118000%Z wseg_118000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11a000%Z).
  { apply (C 0x119000%Z wseg_119000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11b000%Z).
  { apply (C 0x11a000%Z wseg_11a000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11c000%Z).
  { apply (C 0x11b000%Z wseg_11b000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11d000%Z).
  { apply (C 0x11c000%Z wseg_11c000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11e000%Z).
  { apply (C 0x11d000%Z wseg_11d000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11f000%Z).
  { apply (C 0x11e000%Z wseg_11e000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x120000%Z).
  { apply (C 0x11f000%Z wseg_11f000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x121000%Z).
  { apply (C 0x120000%Z wseg_120000); lia. }
  apply (C 0x121000%Z wseg_121000); lia.
Qed.

Section P7.
  Variable sp0 : word.
  Variable rdraw : EntryDraw.
  Variable Jb : word -> option byte.
  Variables av envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av envv uid hw rdraw)) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) ["P7"] "h01ah14__x1h21Hh32H1h42H2h52_Hh67__arithh74__ffh86__sat3h98__varmaph:5__with;4cstrh<1vp;1p;2p;3p;4p;7p;8g00:8j15Tg004@j14Tg005Jj19Tg005hj1ZTg00=Wj1>Tg01__j2<Tg006nj1;Tg00<[j20Tg00O^R0j23Tg01`?j1DTg01a;j37Tg007Nj2YTg00oPj3VTg01IUj1UTg01a\j1RTg0084j36Tg01b`j2QTg01cTj2OTg00<6j1NTg008Nj2LTg01ckj2KTg01d\j2JTg00=7j1ITg00>7j2FTg00>Uj1GTg00?3j1HTg00@Aj2ETg00?^j2?Tg00@dj4:Tg00AOj1CTg017nj7MTg00BUj2BTg00C7j2PTg00CQj2ATg00D=j3STg00D\j4TTg004ej1@Tg00FXj7XTg00G_j8WTf0R1#4#4p=1%@1#@p=2f1R2g00KCR3g00KbR4P4g00LBR5P1g00LbFXp=8f3P3P4P4P5f2R6P2P1GWp==p,3Hvag00MaR7#5R8%47#1R9#9R:#ZR;#>R<p,2avR='<R>#;R?'0R@%49R9#1RA#1#1RB#5RC,0?RD'3RE%D=%4B#1#1#1#1#1#5'01<;1#;%27#2#2#2#2#2#2#2#5'0X0<=7<=g00NFRB,Y:=V;1#UX0<=7<=g01e<R;g00R3R:%R1g00ggRF36g01el,Q1=6:F'3X0;1O<=37'3'3'3R='3P0PEP=PEP1P0P@PDPE\=P1%N>10B?%9Ap,3sp0'LRA%59R9'K10BA10B91JA9,0B[[g00I@R9g00P9RA#I%>A1F92%G9%H9RAP91E97R7g00PeR>1?9CC:,8AR0%C4R<PAP91?98P>P7C:,8AR7P<PAP3P4P4P5P7P0FMC=C=1BA5P1P6g00RSRA,P:1A16=6:AdAS9B2CTb7b9b:W1101C10821086106C'3[[^19P1P?f4f5O3b6b8b;X5=X4DX3@P2P1O2n2001000010121000000X2EP2P1O2n2001000000121000000b<o"). Qed.

  Lemma D8_none : forall tid i, cells_miss D8_cells i = true -> D8 sp0 av envv hw tid rdraw (Z_to_bv 64 i) = None.
Proof.
  intros tid i Hb. pose proof (u64_range tid) as Ht. pose proof len_av as Hlen.
  unfold cells_miss, D8_cells in Hb. cbn [forallb fst snd] in Hb.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
  repeat match goal with H : (_ || _)%bool = true |- _ => apply Bool.orb_true_iff in H; rewrite !Z.leb_le in H end.
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  unfold D8, D_libc.
  repeat (rewrite wbytes_outside by (len_simpl; rewrite ?u_small by lia; lia)).
  reflexivity.
Qed.

  Definition E8 (regs : bvmap 5 word) : env :=
    Env (fun n => match n with
                  | 0%N => sp0
                  | 1%N => argc_w av
                  | 2%N => envp_w sp0 av
                  | 40%N => canary rdraw
                  | _ => getr regs (Z_to_bv 5 (Z.of_N n - 3))
                  end) (fun _ => []).

  Lemma alu_sp : forall regs k, edenot (E8 regs) (EAlu ALU_ADD (EVar 0) (ELit k)) = Z_to_bv 64 (bv_unsigned sp0 + k).
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) ["P7"] "h01zh12b1h22b2h31nh41Hh51bh61kh74regsp;1p;2p;3p;6g004@j19Tg004ej1MTg005Jj1<Tg005hj17Tg00S3j2LTg028Mj1ITg029Dj2DTg007Nj28Tg02:8j2@Tg008Nj20Tg00;2j22Tg0084j35Tg0098j3KTg02:kj24Tg00:8j1>Tg00ifj2HTg01d\j23Tg00C7j2ETg02;Qj3CTg02<8j1:Tg02=3j2;Tg02=bj3BTg02>Jj2ATg00\aj6=Tg02??j1FTg00S_j1GTg02@7j3?Tg00^Aj2JTg00I@R0f1R1f0R235p=1P0f4R3f3R4f2R5P1P2E=p=6g00Ma#9R6#M#<%96#9#9#9#9R7#<R8#7R9'LP9%I1R:g02@oR;'DR<1882R='@R>p,3sp0,08R?/21R@,88RA9592X59g00O@RB%72RC%71RDg00O^%75?51210451041'1RE[10511052'1%74?551[RF%73?545\EAK512P2n2001000000120000000W2W1W3PF^2D^1C^3BP2P81881,08RB,2?RC,88RDPA148C12?5RF,88,08RE,12X001481R412?2R3,48/1EX00148@RE1485,2?,48/12X0012?4RG%>6%>7'HR7'3148FR6,12X001317RH1337/16X0013@7R61357,2?/37/12X00P613F7,12X001E0612?H/37AC1?7D6PE%:@D6P4%:1D6148G%:GD6108A1;8@D6PB1;81D6108D1;8CD6O4b41883R3959>eg02AMR>?B<=1A<=E=%F;%G25?>,J:=593eX60W7o"). Qed.
  Lemma spx_val : forall regs k, edenot (E8 regs) (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
Proof.
ltac2:(KReplay.run1 (kr_t_S1StartInit ()) ["P7"] "h01kh14regsp;1p;2g004@j10Tg004ej15Tg005Jj11Tg005hj12Tg00S3j24Tg02B9j23Tg00Ma#0R0#5#1%00#0#0#0#0#1#2'4g00I@f1f0'3W0W1o"). Qed.

  Theorem start_init_run : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 850416 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 1050296 ->
    getr regs 8 = Z_to_bv 64 945944 ->
    getr regs 9 = Z_to_bv 64 945928 ->
    getr regs 18 = Z_to_bv 64 415208 ->
    getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs' J', wfJ sp0 J' ->
        getr regs' 1 = Z_to_bv 64 0xcfab0 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 0x10800 ->
        getr regs' 4 = Z_to_bv 64 0x1006b8 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = argc_w av ->
        getr regs' 10 = argc_w av ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 0x655e8 ->
        getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        (forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = Z_to_bv 64 0) ->
        G (mkst regs' (0x655e8 : word) (CM J' (apply_runs init_runs (D8 sp0 av envv hw tid rdraw))) rom)) ->
    G (mkst regs (0x930bc : word) (CM (J8 sp0 av envv uid hw Jb s1v) (D8 sp0 av envv hw tid rdraw)) rom).
Proof.
Ltac kimg := split; [lia|]; split; [lia|]; intros i Hi;
                rewrite cmem_at_data by region_side;
                apply D8_none; eapply (range_miss_pt D8_cells); [ | exact Hi]; vm_compute; reflexivity.
  intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
  pose proof len_av as Hlen. pose proof (u64_range tid) as Htid.
  assert (HJ8 : wfJ sp0 (J8 sp0 av envv uid hw Jb s1v)) by (unfold J8, J_aux, J_lsm; repeat apply wfJ_wbytes; exact HJ).
  assert (HR : regs_ok (E8 regs) sr8 regs).
  { apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr8 all_regs]; rewrite ?spx_val;
      first [ reflexivity
            | match goal with H : getr regs ?r = _ |- getr regs ?r = _ =>
                rewrite H; cbn [edenot ev E8]; first [ reflexivity | f_equal; lia | unfold envp_w; reflexivity ] end ]. }
  assert (HK : know_ok SEGS (E8 regs) (CM (J8 sp0 av envv uid hw Jb s1v) (D8 sp0 av envv hw tid rdraw)) kn8).
  { unfold kn8, know_ok. repeat apply Forall_cons; try apply Forall_nil.
    - cbn [kentry_ok edenot ev E8]. lia.
    - cbn [kentry_ok edenot ev E8]. split; [lia | exact Hal].
    - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot ev E8].
      rewrite (u_small 8388608) by lia. split; [lia|]. intros d m Hd Hm.
      apply store_ok_cmem_win; [exact HJ8 | region_side | region_side].
    - eapply (kword_intro SEGS (E8 regs) _ (EVar 0) sp0 (-56) 8 _ (Z_to_bv 64 0xcfaa0)); [reflexivity | reflexivity | lia | lia | lia | lia |].
      rewrite rdn_cmem_win by region_side. unfold J8. rd_hit8.
    - eapply (kword_intro SEGS (E8 regs) _ (EVar 0) sp0 (-64) 8 _ (Z_to_bv 64 (bv_unsigned sp0 + 8))); [reflexivity | apply spx_val | lia | lia | lia | lia |].
      rewrite rdn_cmem_win by region_side. unfold J8. rd_hit8.
    - eapply (kword_intro SEGS (E8 regs) _ (EVar 0) sp0 (-72) 8 _ (argc_w av)); [reflexivity | reflexivity | lia | lia | lia | lia |].
      rewrite rdn_cmem_win by region_side. unfold J8. rd_hit8.
    - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
      rewrite (u_small 0) by lia. rewrite (u_small 0x34000) by lia. split; [lia|]. intros d m Hd Hm.
      apply store_ok_of_all; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
      apply rw_wview. lia.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - kimg.
    - eapply (kword_intro SEGS (E8 regs) _ (ELit 0) (Z_to_bv 64 0) 0x100688 8 _ (Z_to_bv 64 0x120980)); [reflexivity | reflexivity | lia | lia | rewrite (u_small 0) by lia; lia | rewrite (u_small 0) by lia; lia |].
      rewrite (u_small 0) by lia. rewrite Z.add_0_l. rewrite rdn_cmem_data by region_side. unfold D8. rd_hit8.
    - eapply (kword_intro SEGS (E8 regs) _ (ELit 0) (Z_to_bv 64 0) 0x120928 8 _ (canary rdraw)); [reflexivity | reflexivity | lia | lia | rewrite (u_small 0) by lia; lia | rewrite (u_small 0) by lia; lia |].
      rewrite (u_small 0) by lia. rewrite Z.add_0_l. rewrite rdn_cmem_data by region_side. unfold D8. peel. apply rd_guard. }
  destruct init_run_shape as (Hsh & Hpc & Hsr & Hlog).
  destruct (runA_sound SEGS 20000 [MAIN] (SCR [] [] []) CXX_INIT sr8 kn8 41 (fst (fst init_run)) init_scs (snd init_run)
              (E8 regs) (CM (J8 sp0 av envv uid hw Jb s1v) (D8 sp0 av envv hw tid rdraw)) rom regs)
    as (R & HR' & _ & Hms).
  { rewrite init_run_eq. exact Hsh. }
  { exact HR. }
  { exact HK. }
  { rewrite init_scs_nil. constructor. }
  rewrite Hpc, Hlog in Hms. rewrite Hsr in HR'.
  destruct (split_sound sp0 (wrap_mem RPH sp0 av envv uid hw rdraw) (E8 regs) 0 SLO SHI DLIM) with
      (log := init_log) (J := J8 sp0 av envv uid hw Jb s1v) (D := D8 sp0 av envv hw tid rdraw) as (J' & HJ' & Hm).
  { cbn [ev E8]. unfold win_lo, SLO. rewrite stack_max_size_val. lia. }
  { cbn [ev E8]. unfold SHI. lia. }
  { unfold DLIM, win_lo. rewrite stack_max_size_val. lia. }
  { exact init_split_ok. }
  { exact HJ8. }
  rewrite Hm, init_runs_eq in Hms.
  replace (Z_to_bv 64 CXX_INIT) with (0x930bc : word) in Hms by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 MAIN) with (0x655e8 : word) in Hms by (apply bv_eq; reflexivity).
  eapply HG; [exact Hms|].
  Ltac regv HR' :=
    lazymatch goal with |- getr ?R ?r = _ =>
      rewrite (HR' r);
      let e := eval vm_compute in (sr_get init_sr r) in change (sr_get init_sr r) with e;
      first [ reflexivity | rewrite alu_sp; f_equal; lia | cbn [edenot ev E8]; first [ reflexivity | unfold envp_w; reflexivity ] ] end.
  apply (Hk R J' HJ'); try regv HR'.
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [regv HR'|]). destruct Hr.
Qed.
End P7.
