(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed ME, kr_t_Ns0HeapBridgeHn, main_hi_heap0 and 5 more; added auxv_pairs_facts, auxv_pairs_length, auxv_pairs_words and 6 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Src0HeapBridge.v, 111 lines within its lines 28-353. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Mem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Cells OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Step OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Arr.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Ref.Mh_0073. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Ref.Mh_0091. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Ref.Mh_0254. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Ref.Mh_0073.RMallocRep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Ref.Mh_0073.RMallocTree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Ref.Mh_0073.RMalloc_iface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Ref.Mh_0091.RF_aligned OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Ref.Mh_0254.RF_aligned_spec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap Require HnIface HnInst0. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0283. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.HnIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.HnInst0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0283.HnClosed OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0283.HnV16.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require LibTail. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0Exit_run1. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LibTail OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ZStores OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.DrvKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0StartupDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Startup OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0StartupFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0MainEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258.Ns0DrvLibL OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258.Ns0DrvG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258.Ns0DrvMain OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0Exit_run1.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Ns0HeapBridgeHn () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr01I46Stdlib9micromega7EnvRing5PExpr00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00K47Corelib7Numbers7BinNums1N02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC45stdpp9bitvector;definitions7Z_to_bvI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00C59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~K47Corelib4Init;Hexadecimal4uint02K47Corelib4Init;Hexadecimal4uint06K47Corelib4Init;Hexadecimal4uint05K47Corelib4Init6Number4uint02C47Corelib4Init3Nat;of_num_uintC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_windowC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums8positive00I47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes3nat00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init;Hexadecimal4uint01C59OSSVerify5KrLib7Mh_0058<Ns0MainEntry9wseg_dataC1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint04K47Corelib4Init7Decimal4uint09K47Corelib4Init7Decimal4uint08K47Corelib4Init7Decimal4uint0:K47Corelib4Init6Number4uint01C59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint01C47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z3mulI46Stdlib9micromega=RingMicromega5Psatz00C47Corelib4Init3Nat3addC59OSSVerify5KrLib7Mh_0058<Ns0MainEntry5auxvpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058<Ns0MainEntry3rndC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs8canary_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Heap7HnInst0=init_statics0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7ph_addrC56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_entC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_numC56Stdlib6ZArith6BinInt1Z6shiftrK79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell04C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib5Lists7ListDef5skipnC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega:ZMicromega=Zeval_formulaC46Stdlib9micromega5Tauto7eval_bfC59OSSVerify5KrLib7Mh_00419RefLayout8auxv_offC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cells_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs6D_mainC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef3nthC49OSSVerify5KrLib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomI47Corelib4Init5Peano2le00C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init9Datatypes3appC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058<Ns0MainEntry7auxvp_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058<Ns0MainEntry5rnd_uC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts<D_main_missbC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHn=mem_main_noneC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_wfC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHn<rdn_main_imgC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHn=store_ok_dataC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHn?rw_cells_of_rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts?D_main_pagesizeC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHn=rdn_main_dataC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapc49OSSVerify5KrLib?Ns0HeapBridgeHnDbytes_eq_of_unsignedC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc49OSSVerify5KrLib?Ns0HeapBridgeHn>store_ok_relroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts@main_entry_guardC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_0058>Ns0StartupDefsGlength_word_to_le_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutFlength_at_random_bytesC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List=length_firstnC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib=SymExec2Sound4SX2SCbytes_le_to_Z_boundC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib7Mh_0058<Ns0MainEntry<D_main_auxvpC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib7Mh_0058<Ns0MainEntry9main_auxvC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem<bytes_at_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00417ArgvEnv>rdn_wmem_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00417ArgvEnv4wmemC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDriveGword_to_le_bytes_of_lezC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058:Ns0StartupDmain_entry_rdn_aboveC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7ro_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Heap7HnInst0@ref_ro_addr_trueC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init5Logic2ex00C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8bytes_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr4u64sC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init5Peano2ltc49OSSVerify5KrLib?Ns0HeapBridgeHn?bytes_at_of_rdnC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHn=bytes_at_app2C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Ref7Mh_0052:F_syscalls5rsegsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z7inj_addC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M5phdrsC1@~~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiK47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Heap7HnInst06IMG_LOC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00".
Ltac2 kr_t_Ns0HeapBridgeHn () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib4Heap7HnInst02L0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib7Mh_00849HeapIface;hl_alloc_roC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega7EnvRing5PExpr01I47Corelib4Init5Logic3and00C59OSSVerify5KrLib7Mh_00849HeapIface8hl_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_01439Ns0DrvLib:drv_layout01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify5KrLib2CJ3Ref7Mh_0254?RF_aligned_spec>RALIGNED_STACKC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List9nth_errorC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3mrdC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem:rdn_unfoldC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7wa_succC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init9Datatypes8list_indK47Corelib4Init5Logic3and01C45stdpp9bitvector;definitions6bv_addC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem>store_ok_wviewC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idK46Stdlib9micromega=RingMicromega5Psatz06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib7Mh_0058:Ns0StartupCmain_entry_rdn_dataC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts<D_main_missbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts@range_disjoint_bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs6D_mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts;D_main_missC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHn=rdn_main_dataC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts<D_main_cellsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC59OSSVerify5KrLib7Mh_0058<Ns0MainEntry9missb_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058<Ns0MainEntry;D_main_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058:Ns0StartupCmain_entry_mem_dataC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_wfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cells_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem5wr_atC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHn?bytes_at_of_rdnC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHnAwr_at_of_store_okC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Ref7Mh_0052:F_syscalls5rsegsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib5Lists7ListDef3mapI47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseC49OSSVerify5KrLib5BMode5bm_onC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C59OSSVerify5KrLib7Mh_00849HeapIface7hl_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib4Heap7Mh_02835HnV169HIV0_initC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHnBmain_init_statics0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C69OSSVerify5KrLib4Heap7Mh_02835HnV164HIV0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib4Heap7Mh_02835HnV167HIV0_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpI59OSSVerify5KrLib7Mh_0058:Ns0Startup:main_entry00C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHn=main_hi_heap0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0258:Ns0DrvMainBsrc0_realizes_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Heap7HnInst02K0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Heap7HnInst02B0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib?Ns0HeapBridgeHn=drv_layout_L0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemantics?LinuxProcessSem3Run8sc_allocC69OSSVerify5KrLib4Heap7Mh_02835HnV168HIV0_okRC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I49OSSVerify5KrLib5BMode5BMode00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib4Heap7Mh_02835HnV16<HIV0_mallocNC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition zpair (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).

Lemma map_wz_flat_pairs_zpair : forall es : list (word * word),
  map (Z_to_bv 64) (flat_pairs (map zpair es)) = flat_map (fun e : word * word => [fst e; snd e]) es.
Proof.
  induction es as [|[a b] es IH]; [reflexivity|]. cbn [map flat_pairs zpair flat_map fst snd app].
  rewrite IH. rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma auxv_pairs_words : forall la ph entry uid gid hw r x,
  map (Z_to_bv 64) (flat_pairs (map zpair (removelast (auxv_entries la ph entry uid gid hw r x))) ++ [0; 0])
  = flat_map (fun e : word * word => [fst e; snd e]) (auxv_entries la ph entry uid gid hw r x).
Proof.
  intros. remember (auxv_entries la ph entry uid gid hw r x) as es eqn:Ees.
  assert (E : es = removelast es ++ [(AT_NULL, Z_to_bv 64 0)])
    by (subst es; unfold auxv_entries; destruct (la_rseq la); reflexivity).
  rewrite E at 2. rewrite flat_map_app, map_app, map_wz_flat_pairs_zpair. reflexivity.
Qed.

Lemma auxv_pairs_length : forall la ph entry uid gid hw r x,
  (length (map zpair (removelast (auxv_entries la ph entry uid gid hw r x))) + 1 = auxv_count (la_rseq la))%nat.
Proof. intros. rewrite length_map. unfold auxv_entries, auxv_count. destruct (la_rseq la); reflexivity. Qed.

Lemma auxv_pairs_facts : forall la ph entry uid gid hw r x,
  let L := map zpair (removelast (auxv_entries la ph entry uid gid hw r x)) in
  Forall (fun p => fst p <> 0) L /\ last_assoc 25 L = Some (bv_unsigned r)
  /\ Forall (fun p => fst p = 25 -> snd p = bv_unsigned r) L
  /\ Forall (fun p => 0 <= fst p < 2^64 /\ 0 <= snd p < 2^64) L.
Proof.
  intros. subst L.
  assert (RG : forall w : word, 0 <= bv_unsigned w < 2^64)
    by (intros w; pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; cbn in R; lia).
  unfold auxv_entries; destruct (la_rseq la); cbn [removelast map app]; unfold zpair; cbn [fst snd];
    unfold AT_SYSINFO_EHDR, AT_L1I_CACHESIZE, AT_L1I_CACHEGEOMETRY, AT_L1D_CACHESIZE, AT_L1D_CACHEGEOMETRY,
      AT_L2_CACHESIZE, AT_L2_CACHEGEOMETRY, AT_L3_CACHESIZE, AT_L3_CACHEGEOMETRY, AT_MINSIGSTKSZ, AT_HWCAP,
      AT_PAGESZ, AT_CLKTCK, AT_PHDR, AT_PHENT, AT_PHNUM, AT_BASE, AT_FLAGS, AT_ENTRY, AT_UID, AT_EUID, AT_GID,
      AT_EGID, AT_SECURE, AT_RANDOM, AT_EXECFN, AT_RSEQ_FEATURE_SIZE, AT_RSEQ_ALIGN;
    (split; [repeat (apply Forall_cons; [cbn [fst snd]; rewrite u_small by lia; lia|]); apply Forall_nil|]);
    (split; [reflexivity|]);
    (split; [repeat (apply Forall_cons; [cbn [fst snd]; intros HK; first [reflexivity | rewrite u_small in HK by lia; lia]|]);
             apply Forall_nil|]);
    repeat (apply Forall_cons; [cbn [fst snd]; split; [rewrite u_small by lia; lia| apply RG]|]); apply Forall_nil.
Qed.

Lemma u64s_flat_map_le8 : forall ws, u64s ws = flat_map word_le8 ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [u64s flat_map]. rewrite IH. reflexivity. Qed.

Section FPX_1.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.   (* [comment removed for export] *)
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hfs : sc_fs scfg = true.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma drv_layout_L0 : forall sp, valid_sp sp -> drv_layout (L0 (bv_unsigned sp)) sp.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0HeapBridgeHn ()) ["FPX_1"] "p'0h07__arithh14__ffh28__varmaph35__with44__x1h52Hah64__x2h71ah81Hh93Hsph:1eh;2sph<1xi001cp;1p;2p;3p;4p;6p;?p;7p;8g0000j10Tg000Uj1gTg0013j1aTg001Vj1vTg002Kj2OTg0035j1WTg003ij1[Tg004Ij2NTg004cj2hTg005ij1fTg006Ij2\Tg006gj1cTg007Ej1bTg0080j2VTg008Sj12Tg0098j1`Tg009Zj2_Tg00:<j2^Tg00:hj3TTg00;Bj3]Tg00;aj4uTg00<Sj2HTg00=0j2STg00=Lj2tTg00>Nj1sTg00>lj4rTg00?Jj1<Tg00?hj2=Tg00@Dj2YTg00@gj2KTg00ABj1pTg00BAj1nTg00CGj6mTg00Ccj2lTg00DBj2iTg00D_j1jTg00Ecl?kTg00Ffj4LTg00GQj7PTg00H5j3oTg00HXj7XTg00I<j8eTg00I`j7QTg00JDj2dTf0R0#0#0p=J%00#2#0#2p=?%00#2#2#0p=D%20#0p=4%00#<p=Bg00J^R1/N0p=A%00#0#2#0p=:%20#2p=8%20#2#0#0p=;%00#2p=9%00#0#0#<p=3%00#0#0#0p=5%20#2#2#2p=F1Y10p=1f2R2g00K<R3g00K[R4P4g00L;R5P1f1R6g00L[R7P0CLg00MBR8FPp=6%20#0#0#0p=MAo160p=CP1P6g00MbR9P0CLp=If3R:P3P4P4P5P2P6P3P4P4P5P0P8FPFXp=GP:P3P4P4P5P2P6P0Gep=U1=26/K0p=RP2P3P4P4P5P1P6P9P0CLP8FPp=@f4R8P3P4P4P5P:P3P4P4P5P2P6FXP0FQp=>P8P3P4P4P5P:P2P3P4P4P5P6P0FQFQp=Z1=8:1S26'K/d0p=7P1P6P7P0CLp=qg00NIR7/=0p=Eg00NgR:#0R3#0R9#0R;#JR<#0R=#gR>#a%v01O>6R?#WR@P6g00OL#[g00PK'N%?:#D#?#D#4#B#A%?:#D#:#8#4#4#B#A%4:#;#9#J#:#4#3#A%0=#J#5R=#0RA#0#BRB#A%F:#9#J#5#5#3#A1O>2#WRC/h0g00R4RD#fRE%[DRD1\16%c1RF%b1RGPG%8:#;#D#:#8#3RH#1RI1V1:RJ56GRKPG%8:#;#9#M#;#3RL#1RM%2:RN#4#4RO#0#3RP#1'CRQ,IJCG%`4R4PGPKPG%F:#:#5#5#3RK#1RR,IJCGCU1_G5R5P0P2g00R`RSg00S@RT'N1^02=TSTdA]176CuRTb1b2b3X411HLPRP,S09RH01S6K9RH6[^41P0P2P6O2b0W5X711tC0PEPDP11\12P6%s1RCCrPFPGPGPG%1B=6GJRS%23RU#F#4#5#5#3RV#19@GJPGPG%8:#;#9#?#;#3RW#1=6GJPG1IJICGRIPGPGA6GQJPG%2O#3RO#1,CM,IJCGPGPG%4:#:#8#9#?#8#3RM#1RQ=6GJ%<;R;#1RX,CQ9@GJPGPG%8:#;#9#?#M#3RQ#1RY=6GJRZ1CYX9@GJPGPG%F:#:#4#:#:#BRY#1RX=6GJR[%<9R9#1,CX9@GJ1V13=6GJRXD>D>D>DZD>P4PGPGPS%0N#J#;#5#5#3RN#19@GJPGPGPZ%8:#;#?#D#9#3RZ#19@GJPGPIPGPGA6GRJPG%8:#;#M#5#9#3RR#1,IJCGPGPGP[%F:#:#4#:#9#3R[#19@GJPXD>DZD>D>CUP5PTb1b2b3X41X61PBP0P0PVPWP0P0PHPPP0P01HLOPMP0P01HM;PQP0P01HQ;PYP0P01HY91=60D7D7D7D7D7D7PBP6P6PNPQP6P6PZPWP6P6PHPKP6P6PRPYP6P6P[1=26D7D7D7D7D7[^41^61P01O>8P2P6O3b0W5X71%4:#8#5#F#9#D#B#A%A?PEPDPCPFPG1Y17R1%<=R=#1%<<R<#1'CR?56GPG%<ARA#1,q?CGP5PTb1b2b31H=<R<#E1=<A'KP0b0g00S`R<1=<A5R7e%p@R7#E1=7A'KePEPDPCPF%<:R:#196G1P5PTb1b2b3%E:P0b0%n@#Eeg00U2R:g00UXRTg00V>R53TP:PTP:p-0P0g00VdRTg00WAPTn011000003000000X::g00W]P5P0EmPT1lT0b8W<%<3%0U#B'i#Ed%j@#EeM?kW9W;o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_at_of_rdn : forall segs m (a : Z) (bs : list byte),
  rdn segs m (Z_to_bv 64 a) (length bs) = Some bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at segs m a bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0HeapBridgeHn ()) ["FPX_1"] "p'0h02Hrh12Hbh24__x1h32Hah42Hih56__sat3h61ih72E1h81Hh91ah:6__sat2h;4__x2h<3Hi0h=7__arithh>4__ffh?8__varmaph@5__withA4cstrhB5cstr0hC1xi001xhD2E0hE2bshF3Hb0hG2IHhH1bi011bhI1ehJ1oi021ohK4__p1hL5cstr1hM1mhN1yhO1zhP6__sat1hQ2b0hR1ni031nhS1ri041rhT4segsi051lp%0p&0p;1p;2p;3p;4p;6p;<p;:p;8p;9p;7p;Bg003iR0j1]Tg0000j1HTg000Uj1gTg0013j1bTg00X9R1j1nTg00X[j2STg00YAj23Tg00Yaj2:Tg00?Jj1WTg00DBj2pTg00ZCR2j11Tg00@gk20:Tg00Zcj3ZTg005ij1iTg00[AR3j2@Tg00=0R4j2;Tg004Ij2ETg00[Yj4ITg00\@j1CTg00\ej2wTg00]Mj3vTg00^1j2uTg00>Nj1sTg006Ij2aTg00>lj4`Tg006gj1rTg007Ej1qTg00@Dj2VTg008Sj1oTg0080j2TTg0098j1_Tg00^Rk60?Tg009Zk20>Tg00:<k20=Tg00:hj34j1~Tg00;Bk30<Tg00;ak40;Tg00_6j30Tg00_VR5j1FTg00`5j4\Tg00`fj3JTg00aak308Tg00bDk404Tg00CGj6Kl:yj8xTg00cFj17Tg00d@j6hTg00<SR6j22Tg00d]k101Tg00e>k600Tg00e\j1fTg00f:j4}Tg00f]l<PTg00H5j3QTg00Ffj4YTg00gBj4eTg00gmj1{Tg00?hS00j2MTg00hlj3zTg00Ccj2jTg00iOm905Tg00j1j4kTg00GQk706Tg00I<k807Tg00jLj3lTg00k1l<mTg00kVlBtTf5R7f4R8f3R9f2R:f1R;C\f0R<34p=6g00NIR=/M<p=513;<#1p=>12:;/M<p=913;<,@:p=<f7R>f6R?1289#77J7AZ:;<34p=A12;<#7p>09AJ9:;=48<p=Bg00J^R@/E<p=8g00l<RAP@P3P2P4g00l[RBP9P:P;g00m=RCP=P<M<Pp=|P@P;g00L[P<CYp=NP;g00K<RDg00K[REPEg00L;RFP<g00MBK06p=?P@P;g00MbP<CYp=^P9PDPEPEPFP:P;P<L07p=L1:;<949:p=GP7P8Al9:;P<C\p=[A0:;<,:9p==%7<9J:;p>03%7;=l:<p=DAJ789AZ:;<54?p=UPAPAP@P@P5P2P2P9g00m\P:P;P<M<mp=OPAP@P@P@P2P2P7P8P9P:P;P<M<mp=dP@P@P@P@P@P@P6P<P;P:P6P9P8P7P?P>f8R6f9R5MBtp=cPAP@P3P2P4PBP7P8P9P:P;P<M<Pp=RA0:;<,39p=X%1<,2;p>02g00OL#]g00NgRB#HR4#H#HR2#H#H#HR3#gRG#bRH%g2#bR2#nRI[%]2RJ%nJRKP9P:1SG;132<1:J<RLE6%5:1>2:%W4RM%W3R3'pRN599%581>29RO=98NRPA<<28PIP6P>P?%1;RQP2P7P;GA[^6ARR+0:P;PPPRP<P2PKP6P>1SG<RR132;RP1:J;RSE6%5;RTA9:ONROA<<27RUPIf=RVf<RW2097QRXAZ2?;RYDB[^6A]1]3]0^9@XEJPKP>P?PR%i2RZ,32R[1:JZE6%1[R\=9:N1@<[1@;C1;Q=R]P;PQ%8QS011E@=C|P<CIP]%C:S02%1:R]#5S03%C[%5\1wM3R\1;=MR[%531;=N[R^[R_%5MR`g00WARaAvM3;UW3R3%5N\a^3`R`P;g00U21u=M'EP[eO1R[P^p-0Rbg00R4Rc#iRd%]cRcP@%s@S04P;1a@;S05C`%r@Re%q@Rf1V@=Rg%oB,T@Rh'N,?f%_ERiPf1^hg,?fPiPfPDPEPEPFP9J0?CLCL20>fFRFP<P:g00R`REg00S@RD'E20=<:=4EDdB0<@=;H0;RDb>b?b@X2@WK%5<S061;;=P9[[^2@^KbP<PIfCREfBRhPW%16RjP2PZP6GAPjP7P?O4b=b:bPb:bBbAb<W4X6AW1X3TW0X9@PKP5P6PRPPPSE6PIf>RZPVPXPYDB\U^6A^1O^3T]0^9@PKf:RkP5PRA029:Rl,321:JlE6A0278,>2=9:NA02>?9<<2PKf?RlPZ1SG7R7132>#FRmC\PKP<PJA0256CGXJKP8P1P2PKAJlZ7P1PJPKf@RnPlPG1SG?%WBRog00W]S07608GRp1326E[PJP2P;P<C=Rq%_JRrn10110000021010400Prn10110000021010100RsPlPZP7PmH04EKPKPsPJA026>CGB03nl?PI1EI<PIfARsPn%7>P<DBP1P2PIPEPh%75P<DBP1P2PKP;P1PJPKfERmfDR7PGf;Rt#7Pp132VRuE[RvPqPrn10110000021010400Prn10110000021010100PJP2PVPWC=S0854KPIPmP7Pt%1>P2A02ZVRqP>GAS09]0]DP;PIP7PE%7k1:2<DBPKP1PJPKPvPJP2P:P<C=Prn10110000021010400PJPqCGfFRqPmPG%7WPp132ZE[PK1EK<PKfGRvPqADGVp132lP<E6P1PJPKfIRwfHRxADGlp132sRyP<E6P1PJPKP;PJP2P>P<C=Prn10110000021010400PJP2PEPhC=S0:54KPIfKRzfJR{Ps%1VP2A027ER|PVGAR}]0]7P;PKP{PwADGnp132hPLE6PKPJP2P>P;C=PJP|CGPKPJP1PJPJP<P0P2PJP<P8P<n10110500020020101105P9n10110200021010500XIKPJP2P6P:C=PJP2PmP7C=P<EhA4J:7PKP2P1PJP2P<P0P2P2P<PtP;n10110500020020101105Pkn10110200021010500XIKPJP2P5P9C=PJP2PqPmC=P;EhA425qA42kvP2PtA02<x,>2=9qNA02;w9<E2A4J6{PIfSR0fRR|Pw%1mP2A029zPmGA[]4]1XH2A02tv,>2=9mNA02Wx9<h2A4J>wPJP6PKfTRLP0PRPPPSE6PIfYRSfXR~PXPYDB\U^6A^1O^3T]0^9@PKPLP0ADG{pPP1:JkE6A02s:,>2=9zNA02h99<x2PIfWRzfVRPfMRL%1wP2A02E8PwGA]4]1]7]GXEJPKP0P|PR1325RR1:J5R5E61>2t=9:N1@<uPIP~PzPXP2PZP;FU[^6A]1^3T]0^9@PKP0P|ADGwpPRP5E6A02nk,>2=9{NA02st9<v2PAA02EVRV9<<2PIP~PzfNPQP2A027ZR5P;GA]4PxA02hW9<C2P@PLPIP~Pz%7<RR1:27DBXO@Ph12L=&01LJ00PIPzPPPL%1CP2PVPCGAeW4%F<?<25fOR5/2o/2QRC%F;RV#1RL,25R=54@R|12QoR0,25RX94@CP@P@%~@RuP<XC@ROPuA4@;<#fXN@XC@PCPC%8CP=PXPOPOPOP@P@g00n@12;<C}#8XM@XR@S0;P5P5%85PLP0POPO%1<#8XCAS0<PVP012<oRLXC@R5P;PQQ01CORXEdM:cM<PA02mlS01,32Rm,@V%1mRl,;0R0PVP5PQO1PXPmPl%8lERP<CIP0Q02Q03P2P2PvPsCXR0#C%10#5P\P_P3P`P[P^PdPcP@1a@:P;Q04C`R0PeP@1T@BRB1V@oRl5Q@Rm1T@4R45Q@RXg00ndAQ@4lRl9Q@BRQCY,?fPFPDb>b?b@X2@X;@12L;12;oRC,2<Ru54@^2@^;@P<PjPPO2b=b5b:b5bBbAb<CeP|P@fPR|/2oRP/2]PIf[RjfZRUPRP2PsP9FUXO@P>PPPHADG|pPKPjPUP<Py1:JsE6XHHP?%7PRP%{|EKPKPUPSPP132nRP1:JnE6P<b7%F:RUP2P2PqPnCXRq'@12]oRH%1qRj';RRPUP5P]O1S04P5P:P]%8]S03COS02PqPj%8jERP;CIS0=PRfQRj%FyS0>#1S0?'2S0@/MN%1yRq/2o=9jNRYP@P@Q00POQ001M;<#fXN@XC@Q0@POP5PqO1S0@O1S00,2jPOPOPOQ0;PjPj%8jQ0?Q00POPOQ0<Q0>Q0@P5PyPq%8qCOEdM:cPNPN%8NA4@NNeM<PP?CIR?PY%C8Rq%18#5RyP2P2PwPECXRO#CS0@%1O#5RO1327R7#CRj%17#5R7P\P_P3P`P[P^PdPcQ05PePf1NgB,?fPi1Ngm,?fCLPFPDb>b?b@X2@Q06%5C[^2@P<PSPzO2b=b5b:b5bLbBbAbFb<Q0=PRP?PYPqPyQ0@POPjP7P\P_P3P`P[P^PdPcP0PePf1V@M=z@GRM,NQ,?fPi1NXM,?fCLPFPDb>b?b@X2@X;@1MuNA9C:N[^2@^;@P<1>2wPSP>O3b=b5b:b5bLbBbAbFb<P:1@:P%1PRN,;]P:P]Q03PPPN%8NR]ER%FPRu,@U12No,;HRHPUQ04Q02PuP5PNO1P5PPPNP]COERP;CIPHP?PYPqPy132ERE#C%1E#5P\P_P3P`P[P^PdPcP0PePf1^ml,?fPi1^B4,?fCLPFPDb>b?b@X2@X;@1;LC1;;:[^2@^;@P<1>2x%1kP>O3b=b5b:b5bBbAbFb<CeO6202|UP<EKb8PIPSP~%7=P2Q01PVFUeW4X6AP<O1n0110300020011103P<O1W4W1W7WGP{P<PwP>P:P;M:yW8W4W1PxP<PhPnGxW8P<O1b8P<O1b8W0W7XSJP<O1PKPxPvADGZpPPPrE6PKPrPJA02hsCGPKPrP1PJPbP<g00VdRbPan10110200021000000XIKRaQ07Q0:P<EKPb1j}<b8W0W7n10110200021110501P<P:O2b7bJW0WDXQ2P<O1PIPhPs%76%_2DBPKPrPJA02WtCGPKPrPaQ07Q08P<EKPbQ09/j<b8W0WDn10110201021110100P<P:O2bDbJb0W4X6AW1X3TW0X9@WGXEJXH2P9P8P:P;P<N905CkCkW1W3W0WEX9@WMWTo"). Qed.

Lemma wr_at_of_store_ok : forall segs m (a : Z) (n : nat),
  store_ok segs m (Z_to_bv 64 a) n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> wr_at segs m a (Z.of_nat n).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0HeapBridgeHn ()) ["FPX_1"] "h04__x1h16__sat1h24__p1h34__x2h44__x3h52Hah61Wh77__arithh84__ffh98__varmaph:5__with;4cstrh<4__p2h=6__sat0h>6__sat2h?1ih@1xhA1zhB2H0hC2HbhD2HihE2HshF1ahG1mhH1nhI4segshJ2z0p;1p;2p;4p;3p;7p;6p;<p;8g003ij1XTg0000j19Tg000Uj1UTg0013j1PTg00X9j1yTg00X[j2KTg00oKj4jTg00:hj30Tg00ZCR0j11Tg00<Sj26Tg00?Jj1OTg00DBj2ZTg00?hj2>Tg00=0R1j22Tg00@gj25Tg00cFj1=Tg010Kj3;Tg0098j1TTg011Hj1<Tg011aR2j1ITg00[AR3j2fTg012Aj2DTg004Ij2FTg00\@j1HTg012^j2_Tg00JDj2QTg00\ej2^Tg00]Mj3]Tg00^1j2\Tg00_Vj1@Tg013@j2?Tg013ij2LTg005ij1[Tg00_6j3GTg006Ij2JTg00>Nj1YTg00>lj4NTg006gj1xTg007Ej1wTg0080j2ETg00Ffj4CTg00@Dj2WTg00I`j7sTg009Zj2rTg00:<j2qTg00;Bj3pTg00;aj4oTg00gBj4nTg014Uj7iTg002Kj2STg008Sj1hTg00H5j3gTg00hlj3kTg015[j2lTg00CGj6VTg016Zj2mTg00j1j4RTg00k1l<eTg00f]l<dTg0178j3cTg00^Rj6bTg00GQj7tTg00HXj7uTg00I<j8vTg00NIR4f0R5'>p=3g00J^R6g00l<R7P6P6P2f4R2P0f3R8g017af2R9f1R:P5M<ep=aP7P6P3P0P1g00l[f5R1P2P8P9P:P5M<dp=`Ac6:5p=7P:g00K<R0g00K[R3P3g00L;R;P5Ebp=MP:P0P3P3P;P5g00MBFtp=4P9P0P3P3P;P:P5Fup=:P6P:g00L[P5CCp=AP6P:g00MbP5CCp=BP8P0P3P3P;P9P:P5Gvp=8g00OL#Xg00NgR<#9R=#9R>#9R?#9#9#9R@#URA#P%U?#PR?#yRB[g00R`RCP8P91KA:P5Cjg00S@RD30%39RE%19,68%O=RF%O@R@'ZRG'>%32%18,62/>GRH%35RI%12,25'5RJf8RKf7RLf6RM/6:#=3;%T?R?50B#<[^?6RN'5P:PHPNP5PKPL1KAMRNP1%I:RHP21fH11D4:RO%11RP'2PHPOP5X@61D45X@6P:P:1F6:DaP1PP1F6PE`%H1%3P1_4912491D49RP=069'51>94A06P4'5'Q1D48P61^F@RP124FRO%3@124G[RQ[RR%3FRSg00WARTA]F@:UW5R@%3G\T^5SRSP:g00U21\4F'FPOeO1ROPQp-0RTg00R4RUg00m=RV#@RW#@RX#@RY,?6RZ1?6XRX1?6W1?6VRV'7RW'7'7g018NR['L17ZW/L[%[URW5GU3G%XUR\P6P61J68R]P9%Y6R^CNP:P^CN%x6R^%w6R_P_P0P3P3P;1M_1P61E6<R0g00ndR`1E6>R>CC,4_5:_1M_MP6P0P`1W64R`CC,4_5:_Fs%T3R3P_1A`>,4_1E6=R=,B>,4_5:_P31B0=,4_C8C81r_;R;P5P91FCD1q59=0CDdAp64:CoRDb8b9b:X06X36X46X2TW<A0659,58A0654,52'Q%38RC1289'51298[[^06^36^46^2T^<TP51>K4124KPKf<R4#1R>P2P1PLO7b7b>b1b>bJbBb;CnFi1SAN%1H'6#=9;KL=0B?#<P61KAL,SAf:RHf9RN%I8#1R1,65#=3;=0B?#<XA6P5PL%HM%1M#3PPPRP@PSPOPQ%@Y,?617XV,7Z'7/L[=GUWP\P61J69P:P]CNP^P_%h<,E6R<,A`,4_1B<=,4_5:_P3P_Ag60=1W6F=k6ARA'A,4_P3P_1A`0,4_R`P31B0A,4_9:_`C8C8C8P;PDb8b9b:X06X36X46129:,5E16:9/>G128G,5C\E[[^06^36^46P5PLf;RE#1P4PMPKPNO6b7b1b=b1b;,lLEV%I9#1,6L#=9;NK=0B?#<P6P116N5#=9;EH=0B?#<XA6P5P8%HL%1L#3PPPRP@PSPOPQPWP\1J6:P^P_1M_89:_`P3P`C8P;PDb8b9b:X06X2T15I:%3:[^06^2TP512K>PKPLO3b7b1b=b1b;,m8EV16K8#=9;HN=0B?#<P5b6b6b6XDJX?6CRCRWCW5WEXH7XF6WGWIo"). Qed.

Lemma bytes_at_app2 : forall segs m a bs1 bs2,
  bytes_at segs m a bs1 -> bytes_at segs m (a + Z.of_nat (length bs1)) bs2 -> bytes_at segs m a (bs1 ++ bs2).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0HeapBridgeHn ()) ["FPX_1"] "h01ah13bs1h23bs2h31mh44segsh52H1p;1p;4p;2p;3p;5g003ij19Tg0000j11Tg000Uj17Tg0013j18Tg00X9j1<Tg019:j40Tg00YAj25Tg00ZCj13Tg00<Sj22Tg01::j34Tg00@gR0j26Tg01:Wj5;Tg00j1j4:Tg00OL#9R1g00Ng#1#1#1R2#1#1#1#7#8%72#8R2#<[R3g00J^R4%92R5f4R6f3R7f2R8f1R9C0R:f5R;P61528#3,27P9C0R<P0P6P7P8f0R09429C0P;P6P7P8C0/6<R<[P6P71529#3,28P0C0,6:P;P6P7A4289C0[R:f6R=P;P6A4278C0\<P6P7P8P9P0D;P0n2001000000120000000X25X15X04X33X41P:^25^15^04^33^41P0f7R0P=P;P6P7P0P=P;P6C0P0P=1526#3,2;P7C0P8P9C:O6b5UUX25W1W0W3W4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MainEntry.
  Context {RE : RunEnv}. Context {RO : ReaderOn}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Hypothesis ME : main_entry inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Let RND : bv 128 := ed_random rdraw.

  Let Hlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
  Let Hhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  Lemma rdn_main_data : forall (a : Z) (n : nat), 0 <= a -> a + Z.of_nat n <= 0xfa000 ->
    rdn RSEGS mem0 (Z_to_bv 64 a) n = rdn RSEGS (D_main inp sp0 rdraw RND tid) (Z_to_bv 64 a) n.
Proof.
    intros a n Ha Hn. apply (main_entry_rdn_data inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME).
    rewrite u_small by lia. unfold stack_max_size. lia.
Qed.

  (* [comment removed for export] *)
  Lemma rdn_main_img : forall (a : Z) (n : nat), D_main_missb a n = true -> a + Z.of_nat n <= 0xfa000 ->
    rdn RSEGS mem0 (Z_to_bv 64 a) n = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof.
    intros a n Hb Hn.
    assert (Ha : 0 <= a).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
    rewrite rdn_main_data by lia. apply (D_main_miss inp sp0 rdraw tid). exact Hb.
Qed.

  Lemma mem_main_none : forall (lo hi : Z) (x : word), D_main_missb lo (Z.to_nat (hi - lo)) = true -> lo <= hi <= 0xfa000 ->
    lo <= bv_unsigned x < hi -> mem0 x = None.
Proof.
    intros lo hi x Hb Hhi' Hx.
    assert (Hlo0 : 0 <= lo).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
    rewrite <- (Z_to_bv_bv_unsigned 64 x).
    rewrite (main_entry_mem_data inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    destruct (main_entry_inp inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) as (Eav & _).
    apply (D_main_none inp sp0 rdraw RND tid (bv_unsigned x) ltac:(rewrite Eav; exact Hva) Hlo Hhi).
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
Qed.

  (* [comment removed for export] *)
  Lemma store_ok_data : forall (a : Z) (n : nat), 0xc6000 <= a -> a + Z.of_nat n <= 0xfa000 ->
    store_ok RSEGS mem0 (Z_to_bv 64 a) n = true.
Proof.
ltac2:(KReplay.run1 (kr_tL_Ns0HeapBridgeHn ()) ["FPX_1"; "MainEntry"] "h06__sat2h12Hah24__x1h37__arithh44__ffh56__sat1h66__sat4h78__varmaph85__with94__x2h:4cstrh;6__sat3h<1zh=2Hnh>1ah?1np;1p;2p;5p;3p;4p;7p;6p;>p;8g0000j10Tg000Uj18Tg0013j2:Tg001Oj11Tg0024j2;Tg002Wj1XTg003:j1UTg003ej2>Tg004Hj5kTg004lj1hTg005Jj2JTg005gj2^Tg006Hj2=Tg006bj3ITg007Ej3ZTg007hj2HTg008Pj3GTg0094j2FTg009Zj1WTg00:=j2VTg00:gj22Tg00;Cj17Tg00;cj2<Tg00<@j1DTg00<ej1ATg00=Dj2BTg00=mj3CTg00>Vj2RTg00?Bj1QTg00?bj3OTg00@Bj1PTg00@bj2ETg00A@j1NTg00A^j4?Tg00B<j1TTg00BZj1jTg00C<j4MTg00Cgj7iTg00DKj2gTg00Dmj2eTg00EYj3KTg00F3j3cTg00FRj4bTg00GDj2]Tg00G_j2_Tg00H^j1@Tg00I@j1\Tg00Ibj1`Tg00JDj1aTg00Jaj1[Tg00K@j6LTg00K^l>dTg00Lbj7YTg00MFj8fTf0R0#0#0#0#0p=4g00MjR1/20p=5%00#0p=Sg00NHR2f1R3g00NfP0CMp=6P3g00OMR4g00OlR5P5g00PLR6P0g00PlFYp=3f3R7P4P5P5P6f2R8P3P0Gfp=9g00QLR9#0R:#0R;#4g00R1%8:R<,:1p-0R=%5<P=%1:#1#0#8P2%19#1#1#1#0#1#0#4#4#4#8R>,;2%X2R?%U2R@%19#0#S#1#1#0#4#4#4#8RA,;21>29R9'6'3P@P4P5P5P6DkRB1>2;P?f6R;#hg00RVf7RC#8P2f5RD#5REP=1J<;P2g00S41^1<'=f9RFePF1>2:9I29/6C,3@PBf4RB#5R:P=1J<DP21:1BP=PEP=1;2<=Z2FP?1:17P=P:P=f@R:,H<fBR?f;REP;[RG[PGP=fCRGg00SZRHfDRI=G<3UW1PC\H^1Gf8RJ\HRK^1IP=f?RL,H<fFPC\ERM[PMP=fGRMAG<G3VHW1PK^1MfHRKPF\H]1P=fJPC[P=fKPB[P=1FM0%WM1VK0P2g00T612A7%73,<B/2>%D8%78#5f<RKPCPEf:RMP?PMfAR=P:P3fMRHO1PGPBfNR<O1P:g00TURNg00UARO#A#ARP#A,B21B2P1B2O5C25C2g00U`'R%QNRO3O%PNRNP2P21E28RPP8%N2RQC?P3PQC?%T2RRP@1;21RSfXRT'6,3@%j5RUP@AI29TfZ'6,3@PUP@fYRTPUP@P4P5P5P616S9,3@P2P9g00VLPHCM,3@FiC9C9C91g@6R6P0P8g00W3R9g00WSRS'=1e08=K9SdAc213CbR1b4b7b8X22X92%531<38/2>RS12A8%57fQ,:7'][[[^22^92P0%7Mf=RMPCPJPFO5b3b6b0b5b0b;b6b:,_DAK27Dg00X3p,4mem01FHAPDg00Y\#@#@#@#\#`#a#[P7PAP>1=2A1=2>%D7RD%77#5R7PMPJPKPEPGPEP?P=P3P<O1PIPBfOO1P=POPNPQPRfLRI,6T,3@P6P1b4b7b812>HP0b3b6b0b5b0b;b6b:g00Z>P2P;12A0RHX<2PDP7P=PFP:PLP3PIO1RIP?POPN1E23PRP@fVRTPUPTC9P6P1b4b7b8X2212A3\H^22P0PEPCO2b3b0b5b0b:PBP0ELP2P;%7B,<0/2>X<2PDP7P=PFP:PLPIP?POPNP2PPP3PQC?PRP@fPR@PUP@C9P6P1b4b7b8X22X921<03/2>PS[^22^92P0%7JPEP;O3b3b0b5b0b:PBP0ELM>daW=W1W?aaX>2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.
  Lemma store_ok_relro : forall (a : Z) (n : nat), 0xbf000 <= a -> a + Z.of_nat n <= 0xc6000 ->
    store_ok RSEGS mem0 (Z_to_bv 64 a) n = true.
Proof.
ltac2:(KReplay.run1 (kr_tL_Ns0HeapBridgeHn ()) ["FPX_1"; "MainEntry"] "h06__sat2h12Hah24__x1h37__arithh44__ffh56__sat1h66__sat4h78__varmaph85__with94__x2h:4cstrh;6__sat3h<1zh=2Hnh>1ah?1np;1p;2p;5p;3p;4p;7p;6p;>p;8g0000j10Tg000Uj18Tg0013j2:Tg001Oj12Tg0024j2;Tg002Wj1UTg003:j1STg003ej2>Tg004Hj5mTg004lj1jTg005Jj2JTg005gj2]Tg006Hj2<Tg006bj3ITg007Ej3XTg009Zj1WTg0094j2HTg007hj2GTg008Pj3FTg00:=j2VTg00:gj21Tg00;Cj17Tg00;cj2=Tg00<@j1DTg00<ej1ATg00=Dj2BTg00=mj3CTg00>Vj2RTg00?Bj1QTg00?bj3OTg00@Bj1PTg00@bj2ETg00A@j1NTg00A^j4?Tg00B<j1TTg00BZj1lTg00C<j4MTg00Cgj7kTg00DKj2iTg00Dmj2eTg00EYj3@Tg00F3j3`Tg00FRj4_Tg00GDj2\Tg00G_j2^Tg00[Aj1LTg00[_j1[Tg00\=j1aTg00\[j1bTg00]9j1ZTg00Jaj1cTg00]Vj3dTg00K@j6KTg00K^l>fTg00Lbj7gTg00MFj8hTf0R0#0#0#0#0p=4g00MjR1/10p=3%00#0p=Yg00NHR2f1R3g00NfP0CMp=6P3g00OMR4g00OlR5P5g00PLR6P0g00PlFgp=5f3R7P4P5P5P6f2R8P3P0Ghp=9g00QLR9#0R:#0R;#4g00R1%8:R<,:1p-0R=%3<P=%2:#2R>#0#8P2%29#0#Y#2#2#0#4#4#4#8R?,;2%U2R@%S2RA%2>#2#2#2#4#4#4#8R>,;21>29R9'6'5PAP4P5P5P6DmRB1>2;P@f6R;#jg00RVf7RC#8P2f5RD#3REP=1J<;P2g00S41]1<'<f9RFePF1>2:9I29/6C,5APBf4RB#3P=1J<DP21:1BP=PEP=1;2<=X2FP@f:R@#Wp-1f;RE/H>P01:1DP=%3;P=fBR:,G<fDRGf=RHf8RI[RJ[PJP=fERJg00SZRKfFRL=F<3UW1PF\KRM^1JP@\K^1LP=fARL,G<fHPC\HRN[PNP=fIRNAF<J3VKW1PI\K^1NfJRKPM]1P=fLPC[P=fMPB[P=1HN0f>1VK0P2g00T611>7%73,=B/1?%D8%78#3f<RKPCPEP@P:P@PLf@RNP3fOR=O1fCRMPBfPRJO1PNg00TUR<g00UARO#A#ARP#A,B21B2P1B2O5C25C2g00U`'R%Q<RO3O%P<R<P2P21E28RPP8%N2RQC?P3PQC?%T2RRPA1;21RSfZRT'6,5A%l5RUPAAI29Tf\'6,5APUPAf[RTPUPAP4P5P5P616S9,5AP2P9g00VLP=CM,5AFkC9C9C91iA6R6P0P8g00W3R9g00WSRS'<R51e08=@9SdA`213C_R1b4b7b8X22X92%331=38/1?R411>8%37fS,:7'\[[[^22^92P0%7@PHPCPIPFO5b3b6b0b5b0b;b6b:,^DA@27Dg00X3R@p,4mem0PMPDg00^T#L#[#a#b#L#Z#cRDP7P>P?1<2>1<2?%D7R8%77#3R7PHPIPKPEPMPEP:PLP3PJO1PGPBfQO1PLPOP<PQPRfNRG,6T,5AP6P1b4b7b811?=P0b3b6b0b5b0b;b6b:P5Ad@MD=@9SdP2P;11>0RSX<2P8P7PLPFPNf?R9P3PGO1RGP:POP<1E23PRPAfXRDPUPDC9P6P1b4b7b8X2211>3\S^22P0PEPCO2b3b0b5b0b:PBP0EKP2P;%7B,=0/1?X<2P8P7PLPFPNP9PGP:POP<P2PPP3PQC?PRPAfRRAPUPAC9P6P1b4b7b8X22X921=03/1?P4[^22^92P0%7IPEP;O3b3b0b5b0b:PBP0EKM>faW=W1W?aaX>2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_of_rdn : forall (A : Z) cs,
    cells_wf cs ->
    rdn RSEGS mem0 (Z_to_bv 64 A) (length (cells_bytes cs)) = Some (cells_bytes cs) ->
    store_ok RSEGS mem0 (Z_to_bv 64 A) (cells_size cs) = true ->
    0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
    rw_cells rsegs mem0 A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0HeapBridgeHn ()) ["FPX_1"; "MainEntry"] "h01Ah12HAh22HBh32HLh42Hrh52Hsh63Hwfh72csh81np;1p;2p;4p;3p;6p;7g003ij1=Tg01NIj1<Tg0000j10Tg000Uj17Tg0013j1JTg00X9j1HTg00X[j2:Tg01OKj13Tg00YAj22Tg00`5j4?Tg00Yaj2>Tg00:hj35Tg01PPj11Tg00oKj4ITg00?hj26Tg00ZCj14Tg00<Sj2;Tg00?Jj19Tg00DBj2GTg01QTj2FTg01R`j4ETg01Sbj4CTg019:j4BTg00e>j6ATg01T_j7DTg00j1j48Tg01Ucj7@Tg00J^g01Vi#=f0R0#<g00Ng#0R1#0#0R2#7#JR3#=R4#Hg00PKR5p,4mem0R6%02#0#0R2#7R7f2R8':f1R9#3R:,23C?1>4:35g00R`P5P6f3R5,:7%18CIg00S@35g00NIf4R7'6f5R:%17#4';%91%92'GR2'61F:7g00l<R1%3:,23%1:35g01WiR4P6f7R;f6R<CEP4P6P;%1<R=#4CC%<<P4P6P;%3<R<CBP:P4P6P;P<P7P8P1P=f8%40';/62X81P9123<P0EAFDC8P4P6P;P=P5P8P9F@C8b3W2W1W5W4W6W7W0o"). Qed.

  (* [comment removed for export] *)
  Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0HeapBridgeHn ()) ["FPX_1"; "MainEntry"] "p'0h01Hh12H0h22b2h31eh42b1h52l1h62l2h71li001lh82l0h91nh:2H1h;2H2h<2IHi011ai021bi038bv_is_wfi04;bv_unsignedi053mapi061zp;1p;3p;2p;6p;8p;5p;4g0000j16Tg000Uj1DTg0013R0j13Tg003iR1j17Tg002Kj1Cj22Tg00:hj30Tg005ij19Tg004Ij28Tg00_6j34j2<j1BTg00CGj6:Tg00Ccj2>Tg00d@j6=Tg01Xmj3ATg01YQj8;Tg00iOj5?Tg01Ynj4@Tf2R2g00J^R3f1R4f0R5C@p=1A4345p=5g00Ng#6#6#6#DR6#3R7#7R8P7%73R9%C6R:=174R;A17:5R<30A0824[^68R=X58P1P7%97R>917:R?=09<A08>4[P5A09??188>W0A4745917:R@909?P9%93RAP1P3p-0RBP5g00WARCg00VdRDn10110000020020000000X39g00W]RE1262/5;RFP5E:PDf3RG=472RH908>/>5b1W0X68X27P4P5O2n10110000020020102100X88P1P7f4RI=47G917:=09<f5R<=47IRJ=084[P5A17:H=09?P9126IR?A17:G'5P1P3PBP5PDPCn10110000020020000000X39PEPAP5E:PDA08J>/>5b1W0f7RJf6R>547917:=09@P9P9P1P3P9P5P9^78P1P7P9P5PA1264PGP5O1'5n10110000020020101100X78p?1000105f8RAO1P5n10110000020020106100X39126AA17:JR@'5PFP5E=A09@;P9P3P1P3P3P5P0P6P3f:R0P4n101102000120104103P4n10110000020020106100X39f9,26R1A17:A'5126GRAA17:2'5P4E=A031A1260=03?A17:0A17:I509P8P8f<R9,<71<7>f;P<P7P8\8R:%B7R?P?P9P>P:\7/8?g01ZJR?%35R:%34R>g00@g%32?04512G212G4503R9[12241225503%3G?024[R3%3I?0G2\9AA245P5n2001000000120000000W2W4W9P3^2>^4:^9?P5P6f=PJP2O4b0G;P0P<P5O2G;W;W:P5O1b1P5O1b1W0X68X27P4P5O2n10110000020021102100X88X<=X58X47P5D?W5o"). Qed.

  (* [comment removed for export] *)
  Ltac img_read a n :=
    rewrite (rdn_main_img a n) by (first [vm_compute; reflexivity | lia]);
    lazymatch goal with |- ?l = Some _ => let v := eval vm_compute in l in change l with v end;
    f_equal; apply bytes_eq_of_unsigned; vm_compute; reflexivity.

  Lemma main_init_statics0 : init_statics0 (bv_unsigned sp0) mem0.
Proof.
    pose proof (u64_range tid) as Ht.
    destruct (auxvp_u sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME) as [AV1 AV2].
    destruct (rnd_u sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME) as (RN1 & RN2 & RN3 & RN4).
    pose proof (u64_range (auxvp sp0 a0s path envv)) as AVR. pose proof (u64_range (rnd sp0 a0s path envv inp)) as RNR.
    pose proof (u64_range uid) as UR. pose proof (u64_range hw) as HWR. pose proof (u64_range (canary_w RND)) as CR.
    unfold init_statics0.
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - intros a Ha. lazymatch type of Ha with ?lo <= _ < ?hi =>
        apply (mem_main_none lo hi a); [vm_compute; reflexivity | lia | exact Ha] end.
    - intros a Ha. apply (mem_main_none RVMLOCKC (RVMLOCKC + 4) a); [vm_compute; reflexivity | lia | exact Ha].
    - apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
      cbn [length cells_bytes cbytes app].
      lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) ?n = _ => img_read a n end.
    - apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
      cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app].
      rewrite rdn_main_data by (cbn; lia).
      destruct (main_entry_inp inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) as (Eav & _).
      apply (D_main_pagesize inp sp0 rdraw tid ltac:(rewrite Eav; exact Hva)).
    - apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_relro; cbn; lia | lia | cbn; lia].
      cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app].
      lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) ?n = _ => img_read a n end.
    - exists (bv_unsigned (canary_w RND)). split; [lia|].
      apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
      cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app]. rewrite Z_to_bv_bv_unsigned.
      first [ exact (main_entry_guard sp0 [a0s; path] envv uid hw rdraw tid Hva Hlo regs0 mem0 inp mbase entry ME RSEGS)
            | exact (main_entry_guard sp0 [a0s; path] envv uid hw rdraw tid Hva Hlo Hhi regs0 mem0 inp mbase entry ME RSEGS)
            | exact (main_entry_guard sp0 [a0s; path] envv uid hw rdraw tid Hva regs0 mem0 inp mbase entry ME RSEGS)
            | exact (main_entry_guard sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 inp mbase entry ME RSEGS) ].
    - set (sec := firstn 8 (skipn 8 (at_random_bytes RND))).
      assert (Lsec : length sec = 8%nat) by (subst sec; rewrite length_firstn, length_skipn, length_at_random_bytes; reflexivity).
      pose proof (bytes_le_to_Z_bound sec) as SB. rewrite Lsec in SB.
      destruct (main_entry_inp inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) as (Eav & Eev & _ & _ & Hvl & brk & Hlau).
      assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
      assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
      pose proof (proj1 Hvsp) as SPLO. pose proof (proj1 (proj2 Hvsp)) as SPHI.
      set (rw := at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)).
      set (xw := at_execfn_ptr (ed_top rdraw) (in_execfn inp)).
      assert (Erw : rnd sp0 a0s path envv inp = rw) by (unfold rnd, rw; rewrite Eav, Eev; reflexivity).
      rewrite Erw in RN1, RN2, RN3, RN4, RNR.
      set (ES := auxv_entries (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp) rw xw).
      pose proof (auxv_pairs_length (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp) rw xw) as PL.
      destruct (auxv_pairs_facts (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp) rw xw)
        as (NZ & LA & R25 & RNG).
      fold ES in PL, NZ, LA, R25, RNG.
      assert (AOB : (auxv_off (in_argv inp) (in_envp inp) + auxv_size (kb_rseq (in_kernel inp)) + 16
                     <= length (entry_stack_image inp mbase RPH entry sp0 rdraw))%nat)
        by (eapply auxv_off_bound; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact RSEGS | exact Sv48 | eassumption | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
      pose proof (entry_stack_image_no_wrap Sv48 inp mbase RPH entry sp0 brk rdraw Hlau) as NW.
      assert (AVU : bv_unsigned (auxvp sp0 a0s path envv) = bv_unsigned sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp)))
        by (rewrite AV1, Eav, Eev; reflexivity).
      assert (ASZ : auxv_size (kb_rseq (in_kernel inp)) = (16 * auxv_count (kb_rseq (in_kernel inp)))%nat) by reflexivity.
      change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)) in PL.
      exists (bv_unsigned (auxvp sp0 a0s path envv)), (map zpair (removelast ES)), (bv_unsigned rw), (bytes_le_to_Z sec).
      split; [|split; [|split; [|split; [|exact (conj NZ (conj LA (conj R25 RNG)))]]]].
      + apply rw_cells_of_rdn; [cbn; tauto | | unfold RAUXV_CELL; apply store_ok_data; cbn; lia | unfold RAUXV_CELL; lia | unfold RAUXV_CELL; cbn; lia].
        unfold RAUXV_CELL. cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app].
        rewrite rdn_main_data by (cbn; lia). rewrite Z_to_bv_bv_unsigned. eapply (D_main_auxvp sp0 a0s path envv uid hw rdraw tid regs0 mem0); eassumption.
      + subst ES. rewrite auxv_pairs_words, u64s_flat_map_le8.
        change (flat_map (fun e : word * word => [fst e; snd e])
                  (auxv_entries (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp) rw xw))
          with (auxv_words (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp) rw xw).
        rewrite <- auxv_bytes_words.
        rewrite AVU.
        apply bytes_at_of_rdn;
          [| lia | rewrite length_auxv_bytes; change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)); lia].
        rewrite length_auxv_bytes. change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)).
        rewrite <- word_add_nat_Z2bv.
        rewrite (main_entry_rdn_above inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME);
          [ | rewrite word_add_nat_Z2bv, u_small by lia; lia | rewrite word_add_nat_Z2bv, u_small by lia; lia ].
        pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw. unfold wmem in Hw.
        rewrite Hw; [ | rewrite word_add_nat_Z2bv, u_small by lia; lia | rewrite word_add_nat_Z2bv, u_small by lia; lia ].
        eapply read_auxv_all; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact RSEGS | exact Sv48 | eassumption | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)].
      + apply bytes_at_of_rdn; [| lia | unfold le8; rewrite length_word_to_le_bytes; lia]. unfold le8. rewrite length_word_to_le_bytes.
        rewrite (main_entry_rdn_above inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME); [ | rewrite u_small by lia; lia | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
        pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw. unfold wmem in Hw.
        rewrite Hw; [ | rewrite u_small by lia; lia | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
        replace (bv_unsigned rw + 8) with (bv_unsigned rw + Z.of_nat 8) by lia.
        rewrite (RN4 8%nat 8%nat ltac:(lia)). fold sec. rewrite (word_to_le_bytes_of_lez 8 sec Lsec ltac:(lia)). reflexivity.
      + rewrite length_map. pose proof (Nat2Z.inj_add (length (removelast ES)) 1) as LN.
        rewrite length_map in PL.
        assert (Hc : (Z.of_nat (length (removelast ES)) + 1 = Z.of_nat (auxv_count (kb_rseq (in_kernel inp))))%Z) by lia.
        rewrite AVU. repeat split; try lia.
    - intros a b Hab. destruct (ro_addr rsegs a) eqn:E; [|reflexivity]. exfalso.
      apply ref_ro_addr_true in E. unfold IMG_LO in E.
      lazymatch type of E with ?lo <= _ < ?hi =>
        rewrite (mem_main_none lo hi a) in Hab; [discriminate | vm_compute; reflexivity | lia | lia] end.
  Qed.

  (* [comment removed for export] *)
  Theorem main_hi_heap0 : forall brk (lim : Z),
    valid_brk RSEGS brk -> valid_mmap_base mbase -> (bm_on = true \/ 2 ^ 34 <= lim) ->   (* [comment removed for export] *)
    hi_heap (HIV0 (bv_unsigned sp0)) [] (K0, B0) mem0 (mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 (in_kernel inp)) [] [] brk brk lim mbase sp0).
Proof.
    intros brk lim Hbrk Hmb Hlim.
    apply (HIV0_init (bv_unsigned sp0) mem0 lim); [apply main_init_statics0|].
    exists brk, mbase, sp0, (in_kernel inp). split; [reflexivity|]. split; [exact Hbrk|]. split; [exact Hmb|]. split; [exact Hvsp|]. split; [reflexivity | exact Hlim].
Qed.
End MainEntry.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithLib.
  Variable LayF : word -> lib_layout.
  Variable LStF : word -> lib_statics.
  Hypothesis DLLF : forall sp, valid_sp sp -> drv_lib_layout (LayF sp) (L0 (bv_unsigned sp)).
  Hypothesis LIokF : forall sp, valid_sp sp -> lib_iface_ok (LayF sp) scfg (HIV0 (bv_unsigned sp)) (LStF sp).
  Hypothesis LSXF : forall sp, valid_sp sp -> forall g M, ls_ok (LStF sp) g M -> exists ax : axv, atexit_cells M ax.      (* [comment removed for export] *)
  Hypothesis Hbudget : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
    cred (L0 (bv_unsigned sp)) (1 + 4 * fst (ll_credit (LayF sp) n)) (n + 2 ^ 20 + 4 * snd (ll_credit (LayF sp) n)) 0
         (debit (L0 (bv_unsigned sp)) (K0, B0) 65536).

  (* [comment removed for export] *)
  Variable lim : Z.
  Hypothesis HLIM : bm_on = true \/ 2 ^ 34 <= lim.
  Theorem src0_realizes_spec_heap : src_realizes_stmt2 scfg lim.
Proof.
    apply (src0_realizes_spec scfg lim (fun sp => L0 (bv_unsigned sp)) (fun sp => HIV0 (bv_unsigned sp)) LayF LStF (K0, B0)).
    - intros sp Hsp. apply HIV0_ok. exact Halloc.
    - exact drv_layout_L0.
    - exact DLLF.
    - exact LIokF.
    - exact LSXF.
    - intros sp a0s path envp uid hw rdraw tid regs mem brk mbase inp Hsp Hbrk Hmb Hva Hve Htid ME.
      eapply (main_hi_heap0 sp a0s path envp uid hw rdraw tid regs mem); eassumption.
    - exact Hfs.
    - exact Hbudget.
Qed.
End WithLib.
End FPX_1.

(* [comment removed for export] *)
Lemma HIV0_okR_at (scfg : SpuriousCfg) {bmK : BMode} (Halloc : sc_alloc scfg = false) (sp : word) : heap_ifaceR_ok (L0 (bv_unsigned sp)) scfg (HIV0 (bv_unsigned sp)).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0HeapBridgeHn ()) [] "h06Halloch13bmKh24scfgh32spp;1p;3p;2p;4g020^j16Tg00:hj35Tg0000j10Tg000Uj11Tg0013j14Tg002Kj22Tg021Sj43Tg022SR0g023MR1g00R`f1R2#6g024?35R3g00Ng#0#0#0#0#0#0#1R4#4R5f2R6f0R7,24f3R4P2C3X35X03X11X20P4P6P2P7O4W3W0W1W2o"). Qed.
Lemma HIV0_mallocN_at (scfg : SpuriousCfg) {bmK : BMode} (Halloc : sc_alloc scfg = false) (sp : word) : malloc_specN (L0 (bv_unsigned sp)) scfg (HIV0 (bv_unsigned sp)).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0HeapBridgeHn ()) [] "h06Halloch13bmKh24scfgh32spp;1p;3p;2p;4g020^j16Tg00:hj35Tg0000j10Tg000Uj11Tg0013j14Tg002Kj22Tg024_j43Tg022SR0g023MR1g00R`f1R2#6g024?35R3g00Ng#0#0#0#0#0#0#1R4#4R5f2R6f0R7,24f3R4P2C3X35X03X11X20P4P6P2P7O4W3W0W1W2o"). Qed.
