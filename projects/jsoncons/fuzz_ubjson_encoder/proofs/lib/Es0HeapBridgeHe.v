(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: some recorded proofs replaced by tactic proofs; the new launch (process input, auxv, group id, exec file name); the CONFIG_RSEQ flag; the auxv as a list of pairs; new lemmas; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Mem Cells Step Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RMalloc_iface RF_aligned RF_aligned_spec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Heap Require Import HeIface HeInst0 HeClosed HeV16.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import RunEnv
  PropExec CatExec SeqExec StoreOk MemSplit AgentLib StartupTac RefLayout ArgvEnv LibTail ZStores
  SymExec2 SymExec2Sound SymDriveX DrvKit
  SymDrive Es0StartupDefs Es0Startup Es0StartupFacts Es0MainEntry HeapIface LibIface Es0DrvLib Es0DrvLibL Es0DrvG Es0DrvMain Es0Exit_run1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import LibIfaceE UbjEncShapes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Es0HeapBridgeHe () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC45stdpp9bitvector;definitions;bv_unsignedC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeInst02L0C13~~~I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface?hl_alloc_staticC13~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface;hl_alloc_roC13~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega7EnvRing5PExpr01I47Corelib4Init5Logic3and00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8hl_stackC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface?hl_k_per_mallocC13~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3powC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface=hl_b_overheadC13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Es0DrvLib:drv_layout01C13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images5Plain1M?loaded_segmentsC13~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref?RF_aligned_spec>RALIGNED_STACKC13~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List9nth_errorC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes3nat02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3mrdC13~~~K45stdpp9bitvector;definitions2bv01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:rdn_unfoldC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7wa_succC13~~~K46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init9Datatypes8list_indK47Corelib4Init5Logic3and01C45stdpp9bitvector;definitions6bv_addC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem>store_ok_wviewC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S7u_smallC13~~~C56Stdlib6ZArith4Znat5Z2Nat2idK46Stdlib9micromega=RingMicromega5Psatz06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C47Corelib4Init9Datatypes3appC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem<bytes_at_appC13~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3mulC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Es0StartupCmain_entry_rdn_dataC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0StartupFacts<D_main_missbC13~~~C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffI47Corelib4Init9Datatypes4prod00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0StartupFacts@range_disjoint_bC13~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefs6D_mainC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0StartupFacts;D_main_missC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHe=rdn_main_dataC13~~~C46Stdlib5Lists4List7forallbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0StartupFacts<D_main_cellsC13~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0MainEntry9missb_subC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0MainEntry;D_main_noneC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Es0StartupCmain_entry_mem_dataC13~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedK47Corelib4Init;Hexadecimal4uint02K47Corelib4Init;Hexadecimal4uint05K47Corelib4Init6Number4uint02C47Corelib4Init3Nat;of_num_uintC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk?store_ok_windowC13~~~K47Corelib4Init;Hexadecimal4uint01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0MainEntry9wseg_dataC13~~~K47Corelib4Init7Decimal4uint04K47Corelib4Init7Decimal4uint09K47Corelib4Init7Decimal4uint08K47Corelib4Init7Decimal4uint0:K47Corelib4Init6Number4uint01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9StreamSim7wseg_okC13~~~K47Corelib4Init7Decimal4uint01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5CellsBcells_bytes_lengthC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHe?bytes_at_of_rdnC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHeAwr_at_of_store_okC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~C45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib5Lists7ListDef3mapI47Corelib7Numbers7BinNums1N00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9u64_rangeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0MainEntry7auxvp_uC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0MainEntry5auxvpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9RefLayout8auxv_offC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeInst0=init_statics0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0MainEntry5rnd_uC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0MainEntry3rndC13~~~C56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefs8canary_wC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell04C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHe=mem_main_noneC13~~~C47Corelib4Init5Logic7and_indc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHe<rdn_main_imgC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHe=store_ok_dataC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHe?rw_cells_of_rdnC13~~~C56Stdlib6ZArith6BinInt1Z6shiftrC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0StartupFacts?D_main_pagesizeC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHeDbytes_eq_of_unsignedC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHe>store_ok_relroC13~~~C47Corelib4Init5Logic5proj1C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0StartupFacts@main_entry_guardC13~~~C47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutFlength_at_random_bytesC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List=length_firstnC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7ph_addrC56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_entC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_numC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2SCbytes_le_to_Z_boundC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0MainEntry<D_main_auxvpC13~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib5Lists7ListDef3nthC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0MainEntry9main_auxvC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem<bytes_at_nilC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8wrap_memC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArgvEnv>rdn_wmem_stackC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArgvEnv4wmemC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymDriveGword_to_le_bytes_of_lezC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Es0StartupDmain_entry_rdn_aboveC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefsGlength_word_to_le_bytesC13~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7ro_addrC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeInst0@ref_ro_addr_trueC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr4u64sC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHe=bytes_at_app2C13~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC79OSSVerify8jsonconsCfuzz_ubjson_encoder6images5Plain1M5phdrsC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiK47Corelib4Init9Datatypes4bool02C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeInst06IMG_LOC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode5bm_onC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface7hl_segsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8hl_sptopC13~~~K47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z8le_transK47Corelib4Init5Logic2or02C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap5HeV169HIV0_initC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHeBmain_init_statics0C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap5HeV164HIV0C13~~~K47Corelib4Init9Datatypes4prod01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap5HeV167HIV0_okC13~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Es0Startup:main_entry00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHe=main_hi_heap0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Es0DrvMainCsrc0_realizes_specXC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeInst02K0C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeInst02B0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHe=drv_layout_L0C13~~~I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Es0DrvMainBsrc0_realizes_specC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Es0DrvMain?src0_realizes_GC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run8sc_allocC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap5HeV168HIV0_okRC13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode5BMode00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap5HeV16<HIV0_mallocNC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap5HeV168HIV0_okSC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap5HeV16=HIV0_mallocNFC13~~~".
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
Variable lim : Z.   (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma drv_layout_L0 : forall sp, valid_sp sp -> drv_layout (L0 (bv_unsigned sp)) sp.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0HeapBridgeHe ()) ["FPX_1"] "p'0h07__arithh14__ffh28__varmaph35__with44__x1h52Hah64__x2h71ah81Hh93Hsph:1eh;2sph<1xi001cp;1p;2p;3p;4p;6p;?p;7p;8g0000j10Tg000Uj1_Tg0013j1\Tg001Vj1pTg002Kj2LTg0035j1RTg004?j1QTg004_j2JTg0059j14Tg005^j2kTg0072j1fTg007Rj2STg0080j1aTg008Nj1`Tg0099j2PTg009\j1^Tg00:>j2]Tg00:`j2[Tg00;Lj3NTg00;fj3ZTg00<Ej4YTg00=7j2CTg00=Tj2ITg00>0j2XTg00?@j1WTg00?^j4oTg00@<j1;Tg00@Zj2<Tg00A6j2UTg00AYj2GTg00B4j1lTg00CAj1jTg00DUj6hTg00E1j2gTg00EPj2eTg00Emj1cTg00G?l?dTg00HPj4FTg00I;j7KTg00I_j3bTg00JBj7TTg00Jfj8iTg00KJj7MTg00Knj2mTf0R0#0#0p=9%40#4p=5%40#0p=2%00#;p=Bg00LHR1/J0p=>%00#4p=6%00#0#0#0p=:%00#0#0#;p=31U10p=1f2R2g00LfR3g00MER4P4g00MeR5P1f1R6g00NER7P0CFg00NlR8FKp=7Ab160p=AP1P6g00OLR9P0CFp=Ef3R:P3P4P4P5P2P6P3P4P4P5P0P8FKFTp=@P:P3P4P4P5P2P6P0Gip=O1<26/G0p=HP2P3P4P4P5P1P6P9P0CFP8FKp=?f4R8P3P4P4P5P:P3P4P4P5P2P6FTP0FMp==P8P3P4P4P5P:P2P3P4P4P5P6P0FMFMp=V1<8:1I26'G/m0p=8P1P6P7P0CFp=ng00P3R7/<0p=Dg00PQR:#0R3#0R9#0R;#9R<#0R=#_R>#\%p01L>6R?#RR@P6g00Q6#Qg00R5'J%59#2#5#2RA#5#2#5#2#B#>%6A#9#5#2#B#>%4:RA#0#6#6RB#2#:#2#9#3#>%0=#9#:R=#0RC#0#BRD#>%4A#6RA#2#9#:#:#3#>1L>2#RRE/k0g00SCRF#fRG%QFRF1S16%a1RH%`1RIPI%0ARA#4RJ#4RK#0RL#4RM#0#9#2RN#6#3RO#1RP1P1:RQ57IRRPI%2N#3RN#1RS%0A#3RA#1'ART,EQC@%^4R4PIPRPI%5M#5#5RM#0#3RR#1RU,EQC@CO1]I5R5P0P2g00SoRVg00TORW'J1[02=NVWdAZ176CYRWb1b2b3X411CNARA,I09HO01I6R9HO6[^41P0P2P6O2b0W5X711XE0PGPFP11S12P6%W1RECoPHPIPIPI%1D=7IQRV%43RX#4RY#0#6#9#:#:#3RZ#19?IQPIPI%6L#6RL#2#2#3R[#1=7IQPI1EQPC@RPPIPIA7ITQPI%3JRJ#1,AS,EQC@PIPI%4Y#9RY#9#6#6#6#9#3RS#1RT=7IQ%;;R;#1R\,AT9?IQPIPI%0L#5RL#0#3RT#1R]=7IQR^1A]\9?IQPIPI%5K#:#5RK#0#2#BR]#1R\=7IQR_%;9R9#1,A\9?IQ1P13=7IQR\D=D=D=DVD=P4PIPIPV%2Y#:#:#3RY#19?IQPIPIP^%4L#3RL#19?IQPIPPPIPIA7IUQPI%4M#3RM#1,EQC@PIPIP_%4K#3RK#19?IQP\D=DVD=D=COP5PWb1b2b3X41X61PDP0P0PZP[P0P0POPAP0P01CNJPSP0P01CS;PTP0P01CT;P]P0P01C]91<60D8D8D8D8D8D8PDP6P6PYPTP6P6PLP[P6P6POPRP6P6PMP]P6P6PK1<26D8D8D8D8D8[^41^61P01L>8P2P6O3b0W5X71%6B#5#5#9#5#2#B#>%>?PGPFPEPHPI1U17R1%;=R=#1%;<R<#1'AR?57IPI%;CRC#1,n?C@P5PWb1b2b31C=<R<#D1<<C'GP0b0g00ToR<1<<C5H7e%l@R7#D1<7C'GePGPFPEPH%;:R:#197I1P5PWb1b2b3%D:P0b0%j@#Deg00VOR:g00W5RWg00W[R53NP:PWP:p-0P0g00XARWg00X^PWn011000003000000X::g00Y:P5P0EhPW1gW0b8W<%;3%0X#B'e#Dd%c@#DeM?dW9W;o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_at_of_rdn : forall segs m (a : Z) (bs : list byte),
  rdn segs m (Z_to_bv 64 a) (length bs) = Some bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at segs m a bs.
Proof.
  intros segs m a bs Hr Ha Hb. split; [exact Ha|]. split; [exact Hb|].
  revert a Hr Ha Hb. induction bs as [|b bs IH]; intros a Hr Ha Hb i Hi; [cbn in Hi; lia|].
  cbn [length] in Hr. rewrite rdn_unfold in Hr. fold (wa a) in Hr.
  destruct (mrd segs m (wa a)) as [b0|] eqn:E0; [|discriminate].
  destruct (rdn segs m (wa a + 1)%bv (length bs)) as [r|] eqn:E1; [|discriminate].
  injection Hr as <- <-.
  destruct i as [|i].
  - cbn. rewrite Z.add_0_r. exact E0.
  - cbn [nth_error]. replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia.
    cbn [length] in Hb.
    apply (IH (a + 1)); [| lia | lia | cbn in Hi; lia].
    rewrite wa_succ in E1. exact E1.
Qed.

Lemma wr_at_of_store_ok : forall segs m (a : Z) (n : nat),
  store_ok segs m (Z_to_bv 64 a) n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> wr_at segs m a (Z.of_nat n).
Proof.
  intros segs m a n Hs Ha Hb. split; [exact Ha|]. split; [exact Hb|]. intros i Hi.
  pose proof (store_ok_wview segs m (Z_to_bv 64 a) n (Z.to_nat i) Hs ltac:(lia)) as W.
  rewrite u_small in W by lia. rewrite Z2Nat.id in W by lia. exact W.
Qed.

Lemma bytes_at_app2 : forall segs m a bs1 bs2,
  bytes_at segs m a bs1 -> bytes_at segs m (a + Z.of_nat (length bs1)) bs2 -> bytes_at segs m a (bs1 ++ bs2).
Proof. intros. apply bytes_at_app. split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MainEntry.
  Context {RE : RunEnv}.
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
  Lemma rdn_main_data : forall (a : Z) (n : nat), 0 <= a -> a + Z.of_nat n <= 0xec000 ->
    rdn RSEGS mem0 (Z_to_bv 64 a) n = rdn RSEGS (D_main inp sp0 rdraw RND tid) (Z_to_bv 64 a) n.
Proof.
    intros a n Ha Hn. apply (main_entry_rdn_data inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME).
    rewrite u_small by lia. unfold stack_max_size. lia.
Qed.

  (* [comment removed for export] *)
  Lemma rdn_main_img : forall (a : Z) (n : nat), D_main_missb a n = true -> a + Z.of_nat n <= 0xec000 ->
    rdn RSEGS mem0 (Z_to_bv 64 a) n = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof.
    intros a n Hb Hn.
    assert (Ha : 0 <= a).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
    destruct (main_entry_inp inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) as (Eav & _).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
    rewrite rdn_main_data by lia.
    first [ apply (D_main_miss inp sp0 rdraw tid); exact Hb
          | apply (D_main_miss inp sp0 rdraw tid Hva'); exact Hb
          | eapply D_main_miss; first [exact Hb | exact Hva'] ].
Qed.

  Lemma mem_main_none : forall (lo hi : Z) (x : word), D_main_missb lo (Z.to_nat (hi - lo)) = true -> lo <= hi <= 0xec000 ->
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
  Lemma store_ok_data : forall (a : Z) (n : nat), 0xb9000 <= a -> a + Z.of_nat n <= 0xec000 ->
    store_ok RSEGS mem0 (Z_to_bv 64 a) n = true.
  Proof.
    intros a n Ha Hn.
    eapply (store_ok_window RSEGS mem0 (Z_to_bv 64 0xb9000) (Z_to_bv 64 a) 0x33000 n 0xb9000 0xec000);
      [reflexivity | reflexivity | lia | apply Es0MainEntry.wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.
  Lemma store_ok_relro : forall (a : Z) (n : nat), 0xb2000 <= a -> a + Z.of_nat n <= 0xb9000 ->
    store_ok RSEGS mem0 (Z_to_bv 64 a) n = true.
  Proof.
    intros a n Ha Hn.
    eapply (store_ok_window RSEGS mem0 (Z_to_bv 64 0xb2000) (Z_to_bv 64 a) 28672 n 0xb2000 0xb9000);
      [reflexivity | reflexivity | lia | vm_compute; reflexivity | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_of_rdn : forall (A : Z) cs,
    cells_wf cs ->
    rdn RSEGS mem0 (Z_to_bv 64 A) (length (cells_bytes cs)) = Some (cells_bytes cs) ->
    store_ok RSEGS mem0 (Z_to_bv 64 A) (cells_size cs) = true ->
    0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
    rw_cells rsegs mem0 A cs.
  Proof.
    intros A cs Hwf Hr Hs HA HB. pose proof (cells_bytes_length cs Hwf) as HL.
    split; [split; [exact Hwf|]|].
    - apply bytes_at_of_rdn; [exact Hr | exact HA | rewrite HL; exact HB].
    - apply wr_at_of_store_ok; [exact Hs | exact HA | exact HB].
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
  Proof.
    intros l1. induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
    injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
  Qed.

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
      assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
      first [ apply (D_main_pagesize inp sp0 rdraw tid Hva')
            | apply (D_main_pagesize inp sp0 rdraw tid)
            | eapply D_main_pagesize; exact Hva' ].
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
        rewrite rdn_main_data by (cbn; lia). rewrite Z_to_bv_bv_unsigned.
        first [ eapply (D_main_auxvp sp0 a0s path envv uid hw rdraw tid regs0 mem0); eassumption
              | eapply D_main_auxvp; eassumption ].
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
  Theorem main_hi_heap0 : forall brk,    (* [comment removed for export] *)
    valid_brk RSEGS brk -> valid_mmap_base mbase -> (bm_on = true \/ 2 ^ 39 <= lim) ->   (* [comment removed for export] *)
    hi_heap (HIV0 (bv_unsigned sp0) lim) [] (K0, B0) mem0 (mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 (in_kernel inp)) [] [] brk brk lim mbase sp0).
Proof.
    intros brk Hbrk Hmb Hlim.
    apply (HIV0_init (bv_unsigned sp0) lim mem0); [apply main_init_statics0| | exact Hlim].
    exists brk, mbase, sp0, (in_kernel inp). split; [reflexivity|]. split; [exact Hbrk|]. split; [exact Hmb|]. split; [exact Hvsp|]. split; [reflexivity|].
    destruct Hlim as [Hl|Hl]; [left; exact Hl| right; lia].
Qed.
End MainEntry.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithLib.
  Variable LayF : word -> lib_layout.
  Variable LStF : word -> lib_statics.
  Hypothesis DLLF : forall sp, valid_sp sp -> drv_lib_layout (LayF sp) (L0 (bv_unsigned sp)).
  Variables PayOk PayExport : list byte -> Prop.      (* [comment removed for export] *)
  Hypothesis LIokXF : forall sp, valid_sp sp -> lib_iface_ok_x (LayF sp) scfg (HIV0 (bv_unsigned sp) lim) (LStF sp) PayOk PayExport.
  Hypothesis LSXF : forall sp, valid_sp sp -> forall g M, ls_ok (LStF sp) g M -> exists ax : axv, atexit_cells M ax.      (* [comment removed for export] *)
  Hypothesis Hbudget : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
    cred (L0 (bv_unsigned sp)) (1 + 4 * fst (ll_credit (LayF sp) n)) (n + 2 ^ 20 + 4 * snd (ll_credit (LayF sp) n)) 0
         (debit (L0 (bv_unsigned sp)) (K0, B0) 65536).

  (* [comment removed for export] *)
  Hypothesis HLIM : bm_on = true \/ 2 ^ 39 <= lim.      (* [comment removed for export] *)
  Theorem src0_realizes_spec_heapX : src_realizes_stmt2X scfg lim PayOk.
Proof.
    apply (src0_realizes_specX scfg lim (fun sp => L0 (bv_unsigned sp)) (fun sp => HIV0 (bv_unsigned sp) lim) LayF LStF (K0, B0) PayOk PayExport).
    all: first [ exact drv_layout_L0 | exact DLLF | exact LIokXF | exact LSXF | exact Hfs | exact Hbudget
               | (intros sp Hsp; apply HIV0_ok; exact Halloc)
               | (intros sp a0s path envp uid hw rdraw tid regs mem brk mbase inp Hsp Hbrk Hmb Hva Hve Htid ME;
                  pose proof (run_env_of inp) as REi;
                  eapply (main_hi_heap0 sp a0s path envp uid hw rdraw tid regs mem); eassumption) ].
Qed.
  Theorem src0_realizes_spec_heap : (forall p, PayOk p) -> src_realizes_stmt2 scfg lim.
Proof.
    intros HPT.
    apply (src0_realizes_spec scfg lim (fun sp => L0 (bv_unsigned sp)) (fun sp => HIV0 (bv_unsigned sp) lim) LayF LStF (K0, B0) PayOk PayExport).
    all: first [ exact drv_layout_L0 | exact DLLF | exact LIokXF | exact LSXF | exact Hfs | exact Hbudget | exact HPT
               | (intros sp Hsp; apply HIV0_ok; exact Halloc)
               | (intros sp a0s path envp uid hw rdraw tid regs mem brk mbase inp Hsp Hbrk Hmb Hva Hve Htid ME;
                  pose proof (run_env_of inp) as REi;
                  eapply (main_hi_heap0 sp a0s path envp uid hw rdraw tid regs mem); eassumption) ].
Qed.
  Theorem src0_realizes_G_heap : (forall p, PayOk p) -> src_realizes_stmtG scfg lim PayExport.
Proof.
    intros HPT.
    apply (src0_realizes_G scfg lim (fun sp => L0 (bv_unsigned sp)) (fun sp => HIV0 (bv_unsigned sp) lim) LayF LStF (K0, B0) PayOk PayExport).
    all: first [ exact drv_layout_L0 | exact DLLF | exact LIokXF | exact LSXF | exact Hfs | exact Hbudget | exact HPT
               | (intros sp Hsp; apply HIV0_ok; exact Halloc)
               | (intros sp a0s path envp uid hw rdraw tid regs mem brk mbase inp Hsp Hbrk Hmb Hva Hve Htid ME;
                  pose proof (run_env_of inp) as REi;
                  eapply (main_hi_heap0 sp a0s path envp uid hw rdraw tid regs mem); eassumption) ].
Qed.
End WithLib.
End FPX_1.

(* [comment removed for export] *)
Lemma HIV0_okR_at (scfg : SpuriousCfg) {bmK : BMode} (Halloc : sc_alloc scfg = false) (sp : word) (lim : Z) : heap_ifaceR_ok (L0 (bv_unsigned sp)) scfg (HIV0 (bv_unsigned sp) lim).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0HeapBridgeHe ()) [] "h06Halloch13bmKh23limh34scfgh42spp;1p;3p;2p;5g03REj16Tg00;Lj35Tg0000j10Tg000Uj11Tg0013j14Tg002Kj22Tg03S:j53Tg03THR0g03UBR1g00Sof1R2#6g033k35R3g00PQ#0#0#0#0#0#0#1R4#4R5g00LHR6f3R71242f0R4f4R8f2R9D3X26X45X03X11X30P8P7P9P2P4O5X26X45X03X11X30P8P7P9P2P4O5W2W4W0W1W3o"). Qed.
Lemma HIV0_mallocN_at (scfg : SpuriousCfg) {bmK : BMode} (Halloc : sc_alloc scfg = false) (sp : word) (lim : Z) : malloc_specN (L0 (bv_unsigned sp)) scfg (HIV0 (bv_unsigned sp) lim).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0HeapBridgeHe ()) [] "h06Halloch13bmKh23limh34scfgh42spp;1p;3p;2p;5g03REj16Tg00;Lj35Tg0000j10Tg000Uj11Tg0013j14Tg002Kj22Tg03VJj53Tg03THR0g03UBR1g00Sof1R2#6g033k35R3g00PQ#0#0#0#0#0#0#1R4#4R5g00LHR6f3R71242f0R4f4R8f2R9D3X26X45X03X11X30P8P7P9P2P4O5X26X45X03X11X30P8P7P9P2P4O5W2W4W0W1W3o"). Qed.
(* [comment removed for export] *)
Lemma HIV0_okS_at (scfg : SpuriousCfg) {bmK : BMode} (Halloc : sc_alloc scfg = false) (sp : word) (lim : Z) : heap_ifaceS_ok (L0 (bv_unsigned sp)) scfg (HIV0 (bv_unsigned sp) lim) lim.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0HeapBridgeHe ()) [] "h06Halloch13bmKh23limh34scfgh42spp;1p;3p;2p;5g03REj16Tg00;Lj35Tg0000j10Tg000Uj11Tg0013j14Tg002Kj22Tg03W\j53Tg03THR0g03UBR1g00Sof1R2#6g033k35R3g00PQ#0#0#0#0#0#0#1R4#4R5g00LHR6f3R71242f0R4f4R8f2R9D3X26X45X03X11X30P8P7P9P2P4O5X26X45X03X11X30P8P7P9P2P4O5W2W4W0W1W3o"). Qed.
Lemma HIV0_mallocNF_at (scfg : SpuriousCfg) {bmK : BMode} (Halloc : sc_alloc scfg = false) (sp : word) (lim : Z) : malloc_specNF (L0 (bv_unsigned sp)) scfg lim (HIV0 (bv_unsigned sp) lim).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0HeapBridgeHe ()) [] "h06Halloch13bmKh23limh34scfgh42spp;1p;3p;2p;5g03REj16Tg00;Lj35Tg0000j10Tg000Uj11Tg0013j14Tg002Kj22Tg03Xjj53Tg03THR0g03UBR1g00Sof1R2#6g033k35R3g00PQ#0#0#0#0#0#0#1R4#4R5g00LHR6f3R71242f0R4f4R8f2R9D3X26X45X03X11X30P8P7P9P2P4O5X26X45X03X11X30P8P7P9P2P4O5W2W4W0W1W3o"). Qed.
