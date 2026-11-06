(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer HufHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Stdio_pure.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg StdioFiles.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_facts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RF_huf_h_iface RF_huf_iface_m RF_huf_h_kit RF_huf_h_draws RF_huf_h_lib RF_huf_h_split.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_h_asm1 () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib5Ubsan=RMalloc_iface=rclient_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib5Lists4List2InC46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib5Ubsan:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep6RERRNOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep5RLIBCC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec7Harness;fuzz_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:Stdio_pure>implM_from_evtC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5Ubsan=RMalloc_iface5RHEAPC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib5Lists7ListDef6Forall00C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5Ubsan;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RF_huf_h_split8hM_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RF_huf_h_split7fz_restC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog8fuzz_oneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv3Sem4core01C59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr03K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib5Ubsan<RF_huf_h_kitARHEAP_stack_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RF_huf_h_kitDrauxv_ok_stack_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface<rclient_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface=ralloc_staticC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc<Malloc_iface8in_blockC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RMalloc_ifacePGRHEAP_block_range_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface<rblock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RF_huf_h_kitCrheap_pres_of_munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface:rheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RF_huf_iface_m@prod_create_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_ifaceCrheap_pres_rw_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RF_huf_h_asm1Brclient_range_growC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_ifaceCrheap_pres_bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RF_huf_h_split@payload_own_disjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RF_huf_h_draws7hB_postC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib5Ubsan>RF_huf_h_draws<phaseB_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:HufHarness6hp_mtlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:HufHarness9huf_drawsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RF_huf_h_kit8fh_fp_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RF_huf_h_kit<fh_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:HufHarness?huf_draws_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:HufHarness:hp_streamsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:HufHarness:hp_symbolsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:HufHarness7hp_dbufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:HufHarness7hp_restC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:HufHarness8DT_BYTESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness7dt_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9dbuf_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC59OSSVerify5KrLib5Ubsan>RF_huf_iface_m@fuzz_malloc_postC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib5Ubsan=RMalloc_iface=raddr_exposedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RF_huf_h_iface7prod_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib3Lib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC4ELinuxProcessSemantics5Riscv7Prelude4zextC59OSSVerify5KrLib3Lib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib5Ubsan=RMalloc_ifaceArheap_pres_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface@rheap_pres_transC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RF_huf_h_lib=rw_cells_nullC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib4Spec7Harness8free_optC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib3Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib3MemDbytes_at_write_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib6Malloc8ProgDeps8ptr_addrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3maxC59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RF_huf_h_kit9errno_litC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib6Malloc8ProgDeps8raw_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps:raw_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog;new_handlerC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec7Harness=PRODUCER_SIZEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:HufHarness@HUF_TABLELOG_MAXC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib5Ubsan=Harness_iface=HARNESS_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Harness_iface;PFUZZ_ENTRYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9WKSP_SIZEC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib5Ubsan>RF_huf_iface_mAPROD_CREATE_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RF_huf_h_draws=PC_HB_EXIT_RAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RF_huf_h_draws?PFUZZ_MALLOC_HBC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec:HufHarness:huf_params00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RF_huf_iface_mAFUZZ_MALLOC_STACKC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03C59OSSVerify5KrLib5Ubsan>RF_huf_h_split5PC_HMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness=WKSP_SIZE_valC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma rclient_range_grow : forall LB LBX SP SP' A n,
  rclient_range LB SP A n -> SP' <= SP -> rclient_range (LBX ++ LB) SP' A n.
Proof.
  intros LB LBX SP SP' A n R HS. unfold rclient_range in *.
  destruct R as [R|[R|(b & Hb & R)]].
  - left. lia.
  - right. left. exact R.
  - right. right. exists b. split; [apply in_or_app; right; exact Hb| exact R].
Qed.

Section First.
  Hypothesis CREATE : prod_create_stmt.
  Hypothesis FMALLOC : fuzz_malloc_stmt.
  Hypothesis U32R : prod_u32r_stmt.
  Hypothesis I32R : prod_i32r_stmt.

  Ltac walk_to pc := repeat (lazymatch goal with
     | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
     | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [if_true | if_false]
     | |- evt _ _ (MS _ _ _ _ _ _ _) => zstep end).
  Ltac lit_pc := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?c) _ _ _ _) =>
    let v := eval cbv in c in change c with v end.
  Theorem fz_first :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (s : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z) (errv : word)
           (Q : Z -> PState -> machine_state -> Prop),
      RHEAP s LB m ->
      bytes_at usegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      rclient_range LB (bv_unsigned sp) D (zlength payload) ->
      0 < D -> D + zlength payload <= ATOP -> zlength payload < 2^26 ->
      rauxv_ok m AB -> bv_unsigned sp <= AB ->
      stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - HARNESS_STACK ->
      rw_cells usegs m (errno_addr tp) [C4 errv] ->
      mem_inv usegs m ->
      tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
      a0 = wz D -> a1 = wz (zlength payload) ->
      (forall producer dt wksp dBuf s' ms',
         hM_state ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB AB lo D payload m producer dt wksp dBuf s' ms' ->
         implM usegs (fz_rest producer dt wksp dBuf) s' Q ms') ->
      implM usegs (Prog.fuzz_one payload) s Q
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz PFUZZ_ENTRY) fc None m (seg_rom usegs)).
Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB D pl AB lo errv Q.
    intros HP PB PLB RR D0 DA PLEN AUX SPB ST LOA LOS ERR MI TP SPA A0 A1 K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold HARNESS_STACK in LOS. atop_facts.
    unfold wz in *. subst tp a0 a1. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    unfold zlength in *.
    unfold Prog.fuzz_one, Harness.fuzz_one, Harness.dt_size, Harness.dbuf_size, HufHarness.huf_dt_bytes, HufHarness.huf_dbuf.
    rewrite ?Zlength_correct.
    pose proof (huf_draws_range pl (zlen pl) ltac:(lia)) as HR. cbv zeta in HR.
    destruct HR as (HR1 & HR2 & HR3 & HR4 & HR5).
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 128%nat ST.
    lit_pc.
    walk_to 0x20e94.
    apply evt_done.
    assert (HP1 : RHEAP s LB m0) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; lia| constructor]]).
    assert (AUX1 : rauxv_ok m0 AB) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; lia| constructor]]).
    assert (RP0 : rheap_pres LB (bv_unsigned sp) m m0).
    { eapply rheap_pres_of_munch; [exact MU| exact WM| intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]].
      pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). destruct Hr. lia. }
    eapply implM_bind.
    { unfold prod_create_stmt in CREATE.
      eapply CREATE with (lo := lo) (B := AB); try reflexivity; unfold PROD_CREATE_STACK, FUZZ_MALLOC_STACK, RMALLOC_STACK;
        rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | lia | (rewrite errno_lit; unfold RERRNO; exact ERR)]. }
    cbv beta. intros r sA ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2
                    & ERR2 & AUX2 & HPR & FAE & SOE & p & P & -> & -> & BR & HP2 & PRC & HEXP).
    rewrite ?unsigned_lit in ST2, HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    rewrite ret_pc_even by (first [lia | reflexivity]).
    unfold FseNCount.Zlength.
    unfold HUF_TABLELOG_MAX in HR4. unfold PRODUCER_SIZE in BR3, BR4, BR5.
    assert (FR2 := rheap_pres_rw_cells _ _ _ _ _ _ HPR FR ltac:(left; lia)).
    assert (PB2 : bytes_at usegs m2 D (map (Z_to_bv 8) pl)).
    { eapply rheap_pres_bytes_at; [exact HPR| exact PB|].
      rewrite length_map. apply (rclient_range_grow LB [] (bv_unsigned sp)); [exact RR| lia]. }
    assert (DP : D + zlen pl <= P \/ P + 16 <= D).
    { pose proof (payload_own_disj sA m2 [(p, P, PRODUCER_SIZE)] LB (p, P, PRODUCER_SIZE) (bv_unsigned sp) D (zlen pl)
                   HP2 ltac:(left; reflexivity) RR ltac:(lia) DA ltac:(lia)) as H.
      cbn in H. unfold PRODUCER_SIZE in H. lia. }
    eapply implM_evt.
    { eapply (phaseB_proof U32R I32R) with (SP := bv_unsigned sp + -128) (P := P) (D := D) (pl := pl) (lo := lo) (m := m2);
        first [exact PRC | exact ST2 | exact MI2 | exact FR2 | (split; [exact PB2| exact PLB]) | lia]. }
    intros msB HB.
    destruct HB as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & c14
                    & f1 & f2 & f3 & f4 & f5 & j0 & m3 & -> & G1 & G2 & G3 & G4 & G5 & MU3 & WM3 & MI3 & ST3 & FR3 & PR3).
    assert (FW3 : Forall (fh_fp_ok [(p, P, PRODUCER_SIZE)] (bv_unsigned sp))
                    [(P + 8, P + 16); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128);
                     (bv_unsigned sp + -128 + 8, bv_unsigned sp + -128 + 24)]).
    { rewrite Forall_forall. intros iv HI. cbn in HI. unfold fh_fp_ok.
      destruct HI as [<-|[<-|[<-|[]]]]; cbn.
      - right. exists (p, P, PRODUCER_SIZE). cbn. unfold PRODUCER_SIZE. split; [left; reflexivity| lia].
      - left. lia.
      - left. lia. }
    destruct (fh_transport sA [(p, P, PRODUCER_SIZE)] LB m2 m3 _ AB (bv_unsigned sp) HP2 MU3 WM3 FW3 ltac:(lia))
      as (HP3 & AUXT & ERRT & RP3).
    pose proof (AUXT AUX2) as AUX3. pose proof (ERRT _ ERR2) as ERR3. clear AUXT ERRT.
    assert (DTB : 8 <= DT_BYTES (hp_mtl (huf_draws pl (zlen pl))) < 2^32).
    { unfold DT_BYTES.
      pose proof (Z.pow_le_mono_r 2 _ 12 ltac:(lia) (proj2 HR4)) as E1.
      pose proof (Z.pow_pos_nonneg 2 (hp_mtl (huf_draws pl (zlen pl))) ltac:(lia) ltac:(lia)) as E2.
      change (2 ^ 12) with 4096 in E1. lia. }
    eapply implM_bind.
    { unfold fuzz_malloc_stmt in FMALLOC.
      eapply FMALLOC with (lo := lo) (B := AB); try reflexivity; unfold FUZZ_MALLOC_STACK, RMALLOC_STACK;
        rewrite ?unsigned_lit by lia;
        first [exact HP3 | exact AUX3 | exact ST3 | exact MI3 | lia | (rewrite errno_lit; unfold RERRNO; exact ERR3)]. }
    cbv beta. intros r1 s4' ms4 PO.
    destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & errv4 & -> & MI4 & ST4
                    & ERR4 & AUX4 & RP4 & FA4 & SO4 & R1).
    destruct r1 as [pd|]; [| destruct R1 as (R1 & _); exfalso; lia].
    destruct R1 as (DT & jdt & -> & BRD & HP4 & DTC & _).
    rewrite ?unsigned_lit in ST4, RP4 by lia. rewrite errno_lit in ERR4. unfold RERRNO in ERR4.
    unfold PC_HB_EXIT_RA. rewrite ret_pc_even by (first [lia | reflexivity]).
    apply implM_from_evt. walk_to 0x21068. apply evt_done.
    eapply implM_bind.
    { unfold fuzz_malloc_stmt in FMALLOC.
      eapply FMALLOC with (lo := lo) (B := AB); try reflexivity;
        unfold FUZZ_MALLOC_STACK, RMALLOC_STACK, WKSP_SIZE, HufHarness.HUF_WORKSPACE_SIZE;
        rewrite ?unsigned_lit by lia;
        first [exact HP4 | exact AUX4 | exact ST4 | exact MI4 | lia | (rewrite errno_lit; unfold RERRNO; exact ERR4)]. }
    cbv beta. intros r2 s5' ms5 PO.
    destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m5 & errv5 & -> & MI5 & ST5
                    & ERR5 & AUX5 & RP5 & FA5 & SO5 & R2).
    destruct r2 as [pw|]; [| destruct R2 as (R2 & _); unfold WKSP_SIZE, HufHarness.HUF_WORKSPACE_SIZE in R2; exfalso; lia].
    destruct R2 as (W & jw & -> & BRW & HP5 & WC & _).
    rewrite ?unsigned_lit in ST5, RP5 by lia. rewrite errno_lit in ERR5. unfold RERRNO in ERR5.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    apply implM_from_evt. walk_to 0x21068. apply evt_done.
    eapply implM_bind.
    { unfold fuzz_malloc_stmt in FMALLOC.
      eapply FMALLOC with (lo := lo) (B := AB); try reflexivity; unfold FUZZ_MALLOC_STACK, RMALLOC_STACK;
        rewrite ?unsigned_lit by lia;
        first [exact HP5 | exact AUX5 | exact ST5 | exact MI5 | lia | (rewrite errno_lit; unfold RERRNO; exact ERR5)]. }
    cbv beta. intros r3 s6' ms6 PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & errv6 & -> & MI6 & ST6
                    & ERR6 & AUX6 & RP6 & FA6 & SO6 & R3).
    rewrite ?unsigned_lit in ST6, RP6 by lia. rewrite errno_lit in ERR6. unfold RERRNO in ERR6.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    assert (RP36 : rheap_pres ([(p, P, PRODUCER_SIZE)] ++ LB) (bv_unsigned sp + -128) m3 m6).
    { eapply rheap_pres_trans; [exact RP4|].
      eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact RP5| lia| intros b Hb; cbn [In app] in Hb |- *; tauto]|].
      eapply rheap_pres_weaken; [exact RP6| lia| intros b Hb; cbn [In app] in Hb |- *; tauto]. }
    assert (RP56 : rheap_pres ((pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))) :: [(p, P, PRODUCER_SIZE)] ++ LB)
                     (bv_unsigned sp + -128) m4 m6).
    { eapply rheap_pres_trans; [exact RP5|].
      eapply rheap_pres_weaken; [exact RP6| lia| intros b Hb; cbn [In app] in Hb |- *; tauto]. }
    assert (RP26 : rheap_pres LB (bv_unsigned sp) m2 m6).
    { eapply rheap_pres_trans; [exact RP3|].
      eapply rheap_pres_weaken; [exact RP36| lia| intros b Hb; cbn [In app]; tauto]. }
    assert (RPall : rheap_pres LB (bv_unsigned sp) m m6).
    { eapply rheap_pres_trans; [exact RP0|].
      eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]| exact RP26]. }
    assert (PB6 : bytes_at usegs m6 D (map (Z_to_bv 8) pl)).
    { eapply rheap_pres_bytes_at; [exact RP26| exact PB2| rewrite length_map; exact RR]. }
    pose proof (rheap_pres_rw_cells _ _ _ _ _ _ RP36 FR3 ltac:(left; lia)) as FR6.
    pose proof (rheap_pres_rw_cells _ _ _ _ _ _ RP36 PR3
                  ltac:(right; right; exists (p, P, PRODUCER_SIZE);
                        cbn [In app cells_size csize blk_addr blk_size fst snd]; unfold PRODUCER_SIZE;
                        split; [left; reflexivity| lia])) as PR6.
    pose proof (rheap_pres_rw_cells _ _ _ _ _ _ RP56 DTC
                  ltac:(right; right; exists (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl))));
                        cbn [In app cells_size csize blk_addr blk_size fst snd];
                        split; [left; reflexivity| lia])) as DT6.
    pose proof (rheap_pres_rw_cells _ _ _ _ _ _ RP6 WC
                  ltac:(right; right; exists (pw, W, WKSP_SIZE);
                        cbn [In app cells_size csize blk_addr blk_size fst snd];
                        unfold WKSP_SIZE, HufHarness.HUF_WORKSPACE_SIZE;
                        split; [left; reflexivity| lia])) as WC6.
    assert (SO : ps_so s6' = ps_so s) by congruence.
    destruct r3 as [pb|].
    - destruct R3 as (DST & jd & -> & BRB & HP6 & DC & _).
      apply (K (Some p) (Some pd) (Some pw) (Some pb)). unfold hM_state.
      exists p, pd, pw, P, DT, W, DST, [(pb, DST, hp_dbuf (huf_draws pl (zlen pl)))], f1, f2, f3, f4, f5, j0, jdt, jw, jd.
      eexists _, y0, y1, y2, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14. exists m6, errv6.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [right; exists pb; split; [reflexivity| split; [reflexivity| exact BRB]]|].
      split; [reflexivity|].
      split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
      split; [exact HP6|]. split; [exact BR|]. split; [exact BRD|]. split; [exact BRW|].
      split; [exact AUX6|]. split; [exact ERR6|]. split; [exact FR6|]. split; [exact PB6|]. split; [exact PR6|].
      split; [exact DT6|]. split; [exact WC6|]. split; [exact DC|]. split; [exact ST6|]. split; [exact MI6|].
      split; [exact RPall| exact SO].
    - destruct R3 as (HZ & -> & HP6).
      apply (K (Some p) (Some pd) (Some pw) None). unfold hM_state.
      exists p, pd, pw, P, DT, W, 0, [], f1, f2, f3, f4, f5, j0, jdt, jw, [].
      eexists _, y0, y1, y2, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14. exists m6, errv6.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [left; split; [reflexivity| split; [reflexivity| split; [exact HZ| reflexivity]]]|].
      split; [reflexivity|].
      split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
      split; [exact HP6|]. split; [exact BR|]. split; [exact BRD|]. split; [exact BRW|].
      split; [exact AUX6|]. split; [exact ERR6|]. split; [exact FR6|]. split; [exact PB6|]. split; [exact PR6|].
      split; [exact DT6|]. split; [exact WC6|]. split; [rewrite HZ; exact (rw_cells_null m6)|].
      split; [exact ST6|]. split; [exact MI6|].
      split; [exact RPall| exact SO].
  Qed.

End First.
End CANSEC1.
