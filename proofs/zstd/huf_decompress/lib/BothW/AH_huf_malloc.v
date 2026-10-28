(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface AKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AH_huf_malloc () := "C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2InC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4mretC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6implMAC5ARocqVerifyHarness?AgentSubmission4Spec7Harness;fuzz_mallocC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit:implMA_retC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;implMA_bindC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;implMA_monoC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit@implMA_from_evtFC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit@implMA_post_evtFI46Stdlib5Lists4List5NoDup00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoI47Corelib4Init9Datatypes4prod00I47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPK47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:aheap_presC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or02I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_block_boundsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kitCaheap_pres_of_munchC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00I47Corelib4Init5Logic2ex00K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes4prod01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlI5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_blocks_nodupK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceBAI_blocks_disjointC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<shad_in_bandC5ARocqVerifyHarness?AgentSubmission5BothW5ABase?ablk_clear_bandC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC35stdpp4base6lookupC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowK47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6aps_okC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA<new_handlerAc5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocAfuzz_mallocA_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_rtcellsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8artcellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC56Stdlib6ZArith6BinInt1Z6of_natK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps9amalloc_MC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj1K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit8aps_restC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<amalloc_postC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit9aunw_dataK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kitCimplMA_amalloc_callC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5fp_leC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceCaheap_pres_rw_cellsC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA9rng_fp_leC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releasec5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_malloc@aheap_pres_frameC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaheap_pres_weakenC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface@aheap_pres_transC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl9aptr_addrK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr5msize04c5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocCFUZZ_MALLOC_STACK_AC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase:AMALLOC_PCC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<AFMALLOC_RETC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps:AAllocAsanc5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_malloc<AFUZZ_MALLOCI47Corelib4Init9Datatypes9Empty_set00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase=AMALLOC_STACKC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litc5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocAfuzz_mallocA_stmtC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00c5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocBfuzz_mallocA0_postC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA:fp_le_reflc5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocBfuzz_malloc_proofAc5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocBfuzz_mallocA0_stmtc5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocAprod_createA_postC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kitAablock_unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kitBunpoisoned8_rd_offC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib3Tac7sum_natC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib4Init9Datatypes3appK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC46Stdlib4Bool4Bool>negb_false_iffC5ARocqVerifyHarness?AgentSubmission5BothW5ABase>ablk_disj_bandC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_munchc5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_malloc@aheap_pres_freshC5ARocqVerifyHarness?AgentSubmission5BothW4AKit7zxb_litC5ARocqVerifyHarness?AgentSubmission4Spec7Harness=PRODUCER_SIZEc5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocCPROD_CREATE_STACK_Ac5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_malloc<APROD_CREATEK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocAprod_createA_stmtI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6uchain00C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps7afree_MC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:afree_postC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit:aunw_chainC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kitAimplMA_afree_callc5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocBprod_freeA_stmt_atC5ARocqVerifyHarness?AgentSubmission5BothW5ABase;AFREE_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8AFREE_PCC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6UDEPTHc5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_malloc:APROD_FREE".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND, shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.

Section CANSEC1. Context {rc : runConstT}.
Definition AFUZZ_MALLOC : Z := 0x9b17c.     (* [comment removed for export] *)
Definition APROD_CREATE : Z := 0x9ae68.     (* [comment removed for export] *)
Definition APROD_FREE : Z := 0x9aef8.       (* [comment removed for export] *)
Definition APCREATE_RET : Z := 0x9ae98.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition FUZZ_MALLOC_STACK_A : Z := 16 + AMALLOC_STACK.
Definition PROD_CREATE_STACK_A : Z := 32 + FUZZ_MALLOC_STACK_A.

Section Stmts.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fuzz_mallocA_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (s : APS) (LB : list ablock) (n lo : Z) (m : amem)
      (r : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (p : AsanCtrl.aptr) (A : Z) (junk : list byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ r = Some p
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m'
      /\ aps_rest s' = aps_rest s
      /\ ablock_range A n
      /\ AHEAP AI L RNG' (aps_m s') (HB p A n :: LB) m'
      /\ rw_cells bsegs m' A [CB (Z.to_nat n) junk]
      /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7)).

  Definition fuzz_mallocA_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (n lo : Z),
    AHEAP AI L RNG (aps_m s) LB m ->
    mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - FUZZ_MALLOC_STACK_A ->
    bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 ATP ->
    a0 = Z_to_bv 64 n -> 0 < n <= AREQMAX ->
    In [AMALLOC_PC; AFMALLOC_RET] (al_U L) ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
    aps_ok L s ->
    implMA RNG (Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) n) s
           (fuzz_mallocA_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB n lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (Z_to_bv 64 AFUZZ_MALLOC) fc None m (seg_rom bsegs)).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fuzz_mallocA0_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (s : APS) (LB : list ablock) (n lo : Z) (m : amem)
      (r : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (A : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m'
      /\ aps_rest s' = aps_rest s
      /\ match r with
         | None => n = 0 /\ A = 0 /\ aps_m s' = aps_m s /\ AHEAP AI L RNG' (aps_m s') LB m'
         | Some p => exists junk : list byte, 0 < n /\ ablock_range A n /\ AHEAP AI L RNG' (aps_m s') (HB p A n :: LB) m'
                     /\ rw_cells bsegs m' A [CB (Z.to_nat n) junk] /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7))
         end.

  Definition fuzz_mallocA0_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (n lo : Z),
    AHEAP AI L RNG (aps_m s) LB m ->
    mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - FUZZ_MALLOC_STACK_A ->
    bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 ATP ->
    a0 = Z_to_bv 64 n -> 0 <= n <= AREQMAX ->
    In [AMALLOC_PC; AFMALLOC_RET] (al_U L) ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
    aps_ok L s ->
    implMA RNG (Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) n) s
           (fuzz_mallocA0_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB n lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (Z_to_bv 64 AFUZZ_MALLOC) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition prod_createA_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (s : APS) (LB : list ablock) (lo : Z) (dataw sizew : word) (m : amem)
      (r : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (p : AsanCtrl.aptr) (A : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ r = Some p
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m'
      /\ aps_rest s' = aps_rest s
      /\ ablock_range A PRODUCER_SIZE
      /\ AHEAP AI L RNG' (aps_m s') (HB p A PRODUCER_SIZE :: LB) m'
      /\ rw_cells bsegs m' A [C8 dataw; C8 sizew]
      /\ rng RNG' A PRODUCER_SIZE /\ rng RNG' (shad A) (shlen (PRODUCER_SIZE + 7)).

  Definition prod_createA_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (lo : Z),
    AHEAP AI L RNG (aps_m s) LB m ->
    mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - PROD_CREATE_STACK_A ->
    bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 ATP ->
    In [AMALLOC_PC; AFMALLOC_RET] (al_U L) ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
    aps_ok L s ->
    implMA RNG (Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) PRODUCER_SIZE) s
           (prod_createA_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB lo a0 a1 m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (Z_to_bv 64 APROD_CREATE) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition prod_freeA_stmt_at (entry : Z) : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z) (tr : list Z),
    AHEAP AI L RNG (aps_m s) LB m -> In (HB p A n) LB ->
    mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
    bv_unsigned sp + 16 < al_top L ->
    tp = Z_to_bv 64 ATP ->
    a0 = Z_to_bv 64 A ->
    uchain m (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr ->
    In (AFREE_PC :: bv_unsigned ra :: tr) (al_U L) ->
    bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> (length tr <= 28)%nat ->
    bv_unsigned sp mod 16 = 0 ->
    rng RNG lo (al_top L - lo) ->
    aps_ok L s ->
    implMA RNG (afree_M p) s
      (fun _ s' RNG' ms' => aps_rest s' = aps_rest s
         /\ afree_post CI (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma aheap_pres_frame : forall L RNG st LB m m' W lo SP,
    AHEAP AI L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => lo <= fst iv /\ snd iv <= SP) W -> ATOP + 4096 <= lo -> SP <= al_top L ->
    aheap_pres CI LB SP m m'.
Proof.
intros L RNG st LB m m' W lo SP AH MU WM FW BOT TOP.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LAY1 & LAY2 & LAY3 & LAY4 & _).
eapply aheap_pres_of_munch; [exact MU| exact WM|]. intros a Hc.
pose proof (AI_aci_img AI) as CIB.
assert (HA : a < lo \/ SP <= a).
{ destruct Hc as [Hc|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]]; unfold AIMG_HI in *.
- right; lia.
- left. pose proof (CIB iv Hiv). unfold AIMG_HI in *. atop_facts. lia.
- left. pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb). unfold AIMG_HI in *. lia.
- left. rewrite shad_div. unfold ASHOFF.
assert (A47 : a' < 2^47).
{ destruct Ha' as [H|[(iv & Hiv & Hr)|(c & FA & fn & Hb & Hr)]]; [lia| pose proof (CIB iv Hiv); unfold AIMG_HI in *; lia|].
pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb). cbn in *. atop_facts. lia. }
atop_facts. clear - A47 BOT. Z.div_mod_to_equations. lia. }
clear - HA FW. induction W as [|[wlo whi] W IH]; [exact I|]. cbn. inversion FW as [|x l [F1 F2] FW']; subst. cbn in F1, F2.
split; [lia| apply IH; exact FW'].
Qed.

  (* [comment removed for export] *)
  Lemma aheap_pres_fresh : forall L RNG st LB m m' p A n lo SP,
    AHEAP AI L RNG st (HB p A n :: LB) m -> munch [(A, A + n); (lo, SP)] m m' -> wmono bsegs m m' ->
    ATOP + 4096 <= lo -> lo <= SP -> SP <= 2^47 ->
    aheap_pres CI LB SP m m'.
Proof.
intros L RNG st LB m m' p A n lo SP AH MU WM BOT LOSP TOP.
pose proof (AI_block AI _ _ _ _ _ p A n AH (or_introl eq_refl)) as (_ & (BR1 & BR2 & BR3 & BR4) & _).
pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. inversion ND as [|x l NI ND']; subst.
pose proof (AI_aci_img AI) as CIB.
eapply aheap_pres_of_munch; [exact MU| exact WM|]. intros a Hc. cbn [outside].
destruct Hc as [Hc|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
- split; [lia|]. split; [lia| exact I].
- pose proof (CIB iv Hiv). unfold AIMG_HI in *. split; [lia|]. split; [lia| exact I].
- assert (NE : HB p A n <> b) by (intros E; apply NI; rewrite E; exact Hb).
pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB p A n) b AH (or_introl eq_refl) (or_intror Hb) NE) as DJ. cbn [ab_addr ab_size] in DJ.
pose proof (AI_block_bounds AI _ _ _ _ _ b AH (or_intror Hb)) as BB.
split; [lia|]. split; [lia| exact I].
- assert (A47 : 0 <= a' < 2^47).
{ destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA & fn & Hb & Hr)]]; [lia| pose proof (CIB iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
pose proof (AI_block_bounds AI _ _ _ _ _ _ AH (or_intror Hb)). cbn in *. unfold AIMG_HI in *. atop_facts. lia. }
pose proof (shad_in_band a' A47) as SB. pose proof (ablk_clear_band _ _ (shad a') BR1) as CB0. unfold KLS in *.
split; [intros X; apply CB0; [lia| exact X]|].
split; [rewrite shad_div; unfold ASHOFF; atop_facts; clear - A47 BOT H; Z.div_mod_to_equations; lia| exact I].
Qed.

  Theorem fuzz_malloc_proofA : fuzz_mallocA_stmt.
Proof.
unfold fuzz_mallocA_stmt. intros until lo. intros AH MI ST BOT LOS TOPS SP16 TP A0 Hn HUm RSTK RIMG ROK.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LAY1 & LAY2 & LAY3 & LAY4 & _).
pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & GOT & _ & _ & SHB & _).
unfold FUZZ_MALLOC_STACK_A, AMALLOC_STACK in LOS. unfold AREQMAX in *.
unfold Harness.fuzz_malloc. replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
apply implMA_from_evtF.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (RLO : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; lia]).
carve_frame 16%nat ST.
subst a0 tp. unfold AFUZZ_MALLOC.
do 3 zstep.
zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
zstep. zstep. zstep. zstep.
apply evtF_done.
lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
by (eapply (AI_frame AI); [exact AH| exact MU| exact WM| constructor; [left; left; cbn; lia| constructor]])
end.
eapply implMA_bind.
{ eapply (implMA_amalloc_call AI) with (lo := lo) (tr := []); rewrite ?unsigned_lit by lia;
first [ reflexivity | exact AH1 | eassumption | exact ROK
| (apply aunw_data; rewrite ?unsigned_lit by lia; [lia | atop_facts; lia | exact HUm])
| (unfold AMALLOC_PC, AMALLOC_STACK, AREQMAX; cbn; atop_facts; lia)
| (clear - SP16 RSP LOS LAY4 BOT; Z.div_mod_to_equations; lia) ]. }
cbv beta. intros r s' RNG' ms1 [SOE PO].
destruct PO as (LE & u0 & u1 & u2 & xa0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & HPR & RR).
cbn [fst snd] in RR, HPR, ST2, MI2. rewrite ?unsigned_lit in ST2, HPR by lia.
destruct r as [p|]; [| destruct RR].
destruct RR as (A & junk2 & -> & BR & AH2 & BLK & RA & RSA & _).
pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
unfold AFMALLOC_RET. retlit.
assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra])
by (eapply aheap_pres_rw_cells; [exact HPR| eassumption| left; left; cbn; lia]).
apply implMA_ret.
pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTK'.
assert (RLO' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact LE| exact RLO]).
zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
do 3 zstep. zstep.
release_frame FR2 ST2 (bv_unsigned sp).
apply evtF_done. unfold fuzz_mallocA_post. split; [exact LE|].
do 14 eexists. exists m2, p, A, junk2. split; [reflexivity|]. split; [reflexivity|].
split; [exact MI2|]. split; [exact ST2|].
split.
{ eapply aheap_pres_trans.
- eapply (aheap_pres_frame L RNG (aps_m s) LB m _ _ lo (bv_unsigned sp) AH MU WM); [| exact BOT| lia].
constructor; [cbn; lia| constructor].
- eapply aheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]. }
split; [exact SOE|]. split; [exact BR|]. split; [exact AH2|]. split; [exact BLK|]. split; [exact RA| exact RSA].
Qed.


  (* [comment removed for export] *)
  Theorem fuzz_malloc0_proofA : fuzz_mallocA0_stmt.
Proof.
unfold fuzz_mallocA0_stmt. intros until lo. intros AH MI ST BOT LOS TOPS SP16 TP A0 Hn HUm RSTK RIMG ROK.
destruct (Z.ltb_spec 0 n) as [NP|NZ].
- eapply implMA_mono.
  + exact (fuzz_malloc_proofA L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 FR fc m s LB n lo AH MI ST BOT LOS TOPS SP16 TP A0 ltac:(lia) HUm RSTK RIMG ROK).
  + cbv beta. intros r s' RNG' ms' PO. unfold fuzz_mallocA_post in PO. unfold fuzz_mallocA0_post.
    destruct PO as (LE & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & p & A & junk
      & EQ & -> & MI' & ST' & HP & RS & BR & AH' & BLK & RA & RSA).
    split; [exact LE|]. exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', A.
    split; [exact EQ|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HP|]. split; [exact RS|].
    exists junk. split; [lia|]. split; [exact BR|]. split; [exact AH'|]. split; [exact BLK|]. split; [exact RA| exact RSA].
- assert (N0 : n = 0) by lia. subst n.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LAY1 & LAY2 & LAY3 & LAY4 & _).
  unfold FUZZ_MALLOC_STACK_A, AMALLOC_STACK in LOS.
  unfold Harness.fuzz_malloc. rewrite Z.ltb_irrefl. cbv beta iota.
  apply implMA_ret.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  subst a0 tp. unfold AFUZZ_MALLOC.
  do 3 zstep.
  zstep. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].
  do 3 zstep. zstep.
  lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + _) _ |- _ => release_frame H ST (bv_unsigned sp) end.
  apply evtF_done. unfold fuzz_mallocA0_post. split; [apply fp_le_refl|].
  do 15 eexists. exists 0. split; [reflexivity|].
  split; [eassumption|]. split; [exact ST|].
  split.
  { eapply (aheap_pres_frame L RNG (aps_m s) LB m _ _ lo (bv_unsigned sp) AH MU WM); [constructor; [cbn; lia| constructor]| exact BOT| lia]. }
  split; [reflexivity|].
  refine (conj eq_refl (conj eq_refl (conj eq_refl _))).
  eapply (AI_frame AI); [exact AH| exact MU| exact WM| constructor; [left; left; cbn; lia| constructor]].
Qed.

  (* [comment removed for export] *)
  Theorem prod_create_proofA : fuzz_mallocA_stmt -> prod_createA_stmt.
Proof.
intros FMALLOC. unfold prod_createA_stmt. intros until lo. intros AH MI ST BOT LOS TOPS SP16 TP HUm RSTK RIMG ROK.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LAY1 & LAY2 & LAY3 & LAY4 & _).
pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & GOT & _ & _ & SHB & _).
unfold PROD_CREATE_STACK_A, FUZZ_MALLOC_STACK_A, AMALLOC_STACK in LOS.
apply implMA_from_evtF.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (RLO : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; lia]).
carve_frame 32%nat ST.
subst tp. unfold APROD_CREATE.
do 5 zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
apply evtF_done.
lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
by (eapply (AI_frame AI); [exact AH| exact MU| exact WM| constructor; [left; left; cbn; lia| constructor]])
end.
eapply implMA_post_evtF.
{ eapply (FMALLOC L RNG) with (lo := lo) (n := PRODUCER_SIZE) (LB := LB); rewrite ?unsigned_lit by lia;
first [ reflexivity | exact AH1 | eassumption | exact ROK
| (unfold PRODUCER_SIZE, AREQMAX, FUZZ_MALLOC_STACK_A, AMALLOC_STACK; lia)
| (clear - SP16 RSP LOS LAY4 BOT; Z.div_mod_to_equations; lia) ]. }
cbv beta. intros r s' RNG' ms1 PO.
destruct PO as (LE & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & p & A & junk2 & -> & -> & MI2 & ST2 & HPR & SOE & BR & AH2 & BLK & RA & RSA).
rewrite ?unsigned_lit in ST2, HPR by lia.
pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI, PRODUCER_SIZE in *.
unfold APCREATE_RET. retlit.
assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply aheap_pres_rw_cells; [exact HPR| eassumption| left; left; cbn; lia]).
assert (RLO' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact LE| exact RLO]).
destruct (AI_block AI _ _ _ _ _ p A 16 AH2 ltac:(left; reflexivity)) as (_ & _ & _ & _ & BSH & _).
assert (A8 : A mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
pose proof (ablock_unpoisoned m2 A 16 BSH A8 ltac:(lia) ltac:(lia) ltac:(lia)) as UNP.
pose proof (unpoisoned8_rd_off m2 A (A + 16) A 0 UNP ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact A8)) as RD0. rewrite Z.add_0_r in RD0.
pose proof (unpoisoned8_rd_off m2 A (A + 16) A 8 UNP ltac:(lia) ltac:(lia) ltac:(clear - A8; Z.div_mod_to_equations; lia)) as RD8.
unfold ASHOFF in RD0, RD8.
pose proof (munch_refl [(A, A + 16); (lo, bv_unsigned sp)] m2) as MU2. pose proof (wmono_refl bsegs m2) as WM2.
change (Z.to_nat 16) with 16%nat in BLK.
pose proof (rw_cells_split_CB bsegs m2 A [] 16 junk2 [] [8%nat; 8%nat] BLK eq_refl) as BLK2. cbn [mk_CB_cells app] in BLK2.
clear BLK.
zstep. if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by lia; lia|].
zstep. zstep. if_cases KA; zify_cond KA;
[exfalso; rewrite ?unsigned_lit in KA by lia; change 7 with (Z.ones 3) in KA; rewrite Z.land_ones in KA by lia; lia|].
zstep. zstep. zstep. rewrite zxb_lit by lia. zstep. if_cases K1; zify_cond K1; [exfalso; clear - K1; lia|].
zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (UNP0 : unpoisoned mx A (A + 16))
end.
{ pose proof (ablk_disj_band _ _ BR1) as DB. unfold KLS in DB. eapply unpoisoned_munch; [exact UNP| exact MU2|].
rewrite !shad_div. unfold ASHOFF. cbn [disjoint_from]. atop_facts.
split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia| exact I]. }
clear RD8. pose proof (unpoisoned8_rd_off _ A (A + 16) A 8 UNP0 ltac:(lia) ltac:(lia) ltac:(clear - A8; Z.div_mod_to_equations; lia)) as RD8.
unfold ASHOFF in RD8.
zstep. zstep. zstep. zstep. rewrite zxb_lit by lia. zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|].
zstep.
do 4 zstep. zstep.
release_frame FR2 ST2 (bv_unsigned sp).
zstep.
apply evtF_done. unfold prod_createA_post. split; [exact LE|].
do 14 eexists. eexists _, p, A. split; [reflexivity|]. split; [reflexivity|].
split; [eassumption|]. split; [exact ST2|].
split.
{ eapply aheap_pres_trans; [eapply (aheap_pres_frame L RNG (aps_m s) LB m _ _ lo (bv_unsigned sp) AH MU WM); [constructor; [cbn; lia| constructor]| exact BOT| lia]|].
eapply aheap_pres_trans; [eapply aheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]|].
eapply aheap_pres_fresh; [exact AH2| exact MU2| exact WM2| exact BOT| lia| lia]. }
split; [exact SOE|]. split; [exact BR|].
split; [eapply (AI_frame AI); [exact AH2| exact MU2| exact WM2|];
constructor; [right; left; exists (HB p A 16); split; [left; reflexivity| cbn; lia]| constructor; [left; left; cbn; lia| constructor]]|].
split; [exact BLK2|]. split; [exact RA| exact RSA].
Qed.

  (* [comment removed for export] *)
  Theorem prod_free_proofA : prod_freeA_stmt_at APROD_FREE.
Proof.
unfold prod_freeA_stmt_at. intros until tr. intros AH HIN MI ST BOT LOS TOPS TP A0 UC UIN NS8 RA4 RAPC LEN SP16 RSTK ROK.
apply implMA_from_evtF. unfold APROD_FREE. zstep. apply evtF_done.
eapply (implMA_afree_call AI L RNG) with (tr := tr); try eassumption.
apply aunw_chain; assumption.
Qed.
End Stmts.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
