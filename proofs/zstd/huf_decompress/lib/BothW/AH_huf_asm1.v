(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer HufHarness.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AProg_kit AHarness_iface
     AH_huf_kit AH_huf_iface AH_huf_prod AH_huf_malloc AH_huf_draws AH_huf_split.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AH_huf_asm1 () := "C46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission4Spec7Harness;fuzz_mallocC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;implMA_bindC47Corelib4Init9Datatypes3appI46Stdlib5Lists4List5NoDup00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit<harness_topFC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIK46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadK47Corelib4Init5Logic2or02I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgK47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_block_boundsC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00c5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm15geomAI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission5BothW5ABase>ablk_disj_bandC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_blocks_nodupC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceBAI_blocks_disjointC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begK47Corelib4Init5Logic2ex01C35stdpp4base6lookupI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface6AEMPTYC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableK47Corelib4Init9Datatypes4bool02C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_split9hMA_stateC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_split8fz_restAC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface>fuzz_oneA_postC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA9fuzz_oneAC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit?fse_rt_of_aheapK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface2HUC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface;payload_atAI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3AStC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA<new_handlerAC5ARocqVerifyHarness?AgentSubmission4Spec7Harness7dt_sizeC5ARocqVerifyHarness?AgentSubmission4Spec7Harness9dbuf_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj1K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit8cr_stackC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?magree_of_munchc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm1:pag_stack0C5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree;magree_monoC5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocAprod_createA_postC5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocBfuzz_malloc_proofAC5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocBprod_create_proofAC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5fp_leC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit8aps_restC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:aheap_presC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceCaheap_pres_rw_cellsC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceCaheap_pres_bytes_atC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit9aca_monoAC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree<magree_transC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission5BothW6ABytes<rw_cells_appC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission3Lib3Tac7sum_natC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kitAablock_unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow>unpoisoned_nilC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5nshadC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA9rng_fp_leC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C46Stdlib9micromega;ZifyClasses:impl_morphC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow9nshad_divC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;shlen_nshadC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_draws8hB_postAC5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod@prod_u32r_proofAC5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod@prod_i32r_proofAC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_draws=phaseB_proofAC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness9huf_drawsC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness6hp_mtlC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness8DT_BYTESC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness7hp_dbufC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness7hp_restC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:hp_streamsC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:hp_symbolsC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface8prod_atAC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit8cr_blockc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm1?pag_outside_blkC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kitAmagree_munch_stepK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness?huf_draws_rangeC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocAfuzz_mallocA_postC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;aps_ok_restC4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA;fp_le_transC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z8max_specC5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocBfuzz_mallocA0_postC5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocCfuzz_malloc0_proofAK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit6FZRB13C47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit@implMA_from_evtFC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_monoC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_splitCfuzz_oneA_split_hufC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6implMAC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC46Stdlib9micromega;ZifyClasses5mkappK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib9micromega;ZifyClasses6mkapp2C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC56Stdlib6ZArith6BinInt1Z3maxC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase8AFREE_PCI47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps9amalloc_MK4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00C5ARocqVerifyHarness?AgentSubmission4Spec7Harness=PRODUCER_SIZEC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps:AAllocAsanC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface;AFUZZ_ENTRYC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface>AHARNESS_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase:AMALLOC_PCC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<AFMALLOC_RETC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<AFREE_DT_RETC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<AFREE_WK_RETC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<AFREE_DB_RETC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface:AFREEP_RETc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm1=payload_factsC5ARocqVerifyHarness?AgentSubmission4Spec7Harness9WKSP_SIZEC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib7Numbers7BinNums1N01C5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocCPROD_CREATE_STACK_AI5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_draws=PC_HB_EXIT_RAC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_draws?AFUZZ_MALLOC_HBI5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:huf_params00C5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness@HUF_TABLELOG_MAXC5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_mallocCFUZZ_MALLOC_STACK_AC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop03C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_split6PC_HMAC5ARocqVerifyHarness?AgentSubmission4Spec7Harness=WKSP_SIZE_val".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac cl := repeat match goal with H : _ |- _ => clear H end.
Ltac h_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [cl; lia| reflexivity]) end.
Local Ltac xsz := cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length FZRB13].

Section CANSEC1. Context {rc : runConstT}.

Section First.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  (* [comment removed for export] *)
  Variables (L : alayout) (RNG0 : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (FR : bvmap 5 word) (fc : bv 32) (s : APS) (LB : list ablock) (D : Z) (pl : list Z) (lo : Z) (m0 : amem).
  Notation SP := (bv_unsigned sp).
  Hypothesis AH0 : AHEAP AI L RNG0 (aps_m s) LB m0.
  Hypothesis HLB : forall b, In b LB -> exists p A n, b = HB p A n.
  Hypothesis PAY : AHarness_iface.payload_atA LB D pl.
  Hypothesis PAYB : bytes_at bsegs m0 D (map (Z_to_bv 8) pl).
  Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
  Hypothesis D16 : D mod 16 = 0.
  Hypothesis SZ : zlength pl < 2^26.
  Hypothesis ST0 : stk bsegs m0 lo SP.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - AHARNESS_STACK.
  Hypothesis SPG : SP + ATRUN_DEPTH = al_sp0 L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis MI0 : mem_inv bsegs m0.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis HUL : HU L.
  Hypothesis RSTK0 : rng RNG0 lo (al_top L - lo).
  Hypothesis RI0 : rng_aimg RNG0.
  Hypothesis RISH0 : rng_aimg_sh RNG0.
  Hypothesis AOK : aps_ok L s.

  Notation POSTF := (fuzz_oneA_post AI L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m0).

  (* [comment removed for export] *)
  Lemma geomA : 0 <= SP /\ SP + 16 <= al_top L /\ SP < 2^64 /\ al_top L <= 2^47 /\ ATOP + 4096 + 16384 <= SP.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_asm1 ()) ["CANSEC1"; "First"] "h01Hh14__x1h22Hah37__arithh44__p1h57__sat17h67__sat18h77__sat19h87__sat20h97__sat21h:7__sat22h;4__ffh<7__sat23h=7__sat24h>7__sat25h?8__varmaph@5__withA4__x2hB4__p2hC4__p3hD4__x3hE4__x4hF3LY1hG3LY2hH3LY3hI3LY4hJ3RSPhK2T1hL2T2hM2_Hp%0p;1p;2p;3p;4p;8p;7p;6p-1p10000p4p710R0p8p1000Gp4p7211p10018p4p710R1p8p1001Vp4p70R2P0p8P2p1002Mp4p710p8P2p1002ip4p710p8P2p1003Gp4p7210p8P2p1003dp4p7210p8P2p1004ap4p7210p8P2P1p8P2p1005Vp4p710p8P2p1006Vp4p710p8P2p10073p4p710p8p1007Op4p7210P1p8g008;j10Tg008`j1UTg009>j2\Tg00:1j2{Tg00:[j1eTg00;Dj27Tg00;`R1j21Tg00<;j1^Tg00=9j15Tg00=^j1nTg00>Tj23Tg00?0j1<Tg00?Nj2NTg00@?j2OTg00@_j2MTg00AGj2PTg00Adj3RTg00BHj1`Tg00Bhj1TTg00CHj2HTg00Cfj1_Tg00DDj1]Tg00Doj2STg00ERj2GTg00F5j1[Tg00FWj2ZTg00G9j2YTg00GSj2XTg00H?j3DTg00HYj3zTg00I8j4yTg00Ijj4xTg00Jlj24Tg00KIj1wTg00L@j1qTg00M<j8pTg00N>j1oTg00O5j2WTg00ORj1mTg00PPj1lTg00QMj1kTg00RBj2jTg00Rbj1iTg00SBj2hTg00S\j1gTg00TTj1fTg00U2j3VTg00UUj4JTg00V@j1KTg00V_j2ITg00WHj3QTg00X1j2dTg00X]j3cTg00Y=j3bTg00Y`j4LTg00Z;j7aTg00Z_j6rTg00[Cj7sTg00[gj8tTg00\Kj4uTg00\ij3vTf0R2#0#0p=6g00]LR0/32p=2%52#5p=E%52#5#5#5p=>%02#0#0#0p=B%02#0#0#0#0#0#0#0p=A%02#<p=;g00]jR3f1R4g00^HP2CJp==P4g00^oR5g00_NR6P6g00_nR7P2g00`NFap=8P4P5P6P6P7P2Erp=Ff2R8P5P6P6P7P4P2Fsp=Cf3R9P5P6P6P7P8P4P2Gtp=9P3P8P4P2Cup=@1S32p=:Av342p=?g00`nR5#0R:#0R;#6R<#6R=#UR>p,2spR?'\1{>?R?#2R@%e>,7?'1p,1LRAP?p,3SPGp,2rcRB#^RC%55RD#ERE#5#E#>#>RF#0#>#>#6#B#A#A#;RG%nBRH'3%5F#>#>#6#B#A#A#;,3HS00'1RF%<<R<,N?RI%2<RJ1O?<#2[\@RK%<:RL%<=RM'MRN170LRO%2M1PLMRP,70[[RQ%2LRRg00aSRSARLM4UW2RM%2P\S^2RRT%0DRD#5#;RU,MLRV%2U1PLURW,70[\ORXARLU4VSX2RRU%2W\S^2RRWp,1DRY/N<RZ%2Y1OY<#2\J[RJp-0RYg00aoR[#`R\%T[R]1H34R^%_3R_%]3R`1S30Ra1G35R5'=,8`Rb1F`9Rc5C`%[6R6PbC91Z`7R7P2P8g00b[Rbg00c;Rd'Y1X28=DbddAz304CyRdb;b?b@X13W4Rb%22/14%24[^13^4YReP217?PRfP?f8RgO3b3b5b6b7b8b9b:b0Cx14?<%wARh'3Ri%6D#;RD,4?%6=#BR=#<Rj'4,7hRk'1P1PiPk%5:Rl#5Rm#ERn#<Ro,PLRp,3hRq14Hj%6=R=#<Rr'4/3?Rs'1Rt,1fRu,1iRv,1@RwP2PBp,2AIPAp,4RNG0p,1s#qRBp,2LBp,2m0p,3AH0Gp%oARx%A=#;R='4=D3hRy1OhjRz=D30R{%0lRl#0#6#;R|,WH/3x%0E#E#B#;,4H,3xRE'1R}%mB%lA5D3%T3%kA'jg00c[#i'hg00dQ%gARA'3%Bm#5#6#5#0#6#A#;,4A/3H'1'1'1RA'1Rm,1qRB'1R~'1P1PyP~PwP2P1P{PBPwP2P1PqPmPwP2P1P}PAPwP2P@PvPCPFPIPK1MLoRv%2o170p[\OROARLo4VSX2RRo%2p\S^2RRRPNPQPMPT1NhjRS%2h%2j%2z[[RzPVPXPUPWPZPJPbPeP2PfP?fQReO3b3b5b6b7b8b9b:b<b=b>b0PiPuPCPFPIPKPvPOPoPRPNPQPMPTPSPzPVPXPUPWPZPJP\P]1H38%f3Ru7@4P_P`%:<,?51G3:R:'=,8`RbP6PbC9P7Pdb;b?b@X13XA3142</34144</38[^13^A3P2PhP?fMO3b3b5b6b7b8b9b:b<b=b>b0PfPtPCPFPIPKPvPOPoPRPNPQPMPTPSPzPVPXPUPWPZPJP\P]P^P_P`P3P5g00eIRt%:LRL=V3>CJ,8`R>9C`cP6P>C9P7Pdb;b?b@X13X4Y172P,14174P[^13^4YP2P@P?PeO3b3b5b6b7b8b9b:b<b=b>b0PqPsPCPFPIPKPvPOPoPRPNPQPMPTPSPzPVPXPUPWPZPJP\P]P^P_P`%Un9V3L,=5,8`RLP6PLC9P7Pdb;b?b@X13132p134p[^13P2Phf@O2b3b5b6b7b8b9b:b<b=b>b0PCPFPIPKPvPOPoPRPNPQPMPTPSPzPVPXPUPWPZPJg00f0RJ#K#KRZ#KRW#K,I31I3W1I3Z1I3J5Q35Q35Q3g00fO'd=c[\P]f4R],H3?@]u9@u81H39?@]u?@]u7@4P_P`%:G/=5,8`f6R_,F`5C`P6P`%:|9b351G3lRl'=,8`f7,F`5C`P6P`P3%:=,?lg00g;%5;,G3R;CJ,8`P6P`P3P;Pt%:D,?:%:jRt'?CJ,8`P6P`1=a:,8`1F`g5C`P61?5t%:r'?/=:,8`C9C9C9C9C9P7Pdb;b?b@X13XA3XD3XE3X4YXBYXCY13G2/1]1W4|/3]/1_f5R|/4==D3]14]D/4j,7|%2|f:R]'114|j/4r/3_[[[[[^13^A3^D3^E3^4Y^BY^CYP2PfPEQ00PxPhP?PHP]f<fHfLPeO<b3b5b6b7b8b9b:b<b=b>b0CLCLCLCLXMAXI}P4P2O2n2001000000121000000X0mXHqP4P2O2n2001000000121000000X0BXG{P4P2O2n2001000000121000000X0~XFyP4P2O2n2001000000121000000b0XLkXKiP4P2O2n2001000000121000000b0bJo"). Qed.

  (* [comment removed for export] *)
  Lemma pag_stack0 : forall a, aclient_addr CI LB SP a -> a < lo \/ SP <= a.
Proof.
intros a Ha. pose proof geomA as (G1 & G2 & G3 & G4 & _). pose proof atop_range as ATR. unfold AHARNESS_STACK in LOS.
destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
- right; lia.
- pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. cbn in Hr. left; lia.
- pose proof (AI_block_bounds AI _ _ _ _ _ _ AH0 Hb) as BB. cbn in Hr. left; lia.
- assert (A47 : 0 <= a' < 2^47).
{ destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; cbn in Hr; lia|].
destruct (HLB _ Hb') as (p & A & N & E'). discriminate. }
left. rewrite shad_div. unfold ASHOFF. clear - A47 ATR BOT. Z.div_mod_to_equations. lia.
Qed.

  (* [comment removed for export] *)
  Lemma pag_outside_blk : forall RNGx st mx p A n a,
    AHEAP AI L RNGx st (HB p A n :: LB) mx -> ablk A (A + n) ->
    aclient_addr CI LB SP a -> ~ (A <= a < A + n).
Proof.
intros RNGx st mx p A n a AH BK Ha Hin. pose proof geomA as (G1 & G2 & G3 & G4 & G5). pose proof atop_range as ATR.
pose proof (ablk_lin _ _ BK) as (BL1 & BL2 & BL3 & BL4).
destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
- lia.
- pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. cbn in Hr. lia.
- pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. inversion ND as [|x l NI ND']; subst.
  assert (NE : b <> HB p A n) by (intros ->; contradiction).
  pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH (or_intror Hb) (or_introl eq_refl) NE) as DJ. cbn in DJ. lia.
- assert (A47 : 0 <= a' < 2^47).
  { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; cbn in Hr; lia|].
    destruct (HLB _ Hb') as (p' & A' & N' & E'). discriminate. }
  rewrite shad_div in Hin. unfold ASHOFF, ablk, AIMG_HI, KLS in *. clear - A47 ATR BK Hin. Z.div_mod_to_equations. lia.
Qed.

  (* [comment removed for export] *)
  Lemma payload_facts : (pl = [] /\ D = AEMPTY) \/ (exists p, In (HB p D (zlength pl)) LB /\ 0 < zlength pl /\ ablk D (D + zlength pl)).
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_asm1 ()) ["CANSEC1"; "First"] "p'0h02chh11Hh21ph32E1h42E2h53Hinh62NZh72R1h83RHIh93RLOh:2_Hh;3_H0h<3_H1h=1ai001xp;1p;2p;3p;<p;4p;6g014Hj1=Tg01RFj2^Tg015Aj3<Tg00nZj39Tg00;Dj2]Tg00;`R0j20Tg016:R1j27Tg00Bhj1TTg00BHj1PTg00H?j31Tg00lNR2j2BTg00Jlj2:Tg01HRj3HTg00L@j1\Tg01S>l<VTg00?0j18Tg00>Tj23Tg01T?j3UTg01U<j3@Tg00lhj1FTg00=9j1ETg01Uoj1DTg01Vhj3STg01Wfj4CTg01G2j1RTg01XXj4OTg01Xlj4NTg01YEj1MTg01Z>j2LTg01Z`j1KTg01[]j1JTg01\Zj1ITg00@?j2>Tg00O5j2QTg00=^j1[Tg00Y`j4ATg01][j4ZTg00m`j3WTg0104j3XTg01^5j6YTg008;j1GTg001VR3g01^IR4f3R5f2R6f1R7f0R8EYp=51748p=4%G8#Gp=6g00]jR9g00]LR:718p=?f41078,06,05'0p=21078,06p=;p,3PAYg01AnR;%=8p,1DR<p,2plR=,^9R>3<p,2LBR?39R@1]:>RA'0RBX23RC,73RD%T9%P971=R=g01_D919<RE'0RF'BP2PDPFp,2rcR21:<>RG7H<RH,0ARI,0@X23R@,73RJ,BFRKP8P1P3PCPKP8P0%=7?<<>=9;?PAPKP8%=5?<<>=9;?P3P@f5R@%=@?<<>=9;?PIP7PAPHP8P2p,2AIp,1Lp,4RNG0RIp,1s#\R;P?p,2m0R?P@P<P>p,3AH0P7M<Vg00`nR@#8/3>g01`D,3>'0R5AU2<>RCA@I<>R1%F<%E@#E#8,:>#D5@IRLAS?<>RMg01a<RNP?P<P>CCRO%R4RPg01b1RQg01bORRg01bhRSP4CORTPQPRPSP4CNRSf6%M;R;C51L48RR31%K8=19>g00b[%J>g01cF31%I7919<['0RQ'0X04#4%6@#6R@#6RU#6#6#6#8RV,>7#?1>8V#?%8URU,:7/3<1:GU/38%F7RU1Q87#DRV5@IPNP?PUPVCC'0D2X89,79X99,79R9'03;D2P0P5PCP1PLPMPTPSf7P;C5=1PR/0QX04#4=;O9D2PHP8PCP1PLPMPTPSf:P;C5=1PR/0QX04#4=;O9D2P0PCP1PLPMPOPTPSf;P;C5=1PR/0QX04#4/09D2PHP8P0PH13:>%[2,3G%8@,><#?3;R<P1PLPMPOPTPSf?P;C5=1PR/0QX04#4/09D2PH[P8P1PLPMPOPTPSfBP;C5=1PR/0QX04#4/09D2P6W<X;<X7HP7P8O2n2001000000121000000X1CP7P8O2n2001000000121000000W1X:5P7P8O2n2001000000121000000b=CACACZ9WFJX6AW5P7P8O2n2001000000121000000X1BX23P7P8O2n2001000000121100000X1DP8O1P0P=PEPKP8P=PEP7P8CA9XFJX4EX3=P7P8O2n2001000000120000000X1FP8O1n200100000021100010000b2o"). Qed.

  Theorem fz_firstA : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (forall producer dt wksp dBuf s' RNG1 ms,
       hMA_state AI L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 producer dt wksp dBuf s' RNG1 ms ->
       implMA RNG1 (fz_restA producer dt wksp dBuf) s' POSTF ms) ->
    implMA RNG0 (fuzz_oneA AAllocAsan pl) s POSTF
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (zlength pl)) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m0 (seg_rom bsegs)).
Proof.
intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 K.
pose proof geomA as (G1 & G2 & G3 & G4 & G5). pose proof atop_range as ATR. pose proof LOS as LOS'. unfold AHARNESS_STACK in LOS'.
pose proof (AI_rtcells AI _ _ _ _ _ AH0) as (RC1 & RC2 & RC3 & RC4 & RC5 & RC6 & RC7 & RC8 & RC9 & RCX).
pose proof (fse_rt_of_aheap AI _ _ _ _ _ AH0) as (GOT0 & _ & _ & SHB0 & _).
rewrite fuzz_oneA_split_huf.
apply implMA_from_evtF.
assert (DLO : D + zlength pl <= lo).
{ destruct payload_facts as [[E1 E2]|(pd & IND & LEN & BLD)];
  [subst pl D; unfold AEMPTY, zlength; cbn [length Z.of_nat]; lia
  | unfold zlength in *; pose proof (ablk_lin _ _ BLD); lia]. }
pose proof (fun m' (H : munch [(lo, SP)] m0 m') => bytes_at_transport _ _ _ _ _ _ PAYB H
  ltac:(cbn [disjoint_from]; rewrite length_map; unfold zlength in DLO; split; [left; lia| exact I])) as PAYT.
pose proof (munch_refl [(lo, SP)] m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
pose proof ST0 as ST.
carve_frame 128%nat ST.
unfold AFUZZ_ENTRY.
do 22 zstep.
match type of FR0 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?r) =>
  pose proof (proj1 (rw_cells_app bsegs _ _ [c1; c2; c3] r) FR0) as (FRA1 & FRB1) end.
clear FR0. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB1.
apply evtF_done.
lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
  assert (AH1 : AHEAP AI L RNG0 (aps_m s) LB mx)
  by (eapply (AI_frame AI); [exact AH0| exact MU| exact WM| constructor; [left; left; cbn; lia| constructor]])
end.
eapply implMA_bind.
{ eapply (prod_create_proofA AI (fuzz_malloc_proofA AI)) with (LB := LB) (lo := lo); rewrite ?unsigned_lit by lia;
  first [ reflexivity | exact AH1 | eassumption | exact AOK | exact (proj1 HUL)
        | (unfold PROD_CREATE_STACK_A, FUZZ_MALLOC_STACK_A, AMALLOC_STACK; lia)
        | (clear - SP16; Z.div_mod_to_equations; lia)
        | (eapply rng_sub'; [exact RSTK0| lia]) ]. }
cbv beta. intros r s1' RNG1 ms1 PO.
destruct PO as (LE1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & pP & P & -> & -> & MI2 & ST2 & HPR2 & SOE1 & BR & AH2 & PRC & RP & RPS).
rewrite ?unsigned_lit in ST2, HPR2 by lia. h_retlit.
unfold PRODUCER_SIZE in *.
pose proof (rng_fp_le _ _ _ _ LE1 RI0) as RI1.
pose proof (rng_fp_le _ _ _ _ LE1 RISH0) as RISH1.
pose proof (rng_fp_le _ _ _ _ LE1 RSTK0) as RSTK1.
pose proof (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_introl eq_refl)) as (PB1 & PB2 & PB3 & PB4 & PB5 & _).
pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as NDP. apply NoDup_cons_iff in NDP. destruct NDP as (NIP & _).
pose proof (fse_rt_of_aheap AI _ _ _ _ _ AH2) as (GOT2 & _ & _ & SHB2 & _).
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1
  ltac:(left; left; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - G2 G4; lia)) as FRA2.
assert (DF : (pl = [] /\ D = AEMPTY \/ ablk D (D + zlen pl))
   /\ D + zlen pl <= ATOP /\ 0 <= D
   /\ (D + zlen pl <= P \/ P + 16 <= D)
   /\ rng RNG1 D (zlen pl) /\ rng RNG1 (shad D) (nshad (zlen pl))
   /\ unpoisoned m2 D (D + zlen pl) /\ bytes_at bsegs m2 D (map (Z_to_bv 8) pl)).
{ pose proof (ablk_lin _ _ (proj1 PB2)) as PLN. unfold AIMG_HI in PLN.
  destruct payload_facts as [[E1 E2]|(pd & IND & LEN & BLD)].
  - subst pl D. unfold AEMPTY in *. cbn [length map Z.of_nat].
    split; [left; split; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [eapply rng_sub; [exact RI1| lia| lia]|].
    split; [eapply rng_sub; [exact RISH1| |]; unfold shad, nshad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; lia|].
    split; [hnf; split; [lia| split; [lia| intros ? ?; exfalso; lia]]|].
    split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
  - unfold zlength in *.
    pose proof (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_intror IND)) as (QB1 & QB2 & QB3 & QB4 & QB5 & _).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 (or_introl eq_refl) (or_intror IND)
      ltac:(intro E; rewrite E in NIP; exact (NIP IND))) as DJ. cbn [ab_addr ab_size] in DJ.
    destruct QB2 as (QA1 & QA2 & QA3 & QA4). pose proof (ablk_lin _ _ QA1) as QL.
    split; [right; exact BLD|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact QB3|].
    split; [exact QB4|].
    split; [eapply ablock_unpoisoned; [exact QB5| clear - QA4; Z.div_mod_to_equations; lia| lia| lia| lia]|].
    eapply aheap_pres_bytes_at; [exact HPR2| |].
    + exact (PAYT _ MU).
    + right; left; exists (HB pd D (Z.of_nat (length pl))); split; [exact IND| cbn [ab_addr ab_size]; rewrite length_map; lia]. }
destruct DF as (DLOC & DTOP & D0 & DP & RD & RDS & UND & PL2).
unfold zlength in *.
assert (P8 : P mod 8 = 0) by (destruct PB2 as (_ & _ & _ & P16); clear - P16; Z.div_mod_to_equations; lia).
pose proof (ablk_lin _ _ (proj1 PB2)) as PLN0. unfold AIMG_HI in PLN0.
eapply implMA_evtF.
{ eapply phaseB_proofA with (U32R := prod_u32r_proofA) (I32R := prod_i32r_proofA prod_u32r_proofA) (lo := lo);
  first [ exact MI2 | exact ST2 | exact PRC | exact PL2 | exact GOT2 | exact SHB2 | exact UND | exact FRA2
        | exact PLB | exact DLOC | exact DP | exact RD | exact RDS | exact RI1 | exact RP | exact RPS
        | exact (proj1 PB2) | exact BOT | exact SZ | exact P8
        | (eapply rng_sub; [exact RSTK1| lia| lia])
        | (eapply ablock_unpoisoned; [exact PB5| exact P8| lia| lia| lia])
        | (clear - SP16; Z.div_mod_to_equations; lia) | lia ]. }
intros ms' HB.
destruct HB as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15
  & f1 & f2 & f3 & f4 & f5 & m3 & -> & F1 & F2 & F3 & F4 & F5 & MU3 & WM3 & MI3 & ST3 & PRC3 & FRA3).
assert (AH3 : AHEAP AI L RNG1 (aps_m s1') (HB pP P 16 :: LB) m3).
{ eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
  constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
  - right; left; exists (HB pP P 16); split; [left; reflexivity| cbn [ab_addr ab_size]; lia].
  - left; left; lia.
  - left; left; lia. }
pose proof (dt_size_range pl ltac:(unfold zlength; lia)) as DTR.
eapply implMA_bind.
{ eapply (fuzz_malloc_proofA AI) with (lo := lo) (LB := HB pP P 16 :: LB); rewrite ?unsigned_lit by lia;
  first [ exact AH3 | exact MI3 | exact ST3 | exact BOT | exact TP | exact (proj1 HUL) | exact RI1 | exact RSTK1
        | exact (aps_ok_rest _ _ _ SOE1 AOK)
        | (unfold FUZZ_MALLOC_STACK_A, AMALLOC_STACK; lia)
        | (clear - SP16; Z.div_mod_to_equations; lia)
        | (f_equal; unfold dt_size, HufHarness.huf_dt_bytes; rewrite Zlength_correct; reflexivity)
        | (unfold AREQMAX; lia) | lia ]. }
cbv beta. intros r1 s2' RNG2 ms2 PO1.
destruct PO1 as (LE2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m4 & pd & DT & jdt
  & -> & -> & MI4 & ST4 & HPR4 & SOE2 & BRD & AH4 & JDT & RDT & RDTS).
rewrite ?unsigned_lit in ST4, HPR4 by lia. unfold PC_HB_EXIT_RA. h_retlit.
assert (DTE : dt_size pl = DT_BYTES (hp_mtl (huf_draws pl (zlen pl))))
  by (unfold dt_size, HufHarness.huf_dt_bytes; rewrite ?Zlength_correct; reflexivity).
rewrite DTE in *.
apply implMA_from_evtF.
do 4 zstep.
apply evtF_done.
eapply implMA_bind.
{ eapply (fuzz_malloc_proofA AI) with (lo := lo) (LB := HB pd DT (DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))) :: HB pP P 16 :: LB);
  rewrite ?unsigned_lit by lia;
  first [ exact AH4 | exact MI4 | exact ST4 | exact BOT | exact TP | exact (proj1 HUL)
        | exact (rng_fp_le _ _ _ _ LE2 RI1) | exact (rng_fp_le _ _ _ _ LE2 RSTK1)
        | exact (aps_ok_rest _ _ _ (eq_trans SOE2 SOE1) AOK)
        | (unfold FUZZ_MALLOC_STACK_A, AMALLOC_STACK; lia)
        | (clear - SP16; Z.div_mod_to_equations; lia)
        | (rewrite WKSP_SIZE_val; reflexivity)
        | (rewrite WKSP_SIZE_val; unfold AREQMAX; lia) | lia ]. }
cbv beta. intros r2 s3' RNG3 ms3 PO2.
destruct PO2 as (LE3 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m5 & pw & W & jw
  & -> & -> & MI5 & ST5 & HPR5 & SOE3 & BRW & AH5 & JW & RW & RWS).
rewrite ?unsigned_lit in ST5, HPR5 by lia. h_retlit. rewrite WKSP_SIZE_val in *.
assert (DBE : dbuf_size pl = hp_dbuf (huf_draws pl (zlen pl)))
  by (unfold dbuf_size, HufHarness.huf_dbuf; rewrite ?Zlength_correct; reflexivity).
pose proof (dbuf_size_range pl ltac:(unfold zlength; lia)) as DBR.
rewrite DBE in *.
apply implMA_from_evtF.
do 3 zstep.
apply evtF_done.
eapply implMA_bind.
{ eapply (fuzz_malloc0_proofA AI) with (lo := lo)
    (LB := HB pw W 8704 :: HB pd DT (DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))) :: HB pP P 16 :: LB);
  rewrite ?unsigned_lit by lia;
  first [ exact AH5 | exact MI5 | exact ST5 | exact BOT | exact TP | exact (proj1 HUL)
        | exact (rng_fp_le _ _ _ _ LE3 (rng_fp_le _ _ _ _ LE2 RI1))
        | exact (rng_fp_le _ _ _ _ LE3 (rng_fp_le _ _ _ _ LE2 RSTK1))
        | exact (aps_ok_rest _ _ _ (eq_trans SOE3 (eq_trans SOE2 SOE1)) AOK)
        | (unfold FUZZ_MALLOC_STACK_A, AMALLOC_STACK; lia)
        | (clear - SP16; Z.div_mod_to_equations; lia)
        | reflexivity
        | (unfold AREQMAX, BUFF_MAX, HufHarness.DBUF_MAX in *; lia) | lia ]. }
cbv beta. intros r3 s4' RNG4 ms4 PO3.
destruct PO3 as (LE4 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m6 & DST
  & -> & MI6 & ST6 & HPR6 & SOE4 & RM).
rewrite ?unsigned_lit in ST6, HPR6 by lia. h_retlit.
pose proof (fp_le_trans _ _ _ (fp_le_trans _ _ _ (fp_le_trans _ _ _ LE1 LE2) LE3) LE4) as LE.
assert (SOE : aps_rest s4' = aps_rest s) by (rewrite SOE4, SOE3, SOE2, SOE1; reflexivity).
Local Ltac crb k := eapply cr_block; [ k | cbn [ab_addr ab_size]; lia
  | cbn [ab_addr ab_size cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Local Ltac crs := first
  [ (apply cr_stack; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
  | crb ltac:(left; reflexivity) | crb ltac:(right; left; reflexivity) | crb ltac:(right; right; left; reflexivity) ].
Local Ltac trc H HP := let T := fresh "T" in
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HP H ltac:(crs)) as T; clear H; rename T into H.
unfold prod_atA in PRC3.
trc FRB1 HPR2.
replace (SP + -128 + Z.of_nat 24) with (SP + -104) in FRB1 by lia.
pose proof (rw_cells_transport bsegs _ m2 m3 _ _ FRB1 MU3 WM3
  ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as FRB3.
clear FRB1. rename FRB3 into FRB1.
trc FRB1 HPR4. trc FRB1 HPR5. trc FRB1 HPR6.
trc FRA3 HPR4. trc FRA3 HPR5. trc FRA3 HPR6.
trc PRC3 HPR4. trc PRC3 HPR5. trc PRC3 HPR6.
trc JDT HPR5. trc JDT HPR6.
assert (PLX : forall LBx SPx mx my, aheap_pres CI LBx SPx mx my -> (forall b, In b LB -> In b LBx) ->
    bytes_at bsegs mx D (map (Z_to_bv 8) pl) -> bytes_at bsegs my D (map (Z_to_bv 8) pl)).
{ intros LBx SPx mx my HP INC HBY. destruct payload_facts as [[E1 E2]|(pd0 & IND & LEN & BLD)].
  - subst pl. destruct HBY as (HB1 & HB2 & _). split; [exact HB1| split; [exact HB2| intros i Hi; cbn in Hi; lia]].
  - eapply aheap_pres_bytes_at; [exact HP| exact HBY| ].
    eapply cr_block; [exact (INC _ IND)| cbn [ab_addr ab_size]; lia| cbn [ab_addr ab_size]; rewrite length_map; unfold zlength in *; lia]. }
pose proof (bytes_at_transport bsegs _ m2 m3 _ _ PL2 MU3 ltac:(cbn [disjoint_from]; rewrite length_map; lia)) as PL3.
clear PL2. rename PL3 into PL2.
apply (PLX _ _ _ _ HPR4 ltac:(intros b Hb; right; exact Hb)) in PL2.
apply (PLX _ _ _ _ HPR5 ltac:(intros b Hb; right; right; exact Hb)) in PL2.
apply (PLX _ _ _ _ HPR6 ltac:(intros b Hb; right; right; right; exact Hb)) in PL2.
assert (MG : magree bsegs (aclient_addr CI LB SP) m0 m6).
{ assert (MG1 : magree bsegs (aclient_addr CI LB SP) m0 m1).
  { eapply magree_munch_step; [apply magree_refl| exact MU| exact WM|].
    intros a Ha. pose proof (pag_stack0 a Ha). cbn [outside]. lia. }
  assert (MG2 : magree bsegs (aclient_addr CI LB SP) m0 m2).
  { eapply magree_trans; [exact MG1|]. eapply magree_mono; [exact HPR2|].
    intros a Ha. eapply aca_monoA; [exact Ha| exact (fun b Hb => Hb)| lia]. }
  assert (MG3 : magree bsegs (aclient_addr CI LB SP) m0 m3).
  { eapply magree_munch_step; [exact MG2| exact MU3| exact WM3|].
    intros a Ha. pose proof (pag_stack0 a Ha). pose proof (pag_outside_blk _ _ _ _ _ _ a AH2 (proj1 PB2) Ha).
    cbn [outside]. lia. }
  eapply magree_trans; [exact MG3|]. eapply magree_trans; [eapply magree_mono; [exact HPR4|]|].
  { intros a Ha. eapply aca_monoA; [exact Ha| intros b Hb; right; exact Hb| lia]. }
  eapply magree_trans; [eapply magree_mono; [exact HPR5|]|].
  { intros a Ha. eapply aca_monoA; [exact Ha| intros b Hb; right; right; exact Hb| lia]. }
  eapply magree_mono; [exact HPR6|].
  intros a Ha. eapply aca_monoA; [exact Ha| intros b Hb; right; right; right; exact Hb| lia]. }
apply K. unfold hMA_state.
destruct r3 as [pb|].
- destruct RM as (jb & NP & BRB & AH6 & JB & RB & RBS).
  exists pP, pd, pw, P, DT, W, DST, [HB pb DST (hp_dbuf (huf_draws pl (zlen pl)))], f1, f2, f3, f4, f5, jdt,
    v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, y11, v10, v11, v12, v13, m6.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [right; exists pb; split; [reflexivity| split; [reflexivity| split; [exact NP| exact BRB]]]|].
  split; [unfold PC_HMA; reflexivity|].
  do 5 (split; [lia|]).
  split; [exact AH6|]. split; [exact SOE|]. split; [exact LE|]. split; [exact MG|].
  split; [exact BR|]. split; [exact BRD|]. split; [exact BRW|]. split; [exact JDT|].
  split; [exact PRC3|]. split; [exact PL2|]. split; [exact FRA3|]. split; [exact FRB1|].
  split; [exact ST6| exact MI6].
- destruct RM as (N0 & A0 & APM & AH6).
  exists pP, pd, pw, P, DT, W, DST, (@nil ablock), f1, f2, f3, f4, f5, jdt,
    v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, y11, v10, v11, v12, v13, m6.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [left; split; [reflexivity| split; [exact A0| split; [exact N0| reflexivity]]]|].
  split; [unfold PC_HMA; reflexivity|].
  do 5 (split; [lia|]).
  split; [exact AH6|]. split; [exact SOE|]. split; [exact LE|]. split; [exact MG|].
  split; [exact BR|]. split; [exact BRD|]. split; [exact BRW|]. split; [exact JDT|].
  split; [exact PRC3|]. split; [exact PL2|]. split; [exact FRA3|]. split; [exact FRB1|].
  split; [exact ST6| exact MI6].
Qed.
End First.
End CANSEC1.
