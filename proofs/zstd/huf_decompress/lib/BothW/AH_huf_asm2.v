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
     AH_huf_kit AH_huf_iface AH_huf_prod AH_huf_malloc AH_huf_split AH_huf_lib Stdio_kit AH_huf_rdt2 AHarness_bm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AH_huf_asm2 () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC5ARocqVerifyHarness?AgentSubmission4Spec7Harness;fuzz_mallocC47Corelib4Init9Datatypes3appI46Stdlib5Lists4List5NoDup00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit<harness_topFC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC46Stdlib5Lists4List2InI47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission5BothW5ABase>ablk_disj_bandC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_blocks_nodupC46Stdlib5Lists4List8in_splitC46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List>NoDup_remove_2C47Corelib4Init5Logic3notK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceBAI_blocks_disjointC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02C47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC35stdpp4base6lookupC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula06I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00K47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00c5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm25geomSI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSK47Corelib4Init5Logic4True01I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFK46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission4Spec5Monad4mretC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit:implMA_retC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;implMA_bindC5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6implMAC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneI5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface;payload_atAC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface6AEMPTYC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9ATOP_al16C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface;shad_unshadC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit9cl_shadowC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface@astk_shadow_presC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:aheap_presC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit9aca_monoAC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree;magree_monoC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree<magree_transK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit6FZRB13C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceCaheap_pres_rw_cellsC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit;FZRB13_sizeC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit8aps_restC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5fp_leC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface>fuzz_oneA_postC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface2HUC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps7afree_MK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:afree_postI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6uchain00C5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;uchain_dataC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA9rng_fp_leC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;aps_ok_restC5ARocqVerifyHarness?AgentSubmission5BothW=AH_huf_malloc@prod_free_proofAC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9lb_removeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_hb_idsC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit?lb_remove_headAC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm2:frame_presc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm27mg_stepC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA;fp_le_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAK46Stdlib9micromega7EnvRing5PExpr06c5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm2?astk_of_magreeHK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit@implMA_from_evtFC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4Spec7Harness8free_optC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission4Spec7Harness=PRODUCER_SIZEC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8AFREE_PCI4ELinuxProcessSemantics5Riscv5Instr5instr00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface>AHARNESS_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase:AMALLOC_PCC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<AFMALLOC_RETC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<AFREE_DT_RETC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<AFREE_WK_RETC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<AFREE_DB_RETC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface:AFREEP_RETC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase;AFREE_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6UDEPTHC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?afree_null_postC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit9aunw_dataC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kitAimplMA_afree_nullc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm26h_tailC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;implMA_evtFc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm2@implMA_ret_bindHC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kitAimplMA_afree_callC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6hb_idsC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit>lb_remove_midAc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm27h_free3C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_split8fz_restAC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7hinv_bmC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_split9hMA_stateC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness9huf_drawsC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness7hp_dbufC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness6hp_mtlC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness8DT_BYTESC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness7hp_restC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface8prod_atAC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:hp_streamsC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:hp_symbolsC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness?huf_draws_rangec5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm2>new_vs_payloadc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm2<blk_disj_appc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm2;own_outsideC5ARocqVerifyHarness?AgentSubmission5BothW6ABytes<rw_cells_appC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kitAshad_stack_clientC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit>rclean_magreeAC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm>hinv_bm_clientC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm>hinv_bm_magreeC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib8hC_postAC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib3pC1C46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit8cl_stackC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?rw_cells_magreec5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm27h_freesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC46Stdlib9micromega;ZifyClasses6mkapp2I5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_split6PC_HMAI5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:huf_params00C5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness@HUF_TABLELOG_MAXI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_LOC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_HIC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib9PC_HC_OUTC46Stdlib9micromega8ZifyInst7Inj_Z_Z".
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

Section CANSEC1. Context {rc : runConstT}.

Section Second.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis MONO : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Variable dt_ok : amem -> Z -> Z -> Prop.
  Hypothesis RDT1 : huf_rdt_stmtA2 AI rng_fs dt_ok AHUF_RDT_X1.     (* [comment removed for export] *)
  Hypothesis RDT2 : huf_rdt_stmtA2 AI rng_fs dt_ok AHUF_RDT_X2.
  Hypothesis DEC1 : huf_dec_stmtA AI rng_fs dt_ok AHUF_DEC_1X.
  Hypothesis DEC4 : huf_dec_stmtA AI rng_fs dt_ok AHUF_DEC_4X.
  Hypothesis CIBM : forall a, AHBM_LO <= a < AHBM_HI -> in_ranges CI a.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (L : alayout) (RNG0 : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (FR : bvmap 5 word) (fc : bv 32) (s : APS) (LB : list ablock) (D : Z) (pl : list Z) (lo : Z) (m0 : amem).
  Notation SP := (bv_unsigned sp).
  Hypothesis HLB : forall b, In b LB -> exists p A n, b = HB p A n.
  Hypothesis PAY : AHarness_iface.payload_atA LB D pl.
  Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
  Hypothesis D16 : D mod 16 = 0.
  Hypothesis SZ : zlength pl < 2^26.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - AHARNESS_STACK.
  Hypothesis SPG : SP + ATRUN_DEPTH = al_sp0 L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis FRM : frm0 fc.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RAE : ra = Z_to_bv 64 ATRUN_RET.
  Hypothesis HUL : HU L.
  Hypothesis RSTK0 : rng RNG0 lo (al_top L - lo).
  Hypothesis RI0 : rng_aimg RNG0.
  Hypothesis RISH0 : rng_aimg_sh RNG0.
  Hypothesis RFS0 : rng_fs L RNG0.
  Hypothesis AOK : aps_ok L s.

  Notation POSTF := (fuzz_oneA_post AI L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m0).

  Lemma geomS : 0 <= SP /\ SP + 16 <= al_top L /\ SP < 2^64 /\ ATOP + 4096 + 16384 <= SP.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_asm2 ()) ["CANSEC1"; "Second"] "h04__x1h11Hh24__p1h37__arithh47__sat17h57__sat18h67__sat19h77__sat20h87__sat21h97__sat22h:2Hah;4__ffh<8__varmaph=5__with>4__x2h?4__x3h@3RSPhA2T1hB2T2p;1p;2p;3p;4p;7p;6p;8p-1R0p10000p4p710R1p9P0p1000Np4p710R0p8p1000ep4p710R2p1001Bp4p710R3p8P2P1p8p1001^p4p70R4P0p8P4P3p8P4P2p8P4p1002Up4p7210p8P4P1p8P4p1003Rp4p710p8P4p1003op4p710p8p1004Kp4p7210P1p8g0057j10Tg005\j1\Tg006:j2VTg006mj2lTg007Wj1^Tg008@j27Tg008\R1j25Tg0097j1WTg00:5j16Tg00:Zj14Tg00;8j1dTg00;nj23Tg00<Jj2NTg00=;j2MTg00=[j2OTg00>Cj2ITg00>`j3HTg00?Dj1[Tg00?dj1ZTg00@Dj2?Tg00@bj1YTg00A@j1XTg00Akj2=Tg00BNj2ATg00C1j1UTg00CSj2RTg00D5j2QTg00DOj2PTg00E;j3STg00EUj3TTg00F4j4kTg00Ffj4jTg00Ghj22Tg00HEj1iTg00I<j1hTg00IZj4CTg00J8j3BTg00J[j3cTg00K>j4JTg00Kij1LTg00LHj2DTg00M1j3KTg00MZj2aTg00NFj3`Tg00Nfj3bTg00OIj2_Tg00Ofj4FTg00PAj7eTg00Pej6]Tg00QIj7fTg00Qmj8gTf0R4#0#0p=:g00RQR2/34p=1%64#6#6#6p=8%04#0#0#0p=@%04#0#0#0#0#0#0#0p=>g00RoR3f1R0g00SMP4CJp=<P0g00T4R5g00TSR6P6g00U3R7P4g00USFep=9P0P5P6P6P7P4E]p=Gf2R8P5P6P6P7P0P4Ffp=Ef3R9P5P6P6P7P8P0P4Ggp=;g00V3R5#0R:#0#:R;#:R<#\R=p,2spR>'V1l=>R>#1R?%^=,7>'5p,1LR@P>p,3SPGp,2rcRA#WRB%65RC#6#8#8#8RD#0#8#8#0#:#@#>#>#4%dARA'3%6D#8#8#0#:#@#>#>#4,3A'5RD%4;R;,N>RE%1;RF1M>;#1[\?RG%4:RH%4<RI'ORJ172HRK%1I1IHIRL,72[[RM%1HRNg00VXROAHHI0UW:RI%1L\O^:NRP%0CRC#6#0#4RQ,OHRR%1Q1IHQRS,72[\KRKAHHQ0VOX:NRQ%1S\O^:NRNp,1DRO/N;RS%1O1MO;#1\F[RFp-0ROg00W4RT#[RU%ZTRV1?30RW%Y3RX%X3RY1=32RZ1A35R5'<,9YR[1GY9R\5EY%U6R6P[C;1RY7R7P4P8g00W`R[g00X@R]'Q1P48=S[]dAT320CkR2b;b<b=X03W2R]%14/50%10R[[^03^2OR^P417>LR_P>f8O3b3b4b5b6b7b8b9b1Cj12>;%i@R@'3R`%0C#:#4,2>%:<#@R<#4RC'2,7@Ra'5P1P`Pa12AC%:<#4R<'2/3>R1,5_Rb,5`Rc,5?P4P?PcPBPDPEPGPJPMPIPPPRPKPQPNPSPFP]P^P4P_P>f=R^O3b3b4b5b6b7b8b9b1P`PbPBPDPEPGPJPMPIPPPRPKPQPNPSPFPUPVP31?38RbP0%h3R]CCPXPY1=3;9B351A3:Rc'<,9YRdP6PdC;P7P2b;b<b=X03X>3124;/30120;/38[^03^>3P4P@P>f9O3b3b4b5b6b7b8b9b1P_P1PBPDPEPGPJPMPIPPPRPKPQPNPSPFPUPVPWPXPYP3P5g00X`1=3H=c3=CJ,9YR=9EY\P6P=C;P7P2b;b<b=X03X2O174L,50170L[^03^2OP4P?P>P^O3b3b4b5b6b7b8b9b1PBPDPEPGPJPMPIPPPRPKPQPNPSPFg00YGRF#LRS#L,D31D3S1D3F5K35K3g00Yf'a=`TUPVP3PbP0P31?39P9P]CCCCPXPY1<Zc,9Yf5,GY5EYP6PY%6:,A3R:1=3<RZ9b3c'<,9YP6PY1=3C9B35R5/<:,9YP6AB35Z/<c,9YC;C;C;P7P2b;b<b=X03X>3X?3X2O15[91_8<,39128Cf4R8'3129C/2</38[[[^03^>3^?3^2OP4P_p,2loP>PAP^p,3LOSp,3BOTO7b3b4b5b6b7b8b9b1CFCFCFXBaXA`P0P4O2n2001000000121000000b1b@o"). Qed.

  (* [comment removed for export] *)
  Lemma own_outside : forall RNGx st mx LBx b a, AHEAP AI L RNGx st (LBx ++ LB) mx -> In b LBx ->
    (forall b', In b' LBx -> exists p A n, b' = HB p A n) ->
    aclient_addr CI LB (SP - 128) a -> ~ (ab_addr b <= a < ab_addr b + ab_size b).
Proof.
intros RNGx st mx LBx b a AH Hb HBx Ha Hin. pose proof geomS as (G1 & G2 & G3 & G4). pose proof atop_range as ATR.
unfold AHARNESS_STACK in LOS.
pose proof (AI_block_bounds AI _ _ _ _ _ _ AH (in_or_app _ _ _ (or_introl Hb))) as BB.
destruct (HBx b Hb) as (p & A & n & ->). cbn [ab_addr ab_size] in Hin, BB.
pose proof (AI_block AI _ _ _ _ _ _ _ _ AH (in_or_app _ _ _ (or_introl Hb))) as (_ & (BK & _) & _).
destruct Ha as [X|[(iv & Hiv & Hr)|[(b' & Hb' & Hr)|(a' & Ha' & ->)]]].
- lia.
- pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. cbn in Hr. lia.
- pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND.
  assert (NE : HB p A n <> b').
  { intros E. subst b'. clear - ND Hb Hb'. revert ND Hb. induction LBx as [|y l1 IH]; intros ND H1; [destruct H1|].
    inversion ND as [|z l NI ND']; subst.
    destruct H1 as [->|H1]; [apply NI; apply in_or_app; right; exact Hb'| exact (IH ND' H1)]. }
  pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH (in_or_app _ _ _ (or_introl Hb)) (in_or_app _ _ _ (or_intror Hb')) NE) as DJ.
  cbn in DJ, Hr. lia.
- assert (A47 : 0 <= a' < 2^47).
  { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; cbn in Hr; lia|].
    destruct (HLB _ Hb') as (p' & A' & N' & E'). discriminate. }
  rewrite shad_div in Hin. unfold ASHOFF, ablk, AIMG_HI, KLS in *. clear - A47 ATR BK Hin. Z.div_mod_to_equations. lia.
Qed.

  (* [comment removed for export] *)
  Lemma implMA_ret_bindH : forall {X Y} RNG (x : X) (f : X -> MA Y) (q : APS) (Q : Y -> APS -> footprint -> machine_state -> Prop) ms,
    implMA RNG (f x) q Q ms -> implMA RNG (mbind (mret x) f) q Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_asm2 ()) ["CANSEC1"; "Second"] "h02H0h13ms'h22R'h32q'h42x'h51Hh61Qh73RNGh81Xh91Yh:1fh;2msh<1qh=1xp;2p;6p;3p;4p;5p;7p;;p200R0g01VXR1p4p7210p8P0p101WLR2p4p7210p8P0g0000R3p4p710p8P0g01XAR4p4p710p8P0g01Y@R5p4p710p8p201R6g01Z@R7p4p7210p8P6g01[1R8p4p710p8P6P2p4p73110p8P6P5p4p7210p8P7j2=TP8j64TP1j3;Tg00E;j33Tg008\R1j20Tg00D5j27Tg00Ofj48Tg01[lj5:TP4j79TP3j66TP5l;<Tg01\eR5f1R3f0R433p=5g01L\R8?334p=2g01]aR7?334p=1f2R2f3R91=59[f4R:p-0\7\8\5[f6R;f5R<P9P:O1P2P3P4E4f8R=f7R>P;A;5=<P:P9f<R?f9R@739152>f:RA,23114<'0'0'0RBX17X28X35X4=RCP2P3P=P;P<P9PCP3g01KgP;A3@;;15::12>>1142'0'0'0X17P3A3=<<1599RC12;;RD1133RE'0RF'017=<PCPF1759PDPE178;1773C8C8C8D:F9P1f=RE?3:A159=f;RD,22113;'0'0PEP9PAP<O1P:P=P2E4P4f?R2?3;?f@R9PE15>?RF12;211<A'0RC'0fARGP>f>RHP3O1P=P?P;E4[X4915;D12<H11:@'0'0P1PFPCPGP>PHP2O1P=P?P;E4P415@HP5P2fCR2,2AR;11@HRC'0fERFPDfBR:P2O1R2P3P9PAE4[X3512@:11=E'0P1P;PCPFPDP2PGP9PAE4P412?FP8fFR911E:fIR2P3P9fGO1R9PFfDRDPHE4[X2811?GP7P:P2fHP9PFPDP4E4X17PGPEP4E6W0PEP4E6W0P3P4O2n2001000000120000000W0PAP4E6W0P3P4O2n2001000000120000000W0P>P4E6W0P3P4O2n2001000000120000000X0BX17X28X35X4=M;<W5X;7W6X<5W:W=X78X96X80o"). Qed.

  (* [comment removed for export] *)
  Lemma blk_disj_app : forall RNGx st mx l1 l2 b b', AHEAP AI L RNGx st (l1 ++ l2) mx -> In b l1 -> In b' l2 ->
    ab_addr b + ab_size b <= ab_addr b' \/ ab_addr b' + ab_size b' <= ab_addr b.
Proof.
intros RNGx st mx l1 l2 b b' AH H1 H2.
pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND.
assert (NE : b <> b').
{ intros <-. clear - ND H1 H2. revert ND H1. induction l1 as [|y l1 IH]; intros ND H1; [destruct H1|].
  inversion ND as [|z l NI ND']; subst.
  destruct H1 as [<-|H1]; [apply NI; apply in_or_app; right; exact H2| exact (IH ND' H1)]. }
exact (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH (in_or_app _ _ _ (or_introl H1)) (in_or_app _ _ _ (or_intror H2)) NE).
Qed.

  (* [comment removed for export] *)
  Lemma new_vs_payload : forall RNGx st mx LBx b r, AHEAP AI L RNGx st (LBx ++ LB) mx -> In b LBx ->
    (forall b', In b' LBx -> exists p A n, b' = HB p A n) -> 0 <= r <= zlen pl ->
    ab_addr b + ab_size b <= D \/ D + r <= ab_addr b.
Proof.
intros RNGx st mx LBx b r AH Hb HBx Hr.
pose proof (AI_block_bounds AI _ _ _ _ _ _ AH (in_or_app _ _ _ (or_introl Hb))) as BB.
pose proof PAY as PF. hnf in PF. destruct PF as [(p & IND & LEN)|(E1 & E2)].
- pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND.
  assert (NE : b <> HB p D (zlength pl)).
  { intros E. subst b. clear - ND Hb IND. revert ND Hb. induction LBx as [|y l1 IH]; intros ND H1; [destruct H1|].
    inversion ND as [|z l NI ND']; subst.
    destruct H1 as [->|H1]; [apply NI; apply in_or_app; right; exact IND| exact (IH ND' H1)]. }
  pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH (in_or_app _ _ _ (or_introl Hb)) (in_or_app _ _ _ (or_intror IND)) NE) as DJ.
  cbn [ab_addr ab_size] in DJ. unfold zlength in *. lia.
- subst pl D. cbn [length Z.of_nat] in Hr. unfold AEMPTY, AIMG_HI in *. right; lia.
Qed.

  (* [comment removed for export] *)
  Lemma astk_of_magreeH : forall m', al_top L <= 2^47 -> magree bsegs (aclient_addr CI LB SP) m0 m' -> astk_shadow_pres SP m0 m'.
Proof.
intros m' TOP MG a Ha. pose proof geomS as (G1 & G2 & G3 & G4). pose proof atop_range as ATR. pose proof ATOP_al16 as A16.
rewrite !shad_div in Ha.
assert (E : a = shad (8 * (a - ASHOFF))).
{ rewrite shad_div. rewrite (Z.mul_comm 8), Z.div_mul by lia. lia. }
assert (A' : ATOP <= 8 * (a - ASHOFF) < 2^47) by (clear - Ha G1 G2 TOP ATR A16; Z.div_mod_to_equations; lia).
assert (CL : aclient_addr CI LB SP a) by (rewrite E; apply shad_stack_client; lia).
assert (AR : 0 <= a < 2^64) by (unfold ASHOFF in *; clear - Ha G1 G3; Z.div_mod_to_equations; lia).
exact (proj1 (MG a AR CL)).
Qed.

  (* [comment removed for export] *)
  Lemma mg_step : forall LBx m1 m2 m3, magree bsegs (aclient_addr CI LB SP) m1 m2 ->
    (forall b, In b LB -> In b LBx) -> aheap_pres CI LBx (SP - 128) m2 m3 -> magree bsegs (aclient_addr CI LB SP) m1 m3.
Proof.
intros LBx m1 m2 m3 MG INC HP. pose proof geomS as (G1 & G2 & G3 & G4).
eapply magree_trans; [exact MG|]. eapply magree_mono; [exact HP|].
intros a Ha. eapply aca_monoA; [exact Ha| exact INC| lia].
Qed.

  (* [comment removed for export] *)
  Lemma frame_pres : forall LBx m2 m3 (c0 c1 c2 : word), al_top L <= 2^47 ->
    aheap_pres CI LBx (SP - 128) m2 m3 ->
    rw_cells bsegs m2 (SP - 128) [C8 c0; C8 c1; C8 c2] ->
    rw_cells bsegs m2 (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m3 (SP - 128) [C8 c0; C8 c1; C8 c2] /\
    rw_cells bsegs m3 (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
intros LBx m2 m3 c0 c1 c2 TOP HP F1 F2. pose proof geomS as (G1 & G2 & G3 & G4). split.
- eapply aheap_pres_rw_cells; [exact HP| exact F1| apply cr_stack; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
- eapply aheap_pres_rw_cells; [exact HP| exact F2| apply cr_stack; unfold FZRB13; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
Qed.

  (* [comment removed for export] *)
  Lemma h_tail : forall (m3 : amem) (q3 : APS) (R3 : footprint) (pP : AsanCtrl.aptr) (P : Z) (c0 c1 c2 : word)
      (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    AHEAP AI L R3 (aps_m q3) (HB pP P PRODUCER_SIZE :: LB) m3 ->
    magree bsegs (aclient_addr CI LB SP) m0 m3 ->
    aps_rest q3 = aps_rest s -> fp_le RNG0 R3 ->
    stk bsegs m3 lo (SP - 128) -> mem_inv bsegs m3 ->
    rw_cells bsegs m3 (SP - 128) [C8 c0; C8 c1; C8 c2] ->
    rw_cells bsegs m3 (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    implMA R3 (Harness.free_opt afree_M (Some pP) ;;; mret 0) q3 POSTF
      (MS (mkR y1 (Z_to_bv 64 (SP - 128)) gp tp y5 y6 y7 (Z_to_bv 64 P) y9 y10 y11 y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          FR (Z_to_bv 64 0x80200) fc None m3 (seg_rom bsegs)).
Proof.
intros m3 q3 R3 pP P c0 c1 c2 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
  AH3 MG3 REST3 FLE3 ST3 MI3 FRA3 FRB3.
pose proof geomS as (G1 & G2 & G3 & G4). pose proof atop_range as ATR.
pose proof LOS as LOS'. unfold AHARNESS_STACK in LOS'.
pose proof (AI_layout AI _ _ _ _ _ AH3) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
pose proof (rng_fp_le _ _ _ _ FLE3 RSTK0) as RSTK3.
pose proof (AI_block AI _ _ _ _ _ _ _ _ AH3 (or_introl eq_refl)) as (PB1 & PB2 & _).
pose proof (ablk_lin _ _ (proj1 PB2)) as PLN. unfold AIMG_HI in PLN.
cbn [Harness.free_opt].
apply implMA_from_evtF.
do 2 zstep.
apply evtF_done.
eapply implMA_bind.
{ eapply (prod_free_proofA AI) with (LB := HB pP P PRODUCER_SIZE :: LB) (lo := lo) (tr := []); rewrite ?unsigned_lit by lia;
  first [ exact AH3 | exact (or_introl eq_refl) | exact MI3 | exact ST3 | exact BOT | exact TP | reflexivity
        | exact RSTK3 | exact (aps_ok_rest _ _ _ REST3 AOK) | exact HU5
        | (apply uchain_data; lia)
        | (cbn [length]; lia)
        | (unfold AFREE_STACK; lia) | (unfold AFREE_PC; lia)
        | (clear - SP16; Z.div_mod_to_equations; lia) | lia ]. }
cbv beta. intros [] q4 R4 ms4 [REST4 PO4]. unfold afree_post in PO4.
destruct PO4 as (FLE4 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m4 & -> & MI4 & ST4 & HPR4 & AH4).
rewrite ?unsigned_lit in ST4, HPR4 by lia.
rewrite (lb_remove_headA pP P PRODUCER_SIZE LB (AI_hb_ids AI _ _ _ _ _ AH3)) in HPR4, AH4.
h_retlit.
destruct (frame_pres LB m3 m4 c0 c1 c2 LY3 HPR4 FRA3 FRB3) as [FRA4 FRB4].
pose proof (mg_step LB m0 m3 m4 MG3 (fun b Hb => Hb) HPR4) as MG4.
assert (FLE04 : fp_le RNG0 R4) by (intros b j Hb; apply FLE4, FLE3, Hb).
pose proof (rng_fp_le _ _ _ _ FLE04 RSTK0) as RSTK4.
pose proof (stk_of_rw_cells bsegs m4 _ _ FRA4) as SA. cbn [cells_size csize Nat.add] in SA. change (Z.of_nat 24) with 24 in SA.
pose proof (stk_of_rw_cells bsegs m4 _ _ FRB4) as SB. rewrite FZRB13_size in SB. change (Z.of_nat 104) with 104 in SB.
assert (STF : stk bsegs m4 lo SP).
{ apply (stk_merge bsegs m4 lo (SP + -104) SP); [| replace SP with (SP + -104 + 104) at 2 by lia; exact SB| lia].
  apply (stk_merge bsegs m4 lo (SP - 128) (SP + -104)); [exact ST4| replace (SP + -104) with (SP - 128 + 24) by lia; exact SA| lia]. }
unfold FZRB13 in FRB4.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
remember (bv_unsigned sp) as SPz eqn:ESP.
replace (SPz + -104) with (SPz - 128 + 24) in FRB4 by lia.
remember (SPz - 128) as SPA eqn:ESPA.
apply implMA_ret.
zstep.
zstep.
do 12 zstep.
zstep.
zstep.
apply evtF_done.
subst SPA SPz.
match goal with |- context [Z_to_bv 64 ?e] => lazymatch e with context [bv_unsigned sp] =>
  assert (SPE : Z_to_bv 64 e = sp) by (replace e with (bv_unsigned sp) by lia; apply Z_to_bv_bv_unsigned) end end.
unfold fuzz_oneA_post. split; [exact FLE04|].
do 17 eexists. split; [rewrite SPE; reflexivity|].
split; [lia|]. split; [exact MI4|]. split; [exact FRM|]. split; [exact STF|].
split; [exact MG4|]. split; [exact (astk_of_magreeH m4 LY3 MG4)|]. split; [exact AH4|]. split; [exact I| rewrite REST4; exact REST3].
Qed.

  (* [comment removed for export] *)
  Lemma h_free3 : forall (m2 : amem) (q2 : APS) (R2 : footprint) (pP : AsanCtrl.aptr) (P DST dbs : Z) (LBd : list ablock)
      (dBuf : option AsanCtrl.aptr) (c0 c1 c2 : word)
      (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    (dBuf = None /\ DST = 0 /\ LBd = []) \/ (exists pb, dBuf = Some pb /\ LBd = [HB pb DST dbs]) ->
    AHEAP AI L R2 (aps_m q2) (LBd ++ HB pP P PRODUCER_SIZE :: LB) m2 ->
    magree bsegs (aclient_addr CI LB SP) m0 m2 ->
    aps_rest q2 = aps_rest s -> fp_le RNG0 R2 ->
    stk bsegs m2 lo (SP - 128) -> mem_inv bsegs m2 ->
    rw_cells bsegs m2 (SP - 128) [C8 c0; C8 c1; C8 c2] ->
    rw_cells bsegs m2 (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    implMA R2 (Harness.free_opt afree_M dBuf ;;; Harness.free_opt afree_M (Some pP) ;;; mret 0) q2 POSTF
      (MS (mkR y1 (Z_to_bv 64 (SP - 128)) gp tp y5 y6 y7 (Z_to_bv 64 P) y9 y10 y11 y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 (Z_to_bv 64 DST) y23 y24 y25 y26 y27 y28 y29 y30 y31)
          FR (Z_to_bv 64 0x801f8) fc None m2 (seg_rom bsegs)).
Proof.
intros m2 q2 R2 pP P DST dbs LBd dBuf c0 c1 c2 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y23 y24 y25 y26 y27 y28 y29 y30 y31
  DB AH2 MG2 REST2 FLE2 ST2 MI2 FRA2 FRB2.
pose proof geomS as (G1 & G2 & G3 & G4). pose proof atop_range as ATR.
pose proof LOS as LOS'. unfold AHARNESS_STACK in LOS'.
pose proof (AI_layout AI _ _ _ _ _ AH2) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
pose proof (rng_fp_le _ _ _ _ FLE2 RSTK0) as RSTK2.
pose proof (AI_block AI _ _ _ _ _ _ _ _ AH2 (in_or_app _ _ _ (or_intror (in_eq _ _)))) as (PB1 & PB2 & _).
pose proof (ablk_lin _ _ (proj1 PB2)) as PLN. unfold AIMG_HI in PLN.
destruct DB as [(-> & -> & ->)|(pb & -> & ->)].
- cbn [app] in AH2. cbn [Harness.free_opt].
  apply implMA_from_evtF.
  do 2 zstep.
  eapply evtF_cut.
  { eapply (implMA_afree_null AI L R2) with (LB := HB pP P PRODUCER_SIZE :: LB) (lo := lo) (tr := []); rewrite ?unsigned_lit by lia;
    first [ exact AH2 | exact MI2 | exact ST2 | exact BOT | exact TP | reflexivity | exact RSTK2
          | (apply aunw_data; rewrite ?unsigned_lit by lia; [lia| lia| exact HU4])
          | (unfold AFREE_STACK; lia) | (unfold AFREE_PC; lia)
          | (clear - SP16; Z.div_mod_to_equations; lia) | lia ]. }
  cbv beta. intros ms3 PO3. unfold afree_null_post in PO3.
  destruct PO3 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m3 & -> & MI3 & ST3 & HPR3 & AH3).
  rewrite ?unsigned_lit in ST3, HPR3 by lia. h_retlit.
  apply evtF_done. apply implMA_ret_bindH.
  destruct (frame_pres _ m2 m3 c0 c1 c2 LY3 HPR3 FRA2 FRB2) as [FRA3 FRB3].
  pose proof (mg_step (HB pP P PRODUCER_SIZE :: LB) m0 m2 m3 MG2 (fun b Hb => or_intror Hb) HPR3) as MG3.
  eapply h_tail; first [exact AH3 | exact MG3 | exact REST2 | exact FLE2 | exact ST3 | exact MI3 | exact FRA3 | exact FRB3].
- cbn [app] in AH2. cbn [Harness.free_opt].
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_introl eq_refl)) as (QB1 & QB2 & _).
  pose proof (ablk_lin _ _ (proj1 QB2)) as QLN. unfold AIMG_HI in QLN.
  apply implMA_from_evtF.
  do 2 zstep.
  apply evtF_done.
  eapply implMA_bind.
  { eapply (implMA_afree_call AI L R2) with (LB := HB pb DST dbs :: HB pP P PRODUCER_SIZE :: LB) (lo := lo) (tr := []);
    rewrite ?unsigned_lit by lia;
    first [ exact AH2 | exact (or_introl eq_refl) | exact MI2 | exact ST2 | exact BOT | exact TP | reflexivity | exact RSTK2
          | exact (aps_ok_rest _ _ _ REST2 AOK)
          | (apply aunw_data; rewrite ?unsigned_lit by lia; [lia| lia| exact HU4])
          | (unfold AFREE_STACK; lia) | (unfold AFREE_PC; lia)
          | (clear - SP16; Z.div_mod_to_equations; lia) | lia ]. }
  cbv beta. intros [] q3 R3 ms3 [REST3 PO3]. unfold afree_post in PO3.
  destruct PO3 as (FLE3 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m3 & -> & MI3 & ST3 & HPR3 & AH3).
  rewrite ?unsigned_lit in ST3, HPR3 by lia.
  rewrite (lb_remove_headA pb DST dbs (HB pP P PRODUCER_SIZE :: LB) (AI_hb_ids AI _ _ _ _ _ AH2)) in HPR3, AH3.
  h_retlit.
  destruct (frame_pres _ m2 m3 c0 c1 c2 LY3 HPR3 FRA2 FRB2) as [FRA3 FRB3].
  pose proof (fun H => mg_step _ m0 m2 m3 MG2 H HPR3) as MG3. specialize (MG3 (fun b Hb => or_intror Hb)).
  assert (FLE03 : fp_le RNG0 R3) by (intros b j Hb; apply FLE3, FLE2, Hb).
  eapply h_tail; first [exact AH3 | exact MG3 | (rewrite REST3; exact REST2) | exact FLE03 | exact ST3 | exact MI3 | exact FRA3 | exact FRB3].
Qed.

  (* [comment removed for export] *)
  Lemma h_frees : forall (m1 : amem) (q1 : APS) (R1 : footprint) (pP pd pw : AsanCtrl.aptr) (P DT W DST dbs mtl : Z)
      (LBd : list ablock) (dBuf : option AsanCtrl.aptr) (c0 c1 c2 : word)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 y18 y19 y24 y25 y26 y27 x28 x29 x30 x31 : word),
    (dBuf = None /\ DST = 0 /\ LBd = []) \/ (exists pb, dBuf = Some pb /\ LBd = [HB pb DST dbs]) ->
    AHEAP AI L R1 (aps_m q1) (LBd ++ HB pw W 8704 :: HB pd DT (DTABLE_BYTES mtl) :: HB pP P PRODUCER_SIZE :: LB) m1 ->
    magree bsegs (aclient_addr CI LB SP) m0 m1 ->
    aps_rest q1 = aps_rest s -> fp_le RNG0 R1 ->
    stk bsegs m1 lo (SP - 128) -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (SP - 128) [C8 c0; C8 c1; C8 c2] ->
    rw_cells bsegs m1 (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    implMA R1 (fz_restA (Some pP) (Some pd) (Some pw) dBuf) q1 POSTF
      (MS (mkR x1 (Z_to_bv 64 (SP - 128)) gp tp x5 x6 x7 (Z_to_bv 64 P) x9 x10 x11 x12 x13 x14 x15 x16 x17
               y18 y19 (Z_to_bv 64 DT) (Z_to_bv 64 W) (Z_to_bv 64 DST) (Z_to_bv 64 dbs) y24 y25 y26 y27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x801e8) fc None m1 (seg_rom bsegs)).
Proof.
intros m1 q1 R1 pP pd pw P DT W DST dbs mtl LBd dBuf c0 c1 c2
  x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 y18 y19 y24 y25 y26 y27 x28 x29 x30 x31
  DB AH1 MG1 REST1 FLE1 ST1 MI1 FRA1 FRB1.
pose proof geomS as (G1 & G2 & G3 & G4). pose proof atop_range as ATR.
pose proof LOS as LOS'. unfold AHARNESS_STACK in LOS'.
pose proof (AI_layout AI _ _ _ _ _ AH1) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
pose proof (rng_fp_le _ _ _ _ FLE1 RSTK0) as RSTK1.
assert (PERM1 : Permutation (LBd ++ HB pw W 8704 :: HB pd DT (DTABLE_BYTES mtl) :: HB pP P PRODUCER_SIZE :: LB)
                            (HB pd DT (DTABLE_BYTES mtl) :: HB pw W 8704 :: LBd ++ HB pP P PRODUCER_SIZE :: LB)).
{ eapply Permutation.perm_trans; [apply Permutation.Permutation_sym, Permutation.Permutation_middle|].
  eapply Permutation.perm_trans; [apply Permutation.perm_skip, Permutation.Permutation_sym, Permutation.Permutation_middle|].
  apply Permutation.perm_swap. }
pose proof (AI_perm AI _ _ _ _ _ _ PERM1 AH1) as AH1'.
pose proof (AI_block AI _ _ _ _ _ _ _ _ AH1' (or_intror (or_intror (in_or_app _ _ _ (or_intror (in_eq _ _)))))) as (PB1 & PB2 & _).
pose proof (ablk_lin _ _ (proj1 PB2)) as PLN. unfold AIMG_HI in PLN.
unfold fz_restA. cbn [Harness.free_opt].
apply implMA_from_evtF.
do 2 zstep.
apply evtF_done.
eapply implMA_bind.
{ eapply (implMA_afree_call AI L R1) with (LB := HB pd DT (DTABLE_BYTES mtl) :: HB pw W 8704 :: LBd ++ HB pP P PRODUCER_SIZE :: LB)
    (lo := lo) (tr := []); rewrite ?unsigned_lit by lia;
  first [ exact AH1' | exact (or_introl eq_refl) | exact MI1 | exact ST1 | exact BOT | exact TP | reflexivity | exact RSTK1
        | exact (aps_ok_rest _ _ _ REST1 AOK)
        | (apply aunw_data; rewrite ?unsigned_lit by lia; [lia| lia| exact HU2])
        | (unfold AFREE_STACK; lia) | (unfold AFREE_PC; lia)
        | (clear - SP16; Z.div_mod_to_equations; lia) | lia ]. }
cbv beta. intros [] q2 R2 ms2 [REST2 PO2]. unfold afree_post in PO2.
destruct PO2 as (FLE2 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & -> & MI2 & ST2 & HPR2 & AH2).
rewrite ?unsigned_lit in ST2, HPR2 by lia.
rewrite (lb_remove_headA pd DT (DTABLE_BYTES mtl) _ (AI_hb_ids AI _ _ _ _ _ AH1')) in HPR2, AH2.
h_retlit.
destruct (frame_pres _ m1 m2 c0 c1 c2 LY3 HPR2 FRA1 FRB1) as [FRA2 FRB2].
pose proof (fun H => mg_step _ m0 m1 m2 MG1 H HPR2) as MG2. specialize (MG2 (fun b Hb => in_cons _ _ _ (in_or_app _ _ _ (or_intror (in_cons _ _ _ Hb))))).
assert (FLE02 : fp_le RNG0 R2) by (intros b j Hb; apply FLE2, FLE1, Hb).
pose proof (rng_fp_le _ _ _ _ FLE02 RSTK0) as RSTK2.
apply implMA_from_evtF.
do 2 zstep.
apply evtF_done.
eapply implMA_bind.
{ eapply (implMA_afree_call AI L R2) with (LB := HB pw W 8704 :: LBd ++ HB pP P PRODUCER_SIZE :: LB)
    (lo := lo) (tr := []); rewrite ?unsigned_lit by lia;
  first [ exact AH2 | exact (or_introl eq_refl) | exact MI2 | exact ST2 | exact BOT | exact TP | reflexivity | exact RSTK2
        | exact (aps_ok_rest _ _ _ REST2 (aps_ok_rest _ _ _ REST1 AOK))
        | (apply aunw_data; rewrite ?unsigned_lit by lia; [lia| lia| exact HU3])
        | (unfold AFREE_STACK; lia) | (unfold AFREE_PC; lia)
        | (clear - SP16; Z.div_mod_to_equations; lia) | lia ]. }
cbv beta. intros [] q3 R3 ms3 [REST3 PO3]. unfold afree_post in PO3.
destruct PO3 as (FLE3 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & -> & MI3 & ST3 & HPR3 & AH3).
rewrite ?unsigned_lit in ST3, HPR3 by lia.
rewrite (lb_remove_headA pw W 8704 _ (AI_hb_ids AI _ _ _ _ _ AH2)) in HPR3, AH3.
h_retlit.
destruct (frame_pres _ m2 m3 c0 c1 c2 LY3 HPR3 FRA2 FRB2) as [FRA3 FRB3].
pose proof (fun H => mg_step _ m0 m2 m3 MG2 H HPR3) as MG3. specialize (MG3 (fun b Hb => in_or_app _ _ _ (or_intror (in_cons _ _ _ Hb)))).
assert (FLE03 : fp_le RNG0 R3) by (intros b j Hb; apply FLE3, FLE02, Hb).
eapply (h_free3 m3 q3 R3 pP P DST dbs LBd dBuf c0 c1 c2);
  first [exact DB | exact AH3 | exact MG3 | (rewrite REST3, REST2; exact REST1) | exact FLE03 | exact ST3 | exact MI3
        | exact FRA3 | exact FRB3].
Qed.

  Theorem fz_secondA : forall producer dt wksp dBuf s' RNG1 ms (rstk : region),
    rclean m0 rstk -> r_lo rstk <= lo -> SP <= r_hi rstk -> ATOP <= r_rlo rstk -> rrng RNG0 rstk ->
    hinv_bm m0 ->
    hMA_state AI L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 producer dt wksp dBuf s' RNG1 ms ->
    implMA RNG1 (fz_restA producer dt wksp dBuf) s' POSTF ms.
Proof.
intros producer dt wksp dBuf s' RNG1 ms rstk RC RLO RHI RRLO RR HBM HS.
destruct HS as (pP & pd & pw & P & DT & W & DST & LBd & f1 & f2 & f3 & f4 & f5 & jdt
  & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r22 & t3 & t4 & t5 & t6 & m
  & -> & -> & -> & DB & -> & F1 & F2 & F3 & F4 & F5 & AH & REST & FLE & MG & PR1 & PR2 & PR3 & JD & PRA & BY & CS & FRB & ST & MI).
pose proof geomS as (G1 & G2 & G3 & G4).
assert (SZ' : 0 <= zlen pl <= 2^26) by (unfold zlength in SZ; lia).
pose proof (huf_draws_range pl (zlen pl) SZ') as HR. cbv zeta in HR. destruct HR as (HR1 & HR2 & HR3 & HR4 & HR5).
remember (huf_draws pl (zlen pl)) as h eqn:EH.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof LOS as LOS'. unfold AHARNESS_STACK in LOS'.
pose proof (ablk_lin _ _ (proj1 PR2)) as DLN. unfold AIMG_HI in DLN.
pose (LBx := LBd ++ [HB pw W 8704; HB pd DT (DT_BYTES (hp_mtl h)); HB pP P PRODUCER_SIZE]).
assert (AHX : AHEAP AI L RNG1 (aps_m s') (LBx ++ LB) m) by (unfold LBx; rewrite <- app_assoc; exact AH).
assert (HBX : forall b, In b LBx -> exists p A n, b = HB p A n).
{ intros b Hb. unfold LBx in Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
  - destruct DB as [(_ & _ & _ & E)|(pb & _ & E & _)]; rewrite E in Hb; [destruct Hb|].
    destruct Hb as [<-|[]]. do 3 eexists; reflexivity.
  - destruct Hb as [<-|[<-|[<-|[]]]]; do 3 eexists; reflexivity. }
assert (HBL : forall b, In b (LBx ++ LB) -> exists p A n, b = HB p A n).
{ intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (HBX b Hb)| exact (HLB b Hb)]. }
assert (NVP : forall b, In b LBx -> ab_addr b + ab_size b <= D \/ D + hp_rest h <= ab_addr b).
{ intros b Hb. exact (new_vs_payload _ _ _ _ b (hp_rest h) AHX Hb HBX ltac:(lia)). }
assert (OWX : forall b a, In b LBx -> aclient_addr CI LB (SP - 128) a -> ~ (ab_addr b <= a < ab_addr b + ab_size b)).
{ intros b a Hb CA. exact (own_outside _ _ _ _ b a AHX Hb HBX CA). }
assert (IPW : In (HB pw W 8704) LBx) by (unfold LBx; apply in_or_app; right; apply in_eq).
assert (IPD : In (HB pd DT (DT_BYTES (hp_mtl h))) LBx) by (unfold LBx; apply in_or_app; right; apply in_cons, in_eq).
assert (DG : 16 <= D).
{ pose proof PAY as PY. unfold payload_atA in PY. destruct PY as [(p & IP & _)|(_ & ->)]; [| unfold AEMPTY; lia].
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AHX (in_or_app _ _ _ (or_intror IP))) as (_ & PB2 & _).
  pose proof (ablk_lin _ _ (proj1 PB2)) as PLN. unfold AIMG_HI in PLN. lia. }
eapply implMA_evtF.
{ eapply (pC1 AI rng_fs dt_ok RDT1 RDT2 DEC1 DEC4 CIBM L RNG1 gp tp FR fc (aps_m s') SP lo P D DT W DST
    (hp_dbuf h) (hp_mtl h) (hp_streams h) (hp_symbols h) pl (hp_rest h) pP pd pw LB LBd).
  all: try first [ exact AH | exact MI | exact ST | exact RC | exact RLO | exact RHI | exact RRLO | exact JD | exact PRA
                 | exact BY | exact CS | exact F1 | exact F2 | exact F3 | exact F4 | exact F5 | exact HLB | exact PLB
                 | exact D16 | exact BOT | exact LOS | exact SP16 | exact TP | exact HR4 | exact DG
                 | exact (rng_fp_le _ _ _ _ FLE RSTK0) | exact (rng_fp_le _ _ _ _ FLE RI0) | exact (rng_fp_le _ _ _ _ FLE RISH0)
                 | exact (MONO _ _ _ FLE RFS0) | (unfold rrng in *; exact (rng_fp_le _ _ _ _ FLE RR))
                 | exact (NVP _ IPD) | exact (NVP _ IPW) | lia ].
  all: try first
    [ solve [ unfold zlength in SZ; lia ]
    | solve [ destruct DB as [(_ & E1 & E2 & E3)|(pb & _ & E1 & E2 & _)]; [left; auto| right; exists pb; auto] ]
    | solve [ pose proof PAY as PY; unfold payload_atA, zlength in PY; destruct PY as [PY|PY]; [right; exact PY| left; exact PY] ]
    | solve [ eapply rng_sub; [exact (rng_fp_le _ _ _ _ FLE RSTK0)| lia| lia] ]
    | solve [ intros b Hb; apply HBL; first [ unfold LBx; rewrite <- app_assoc; exact Hb
                                            | apply in_or_app; left; unfold LBx; apply in_or_app; left; exact Hb ] ]
    | solve [ intros b Hb; assert (Hb' : In b (LBx ++ LB)) by (unfold LBx; rewrite <- app_assoc; exact Hb);
              destruct (HBL b Hb') as (p & A & n & ->);
              pose proof (AI_block AI _ _ _ _ _ _ _ _ AHX Hb') as (_ & PB & _); exact (proj1 PB) ]
    | solve [ intros RP; assert (ZP : 0 < zlen pl) by lia; pose proof PAY as PY; unfold payload_atA, zlength in PY;
              destruct PY as [(p & IP & _)|(EP & _)];
              [ exists p, D, (zlen pl); split; [apply in_or_app; right; apply in_cons, in_cons, in_cons; exact IP| lia]
              | rewrite EP in ZP; cbn in ZP; lia ] ]
    | solve [ destruct DB as [(_ & E1 & E2 & _)|(pb & _ & ELd & _ & _)];
              [ rewrite E1, E2; lia
              | refine (NVP (HB pb DST (hp_dbuf h)) _); unfold LBx; rewrite ELd; apply in_or_app; left; apply in_eq ] ]
    | solve [ destruct DB as [(_ & E1 & E2 & _)|(pb & _ & ELd & _ & _)];
              [ rewrite E1, E2; lia
              | assert (I1 : In (HB pb DST (hp_dbuf h)) LBd) by (rewrite ELd; apply in_eq);
                destruct (blk_disj_app _ _ _ _ _ _ (HB pd DT (DT_BYTES (hp_mtl h))) AH I1 (in_cons _ _ _ (in_eq _ _))) as [S|S];
                [right; exact S| left; exact S] ] ]
    | solve [ assert (AH5 : AHEAP AI L RNG1 (aps_m s') ((LBd ++ [HB pw W 8704; HB pd DT (DT_BYTES (hp_mtl h))]) ++ HB pP P PRODUCER_SIZE :: LB) m)
                by (rewrite <- app_assoc; exact AH);
              assert (I1 : In (HB pd DT (DT_BYTES (hp_mtl h))) (LBd ++ [HB pw W 8704; HB pd DT (DT_BYTES (hp_mtl h))]))
                by (apply in_or_app; right; apply in_cons, in_eq);
              destruct (blk_disj_app _ _ _ _ _ _ (HB pP P PRODUCER_SIZE) AH5 I1 (in_eq _ _)) as [S|S]; [right; exact S| left; exact S] ]
    | solve [ intros a CA; split; [exact (OWX _ a IPD CA)| split; [exact (OWX _ a IPW CA)|]];
              destruct DB as [(_ & E1 & E2 & _)|(pb & _ & ELd & _ & _)];
              [ rewrite E1, E2; lia
              | refine (OWX (HB pb DST (hp_dbuf h)) a _ CA); unfold LBx; rewrite ELd; apply in_or_app; left; apply in_eq ] ]
    | solve [ eapply rclean_magreeA; [exact RC| exact MG| | exact RRLO];
              intros a Ha; unfold aclient_addr; right; right; right; exists a; split; [left; lia| reflexivity] ]
    | solve [ eapply hinv_bm_magree; [exact MG| intros a Ha; apply hinv_bm_client; [exact CIBM| exact Ha]| exact HBM] ] ]. }
cbv beta. intros ms' (x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & y18 & y19 & y24 & y25 & y26 & y27
  & x28 & x29 & x30 & x31 & m' & -> & MI' & ST' & MG' & AH').
assert (MG1 : magree bsegs (aclient_addr CI LB SP) m0 m').
{ eapply magree_trans; [exact MG|]. eapply magree_mono; [exact MG'|].
  intros a Ha. eapply aca_monoA; [exact Ha| intros b Hb; exact Hb| lia]. }
assert (FRA1 : rw_cells bsegs m' (SP - 128) [C8 (Z_to_bv 64 (hp_streams h)); C8 (Z_to_bv 64 ASHOFF); C8 (Z_to_bv 64 (hp_symbols h))]).
{ eapply rw_cells_magree; [exact MG'| exact CS|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
  unfold aclient_addr. left. lia. }
assert (FRB1 : rw_cells bsegs m' (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
{ eapply rw_cells_magree; [exact MG'| exact FRB|]. intros a Ha. rewrite FZRB13_size in Ha.
  unfold aclient_addr. left. lia. }
assert (DB1 : (dBuf = None /\ DST = 0 /\ LBd = []) \/ (exists pb, dBuf = Some pb /\ LBd = [HB pb DST (hp_dbuf h)])).
{ destruct DB as [(E1 & E2 & _ & E3)|(pb & E1 & E2 & _)]; [left; auto| right; exists pb; auto]. }
unfold PC_HC_OUT.
eapply h_frees; first [ exact DB1 | exact AH' | exact MG1 | exact REST | exact FLE | exact ST' | exact MI' | exact FRA1 | exact FRB1 ].
Qed.
End Second.
End CANSEC1.
