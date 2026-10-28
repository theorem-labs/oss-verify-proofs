(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_adisp () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=bytes_at_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnK47Corelib4Init9Datatypes6option01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5Plain<RF_huf_iface8x1_bytesC47Corelib4Init3Nat3minC47Corelib4Init3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8min_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit29x1_bytes'C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2@x1_bytes'_lengthC46Stdlib5Lists4List=length_firstnK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission5Plain<RF_huf_iface8x2_bytesC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit39x2_bytes'C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3@x2_bytes'_lengthI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface7src_inAC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPK47Corelib4Init5Logic2or02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib4Init5Logic2or01C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC35stdpp4base6lookupC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC56Stdlib6ZArith4Znat5Nat2Z8inj_succI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00K47Corelib4Init9Datatypes4bool02C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?magree_of_munchC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_block_boundsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic6eq_indK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree;magree_monoC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree<magree_transK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K47Corelib4Init5Logic2ex01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HII47Corelib4Init5Logic4True00C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFK47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface>dec1_int_stmtAC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface:huf_dt_okAI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface=hb_unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_rtcellsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8artcellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_adisp>disp_src_boundC56Stdlib6ZArith6BinInt1Z7div_posC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow?unpoisoned_fullC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface@huf_dt_okA_casesC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface7x1_tabAC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface7x2_tabAC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_adisp:x1_tab_lenC56Stdlib6ZArith6BinInt1Z9pow_add_rK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem;wr_at_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj1K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divK4ELinuxProcessSemantics5Riscv5Instr5instr06C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_adisp;desc_tt_rdAC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit@rclean_transportc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_adisp9disp_postC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_monoC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_adisp:x2_tab_lenC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_nilC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_stmtAC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdK46Stdlib9micromega5Tauto8GFormula07K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface;AHUF_DX1_1XC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface;AHUF_DX2_1XI5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface?HUF_DEC_STACK_AC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXI47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KLOWC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface;AHUF_DEC_1XC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface>dec4_int_stmtAC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface;AHUF_DX1_4XC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface;AHUF_DX2_4XC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface;AHUF_DEC_4X".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma desc_tt_rdA : forall m DT mtl tt tl,
  bytes_at bsegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 tt; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
  ov_read_bytes bsegs m (Z_to_bv 64 (DT + 1)) 1 = Some [Z_to_bv 8 tt].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_adisp ()) ["CANSEC1"] "h07__arithh14__ffh24__p1h34__p2h48__varmaph55__with64__x1h71xh82DTh91Hh:2H0h;1Rh<1mh=3mtlh>2tlh?2tth@2z0p;1p;2p;3p;4p;7p;8p;9p;<p;Bp;6p10000p4p7210p1000\p4p710p8g001:j11Tg001_j1FTg002=j1BTg002`j1=Tg003Bj24Tg003hj1DTg004Hj30Tg004hj4STg005]j1@Tg006;j17Tg006Zj1?Tg007:j1ITg007Xj1HTg0086j1jTg008aj29Tg009Dj2YTg009fj2:Tg00:@j2WTg00:lj32Tg00;Fj3UTg00;ej4RTg00<WR0j25Tg00=3R1j1QTg00=Sj2OTg00=jR2j2<Tg00>Dj2>Tg00>aR3j28Tg00?>j2JTg00?`j2NTg00@<j26Tg00@Wj2ATg00A1j2PTg00AOj2TTg00B2j4CTg00B]j7iTg00CAj1hTg00Ccj3gTg00DFj8fTg00Djj4eTg00EUj2^Tg00F5l9]Tg00Foj1\Tg00G^j4[Tg00Hcj3ZTg00IAj3_Tg00I`j2`Tg00JBj7aTg00Jfl<bTg00KKlBXTg00L1l<cTg00LVj6dTg00M:j7VTg00M^R4f1R5g00N<f0R6CCp=;P5g00NcR7g00OBR8P8g00ObR9P6g00PBFap=3P4g00PbR:P4P4P1f4R1g00QAR;f3R<g00Qaf2R=P5P6M<bp=MP:P:P:P4P4P4g00RNP;P;P;P3g00Rnf5R3P1P<P=P5P6MBXp=LP:P4P2P;P0g00SQP3P1P<P=P5P6M<cp=KP5P7P8P8P9P6Edp=EP=P7P8P8P9P5P6FVp=Gg00T3R0#1#1R;#1R2#1#1#1#F#B%F2R2#BR:#=[g00TXR>P1P<142=R?1425R@1426%D:RA90:?50:50:50:CSP>P3P1142<R2A0:2A90:@90:?50:R?%@0R@g00UM#7R2P6g00UlRA#DRB%?ARA%I4%H4RC%j4RDg00VXRE,94RF194@RG';'31YD9RHP6P=g00W6RIg00WVRJ':1W6==2IJdAU4E5CRRJb1b4b515E@P6b0%Q@RI/O2RK%72#7#7RL'<1>E@RM/8@RN%@;R;'5PKPNPIPMP6X741>E6X74P@P@1:4@RNDMP2P@PNELPLP;1:4;EK1JE@1NE@RLA24M@'615@ERNA24ME'6'APMP4p-0RMPBPA1P45PCPDP7P8P8P9PDP7P8P8P91ED<P41T40R0g00X6PGCC,3D5GD1;GF,3D1ED15GDFi%h8Ag40G194;';,3DGfPHPJb1b4b5X64X2MW3A246@,6516N='A185@/5;[^64^2M^3MP6A245EPLP5P=O4b0b@b:Ce1^:?,<KeM9]%?:RK#=P>P3181@#\P2C[AZ:I?9_:2,`K32P6b;W9X>4X?4X=4X84W<o"). Qed.

Section DISP.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma x1_tab_len : forall (cells : list deltX1) tl mtl, zlen cells = 2^(mtl+1) -> 0 <= tl <= mtl + 1 -> 0 <= mtl ->
    zlen (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells)) = 2 * 2^tl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_adisp ()) ["CANSEC1"; "DISP"] "h04__p1h14__x1h24cstrh37__arithh44__ffh58__varmaph65__with74__x2h81xh94__p2h:4__x3h;4__x4h<4__x5h=1nh>1Hh?2H0h@2H1hA2H2hB2LChC1MhD1ThE5cellshF3mtlhG2tlhH1yhI2z1hJ2z2p&0p;1p;2p;4p;3p;5p;<p;6p;7p;8p;Bg006Zj1aTg00QAR0j16Tg001:j1RTg005]j1bTg00>aj2ATg00X]j27Tg00<Wj25Tg00@<j24Tg00Y:R1j23Tg00=3R2j1PTg001_k109Tg002=k107Tg00YWk102Tg00EUj2NTg00ZWj2QTg006;j1:Tg00Znj2\Tg00[Ej1TTg003hj1rTg007:j1pTg007Xj1oTg0086j1nTg008aj2UTg00B2j4MTg009Dj2iTg009fj2GTg00:@j2fTg00:lj3Ik101Tg00;Fj3eTg00;ej4dTg00?`j2<Tg00A1j2HTg00[jj4JTg00AOj2FTg00Ccj3cTg00CAk108Tg00\Hk506Tg00\ok405Tg00>Dj2OTg00]WR3j2VTg00^4k100Tg00L1l<xTg00?>j2tTg00@Wj2LTg00^Rj2sTg00_4j1[Tg00_Rj2WTg00`3j3DTg00`\j2ZTg00aEj2qTg00anj3ETg00bWj2STg00cCj1YTg00chj3XTg00Djj4uTg00dKj1vTg00eLj1wTg000\j6^Tg00IAj3mTg00fTj3lTg00JBj7kTg00LVj6{Tg00M:j7|Tg00DFj8jTg00Jfl<_Tg00KKlB`Tg00g6j3hTg00g_k203Tg004Hk304Tg00B]j7gTg00hKR4f0R5'Np=>g00M^R6f1R7;I5p=2g00VXR8/55p=9P7g00NcR9g00OBR:P:g00ObR;P5g00PBFkp=1P7P9P:P:P;P5E{p=KP6P7g00N<P5CMp=Cf2R<P9P:P:P;P7P5F|p=Bf3R=P9P:P:P;P<P7P5Gjp=8P6g00PbR>P6P6P2f4R2P0P=g00QaP<P7P5M<_p=~P>P>P>P6P6P6g00iKP0P0P0P1g00ikf5R1P2P=P<P7P5MB`p=}P>P>P>P6P6P6g00jNP0P0P0P3g00jnP1P2P=P<P7P5MB`p=zP>P6P6P6P0P0P1P2P=P<P7P5M<_p=y1Z65p==Ah675p=0g00kQ-035p=@g00UlR0@0475p=;P6P7g00X6P5CMp=?P<P9P:P:P;P7P5Fgp=]%a4%><#6g00T3R4#RR9#bR3%b4R?,A5'7'2%9<R@1A7?RA,5<'4P>1732RB,33#PRC%R9RD#R$09$07RE&021RF'N'Q%65RG1731RH,33RI'2X=>P>g00UMRJ#:RK#:RL%>1RM'\%PI/Q5#6/2IX=>P3P21A=?RI%TMRN%6M#9RM%r0RO%a0R0%p6RP%o6RQ%n6RRP61U68RSg00l=RT1U63RUCM'11iR;R;P5P<g00W6RVg00WVRW'G1f5<=IVWdAe687CdRWb4b5b61<83P5b3RVb2PNPMp-0RMPOP0P61H6<P7PPCJPQPR1KR21F64RN1F69RX1U6?5c6'C,1RRY5BR&08:R:PYC8P;PWb4b5b6X16X76W0155A,4<1A<?,57[^16^76^0MP5f6RA#9P1PAP=O4b3b2I06173I,5BP3P1%>ARB#TRI%6B#9RBPVb2PIPBPOP01H67PQPR1CSN,1RRB1KR=5BRP:PBC8P;PWb4b5b6X16X0M%95/47%97[^16^0MP5f7RB1AA?'5PBP2O3b3b2H051<8H173A,33RH#PRI%>BRV,\LRY'QRZ#6R[/2H1O8HR\%6VR],33R^'VR_/2HP6P6&016R`P5X86RaP`1275$00XH6X86P[P_PaPa1G6GX8>PZP_PIP\Pa1O85X86PHPH1G6HRaD~PYP^PLP31G63PVP]1G6]E}EzEyPHPHPaM<x%TV%9]173B,33R],t81<8]1O8]RV/2]'415]8AI6V8'4'Lf8RV,73,33,O8P6f:R]#>#6,33Ra,s51<5a1V5aRH/25'415a512Ha'4'Lf;RH#>#6,33,V7P6%[4,W6Ra%:LR^#:#:RY#:R\#:RI#=R_5D6%[9,W6R9%=KRK5D61Z6JRJ'0RZ'01q63R>=E6JRG%=YRY9E6>%=LRL9E6>'0,0_'0#@'S%=\R\%=^R^9E6>'0#@R_AE6>K/0J,0\%:I#=AD69L,0\'0,0G#@'SAD6a\RG/0Z10J^#@'SAD6aY/0J,0G#@10YJ,0\#@1;_O,;_';';';';';';P0P6P61H62P<PPCJP7P6PPP=1H61CJCJPQPR1KRB%Y4R4#Y,F6RQ,?N,1R5BR1F64R49X6URP/CQ,1R1?NP,1R5BR5]RP:PR1KRVAX6UXRU,?Q,1R5BR1CUS,1R1?QS,1R5BR5]RP:PR1CS4,1RP:PRP6PSPTPXCM,1RP:PR1F6DRD,CX,1RP:PR1?4D,1RP:1?NU,1RC8C8C8C8C8C8P;PWb4b5b6X16X76X:6X;6X<6X0MX9M1252,41133<RW/52125W'4'L121W,4B15W8AI618'4'L%921<82151B12BV133B,2A[[[[[[^16^76^:6^;6^<6^0M^9MP5f<,73R5,33,<8f=#>#6R8,33,<=P=1AH?,73P8P5P7P<P2P1PAPBP]O=b3bJbAbIb@b2Cub?b>%v1,NE%w1E^AmECF,NEAlECFE^XC@WDWBXF6XG6WEo"). Qed.
  Lemma x2_tab_len : forall (cells : list deltX2) tl mtl, zlen cells = 2^mtl -> 0 <= tl <= mtl -> 0 <= mtl ->
    zlen (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes cells)) = 4 * 2^tl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_adisp ()) ["CANSEC1"; "DISP"] "h04__p1h14__x1h24cstrh37__arithh44__ffh58__varmaph65__with74__x2h81xh94__p2h:4__x3h;4__x4h<4__x5h=1nh>1Hh?2H0h@2H1hA2H2hB2LChC1MhD1ThE5cellshF3mtlhG2tlhH1yhI2z1hJ2z2p&0p;1p;2p;4p;3p;5p;<p;6p;7p;8p;Bg006Zj1aTg00QAR0j16Tg001:j1PTg005]j1`Tg00X]j27Tg00<Wj24Tg00@<j25Tg00Y:R1j23Tg00=3R2j1OTg001_j1bTg002=k107Tg00ldk104Tg00EUj2LTg00ZWj2TTg006;j1;Tg00Znj2[Tg00[Ej1RTg003hj1rTg007:j1pTg007Xj1oTg0086j1nTg008aj2STg00B2j4GTg009Dj2hTg009fj2FTg00:@j2eTg00:lj3Hk102Tg00;Fj3dTg00;ej4cTg00?`j2<Tg00A1j2MTg00[jj4JTg00AOj2CTg00CAk106Tg00\Hk505Tg00\ok403Tg00>Dj2NTg00]WR3j2UTg00^4k101Tg00L1l<vTg00?>j2uTg00@Wj2ITg00^Rj2sTg00_4j1VTg00_Rj2XTg00`3j3DTg00`\j2ZTg00aEj2qTg00anj3ETg00bWj2QTg00cCj1YTg00chj3\Tg00Djj4mTg00mdj1tTg00nej1lTg000\j6]Tg00IAj3wTg00fTj3kTg00JBj7jTg00LVj6{Tg00M:j7iTg00DFj8|Tg00Jfl<^Tg00KKlB_Tg00g6j3~Tg00g_k200Tg004Hj3gTg00B]j7fTg00omR4f0R5'Lp=>g00M^R6f1R7;H5p=2g00VXR8/45p=8P7g00NcR9g00OBR:P:g00ObR;P5g00PBFjp=1P7P9P:P:P;P5E{p=KP6P7g00N<P5CGp=Bf2R<P9P:P:P;P7P5Fip=Af3R=P9P:P:P;P<P7P5G|p=:P6g00PbR>P6P6P2f4R2P0P=g00QaP<P7P5M<^p=}P>P>P>P6P6P6g00iKP0P0P0P1g00ikf5R1P2P=P<P7P5MB_p=zP>P>P>P6P6P6g00jNP0P0P0P3g00jnP1P2P=P<P7P5MB_p=yP>P6P6P6P0P0P1P2P=P<P7P5M<^p=x1Z65p==A~675p=0g00kQ-005p=@g00UlR0?g75p=9P6P7g00X6P5CGp=?P<P9P:P:P;P7P5Ffp=W%a4%><#6g00T3R4#PR9#`R3/75'2%8<R?14<7'5P>%P9R@#`RA1732RB'3#ORC%P@#b$07RD&041RE'L'T%65RF1731RG,3ARH'2X=>P>g00UMRI#;RJ#;RK#;RL#;RM%>1RN'[%OH/T5#6/2HX=>P3P2P=%RNRH%6N#8RN%r0RO%a0R0%p6RP%o6RQ%n6RRP61S68RSg00l=RT1S63CG'11hR;R;P5P<g00W6RUg00WVRV'F1e5<=HUVdAd687CcRVb4b5b61<83P5b3RUb2PHPNp-0RNPOP0P61M6<P7PPCJPQPR1KR21C64RH1C69R9'B,1RRW5AR&06:R:PWC:P;PVb4b5b6X16X76W01457,5<147<[^16^76^0NP5f6RW#8P1PWP=O4b3b2I05173=,4BP3P1%>WRB#RRX%6B#8RBPUb2PXPBPOP01M67PQPR1BSH,1RRB1KR=5ARP:PBC:P;PVb4b5b6X16X0N%85/57%87[^16^0NP5f7RB/4WPBP2O3b3b2H031<8G173W,3ARG#ORX%>BRU,[MRY'TRZ#6R[/2G1N8GR\%6UR],3AR^'UR_/2GP6P6&026R`P5X86RaP`1275$01XH6X86P[P_PaPa1F6FX8>PZP_PXP\Pa1N85X86PGPG1F6GRaD}PYP^PMPA1F6APUP]1F6]EzEyExPGPGPaM<v%RU%8]173B,3AR],u81<8]1N8]RU/2]'514]8AH6U8'5'If8RU,73,3A,N8P6f:R]#>#6,3ARa,s51<5a1U5aRG/25'514a512Ga'5'If;RG#>#6,3A,U7P6%V4,X6Ra%;MRM#;R^#;RY#=R\5D6%V@,X6RX%=JRJ5D61Z6IRI'0R_'01q6ARZ=E6IR>%=MRM9E6Z%=KRK9E6Z'0,0\'0#@'Q%=^R^%=LRL9E6Z'0#@R\AE6ZJ/0I,0^%;Y#=AD6XK,0^'0,0>#@'QAD6a^R>/0_10IL#@'QAD6aM/0I,0>#@10MI,0^#@19\O,9\'9'9'9'9'9'9P0P6P61M62P<PPCJP7P6PPP=1M61CJCJPQPR1KRB%Y4R4#Y,C6RQ,?H,1R5AR1S6ARP1C64R45\6R0/BQ,1R1?H0,1R5AR5WRP:PR1KRUA\6P9RP,?Q,1R5AR1BPS,1R1?QS,1R5AR5WRP:PR1BS4,1RP:PRP6PSPTP9CG,1RP:PR1C6@R@,B9,1RP:PR1?4@,1RP:1?HP,1RC:C:C:C:C:C:P;PVb4b5b6X16X76X:6X;6X<6X0NX9N1252,5113A<RV/42125V'5'I121V,5B14V8AH618'5'I%821<82141B12BU13AB,2W[[[[[[^16^76^:6^;6^<6^0N^9NP5f<,73R5,3A,<8f=#>#6R8,3A,<=P=173GP8P5P7P<P2P1PWPBP]O=b3bJbAbIb@b2Cmb?b>%t1,LD%l1E]AwDCE,LDAkDCEE]XC?WDWBXF6XG6WEo"). Qed.

  (* [comment removed for export] *)
  Lemma disp_src_bound : forall L RNG st LB m S (src : list Z), AHEAP AI L RNG st LB m -> src_inA LB S src ->
    S + zlen src <= ATOP \/ src = [].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_adisp ()) ["CANSEC1"; "DISP"] "p'0h01Hh13RHIh23RLOh32chh41nh51Ah63SINh74__x1h81xi001xh91ph:7__arithh;4__ffh<8__varmaph=5__with>4__x2h?4__x3h@4__x4hA4__x5hB4cstrhC2AHhD2H1hE2H2hF3HinhG1LhH2LBhI2R1hJ2R2hK2R3hL2R4hM3RNGhN1ShO2_HhP3_H0hQ1chR1ehS1mhT3srchU4src'hV2sthW1yi011li021zp&0p;1p;7p;3p;2p;4p;<p;8p;6g006ZR0j1aTg001:j11Tg001_j1mTg002=j1rTg002`j1oTg010mk70>Tg011kj3VTg00QAR1j16Tg012jj1{Tg003hj1dTg00:lj37Tg00@Wk20ITg009fj2RTg013`k30CTg006;R2j1]Tg00?`R3j2PTg005]j1DTg00>aj20Tg00^4k106Tg00[Ej1eTg00A1j2_Tg007Xj1zTg0086j1xTg008aj2qTg00AOj2STg00CAj1sTg00Ccj3YTg00B2j4cTg009Dk20KTg00:@k20JTg00;Fk30HTg00;ek40GTg00Djk40FTg014:j1HTg0153j3GTg015lR4j2WTg00<Wj22Tg016Fm<0BTg017Gj3QTg00cCj1:Tg018Dk40=Tg018Xk40<Tg00I`k20;Tg0191k10:Tg019nk108Tg01:oj1iTg01;gk207Tg01<Dj1gTg01==j3NTg01>0j3fTg01>ek100Tg00`\j2[Tg00g6j3hTg00g_j2~Tg004Hj3OTg007:j1}Tg00[jj4^Tg01?ck309Tg00EUj2KTg00Jfl<jTg00L1l<yTg00JBk70?Tg00DFk80@Tg01@=k30ATg00@<R5j23Tg01@Tj1wTg01AQk10DTg01BJj6vTg01B^j2uTg01C>j4pTg01D0j3tTf0R6#1#1p=Tg00M^R7/K6p>05f2R8f1R9'0/26p=I1K79#6,08/26p>0EAO796p=l1K76#6p=kg00PbR:P:P7P7P2P1P1f3R2g01DnP8P9P6M<jp>04P:P7P7P7P1P1f5R1f4R;P2P8P9P6M<jp>03P7P7P3P1P3P;g00VXR3P3P2P8P9P6M<yp>021236p=JP7P9g00N<P6Ccp=XP9g00NcR<g00OBR=P=g00ObR>P6g00PBK0?p=MP2P<P=P=P>P8P9P6L0@p=bg01ERR<@0A96p=9AO789,K7#6,02/26p=41289/36,32p=81W76p=5AO796,K7p=`%66,09p=n1289/36p=Fg00W6R?%w6g01FK37p=AA7796p=CA7789/36p==f6R@g01FkRAg01GbRBP1P;P2&0D8Ev;79/36p=@%16#1#1#1p=\1u96=773p=?AN1;2g00TXRCP8P9P6Cp'3p=Bf7RD121;1028/29/36'3,3@'3p=<AtD@1PCP;P2P8Cp1WB91W76'3'3'3p=;%i21089#g5N;/36p=>AN289/36p=L1396,38p=Z1028/29/36p>01%:6#:#:#:p=E%16#1#1#1#1#1#1#1p=UAO796,K7#6p=|g01H]g01IWg01JP%a<g00T3R<#1RC#1RE#1RF#1RG#TRH#m#r%mF#r#o[%a7RFp,2rcRIp,2AIRJP@P1P;P2P8K0>AV;89P0P7AV@;6&059R0#6RK%{IRL5I1%d7RM97F9+0I]6P8AV12MB0E;MLA7FMM1RFM40CW6f9RN1l967VDf8RO1l89RP#kRQ;ILA7FPMP6%]0RP#6RM,P3%D<RR,0KRS,P3P6X87RT1P96$06XW7X871R73PMPSPTPT%66,R7X8:PPPS106RX87P0PK1R7KH04J03J02%e0%JKg00UlRK#dR0%aKRS1_79%z7RP%x7R:1q73RT1S7<RM'X,M:%s=R=P7PTg00l=1q7R9Y7MCc,M:Cb20K:>R>P6P8g00WVRT,R?20J68=7?TdB0H739H0GRTb;b<b=X77%J6109R,P3[^77P6%k2P9O2b:bBH0F1P3QeO1%H8?G96RQf=R3'9P9f;R?P?P1P;1096RUC4C8X47#5X57#5X9A,WAP4PAf>RV,9QP9f<RWPWP@P1PUC4C8X47#5X57#5X9Af:RXP;P2PLC4P6f@RY,9QP9PV1`OD,nVRQ/2UC8X47#5X57#5P4P7%H2?G96fARZ'9P9f?R[P[PNPOPUC4C8X47#5X5712QLP6%H1?G96fCRQ'9P9PZPZP?PXPUC4C8X47#5P4P7%H@?G86fDR@'9P8fBR41`W?,n4RU1086'2C8X4712ULP6%HO?G;6fFRU'9P;P@P@PVP310;6C4C8P5%HN?G19fGR\'9fER]P]P[PV1019C45F1PUPYP[PLC4P6%H??GD2fIRD'9fHR^P^P4PZ10O;C45FOP512NDPDPQP410N1C4fJR_P@PQPLC4P6fKR`,2?fLRaPUP]10WOC4PIPJfRRJfQROfPRbfORcfNRdPZP3PNP`P1N<0Bg01KKRe,2N9FRNAQI3NPOP3PNPOP3PN%:<R<#:Rf#DRgPdP3PNPdP3PN%oBRNg01LCRhg01LaRig01M:RjPBH0=RkPhPiPjPBH0<RjP4PO20;B6Ri&0:6Rh%AX&089Rl,C[[7=XF@X3B%TH#\#DRm,?9Rn1?6mRm%DHRH,09RoP[10[?PHP6fSRp%i9Rq20769#gRrPbPqPrEBG<X17#5X27G;D>CL3ZP512Xe9FRXAQIVXANJVXPJPVPXPgPcPVPXPcPVPXPNPkPjPQPJPi%A?1CYl[9=h?F@X3BPnPmPoPY10YWPHP6fTR?PqPrPOPqPrEBG<X17#5X27G;D>3ZPcPDP^PLC4P612We9FRWAQIZ3fURW?NZ3PWPZP3PgPJPZP3PJPZP3PNPkPjPUPWPi%AV1CQl[9=hVF@X3BPnPmPoPQ10Q[PHP6fWR3PqPrP?PqPrEBG<X17#5X27G;D>3ZP5AQI4VfVRJP4PVPJP4PVPgPpP4PVPpP4PVPNPkPjP\PJPi%A[1C@l[9=h[F@X3BPnPmPoP@10@YPHP6fXR[PqPrPWPqPrEBG<X17#5X27G;D>CLPpfMRVPaPLC4P6AQI@YP510]ZRY9fI]%JZPYPL%DGRG,?]C8fZRYPUP4PYPUP4PgP3PUP4P3PUP4PNPkPjP`PYPi%AQ1C^l[9=hQF@X3BPnPmPoP^10^@RYPHP6f\R4PqPrfYRZPqPrEBG<X17#5X27G;D>CLP3POPbPLC4[P610\Q9fI\%J@PYPL1?^GC8P5%J]PDP]PL1?DGH01f^R]P_PUP]P_PUPgf[RYP_PUPYP_PUPNPkPjPcP]Pi%A\1Cal[9=h\F@X3BPnPmPoPa10a^RUPHP6f`PqPrf]R@PqPrEBG<X17#5X27G;D>CLPYPWP?PLC4[P6%J\1?aG9FULP5AIVDL1?VGfbRDPdP_PDPdP_Pgf_R5PdP_P5PdP_PNPkPjPpPDPi%A`1Cbl[9=h`F@X3BPnPmPoPb10baPHP6fdRaPqPrfaPqPrEBG<X17#5X27G;D>CLP5PZP[PLC4[P6AIc`L1?bGfeRGPOPVPGPOPVPgPDPOPVPDPOPVPNPkPjPJPGPi%Ad1Cpl[9=hdF@X3BPnPmPoPp10pcPHP6fgPqPrPaPqPrEBG<X17#5X27G;D>CL&00I%Ef#E#ERf#1#E#E#1#T#\#U#U#D%:f#E#E#1#T#\#U#U#D,2L7FL1`@4R@#e%6@#Jg00UMR@#]R4#],[71[741[7@5h75h7g00kQ'~=OK0PSP7P71_7;P8%}7RSC^P9P71_71P2PSC^C^PPP:1S7E%:C,S75Y7RE1S7<R<'X,M:P=P:1S7C9Y7MRM/XE,M:P=1XM<,M:CbCbP>PTb;b<b=X77X>7X?7X@7XA7AI2;810;19I98AI82;[[^77^>7^?7^@7^A7P6POPWPL1|5]PGP1P^O7b:bBb0WPWLWKP9P6O2n2001000000121000000W0WJP9P6O2n2001000000121000000W0WIP9P6O2n2001000000121000000W0P9P6O2n2001000000121000000W0WOP9P6O2n2001000000121000000b0WEWDP9P6O2n2001000000121000000W0WFP9P6O2n2001000000121000000W0X47P9P6O2n2001000000121100000W0X57P9P6O2n2001000000121100000W0X9AP9P6O2n2001000000121100000bR409W6XUFXQ7P9P6O2n10110100020021102101P6O1W6WCWTXN7WSWHWVWMWGo"). Qed.

  (* [comment removed for export] *)
  Ltac dec_ifF := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let b := eval vm_compute in c in change c with b; cbv iota end.

  (* [comment removed for export] *)
  Lemma disp_post : forall L RNG st LB (m m0 : amem) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) FR fc DST dcap lo ms',
    AHEAP AI L RNG st LB m -> ATOP + 4096 + 16 <= bv_unsigned sp ->
    munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m0 -> wmono bsegs m m0 ->
    huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0 ms' ->
    huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m ms'.
Proof.
  intros L RNG st LB m m0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc DST dcap lo ms' AH SPB MU WM
    (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & HMS & MI & ST & MG & AH').
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [exact HMS |]. split; [exact MI |]. split; [exact ST |]. split; [| exact AH'].
  eapply magree_trans; [| exact MG].
  apply (munch_magreeA _ _ _ _ MU WM).
  intros a [HC _]. cbn [outside]. split; [| exact I].
  pose proof ATOP_range as AT. unfold ATOP_MIN, ATOP_MAX in AT.
  unfold aclient_addr in HC.
  destruct HC as [HC | [(iv & HIN & HR) | [(b & HIN & HR) | (a' & HA' & ->)]]].
  - lia.
  - pose proof (AI_aci_img AI iv HIN). unfold AIMG_HI in *. lia.
  - pose proof (AI_block_bounds AI L RNG st LB m b AH HIN). unfold AIMG_HI in *. lia.
  - assert (RA : 0 <= a' < 2^47).
    { destruct HA' as [HA' | [(iv & HIN & HR) | (cls & A & n & HIN & HR)]].
      - lia.
      - pose proof (AI_aci_img AI iv HIN). pose proof (AI_aci_lo AI iv HIN). unfold AIMG_HI in *. lia.
      - pose proof (AI_block_bounds AI L RNG st LB m _ AH HIN) as BB. cbn [ab_addr ab_size] in BB.
        unfold AIMG_HI in *. lia. }
    pose proof (shad_in_band a' RA). lia.
Qed.

  Definition disp_walk_stmt (KEEP : bool) (E X1 X2 : Z) : Prop :=
    forall (Q : machine_state -> Prop) (RNG : footprint) (m : amem) (F : bvmap 5 word) (fc : bv 32)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (lo DT DTL mtl tt tl : Z),
    artcells m -> mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
    ATOP + 4096 <= lo -> bv_unsigned sp <= 2^47 -> rng RNG (bv_unsigned sp - 16) 16 -> rng_aimg RNG ->
    bytes_at bsegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 tt; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
    unpoisoned m DT (DT + DTL) -> DT mod 16 = 0 -> 12 <= DTL -> AIMG_HI <= DT -> DT + DTL <= ATOP ->
    rng RNG DT DTL -> rng RNG (shad DT) (shlen (DTL + 7)) -> (tt = 0 \/ tt = 1) ->
    (tt = 0 -> forall mm (y5 y6 y7 y16 y17 y28 y29 y30 y31 : word),
       munch [(bv_unsigned sp + -16, bv_unsigned sp)] m mm -> wmono bsegs m mm -> mem_inv bsegs mm -> stk bsegs mm lo (bv_unsigned sp) ->
       evtF bsegs RNG Q (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 DT) (if KEEP then a5 else Z_to_bv 64 tt) y16 y17
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                           F (Z_to_bv 64 X1) fc None mm (seg_rom bsegs))) ->
    (tt = 1 -> forall mm (y5 y6 y7 y16 y17 y28 y29 y30 y31 : word),
       munch [(bv_unsigned sp + -16, bv_unsigned sp)] m mm -> wmono bsegs m mm -> mem_inv bsegs mm -> stk bsegs mm lo (bv_unsigned sp) ->
       evtF bsegs RNG Q (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 DT) (if KEEP then a5 else Z_to_bv 64 tt) y16 y17
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                           F (Z_to_bv 64 X2) fc None mm (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 E) fc None m (seg_rom bsegs)).

  Ltac dwalk :=
    intros Q RNG m F fc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 lo DT DTL mtl tt tl
      ART MI ST LOS LOA SPH RFR WIM HHD UDT DT16 DTL12 DTLO DTHI RDT RSH TT K1 K2;
    pose proof ATOP_range as AT; unfold ATOP_MIN, ATOP_MAX in AT; unfold AIMG_HI in DTLO; unfold artcells in ART;
    let rec dc H := lazymatch type of H with
      | _ /\ _ => let H1 := fresh "RT" in let H2 := fresh "RT" in destruct H as [H1 H2]; dc H2 | _ => idtac end in
    dc ART;
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU; pose proof (wmono_refl bsegs m) as WM;
    carve_frame 16%nat ST;
    lazymatch goal with FR0 : rw_cells bsegs _ (bv_unsigned _ + -16) [CB 16 _] |- _ =>
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8]%nat) in FR0; [| reflexivity]; cbn [mk_CB_cells app] in FR0 end;
    do 4 zstep;
    assert (DT4 : Z.land DT 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - DT16; Z.div_mod_to_equations; lia);
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?e) (Z_to_bv 64 0)) then _ else _) _ _ _ _) =>
      replace e with 0 by (symmetry; first [ exact DT4
        | rewrite <- Z.land_assoc; lazymatch goal with |- Z.land DT (Z.land ?k 3) = 0 =>
            let v := eval vm_compute in (Z.land k 3) in change (Z.land k 3) with v; exact DT4 end ]) end;
    dec_ifF;
    do 5 zstep;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr DT 3 + ?C)] =>
        assert (UM : unpoisoned mm DT (DT + DTL))
          by (eapply unpoisoned_munch; [exact UDT | exact MU | cbn [disjoint_from]; split; [| exact I];
              pose proof (shad_in_band DT ltac:(lia)); pose proof (shad_in_band (DT + DTL - 1) ltac:(lia)); lia]);
        assert (HSR : ov_read_bytes bsegs mm (Z_to_bv 64 (Z.shiftr DT 3 + C)) 1 = Some [Z_to_bv 8 0])
          by (eapply unpoisoned_full_rd; [exact UM | unfold shad, ASHOFF; lia
              | unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - DTL12; Z.div_mod_to_equations; lia]);
        assert (RSA : rng RNG (Z.shiftr DT 3 + C) 1)
          by (eapply rng_sub; [exact RSH | unfold shad, ASHOFF; lia
              | unfold shad, shlen, ASHOFF; rewrite (Z.shiftr_div_pow2 (DTL + 7)) by lia; change (2^3) with 8;
                clear - DTL12; Z.div_mod_to_equations; lia])
      end;
      pose proof (desc_tt_rdA mm DT mtl tt tl HHD) as HTR
    end;
    do 2 zstep; dec_ifF;
    do 2 zstep;
    destruct TT as [-> | ->]; dec_ifF; do 3 zstep;
    lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -16) _ |- _ => release_frame H ST (bv_unsigned sp) end;
    [ eapply K1 | eapply K2 ]; first [ reflexivity | eassumption ].

  Lemma disp1_walk : disp_walk_stmt false AHUF_DEC_1X AHUF_DX1_1X AHUF_DX2_1X.
  Proof. unfold disp_walk_stmt, AHUF_DEC_1X. cbv beta iota. dwalk. Qed.

  Lemma disp4_walk : disp_walk_stmt true AHUF_DEC_4X AHUF_DX1_4X AHUF_DX2_4X.
  Proof. unfold disp_walk_stmt, AHUF_DEC_4X. cbv beta iota. dwalk. Qed.

  Lemma bytes_at_fr : forall (m mm : amem) sp A bs, bytes_at bsegs m A bs -> munch [(sp + -16, sp)] m mm ->
    A + zlen bs <= sp + -16 -> bytes_at bsegs mm A bs.
  Proof.
    intros m mm sp A bs H MU HL. eapply bytes_at_transport; [exact H | exact MU | cbn [disjoint_from]; split; [lia | exact I]].
  Qed.

  Lemma bytes_at_nil_any : forall (m mm : amem) A, bytes_at bsegs m A [] -> bytes_at bsegs mm A [].
  Proof.
    unfold bytes_at. intros m mm A (H1 & H2 & _). split; [exact H1 | split; [exact H2 | intros i Hi; cbn [length] in Hi; lia]].
  Qed.

  Ltac dpre AH HDT LOS WSK :=
    lazymatch type of HDT with In (HB ?pdt ?DT (DTABLE_BYTES ?mtl)) _ =>
    lazymatch type of AH with AHEAP _ ?L ?RNG ?st ?LB ?m =>
    pose proof (hb_unpoisoned AI L RNG st LB m pdt DT (DTABLE_BYTES mtl) AH HDT) as (UDT & DT16 & DTN & DTB & DTT & RDT & RSH & WDT);
    pose proof (AI_rtcells AI L RNG st LB m AH) as ART;
    pose proof (AI_layout AI L RNG st LB m AH) as (_ & _ & ALT & _);
    pose proof (ablk_lin _ _ DTB) as (DTL0 & _ & _ & _);
    pose proof ATOP_range as AT; unfold ATOP_MIN, ATOP_MAX in AT;
    unfold HUF_DEC_STACK_A in LOS;
    let sp := lazymatch type of LOS with _ <= bv_unsigned ?sp - _ => sp end in
    assert (RFR : rng RNG (bv_unsigned sp - 16) 16) by (eapply rng_sub; [exact WSK | lia | lia]);
    assert (DTL12 : 12 <= DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; pose proof (Z.pow_le_mono_r 2 1 mtl ltac:(lia) ltac:(lia)) as P2;
          change (2^1) with 2 in P2; lia)
    end end.

  Lemma disp_frame_facts : forall L RNG st LB (m mm : amem) (sp : word) lo rstk S src,
    AHEAP AI L RNG st LB m -> munch [(bv_unsigned sp + -16, bv_unsigned sp)] m mm -> wmono bsegs m mm ->
    ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 8192 -> bv_unsigned sp + 16 < al_top L ->
    bytes_at bsegs m S (map (Z_to_bv 8) src) -> src_inA LB S src -> rclean m rstk ->
    AHEAP AI L RNG st LB mm /\ bytes_at bsegs mm S (map (Z_to_bv 8) src) /\ rclean mm rstk.
  Proof.
    intros L RNG st LB m mm sp lo rstk S src AH MU WM LOA LOS SPT SBY SIN RCL.
    pose proof (AI_layout AI L RNG st LB m AH) as (_ & _ & ALT & _).
    pose proof ATOP_range as AT. unfold ATOP_MIN, ATOP_MAX in AT.
    split; [| split].
    - eapply (AI_frame AI); [exact AH | exact MU | exact WM | constructor; [left; left; cbn [fst snd]; lia | constructor]].
    - destruct (disp_src_bound L RNG st LB m S src AH SIN) as [SBd | SBd].
      + eapply bytes_at_fr; [exact SBY | exact MU | rewrite length_map; lia].
      + subst src. cbn [map] in SBY |- *. eapply bytes_at_nil_any. exact SBY.
    - eapply rclean_transport; [exact RCL | exact MU | exact WM |].
      unfold appW. apply Forall_cons; [cbn [fst snd]; unfold KHIGH, KLOW; lia | apply Forall_nil].
  Qed.

  Lemma x1_tab_fr : forall (m mm : amem) sp DT mtl, x1_tabA m DT mtl -> munch [(sp + -16, sp)] m mm ->
    1 <= mtl <= 12 -> DT + DTABLE_BYTES mtl <= sp + -16 -> x1_tabA mm DT mtl.
  Proof.
    intros m mm sp DT mtl (tl & cells & HH & HC & HOK & HTL & HTB) MU MTL HB.
    unfold DTABLE_BYTES, HufHarness.DT_BYTES in HB.
    assert (TLR : 1 <= tl <= HUF_TABLELOG_MAX) by (destruct HOK as [X _]; exact X).
    exists tl, cells.
    split; [eapply bytes_at_fr; [exact HH | exact MU | cbn [length]; lia] |].
    split; [exact HC |]. split; [exact HOK |]. split; [exact HTL |].
    pose proof (Z.pow_le_mono_r 2 tl (mtl + 1) ltac:(lia) ltac:(lia)) as P1. rewrite Z.pow_add_r in P1 by lia.
    change (2^1) with 2 in P1.
    eapply bytes_at_fr; [exact HTB | exact MU |].
    rewrite (x1_tab_len cells tl mtl HC ltac:(lia) ltac:(lia)). lia.
  Qed.

  Lemma x2_tab_fr : forall (m mm : amem) sp DT mtl, x2_tabA m DT mtl -> munch [(sp + -16, sp)] m mm ->
    1 <= mtl <= 12 -> DT + DTABLE_BYTES mtl <= sp + -16 -> x2_tabA mm DT mtl.
  Proof.
    intros m mm sp DT mtl (tl & cells & HH & HC & HOK & HTL & HTB) MU MTL HB.
    unfold DTABLE_BYTES, HufHarness.DT_BYTES in HB.
    assert (TLR : 1 <= tl <= HUF_TABLELOG_MAX) by (destruct HOK as [X _]; exact X).
    exists tl, cells.
    split; [eapply bytes_at_fr; [exact HH | exact MU | cbn [length]; lia] |].
    split; [exact HC |]. split; [exact HOK |]. split; [exact HTL |].
    pose proof (Z.pow_le_mono_r 2 tl mtl ltac:(lia) ltac:(lia)) as P1.
    eapply bytes_at_fr; [exact HTB | exact MU |].
    rewrite (x2_tab_len cells tl mtl HC ltac:(lia) ltac:(lia)). lia.
  Qed.

  Theorem huf_dec_1x_dispA :
    dec1_int_stmtA AI rng_fs x1_tabA AHUF_DX1_1X -> dec1_int_stmtA AI rng_fs x2_tabA AHUF_DX2_1X ->
    huf_dec_stmtA AI rng_fs huf_dt_okA AHUF_DEC_1X.
Proof.
  intros D1 D2 L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m st LB DST dcap S DT mtl flags pdt src lo rstk AH NF BLK MTL HDT DTOK HOUT DCAP SBY SF SL S16 SIN DS1 DS2 DS3
    ST LOA LOS RCL RLO RHI RRL SPT SP16 MI HTP FLG HI WSK WIM WIMS WFS WRS -> -> -> -> -> ->.
  dpre AH HDT LOS WSK.
  destruct (huf_dt_okA_cases m DT mtl DTOK) as [XT | XT]; pose proof XT as (tl & cells & HH & HC & HOK & HTL & HTB).
  - eapply (disp1_walk _ RNG m FR fc ra sp gp tp t0 t1 t2 s0 s1 _ _ _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              lo DT (DTABLE_BYTES mtl) mtl 0 tl); try (first [eassumption | lia]); try (intros HF; discriminate HF).
    intros _ mm y5 y6 y7 y16 y17 y28 y29 y30 y31 MU1 WM1 MI1 ST1.
    destruct (disp_frame_facts L RNG st LB m mm sp lo rstk S src AH MU1 WM1 LOA LOS SPT SBY SIN RCL) as (AH1 & SB1 & RC1).
    assert (TB1 : x1_tabA mm DT mtl) by (eapply x1_tab_fr; [exact XT | exact MU1 | lia | lia]).
    eapply evtF_mono;
      [ eapply (D1 L RNG ra sp gp tp y5 y6 y7 s0 s1 _ _ _ _ _ _ y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31
                FR fc mm st LB DST dcap S DT mtl pdt src lo rstk);
        first [ eassumption | reflexivity | exact I | unfold HUF_DEC_STACK_A; lia ]
      | intros ms' HP; eapply disp_post; [exact AH | lia | exact MU1 | exact WM1 | exact HP] ].
  - eapply (disp1_walk _ RNG m FR fc ra sp gp tp t0 t1 t2 s0 s1 _ _ _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              lo DT (DTABLE_BYTES mtl) mtl 1 tl); try (first [eassumption | lia]); try (intros HF; discriminate HF).
    intros _ mm y5 y6 y7 y16 y17 y28 y29 y30 y31 MU1 WM1 MI1 ST1.
    destruct (disp_frame_facts L RNG st LB m mm sp lo rstk S src AH MU1 WM1 LOA LOS SPT SBY SIN RCL) as (AH1 & SB1 & RC1).
    assert (TB1 : x2_tabA mm DT mtl) by (eapply x2_tab_fr; [exact XT | exact MU1 | lia | lia]).
    eapply evtF_mono;
      [ eapply (D2 L RNG ra sp gp tp y5 y6 y7 s0 s1 _ _ _ _ _ _ y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31
                FR fc mm st LB DST dcap S DT mtl pdt src lo rstk);
        first [ eassumption | reflexivity | exact I | unfold HUF_DEC_STACK_A; lia ]
      | intros ms' HP; eapply disp_post; [exact AH | lia | exact MU1 | exact WM1 | exact HP] ].
Qed.

  Theorem huf_dec_4x_dispA :
    dec4_int_stmtA AI rng_fs x1_tabA AHUF_DX1_4X -> dec4_int_stmtA AI rng_fs x2_tabA AHUF_DX2_4X ->
    huf_dec_stmtA AI rng_fs huf_dt_okA AHUF_DEC_4X.
Proof.
  intros D1 D2 L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m st LB DST dcap S DT mtl flags pdt src lo rstk AH NF BLK MTL HDT DTOK HOUT DCAP SBY SF SL S16 SIN DS1 DS2 DS3
    ST LOA LOS RCL RLO RHI RRL SPT SP16 MI HTP FLG HI WSK WIM WIMS WFS WRS -> -> -> -> -> ->.
  dpre AH HDT LOS WSK.
  destruct (huf_dt_okA_cases m DT mtl DTOK) as [XT | XT]; pose proof XT as (tl & cells & HH & HC & HOK & HTL & HTB).
  - eapply (disp4_walk _ RNG m FR fc ra sp gp tp t0 t1 t2 s0 s1 _ _ _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              lo DT (DTABLE_BYTES mtl) mtl 0 tl); try (first [eassumption | lia]); try (intros HF; discriminate HF).
    intros _ mm y5 y6 y7 y16 y17 y28 y29 y30 y31 MU1 WM1 MI1 ST1.
    destruct (disp_frame_facts L RNG st LB m mm sp lo rstk S src AH MU1 WM1 LOA LOS SPT SBY SIN RCL) as (AH1 & SB1 & RC1).
    assert (TB1 : x1_tabA mm DT mtl) by (eapply x1_tab_fr; [exact XT | exact MU1 | lia | lia]).
    eapply evtF_mono;
      [ eapply (D1 L RNG ra sp gp tp y5 y6 y7 s0 s1 _ _ _ _ _ _ y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31
                FR fc mm st LB DST dcap S DT mtl flags pdt src lo rstk);
        first [ eassumption | reflexivity | exact I | unfold HUF_DEC_STACK_A; lia ]
      | intros ms' HP; eapply disp_post; [exact AH | lia | exact MU1 | exact WM1 | exact HP] ].
  - eapply (disp4_walk _ RNG m FR fc ra sp gp tp t0 t1 t2 s0 s1 _ _ _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              lo DT (DTABLE_BYTES mtl) mtl 1 tl); try (first [eassumption | lia]); try (intros HF; discriminate HF).
    intros _ mm y5 y6 y7 y16 y17 y28 y29 y30 y31 MU1 WM1 MI1 ST1.
    destruct (disp_frame_facts L RNG st LB m mm sp lo rstk S src AH MU1 WM1 LOA LOS SPT SBY SIN RCL) as (AH1 & SB1 & RC1).
    assert (TB1 : x2_tabA mm DT mtl) by (eapply x2_tab_fr; [exact XT | exact MU1 | lia | lia]).
    eapply evtF_mono;
      [ eapply (D2 L RNG ra sp gp tp y5 y6 y7 s0 s1 _ _ _ _ _ _ y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31
                FR fc mm st LB DST dcap S DT mtl flags pdt src lo rstk);
        first [ eassumption | reflexivity | exact I | unfold HUF_DEC_STACK_A; lia ]
      | intros ms' HP; eapply disp_post; [exact AH | lia | exact MU1 | exact WM1 | exact HP] ].
Qed.
End DISP.
End CANSEC1.
