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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkMem HufWalkKit HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXGoM FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_ax1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import Stdio_kit ABytes AF_huf_tbl_iface2 AF_huf_bitd AF_huf_fdw_kit AF_huf_ax1b AF_huf_ax1d.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fdw_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax1e () := "C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begI47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC47Corelib4Init5Logic3notK47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic6or_indC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib5Lists4List2InK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K47Corelib4Init5Logic2or01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameK47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1e=ent_sp_boundsI47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_block_boundsC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic6eq_indC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergec5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1e:ent_magreec5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1e9ent_aheapC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax17AX1_EPIC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit28sgtz_andC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC5ARocqVerifyHarness?AgentSubmission5Plain<RF_huf_iface8x1_bytesC47Corelib4Init3Nat3minC47Corelib4Init3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit29x1_bytes'C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2@x1_bytes'_lengthC47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List=length_firstnC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface7x1_tabAI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface7src_inAC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface=hb_unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_rtcellsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8artcellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1e<ax1e_tab_lenC56Stdlib6ZArith6BinInt1Z9pow_add_rC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow>unpoisoned_nilC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission5BothW7RtCells=no_image_asanC5ARocqVerifyHarness?AgentSubmission4LibA6ShadowArw_cells_of_wr_atC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3ArrAu8arr_of_rw_cellsC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKitAbytes_of_unsignedC56Stdlib6ZArith6BinInt1Z7div_posC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow?unpoisoned_fullC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC35stdpp7tactics<f_equal_helpC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj1K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC47Corelib4Init3Nat3addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=bytes_at_readC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqK4ELinuxProcessSemantics5Riscv5Instr5instr03c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1e7ent_epiC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit=le2_two_bytesC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sltC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sltC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax14AX1MC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1g9ax1_smallC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1f7ax1_bigC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem:zx16_shortc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1e:sgtz_and_lC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9v_slt_b2zC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface>dec1_int_stmtAC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC46Stdlib9micromega;ZifyClasses9and_morphK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib3Mem;wr_at_writeC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface?HUF_DEC_STACK_AC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface;AHUF_DX1_1X".
Import ListNotations.
Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ENT.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap lo : Z).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -128).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HOUT : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis WSK : rng RNG lo (al_top L - lo).

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS11 := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma ent_sp_bounds : 0x10007fff8000 <= SPF /\ SP <= 2^47 /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP.
Proof using All.
  pose proof ATOP_range as AT. unfold ATOP_MIN, ATOP_MAX in AT.
  pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
  unfold HUF_DEC_STACK_A in LOS. lia.
Qed.

  Lemma ent_aheap : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
Proof using All.
  intros mm MU WM.
  pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
  assert (FST : aclient_range CI LB (ATOP + 4096) lo (SP - lo)).
  { unfold aclient_range, aclient_app_range. left. left. lia. }
  destruct HOUT as [[D0 C0] | [pb HPB]].
  - eapply (AI_frame AI L RNG st LB m0 mm [(lo, SP)] AH); [| exact WM | constructor; [exact FST | constructor]].
    eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as [Hx _].
    split; [exact Hx |]. split; [lia | exact I].
  - eapply (AI_frame AI L RNG st LB m0 mm _ AH MU WM).
    constructor; [exact FST | constructor; [| constructor]].
    cbn [fst snd]. unfold aclient_range. right. left. exists (HB pb DST dcap). cbn [ab_addr ab_size]. split; [exact HPB | lia].
Qed.

  Lemma ent_magree : forall mm, munch DW m0 mm -> wmono bsegs m0 mm ->
    magree bsegs (fun a => aclient_addr CI LB SP a /\ ~ (DST <= a < DST + dcap)) m0 mm.
Proof using All.
  intros mm MU WM.
  apply (munch_magreeA _ _ _ _ MU WM).
  intros a [HC HD]. cbn [outside]. split; [| split; [exact HD | exact I]].
  pose proof ATOP_range as AT. unfold ATOP_MIN, ATOP_MAX in AT.
  unfold aclient_addr in HC.
  destruct HC as [HC | [(iv & HIN & HR) | [(b & HIN & HR) | (a' & HA' & ->)]]].
  - lia.
  - pose proof (AI_aci_img AI iv HIN). unfold AIMG_HI in *. lia.
  - pose proof (AI_block_bounds AI L RNG st LB m0 b AH HIN). unfold AIMG_HI in *. lia.
  - assert (RA : 0 <= a' < 2^47).
    { destruct HA' as [HA' | [(iv & HIN & HR) | (cls & A & n' & HIN & HR)]].
      - lia.
      - pose proof (AI_aci_img AI iv HIN). pose proof (AI_aci_lo AI iv HIN). unfold AIMG_HI in *. lia.
      - pose proof (AI_block_bounds AI L RNG st LB m0 _ AH HIN) as BB. cbn [ab_addr ab_size] in BB.
        unfold AIMG_HI in *. lia. }
    pose proof (shad_in_band a' RA). lia.
Qed.

  (* [comment removed for export] *)
  Lemma ent_epi : forall mm (dcs : list cell) (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6 xra : word),
    stk bsegs mm lo SPF -> rw_cells bsegs mm SPF dcs -> cells_size dcs = 40%nat -> rw_cells bsegs mm (SP + -88) FRS11 ->
    mem_inv bsegs mm -> munch DW m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                                 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 AX1_EPI) fc None mm (seg_rom bsegs)).
Proof using All.
  intros mm dcs t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6 xra STK FRD CS FRC MI MU WM.
  unfold AX1_EPI.
  destruct (rw_cells_forget _ _ _ _ FRD) as [dj FRJ]. rewrite CS in FRJ. clear FRD CS.
  pose proof ent_sp_bounds as SB. unfold HUF_DEC_STACK_A in LOS.
  pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
  do 13 zstep.
  release_frame FRJ STK (bv_unsigned sp + -88). release_frame FRC STK (bv_unsigned sp).
  apply evtF_done. unfold huf_dec_postA.
  do 16 eexists. split; [reflexivity|]. split; [exact MI|]. split; [exact STK|].
  split; [exact (ent_magree mm MU WM) | exact (ent_aheap mm MU WM)].
Qed.
End ENT.

  Lemma ax1e_rdC4 : forall m A cs k v sx, rw_cells bsegs m A cs -> cell_at cs k = Some (C4 (Z_to_bv 64 v)) -> 0 <= v < 2^31 ->
    rdval bsegs m (Z_to_bv 64 (A + Z.of_nat k)) 4 sx = Z_to_bv 64 v.
  Proof.
    intros m A cs k v sx H HC HV. unfold rdval. rewrite <- ov_rdn.
    change (Z_to_bv 64 (A + Z.of_nat k)) with (wa (A + Z.of_nat k)).
    pose proof (rw_cells_read bsegs m A cs k _ H HC) as R. cbn [csize cbytes] in R. rewrite R.
    rewrite bytes_le_to_Z_le4, Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. rewrite (Z.mod_small v) by (change (2^Z.of_N 64) with (2^64); lia).
    rewrite (Z.mod_small v) by lia.
    destruct sx; unfold extz; [| reflexivity].
    f_equal. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (Z.of_N (8 * N.of_nat 4)) with 32.
    change (2^(32 - 1)) with (2^31). rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma ax1e_rdDT : forall m D tl0 mtl0 sx, bytes_at bsegs m D [Z_to_bv 8 mtl0; Z_to_bv 8 0; Z_to_bv 8 tl0; Z_to_bv 8 mtl0] ->
    0 <= tl0 < 256 -> 0 <= mtl0 < 128 ->
    rdval bsegs m (Z_to_bv 64 (D + 2)) 2 sx = Z_to_bv 64 (tl0 + 256 * mtl0).
  Proof.
    intros m D tl0 mtl0 sx H HT HM. unfold rdval.
    change (Z_to_bv 64 (D + 2)) with (wa (D + Z.of_nat 2)).
    rewrite (bytes_at_rdn bsegs m D _ 2 2 H ltac:(cbn; lia)). cbn [firstn skipn].
    rewrite <- le2_two_bytes by lia. rewrite bytes_le_to_Z_le2, Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. change (2^Z.of_N 64) with (2^64).
    rewrite (Z.mod_small (tl0 + 256 * mtl0)) by lia. rewrite (Z.mod_small (tl0 + 256 * mtl0)) by lia.
    destruct sx; unfold extz; [| reflexivity].
    f_equal. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (Z.of_N (8 * N.of_nat 2)) with 16.
    change (2^(16 - 1)) with (2^15). rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma ax1e_br65 : forall v, 0 <= v <= 64 ->
    negb (bv_ltu (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 v)) (low32 (Z_to_bv 64 0)))) (Z_to_bv 64 65)) = false.
  Proof.
    intros v Hv. assert (exists k : nat, v = Z.of_nat k /\ (k <= 64)%nat) as (k & -> & Hk) by (exists (Z.to_nat v); lia).
    do 65 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  Qed.

  Lemma ax1p_wr_u8arr : forall m A n, wr_at bsegs m A n -> 0 <= n -> AIMG_HI <= A ->
    exists buf : list Z, u8arr bsegs m A (map (Z_to_bv 8) buf) /\ zlen buf = n.
  Proof.
    intros m A n (A0 & AN & WV) N0 AIH. unfold AIMG_HI in AIH.
    set (f := fun i : nat => match m (wa (A + Z.of_nat i)) with Some b => bv_unsigned b | None => 0 end).
    exists (map f (seq 0 (Z.to_nat n))).
    assert (LN : length (map (Z_to_bv 8) (map f (seq 0 (Z.to_nat n)))) = Z.to_nat n)
      by (rewrite !length_map, length_seq; reflexivity).
    split; [| rewrite length_map, length_seq; lia].
    split; [| rewrite LN, Z2Nat.id by lia; exact (conj A0 (conj AN WV))].
    split; [exact A0|]. split; [rewrite LN; lia|].
    intros i Hi. rewrite LN in Hi.
    rewrite !nth_error_map. rewrite (nth_error_nth' (seq 0 (Z.to_nat n)) (n := i) 0%nat) by (rewrite length_seq; lia).
    rewrite seq_nth by lia. cbn [option_map Nat.add]. unfold f, mrd.
    specialize (WV (Z.of_nat i) ltac:(lia)).
    rewrite ref_wview_overlay in WV;
      [| unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; right; lia].
    destruct (m (wa (A + Z.of_nat i))) as [b|]; [| congruence]. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
  Qed.

Section AX1E.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte) (pdt : aptr) (SBL SBH : Z).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -128).
  Notation n := (zlen src).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HOUT : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis NSM : 1 <= n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SBB : SBL <= SS /\ SS + n <= SBH.
  Hypothesis SBA : ablk SBL SBH /\ SBL mod 8 = 0.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DJ1 : KXGoM.apart DST dcap DT DTL.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  Hypothesis DJ3 : KXGoM.apart SS n DT DTL.
  Hypothesis UDT : unpoisoned m0 DT (DT + DTL).
  Hypothesis UDB : unpoisoned m0 DST (DST + dcap).
  Hypothesis USB : unpoisoned m0 SBL SBH.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WDT : rng RNG DT DTL.
  Hypothesis WSB : rng RNG SBL (SBH - SBL).
  Hypothesis WDTS : rng RNG (shad DT) (shlen (DTL + 7)).
  Hypothesis WSBS : rng RNG (shad SBL) (shlen (SBH - SBL + 7)).
  Hypothesis WDB : 0 < dcap -> rng RNG DST dcap.
  Hypothesis WDBS : 0 < dcap -> rng RNG (shad DST) (shlen (dcap + 7)).

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS11 := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation A1 l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      pdt SBL SBH AH HDT HOUT LOA LOS SPT SP16 TOK ECB LCB MTL TLM DC NSM S16 SBB SBA BYS DJ1 DJ2 DJ3 UDT UDB USB
                      WSK WIM WDT WSB WDTS WSBS WDB WDBS) (only parsing).
  Notation AX1M' mm := (AX1M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m0 DST dcap SS DT lo src cbs mm).

  Notation FRM' mm fb := (AX1F sp SS mm fb).
  Notation ALINV' P bc := (ALINV SS src P bc).
  Notation LST pc mm x1 x10 x11 x12 x13 x14 j x22 x23 x24 x25 x28 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 65) (Z_to_bv 64 AX1_KT15) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 dcap)
             (Z_to_bv 64 DST) x10 x11 x12 x13 x14 (Z_to_bv 64 j) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (-1 * DT + -5))
             (Z_to_bv 64 AX1_KSB) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl))
             x22 x23 x24 x25 s10 s11 x28 (Z_to_bv 64 3) (Z_to_bv 64 2) (Z_to_bv 64 AX1_KL31))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Ltac ax1_lfacts :=
    pose proof (A1 ax1_sp_bounds) as SB; pose proof (A1 ax1_blocks) as BK; pose proof (A1 ax1_outb) as OB;
    lazymatch goal with HM : AX1M' ?mm |- _ =>
      destruct HM as ((buf & OUT & LBF) & SRCB & CBS & STK & FRC & MI & MU & WM);
      destruct (A1 ax1_unp mm MU) as (UDT' & UDB' & USB') end;
    destruct BK as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6);
    pose proof ATOP_range as AT; unfold ATOP_MIN, ATOP_MAX in AT; unfold ABase.AIMG_HI, KLS in *;
    unfold AX1_TL, AX1_TS, AX1_T0, AX1_TX, AX1_HD, AX1_RL, AX1_R2, AX1_R3, AX1_END, AX1_KSB, AX1_KT15, AX1_KL31, DTABLE_BYTES, HufHarness.DT_BYTES in *;
    assert (TL1 : 1 <= tl <= 12) by (destruct TOK as (TT & _); unfold HUF_TABLELOG_MAX in TT; lia);
    assert (P2 : 2 <= 2^tl <= 4096) by (split; [replace 2 with (2^1) by reflexivity | replace 4096 with (2^12) by reflexivity]; apply Z.pow_le_mono_r; lia);
    assert (PT : 2^tl <= 2 * 2^mtl) by (replace (2 * 2^mtl) with (2^(mtl+1)) by (rewrite Z.pow_add_r by lia; lia); apply Z.pow_le_mono_r; lia);
    assert (LSRC : zlen (map (Z_to_bv 8) src) = n) by (rewrite length_map; reflexivity);
    lazymatch goal with HL : zlen ?b = dcap, HO : u8arr _ _ DST (map _ ?b) |- _ => assert (LBF' : zlen (map (Z_to_bv 8) b) = dcap) by (rewrite length_map; exact HL) end;
    try (lazymatch goal with HL : zlen ?b = 24 |- _ => assert (LFB' : zlen (map (Z_to_bv 8) b) = 24) by (rewrite length_map; exact HL) end).
  Ltac ax1_ldfacts := pose proof (WDB ltac:(lia)) as WDB1; pose proof (WDBS ltac:(lia)) as WDBS1;
    lazymatch goal with BK6 : 0 < dcap -> _ |- _ => destruct (BK6 ltac:(lia)) as (B1 & B2 & B3 & B4) end.

  Ltac ax1_lstfix :=
    try replace (- tl + 64) with (64 - tl) by lia;
    try replace (dcap + DST) with (DST + dcap) by lia;
    try replace (dcap + DST + -3) with (DST + dcap - 3) by lia;
    try replace (DST + dcap + -3) with (DST + dcap - 3) by lia;
    try replace (- DT + -5) with (-1 * DT + -5) by lia;
    try lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?r31) _ _ _ _ _ _) =>
      replace r31 with (Z_to_bv 64 AX1_KL31)
        by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold AX1_KL31, bv_wrap, bv_modulus; vm_compute; reflexivity) end.

  Ltac ax1_fl := first [ left; reflexivity | right; split; [reflexivity | lia]
    | lazymatch goal with |- context [Z.b2z (?a <? ?b)] =>
        first [ rewrite (proj2 (Z.ltb_ge a b)) by (rewrite ?Z.mod_small by lia; lia)
              | rewrite (proj2 (Z.ltb_lt a b)) by (rewrite ?Z.mod_small by lia; lia) ] end;
      first [ left; vm_compute; reflexivity | right; split; [vm_compute; reflexivity | lia] ] ].

  Ltac ax1_rl_post :=
    kx_post_regs_keep;
    lazymatch goal with H : u8arr bsegs ?mm SPF (map _ ?b), HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ mm _ SPF b H HL) as (fb' & FB' & LFB2); clear H end;
    lazymatch goal with H : munch [(lo, SP); (DST, DST + dcap)] m0 ?mm |- _ =>
      let MUW := fresh "MUW" in let WMr := fresh "WMr" in
      pose proof (munch_refl [(SPF, SPF + 24)] mm) as MUW; pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SPF, 24)]; kx_munch_wins H [(SPF, 24)] end;
    kx_post_mem_free;
    lazymatch goal with |- context [mem_denot ?E ?mm ?l] => let EM1 := fresh "EM1" in remember (mem_denot E mm l) as m1 eqn:EM1 end;
    unfold KXGoM.apart in DJ1, DJ2, DJ3;
    lazymatch goal with MUW' : munch [(SPF, SPF + 24)] ?mm ?m1', WMr' : wmono bsegs ?mm ?m1' |- _ =>
      transport_after_call bsegs mm m1' MUW' WMr' end.
  Ltac ax1e_rdbits BD v RD :=
    kx_read_eq 33%nat RD;
    lazymatch type of RD with _ = rdval _ _ ?ad _ _ =>
      replace ad with (Z_to_bv 64 (SPF + Z.of_nat 8)) in RD
        by (unfold adenot; cbn [a_base a_off]; ax1_ez2; rewrite v_addi_lit; f_equal; lia) end;
    rewrite (ax1e_rdC4 _ SPF _ 8 v false BD eq_refl ltac:(lia)) in RD.

  Ltac ax1e_bdside BD v :=
    try (lazymatch goal with |- exists bs, rdn _ _ ?ad _ = Some bs =>
      replace ad with (Z_to_bv 64 (SPF + Z.of_nat 8))
        by (unfold adenot; cbn [a_base a_off]; ax1_ez2; rewrite v_addi_lit; f_equal; lia);
      eexists; rewrite <- ov_rdn; exact (rw_cells_read bsegs _ SPF _ 8 _ BD eq_refl) end);
    try (lazymatch goal with |- branch_taken _ _ _ = _ =>
      let RD := fresh "RD" in ax1e_rdbits BD v RD; unfold branch_taken; cbn [edenot]; rewrite RD; apply ax1e_br65; lia end).

  Ltac ax1e_wrapfix :=
    repeat lazymatch goal with |- context [Z_to_bv 64 (- tl + ?k)] =>
      replace (Z_to_bv 64 (- tl + k)) with (Z_to_bv 64 (64 - tl))
        by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
            change (2 ^ Z.of_N 64) with 18446744073709551616;
            rewrite <- (Z.mod_add (- tl + k) 1 18446744073709551616) by lia; f_equal; lia) end.

  Lemma ax1e_alinv : forall d, init_dstream src = Ok d -> ALINV' (SS + bd_ptr d) (bd_bits d).
  Proof using All.
    intros d ID. destruct (init_facts src d BYS ID) as ((OK1 & OK2 & OK3 & OK4 & OK5 & OK6) & BB & BZ).
    unfold ALINV. split; [lia|]. destruct (Z.eq_dec (bd_ptr d) 0) as [P0|P0]; [left; lia|right].
    destruct (Z_lt_le_dec n 8) as [N8|N8]; [specialize (OK5 N8); lia|].
    rewrite Z.max_r in OK4 by lia. lia.
  Qed.

  Lemma ax1e_ok4 : forall mm d jp (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    AX1M' mm -> rw_cells bsegs mm SPF (bitdz_cellsA SS d jp) -> init_dstream src = Ok d -> 4 <= dcap ->
    evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (AX1_CALL + 4)) (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST)
                               (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 AX1_KSB) (Z_to_bv 64 (DT + 4))
                               (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            FR (Z_to_bv 64 AX1_POST) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros mm d jp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HM BD ID HD4.
    pose proof HM as HM0. pose proof (ax1e_alinv d ID) as AL.
    ax1_lfacts. ax1_ldfacts.
    destruct (init_facts src d BYS ID) as ((OK1 & OK2 & OK3 & OK4 & OK5 & OK6) & BB & BZ).
    unfold bitdz_cellsA in BD. rewrite BZ in BD.
    unfold AX1_POST, AX1_CALL in *.
    kx_runFm [AX1_RL] 60%nat
        [KZRange SP 8192 (2^47); KZRange SPF 4096 (2^47); KZAlign SP 16; KZRange DST 4096 (2^47); KZRange dcap 4 (2^32 - 1);
         KZRange (DST + dcap) 4100 (2^47); KZRange SS 16 (2^47); KZRange n 1 (2^26); KZRange DT 4096 (2^47 - 8192);
         KZRange tl 1 12; KZRange mtl 1 12; KZRange (bd_bits d) 0 64; KZRange (bd_ptr d) 0 (2^26);
         KZWord SPF 8 (bd_cont d); KZWord (SPF + 16) 8 (SS + bd_ptr d); KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8)]
        (@nil (Z * Z)) [(SPF, 40)] (@nil (Z * Z)).
    all: ax1_side.
    all: ax1e_bdside BD (bd_bits d).
    ax1e_rdbits BD (bd_bits d) RD.
    kx_post_regs_keep. rewrite RD. ax1_ez2. cbn [mem_denot]. kx_clear. ax1_lstfix. ax1e_wrapfix.
    destruct (ax1_fr_split _ _ _ _ _ _ _ _ BD) as ((fb & FB & LFB) & FS).
    eapply (A1 ax1_loop) with (fb := fb) (P := SS + bd_ptr d) (bc := bd_bits d) (j := 0);
      [eassumption | unfold AX1F; split; [exact FB | split; [exact LFB | exact FS]] | exact AL | lia | lia].
  Qed.

  Notation T13 mm x1 x5 x6 x7 p x12 bc x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 (SS + p))
             x12 (Z_to_bv 64 bc) x14 x15 x16 x17 (Z_to_bv 64 AX1_KSB) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap))
             (Z_to_bv 64 (tl + 256 * mtl)) x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
        FR (Z_to_bv 64 (AHUF_DX1_1X + 1392)) fc None mm (seg_rom bsegs)).

  Ltac ax1e_t0post :=
    ax1_rl_post; ax1_ez2; ax1_lstfix;
    replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia);
    eapply (A1 ax1_tail0); [lia | | ];
    [ unfold AX1M; split; [eexists; split; eassumption |]; repeat (split; [assumption|]); assumption
    | unfold AX1F; split; [eassumption | split; [lia | assumption]] ].

  Ltac ax1e_q8 q r :=
    try replace ((8 * q + r) / 8) with q by (Z.div_mod_to_equations; lia);
    try replace ((8 * q + r) mod 2 ^ 64 / 8) with q by (Z.div_mod_to_equations; lia);
    try replace (Z.shiftr (8 * q + r) 3) with q by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).

  Lemma ax1e_ne0 : forall z, 0 < z <= 7 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
  Proof.
    intros z Hz. assert (exists k : nat, z = Z.of_nat k /\ (1 <= k <= 7)%nat) as (k & -> & Hk) by (exists (Z.to_nat z); lia).
    do 8 (destruct k as [|k]; [first [lia | vm_compute; reflexivity] |]). lia.
  Qed.

  Lemma ax1e_lts7 : forall (w : word) z, 0 <= bv_unsigned w < z -> z <= 7 -> bv_lts w (Z_to_bv 64 z) = true.
  Proof.
    intros w z H1 H2. rewrite <- (Z_to_bv_bv_unsigned w).
    assert (exists i j : nat, bv_unsigned w = Z.of_nat i /\ z = Z.of_nat j /\ (i < j <= 7)%nat) as (i & j & -> & -> & Hij)
      by (exists (Z.to_nat (bv_unsigned w)), (Z.to_nat z); lia).
    do 8 (destruct j as [|j]; [do 8 (destruct i as [|i]; [first [lia | vm_compute; reflexivity] |]); lia |]). lia.
  Qed.

  Lemma ax1e_and7 : forall x, 0 <= x < 2^64 -> bv_unsigned (alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 7)) = x mod 8.
  Proof.
    intros x Hx. change (bv_unsigned (alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 7))) with (zalu ALU_AND x 7).
    rewrite <- zfast_eq by (unfold two64; lia). cbn [zfast]. exact (zb_land_mask x 3 ltac:(lia)).
  Qed.

  Ltac ax1e_shrd j x SB RD :=
    kx_read_eq j RD;
    lazymatch type of RD with _ = rdval _ _ (adenot ?E {| a_base := EAlu ALU_SRL ?X (ELit 3); a_off := ?o |}) _ _ =>
      change o with ASHOFF in RD; rewrite (adenot_shad E X) in RD;
      let EX := fresh "EX" in
      assert (EX : edenot E X = Z_to_bv 64 x) by (ax1_ez2; f_equal; lia);
      rewrite EX, Z_to_bv_unsigned in RD; unfold bv_wrap, bv_modulus in RD;
      rewrite (Z.mod_small x) in RD by (change (2 ^ Z.of_N 64) with (2^64); lia);
      rewrite (rdval_shadow _ _ _ _ SB) in RD; clear EX end.

  Ltac ax1e_shck x SB :=
    lazymatch goal with
    | |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot _ (ELit 0)) = ?d =>
        let RD := fresh "RD" in ax1e_shrd j x SB RD;
        unfold branch_taken; change (edenot E (EVar j)) with (ev E j); change (edenot E (ELit 0)) with (Z_to_bv 64 0);
        rewrite RD;
        first [ lazymatch goal with S0 : sval _ = 0 |- _ => rewrite S0; vm_compute; reflexivity end
              | apply ax1e_ne0; lia ]
    | |- branch_taken BC_LT (edenot ?E (EAlu ALU_AND ?X (ELit 7))) (edenot ?E (EVar ?j)) = true =>
        let RD := fresh "RD" in ax1e_shrd j x SB RD;
        let EX := fresh "EX" in assert (EX : edenot E X = Z_to_bv 64 (x)) by (ax1_ez2; f_equal; lia);
        unfold branch_taken; change (edenot E (EVar j)) with (ev E j); rewrite RD;
        change (edenot E (EAlu ALU_AND X (ELit 7))) with (alu64 ALU_AND (edenot E X) (edenot E (ELit 7)));
        rewrite EX; change (edenot E (ELit 7)) with (Z_to_bv 64 7);
        apply ax1e_lts7; [rewrite ax1e_and7 by lia; Z.div_mod_to_equations; lia | lia]
    end.

  Lemma ax1e_t0 : forall mm fb p bc (x1 x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    AX1M' mm -> FRM' mm fb -> dcap < 4 -> 0 <= bc <= 64 -> p = 0 ->
    evtF bsegs RNG POST (T13 mm x1 x5 x6 x7 p x12 bc x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof using All.
    intros mm fb p bc x1 x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 HM (FB & LFB & FS) HD HBC HP.
    subst p. pose proof HM as HM0.
    ax1_lfacts.
    kx_runFm [AX1_T0] 20%nat
        [KZRange bc 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange SPF 4096 (2^47); KZRange DST 0 (2^47); KZRange dcap 0 3;
         KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS n; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, n); (SPF, 24)] [(SS, n); (SPF, 40)] [(SS, n)].
    all: ax1_side.
    ax1e_t0post.
  Qed.

  Lemma ax1e_tS1 : forall mm fb p bc q r (x1 x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    AX1M' mm -> FRM' mm fb -> dcap < 4 -> bc = 8 * q + r -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    1 <= p <= 7 -> SS + p + 8 <= SS + n -> q <= p ->
    evtF bsegs RNG POST (T13 mm x1 x5 x6 x7 p x12 bc x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof using All.
    intros mm fb p bc q r x1 x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 HM (FB & LFB & FS) HD EB HQ HR HBC P1 P2' HC.
    subst bc. pose proof HM as HM0.
    ax1_lfacts.
    destruct (unp_gran _ _ _ (SS + p - q + 7) 1 USB' ltac:(lia) ltac:(lia) ltac:(lia)) as (sb & SHB & SBV).
    kx_runFm [AHUF_DX1_1X + 1412] 20%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange p 1 7; KZRange SPF 4096 (2^47); KZRange DST 0 (2^47); KZRange dcap 0 3;
         KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS n; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, n); (SPF, 24)] [(SS, n); (SPF, 40)] [(SS, n)].
    all: ax1_side.
    kx_post_regs. cbn [mem_denot]. ax1_ez2. ax1e_q8 q r.
    kx_clear.
    destruct SBV as [S0 | (S1 & S2)];
    [ kx_runFmd [AX1_T0] 80%nat (false :: true :: false :: true :: repeat false 100)
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange p 1 7; KZRange SPF 4096 (2^47); KZRange DST 0 (2^47); KZRange dcap 0 3;
         KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 (SS + p - q) 8; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [((SS + p - q), 8); (SPF, 24)] [((SS + p - q), 8); (SPF, 40)] [((SS + p - q), 8)]
    | kx_runFmd [AX1_T0] 80%nat (false :: true :: false :: false :: true :: repeat false 100)
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange p 1 7; KZRange SPF 4096 (2^47); KZRange DST 0 (2^47); KZRange dcap 0 3;
         KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 (SS + p - q) 8; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [((SS + p - q), 8); (SPF, 24)] [((SS + p - q), 8); (SPF, 40)] [((SS + p - q), 8)] ].
    all: ax1_side.
    all: try ax1e_shck (SS + p - q + 7) SHB.
    all: ax1e_t0post.
  Qed.


  Lemma ax1e_tS2 : forall mm fb p bc q r (x1 x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    AX1M' mm -> FRM' mm fb -> dcap < 4 -> bc = 8 * q + r -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    1 <= p <= 7 -> SS + p + 8 <= SS + n -> p < q ->
    evtF bsegs RNG POST (T13 mm x1 x5 x6 x7 p x12 bc x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof using All.
    intros mm fb p bc q r x1 x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 HM (FB & LFB & FS) HD EB HQ HR HBC P1 P2' HC.
    subst bc. pose proof HM as HM0.
    ax1_lfacts.
    destruct (unp_gran _ _ _ (SS + 7) 1 USB' ltac:(lia) ltac:(lia) ltac:(lia)) as (sb & SHB & SBV).
    kx_runFm [AHUF_DX1_1X + 1412] 20%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange p 1 7; KZRange SPF 4096 (2^47); KZRange DST 0 (2^47); KZRange dcap 0 3;
         KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS n; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, n); (SPF, 24)] [(SS, n); (SPF, 40)] [(SS, n)].
    all: ax1_side.
    kx_post_regs. cbn [mem_denot]. ax1_ez2. ax1e_q8 q r.
    kx_clear.
    destruct SBV as [S0 | (S1 & S2)];
    [ kx_runFmd [AX1_T0] 80%nat (false :: false :: false :: true :: repeat false 100)
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange p 1 7; KZRange SPF 4096 (2^47); KZRange DST 0 (2^47); KZRange dcap 0 3;
         KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS 8; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, 8); (SPF, 24)] [(SS, 8); (SPF, 40)] [(SS, 8)]
    | kx_runFmd [AX1_T0] 80%nat (false :: false :: false :: false :: true :: repeat false 100)
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange p 1 7; KZRange SPF 4096 (2^47); KZRange DST 0 (2^47); KZRange dcap 0 3;
         KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS 8; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, 8); (SPF, 24)] [(SS, 8); (SPF, 40)] [(SS, 8)] ].
    all: ax1_side.
    all: try ax1e_shck (SS + 7) SHB.
    all: ax1e_t0post.
  Qed.

  Lemma ax1e_tFa : forall mm fb p bc q r (x1 x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    AX1M' mm -> FRM' mm fb -> dcap < 4 -> bc = 8 * q + r -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    8 <= p -> SS + p + 8 <= SS + n -> p <> q ->
    evtF bsegs RNG POST (T13 mm x1 x5 x6 x7 p x12 bc x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof using All.
    intros mm fb p bc q r x1 x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 HM (FB & LFB & FS) HD EB HQ HR HBC P1 P2' HC.
    subst bc. pose proof HM as HM0.
    ax1_lfacts.
    kx_runFm [AHUF_DX1_1X + 1572] 20%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange p 8 (2^26); KZRange SPF 4096 (2^47); KZRange DST 0 (2^47); KZRange dcap 0 3;
         KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS n; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, n); (SPF, 24)] [(SS, n); (SPF, 40)] [(SS, n)].
    all: ax1_side.
    kx_post_regs. cbn [mem_denot]. ax1_ez2. ax1e_q8 q r.
    kx_clear.
    kx_runFm [AX1_T0] 60%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange p 8 (2^26); KZRange SPF 4096 (2^47); KZRange DST 0 (2^47); KZRange dcap 0 3;
         KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 (SS + p - q) 8; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [((SS + p - q), 8); (SPF, 24)] [((SS + p - q), 8); (SPF, 40)] [((SS + p - q), 8)].
    all: ax1_side.
    ax1e_t0post.
  Qed.

  Lemma ax1e_tFb : forall mm fb p bc (x1 x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    AX1M' mm -> FRM' mm fb -> dcap < 4 -> bc = 64 -> p = 8 -> SS + p + 8 <= SS + n ->
    evtF bsegs RNG POST (T13 mm x1 x5 x6 x7 p x12 bc x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof using All.
    intros mm fb p bc x1 x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 HM (FB & LFB & FS) HD EB EP P2'.
    subst bc p. pose proof HM as HM0.
    ax1_lfacts.
    kx_runFm [AX1_T0] 80%nat
        [KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange SPF 4096 (2^47); KZRange DST 0 (2^47); KZRange dcap 0 3;
         KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS 8; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, 8); (SPF, 24)] [(SS, 8); (SPF, 40)] [(SS, 8)].
    all: ax1_side.
    ax1e_t0post.
  Qed.

  Lemma ax1e_lt4 : forall mm d jp (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    AX1M' mm -> rw_cells bsegs mm SPF (bitdz_cellsA SS d jp) -> init_dstream src = Ok d -> dcap < 4 ->
    evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (AX1_CALL + 4)) (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST)
                               (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 AX1_KSB) (Z_to_bv 64 (DT + 4))
                               (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            FR (Z_to_bv 64 AX1_POST) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros mm d jp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HM BD ID HD4.
    pose proof HM as HM0. pose proof (ax1e_alinv d ID) as AL.
    ax1_lfacts.
    destruct (init_facts src d BYS ID) as ((OK1 & OK2 & OK3 & OK4 & OK5 & OK6) & BB & BZ).
    unfold bitdz_cellsA in BD. rewrite BZ in BD.
    unfold AX1_POST, AX1_CALL in *.
    kx_runFm [AHUF_DX1_1X + 1392] 20%nat
        [KZRange SP 8192 (2^47); KZRange SPF 4096 (2^47); KZAlign SP 16; KZRange DST 0 (2^47); KZRange dcap 0 3;
         KZRange (DST + dcap) 0 (2^47); KZRange SS 16 (2^47); KZRange n 1 (2^26); KZRange DT 4096 (2^47 - 8192);
         KZRange tl 1 12; KZRange mtl 1 12; KZRange (bd_bits d) 0 64; KZRange (bd_ptr d) 0 (2^26);
         KZWord SPF 8 (bd_cont d); KZWord (SPF + 16) 8 (SS + bd_ptr d); KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8)]
        (@nil (Z * Z)) [(SPF, 40)] (@nil (Z * Z)).
    all: ax1_side.
    all: ax1e_bdside BD (bd_bits d).
    all: try (lazymatch goal with |- branch_taken BC_GEU (edenot ?E (EVar ?j)) _ = _ =>
           let RD := fresh "RD" in ax1e_rdbits BD (bd_bits d) RD;
           unfold branch_taken; change (edenot E (EVar j)) with (ev E j); rewrite RD; ax1_br end).
    ax1e_rdbits BD (bd_bits d) RD.
    kx_post_regs_keep. rewrite RD. ax1_ez2. cbn [mem_denot]. kx_clear. ax1_lstfix.
    destruct (ax1_fr_split _ _ _ _ _ _ _ _ BD) as ((fb & FB & LFB) & FS).
    assert (HF : FRM' mm fb) by (unfold AX1F; split; [exact FB | split; [exact LFB | exact FS]]).
    destruct AL as (HBC & HP).
    assert (QR : bd_bits d = 8 * (bd_bits d / 8) + bd_bits d mod 8 /\ 0 <= bd_bits d / 8 <= 8 /\ 0 <= bd_bits d mod 8 <= 7)
      by (Z.div_mod_to_equations; lia).
    destruct QR as (QE & HQ & HR).
    destruct HP as [HP0 | (PP1 & PP2)].
    - eapply ax1e_t0; [eassumption | exact HF | exact HD4 | lia | lia].
    - destruct (Z_lt_le_dec (bd_ptr d) 8) as [D8 | D8].
      + destruct (Z_le_gt_dec (bd_bits d / 8) (bd_ptr d)) as [QD | QD].
        * eapply ax1e_tS1; [eassumption | exact HF | exact HD4 | exact QE | lia | lia | lia | lia | lia | lia].
        * eapply ax1e_tS2; [eassumption | exact HF | exact HD4 | exact QE | lia | lia | lia | lia | lia | lia].
      + destruct (Z.eq_dec (bd_ptr d) (bd_bits d / 8)) as [QD | QD].
        * eapply ax1e_tFb; [eassumption | exact HF | exact HD4 | lia | lia | lia].
        * eapply ax1e_tFa; [eassumption | exact HF | exact HD4 | exact QE | lia | lia | lia | lia | lia | lia].
  Qed.

  Lemma ax1e_cont : forall mm d jp (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    AX1M' mm -> rw_cells bsegs mm SPF (bitdz_cellsA SS d jp) -> init_dstream src = Ok d ->
    evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (AX1_CALL + 4)) (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST)
                               (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 AX1_KSB) (Z_to_bv 64 (DT + 4))
                               (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            FR (Z_to_bv 64 AX1_POST) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros mm d jp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HM BD ID.
    destruct (Z_lt_le_dec dcap 4) as [D4 | D4]; [eapply ax1e_lt4 | eapply ax1e_ok4]; eassumption.
  Qed.
End AX1E.

Section AX1P.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte) (pdt : aptr) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -128).
  Notation n := (zlen src).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HOUT : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis NSM : n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DJ1 : KXGoM.apart DST dcap DT DTL.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  Hypothesis DJ3 : KXGoM.apart SS n DT DTL.
  Hypothesis SRCI : src_inA LB SS src.
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS11 := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation E1 l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap lo AH HOUT LOA LOS SPT WSK)
    (only parsing).
  Notation AX1M' mm := (AX1M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m0 DST dcap SS DT lo src cbs mm).
  Ltac ax1p_facts :=
    pose proof (AI_rtcells AI L RNG st LB m0 AH) as (RG0 & RGOT & RGRIC & RMEM & RSHB & _);
    pose proof (E1 ent_sp_bounds) as SB;
    pose proof (hb_unpoisoned AI L RNG st LB m0 pdt DT DTL AH HDT) as (UDT & D16 & _ & DBLK & DTOP & WDT & WDTS & _);
    pose proof (ablk_lin _ _ DBLK) as (D1 & _ & _ & _);
    pose proof ATOP_range as AT; unfold ATOP_MIN, ATOP_MAX in AT; unfold ABase.AIMG_HI in *;
    unfold AX1_CALL, AX1_POST, DTABLE_BYTES, HufHarness.DT_BYTES in *;
    assert (TL1 : 1 <= tl <= 12) by (destruct TOK as (TT & _); unfold HUF_TABLELOG_MAX in TT; lia);
    assert (SHD : Z.shiftr DT 3 + 0x7fff8000 + 1 <= SP - 128) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia);
    assert (WDTS2 : rng RNG (Z.shiftr DT 3 + 0x7fff8000) 1)
      by (eapply rng_sub; [exact WDTS | unfold shad, ASHOFF; lia | unfold shad, ASHOFF, shlen; rewrite !Z.shiftr_div_pow2 by lia;
                           change (2^3) with 8; Z.div_mod_to_equations; lia]).

  Ltac ax1p_frame STK :=
    carve_frame 128%nat STK;
    lazymatch goal with FR0 : rw_cells bsegs _ (bv_unsigned _ + -128) [CB 128 ?j] |- _ =>
      pose proof (StrFun.rw_cells_CB_length bsegs _ _ _ _ FR0) as LJ;
      let FRU := fresh "FRU" in pose proof FR0 as FRU; apply u8arr_of_rw_cells in FRU;
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [40;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR0; [| reflexivity];
      cbn [mk_CB_cells app] in FR0; kx_cells_split FR0 end;
    repeat match goal with H : rw_cells bsegs ?m ?A [CB 8 ?b] |- _ =>
      let w := fresh "w" in let H' := fresh "KW" in destruct (c8_of_CB _ _ _ H) as (w & H' & _); clear H end.

  Lemma ax1p_appW : appW DW.
  Proof using All.
    pose proof (@ATOP_lo rc) as HA. pose proof (E1 ent_sp_bounds) as SB.
    destruct HOUT as [[-> ->]|(pb & HB)].
    - unfold appW, KLOW, KHIGH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; lia.
    - pose proof (AI_block AI L RNG st LB m0 pb DST dcap AH HB) as (D1 & (C2 & C3 & C4 & C5) & _).
      unfold ablk, AIMG_HI, KLS in C2.
      unfold appW, KLOW, KHIGH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; lia.
  Qed.

  Lemma ax1p_rcl : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> rclean mm rstk.
  Proof using All. intros mm MU WM. eapply rclean_transport; [exact RCL|exact MU|exact WM|exact ax1p_appW]. Qed.

  Lemma ax1p_art : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> artcells mm.
  Proof using All. intros mm MU WM. exact (AI_rtcells AI _ _ _ _ _ (E1 ent_aheap mm MU WM)). Qed.

  Lemma ax1p_shar : forall a l b h, b mod 16 = 0 -> b <= a -> 0 <= l -> a + l <= h ->
    shad a + nshad (l + a mod 8) <= shad b + shlen (h - b + 7).
  Proof.
    intros a l b h B16 BA L0 AHh. rewrite !shad_div, nshad_div. unfold shlen. rewrite Z.shiftr_div_pow2 by lia.
    change (2^3) with 8. Z.div_mod_to_equations. lia.
  Qed.

  Lemma ax1p_src : 0 < n -> ablk SS (SS + n) /\ SS + 8 <= 2^47 /\ rng RNG SS n /\
      rng RNG (shad SS) (nshad (n + SS mod 8)) /\ (forall mm, munch DW m0 mm -> unpoisoned mm SS (SS + n)).
  Proof using All.
    intros NP. destruct (SRCI NP) as (p & A & k & HS & L1 & L2).
    destruct (hb_unpoisoned AI L RNG st LB m0 p A k AH HS) as (U & A16 & N1 & AB & AT & R1 & R2 & _).
    pose proof (ablk_lin _ _ AB) as AL.
    split; [eapply ablk_sub; [exact AB|lia|lia]|]. split; [lia|]. split; [eapply rng_sub; [exact R1|lia|lia]|].
    split.
    - eapply rng_sub; [exact R2| |].
      + unfold shad. rewrite !Z.shiftr_div_pow2 by lia. apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
      + replace (k + 7) with (A + k - A + 7) by lia. apply ax1p_shar; lia.
    - intros mm MU. apply (unpoisoned_sub mm A (A + k)); [|lia|lia].
      eapply unpoisoned_appW; [exact U|exact MU|exact ax1p_appW|lia|]. lia.
  Qed.

  Lemma ax1p_sh5 : forall A, A mod 8 = 0 -> shad (A + 40 - 1) + 1 - shad A = 5.
  Proof. intros A HA. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.

  Lemma ax1p_m64 : forall x, x mod 64 = 0 -> x mod 8 = 0.
  Proof. intros x HX. Z.div_mod_to_equations. lia. Qed.

  Lemma ax1p_call : forall (Q : machine_state -> Prop) mm (j : list byte) S
      (xra t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    munch DW m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm lo SPF -> rw_cells bsegs mm SPF [CB 40 j] ->
    bytes_at bsegs mm S (map (Z_to_bv 8) src) -> 0 <= S -> S + n <= 2^64 -> (0 < n -> S = SS) ->
    x10 = Z_to_bv 64 SPF -> x11 = Z_to_bv 64 S -> x12 = Z_to_bv 64 n ->
    (forall m' (ret : Z) (u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word),
       munch [(SPF - ABIT_INIT_STACK, SPF); (SPF, SPF + 40)] mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' ->
       stk bsegs m' lo SPF ->
       match init_dstream src with
       | Ok d => ret = n /\ bd_zero d = false /\ exists jp, rw_cells bsegs m' SPF (bitdz_cellsA S d jp)
       | Err e => ret = - e /\ exists j', rw_cells bsegs m' SPF [CB 40 j']
       | Ub | NoFuel => False
       end ->
       evtF bsegs RNG Q (MS (mkR xra (Z_to_bv 64 SPF) gp tp u5 u6 u7 x8 x9 (Z_to_bv 64 ret) u11 u12 u13 u14 u15 u16
                                 u17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u28 u29 u30 u31)
                            FR (ret_pc xra) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR xra (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16
                              x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                         FR (Z_to_bv 64 ABIT_INIT_D) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros Q mm j S xra t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
      t3 t4 t5 t6 MU WM MI STK RWA BYT SR1 SR2 SE E10 E11 E12 K.
    pose proof (E1 ent_sp_bounds) as SB. pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    pose proof ATOP_range as AT. unfold ATOP_MIN, ATOP_MAX in AT.
    unfold HUF_DEC_STACK_A in LOS.
    pose proof (ax1p_rcl mm MU WM) as RC. pose proof (ax1p_art mm MU WM) as ART.
    pose proof bit_init_proofAD as BI. unfold bit_init_stmtA in BI.
    pose proof (rclean_shclean _ _ RC) as SHC. pose proof (shclean_hull _ _ _ _ _ SHC) as HU.
    assert (SPF8 : SPF mod 8 = 0) by (Z.div_mod_to_equations; lia).
    eapply evtF_cut.
    - eapply (BI RNG xra (Z_to_bv 64 SPF)) with (D := SPF) (S := S) (bs := src) (j := j) (lo := lo)
        (RLO := r_rlo rstk) (RHI := r_rhi rstk).
      + exact RWA.
      + exact SPF8.
      + exact BYT.
      + exact BYS.
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; lia.
      + lia.
      + intros NP. rewrite (SE NP). destruct (ax1p_src NP) as (S1 & S2 & _). exact (conj S1 S2).
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; exact STK.
      + exact LOA.
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; unfold ABIT_INIT_STACK; lia.
      + exact MI.
      + exact ART.
      + eapply shclean_sub; [exact SHC|lia|lia|lia].
      + destruct (Z_lt_le_dec 0 n) as [NP|N0].
        * rewrite (SE NP). destruct (ax1p_src NP) as (_ & _ & _ & _ & U). exact (U mm MU).
        * unfold unpoisoned. split; [lia|]. split; [lia|]. intros. lia.
      + eapply rng_sub; [exact WSK|lia|lia].
      + destruct HU as (U1 & U2 & U3 & U4 & U5 & _). rewrite <- (ax1p_sh5 SPF SPF8).
        apply (rng_shad_sub RNG (r_rlo rstk) (r_rhi rstk)); [exact RRS|lia|lia|lia|exact U5|apply ax1p_m64, U4].
      + intros NP. rewrite (SE NP). destruct (ax1p_src NP) as (_ & _ & S3 & S4 & _). exact (conj S3 S4).
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia. eapply rng_sub; [exact WSK|lia|lia].
      + exact RRS.
      + exact WIM.
      + exact E10.
      + exact E11.
      + exact E12.
    - intros ms' (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & ret & m' & EQ & MU' & WM' & MI' & STK' & BY' & RES).
      subst ms'. rewrite Z_to_bv_unsigned in MU', STK'. unfold bv_wrap, bv_modulus in MU', STK'.
      rewrite Z.mod_small in MU', STK' by lia.
      apply K; [exact MU'|exact WM'|exact MI'|exact STK'|exact RES].
  Qed.

  Notation CONT := (forall mm d jp (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    AX1M' mm -> rw_cells bsegs mm SPF (bitdz_cellsA SS d jp) -> init_dstream src = Ok d ->
    evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (AX1_CALL + 4)) (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST)
                               (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 AX1_KSB) (Z_to_bv 64 (DT + 4))
                               (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            FR (Z_to_bv 64 AX1_POST) fc None mm (seg_rom bsegs))) (only parsing).

  Lemma ax1p_d0 : 0 <= DST /\ DST + dcap <= ATOP.
  Proof using All.
    pose proof (@ATOP_lo rc) as HA.
    destruct HOUT as [[-> ->]|(pb & HB)]; [lia|].
    pose proof (hb_unpoisoned AI L RNG st LB m0 pb DST dcap AH HB) as (_ & _ & _ & BBLK & BTOP & _).
    pose proof (ablk_lin _ _ BBLK). lia.
  Qed.

  Lemma ax1p_bt : forall W m m' A bs, bytes_at bsegs m A bs -> munch W m m' ->
    bs = [] \/ disjoint_from W A (Z.of_nat (length bs)) -> bytes_at bsegs m' A bs.
  Proof.
    intros W m m' A bs H MU [-> | D].
    - unfold bytes_at in *. destruct H as (H1 & H2 & _). split; [exact H1 | split; [exact H2 | intros i Hi; cbn [length] in Hi; lia]].
    - eapply bytes_at_transport; [exact H | exact MU | exact D].
  Qed.

  Lemma ax1p_dtb : DT + 4 + zlen cbs <= ATOP /\ AIMG_HI <= DT.
  Proof using All.
    pose proof (hb_unpoisoned AI L RNG st LB m0 pdt DT DTL AH HDT) as (_ & _ & _ & DBLK & DTOP & _).
    pose proof (ablk_lin _ _ DBLK) as HTL.
    assert (TL1 : 1 <= tl <= 12) by (destruct TOK as (TT & _); unfold HUF_TABLELOG_MAX in TT; lia).
    rewrite LCB. cbv [DTABLE_BYTES HufHarness.DT_BYTES] in DTOP.
    assert (P2 : 2 ^ tl <= 2 * 2 ^ mtl).
    { replace (2 * 2 ^ mtl) with (2 ^ (mtl + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
    lia.
  Qed.

  Lemma ax1p_neg : forall e, Z_to_bv 64 (- e) = Z_to_bv 64 (18446744073709551616 - e).
  Proof.
    intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    replace (18446744073709551616 - e) with (- e + 1 * 2 ^ Z.of_N 64) by (cbn; lia). rewrite Z.mod_add by (cbn; lia).
    reflexivity.
  Qed.

  Lemma ax1p_err : forall mm e j' (u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word),
    0 < e < 120 -> munch DW m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm lo SPF ->
    rw_cells bsegs mm SPF [CB 40 j'] -> rw_cells bsegs mm (SP + -88) FRS11 ->
    evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (AX1_CALL + 4)) (Z_to_bv 64 SPF) gp tp u5 u6 u7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST)
                               (Z_to_bv 64 (18446744073709551616 - e)) u11 u12 u13 u14 u15 u16 u17 (Z_to_bv 64 AX1_KSB)
                               (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl))
                               s6 s7 s8 s9 s10 s11 u28 u29 u30 u31)
                            FR (Z_to_bv 64 AX1_POST) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros mm e j' u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 HE MU WM MI STK RWJ FRC.
    pose proof (E1 ent_sp_bounds) as SB. unfold AX1_POST, AX1_CALL, AX1_KSB in *.
    kx_runFm [AX1_EPI] 10%nat [KZRange e 1 119; KZRange SP 8192 (2^47); KZRange SPF 4096 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
    all: ax1_side.
    kx_post_regs. cbn [mem_denot].
    eapply (E1 ent_epi); [exact STK | exact RWJ | reflexivity | exact FRC | exact MI | exact MU | exact WM].
  Qed.

  Lemma ax1p_keep : forall mm m', AX1M' mm ->
    munch [(SPF - ABIT_INIT_STACK, SPF); (SPF, SPF + 40)] mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' ->
    stk bsegs m' lo SPF -> AX1M' m'.
  Proof using All.
    intros mm m' HM MU' WM' MI' STK'.
    destruct HM as ((buf & BU & BL) & BSS & BCB & STK & FRC & MI & MU & WM).
    pose proof (E1 ent_sp_bounds) as SB. pose proof ax1p_d0 as D0. pose proof ax1p_dtb as DTB.
    unfold ABIT_INIT_STACK, HUF_DEC_STACK_A in *.
    unfold AX1M.
    split; [exists buf; split; [eapply u8arr_transport; [exact BU | exact MU' | exact WM' |] | exact BL] |].
    { rewrite length_map, BL. cbn [disjoint_from]. lia. }
    split.
    { eapply ax1p_bt; [exact BSS | exact MU' |]. destruct (Z_lt_le_dec 0 n) as [NP|N0].
      - right. destruct (ax1p_src NP) as (AB & _). pose proof (ablk_lin _ _ AB). rewrite length_map. cbn [disjoint_from]. lia.
      - left. destruct src; [reflexivity | cbn [length] in N0; lia]. }
    split; [eapply bytes_at_transport; [exact BCB | exact MU' |]; cbn [disjoint_from]; lia |].
    split; [exact STK' |].
    split; [eapply rw_cells_transport; [exact FRC | exact MU' | exact WM' |]; cbn [disjoint_from cells_size csize]; lia |].
    split; [exact MI' |].
    split.
    - eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']].
      intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia.
    - eapply wmono_trans; [exact WM | exact WM'].
  Qed.

  Lemma ax1p_post : forall mm m' (ret : Z) (u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word),
    CONT -> AX1M' mm ->
    munch [(SPF - ABIT_INIT_STACK, SPF); (SPF, SPF + 40)] mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' ->
    stk bsegs m' lo SPF ->
    match init_dstream src with
    | Ok d => ret = n /\ bd_zero d = false /\ exists jp, rw_cells bsegs m' SPF (bitdz_cellsA SS d jp)
    | Err e => ret = - e /\ exists j', rw_cells bsegs m' SPF [CB 40 j']
    | Ub | NoFuel => False
    end ->
    evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (AX1_CALL + 4)) (Z_to_bv 64 SPF) gp tp u5 u6 u7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST)
                               (Z_to_bv 64 ret) u11 u12 u13 u14 u15 u16 u17 (Z_to_bv 64 AX1_KSB) (Z_to_bv 64 (DT + 4))
                               (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl)) s6 s7 s8 s9 s10 s11 u28 u29 u30 u31)
                            FR (ret_pc (Z_to_bv 64 (AX1_CALL + 4))) fc None m' (seg_rom bsegs)).
  Proof using All.
    intros mm m' ret u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 KC HM MU' WM' MI' STK' RES.
    pose proof (ax1p_keep mm m' HM MU' WM' MI' STK') as HM'.
    rewrite (ret_pc_even (AX1_CALL + 4)) by (unfold AX1_CALL; lia).
    destruct (init_dstream src) as [d|e| |] eqn:ID; try contradiction.
    - destruct RES as (-> & BZ & jp & RW). eapply KC; [exact HM' | exact RW | first [exact ID | reflexivity]].
    - destruct RES as (-> & j' & RW). rewrite ax1p_neg. pose proof (init_err src e ID) as HE.
      destruct HM' as (_ & _ & _ & STK2 & FRC2 & MI2 & MU2 & WM2).
      eapply ax1p_err; [exact HE | exact MU2 | exact WM2 | exact MI2 | exact STK2 | exact RW | exact FRC2].
  Qed.

  Lemma ax1p_e1 : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) buf,
    mem_inv bsegs m0 -> stk bsegs m0 lo SP -> bytes_at bsegs m0 SS (map (Z_to_bv 8) src) ->
    bytes_at bsegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl] -> bytes_at bsegs m0 (DT + 4) cbs ->
    u8arr bsegs m0 DST (map (Z_to_bv 8) buf) -> zlen buf = dcap -> 1 <= dcap ->
    CONT ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 n)
                               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            FR (Z_to_bv 64 AHUF_DX1_1X) fc None m0 (seg_rom bsegs)).
  Proof using All.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 buf MI STK SRCB DTH CBS OUT LBF DC1 KC.
    ax1p_facts.
    destruct HOUT as [[D0 C0] | [pb HPB]]; [lia |].
    pose proof (hb_unpoisoned AI L RNG st LB m0 pb DST dcap AH HPB) as (UDB & B16 & _ & BBLK & BTOP & WDB1 & WDBS1 & WRB).
    pose proof (ablk_lin _ _ BBLK) as (B1 & _ & _ & _).
    assert (UDT4 : unpoisoned m0 DT (DT + 4)) by (eapply unpoisoned_sub; [exact UDT | lia | lia]).
    assert (ESP : sp = Z_to_bv 64 SP) by (symmetry; apply Z_to_bv_bv_unsigned).
    rewrite ESP at 2.
    pose proof (munch_refl DW m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
    ax1p_frame STK.
    assert (LDTH : Z.of_nat (length [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl]) = 4) by reflexivity.
    kx_runFm [ABIT_INIT_D] 60%nat
        [KZRange SP 8192 (2^47); KZRange SPF 4096 (2^47); KZAlign SP 16; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32 - 1);
         KZRange (DST + dcap) 4097 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000;
         KZDisj SPF 128 0xb2128 8; KZDisj SPF 128 0xba2f8 8; KZDisj SPF 128 (Z.shiftr DT 3 + 0x7fff8000) 1;
         KZRange n 0 (2^26); KZRange DT 4096 (2^47 - 8192); KZAlign DT 16;
         KZRange tl 1 12; KZRange mtl 1 12;
         KZWr SPF 128; KZDisj SPF 128 DT 4]
        [(DT, 4)] [(DT, 4); (SPF, 128); (0xb2128, 8); (0xba2f8, 8)] [(DT, 4)].
    all: ax1_side.
    all: try (unfold ABase.AIMG_HI in *; lia).
    all: try (rewrite ?Z.shiftr_div_pow2 by lia; lia).
    lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "ax1p: side goal left" end.
    kx_read_eq 35%nat RD35.
    lazymatch type of RD35 with _ = rdval _ _ ?ad _ _ =>
      replace ad with (Z_to_bv 64 (DT + 2)) in RD35
        by (unfold adenot; cbn [a_base a_off]; ax1_ez2; rewrite ?v_addi_lit; f_equal; lia) end.
    rewrite (ax1e_rdDT _ DT tl mtl _ DTH ltac:(lia) ltac:(lia)) in RD35.
    kx_post_regs_keep. rewrite RD35. ax1_ez2.
    pose proof (munch_refl [(SPF, SPF + 128)] m0) as MUW.
    kx_munch_wins MUW [(SPF, 128)]. kx_munch_wins MU [(SPF, 128)].
    kx_post_mem_free.
    kx_cells_post.
    lazymatch goal with |- context [mem_denot ?E m0 ?lg] => set (mm := mem_denot E m0 lg) in * end.
    kx_clear.
    pose proof ax1p_d0 as D0'. pose proof ax1p_dtb as DTB.
    assert (HM : AX1M' mm).
    { unfold AX1M. split; [exists buf; split; [eapply u8arr_transport; [exact OUT | exact MUW | exact WM |] | exact LBF];
              rewrite length_map, LBF; cbn [disjoint_from]; unfold ABase.AIMG_HI in *; lia|].
      split.
      { eapply ax1p_bt; [exact SRCB | exact MUW |]. destruct (Z_lt_le_dec 0 n) as [NP|N0].
        - right. destruct (ax1p_src NP) as (AB & _). pose proof (ablk_lin _ _ AB). rewrite length_map. cbn [disjoint_from]. lia.
        - left. destruct src; [reflexivity | cbn [length] in N0; lia]. }
      split; [eapply bytes_at_transport; [exact CBS | exact MUW |]; cbn [disjoint_from]; unfold ABase.AIMG_HI in *; lia |].
      split; [eassumption |].
      split; [kx_cells_merge |].
      split; [eassumption |]. split; eassumption. }
    destruct SRCB as (SR1 & SR2 & _). rewrite length_map in SR2.
    eapply (ax1p_call POST mm _ SS); [exact MU | eassumption | eassumption | eassumption | eassumption
      | destruct HM as (_ & HB & _); exact HB | lia | lia | intros; reflexivity | reflexivity | reflexivity | reflexivity |].
    intros m' ret u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 MU' WM' MI' STK' RES.
    eapply (ax1p_post mm m'); eassumption.
  Qed.

  Lemma ax1p_e0 : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv bsegs m0 -> stk bsegs m0 lo SP -> bytes_at bsegs m0 SS (map (Z_to_bv 8) src) ->
    bytes_at bsegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl] -> bytes_at bsegs m0 (DT + 4) cbs ->
    DST = 0 -> dcap = 0 ->
    CONT ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 n)
                               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            FR (Z_to_bv 64 AHUF_DX1_1X) fc None m0 (seg_rom bsegs)).
  Proof using All.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 MI STK SRCB DTH CBS D0 C0 KC.
    ax1p_facts.
    assert (UDT4 : unpoisoned m0 DT (DT + 4)) by (eapply unpoisoned_sub; [exact UDT | lia | lia]).
    assert (ESP : sp = Z_to_bv 64 SP) by (symmetry; apply Z_to_bv_bv_unsigned).
    rewrite ESP at 2.
    pose proof (munch_refl DW m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
    ax1p_frame STK.
    assert (LDTH : Z.of_nat (length [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl]) = 4) by reflexivity.
    kx_runFm [ABIT_INIT_D] 60%nat
        [KZRange SP 8192 (2^47); KZRange SPF 4096 (2^47); KZAlign SP 16; KZRange DST 0 0; KZRange dcap 0 0; KZRange (DST + dcap) 0 0;
         KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000;
         KZDisj SPF 128 0xb2128 8; KZDisj SPF 128 0xba2f8 8; KZDisj SPF 128 (Z.shiftr DT 3 + 0x7fff8000) 1;
         KZRange n 0 (2^26); KZRange DT 4096 (2^47 - 8192); KZAlign DT 16;
         KZRange tl 1 12; KZRange mtl 1 12;
         KZWr SPF 128; KZDisj SPF 128 DT 4]
        [(DT, 4)] [(DT, 4); (SPF, 128); (0xb2128, 8); (0xba2f8, 8)] [(DT, 4)].
    all: ax1_side.
    all: try (unfold ABase.AIMG_HI in *; lia).
    all: try (rewrite ?Z.shiftr_div_pow2 by lia; lia).
    lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "ax1p: side goal left" end.
    kx_read_eq 35%nat RD35.
    lazymatch type of RD35 with _ = rdval _ _ ?ad _ _ =>
      replace ad with (Z_to_bv 64 (DT + 2)) in RD35
        by (unfold adenot; cbn [a_base a_off]; ax1_ez2; rewrite ?v_addi_lit; f_equal; lia) end.
    rewrite (ax1e_rdDT _ DT tl mtl _ DTH ltac:(lia) ltac:(lia)) in RD35.
    kx_post_regs_keep. rewrite RD35. ax1_ez2.
    pose proof (munch_refl [(SPF, SPF + 128)] m0) as MUW.
    kx_munch_wins MUW [(SPF, 128)]. kx_munch_wins MU [(SPF, 128)].
    kx_post_mem_free.
    kx_cells_post.
    lazymatch goal with |- context [mem_denot ?E m0 ?lg] => set (mm := mem_denot E m0 lg) in * end.
    kx_clear.
    pose proof ax1p_d0 as D0'. pose proof ax1p_dtb as DTB.
    assert (HM : AX1M' mm).
    { unfold AX1M. split; [exists []; split; [unfold u8arr; split; [unfold bytes_at; cbn [map length]; split; [lia|]; split; [lia|]; intros; lia
              | unfold wr_at; cbn [map length]; split; [lia|]; split; [lia|]; intros; lia] | cbn [length]; lia]|].
      split.
      { eapply ax1p_bt; [exact SRCB | exact MUW |]. destruct (Z_lt_le_dec 0 n) as [NP|N0].
        - right. destruct (ax1p_src NP) as (AB & _). pose proof (ablk_lin _ _ AB). rewrite length_map. cbn [disjoint_from]. lia.
        - left. destruct src; [reflexivity | cbn [length] in N0; lia]. }
      split; [eapply bytes_at_transport; [exact CBS | exact MUW |]; cbn [disjoint_from]; unfold ABase.AIMG_HI in *; lia |].
      split; [eassumption |].
      split; [kx_cells_merge |].
      split; [eassumption |]. split; eassumption. }
    destruct SRCB as (SR1 & SR2 & _). rewrite length_map in SR2.
    eapply (ax1p_call POST mm _ SS); [exact MU | eassumption | eassumption | eassumption | eassumption
      | destruct HM as (_ & HB & _); exact HB | lia | lia | intros; reflexivity | reflexivity | reflexivity | reflexivity |].
    intros m' ret u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 MU' WM' MI' STK' RES.
    assert (EQ8 : Z_to_bv 64 0 = Z_to_bv 64 dcap) by (rewrite C0; reflexivity).
    assert (EQ9 : Z_to_bv 64 0 = Z_to_bv 64 DST) by (rewrite D0; reflexivity).
    assert (EQ20 : Z_to_bv 64 0 = Z_to_bv 64 (DST + dcap)) by (rewrite D0, C0; reflexivity).
    rewrite EQ8 at 1. rewrite EQ9 at 1. rewrite EQ20 at 1.
    eapply (ax1p_post mm m'); eassumption.
  Qed.

  Lemma ax1p_main : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) buf,
    mem_inv bsegs m0 -> stk bsegs m0 lo SP -> bytes_at bsegs m0 SS (map (Z_to_bv 8) src) ->
    bytes_at bsegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl] -> bytes_at bsegs m0 (DT + 4) cbs ->
    ((DST = 0 /\ dcap = 0) \/ (u8arr bsegs m0 DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap /\ 1 <= dcap)) ->
    CONT ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 n)
                               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            FR (Z_to_bv 64 AHUF_DX1_1X) fc None m0 (seg_rom bsegs)).
  Proof using All.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 buf MI STK SRCB DTH CBS [(D0 & C0) | (OUT & LBF & DC1)] KC.
    - eapply ax1p_e0; eassumption.
    - eapply ax1p_e1; eassumption.
  Qed.
End AX1P.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DEC1.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.

  Ltac dec_ifF := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let b := eval vm_compute in c in change c with b; cbv iota end.

  (* [comment removed for export] *)
  Ltac ax1e_pro STK DT :=
    carve_frame 64%nat STK;
    lazymatch goal with FR0 : rw_cells bsegs _ (bv_unsigned _ + -64) [CB 64 _] |- _ =>
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8]%nat) in FR0; [| reflexivity]; cbn [mk_CB_cells app] in FR0 end;
    zstep; do 8 zstep;
    zstep;
    zstep; zstep; zstep; zstep; zstep;
    rewrite ?(Z.land_ones DT 64) by lia; rewrite ?(Z.mod_small DT (2^64)) by lia; rewrite ?Z.shiftr_div_pow2 by lia;
    change (2^3) with 8;
    lazymatch goal with H : bytes_at bsegs ?mm (2147450880 + DT / 8) _ |- _ =>
      let RSH := fresh "RSH" in
      pose proof (bytes_at_read bsegs mm (2147450880 + DT / 8) _ 0 1 H ltac:(lia) ltac:(cbn; lia)) as RSH;
      rewrite Z.add_0_r in RSH;
      zstep; clear RSH end;
    zstep; dec_ifF;
    zstep.

  Lemma sgtz_and_l : forall x, 0 <= x < 2^63 ->
    Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? Z.lxor x 9223372036854775808)) 18446744073709551615) x = x.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax1e ()) ["CANSEC1"; "DEC1"] "h07__arithh14__ffh28__varmaph35__with44__x1h52Hxh61xh71zp;2p;1p;3p;4p;7p;8p;6g008Tj27Tg004Aj10Tg004fj13Tg007Rj12Tg0087j2<Tg00CJj2:Tg00?ej29Tg02S@j2ATg02S^j2@Tg02T;j1>Tg009fj2=Tg0072j2XTg02TXj2;Tg006Xj38Tg00Gbj1VTg00<>j1UTg00I@j2TTg00J<j1FTg00JZj1ETg00Qaj25Tg00KEj2CTg00N4j44Tg00@@j1BTg00Lnj3GTg00Rhj7HTg00LLj1ITg00SLj8JTg00OBj2KTg00Dkj2?Tg00Odj2LTg00PPj3MTg00Poj4NTg02U6j2OTg02V6j1PTg00Hbj1QTg02VTj3RTg001jj6STg00RDj7WTf0R0#0#0#0#0p=D%00#0#0#0#0#0#0#0p=1f1R1g00U5R2g00UTR3P3g00V4R4P0g00VTFWp=6g00T0R5g00WYR6/70g00W4R7#0R8#3R9%27#2#2#2#2R:#3'<R;,:0'9R<P5%08#DR8#0#1#1#1#1#1#1#1#3R=1A1='@#>,=6R=%38R8,<9'Xf2R>,;0=85>X75g00\[R?#VR@%U?R?1T51%F5RA%E5RBP2P3P3P4PBP2P3P3P4P51556R2g00TNRC1C57R7C4,6BP5P7g00^R1559%B:5G5C4,6BFHR:%I3P:GJ1KB4R4P0P>g00_9R:g00_YR3'?1L0>=8:3dAM561CNR3b1b2b3X4517611:1;'9\<^45P0P>P1O2b0,O1%P8,;=P@P?%Q5PAP5P2PC1558C4,6BP4P3b1b2b31768P0b09R=8ESW5W6o"). Qed.

  Lemma ax1e_tab_len : forall (cells : list deltX1) tl mtl, zlen cells = 2^(mtl+1) -> 0 <= tl <= mtl + 1 -> 0 <= mtl ->
    zlen (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells)) = 2 * 2^tl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax1e ()) ["CANSEC1"; "DEC1"] "h04__p1h14__x1h24cstrh37__arithh44__ffh58__varmaph65__with74__x2h81xh94__p2h:4__x3h;4__x4h<4__x5h=1nh>1Hh?2H0h@2H1hA2H2hB2LChC1MhD1ThE5cellshF3mtlhG2tlhH1yhI2z1hJ2z2p&0p;1p;2p;4p;3p;5p;<p;6p;7p;8p;Bg00<>j1aTg02EMR0j16Tg004Aj1RTg004fj1bTg005Dj2ATg0087j27Tg008Tj25Tg00?ej24Tg012:R1j23Tg00>3R2j1PTg00@@k109Tg00`9k107Tg02W7k102Tg00=Sj2NTg02X7j2QTg00EEj1:Tg02XNj2\Tg02Xej1TTg00Gbj1rTg00Hbj1pTg00J<j1oTg00JZj1nTg00Qaj2UTg00N4j4MTg00OBj2iTg00Dkj2GTg00Odj2fTg006Xj3Ik101Tg00PPj3eTg00Poj4dTg00CJj2<Tg00I@j2HTg00I^j4JTg00KEj2FTg00MQj3cTg00LLk108Tg02YJk506Tg00Bbk405Tg02Z1j2OTg02ZNR3j2VTg02Zkk100Tg02[Il<xTg02[nj2tTg00eRj2LTg02\Pj2sTg00AHj1[Tg02]2j2WTg02]Sj3DTg00Edj2ZTg02^<j2qTg02^ej3ETg02_Nj2STg007Rj1YTg01J1j3XTg02`:j4uTg02`ej1vTg02afj1wTg001jj6^Tg02bnj3mTg02cMj3lTg00RDj7kTg00Khj6{Tg00Rhj7|Tg00SLj8jTg02col<_Tg02dTlB`Tg00FMj3hTg00G6k203Tg00HBk304Tg02e:j7gTg02e^R4f0R5'Np=>g00T0R6f1R7;I5p=2g00WYR8/55p=9P7g00U5R9g00UTR:P:g00V4R;P5g00VTFkp=1P7P9P:P:P;P5E{p=KP6P7g00TNP5CMp=Cf2R<P9P:P:P;P7P5F|p=Bf3R=P9P:P:P;P<P7P5Gjp=8P6g02L>R>P6P6P2f4R2P0P=g02f^P<P7P5M<_p=~P>P>P>P6P6P6g02gKP0P0P0P1g02gkf5R1P2P=P<P7P5MB`p=}P>P>P>P6P6P6g02hNP0P0P0P3g02hnP1P2P=P<P7P5MB`p=zP>P6P6P6P0P0P1P2P=P<P7P5M<_p=y1Z65p==Ah675p=0g00]f-035p=@g00\[R0@0475p=;P6P7g02NPP5CMp=?P<P9P:P:P;P7P5Fgp=]%a4%><#6g00W4R4#RR9#bR3%b4R?,A5'7'2%9<R@1A7?RA,5<'4P>1732RB,33#PRC%R9RD#R$09$07RE&021RF'N'Q%65RG1731RH,33RI'2X=>P>g00]GRJ#:RK#:RL%>1RM'\%PI/Q5#6/2IX=>P3P21A=?RI%TMRN%6M#9RM%r0RO%a0R0%p6RP%o6RQ%n6RRP61U68RSg00^RRT1U63RUCM'11iR;R;P5P<g00_9RVg00_YRW'G1f5<=IVWdAe687CdRWb4b5b61<83P5b3RVb2PNPMp-0RMPOP0P61H6<P7PPCJPQPR1KR21F64RN1F69RX1U6?5c6'C,1RRY5BR&08:R:PYC8P;PWb4b5b6X16X76W0155A,4<1A<?,57[^16^76^0MP5f6RA#9P1PAP=O4b3b2I06173I,5BP3P1%>ARB#TRI%6B#9RBPVb2PIPBPOP01H67PQPR1CSN,1RRB1KR=5BRP:PBC8P;PWb4b5b6X16X0M%95/47%97[^16^0MP5f7RB1AA?'5PBP2O3b3b2H051<8H173A,33RH#PRI%>BRV,\LRY'QRZ#6R[/2H1O8HR\%6VR],33R^'VR_/2HP6P6&016R`P5X86RaP`1275$00XH6X86P[P_PaPa1G6GX8>PZP_PIP\Pa1O85X86PHPH1G6HRaD~PYP^PLP31G63PVP]1G6]E}EzEyPHPHPaM<x%TV%9]173B,33R],t81<8]1O8]RV/2]'415]8AI6V8'4'Lf8RV,73,33,O8P6f:R]#>#6,33Ra,s51<5a1V5aRH/25'415a512Ha'4'Lf;RH#>#6,33,V7P6%[4,W6Ra%:LR^#:#:RY#:R\#:RI#=R_5D6%[9,W6R9%=KRK5D61Z6JRJ'0RZ'01q63R>=E6JRG%=YRY9E6>%=LRL9E6>'0,0_'0#@'S%=\R\%=^R^9E6>'0#@R_AE6>K/0J,0\%:I#=AD69L,0\'0,0G#@'SAD6a\RG/0Z10J^#@'SAD6aY/0J,0G#@10YJ,0\#@1;_O,;_';';';';';';P0P6P61H62P<PPCJP7P6PPP=1H61CJCJPQPR1KRB%Y4R4#Y,F6RQ,?N,1R5BR1F64R49X6URP/CQ,1R1?NP,1R5BR5]RP:PR1KRVAX6UXRU,?Q,1R5BR1CUS,1R1?QS,1R5BR5]RP:PR1CS4,1RP:PRP6PSPTPXCM,1RP:PR1F6DRD,CX,1RP:PR1?4D,1RP:1?NU,1RC8C8C8C8C8C8P;PWb4b5b6X16X76X:6X;6X<6X0MX9M1252,41133<RW/52125W'4'L121W,4B15W8AI618'4'L%921<82151B12BV133B,2A[[[[[[^16^76^:6^;6^<6^0M^9MP5f<,73R5,33,<8f=#>#6R8,33,<=P=1AH?,73P8P5P7P<P2P1PAPBP]O=b3bJbAbIb@b2Cub?b>%v1,NE%w1E^AmECF,NEAlECFE^XC@WDWBXF6XG6WEo"). Qed.

  Theorem dec_1x1_proofA : dec1_int_stmtA AI rng_fs x1_tabA AHUF_DX1_1X.
  Proof.
    unfold dec1_int_stmtA.
    intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      FR fc m st LB DST dcap S DT mtl pdt src lo rstk
      AH NFK ABL MTL HDT TAB HOUT DC BYT BYS NSM S16 SRCI DJ1 DJ2 DJ3 STK LOA LOS RCL RLO RHI RRL SPT SP16 MI TPA HINV
      WSK WIM WIS WFS RRS E10 E11 E12 E13 E14.
    subst a0 a1 a2 a3 a4.
    destruct TAB as (tl & cells & DTH & LC & TOK & TLM & CBS).
    assert (TL1 : 1 <= tl <= 12) by (destruct TOK as (TT & _); unfold HUF_TABLELOG_MAX in TT; lia).
    pose proof (ax1e_tab_len cells tl mtl LC ltac:(lia) ltac:(lia)) as LCB.
    remember (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells)) as cbs eqn:ECB.
    assert (OUTC : exists buf, (DST = 0 /\ dcap = 0) \/
                               (u8arr bsegs m DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap /\ 1 <= dcap)).
    { destruct HOUT as [D0 | (pb & HPB)]; [exists []; left; exact D0 |].
      destruct (hb_unpoisoned AI L RNG st LB m pb DST dcap AH HPB) as (_ & _ & N1 & BB & _ & _ & _ & WR).
      pose proof (ablk_lin _ _ BB) as BL.
      destruct (ax1p_wr_u8arr m DST dcap WR ltac:(lia) ltac:(lia)) as (buf & U & LU).
      exists buf. right. split; [exact U|]. split; [exact LU|lia]. }
    destruct OUTC as (buf & OUTC).
    assert (DSTF : unpoisoned m DST (DST + dcap) /\ (0 < dcap -> rng RNG DST dcap) /\
                   (0 < dcap -> rng RNG (shad DST) (shlen (dcap + 7)))).
    { destruct HOUT as [(-> & ->) | (pb & HPB)].
      - split; [unfold unpoisoned; split; [lia|]; split; [lia|]; intros; lia | split; intros; lia].
      - destruct (hb_unpoisoned AI L RNG st LB m pb DST dcap AH HPB) as (UD & _ & _ & _ & _ & RD & RDS & _).
        split; [exact UD | split; intros; assumption]. }
    destruct DSTF as (UDB & WDB & WDBS).
    pose proof (hb_unpoisoned AI L RNG st LB m pdt DT (DTABLE_BYTES mtl) AH HDT) as (UDT & _ & _ & _ & _ & WDT & WDTS & _).
    eapply (ax1p_main AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m DST dcap S DT mtl tl lo src
              cells cbs pdt rstk); try eassumption; try (unfold KXGoM.apart; lia); try (subst cbs; reflexivity).
    intros mm d jp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HM BD ID.
    assert (NP : 0 < zlen src) by (destruct src; [cbn in ID; discriminate | cbn [length]; lia]).
    destruct (SRCI NP) as (p & A & k & HS & L1 & L2).
    destruct (hb_unpoisoned AI L RNG st LB m p A k AH HS) as (U & A16 & N1 & AB & AT & R1 & R2 & _).
    eapply (ax1e_cont AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m DST dcap S DT mtl tl lo src
              cells cbs pdt A (A + k)); try eassumption; try (unfold KXGoM.apart; lia); try (subst cbs; reflexivity).
    all: try (split; lia).
    all: try (split; [exact AB | Z.div_mod_to_equations; lia]).
    all: try (replace (A + k - A) with k by lia; assumption).
    all: try (replace (A + k - A + 7) with (k + 7) by lia; assumption).
  Qed.
End DEC1.
End CANSEC1.
