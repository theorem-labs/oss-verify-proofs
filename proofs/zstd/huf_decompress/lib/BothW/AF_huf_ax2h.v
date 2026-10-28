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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkMem HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXGoM FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_ax2 AF_huf_ax2b AF_huf_ax2c AF_huf_ax2d AF_huf_ax2e AF_huf_ax2f AF_huf_ax2g AF_huf_ax2g2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax2h () := "C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begI47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC47Corelib4Init5Logic3notK47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic6or_indC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib5Lists4List2InK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K47Corelib4Init5Logic2or01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameK47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2h>ent2_sp_boundsI47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_block_boundsC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic6eq_indC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergec5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2h;ent2_magreec5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2h:ent2_aheapC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27AX2_EPIC5ARocqVerifyHarness?AgentSubmission5Plain<RF_huf_iface8x2_bytesC47Corelib4Init3Nat3minC47Corelib4Init3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit39x2_bytes'C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3@x2_bytes'_lengthC47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List=length_firstnC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface7x2_tabAI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface7src_inAC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface=hb_unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_rtcellsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8artcellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2h<ax2e_tab_lenC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow>unpoisoned_nilC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission5BothW7RtCells=no_image_asanC5ARocqVerifyHarness?AgentSubmission4LibA6ShadowArw_cells_of_wr_atC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3ArrAu8arr_of_rw_cellsC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKitAbytes_of_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC35stdpp7tactics<f_equal_helpC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqK4ELinuxProcessSemantics5Riscv5Instr5instr03c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2h8ent2_epiC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax24AX2MC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2g9ax2_smallC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_ax2g27ax2_bigC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface>dec1_int_stmtAC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC46Stdlib9micromega;ZifyClasses9and_morphK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem;wr_at_writeC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface?HUF_DEC_STACK_AC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface;AHUF_DX2_1X".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)

  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DEC2.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.

  (* [comment removed for export] *)

  Lemma ax2e_tab_len : forall (cells : list deltX2) tl mtl, zlen cells = 2^mtl -> 0 <= tl <= mtl -> 0 <= mtl ->
    zlen (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes cells)) = 4 * 2^tl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax2h ()) ["CANSEC1"; "DEC2"] "h04__p1h14__x1h24cstrh37__arithh44__ffh58__varmaph65__with74__x2h81xh94__p2h:4__x3h;4__x4h<4__x5h=1nh>1Hh?2H0h@2H1hA2H2hB2LChC1MhD1ThE5cellshF3mtlhG2tlhH1yhI2z1hJ2z2p&0p;1p;2p;4p;3p;5p;<p;6p;7p;8p;Bg00<>j1aTg02G\R0j16Tg004Aj1PTg004fj1`Tg0087j27Tg008Tj24Tg00?ej25Tg012:R1j23Tg00>3R2j1OTg00@@j1bTg00`9k107Tg02SCk104Tg00=Sj2LTg02TCj2TTg00EEj1;Tg02TZj2[Tg02U1j1RTg00Gbj1rTg00Hbj1pTg00J<j1oTg00JZj1nTg00Qaj2STg00N4j4GTg00OBj2hTg00Dkj2FTg00Odj2eTg006Xj3Hk102Tg00PPj3dTg00Poj4cTg00CJj2<Tg00I@j2MTg00I^j4JTg00KEj2CTg00LLk106Tg02UVk505Tg00Bbk403Tg02V=j2NTg02VZR3j2UTg02W7k101Tg02WUl<vTg02X:j2uTg00eRj2ITg02X\j2sTg00AHj1VTg02Y>j2XTg02Y_j3DTg00Edj2ZTg02ZHj2qTg02[1j3ETg02[Zj2QTg007Rj1YTg01J2j3\Tg02\Fj4mTg02]1j1tTg02^2j1lTg001jj6]Tg02_:j3wTg02_Yj3kTg00RDj7jTg00Khj6{Tg00Rhj7iTg00SLj8|Tg02`;l<^Tg02``lB_Tg00FMj3~Tg00G6k200Tg00HBj3gTg02aFj7fTg02ajR4f0R5'Lp=>g00T0R6f1R7;H5p=2g00WYR8/45p=8P7g00U5R9g00UTR:P:g00V4R;P5g00VTFjp=1P7P9P:P:P;P5E{p=KP6P7g00TNP5CGp=Bf2R<P9P:P:P;P7P5Fip=Af3R=P9P:P:P;P<P7P5G|p=:P6g02LAR>P6P6P2f4R2P0P=g02bjP<P7P5M<^p=}P>P>P>P6P6P6g02cWP0P0P0P1g02d7f5R1P2P=P<P7P5MB_p=zP>P>P>P6P6P6g02dZP0P0P0P3g02e:P1P2P=P<P7P5MB_p=yP>P6P6P6P0P0P1P2P=P<P7P5M<^p=x1Z65p==A~675p=0g00]f-005p=@g00\[R0?g75p=9P6P7g02NSP5CGp=?P<P9P:P:P;P7P5Ffp=W%a4%><#6g00W4R4#PR9#`R3/75'2%8<R?14<7'5P>%P9R@#`RA1732RB'3#ORC%P@#b$07RD&041RE'L'T%65RF1731RG,3ARH'2X=>P>g00]GRI#;RJ#;RK#;RL#;RM%>1RN'[%OH/T5#6/2HX=>P3P2P=%RNRH%6N#8RN%r0RO%a0R0%p6RP%o6RQ%n6RRP61S68RSg00^RRT1S63CG'11hR;R;P5P<g00_9RUg00_YRV'F1e5<=HUVdAd687CcRVb4b5b61<83P5b3RUb2PHPNp-0RNPOP0P61M6<P7PPCJPQPR1KR21C64RH1C69R9'B,1RRW5AR&06:R:PWC:P;PVb4b5b6X16X76W01457,5<147<[^16^76^0NP5f6RW#8P1PWP=O4b3b2I05173=,4BP3P1%>WRB#RRX%6B#8RBPUb2PXPBPOP01M67PQPR1BSH,1RRB1KR=5ARP:PBC:P;PVb4b5b6X16X0N%85/57%87[^16^0NP5f7RB/4WPBP2O3b3b2H031<8G173W,3ARG#ORX%>BRU,[MRY'TRZ#6R[/2G1N8GR\%6UR],3AR^'UR_/2GP6P6&026R`P5X86RaP`1275$01XH6X86P[P_PaPa1F6FX8>PZP_PXP\Pa1N85X86PGPG1F6GRaD}PYP^PMPA1F6APUP]1F6]EzEyExPGPGPaM<v%RU%8]173B,3AR],u81<8]1N8]RU/2]'514]8AH6U8'5'If8RU,73,3A,N8P6f:R]#>#6,3ARa,s51<5a1U5aRG/25'514a512Ga'5'If;RG#>#6,3A,U7P6%V4,X6Ra%;MRM#;R^#;RY#=R\5D6%V@,X6RX%=JRJ5D61Z6IRI'0R_'01q6ARZ=E6IR>%=MRM9E6Z%=KRK9E6Z'0,0\'0#@'Q%=^R^%=LRL9E6Z'0#@R\AE6ZJ/0I,0^%;Y#=AD6XK,0^'0,0>#@'QAD6a^R>/0_10IL#@'QAD6aM/0I,0>#@10MI,0^#@19\O,9\'9'9'9'9'9'9P0P6P61M62P<PPCJP7P6PPP=1M61CJCJPQPR1KRB%Y4R4#Y,C6RQ,?H,1R5AR1S6ARP1C64R45\6R0/BQ,1R1?H0,1R5AR5WRP:PR1KRUA\6P9RP,?Q,1R5AR1BPS,1R1?QS,1R5AR5WRP:PR1BS4,1RP:PRP6PSPTP9CG,1RP:PR1C6@R@,B9,1RP:PR1?4@,1RP:1?HP,1RC:C:C:C:C:C:P;PVb4b5b6X16X76X:6X;6X<6X0NX9N1252,5113A<RV/42125V'5'I121V,5B14V8AH618'5'I%821<82141B12BU13AB,2W[[[[[[^16^76^:6^;6^<6^0N^9NP5f<,73R5,3A,<8f=#>#6R8,3A,<=P=173GP8P5P7P<P2P1PWPBP]O=b3bJbAbIb@b2Cmb?b>%t1,LD%l1E]AwDCE,LDAkDCEE]XC?WDWBXF6XG6WEo"). Qed.

  Lemma dec2_out : forall L RNG st LB m DST dcap, AHEAP AI L RNG st LB m ->
    ((DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB)) ->
    unpoisoned m DST (DST + dcap) /\ (0 < dcap -> rng RNG DST dcap) /\ (0 < dcap -> rng RNG (shad DST) (shlen (dcap + 7))).
Proof.
  intros L RNG st LB m DST dcap AH [(D0 & C0) | (pb & HB2)].
  - subst DST dcap. rewrite Z.add_0_r. split; [apply unpoisoned_nil; lia | split; intros; lia].
  - destruct (hb_unpoisoned AI _ _ _ _ _ _ _ _ AH HB2) as (U & _ & _ & _ & _ & R & RS & _).
    split; [exact U | split; intros; assumption].
Time Qed.

  Lemma dec2_blk : forall L RNG st LB m p A k, AHEAP AI L RNG st LB m -> In (HB p A k) LB ->
    unpoisoned m A (A + k) /\ ablk A (A + k) /\ A mod 8 = 0 /\ rng RNG A (A + k - A) /\ rng RNG (shad A) (shlen (A + k - A + 7)).
Proof.
  intros L RNG st LB m p A k AH HIN.
  destruct (hb_unpoisoned AI _ _ _ _ _ _ _ _ AH HIN) as (U & A16 & _ & BK & _ & R & RS & _).
  replace (A + k - A) with k by lia.
  split; [exact U | split; [exact BK | split; [| split; [exact R | exact RS]]]].
  clear - A16. Z.div_mod_to_equations. lia.
Time Qed.

  Lemma dec2_apart : forall a k b j, b + j <= a \/ a + k <= b -> KXGoM.apart a k b j.
Proof.
  unfold KXGoM.apart. intros. lia.
Time Qed.

  Section DEC2M.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr) (SBL SBH : Z).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HOUT : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
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
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation G2 l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs) (only parsing).

  Lemma dec2_main : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (rstk : region),
    bytes_at bsegs m0 SS (map (Z_to_bv 8) src) ->
    bytes_at bsegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
    bytes_at bsegs m0 (DT + 4) cbs ->
    stk bsegs m0 lo SP -> mem_inv bsegs m0 ->
    rclean m0 rstk -> r_lo rstk <= lo -> SP <= r_hi rstk -> ATOP <= r_rlo rstk ->
    rng_aimg_sh RNG -> rrng RNG rstk ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 n)
                               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            FR (Z_to_bv 64 AHUF_DX2_1X) fc None m0 (seg_rom bsegs)).
Proof using All.
  intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 rstk BS BDT BCB STK MI RCL RLO RHI RRLO WSH WRR.
  assert (G4772 : G2 ax2_goal_4772) by (eapply ax2_goal_4772_ok; eassumption).
  assert (G4768 : G2 ax2_goal_4768) by (eapply ax2_goal_4768_ok; eassumption).
  assert (G3976 : G2 ax2_goal_3976) by (eapply ax2_goal_3976_ok; eassumption).
  assert (G3924 : G2 ax2_goal_3924) by (eapply ax2_goal_3924_ok; eassumption).
  assert (G276 : G2 ax2_goal_276) by (eapply ax2_goal_276_ok; eassumption).
  assert (G2272 : G2 ax2_goal_2272) by (eapply ax2_goal_2272_ok; eassumption).
  assert (G200 : G2 ax2_goal_200) by (eapply ax2_goal_200_ok; eassumption).
  assert (G2052 : G2 ax2_goal_2052) by (eapply ax2_goal_2052_ok; eassumption).
  eapply ax2_entry_ok; eassumption.
Time Qed.
  End DEC2M.

  Theorem dec_1x2_proofA : dec1_int_stmtA AI rng_fs x2_tabA AHUF_DX2_1X.
Proof.
  unfold dec1_int_stmtA.
  intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB
    DST dcap S DT mtl pdt src lo rstk AH NFK BLKS MTL HDT TAB HOUT DC BS BYS NS S16 SIN DJ3 DJ2 DJ1 STK LOA LOS
    RCL RLO RHI RRLO SPT SP16 MI TP HI WSK WIM WSH WFS WRR E0 E1 E2 E3 E4.
  destruct (Z.eq_dec (zlen src) 0) as [Z0 | NZ]; [eapply (dec_1x2_zero AI rng_fs); eassumption |].
  destruct TAB as (tl & cells & BDT & LC & TOK & TLM & BCB).
  destruct (SIN ltac:(lia)) as (ps & SBL & sn & HSB & SB1 & SB2).
  destruct (hb_unpoisoned AI _ _ _ _ _ _ _ _ AH HDT) as (UDT & _ & _ & _ & _ & WDT & WDTS & _).
  destruct (dec2_blk _ _ _ _ _ _ _ _ AH HSB) as (USB & SBK & SB8 & WSB & WSBS).
  destruct (dec2_out _ _ _ _ _ _ _ AH HOUT) as (UDB & WDB & WDBS).
  pose proof TOK as (TL1 & _).
  assert (LCB : zlen (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells)) = 4 * 2^tl)
    by (apply (ax2e_tab_len cells tl mtl LC); lia).
  assert (NSM : 1 <= zlen src < 2^26) by lia.
  subst a0 a1 a2 a3 a4.
  exact (dec2_main L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m DST dcap S DT mtl tl lo src cells
    (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells)) pdt SBL (SBL + sn)
    AH HDT HOUT LOA LOS SPT SP16 TOK eq_refl LCB MTL TLM DC NSM S16 (conj SB1 SB2) (conj SBK SB8) BYS
    (dec2_apart _ _ _ _ DJ1) DJ2 (dec2_apart _ _ _ _ DJ3) UDT UDB USB WSK WIM WDT WSB WDTS WSBS WDB WDBS
    t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 rstk BS BDT BCB STK MI RCL RLO RHI RRLO WSH WRR).
Time Qed.
End DEC2.
End CANSEC1.
