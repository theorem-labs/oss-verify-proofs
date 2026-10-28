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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_z4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_z4sb () := "C46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:length_mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_seqC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init5Logic6eq_indC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission5BothW4BImgAref_wview_overlayK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init9Datatypes:option_mapC56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init3Nat3addC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit@byte_of_unsignedC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_lC46Stdlib5Lists4List=nth_error_seqC46Stdlib5Lists4List=nth_error_mapK47Corelib4Init5Logic3and01C47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef3seqC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m<z4_sp_boundsC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega:ZMicromega;ZArithProof03K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04C35stdpp4base6lookupC46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXK47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb8z4s_srcpI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchI47Corelib5Lists7ListDef6Forall00C46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_nilC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb:z4s_blocksc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb6z4s_spC46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb;z4_wr_u8arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit9appW_consC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KLOWC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit8appW_nilC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit7shcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kitEshclean_transport_appc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb8z4s_appWC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4appWK46Stdlib9micromega=RingMicromega5Psatz07C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_munchC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface=hb_unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow>unpoisoned_subK46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb6z4s_d0C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_block_boundsC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb:z4s_magreec5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb9z4s_aheapC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m7AZ4_EPIc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb:z4s_srcblkc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb7z4s_epic5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb7z4s_retC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_lit".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Lemma z4_wr_u8arr : forall m A n, wr_at bsegs m A n -> 0 <= n -> AIMG_HI <= A ->
  exists buf : list Z, u8arr bsegs m A (map (Z_to_bv 8) buf) /\ zlen buf = n.
Proof.
  intros m A n (A0 & AN & WV) N0 AH. unfold AIMG_HI in AH.
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


Lemma z4_mod16_8 : forall A, A mod 16 = 0 -> A mod 8 = 0.
Proof. intros A H. Z.div_mod_to_equations. lia. Qed.

Lemma z4_shad_span : forall x, shad (x - 1) + 1 = shad (x + 7).
Proof. intros x. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Z4SB.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
            (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -576).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis NFK : forall F k, ~ In (mkABlock (ABFake 0) F k) LB.
  Hypothesis ABL : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis DSTF : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis NSM : n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SRCB : 0 < n -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + n <= SBH.
  Hypothesis DJ1 : DT + DTL <= SS \/ SS + n <= DT.
  Hypothesis DJ2 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis DJ3 : DT + DTL <= DST \/ DST + dcap <= DT.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TPA : tp = Z_to_bv 64 ATP.
  Hypothesis HINV : harness_invA m0.
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WIS : rng_aimg_sh RNG.
  Hypothesis WFS : rng_fs L RNG.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma z4s_sp : 0x10007fff8000 <= SPF /\ SP <= 2^47 /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP.
Proof using All.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
  unfold HUF_DEC_STACK_A in LOS. lia.
Qed.

  (* [comment removed for export] *)
  Lemma z4s_blocks : AIMG_HI <= DT /\ DT + DTL <= ATOP /\ DT mod 16 = 0 /\ DT + 4 + zlen cbs <= DT + DTL
                     /\ (dcap = 0 \/ (AIMG_HI <= DST /\ DST + dcap <= ATOP))
                     /\ (n = 0 \/ (AIMG_HI <= SBL /\ SBL <= SS /\ SS + n <= SBH /\ SBH <= ATOP)).
Proof using All.
  pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HDT) as (D1 & D2 & D3). cbn [ab_addr ab_size] in D1, D2, D3.
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (_ & AR & _). unfold ablock_range in AR. destruct AR as (_ & _ & _ & D4).
  assert (PT : 2^tl <= 2^mtl) by (destruct (Z.ltb_spec tl 0) as [TN | TN];
    [rewrite (Z.pow_neg_r 2 tl TN); lia | apply Z.pow_le_mono_r; lia]).
  unfold DTABLE_BYTES, HufHarness.DT_BYTES in *.
  split; [exact D1|]. split; [lia|]. split; [exact D4|]. split; [rewrite LCB; lia|]. split.
  - destruct DSTF as [[_ D0] | (pb & IN)]; [left; exact D0 | right].
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3. lia.
  - destruct (Z.eq_dec n 0) as [Z0 | NZ]; [left; exact Z0 | right].
    destruct (SRCB ltac:(lia)) as (p & IN & S1 & S2).
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3. lia.
Qed.

  (* [comment removed for export] *)
  Definition z4s_srcp (m : amem) : Prop := bytes_at bsegs m SS (map (Z_to_bv 8) src).
  Lemma z4s_src : forall m, z4s_srcp m0 -> munch DW m0 m -> z4s_srcp m.
Proof using All.
  intros m H0 MU. unfold z4s_srcp in *.
  destruct (Z.eq_dec n 0) as [Z0 | NZ].
  - pose proof (bytes_at_bound _ _ _ _ H0) as BB. rewrite length_map in BB.
    assert (E : src = []) by (apply length_zero_iff_nil; lia). rewrite E. cbn [map]. apply bytes_at_nil. lia.
  - eapply bytes_at_transport; [exact H0 | exact MU |]. rewrite length_map.
    pose proof z4s_blocks as (_ & _ & _ & _ & _ & [SB | SB]); [lia|].
    pose proof z4s_sp as SPB. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

  (* [comment removed for export] *)
  Lemma z4s_out : forall m, wmono bsegs m0 m ->
    (DST = 0 /\ dcap = 0) \/ (exists buf, u8arr bsegs m DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap).
Proof using All.
  intros m WM. destruct DSTF as [D0 | (pb & IN)]; [left; exact D0 | right].
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH IN) as (_ & _ & _ & _ & _ & WA & _).
  pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (B1 & B2 & _). cbn [ab_addr ab_size] in B1, B2.
  apply (z4_wr_u8arr m DST dcap); [exact (wr_at_transport _ _ _ _ _ WA WM) | lia | exact B1].
Qed.

  Lemma z4s_stk_ext : forall m lo' A cs hi, stk bsegs m lo' A -> rw_cells bsegs m A cs -> lo' <= A ->
    hi = A + Z.of_nat (cells_size cs) -> stk bsegs m lo' hi.
Proof.
  intros m lo' A cs hi ST RW LE ->. eapply stk_merge; [exact ST | exact (stk_of_rw_cells _ _ _ _ RW) | lia].
Qed.

  Lemma z4s_d0 : 0 <= DST /\ DST + dcap <= ATOP /\ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST).
Proof using All.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  destruct DSTF as [[D0 C0] | (pb & IN)]; [lia|].
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH IN) as (_ & (AB & _) & _).
  pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
  unfold ablk, AIMG_HI, KLS in *. lia.
Qed.

  (* [comment removed for export] *)
  Lemma z4s_appW : appW DW.
Proof using All.
  pose proof z4s_d0 as D0. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  apply appW_cons; [| apply appW_cons; [| exact appW_nil]]; unfold KLOW, KHIGH; lia.
Qed.

  Lemma z4s_rclean : forall m, munch DW m0 m -> wmono bsegs m0 m -> rclean m rstk.
Proof using All.
  intros m MU WM. destruct RCL as (SH & LT). split; [| exact LT].
  exact (shclean_transport_app _ _ _ _ _ _ _ SH MU WM z4s_appW LT).
Qed.

  Lemma z4s_blk_unp : forall p A k m, In (HB p A k) LB -> munch DW m0 m -> unpoisoned m A (A + k).
Proof using All.
  intros p A k m IN MU.
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH IN) as (_ & AR & _ & _ & SD & _).
  pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
  unfold ablock_range in AR. destruct AR as (_ & K0 & _ & AM).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI in B1.
  assert (U0 : unpoisoned m0 A (A + k))
    by (apply ablock_unpoisoned; [exact SD | exact (z4_mod16_8 _ AM) | lia | lia | lia]).
  eapply unpoisoned_munch; [exact U0 | exact MU |].
  rewrite z4_shad_span.
  apply appW_shadow_disjoint; [exact z4s_appW | lia | unfold KEND; lia].
Qed.

  (* [comment removed for export] *)
  Lemma z4s_unp : forall m, munch DW m0 m ->
    unpoisoned m DT (DT + DTL) /\ (0 < n -> unpoisoned m SS (SS + n)).
Proof using All.
  intros m MU. split; [exact (z4s_blk_unp _ _ _ m HDT MU)|].
  intros NP. destruct (SRCB NP) as (p & IN & S1 & S2).
  pose proof (z4s_blk_unp _ _ _ m IN MU) as U. replace (SBL + (SBH - SBL)) with SBH in U by lia.
  eapply unpoisoned_sub; [exact U | lia | lia].
Qed.

  (* [comment removed for export] *)
  Lemma z4s_aheap : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
Proof using All.
  intros mm MU WM. pose proof (AI_layout AI L RNG st LB m0 AH) as HL. unfold HUF_DEC_STACK_A in LOS.
  destruct DSTF as [[D0 C0] | (pb & HDB)].
  - eapply (AI_frame AI _ _ _ _ _ _ [(lo, SP)]); [exact AH | | exact WM |].
    + eapply munch_weaken; [| exact MU]. intros x. cbn [outside]. intros [X1 _]. split; [exact X1 | split; [lia | exact I]].
    + apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold aclient_range, aclient_app_range. left. left. lia.
  - eapply (AI_frame AI); [exact AH | exact MU | exact WM |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
    + left. left. lia.
    + right. left. exists (HB pb DST dcap). split; [exact HDB|]. cbn. lia.
Qed.

  Lemma z4s_magree : forall mm, munch DW m0 mm -> wmono bsegs m0 mm ->
    magree bsegs (fun a => aclient_addr CI LB SP a /\ ~ (DST <= a < DST + dcap)) m0 mm.
Proof using All.
  intros mm MU WM. apply (munch_magreeA DW m0 mm); [exact MU | exact WM |].
  intros a [CA ND]. cbn [outside]. split; [| split; [exact ND | exact I]].
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  destruct CA as [S | [R | [B | (a' & A' & E)]]].
  - lia.
  - destruct R as (iv & IN & R1 & R2). pose proof (AI_aci_img AI iv IN) as HI. unfold ABase.AIMG_HI in HI. lia.
  - destruct B as (b & IN & B1 & B2). pose proof (AI_block_bounds AI _ _ _ _ _ b AH IN) as (BB1 & BB2 & BB3).
    unfold ABase.AIMG_HI in BB1. lia.
  - subst a. unfold shad, ASHOFF. rewrite ?Z.shiftr_div_pow2 by lia.
    assert (A'B : 0 <= a' < 2^47).
    { destruct A' as [A1 | [(iv & IN & R1 & R2) | (cls & A & k & IN & F1 & F2)]].
      - lia.
      - pose proof (AI_aci_img AI iv IN). pose proof (AI_aci_lo AI iv IN). unfold ABase.AIMG_HI in *. lia.
      - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (BB1 & BB2 & BB3). cbn [ab_addr ab_size] in BB1, BB2, BB3.
        unfold ABase.AIMG_HI in *. lia. }
    Z.div_mod_to_equations. lia.
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma z4s_srcblk : 0 < n ->
    (exists p, In (HB p SBL (SBH - SBL)) LB) /\ SBL <= SS /\ SS + n <= SBH /\ SBL mod 8 = 0 /\ 0x60d000 <= SBL /\ SBH <= ATOP
    /\ rng RNG SBL (SBH - SBL) /\ rng RNG (shad SBL) (shlen (SBH - SBL + 7)) /\ ablk SBL SBH.
Proof using All.
  intros NP. destruct (SRCB NP) as (p & IN & S1 & S2).
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH IN) as (_ & AR & R1 & R2 & _).
  pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
  unfold ablock_range in AR. destruct AR as (AB & _ & _ & AM).
  replace (SBL + (SBH - SBL)) with SBH in AB by lia. unfold AIMG_HI in B1.
  split; [exists p; exact IN|]. split; [exact S1|]. split; [exact S2|]. split; [exact (z4_mod16_8 _ AM)|].
  split; [lia|]. split; [lia|]. split; [exact R1|]. split; [exact R2|]. exact AB.
Qed.

  Lemma z4s_unpS : forall m, munch DW m0 m -> 0 < n -> unpoisoned m SBL SBH.
Proof using All.
  intros m MU NP. destruct (SRCB NP) as (p & IN & _ & _).
  pose proof (z4s_blk_unp _ _ _ m IN MU) as U. replace (SBL + (SBH - SBL)) with SBH in U by lia. exact U.
Qed.

  (* [comment removed for export] *)
End Z4SB.
End CANSEC1.
