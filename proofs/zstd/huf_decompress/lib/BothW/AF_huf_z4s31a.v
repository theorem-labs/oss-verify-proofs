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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4spa AF_huf_z4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_z4s31a () := "C46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_z4s3_iface4BD4AK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4spa8rwc_consC56Stdlib6ZArith6BinInt1Z3addK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums1Z02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6of_natK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission5BothW6ABytes<rw_cells_appC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z4lxorK47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init5Logic4True00C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb6z4s_spC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_z4s3_iface3SPAC5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_z4s3_iface4Z4SFI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4sb:z4s_blocksC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4s1e9z4s1_dblkC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transI47Corelib5Lists7ListDef6Forall00K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC46Stdlib5Lists4List9nth_errorC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_nilC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromK46Stdlib9micromega5Tauto8GFormula01C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdK46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib6ZArith4Znat5Nat2Z8inj_succc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a6z31_ffC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXK47Corelib4Init5Logic4True01I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4spa9SPA_splitC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4spa9SPA_mergeK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01C56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4s1e:z4s1_factsC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4s1a9z4s1_dctxC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4skx1;z4s_src_ctxC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit39x2_bytes'C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics5Riscv3Sem4core01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a:z31_shift0c5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a7z31_idxc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a9z31_dmoveC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31k8z4s31_L2C56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31k8z4s31_L1C5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31k7z4s31_LC5ARocqVerifyHarness?AgentSubmission6Common7SFModel<mod64_land63C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a8z31_lastC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31k7z4s31_TC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a9z31_tbodyC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib9micromega;ZifyClasses6eq_iffC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_lxorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_land_lc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a7z31_st2c5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a8z31_t36cC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31k8z4s31_D2C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_wordC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31k8z4s31_R2c5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a:z31_land32C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge?zb_shl_shr_landK4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a9z31_land7K47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a9z31_join2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC56Stdlib6ZArith6BinInt1Z:mul_div_lec5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a:z31_land64C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divK47Corelib4Init5Logic2or01K4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a9z31_loop2c5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4s31a8z31_c154".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Lemma z4s1_bd4_split : forall (SP : Z) m (c b p s l : word) jp, rw_cells bsegs m (SP + -256) (BD4A c b jp p s l) ->
  rw_cells bsegs m (SP + -256) [C8 c] /\ rw_cells bsegs m (SP + -248) [C4 b; CB 4 jp] /\ rw_cells bsegs m (SP + -240) [C8 p]
  /\ rw_cells bsegs m (SP + -232) [C8 s; C8 l].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4s31a ()) [] "h01Hh14__x1h21mh32H0h41Ah57__arithh64__ffh78__varmaph85__with91ch:1xh;1zh<2H4h=2csh>3cs1h?3cs2h@4segshA2H1hB2H2hC2H3hD2SPhE1bhF2jphG1lhH1nhI1phJ1shK1yp;1p;6p;4p;2p;3p;5p;<p;7p;Bp-1p10000p4p710R0p8p1000Gp4p70P0p8p1001>p4p7210g001jR0p4p710p8g002Hj1@Tg002mj1YTg003Kj1TTg003nj1vTg004Pj1HTg0050j1JTg005Nj6hTg006Oj1STg006oj4uTg007oR1j20Tg008Lj11Tg009Aj1<Tg009`j1GTg00:Ej2eTg00:cj1dTg00;Aj1cTg00;lj2bTg00<Oj1UTg00<mj2aTg00=Oj2ATg00=ij2`Tg00>Uj3Rj1sTg00>oj3_Tg00?Nj4^Tg00@@R2j1:Tg00@`j1QTP0j6PTg00AUj3\Tg00B2j43Tg00Bhj1DTg00CaR0j2=Tg00D<j5tTg00E:j2ZTg00EQj1rTg00Eoj4pTg00FRl<kTg00G7j2WTg00GZj4jTg00HEj4NTg00H`j3>Tg00I@j1VTg00J4j2XTg00Jij3iTg00KLj4gTg00L7j7fTg00L[lBMTg00MAl<qTf0R3#@#@p=?g00MfR4f3R5f2R6f1R7'0P3C3p=5P4P5P6g00N[R8?>73C3p=7A>873p=2%V3#:p=FP4f6R9f5R:f4R;C3P4P51067P3C3'=p=EA>8739>86p=4%Q51X67=>835>8p=6P4P5%V7#:,06P3C3p=IP4P;1056P7C3/=3p=9g00OPR</W3p=BAi<73p=8P<P7g00OnP3Cgp=LP7g00PUg00Q4R=P=g00QTR=P3g00R4Ffp=K1067/03p=CAR<73p=;1X67=>83p=]%:3,07p=OP4P6P7P3C3p=[g00RTR>P>P>P<P<P<g00S3R?P2P2P2P1g00SSR@P5P6P7g00T6RAg00TURBP3MBMp=oP>P>P>P<P<P<P?P2P2P2P1P@P:P;P5P6P7P3MBMp=nP>P<P<P<P2P2P:P;P5P6P7P3M<qp=mP<P<P<P<P<P<P1P3P7P6P1P5P;P:P9f7R1f8R2f9R@MBMp=lg00U3R?#?RC#@RD#@#?RE#Y#TRF%YD#TRG#v[RH%HGP9P1%?E#JREP:P;P3P5P6P7EhC5%H8RGP0P5P6P7P3C7P;P5%S8RI,26P;P5%F6P7FE[RJP5P6127IP5P6%F7P3FEP;P5P6P7C7RK[P:P;125IP:P;%F5P6FE\KP5P6P7P3CuP7n2001000000120000000W=X98X4<X2HRKPJ^=G^98^4<^2HRJP3P210@ERL%11RMP9%<A#<#<#<RNP6%1:RO%1;RP%15/2I34C6RQP7O5P2PL12MIRRP2PL%FMPQFEP0P@f:RQ/0ERM%12RLPIC7P@PMPLP1PNP5%19R112PI74OC6CIPQf;RPPE%1@RM/2IRSPQPP%G?#GRT#GRU#G#@#?#JRVP2PNP;PIC6PQPP%?U#?#JRUPRPQPP%@T#G#@#?#JRTA41OIC5D9D9D9P3PPf<R1PE%1QRO/2IRWC5P1f=RX/0E%1PRYPQPNP9A4MLRC6CIg00UXRM#SRL%HMRM1e<7RR%d<RZ%c<R[1b<?R?%BV'8R\%BE,8?%UDRD#BR]'8'L'K1a[=R=P3P6g00VDR^g00VdR_'A1`36=R^_dA_<B7C^R_b6b7b8X1<103VR^AC3ED';^1<P3f?R`O1b5f>Ra/0V%<N#<#<#<#:Rb9CaE';P<AC`EbP`P3%QX%11Rc?4YW9]N@C7X;<P710`VR@P3EPPaP@%Q1A4YOS9]N2C7g00WD#HR2P0P;P5P6A\873C3P:P;P5P6C3P:P;%D6,O5P7C3'=[ROP;P5P6P7C3P;P5%D7,O6P3C3'=P:P;P5A\867C3R8[P9P:P;P5C3P9P:%D5,O;P6C3'=\8P;P5P6P7P3DtP7n2001000000120000000X?GX>GX4<X2HW@PO^?G^>G^4<^2H^@2P3P4f@R4fAR2/0VRHPaPNPQPIC6RQ%1XRG12YI74cRYP7O6P4PHPQP4PH%DQ#:PYFEP0fBRY/0VRQP`PNPPPIC6RH5[2P2PQ%DH#:%1aRH12cI74GC5PYfCRcPE%12RQ/2IROPYPcPVP4PNP1PIC6PYPcPU%1`/2IR`PYPcPTA4HGIC5D9D9D9P3PcfDRHPVP2PNPXPIC6C5PHfERX/0VPYPNPaPIC6#D#:%14=4Q`C5fFR`/0URQ10`VR41ZNARA,ZNRa#:R2'0RG';R1%UCRC10CBR6'0R;,04R8,;QP<P<%s<R:P3X:<R9P:1;73#rXK<X:<PQPQ1A<QPGP8P9P9P9P<P<g00XC1073Cp,A<X2<XH<P4P41A<4P2P;P9P9%:3,A<X:>PaP;PNPC1A<CRaPAP6PNPCPa1A<BCoEnEmM:lM<kPLPMPRPZ%BU,8?Ra%BCRC1W<B,8C'8,8\'L,K[P=P_b6b7b8X1<103UR\10^;';^1<P3fGR;O1b5CjP1P<AC;V2P;P3%1HR2%1cR1%1YRY;4IC7X;<P710;UR^P3EPP`P^P112YOC7PKPJP3fHRJfIRK/0URY%1XRXA421IR1P7O5PJPY12XIROPJPY%FXP1FEP0PKfJR0/0UR1%1`R`PIC7PKP1P`A4X2ICIP0fKRXPE%1KR2/2IR1P0PXPVPJPNPHPIC6P0PXPU%1;/2IR;P0PXPT12`OC5D9D9D9P3PXfLR`PU%1JRJ/2IC5P`fMRO/0UP212J;CIPLPMPRPZ%BT,8?18a]'L,K[P=P_b6b7b8X1<103T10\D';^1<P3fOR\O1b5fNRD/0TACDUb';P<AC\Ub%1X%10R0;4IRX9[\3X;<P710\TRbP3EPPDPbP0P1C7P\fPR1PE%1D/2IC5P\P1PVPOPNPKPIC6C5RKP\P1PU%1`/2IC5RIP\P1PTPXC5RX'=RT'=PcPKPTPPPIPXP5P3CNCNCNb<b0W<WCP7P3O2n2001000000121000000b0b3b0b3W0WBP7P3O2n2001000000121000000b0b3b0b3W0WAP7P3O2n2001000000121000000b0b3W0WFXGFXJFXIFXEFX9FW2XD<o"). Qed.

Lemma z4s1_bd4_merge : forall (SP : Z) m (c b p s l : word) jp,
  rw_cells bsegs m (SP + -256) [C8 c] -> rw_cells bsegs m (SP + -248) [C4 b; CB 4 jp] -> rw_cells bsegs m (SP + -240) [C8 p] ->
  rw_cells bsegs m (SP + -232) [C8 s; C8 l] -> rw_cells bsegs m (SP + -256) (BD4A c b jp p s l).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4s31a ()) [] "h01Hh14__x1h21mh31Ah47__arithh54__ffh68__varmaph75__with81ch91xh:1zh;2csh<3cs1h=3cs2h>4segsh?2H1h@2H2hA2H3hB2H4hC2SPhD1bhE2jphF1lhG1nhH1phI1shJ1yp;1p;2p;4p;3p;5p;<p;6p;7p;Bg002Hj1<Tg002mj1STg003Kj1PTg003nj1nTg004Pj1ATg0050j1CTg008Lj12Tg006Oj1RTg009`j1?Tg00@`j1ETg009Aj16Tg00J4j2ITg00I@j1BTg00@@R0j11Tg00CaR1j2@Tg006oj4^Tg007oR2j20Tg00:Ej2]Tg00:cj1\Tg00;Aj1[Tg00;lj2ZTg00<Oj1QTg00<mj2YTg00=Oj29Tg00=ij2XTg00>Uj3Oj1lTg00>oj3WTg00?Nj4VTg00AUj3FTg00B2j44Tg00Bhj1NTg00D<j5mTg00E:j2UTg00EQj1kTg00Eoj4iTg00FRl<cTg00G7j2TTg00GZj4bTg00Xgj6KTg00HEj4LTg005Nj6aTg00H`j3DTg00Jij3`Tg00KLj4_Tg00L7j7gTg00L[lBMTg00MAl<jTf0R3#<#<p=:g00N[R4f1R5;D3p=;g00MfR6f3R7f2R8/05P3C4p=3AD4539D48p=>P6P7P8AD453C4p=7P6P8P5P3C4p=Jg00OPR9/T3p==A`953p=5P9P5g00OnP3C_p=HP5g00PUg00Q4R:P:g00QTR:P3g00R4Fgp=GAO953p=8g00RTR;P;P;P9P9P9g00S3R<P0P0P0P2g00SSR=P7P8P5g00T6R>g00TUR?P3MBMp=hP;P;P;P9P9P9P<P0P0P0P2P=f5R=f4R<P7P8P5P3MBMp=fP;P9P9P9P0P0P=P<P7P8P5P3M<jp=eP9P9P9P9P9P9P2P3P5P8P2P7P<P=f6R2f7R0f8R@f9RAMBMp=dg00U3RB#:RC#<RD#<#:RE#S#PRF%SD#PRG#n[RH%AGP2P0%:E#CRE%2=RG%R4RI';RJC3P0P@%?B#?RK#?RL#?#<#:#CRM%E=%6>#6#6#6RN/I5;>IC3P@PA%:L#:#CRLPJC3PAf:RJ%<K#?#<#:#CRK%2<=>GIC3%A4RGP1P7P8P5P3C7P<P7P8PIC7P<P7%B8#1P5C3'@RO[P7P8P5PIC7P7P8%B5#1P3C3'@P<P7P8P5C7[RPP=P<P7P8C7\OP7P8P5P3C^P3n2001000000120000000W;X84X39X2HROPP^;G^84^39^2HRPP3f;RQf<RR/0ERS%2JRT%EA1IN=%2@RU%20%22/;I3>3>RV1;TIRW9JQSPQPS%BT#1PVC3RVP<g00UXRX#RRY%AXRX1]95RZ%\9R[%[9R\1Z9BRB%=M'5R]%=E,5B%QDRD#=R^'5'H'G1Y\:R:P3P8g00VDR_g00VdR`'91X38=O_`dAW9?5CVR`b5b6b7X19103MR_103E/0D'8^19P3f=RaO1b410RM%6N#6#6#6#1Rb,0S'8P910aMPaP3%EQRS1IN0Rc%2A1;UI5>TRT';C7X:9g00WD#ARUP1P<P7P8AF453C4P=P<P7P8C4P=P<%N8#1,07P5C4'@R1[P<P7P8P5C4P<P7%N5#1,08P3C4'@P=P<P7AF485C4[RdP2P=P<AF478C4\1P<P7P8P5P3DmP3n2001000000120000000X=GX<GX39X2HW>Pd^=G^<G^39^2H^>UP3P6Paf>R6/0MRUA>ScIRcPTAJaUcPaPU%Nc#1PTC3RTP=106LR61UN>R>,UNRc#1RS,0URH'8RG%QCRC10C?Rd'0R8,0UR7,86P9P9%l9R1P3X99R4P11853#kXJ9X99P6P61996PHP7P4P4P4P9P9g00XC1053Ci,99X29XG9PUPU199UPSP8P4P4%13,99X9;PcP8PNPC199CRcP>PdPNPCPc199?ChEfEeM:dM<cPYPXPZP[%=L,5BRc%=CRC1T9?,5C'5,5]'H,G\P:P`b5b6b7X19103LR]10_8'8^19P3f?R8O1b4CbPGP9108LP8P3%2RRR%2Q/;WRWC7X:9POPPP3P8f@RP/0LROPRPW1;RIRI9J8OP8PO%BR#1PWC3RWP2PYPXPZP[%=K,5B15c^'H,G\P:P`b5b6b7X19103K10]D'8^19P3fAR]O1b410PK10Ob'8P910]KP]P3%2aPIC7X:9P210]L/0bP3EKb0PWeCLO5b0108M/0SP3EKb0PTeCLO6b010aE/0bP3EKb0PVeCLO5b0PJPQPEPAP@P<P0P2P=EaC3eWBWAW@W?WEXFFXIFXHFXDFX8FW2XC9o"). Qed.


(* [comment removed for export] *)
Lemma z31_shift : forall tl mtl, 1 <= tl <= 12 -> 1 <= mtl <= 12 ->
  Z.land (Z.land (bv_swrap 32 (0 - Z.land (tl + 256 * mtl) 18446744073709551615)) 18446744073709551615) 63 = 64 - tl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4s31a ()) [] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61zh71Hh82H0h92H5h:4__x3h;4__x4h<4__x5h=4__x6h>2H1h?2H2h@2H3hA2H4hB2H6hC2H7hD2H8hE1MhF1ThG3mtlhH1qhI2q0hJ1rhK2r0hL2tlp&0p;1p;2p;3p;4p;6p;7p;8g00<Oj18Tg00YCj2BTg009`j13Tg002Hj11Tg00Caj29Tg00Y_j2fTg00Z<j20Tg00Z\j2DTg007oj26Tg00[9j2^Tg009Aj1ETg00[bj3[Tg00\Kj2pTg00]4j2QTg006Ok100Tg004Pj1}Tg00:Ej2RTg00]`j1|Tg00^>j4PTg00:cj1zTg00;Aj1xTg00;lj2FTg00^\j1tTg00G7j2`Tg00_>j3NTg00Jij3KTg002mj1_Tg00_aj3sTg00<mk208Tg00=Oj2]Tg00=ik207Tg00>Uj3\Tg00>ok306Tg00?Nk405Tg00`Dj24Tg00``j3rTg00aCk403Tg00a_j1oTg00b=j2@Tg00b[j3YTg001jj6OTg00c>j27Tg00c[j2lTg00dBj2iTg00dej3WTg00eHj1MTg00eej2hTg00fFj1gTg00f_j2HTg00g<j2eTg00gcj2aTg00hJj2bTg00i0j2dTg00iVj2cTg0050j1{Tg00j7j2yTg00jXj3TTg00kAj2qTg00Xgj6mTg00kmj3kTg00H`j3wTg00KLj4XTg00L7j7nTg00lVj7vTg00m:j8uTg00m^k604Tf0R0#1#1p=Zf2R1f1R2/D0'6p=Vg00OPR3?\20p=21p30p=CAk3209k31p=?g00UXR4?w20p=J1`30p==P1g00PUR5g00Q4R6P6g00QTR7P3P2g00nBP0CXg00R4R8Fnp=;P1P5P6P6P7P2P0Fvp=LP3P2g00niP0CXp=UP2P5P6P6P7P0P8Fnp=<f3R8P5P6P6P7P1P2P0Gup=:g00TUR9/B0p=>%30#3#3#3p>02%30#3p>01%30#3#3#3#3#3#3#3p=A%10#1#1#1p=~%10#1#1#1#1#1#1#1p=IP3P2g00OnP0CXp=GA\309p=S1D20,61#Mp=5P2P5P6P6P7P0J04p=jg00U3R5#8R:/B2%35R;#1R<#1#8R=,B2'9R>P3%15R?#1R@#1#ZRA#1RB#ZRC#8RD=V81RE%8?RF%8BRG'fRH'0RIf4RJ1DD8RK'6RL/20X63P3PIPE1^3DRIg00T6RM#ERN#ERO#ERP#ERQ#CRR5[3%CORO1p3MRM3?g00oPRS'QRT%CPRP9[3I%CN;?M/QSRN&004RI'J'J%}4R4P31R31P2%|3RUCPRV%z3RW%x3RX%=:RY1F3?RZ5;X%==R[9;XZ5LXR\%t6R6PX1F35R]9;XYA;X][5LXR[P61`39RY%=DR^=N3Z9K3]R_5;X%=F%_B5s3,U_,<X5LXC:C:208X7R7P0P1g00VDRBg00VdR`']20701=\B`dB06392H05R`b3b4b5X03X13161KRK#>14KH'9\>\>^03^13P0P8PJP2P1O4b29rEHH03%oGRB,@EPIP4PUPW%=GRa9;XYP7P`b3b4b5%>GP0b2Rb9YEGEO&02;Rc$01#A#A#A#A#A#A#A#8Rd,@E,2EP3PL%_ARA1790'l/@d%8c'@f5Rc,7GRE'2X63P3179LRe,lARA/@BRB%8<Rf,fFRF'0120EX63P310AHRg100F/2EX63P3%1C#Z#~#I#IRC#8Rh,6eRe170h/0H/0F/2EX63PIP4PVPW1i3_AW3Y_%=hR_5K3Ri=W3_'G,<XP7P`b3b4b5X03X13AV0D2R_#M179_/6h/7h'2^03^13P0PJPcO2b2%ML17eh'2P3AVcDJR_#MRj100H/0Ff6RH,7G'2X63%1CRC#I#I#I#I#8Rk,0j/hG%SGRj#gA5HDc/0kRl1HlG,DG10lG'6'2[1elG149GRlf7Rm?5DH/0kRn/0GRo#>14oG'9[1anG14G9f8Rn?5Dm/0kRo/0GRp,4G1Bp9'9[1boGf9Ro?5Dn/0kRp/HG#S\j1dpGf:Rp?5Do/0kRq/0G/2q\j1HqGP3f;Rq?5Dp/0k/0GP3f<Rr?5Dq/hk%SkRs#gf=Rt?5DrRr1Hrk,Dk10rk'6'2[1erk149kRrf>Ru?5DtRv/0kRw#>14wk'9[1avk14k9f?Rv?5DuRu/0kRw,4k1Bw9'9[1bukf@Ru?5DvRv/Hk#S\s1dvkfARv?5DuRw/0k/2w\s1HwkP3fB?5Dv/0kP3Pcg010<Rv1c9k']PreO1%>0140k'9Pt1c9G,]vPleO1%>n14nG'9%EQRQ#ERn#CRl??PM1^3G=[3MRv%{5,y3R5%En#CRn5T3AT35R=?lP3?/QS'qAT35lAT35P;?M%CQ??RO9?vn/QS'q/JI'JP4P3P31R3JP11R3HCPP2P31R3cP8PUCPCPPWPXPX%=kRS/GY,<X,jXP61F3;9N3^9K3Z,i31F3<9N3S1F3@R@5K3'G,<XC:P6PXA;XY]1U]a,<X5LXP6PXPX1GaY,<X,jXP6%3?,F39N3a=K3],G@,<XC:P6PXP\P6AW3aZ,G],<XC:C:C:C:P7P`b3b4b5X03X13X:3X;3X<3X=3g010bR]\s%MK1DkH/6J'2[%>2142G'9P]\j1DGm/68,2H[1B:J1BJ='912JE[[[[^03^13^:3^;3^<3^=3P0PJPqP8fEfFPpPoP2PufDO:b2b8b9bKbIbDbCbBb9bAbJbHb@b?b>b8b7179_/6h/7hP0Emb7%8CRC,0e1JTI,JNP4PVPWPXP\P6PXP[P6A;XYi%=C,Ui,<X5LXC:C:P7P`b3b4b5X03X13179K/6hRh#>14hC'9\>\>^03^13P0PJPcP1P8O4b29reCEO10gF17GJ'2ePBAYAGbEO%of,@BPIP4PUPW%=f9;XYP7P`b3b4b5%>fP0b29YBfEO1@LdP0Emb7XE>WFXG3XL3o"). Qed.

Lemma z31_shift0 : forall tl mtl, 1 <= tl <= 12 -> 1 <= mtl <= 12 ->
  Z.land (Z.land (bv_swrap 32 (0 - (tl + 256 * mtl))) 18446744073709551615) 63 = 64 - tl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4s31a ()) [] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61zh71Hh82H0h92H5h:4__x3h;4__x4h<4__x5h=4__x6h>2H1h?2H2h@2H3hA2H4hB2H6hC2H7hD2H8hE1MhF1ThG3mtlhH1qhI2q0hJ1rhK2r0hL2tlp&0p;1p;2p;4p;3p;6p;7p;8g00<Oj18Tg00YCj2ATg009`j1_Tg002Hj11Tg00Caj27Tg002mj1~Tg00c>j26Tg00c[j2qTg00a_j1ZTg00b=j2YTg00Y_j2XTg00Z<j20Tg007oj24Tg006Ok100Tg004Pj1}Tg00:Ej2PTg00]`j1yTg00^>j4NTg00:cj1wTg00;Aj1tTg00;lj2ETg00_>j3LTg00Jij3GTg00dBj2\Tg00G7j2[Tg00dej3TTg00<mj2pTg00=Oj2STg00=ij2oTg00>Uj3RTg00>oj3nTg00?Nj4mTg00eHj1HTg00Z\j2?Tg00eej2lTg00fFj1kTg00f_j2DTg00g<j2jTg00`Dj25Tg00gcj2iTg00hJj2hTg00i0j2gTg00iVj2fTg009Aj1@Tg00\Kj2eTg00[9j2dTg00[bj3VTg0050j1|Tg00j7j2zTg00jXj3JTg00]4j2OTg00kAj2aTg00H`j3ITg00^\j1xTg00KLj4KTg00Xgj6vTg00``j3uTg001jj6WTg00b[j3cTg00L7j7]Tg00kmj3bTg00m^j6sTg00m:j8rTg00lVj7{Tf0R0#1#1p=Uf2R1f1R2/?0'4p=`g00OPR3?R20p=2%10#1#1#1p>01%10#1#1#1#1#1#1#1p=F1[30p==P3P2g00OnP0CKp=CP2g00PUR4g00Q4R5P5g00QTR6P0g00R4R7F]p=>g00TUR89R30p=Q1?20,41#Hp=31A80p=;1e30p=BAb3209b31p=9P2P4P5P5P6P0Esp=^f3R9P4P5P5P6P1P2P0Grp=<P1P4P5P5P6P3P2g00nBP0CKP7F]p=:P1P4P5P5P6P2P0F{p=Mg00U3R4#8R7/A2%_4R:#1R;#1#8R<,A2'7R=P3%14R>#1R?#1#UR@#~%1@R@#URA#8RB=`91RC,68RD'qRE%8@R@#Z'YRF%8>RG%8;RH'XRI'0f4RJ,6@RK,20X63P31XG@RG,0ERL100I/2KX63P3%1A#U$01#F#FRA#8RM,4DRD160M/0G/0I/2KX63g00UXRK$00RN%}KROP31P31P2%y3RPCNRQ%w3RR%t3RS1E34RT%=BRU1E3>RV5L35G3RW,\31[38RX=T3W%=MRW5G3RY=T3W'C'>1pS6R6P0P1g00VDRWg00VdRZ'S1o01=RWZdAn382CmRZb3b4b5X03X13A`0B2RW#H168W/4M/6M'2^03^13P0P9PJO2b2%HC16DM'2P31?B9RC,4JRW#HR[100G/0If5RG,6@R\'2X63%1ARA#F#F#F#F#8R],0[/l@%Q@R[#kA3GBJ/0]R^1D^@,?@10^@'4'2[1j^@158@R^f6R_?3BG/0]R`/0@Ra#;15a@'7[1i`@15@8f7R`?3B_/0]Ra/0@Rb,5@1Ab8'7[1ha@f8Ra?3B`/0]Rb/D@#Q\[1gb@f9Rb?3Ba/0]Rc/0@/2c\[1Dc@P3f:Rc?3Bb/0]/0@P3f;Rd?3Bc/l]%Q]Re#kf<Rf?3BdRg1Dg],?]10g]'4'2[1jg]158]Rgf=Rh?3BfRf/0]Ri#;15i]'7[1if]15]8f>Rf?3BhRi/0]Rj,5]1Aj8'7[1hi]f?Ri?3BfRf/D]#Q\e1gf]f@Rf?3BiRi/0]/2i\e1Di]P3fA?3Bf/0]P3PGg010<Ri1f8]'SPgeO1%;0150]'7Ph1f8@,SiP^eO1%;a15a@'7g00T6Ra#@R^#@Ri#@Rh#@Rg#@Rj#@Rk#BRl%BhRh1e3aRa391d3@=V3aRm%|4,z3R4%@k#BRk5J3%BgRg9J34=9lh39g00oPRn'O'aAJ34lAJ34h;9a%Bj%BiRi79g99mk/On'a=IKN5IKPOP3P31P3JP11P3_CNP2P31P3GP9PPCNCNPRPSPS%=]RG/CX,>S,^S%x5R51E3:9L3U9G3V,\31E3;9L3G1E3?R?5G3'C,>SC<P5PSA:SXTP3PTg00niRG%=@R;CK,>S5MSP5PSPS1C;X,>S,^SP5%_>,E39L3;=G3T,C?,>SC<P5PS%=7R?=:SV%=<R>9:SV5MSRUP5AT3;V,CT,>SC<C<C<C<P6PZb3b4b5X03X13X:3X;3X<3X=3g010bRV\e141CRC#H1?]_/4J'2[%;2152@'7PV\[1?@`/49,2_[1A7J1AJ<'712J\[[[[^03^13^:3^;3^<3^=3P0PJPdP9fDfEPcPbP2PffCO:b2b8b9bKbIbDbCbBb9bAbJbHb@b?b>b8b7168W/4M/6MP0Evb7%8ARA,0D1d3BRB=V3h%B^;9a/OnAV3Bg?9ia/On=IKN5IKPOPQPRPSPUP5PSA:S?TA:ST>5MSP5A:SXYP3PYPG%=ACK,>S5MSC<C<P6PZb3b4b5X03X13168C/4MRM#;15MA'7\=\=^03^13P0P9PJP2P1O4b29uDAEW10LI16@9'2ePFPNPOPPPRA:SX;P6PZb3b4b5%;@P0b29cE@EW%ZH,YFPNPOPPPR%=H9:SXP6PZb3b4b5%;HP0b29cFHEWXE=WFXG3XL3o"). Qed.

Lemma z31_land32 : forall x, 0 <= x < 2^32 -> Z.land x 4294967295 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4s31a ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h52Hxh61xh71zp;2p;1p;3p;4p;7p;8p;6g00YCj21Tg002Hj10Tg00<Oj15Tg00Y_j2<Tg00`Dj28Tg00Caj27Tg00Z<j2DTg00>Uj36Tg006Oj1>Tg004Pj1=Tg00:Ej2;Tg00:cj1:Tg00;Aj19Tg00G7j24Tg00;lj2QTg00KLj43Tg002mj1PTg00_aj3OTg00lVj7CTg00^\j1BTg00m:j8ATg00<mj2@Tg00=Oj2?Tg00=ij2ETg00>oj3FTg00?Nj4GTg00``j3HTg00a_j1ITg00b=j2JTg00]`j1KTg00b[j3LTg001jj6MTg00L7j7NTf1R0g00PUR1g00Q4R2P2g00QTR3f0R4g00R4FNp=2g00OPR5g00TUR6/14g00U3R7#0R8#5R9%08#0#0#0R8#5R:'<R;,84'7R<P51D0;f2R=9654X75g00UXR>#>R?%=>R>1;50%:5R@%95RAP1P2P2P3PAP1P2P2P3P51456R1g00nBRB1Q57R7C3,2AP5P7g00ni1459%P85O5C3,2AFCR8%B2P8GA1@A3R3P4P=g00VDR8g00VdR2'?1E4==682dAF560CGR2b1b2b3X451160180;'7\<^45P4P=P0O2b09H0;%I:,J0P?P>%K5P@P5P1PB145:C3,2AP3P2b1b2b3116:P4b09L0:EMW5W6o"). Qed.
Lemma z31_st2 : forall (b : bool) flag, flag = 0 \/ flag = 1 ->
  Z.land (Z.lxor (Z.b2z b) 18446744073709551615) flag = if b then 0 else flag.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4s31a ()) [] "p'0h01Hh14flagh21bi001bp;1p;2p;6p;3g00<Oj19Tg011?R0j2;Tg011Yj17Tg009`j10Tg0126j26Tg00b=j24Tg00=Oj28Tg001jj65Tg00>Uj3:Tg00OPR1f0R2g00TUR33:p=3f1R4=:12p=2%02#0p==%02#0#0#0p=<%02#0#0#0#0#0#0#0p=1g00VDR5P5%32g00U3R6#9R7,22';R8f2R9#7%06#=#<#1#1#1#1#1#1#1#9R6'6/44P5P1P9P3P4n0110000020000'2[^11P2P0%34R51247R4g00Vd#7/66R:/49#3P2%39R;P1P314:2#3X11R:1813R<f3R=P2E5W0P2O11297R>P1P7P:P<P=P2E5W0P2O1n200100000021000010000X08X11P0P5P4g012T#7/66R6/49/29P2P1P31462/22X11R6P<P=P2E5X0;P2O1P1P7P61817P=P2E5X0>P2O1n200100000021000010000X08X11n0110000020101W2o"). Qed.
Lemma z31_land64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4s31a ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h52Hxh61xh71zp;2p;1p;3p;4p;7p;8p;6g00YCj21Tg002Hj10Tg00<Oj15Tg00Y_j2<Tg00`Dj28Tg00Caj27Tg00Z<j2DTg00>Uj36Tg006Oj1>Tg004Pj1=Tg00:Ej2;Tg00:cj1:Tg00;Aj19Tg00G7j24Tg00;lj2QTg00KLj43Tg002mj1PTg00_aj3OTg00lVj7CTg00^\j1BTg00m:j8ATg00<mj2@Tg00=Oj2?Tg00=ij2ETg00>oj3FTg00?Nj4GTg00``j3HTg00a_j1ITg00b=j2JTg00]`j1KTg00b[j3LTg001jj6MTg00L7j7NTf1R0g00PUR1g00Q4R2P2g00QTR3f0R4g00R4FNp=2g00OPR5g00TUR6/14g00U3R7#0R8#5R9%08#0#0#0#0R8#5R:'<R;,84'7R<P51D0;f2R=9654X75g00UXR>#>R?%=>R>1;50%:5R@%95RAP1P2P2P3PAP1P2P2P3P51456R1g00nBRB1Q57R7C3,2AP5P7g00ni1459%P85O5C3,2AFCR8%B2P8GA1@A3R3P4P=g00VDR8g00VdR2'?1E4==682dAF560CGR2b1b2b3X451160180;'7\<^45P4P=P0O2b09H0;%I:,J0P?P>%K5P@P5P1PB145:C3,2AP3P2b1b2b3116:P4b09L0:EMW5W6o"). Qed.
Lemma z31_land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4s31a ()) [] "h02Hxh17__arithh24__ffh38__varmaph45__with51xh61zp;2p;1p;3p;4p;7p;6g00YCj26Tg002Hj12Tg00<Oj11Tg009`j17Tg00Y_j2GTg00Z<j20Tg00>Uj33Tg00=Oj24Tg00a_j1<Tg00b=j2;Tg006Oj18Tg004Pj19Tg00]`j1:Tg00:cj1FTg00;Aj1ETg00G7j25Tg00KLj4DTg00L7j7CTg00<mj2BTg00=ij2?Tg00>oj3@Tg00?Nj4ATg00b[j3>Tg001jj6=Tg00OPR0g00TUR1f0R2'6P0f1R3g00U3R4#2R5#1%74#1R4'G'0f2R6%25#2#1R5'09302X601035,40%<4,;3g00UXR5#8%95%:0%F0%E0R5g00PUg00Q4R7P7g00QTR7P01501g00nB1504CDg00R4FC1B57P2P6g00VDR7g00VdR5'41?26=375dA@013CAb2b3b41614P2b19>34E=W0W5o"). Qed.

(* [comment removed for export] *)
Lemma z31_idx : forall x tl, 1 <= tl <= 63 -> 0 <= Z.shiftr (Z.land x 18446744073709551615) (64 - tl) < 2^tl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4s31a ()) [] "h04__x1h14__p1h27__arithh34__ffh48__varmaph55__with62Hah71zh86__sat2h96__sat4h:4__x2h;1Bh<1Hh=1Th>6__sat0h?6__sat1h@6__sat3hA2tlhB1xp;1p;2p;3p;4p;6p;5p;7p;8g00<Oj1?Tg00YCj26Tg009`j1;Tg00Caj25Tg002Hj1:Tg00Y_j23Tg00Z<j2>Tg00c>j24Tg0134j2ITg00`Dj22Tg00f_j2ETg006Oj1OTg004Pj1lTg00]`j1iTg00:cj1`Tg00;Aj1\Tg00G7j2<Tg002mj1YTg00_aj3XTg00<mj2VTg00=Oj2KTg00=ij2UTg00>Uj3@Tg00>oj3STg00?Nj4RTg00g<j3QTg00:Ej2GTg00;lj2FTg00^\j1PTg013Tj2HTg014<j3JTg014`j2TTg00iVj2kTg00^>j4jTg00dej3NTg015Qj4hTg007oj2BTg00Jij3eTg00KLj4CTg00Xgj6LTg00Z\j2_Tg0162j5[Tg016Uj5]Tg00HEj4^Tg017Aj3ZTg001jj6MTg00a_j1aTg00b=j2bTg00b[j3cTg00L7j7dTg017jj6WTg00lVj7fTg00m:j8gTg00TUR0f0R1'6p=0g00OPR2f1R3g00niP1CCp=AP3g00PUR4g00Q4R5P5g00QTR6P1g00R4Fdp=11201p=9P2P3g00nBP1CCp=7P3P4P5P5P6P1EWp=Df2R7P4P5P5P6P3P1Ffp==f3R8P4P5P5P6P7P3P1Ggp=8g00U3R4#?R9/61R:%;4#;#;#;#;#?R;,61R<'5P2%:4R=#?R>%:=#:#:#:#:R?#?R@'3RA,>7RB14@7RC,I1RD#013>7RE,2D'5X72P214@3RD,3>,EB%01RF121E'5X72g00UXRG#ORH%lGRG%i2RI%`2RJ%\2RK1<20RL1<2>%Y?5X2R?'A'11VK6R6P1P7g00VDRMg00VdRN'K1U17=@MNdAS203CRRNb3b4b5%9ARMP1b29Q7A%0B12BA'51>8ARO13>CRP'ERQ#012QEPOPPp-0RQPHPG1G23RRPJPK1F24R4,7L,1KRS1DK8RT5=K%P5R5PSC8P6PNb3b4b5X02W115F3%03RF[^02^1QP1f4RU/>ARV/2APVP3O3b21H>C%9>RW14@8RX#014@U,3>#9[[%0>RYg018NRZf5R[,4@R\=J>3UW613>\#0\Z^6Y1H>@%0@R\PM[RM\WAJ>@3VZX6Y%0AR]\Z^6Yf7RY/TA%0Yf9RY/>A#0\][P7g010<1k0>'KPWeRWO1PMP[PWO1f8,4@#014@Y,3>#9[PHPGP21G27P3PICjPJPKPK1<2@RW1F2=R=5N2,7L,1KP51AL4,1KRMC8P5PK1DKU1<2;RU,7=,1K5=KP5PMC8C8P6PNb3b4b5X02X:2X1Q%0DRM%93[167;,58%97[[^02^:2^1QP1f:R=,69P=14@=,3>P3PYO5b2b9b8b>b?b8b@b9RYChPOPPPEPYP21BC7RY,3>12V1X72PHPGPRPJP2PWg00OnAN2W4RV=e24CC,1KP6PNb3b4b5X0214@1/B19@2@^02P1P8O1b2A@2@YP2P@1>[AR[13>1'2X72PHPGPRPJPK1A4?,1KR?9=KTP5P?C8P6PNb3b4b5X02X1Q121A,53123A[^02^1QP1%0[P[P7O3b21BX8P1ELb<1_PEP>PCP7PHPGPRPJPK174U,1K9=KTP517LV,1KC8P6PNb3b4b5X02X1QRV153<PM[^02^1QRMP11698P8P7O3b2PHPGPRPJPK1<29/74,1K==KTP5PSC8P6PNb3b4b5X02X1Q15:3PF[^02^1QP1168;P8P7O3b2D[ELD]C^b;1IBDPVPMP11697P7P3O3b29ZBDEM%a@,b7PHPGPIPJ17LW,1KP6PNb3b4b5P\P1b29c7@EMW=XA2XB2o"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi.
Import KXS.
Local Notation amem := (word -> option byte).

Lemma z4s31_J2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 c p s l : word) (jp : list byte)
    (SP DST dcap DT q Qe b tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap -> 0 <= b < 2^31 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (Qe - q < 2 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (- q + Qe)) (Z_to_bv 64 2) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
            x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 0x90cb4) fc None mm (seg_rom bsegs))) ->
  (2 <= Qe - q -> b <= 64 -> forall z10 : word,
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 z10 (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
            x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 0x90a40) fc None mm (seg_rom bsegs))) ->
  (2 <= Qe - q -> 64 < b -> forall z10 : word,
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 z10 (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
            x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 0x90ca4) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
           x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
           (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 c p s l jp SP DST dcap DT q Qe b tl mtl
    SPL BD2 MI RS HD HDE HDC HQ HQE HB HTL HMT HDT HSP K1 K2 K3.
  unfold AZ4_SB in *.
  destruct (Z_lt_ge_dec (Qe - q) 2) as [C1|C1]; [|destruct (Z_le_gt_dec b 64) as [C2|C2]].
  3: kx_runFmd [0x90a40; 0x90cb4; 0x90ca4; 0x8fbec] 40%nat [false; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 0 (2^31 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -280) 8 (DT + 4);
     KZWord (SP + -136) 4 b; KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [0x90a40; 0x90cb4; 0x90ca4; 0x8fbec] 40%nat [false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 0 (2^31 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -280) 8 (DT + 4);
     KZWord (SP + -136) 4 b; KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x90a40; 0x90cb4; 0x90ca4; 0x8fbec] 40%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 0 (2^31 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -280) 8 (DT + 4);
     KZWord (SP + -136) 4 b; KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brdl.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: z4_m64.
  3: (eapply K3; lia).
  2: z4_m64.
  2: (eapply K2; lia).
  1: (apply K1; lia).
Qed.

Lemma z4s31_R2A : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt + 8 <= L -> 0 <= qb <= 8 -> qb <= pt -> 8 * qb <= b <= 8 * qb + 7 -> SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * qb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - qb)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z17 x6 x7 x8 x9 (Z_to_bv 64 1) z11 x12 z12 z13 z14 z15 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90b70) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           x12 (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x15 (Z_to_bv 64 qb) x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x90a58) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPL HQB HPQ HBQ HSS KA.
  unfold AZ4_SB in *.
  assert (HP2 : exists p2, pt = p2 + qb /\ 0 <= p2 <= 7) by (exists (pt - qb); lia).
  destruct HP2 as (p2 & -> & HP2). rewrite Z.add_simpl_r in KA.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x90b70] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange p2 0 7; KZRange qb 0 8; KZRange (p2 + qb) 1 7; KZRange b 0 64; KZRange (b - 8 * qb) 0 7;
     KZRange (L - p2) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + (p2 + qb)); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWord (SP + -312) 8 (DST + Qe); KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * qb) with (b - 8 * qb) in * by lia.
  all: try rewrite (Z.add_assoc _ O p2) in *.
  all: (eapply KA; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s31_R2B : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt < qb <= 8 -> pt + 8 <= L -> 8 * qb <= b <= 8 * qb + 7 -> b <= 64 ->
  SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z17 x6 x7 x8 x9 (Z_to_bv 64 0) z11 x12 z12 z13 z14 z15 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90b70) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           x12 (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x15 (Z_to_bv 64 qb) x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x90a58) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPQ HPL HBQ HB6 HSS KB.
  unfold AZ4_SB in *.
  assert (HD2 : exists d, qb = pt + d /\ 1 <= d <= 7) by (exists (qb - pt); lia).
  destruct HD2 as (d & -> & HDD).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x90b70] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 9 (2^26); KZRange pt 1 7; KZRange d 1 7; KZRange (pt + d) 2 8; KZRange b 0 64;
     KZRange (b - 8 * (pt + d)) 0 7; KZRange (b - 8 * pt) 8 63; KZRange (L - pt) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWord (SP + -312) 8 (DST + Qe); KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * pt) with (b - 8 * pt) in * by lia.
  all: (eapply KB; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s31_H2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b <= 64 -> SS + O + L + 400 <= SP ->
  (8 <= pt -> forall z12 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x90b5c) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (SP + -144))
               (Z_to_bv 64 b) x12 z12 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x12 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs))) ->
  (pt = 0 -> forall z10 z12 z13 : word,
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 b) x12 z12 z13 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90cb0) fc None mm (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> b / 8 <= pt -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * (b / 8))); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - b / 8)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z17 x6 x7 x8 x9 (Z_to_bv 64 1) z11 x12 z12 z13 z14 z15 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90b70) fc None mm' (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> pt < b / 8 -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z17 x6 x7 x8 x9 (Z_to_bv 64 0) z11 x12 z12 z13 z14 z15 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90b70) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
           x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x90a40) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HP0 HPL HB HSS KC KZ KA KB.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec pt 8) as [P7|P8]; [destruct (Z.eq_dec pt 0) as [P0|P1]|].
  3: kx_runFmd [AHUF_RELOADI; 0x90cb0; 0x90a58] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 8 (2^26); KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWord (SP + -312) 8 (DST + Qe); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [AHUF_RELOADI; 0x90cb0; 0x90a58] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 1 7; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWord (SP + -312) 8 (DST + Qe); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [AHUF_RELOADI; 0x90cb0; 0x90a58] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 0; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWord (SP + -312) 8 (DST + Qe); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: (apply KC; lia).
  2: { lazymatch goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
         rewrite (z4_srlw3 E e b) by (first [reflexivity | lia | (z4ez; reflexivity)]) end.
       rewrite (Z.add_assoc _ O pt).
       assert (HB8 : 0 <= b / 8 <= 8 /\ 8 * (b / 8) <= b <= 8 * (b / 8) + 7) by (clear - HB; Z.div_mod_to_equations; lia).
       destruct (Z_le_gt_dec (b / 8) pt) as [Q1|Q1].
       - eapply z4s31_R2A with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KA ltac:(lia) Q1).
       - eapply z4s31_R2B with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KB ltac:(lia) ltac:(lia)). }
  1: (apply (KZ P0)).
Qed.

Lemma z4s31_B2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 2 <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b <= 64 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (z10 y12 y13 y14 y15 y17 : word) (nb : Z), 0 <= nb <= 12 -> 1 <= bv_unsigned z10 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (b + nb)); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp y17 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 z10 (Z_to_bv 64 (b + nb)) (Z_to_bv 64 (DST + (q + bv_unsigned z10))) y12
              y13 y14 y15 x17 x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
              (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90c3c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (DST + q)) x13
           x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90b70) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 p s l jp cbs ob SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3
    SPL BD2 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 2 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x90c3c] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 2 (2^32); KZRange (Qe - q) 2 (2^32); KZRange (dcap - q) 2 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 64; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: let R40 := fresh "R40" in kx_range (EVar 40) R40.
  all: let R42 := fresh "R42" in kx_range (EVar 42) R42.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_C2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 c p s l : word) (jp : list byte)
    (SP DST dcap DT q Qe b tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap -> 0 <= b < 2^31 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (b <= 64 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
            x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
         F (Z_to_bv 64 0x90a40) fc None mm (seg_rom bsegs))) ->
  (64 < b ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
            x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
         F (Z_to_bv 64 0x90ca4) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
            x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90c3c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 c p s l jp SP DST dcap DT q Qe b tl mtl
    SPL BD2 MI RS HD HDE HDC HQ HQE HB HTL HMT HDT HSP K1 K2.
  unfold AZ4_SB in *.
  destruct (Z_le_gt_dec b 64) as [C|C].
  2: kx_runFmd [0x90a40; 0x90ca4] 10%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 65 (2^31 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -136) 4 b; KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x90a40; 0x90ca4] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 0 64;
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -136) 4 b; KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: kx_post_regs_keep.
  all: z4post_ez.
  1: apply K1; lia.
  1: apply K2; lia.
Qed.

Lemma z4s31_RT : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (bd3 : list cell)
    (SP DST dcap DT q Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x90b5c) (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
            x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (DST + q)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90b70) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x90b5c) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
            x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (DST + q)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            x30 x31)
       F (Z_to_bv 64 0x90b5c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 bd3 SP DST dcap DT q Qe tl mtl SPL MI RS HD HDE HDC HQ HQE HTL HMT HDT HSP K.
  unfold AZ4_SB in *.
  kx_runFmd [0x90b70] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -312) 8 (DST + Qe); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: kx_post_regs_keep.
  all: z4post_ez.
  exact K.
Qed.

Lemma z4s31_X2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word)
    (SP DST dcap DT q Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (Qe - q < 2 \/ x10 = Z_to_bv 64 0) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
            x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90cb0) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
            x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90b70) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 SP DST dcap DT q Qe tl mtl SPL MI RS HD HDE HDC HQ HQE HTL HMT HDT HSP HC K.
  unfold AZ4_SB in *.
  destruct (Z_lt_ge_dec (Qe - q) 2) as [C|C].
  - kx_runFmd [0x90c3c; 0x90cb0] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact K.
  - destruct HC as [HC|HC]; [lia|]. subst x10.
    kx_runFmd [0x90c3c; 0x90cb0] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 2 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact K.
Qed.
