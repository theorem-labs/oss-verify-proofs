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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXGoM KXTac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax2 () := "C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2Cnth_error_firstn_ltC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit39x2_bytes'C47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3@x2_bytes'_lengthC46Stdlib5Lists4List=length_firstnC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission6Common5KXTac:find_fieldC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2or01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic3notK47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega=RingMicromega5Psatz07C46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3<x2_cellbytesC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_seqC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX29x2_nbBitsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_lenC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedK47Corelib4Init5Logic2ex01C47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3=x2_bytes'_nthC5ARocqVerifyHarness?AgentSubmission6Common5KXTacBztab_fact_bytes_atC47Corelib5Lists7ListDef3nthK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultI47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC35stdpp4base6lookupI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableK47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2=ax2_sp_boundsC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_block_boundsC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_munchC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7gran_okC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow>unpoisoned_nilc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2:ax2_blocksc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax28ax2_outbK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergec5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2:ax2_magreec5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax29ax2_aheapC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27AX2_EPIC56Stdlib6ZArith6BinInt1Z4lxorK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_xorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_xorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_wordC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_lxorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27ax2_epiC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27AX2_ENDc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2>ax2_x2tab_fact".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition AX2_EPI : Z := 0x84d34.     (* [comment removed for export] *)
Definition AX2_END : Z := 0x84d1c.     (* [comment removed for export] *)
Definition AX2_FIN : Z := Eval compute in AHUF_DX2_1X + 5256.
Definition AX2_RET : Z := Eval compute in AHUF_DX2_1X + 5288.
Definition AX2_K8 : Z := 134656.

(* [comment removed for export] *)
Lemma ax2_x2tab_fact : forall mm A cells tl, x2_table_ok cells tl ->
  bytes_at bsegs mm A (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells)) ->
  KXTac.ztab_fact bsegs mm A (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax2 ()) [] "p'0h04__x1h14__p1h21Hh34cstrh47__arithh54__ffh68__varmaph75__with84__x2h91bi001bh:2Hfh;4__p2h<4__x3h=4__x4h>4__x5h?2H5h@4__p3hA4__x6hB2z5hC2H6hD2H7hE3Hi0hF2z6hG2z7hH4__p4hI4__x7hJ1zi011zhK1ei021ehL2hihM1ihN2lohO1xhP4__p5hQ4__p6hR4__p7hS4__p8hT4__x8hU1ni031nhV1EhW2H3hX2TChY5__p10hZ5__p11h[5__p12h\4__p9h]1ri041rh^1yh_2z3h`1Aha2E2hb2E3hc2H4hd2H8he2HBhf2Hihg3Hi4hh2Hjhi2Hmhj2Hvhk2LNhl2N2hm2N3hn2NBho2P2hp2TLhq3TLRhr3TOKhs2_Hht1chu5cellshv1mhw2mmhx1oi051ohy2tlhz2z4h{2z8i061pp%0p%1p&0p&1p;1p;2p;3p;4p;6p;5p;<p;7p;:p;8p;Bg0000R0p4p710g001;R1p4p710R2p8p1001Yp4p7210P2p8g002Ej1dTg002jk10jTg003Hk10`Tg003kR2k10~Tg004Mk10wTg004mk20kTg0060j1lTg006Nj28Tg006kR3j23Tg007HR4j17Tg007hk10CTg008ik30KTg009Hk41]Tg00:=k20HTg00;8k20=Tg00<:R5k20}Tg00<Zj4{Tg00=:k10<Tg00=_k10eTg00>?j3STg00>_k60cTg00?ZR6j21Tg00@6j1]Tg00@[k118Tg00A9k116Tg00AWk115Tg00BBj2vTg00Bek214Tg00CGk20@Tg00Cak212Tg00DMj34k10|Tg00Dgk31[Tg00EFk41XTg00F8k20{Tg00F[k10yTg00G=S00j22Tg00GXk50vTg00H?k40DTg00HZk20STg00I:k20sTg00IQR7j1DTg00J1j1KTg00JPk20:Tg00JgR8j2tTg00KDk11LTg00Kbk41GTg00LEm<0YTg00Ljk21@Tg00MLR9j29Tg00Mhk10iTg00NFk20hTg00Ngk20gTg00OPk20;Tg00P<k409Tg00Pgk21<Tg00QEk21;Tg00Qek21:Tg00RHk119TP1j6xk70ETg00SPk317Tg00T2j26Tg00TRk208Tg00UNk20^Tg00V0k207Tg00VMS01k20]Tg00W0j2rTg00WRk60ATg00Wok313Tg00XIk60>Tg00Xek10\Tg00Y>k311Tg00YXk210Tg00Z7j2CTg00ZTk41\Tg00[5k51ZTg00[ak31YTg00\Hk61WTg00\lk31VTg00]MR1j2WTg00]jk20WTg00^Ak21STg00^dk31RTg00_Ak20zTg00_jk302Tg00`Hk20TTg00a2j2HTg00aLj1cTg00bPk10tTg00cNk104Tg00dOk101Tg00eMk20rTg00f3k20qTg00fYk40pTg00g@k31OTg00gck11NTg00hAk11MTg00hjk30fTg00iVk20nTg00jEk40mTg00j_R:k20QTg00k7k51KTP0k51JTg00l<m:1ITg00m@k41FTg00m\j4uTg00nGj7sTg00nkk21ETg00oIk61HTg00omj7~Tg010Qj8^Tg0115mB0PTg011[m<0oTg012@S02k206Tg012Zk31BTg013Cj3fTg013lk20ITg014Xk40[Tg0156k31ATg015Yk70ZTg016=k21TTg016Zk21UTg017<k31?Tg017ek31>Tf0R0#d#dp>05f3R;f2R<'1f1R=/10'2p=Ng018HR>/10p=<19=0,2<p=;g018fR?P=P0g019fH1Fp=w11<=/20p=|g01:hR@P@P=P0C{p>1=20S?0p=F%D0,1>p=hP<g01;FRAg01;eRBPBg01<ERCP@P=g01<eRDP0Cug01=LREFsp=A19>0p=Q21E@0p=jP<PAPBPBPCP@P=g01=lRFP0CuPEFsp=LP=PAPBPBPCP0J1Hp=:f5RGPAPBPBPCf4RHPAPBPBPCP;P<F~P=P0G^p==20@@0p=Ig01>SRIPIPIP@P@P@g01?2P7P7P7P3g01?RPGPHP;P<P=P0NB0Pp>0FPIP@P@P@P7P7PGPHP;P<P=P0N<0op>1DP@P@P@P@P@P@P8P0P=P<P8P;PHPGf6R8f7R3f8RJf9RKNB0Pp>1CA4@=0p=0A4@<=,2;0060p=X20g@0p=JB1B@=0p=`Af@=0p=RAf@=0g01@5RL+0Ip=E20I0Lp>0dg01@aRMASM=07S<p=kP@P@PHP;P<H0[P=P0H0[p=Z20{@0p=[B1A@=0p=zP@P=g01AMRNP0Cup=VP;PAPBPBPCP<P=PAPBPBPCP0PEFsF~p=\P<PAPBPBPCP@P=PNP0CuPEFsp=?P@P=PFP0Cup=pPHPAPBPBPCP;PAPBPBPCP<PEFsP=P0G^p>0bP3PAPBPBPCP8PAPBPBPCPGPHPAPBPBPCP;P<F~K0ZP=P0G^p>0aA4@=0,2<p=_ASM=0p>0NP@PHP;P<P=P0Exp=iP@P@P=P0C{,r<p=PP@P@P>P0C{p>0MA4@0>p=>A4@<=/20p=M12<=0060p=UA4@>0p>0L12=0,2<p=G20I=L=SM0p>0JP;PAPBPBPCP<PAPBPBPCP=PEFsP0F~p=nPGPAPBPBPCPHPAPBPBPCP@P;PNP<CuPEFsP=P0G^p=mP@P<P=P0H0[p=g11>=/20p=Y21T>0p=5P@PIP@P@P4PHP7P;g01B4P<P=P0N<0op=qPIPIPIP@P@P@g01BaP7P7P7P1g01CAPGPHP;P<P=P0NB0Pp>0VPIP@P0P7P=P<P;PHPGP8P3PJN<0Yp>0O21U>0p=@19>HA4@;<'211=>A4@0>'2+06p=BB1?@=0p>03Af@=09f@<p=TAf@=09f@<9f@;p=}ASM=09SM<9SM;9SMHp>0?Af@<=9f@;00IL=SM0p=aP<PAPBPBPCP=P0F~p=OP@P=PDP0Cup>0xB1>@=0p>00PGPAPBPBPCPHPAPBPBPCP;P<K0ZP=P0G^p>0GP3PAPBPBPCP8PAPBPBPCPGPAPBPBPCPHP;F~P<K0ZP=P0G^p=b110>p=oA4@0>,2=p>0U11=>/20p>0X19></2=0060p>1Q19>;A4@<='20060p>0uA4;<=/20p>1PB02H;<=4G=/20p=eB02;<==4H0p>0B11=0,2<p=yP8PAPBPBPCPGPHP;PAPBPBPCP<P=P0G^G^p>0_P;PAPBPBPCP<P=P0G^p>0lPIP@P:P7P9g01CdPGPHP;P<P=P0N<0Yp>0Rg01DFR9#dS03#dR7#dS04#d$05R:$0j$0`Q04$0jRD$0`RL$0~R1[&0w?20k=0g01DkR4PHP;%l7REQ03#lRN/8='3#7&0C<60KLH1]P=20k;<Q00%l9RFP;P;g01E`ROCN18N;20H?H%<0RP18NHRQ7;0%7=S05/w8-0=G[^M@3|P4P3P813EQPE20}@@RQ00}@RRPQP@P@P@PNP>C{&0<9RS#dS06#d#lRTC{PQP@%lSRU01=FPNC{&0eR5SR3SRRJ0cP0PFPGPGPOCN18N820H?318N3RO9;P0Q05/wK-0=J[^M@3|Q0020H?J,1O18NJRO9;P0Q05f:RV'w-0=K[^M@P4f;RWPV13EOPEPRJ0cP018NK20H?V'118NWRO9;P0f<RXQ05f=RY'w+0=[^M@11NORZ&05:$05$05S07#lS08,1OROPNPFPW%FXR:#]R[%h:R:&0eMR\&0wMRM&18@R]&16@R^&15@R_1v@>R`1v@NRa3A214_CRbP0P<g01FhRcg01GHRd+0@2120<=4cddB1[@>=H1XRdb5b6b7%QNP0b4b3ReP[P:p-0RfP\PM%j=S09P^P_P_1v@FRg20{@9Rh5L_S0:1:_;Ri&0yBRjQ0:E=PbPdb5b6b7X0@W111F0S0;/2=11F=S0<[^0@^1fP011YTPYP3O3b4b3I0vPNPWPTPeP[P:P\PMQ09P^P_P_Pi1v@TS0=9L_hS0>PjQ0>E=PbPdb5b6b7X0@X1f110TS0?,2=11=T[^0@^1fP011FYPYP3O3b4b3I0vH0D12ZOP4f?R4f>RO18NX,3ERZPEPR%7ZR:&0CYR[60KLRePVPI20SL[S0@-0s:18NY,3ERk%D0Rl'1XUIPIg01GhRm#KS0A#KRn#KS0B#KRo%FYRp+0:Rq%7k00s0#D,1kXUI%D:Rr%DqRs't11k0XJ@PZ%FORt-0:o#D,t0,1kXJ@1tZsRu,1Z%DpRv,3ERw,tZRx,1ZP@P@P6P0XO@RyP611=0$1LX^@XO@PZPZ%IZR6PuPxPyPyPyP@P@g01HG1t=0H1G#IXv@XU@PZPZP6PsPwPyPy%IlXOIPqPwPoPE%IES0CPpPv%IvJ0FJ1DN:1CN<0Y%]pRp%<vRv%Dt,3ERt-1@k19kt1tktRwPk10wt9|tkCX18NORt,3E%F4#D,3E'tP@&0i9-0h@R9%JnRn'`20g@mRm'RRk1EmnRw+0;&0dk;k\PM%j;S0DP<P]P=P]DZP^P_P_P_1:_GP_Q03#[Rk1v@ERs/zhS0E'VC\P_1:_8%[7R6,zsS0F9?_kS0GPjP_P_1ph6PjQ0E=L_kI0bL0aPbPdb5b6b7X0@X8@X<@X1fX;fP;P=13E013E<Rx9_H=CX11=;11x;[[^0@^8@^<@^1f^;fP0fARu#F#DRz,3ER{f@R|,8NR},3ER~'119~{PzP=P}P<P8O7b4b_bWb3H09PrPpPv20;mw00N\PMQ09P^P_P_AL_ahPiPjQ0E9L_`E=PbPdb5b6b7X0@X1fA|N0=13E=S0H#<[^0@^1fP0Q08,1tPtP<O3b4b3-1<ZDi21;:q#D21::qDiQ0@&19YEx20SLeB17L:[Ex%<<S0@18N4,3E7;<&0~QR[16;E008RAPQ<=3416HER:-0^N10N:207N:+0]16GE-07NPcQ01168ERe,0NPcP[P=&0MT,rQS0IPcP[16JERq-07UAPQFNS0J&0yQRZn0100000020000S0Kn0100000020000APQ38Rt54[16KERw/0N%>JS0L?_3T103N9MJF9MwU3U]:P=163ERv,0NS0MQ0I=4[tP[P@P2PQP@P0P5P@P@P@P0P0n2001106000120101101S0NPTn10110500021010600XK[Q0IAPQJ3P0J0A10T3P[P@P2PQP@P0P5P@P@P@P0P=n2001106000120101101S0OP>n10110500021010600XK[Q0IAPQKJP=J0A&0LK&0LVP@P>10TW16OER5/0NRp%>=S0P10XTS0Q'2105URr10=FS0R10XNR}3G3U[XN@10TVP@PTA4@>>Rz100TS0S'2&0LFR~100NS0T5Gr5UpXL@16YES0UA_zTTRz7MNQ0UA_~TN7MUfKR~#FR{#]%h{Q0A#JS0A,`9/Rm00J\S0VPMQ09P^P_P_PaPhPjP_P_1VhaP_P_1V``Q0=Q0=5?_CnCnEmPbPdb5b6b7X0@10N0AM=Nz[^0@P0164ES0WP3O2b4b3413PWP0J0>W2PWP0J0>W2P0O1b2P0O1b2W:WaP0O1Q0M$0\Q0K=4[t20^Uw10Uw207Uw+0]16VES0K-07UPcQ0116WES01,0UPcP[P=Q0JPZn0100000020000APQXWRc54[%>YQ0Q'210YF=Gr}5Up]:P=16XERp,0US0QQ0J=4[cP[P@P2PQP@P0Q0NPNn10110500021010600XK[Q0JAPQYXS0NP0J0A10NXP[P@P2PQP@P0Q0OPFn10110500021010600XK[Q0JAPQOYP=J0A10FO10F4P@PF10N|fCR}/6ERr/0NRtQ0P10uTS0O'210rUS0MQ0R10uNS0X3G3U[XN@10N4P@PN%>FS0RQ0S'2Q0M10FFS0SQ0T3G5UtXL@fBRz/6ER{/0NS0TQ0R10NT3G10{US0RQ0S?_NNS0S'2fPS0Y#FR{#]%h{Q0VPMQ09P^P_P_1v@UR{PhPjP_P_1Vh{P_P_1VggA?_aaCnCnEmPbPdb5b6b7X0@10U0Q0S9M=U[^0@P0fDRg/6ES0SP3O2b4b3411P|P0J0>W2P|P0J0>W2P0O1b2P0O1b2W:WbP0O1Q0Q$0\A4[ZcP[PZP2PQPfP0g01HkR2g01IHn10110500021000000XK[g01IdQ0NP0J0>P2Q0W/0N%>O?_YTQ0W10YN9MOF7MU3U0100b2W:WmP0O1n10210010400021110210103P<O1b9b]W:WlP0O1n10210010400021110211103P<O1b9b]10:N%>;?_<T10<N9M;F9M:U3U1CGER:#<RZ18NzS0N,9:R:PGPE%F}Rc#]R{%hcRcP\PMQ09P^P_P_AL_`hS0QPiPjQ0QE=PbPdb5b6b7X0@X1f12P=%<=S0V[^0@^1fP018NgS0Z,3E,93P3PHO3b4b3P{PcP\PMP]P^AA_`sPbPdb5b6b7%QEP0b4S0[b3RiH1\PGPEQ0NPiP{PcP\PM%j<S0N?g=]S0\P^P_P_1:_HS0]1zskS0^9A_hRcPjPcE=PbPdb5b6b7X0@X8@X1fQ0H9;<019=x[^0@^8@^1fP0%<3Q0ZP3PHO4b4b3I1ZH0D12Z:%FgR:#]%h:Q0[b3:1Y8E19eE,YefERe#FR:#]%h:P\PMP]P^P_PAPBPBPCA?_s`J1WPbPdb5b6b7%>EP2[P0b4b3:1V3E1C3ES0[,3E/Wv,03%7JR21CJES0Z#7S0H-0:oS0_%7qS0`+0WS0a54IS0b%5JS0cQ0Z#5S0d,3ERC%5qS0e'WRB'0S0f&0|IS0g&0|@S0h%D=/0lA4I=021S=041RX^IXOIS0iP2Q0cPy%50XO@RlPJPJ%IJDqS0jQ0aPBQ0_PCPoPEQ0CQ0HQ0dPyPlQ0ZQ0ZQ0Z#IDqS0kJ0FQ0`Q0ePyPlPqPq%IqDqS0lJ0VN90OfFRC#FS0m#]Q0m#DS0n#<%@wPw%5wRBPwPwPBDBQ0K#5S0oP@1CWERB#@PB%5BS0pPBPBQ0pDB1CXES0q#5S0rP@%@YPY%5YS0sPYPYQ0sDB%5OS0tP@%KoRB#KRw#KRA#KR:#KRZ#KRx#JRc,`9S0u20z@ES0v%J:S0w+03S0x%JwRw/RmPc&0i7-0h@S0yQ0w'`R:1`9wR{/Rm%KxRx#JS0z%JBS0{,`9RB/RmS0|9T:{7Tc20z@N003mQ0w?Twn'E+0;Q0z%JARAQ0v003nS0}7TB'ERiPiPiQ0zQ0v%JZS0~+03S10%JoS117TB'ERZQ0uQ0xPwPBQ11PmC}PcP:Q0{=T{mRB,RAATc:BRBQ0uQ0xPwQ0|C}R:Q0v003mS0|%Kx#JQ117Tw'E-0;:1Emc-0;BQ0zQ10Q0{7TA'ERBPBP\I0?+0J+0JCaCa7kZI0?CaCaPM%jGS0u?g8]P<P]P=%j8S12P8P]P;%jHS13DZDZP^P_P_P_&0<S#[RZ9A_`S14A?_hZS15AL_Z`S16A?_h`S175O_PjP_P_P_Q04#[RB9A_`S18P_1VkBC\P_P_1pB`A?_k`CnPjP_P_P_P_&0<7#[R7-0x`%[SRS=?_7CnP_P_1p7`A?_S`CnPjP_P_PZ1zsB0007PjP_P_AL_`7AA_7sPjP_P_AL_`B1:_JS19PjP_P_AL_`ZS1:1:_KS1;PjQ0^000S9?_hE=E=E=EmJ0GJ0GGbPbPdb5b6b7X0@X8@X<@X=@X>@XA@X1fX;f%Q;S0^P0P;%o;S1<00U0CX10<GS1=%><S1>-0XG61QGP3PHP3%>HS1?-0X3H0u13E3/WJ,08S1@%<KS1A?;KEQ1A/2WQ1A/2Y13EJS1B/WK,03[[[[[[[^0@^8@^<@^=@^>@^A@^1f^;fP0fMRS,8NR:,3E,9|1C|ES1C/9:16|ES1DQ1CP|PGP;P=P<PHP8PJPKPVPYO?b4bBb?bzbcb_bWb3H09b2%73Q0[#7-0:o%7v+0W54IP1&0CCS0[>02L2P1P=1rL0RvPK20TD0R:P:PJCNRxH1PX9L,HLXx1RiPIQ0aP1PLfHS1E$0CP=PvPxEeX9L,HLXUIP1Q0H/wCRx#cQ0`602LPiPVQ0ZP<O220=ex1CKE#7fGRx'wP?Q00&0t0R?Q07$05$05#lRi,9?'Y&040R?11?x'Y&010R?,1F11?N3GP1PL%c<%7pPvPWP:P:PVCNEeX9L,HLP=&0t<R?19?i'Y&04;R?fJRi,1?'Y&01;R?,1F11?N3GQ00&04HR?11?~'YPF&01HR?P?PNCNP1PL%c8Q1D#7PvP4P:P:POCNEeX9L,HLP0&048R?11?S'YPF&013R?P?PNCNQ02Q0T%>u10|T3GQ0R10uF10|N3GP1PL%cVQ0S#7PvP}P:P:PzCNEeX9L,HLPY%>zQ0O5GtQ00Q0S/0N%>}?_zTP1PL%cX16CES0O#7PvPeP:P:PgCNEeX9L,HLS0RP0Q0O/0N%>C?_eTQ00%>x10CTP1PL%c|16iE#7PvfIRtP:P:Q1ECNEeX9L,HLS0TP0%>tP@P>fL/6E008RAPQ0i54[S0210~TP1PL%ceS1DfOS07/6E#7PvP;P:P:PSCNEeX9L,HLS1F[]:XN@16~E008RS1G&0Mt,rQ54[10iTP@PTfNR>/6ER?008RS1H&0M0,rQ54[P1PL%cCS1IQ0Y/6ES1J#7PvI0BS1K%<:S1L11:<S1M3GX9L,HL]:XL@16SE008RS1NQ0I54[PNP1PLQ1IQ05PvI0BS05Q1L?y:TRR'2X9L,HLXJ@PLP1PLQ1D%7NS1LPvPREeX9LS1I&04gRR-0rDS0IP1PL%cgS1OQ1LQ0I,rLS1LI0BQ0I-0TDS0IQ0I/1T'YQ1L-0@120qDRS1LQ0?,2PXJ@S0?PRQ0?%7>S0?1C>ES1P#7S1Q-0:oS1R%7?S1S+0WS1T54I%5>Q1P#5,3E%5?'W'0S1UQ0gQ0hQ0iQ0?PlP>O1PyPlP>P>%I>DqQ1TPlQ1PO1S1T,3ERIPlP?O1S0?'WQ1RPIPoPEQ0CQ1QQ1TPyPlQ1PQ1PQ1P#IDqJ0FQ1SQ0?PyPlP?P?%I?DqJ0VN90OPCH0pS0?Q1Uf]#FRI#]S1S%hIS1PQ1J#@S1TQ1JQ1J#5RIQ1JQ1JPIDBS1JfQ/6E#5S1QP@fR/CERI#@S1RPI%5IS1VPIPIQ1VDBS1VfS/CE#5S1WP@fTRI#@S1XPI%5IS1YPIPIQ1YDBS1YfU#5S1ZP@Q11,`9,EARIQ0A/RmS1[,RnS1\$0dS1]Q1]PIP\I0?PMQ13?g3]P<Q12?g3]P=Q0uP3P]P3%j3S1^?g;]S1_DZDZP^P_P_P_Q18Q03$0<S03#d#[RI=?_BS18Q1;A?_I`S1`5O_PjP_P_P_1:_VS1aP_Q03$0<#[S1b/VZC\P_Q16P_Q1b/V`C\PjP_P_P71zsIQ1b+00PjP_P_PZPaPjP_P_Q0QP_1phkC\S1bPjP_1:_WS16Q0=9L_kS0=5O_PjQ0QQ0>5O_K0_EmEmJ0GGbPbPdb5b6b7X0@X8@X<@X=@X>@XA@XI@X1fX;fX@fQ0^PGP;20U3GCXPKP3P;Q1<%>3S0^'2CXQ1@10GN11HG,YH118TS1<,2OQ1<,Y8[[[[[[^0@^8@^<@^=@^>@^A@^I@^1f^;f^@fP0fdS1@,1FS1<fWS0>/6ES1c#QQ0>/CES0>#oPGP;P=Q0>Q1cQ1@&04SS1cPHP8PJP|PCf^S0>O@b4bGbDbFbCbBb?b3bEQ1LQ0?Q1UQ1SQ1PQ1TQ1JQ1QP@Q1RQ1VQ1WP@Q1XQ1YQ1ZP@Q1]00N\PMQ0\P^P_Q1bPjP_Q0]Q0=5O_PjP_Q0QP_B1O@aD-0xhC\S0QK0_PbPdb5b6b7X0@X8@X1fAyP0=Ay;<TQ0@Q04#l,8NS047;<[[^0@^8@^1fP0Q1<Q1@Q1cPCQ0>O5b4bGbDbFbCbBb?b3bE%<RRT&1ND,8NS0>7;Re&1MDRP9;TRe:0fDRDiQ0I20nDRDiH0DH0mQ1I,HLeP?P3DiW:P~P0P=K0EW2W:PiP0PxK0EW2P=P0O2n2001000000121000000W2WVP=P0O2n2001000000121000000W2P0O1Q0M10zFQ0X3GQ00Q0S/0U10zN9M}FQ0RP0Q0O/0U10eN9MCFQ0010xF10CNQ0TP010tFP@PFQ0210~NQ1F[]:XN@Q1GAPQFt54[10iNP@PNQ1HAPQF054[Q1K11F:RQQ1M3GX9L,HL]:XL@Q1NQ0J54[PUQ05AyQ:NRQ'2X9L,HLXJ@PLP1PLQ1D%7URUPvPQEeX9LRQ&01gRv-0rDR:P1PLQ1OPU1rL:RUI0BPF20TD:R:P:PNCN20@1U20qDvRUQ0;?y0NR1XJ@RFPvPFQ0?Q1UQ1SQ1PQ1TQ1JQ1QP@Q1RQ1VQ1WP@Q1XQ1YQ1ZP@P\PMQ09P^P_P_Q0:P_1phaC\RFPjPFH0lPbPdb5b6b7X0@Q0<?y=N\1^0@P0&01SPeO2RSb4bGbDbFbCbBb?b3bEPUQ0?Q1UQ1SQ1PQ1TQ1JQ1QP@Q1RQ1VQ1WP@Q1XQ1YQ1ZP@P\PMQ09P^P_PFPjQ0QH0lPbPdb5b6b7X0@Q0VQ047;=\1^0@PSb4bGbDbFbCbBb?b3bE%<vRSQ0>7;veA;SvPe:0fDvDiP:20nDvDiH0DH0m1HLQeP?P3DiW:P~P0P=K0EW2W:PiP0PxK0EW2P=P0O2n2001000000121000000W2WVP=P0O2n2001000000121000000W2P0O1n200100000021100011000WkWnP=P0O2n2001000000121000000W2WsP=P0O2n2001000000121000000btbXQ0[Q0a602LPCQ0HQ0`Q0HQ0m+0QQ0dQ0n'9Q0HQ0dQ0kQ0mQ0nQ0n#IJ0RQ0bQ0fQ0gQ0hQ0iP2PlPJO1Q0jQ0aPlQ0ZO1Ri,3ER?PlPqO1Rq'WQ0_P?PoPEQ0CQ0HPiQ0kJ0FQ0`PqQ0lJ0VN90OP0H0pRqQ0f%FxRi#]R?%hiRi1CVERQ#@PQ%5QRvPQPQPvDBQ0pP@%@pPp%5pRvPpPpPvDBQ0U#5P@%@ORvPOQ0tPOPOQ0tDBRp%54RQP@Q1\,EARDQ0~,`9R9Q0xQ0y/`AP{C},EcQ0zP9P{Q0{Q0}Q0vQ0A+03R:Q0|'RRSC}Q0zPcP9P{Q0B#JR9PSC}PAQ11Q1[20ND\CaCa9kDDCa3kPMQ1_P<Q0uP=%jJ?gH]S1_Q127gJDZP^P_P_P_Q1aP_Q03#[RD,VBC\P_Q16P_1VB`C\PjP_P_P_Q14A?_7ZS141:_XS03A?_7`RS5O_PjP_P_P_Q06#[Rc9A_`RPA?_hcS061:_YR1Q175O_PjP_P_PBQ0E0007PjP_P_Q1:1:_ORFPjP_P_1:_4RUAA_c6PjP_P_1:_|R[Q0F9A_DPjP_P_AL_a6S1:1:_uRaPjP_P_1p6kPjAA_hkS0EI0bE=E=E=E=EmGbGbJ0GPbPdb5b6b7X0@X8@X<@X=@X>@XA@XI@XT@X1fX;fX@fXHfXPfXQfXRfXSfPJP8P;20UK8S0BCX%Q8Rk10J8RDQ0L,2W3UPkP<P8Q1>,2YCX13E;/WV,0KQ1A/2|A;zK3Q1B9;gKA|NKC11VK19KVS1B[[[[[[[[[^0@^8@^<@^=@^>@^A@^I@^T@^1f^;f^@f^Hf^Pf^Qf^Rf^SfP018N>R>Q08'1%<u1CuERC#<16uERk/9E%oCRR%okRT%ou%QuP;P=PkPCPuP>Q07#F#DPGP<PHP8PJPVPWPOPzPgOIb4bGbDbFbCbBb?b3bEH09Q0`00QoQ0e/9EQ0`Q0eQ0lPoPEQ0CJ0RPqQ0fP?PiQ0K#@Q0KQ0oQ0KQ0KQ0oDBQ01#5P@Q0q#@Q0qQ0rQ0qQ0qQ0rDB1CYE#5P@PvPpPQP@Q1[,E9R9?k9\PMQ13?gG]PGQ0NP=Q0uPGP]PGQ0DDZDZP^P_P_P_PPP_1V7cC\P_1:_3PSPjP_P_P_Q19Q15Q1;Q175O_PjP_P_PB1zs7R7000hPjP_P_Q1aAA_ZsPjAA_hsE=EmGbL0aPbPdb5b6b7X0@X8@X<@X=@X>@X1fX;fX@fXHfP=PHP=Q1?,2GH0uP3P=P;Q0P,2JCX13E8/W<,0GA;WGE19HE[[[[^0@^8@^<@^=@^>@^1f^;f^@f^HfP0%<kPT%QkPRP;P=PkPCPGPHP8PJPVO=b4bGbDbFbCbBb?b3bEH09I1KExP2P0Ex18Ne,3ERk#7RRQ0[60KL>02L2PLQ0[PRP220Q2RQ0c%5kRL'9P2Q0cQ0jPRPLPyPlPkPk%IkDqJ0RPqQ0fP?Pi18Nx,3ERi#@Pi%5iR?PiPiP?DBQ1E,8N,3E#5P@%@XPX%5XR?PXPXP?DBQ0sP@%@5P5%55R?P5P5P?DBQ0W#5P@Q1C#@Q1CQ1C#5R?Q1CQ1CP?DB%5CP@1Ew:Rw1R:mR:,R{,EARCQ10Q0wQ0{=T{:Q10Q0wP{Q0{Q11P:C}PCPwPwPCAT{nm,EARAPwPwPAAkCw\I0?I0?Ca9kwwCa3kPMQ12?g;]P<Q1_P=Q1^PJP]PJQ0uDZDZP^P_P_P_Q1aQ14Q16=O_SPjP_P_P_Q03Q18Q1`9O_1PjP_P_P_PFQ06Q179O_UPjP_P_P_P[Q0GP_P_Q0F/p`PaCnPjP_P_Ph2007IPjP_P_1:_zAA_BsPjP_P_1:_}AA_Z6PjP_P_1:_gQ0F9A_cPjP_P_Q1:1:_ePjQ0EE=E=E=E=EmGbGbGbGbPbPdb5b6b7X0@X8@X<@X=@X>@XA@XI@XT@X1fX;fX@fXHfXPfXQfXRfXSfX\fXYfXZfX[fPJP8PHQ0BCXQ0L,2X9UWDQ1=Q1>,245UOPuPH13EGRu20XuzCX13EV/WW,0HA;eVEA;xVJ13EK9;tVA|NV~Q1B[[[[[[[[[^0@^8@^<@^=@^>@^A@^I@^T@^1f^;f^@f^Hf^Pf^Qf^Rf^Sf^\f^Yf^Zf^[fP0Q0Y,8NRNQ08'1%<}1C}ERf#<%<rQ0^13EN#Q%o}%Q}%or%Qr%of%QfP;P=PrPfP}PNP3PGP<PHP8PJPVPXPYP|PgOMb4b{bdbGbDbFbCbBb?b3bEH09I1JExbgbibjbhW:WfXL@XN@XM@N:1IboWXWpP=P0O2n2001000000121000000W2WqP=P0O2n2001000000121000000b2WeWrXy@WuX`@Wwo"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section AX2.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr) (SBL SBH : Z).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -64).
  Notation n := (zlen src).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HOUT : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  (* [comment removed for export] *)
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  (* [comment removed for export] *)
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis NSM : 1 <= n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SBB : SBL <= SS /\ SS + n <= SBH.
  Hypothesis SBA : ablk SBL SBH /\ SBL mod 8 = 0.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  (* [comment removed for export] *)
  Hypothesis DJ1 : KXGoM.apart DST dcap DT DTL.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  Hypothesis DJ3 : KXGoM.apart SS n DT DTL.
  (* [comment removed for export] *)
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

  Notation DW := [(SP + -56, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS6 := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma ax2_sp_bounds : 0x10007fff8000 <= SPF /\ SP <= 2^47 /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP.
Proof using All.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax2 ()) ["CANSEC1"; "AX2"] "h02Hah11Hh24__p1h37__sat19h47__sat21h57__sat23h67__sat25h74__x1h84__x2h94__x3h:4__x4h;2ATh<2H0h=3TOPh>2_Hh?3_H0h@3_H1hA7__arithhB4__ffhC7__sat17hD7__sat18hE7__sat20hF7__sat22hG7__sat24hH7__sat26hI8__varmaphJ5__withK1ahL4cstrhM5cstr0p;8p;1p;2p;3p;4p;6p;7p101J@p4p70p101K7p4p710p8g01KNj8yTg01LPj1xTg002Ej10Tg00]Mj24Tg01MGj1aTg00DMj3ETg0060j1:Tg00T2j2NTg00=:j12Tg006Nj2ITg00?Zj23Tg01N>j1qTg01O4j2UTg01OQj1lTg01POj1hTg004Mj1TTg01QLj1fTg00HZj2MTg007Hj1bTg01RAj2`Tg01R[j1_Tg00G=R0j27Tg002jj1OTg00`Hj2^Tg00Mhj1]Tg01SSj1\Tg00@6j1RTg00IQj1QTg003Hj1[Tg01TOj2PTg01U@j2JTg00MLj2;Tg01Uhj3LTg01VLj2wTg00CGj2ZTg00J1j1DTg00Ngj2ATg013Cj3BTg013lj2YTg00=_j1vTg00>?j3XTg00@[j1pTg00nkj2WTg014Xj4VTg00A9j1oTg00AWj1nTg00F8j2HTg00oIj6kTg00F[j1jTg00g@j3iTg017ej3FTg00m\j4STg01Vmj3gTg00Bej2mTg00Caj2eTg00Dgj3dTg00EFj4rTg00BBj2cTg00nGj7sTg00omj7tTg010Qj8uTf0R1#0#0p=<%01#0#0#0p=?%01#0#0#0#0#0#0#0p=>%01#:p=9%21#2p=Kf2R2f1R3'3/71p=5%21#2#2#2p=6g018HR4/31p=1g01:hR5/c1p=@P5P3g01=lP1CSp==P3g01;FR6g01;eR7P7g01<ER8P1g01=LFsp=8P2P6P7P7P8P3P1Ftp=Gf3R9P6P7P7P8P2P3P1Gup=Cp,2rcR:p,2AIp,1LR;p,3RNGp,2stR<p,2LBp,2m0p,2AHGy%x;R=g01DFR>#0R?#<R@#0RA#0RB#0RC#<#?RD#0RE#0#>#9'4%a;RF5E5RG%:DRD,NF=E54RH%:?RI%2?RJ#2RK#KRL#:RM'IRN,3FRO%q:RP%?J#9'U%2>RJ#KRQ#0#K#?#9,4P,3=75=%l<%h;5E5%T5%f;'Mg01WP#b'`g01XF%_;R;%?K#2#<#2#0#<#>#9,4;/3P35'7'7'7R;'7RK'7R<'7P0PGP<%6E#6#6#6#<#?#>#9R=%OCp,2sp'^RR%]CRC'414PDp,2loRS%:ERE,4S/3R3595RN35RTP1P0PHPKPTP1P0POP;PTP1%\:g01Y>g01Z8,3P75Pp,3src,M5R:#R%Q:#1%O@#[p,3cbs'MR:#R%Q:#1%:ARA,PR%1R%1A1NRA#1[[1JIM1;4IR:%1M1;4N[RU[%1IRVg01IHRWALIM3UW0%1N\W^0V%:BRB,JI%1B1IIBRM,;4[RX\:ALIB3VWX0V%1M\W^0V%0JRB#2#9RY,JI%1Y1IIYRZ,;4[R[\:ALIY3VWX0V%1Z\W^0Vp,2tlRZ,JI%1Z1IIZRY,;4[R\\:ALIZ3VWX0V%1Y\W^0Vp,3SBLRV%:@R@'P%1V%1@1NV@#1[[p,2DCp,4dcapR@#1RV1;@MR@'7P0PVP@PTP1f7R0g01[21w4I'ZP:eR:O1P\f:P:O1P[f=P:O1PXf@P:O1PUp-0RUg01@aR:g01GhRX#DR[#DR\#DRM#DRW,A51A5M1A5XRX5B55B5g01@5RM'Y%DW,A51A5\1A5[=B5X5B55B5/YM%v:5X:3X%T:P5P5%p5P2f4R:,W5CVP31W59CV%o5%n5RM%2Q#K#6#6RQ#0#6#6#<#?#>#>#9RX#@1H5?R?'=,8MPMP6P7P7P8f6R6Ek5GM%j7R7PM1H5BRB%@I%OL5i5RL'=,8MP7PMP51H5>R>%@A5F5g01<ePBCS,8MP7PM1H5JRJ%@ERB9g5>'=,8MP7PM%@D9F5?/=J,8MR?P7%@=%@C9F5>'=,8M1=>L,8MAF5JB/=>,8M9GM?5GM5GMCCCCCCCCCC1mM8P1P2g01FhRMg01GHR8'Z1e12=EM8dAd543CrbBbIbJX75X85X95X:5W2A5X3:13:N142Af5RA';1U9E,3A14AD/3614AC146D140E/3A75095AN55=[[[[[^75^85^95^:5^2UP1%2Q#6#6#<#?#>#>#9,3PPFPSPPPRfFfHp,3SPTp,3LOSp,3LOAO:bAb6b5b4b3X<@X1VP3P1O2n2001000000121000000bKbCbDb3bEb4bFb5bGb6bHbMbLPTeb;X@;X=OP3P1O2n2001000000121000000X1KX?HP3P1O2n2001000000121000000X1<X>GP3P1O2n2001000000121000000b1o"). Qed.

  (* [comment removed for export] *)
  Lemma ax2_blocks : AIMG_HI <= DT /\ DT + DTL <= ATOP /\ DT mod 16 = 0 /\ AIMG_HI <= SBL /\ SBH <= ATOP
                     /\ (0 < dcap -> AIMG_HI <= DST /\ DST + dcap <= ATOP /\ DST mod 16 = 0 /\ ablk DST (DST + dcap)).
Proof using All.
destruct (hb_unpoisoned AI _ _ _ _ _ _ _ _ AH HDT) as (_ & DT16 & _ & DBLK & DTOP & _).
pose proof (ablk_lin _ _ DBLK) as (D1 & D2 & D3 & D4).
destruct SBA as (SBK & _). pose proof (ablk_lin _ _ SBK) as (S1 & S2 & S3 & S4).
split; [lia|]. split; [lia|]. split; [exact DT16|]. split; [lia|]. split; [lia|].
intros DP. destruct HOUT as [(_ & D0) | (pb & HB2)]; [lia|].
destruct (hb_unpoisoned AI _ _ _ _ _ _ _ _ AH HB2) as (_ & O16 & _ & OBLK & OTOP & _).
pose proof (ablk_lin _ _ OBLK) as (O1 & O2 & O3 & O4).
split; [lia|]. split; [lia|]. split; [exact O16 | exact OBLK].
Qed.

  (* [comment removed for export] *)
  Definition AX2M (mm : amem) : Prop :=
    (exists buf, u8arr bsegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at bsegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at bsegs mm (DT + 4) cbs
    /\ stk bsegs mm lo (SP + -56)
    /\ rw_cells bsegs mm (SP + -56) FRS6
    /\ mem_inv bsegs mm /\ munch DW m0 mm /\ wmono bsegs m0 mm.

  (* [comment removed for export] *)
  Lemma ax2_aheap : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
Proof using All.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax2 ()) ["CANSEC1"; "AX2"] "p'0h01Hh17__sat19h27__sat21h37__sat23h47__sat25h54__x1h62Hah72H0h82H1h93H16h:7__arithh;7__sat17h<7__sat18h=7__sat20h>7__sat22h?7__sat24h@7__sat26hA1ahB4cstrhC5cstr0hD2pbhE2MUhF4__ffhG4__p1hH8__varmaphI5__withJ4__x2hK3DJ1hL3DJ2hM3H18hN4HOUThO3UDBhP3WDBhQ4WDBShR3H12hS4__x3hT2DChU3H11hV3H19hW4__p2hX1bhY2ivhZ3DSTh[2FAh\3H10h]3H13h^3H14h_3H15h`3H17ha2H2hb3H20hc2H3hd2H4he2H5hf2H6hg2H7hh2H8hi2H9hj3HDBhk2Hxhl2SBhm2WMhn3clsho4dcaphp2fnhq2mmhr1ohs1xi001xp%0p&0p;1p;2p;3p;7p;4p;6p;5p;=p;>p;8g002Ej12Tg002jj1_Tg003Hj1hTg003kk10WTg00<:k20TTg00`Hk20NTg00=:j18Tg00Mhj1mTg00]Mj21Tg00=_j1gTg00>?j37Tg023cj3MTg024Wk30VTg0060j16Tg00?Zj20Tg006Nj2RTg01N>k10ETg00G=R0j24Tg01k3j1nTg01klj3GTg00a2S00j2;Tg012@R1j2@Tg025Kj7QTg01[Xk10:Tg01m<j4ATg00HZj2oTg00IQj1tTg01n3j3TTg01^Zj3CTg01_Mj1|Tg01`Ej1dTg00DMj3fTg00MLj25Tg026Ij2~Tg00Xej1YTg01gOk30UTg00T2j2}Tg00H?j4FTg00YXk20STg027?k60PTg027[j5zTg0288k10OTg00@6j1xTg01TOj2wTg01U@j2VTg01Uhj3UTg01VLk20MTg00CGj2vTg004Mk10KTg00nkj2bTg00A9k10ITg00AWk10FTg00BBj2rTg00F8j2STg00m\j4qTg00\Hk60CTg00Bek20BTg00Cak20ATg00Dgk30@Tg00EFk40?Tg0296k20>Tg029kk60=Tg02:fk20<Tg01O4j2?Tg02;bj6]Tg02<hj5NTg02>2j1lTg02>jj1kTg006kj2PTg01lej3jTg02?bk10;Tg00J1j1iTg00Ngj2[Tg013Cj3yTg013lk209Tg014Xj4WTg00F[k108Tg00g@k307Tg01Vmj3pTg00Woj3LTg02@[k206Tg02A<j6aTg02A]l=sTg001;m>05m=0GTg00@[k10HTg00jEk404Tg00Y>k30JTg00<Zj4uTg00nGj7{Tg017ek303Tg00omk702Tg02B^k301Tg02C;k30QTg00oIk60RTg010Qk800Tf0R2#2#2p=Jg01:hR3P3f1R4P2Cup=\%22#2#2#2p=X%82#8#8#8p=9%22#2#2#2#2#2#2#2p=K%82#8p>0Lg018HR59f32p=Og022jR6?j42p=B1552p=DP3P3P5P2Cup=e1052p=3f2R7/04/42p=Hf3R8P7g01HkR9P4P2Dzp=>P7g01;FR:g01;eR;P;g01<ER<P3P4g01=lP2Cqg01=LR=F{p=:B03342p=<P4P:P;P;P<P2P=F{p>0DP7P:P;P;P<P4P2K02p==B01332p=^B0Q332p=Z1442,47p=E1r32p=IP4P:P;P;P<P2J0Rp=`P8P:P;P;P<P7P4P2L00p=cg01DFR=#2R>#JR?#2R@#2RA#2RB#_RC#h%_?#hRD$0W[20T33REp,2sp-0NCRC%8=S01#8RF#2#J#mRG'1RH/\CRIp,3DSTRJp,4dcapRK,1JS02'\S03%gERL57ES0437S05p,2m0RM;M2g01Dk@0VM4g02CX%JB#XRN#2RO#9#9#9#9#2#J#X#K#6S06%mBS07,1C'0S08%6>RB%8>S09#8$0LS0:#6RP'RRQ,0CS0;p,2rcRR$0ERS%6NRN'1RTp,2loS0<'0RUQ0<%6OS0='1/0CRO'4S0>'4RV'4p,4HOUTS0?%OJS0@%OKRW'4S0Ag01J@RX%n2RY?GJKp,2LBRZ'BS0BXDXS0C';S0D'@P1Q0AQ0DPRp,2AIR1p,1LS0Ep,3RNGR[p,2stS0FPZf5R\FQP2Q0AP0Q0@PWPRP1Q0EP[Q0FPZf7R]FQS0GP2Q0@P3P5%O2R^/4WAGY4K/BZXDX,;X'@P4PKp,2DTR_p,3mtlR`$0:RaCAP7PKp,2SSRbp,3src,o3Rc#tRdCA118K9TM8%DKReAC[\K[f6Rf#|%6FRg,1K#dRh5C[\e11fK,\f=7EL97EIf@Ri7MMPRP1Q0EP[Q0FPZfBFQ\W]E]Q]P]O]L]K]NXZ3Af355Rj/4WAGY5K/BZXDX,;X'@P5PKP_PaCAP5PKPbPdCA115KRk9TM5AC[5K\e%|5Rl=C[h\e%ek=7EL97EIf?7MMP3P514j^AGY54/BZXDX,;X'@%34R^%6ARA,RBRk,54'4P5P7PbPdCAP5P8P_PaCAf4S0H,159TM5%D\11fg#d9C[l[%DfAC[5][115]#e=7EL97EIfIRe7MMPRP1Q0EP[Q0FPZfJRhFQ]E]P]Q]O]K]L]T]NXo314jjRmAGY55/BZXDX,;XRY'@1055Rn%DkRo'4S0IP5P5PbPdCAP5P5P_PaCA1155Ra9TM51555R_115g#d9C[l[AC[55\_%ea=7EL97EIR_fHS0J7MMPRP1Q0EP[Q0FPZPMPeA7EILRlp,2AHS0KP_PlPMPe1~l2154C9HH4Rg#YS0L154a,4^#YS0Mg01IHR^'4%6=Rp/0`RqQ01#2Rr#2#6,0`R`PnPo10pdRp%8r#2#6Rr,RBRs,5dRtp,3SBLRu/0bRv11bdp,3SBHRb'0RwB0URubRb%6?R?,}uRx#ORyQ08PVQ08f>Rz15zC5HH#YR{P^P910HiR|15iCfA/5CQ0;Q0>Q0;Q0>PUPOPmPYP9PjPj10HeR}15hCRhf<fKR~,0H15~CP4P2CFO1WbW9P9\hRh\}P2f9S0NO1R~PhP~P920S92R~b9bRb9XVjXMjP2C>X9mfGS0O,0HRmQ0J/5CRjf:S0PP}15eCP4P2CFO1WVWMP9\jRj\mP2P]O1RmPjPmP9P~bMbRbMX9YfNS0QJ0PX`OXUUP2C>W9W0Q0HC>W_X^|PzC>X]^XR{f=R{DzXUVW\fSC>XiyXhbp,3SBAC>XgwXfvp,3SBBC>XetXdpp,3NSMC>XcoXanf;C>X8`X7qp,3MTLC>X0gQ0LeQ0MP^&0ORRg%9F#9#9RF#2#9#9#2#J#X#K#K#6%8F#9#9#2#J#X#K#K#6,0S7HSRF%xcRc%3dRdp,3cbs,oDRD#xRq%tD#3RD%6@R@,wCR`%3C%3@1}C@#3[[R@1VBPRp%DBRt%3P%DQ[Rv[Rw%3BRbAUBP4V^W6RP%3Q\^^6bRy1VBARV%3APo[Rz\tR|AUBA4V^X6bRA%3k\^^6bRU1VBrRO%3r%Ds[RY\tR~AUBr4V^X6bRr%3s\^^6bRsp,2tlRm,VBRj%3m1RBmRe#D[R}\tRhAUBm4V^X6bRm%3e\^^6bRb1wu?R^%3u%3?%3x[[RxfEQ0IP0PnPo%3i15ia'4#YP2P]g01[220M5B'vPteRtO1RuP}Q0PPtO1RePYP{PtO1R{PzPiPtO1RtPvg01@aS0M#gS0LQ0M$0KS0R1b34S0S&0I3S0T&0F3RiP:P;P;P<1r35R:1S3=R=5:iP3P=g01<e1<::Cq-0Di5=iJ0C20Bi<S0UP2P7g01FhR<g01GHR:'v20A27=f<:dB0@354H0?S0VbFbHbIX53%32152a'4P9[^53P2Q0JO1b:b4b3b2b1X8oX7nP4P2O2n2001000000121000000bAb;b<b1b=b2b>b3b?b4b@bCbBb0g01IdCFCF1~_4eWkXs320>_leP2J0=Q0OPEPR20<R1RlPZPT%^2R_%Z2S0O/?_E]XYER9PIPLPlPZPTPH1?CHRaDNS0J1B2ZS0W%l2R5/0H11HaR:%k2,15S0X'03EXX6,;6PlPZPSg02D[S0Y,?H,P?1P?aDN'@S0Z10THRa10:QR<'4S0[AjE2l10_HQ0O,0:3EXYE,;E&0;7?G42/BZ104H1142,0:3EXp3,;3X[3,;3Xn3,;3'@S0OPaP<PgPFPcPdPqPDP`P@PpPwPPPyPVP|PAPUPOP~PrPsPjPhPmPbP^PxfCS0\Q0IP0PnPoPaP2PuP}PePYP{PzPtPvp-0R:Q0Mg01GhRH#iR_#i,[31[3_1[3H5y35y3g01@5+09Q0L37S0MQ0RP31b37S0]P41b38S0^CWQ0TPiQ06#I1S3>R>Q07#I'<5:iS0_1`i\S0`%IN,<=RHQ01,S3R_5:iQ0=#IS01,<_=:i>5=i5=i5=i&08;R;%IGR_,<>9:iHS0aCcQ0UQ0VbFbHbIX53XJ3XS3WGQ06Q07,14112N/07Q0=,17/045E83H114N117G'0[^53^J3^S3^G:S06P2Q0;Q0<PCPSf]RNO5b:b4b3b2b1X8oX7nP4P2O2n2001000000121000000bAb;b<b1b=b2b>b3b?b4b@bCbBb0PgPFPcPdPqPDP`P@PpPwPPPyPVP|PAPUPOP~PrPsPjPhPmPbP^PxQ0\Q0IP0PnPoP<P2PuP}PePYP{PzPtPvQ0LQ0RQ0SQ0TPi1`i8%IBQ0:#_6073RB9:i=Q0H,`i5=i5=iP;1<=_R_Ap3=_'<=:iBCcQ0UQ0VbFbHbIX53XG:XW:RB102Q=E47114GRG1?4G'1/0Q[^53^G:^W:RQP2Q0>Q08PCPNO4b:b4b3b2b1X8oX7nP4P2O2n2001000000121000000bAb;b<b1b=b2b>b3b?b4b@bCbBb0CF3L3LPRPlPZPT%^IRn%ZI/?nE]Rne206E9RoEaM=sWEWPWQWOWKWLWTWNPKP2P]p,2DCR]P\PfQ0HP7P8P4N>05X0WWEWQWPWOWLWKWNPJP2Q0?p,3DJ1p,3DJ2p,3UDBp,3WDBp,4WDBSf8RWN=0GW0P4P2O2n2001000000121000000W0P2O1Q0DQ00PXQ0CQ0GP2Q0BPRP1Q0EP[Q0FPZPMQ0PQ05Q0KQ0NPWPEP9PIQ04Q0JQ0ZQ0[Q0OPaP<PgPFPcPdPqPDP`P@PpPwPPPyPVP|PAPUPOP~PrPsPjPhPmPbP^PxP]%3KRI15KkRk'4RWP0PIPkPaP2PuP}PePYP{PzPtPvQ0MQ0RP3Q0]P4P3Q0^P8&0H3R8CWCWQ0TPiQ0_Q0`Q09,S3Ra9:iHQ01,<a=:i>5=i5=i5=iP;Q0aCcQ0UQ0VbFbHbIX53XJ3XS3XG:Q06P2Q0;Q0<PCPSQ0QO5b:b4b3b2b1X8kX7IP4P2O2n2001000000121000000bAb;b<b1b=b2b>b3b?b4b@bCbBb0PgPFPcPdPqPDP`P@PpPwPPPyPVP|PAPUPOP~PrPsPjPhPmPbP^PxP]PWP0PIPkP<P2PuP}PePYP{PzPtPvPBPQP2Q0>Q08PCQ0QO4b:b4b3b2b1X8kX7IP4P2O2n2001000000121000000bAb;b<b1b=b2b>b3b?b4b@bCbBb0CF3L3LPnePEP9Q03PLPlPZPTPJQ02/?JRLDNQ0W105J11JLR5Q0X'03EXX6R9,;6REPlPZPSQ0Y,?J,P?1P?LDNRL'@P6P9%n4?GJKR91B9ZR6Q02,059HJJR?P2PgPFPcPdPqPDP`P@PpPwPPPyPVP|PAPUPOP~PrPsPjPhPmPbP^PxP]PWP0PIPkP?P2PuP}PePYP{PzPtPvQ0LQ0RP3Q0]P4P8CWQ0TA:i==1<=>R>=p3=,<==:i>5=iQ0UQ0VbFbHbIX53XJ31124Ri/?2,12/0i9H22^53^J3P2PKPJO2b:b4b3b2b1X8kX7IP4P2O2n2001000000121000000bAb;b<b1b=b2b>b3b?b4b@bCbBb0CF%l9RI/0J%k9,1I,055E6eH049LEL40JPRPlPZPTQ03#^RTQ03#Z/?TE]ePoEaEaM=sWjXDXP4P2O2n2001000000121100000W0P2O1n200100000021100011000brblWmWEWqo"). Qed.

  (* [comment removed for export] *)
  Lemma ax2_magree : forall mm, munch DW m0 mm -> wmono bsegs m0 mm ->
    magree bsegs (fun a => aclient_addr CI LB SP a /\ ~ (DST <= a < DST + dcap)) m0 mm.
Proof using All.
  intros mm MU WM. apply (munch_magreeA DW m0 mm); [exact MU | exact WM |].
  intros a [CA ND]. cbn [outside]. split; [| split; [exact ND | exact I]].
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold HUF_DEC_STACK_A in LOS.
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
  Lemma ax2_outb : (DST = 0 /\ dcap = 0) \/ (1 <= dcap /\ AIMG_HI <= DST /\ DST + dcap <= KLS)
                    \/ (1 <= dcap /\ 0x10007fff8000 <= DST /\ DST + dcap <= ATOP).
Proof using All.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax2 ()) ["CANSEC1"; "AX2"] "p'0h02chh11Hh21ah32Hah42zhh52H1h63H13h72H7h84__p1h97__sat18h:7__sat19h;7__sat20h<7__sat21h=7__sat22h>7__sat23h?4__x1h@4__x2hA4__x3hB4__x4hC4__x5hD2pbhE1EhF2H0hG3H10hH3H11hI3H12hJ3H14hK3H15hL3H16hM3H17hN3H18hO3H19hP2H2hQ2H3hR2H4hS2H5hT2H6hU2H8hV2H9hW3HDBhX2HNhY2Q1hZ2Q2h[2Q3h\2Q4h]3RHIh^3RLOh_2_Hh`7__arithha4__ffhb7__sat17hc7__sat24hd7__sat25he8__varmaphf5__withg4cstrhh5cstr0hi1oi001xp&0p;2p;1p;3p;<p;4p;6p;7p;8g00G=R0j21Tg01k3j1}Tg01klj3pTg01lek30BTg00a2R1j2HTg012@R2j2FTg0060j14Tg00?Zj23Tg00]Mj29Tg002Ej10Tg01N>k10?Tg00Wok303Tg01\\m<02Tg01]]k300Tg01^Zj3VTg01_Mj1`Tg00=:j18Tg01`Ej1_Tg01a>j3zTg01b<j4]Tg003kj1vTg01bnj4uTg01cBj4tTg01c[j1rTg00W0j2qTg01dTj1oTg01eQj1lTg00DMj3ATg01fNj1kTg00T2j2ETg01O4j2jTg01gOk30ATg0288k10@Tg00HZj2hTg00@6j1gTg00IQj1fTg002jj1eTg003Hk10>Tg00`Hk20=Tg01TOj2YTg01U@j2XTg006Nj2ZTg01Uhj3[Tg00\lj2\Tg00Xej1aTg00Z7j2WTg006kj2MTg00[aj2NTg00MLj26Tg01hDj2OTg01hkj2QTg01iQj2TTg01j7j2UTg01VLj2RTg00CGj2JTg00=_j1|Tg004Mj1{Tg00nkj2^Tg00@[j1yTg014Xj4STg00A9j1xTg00AWj1wTg00F8j2DTg017ej3~Tg00BBj2cTg00F[k101Tg00oIj6sTg00Bek204Tg00Cak205Tg00Dgk306Tg00EFk407Tg00Y>k308Tg01nnk609Tg00m\k40:Tg00nGj7nTg00omk70;Tg015Yk70<Tg010Qj8mTg01:hR3f0R4g018HR53Ap=7f2R6f1R7/14'1p=:%04#0p=K%04#0#0#0p=L%84#8#8#8p=5%04#0#0#0#0#0#0#0p=IAA374p=<f6R8g01J@R9g01oBR:f5R;f4R<f3R=P6J09;A7/14p==1367/14p=?1H:7/14p=@1174,16,1=,1<p=;1H:4p=i1354p=21654p=>1374,16p=PP3P7g01=lP4H0:p=CP7g01;FR>g01;eR?P?g01<ER@P4g01=LFnp=GP6P>P?P?P@P7P4K0;p=BP6P>P?P?P@P7P4K0<p=bP=P>P?P?P@P6P7P4Gmp=dp,4HOUTp,3DSTRA#7p,4dcapRB#7'1RCg022j%}4?pABp,2LBRD40BREXD9RF,H9RG'FP2PCPGg01DFR2#4RH/3BRIg01XFRJ/3A19ABRKg02Q3RL'33:%02RM#0RN#0RO#0RP#0RQ#0RR#K#LRS#0#5#5#5#5#0#K#L#I#4RT/3Ap,2rcRU$0?RV,3KRW5:I'FRX,FCRYP4B03CX4XECP4O1P1P9PFPYP4PUp,2AIp,1Lp,3RNGRFp,2stR1PDp,2m0RDP7PAPBp,2AHP4N<02g020=,3BRZ,1IRIB00UABR[AVFABR\%`A%82R]#8R^#4,9B#_5VFR_AzDABR`g01DkRaPDPAPBC]Rb%v:Rcg0215Rdg021SReg021lRfP:CuRgPdPePfP:CtRfP6%r1R11q:4Re%o4/<Bg01FhRd%lBg022J3A%k7,<A['1RhF=X0:%4SRS,E7#71E4S#7%4RRS,9719KS%`7RS1j47#_Ri5VFPaPDPSPiC]'17?47?A3:X]3,H3X^3,H3Ri'@3:D;P0PIP[P\P_P`PcPgPfP=P1PePhF=X0:#i=:biD;PYP4P[P\P_P`PcPgPfP8P1PePhF=X0:#i=:biD;P0P[P\P_P`PbPcPgPff7RSP1PePhF=X0:/@iD;PYP4P0B0AUAKRK%2BRD%4PRP,EARa#7RF,1WRj'1RkP\P_P`PbPcPgPff;RlP1PePhF=X0:/@iD;PY[P4P0PDPjP\P_P`PbPcPgPff?P1PePhF=X0:/@iD;PY[P4P0PWPFP\P_P`PbPcPgPffCP1PePhF=X0:/@iD;PY[P4P\P_P`PbPcPgPffFP1PePhF=X0:/@iD;&0@U%5^#5#5R^#0#5#5#0#K#L#I#I#4%8^#5#5#0#K#L#I#I#4,3V7?Vp,3src,h3R^#g%f^#2%eO$0>p,3cbs'hR^#g%f^#2%eRp,2sp+0=RR/YP%2R%2PR^1ERPRU#2Ri[[1YAP%2A%2aR:\^[%4MR^%4QRQ'X%>^Rh%2Q1Z^QRe#>[R1[%2^Rfg01IHRgA[^Q7UW3%2eRQ\g^3f%0]#8#0#4Rc,X^%2c1Z^cRb#>[R`\hA[^c7VgX3f%2bRb\g^3fp,2tlRc,X^%2c1Z^cR_#>[R\\hA[^c7VgX3f%2_R_\g^3fp,3SBLRc%4ORO'Y%2c%2O1EcORY#2Rm[[1\cO%7ORn#a1WcORo,MO/9Y,<c[1NcO%>ORp16YO,1mRm[1OcO16O516OY?PY5[1QcO%7o\n1TcO1<Yc\ng01IdRn1UcORcePc1\AP%7PRc#aRY1WAPRo,MP/9a,<A[1NAP%>PRq16aP,1:R:[1OAP16P5Rr16Pa?Pa5[1QAP%7o\c1TAP1<aA\cPn1UAPRaePa1\RP1WRPRa,MP/9U,<R\Y1NRP16UP,1iRi\q1ORP16PU?PU5\r1QRP%7a\c1TRP1<UR\cPn1URPRRePRp,2DC16BeRe,1DP0PDPePXP4f9g01[2R01R5P'JPqeRqO1Pif@PqO1P:fG1R5O,J0PpeO1Pmf8PgfMP4P7O2X2fP_^2ffN1R5^,J0PheRhO1P\PlPgfRP4P7O2X2fPb^2ffSPhO1P`f>PgfWP4P7O2X2fPQ^2ffXPhO1P1p-0R1g01@aRh#|%{hP3P31^3<P6%y3RhCSP7P31^3;P=PhCSCS%x3%w3Rh1D3M1D3]R]'C,Gh1D32R29~3]Rf1D3N'C,Gh5BhRN1c3T/C],Gh%8M,D3,Cf,Gh5BhRf5bh&01?RMPh1c3H/C2,GhR2PhP>P?P?P@PSEs5BhPMABh2NABh2f5bhCdCd204h@P4P6g01GHRh,Jd20546=AdhdB06357H07babebfX?3X@3XA3XB3XC3W81964R5/3=9?76135<9?T6'FA?H7813H6RH13=<19<6R6/3;3:13T<13685:H'F[[^?3^@3^A3^B3^C3^81P4PZPVPLPAPJPBfjfqO8b`b>b=b4b<b;b4b:b9b4b5b7b6XOeXNDP7P4O2n2001000000121000000b2PXebMbLbKbJb6bIbHbGbVbUb7bTbSbRbQbPb5bFbbb9b:b;b<b=b>bcbdbhbgb1:08CXW_X\FX[WP7P4O2n2001000010121000000X1jXZDP7P4O2n2001000010121000000X1kXYKP7P4O2n2001000010121000000X1[P7P4O2n2001000000121000000W1XXIP7P4O2n2001000000121000000b1XWEXD9P7P4O2n2001000000121100000X1GP4O1n200100000021000011000bio"). Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ax2_tab : forall mm, bytes_at bsegs mm (DT + 4) cbs -> KXTac.ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)].
Proof using All.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax2 ()) ["CANSEC1"; "AX2"] "h01Hh13cbsh22mmp;1p;2p;4p;3p;6g002Ej10Tg002jj13Tg003Hj12Tg003kj15Tg0060j14Tg00]Mj2<Tg009Hj41Tg004Mj1;Tg006Nj2:Tg006kj26Tg007Hj17Tg007hj18Tg008ij39Tg00XIj6>Tg03n=j6=Tg01DF#0R0#0R1#0R2#0#0#0#3#2%32#2R2#5[g01DkR3f0R4p,2DT%41R1'<R5p,3cbsR6C1%;2R7P6P3f2R6P5P4C1X17P4%40p,2tlR0':,61#7p,5cellsR1#8592R2p,3ECBE>P3f1P5P2C1P6P5P1P0p,3TOKP4E=b0W0W2o"). Qed.

  Notation DW' := [(SP + -2352, SP); (DST, DST + dcap)].
  Notation FRS8 := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition AX2F (mm : amem) : Prop :=
    (exists buf, u8arr bsegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at bsegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at bsegs mm (DT + 4) cbs
    /\ stk bsegs mm lo (SP + -112)
    /\ (exists g, rw_cells bsegs mm (SP + -112) [CB 8 g])
    /\ rw_cells bsegs mm (SP + -64) FRS8
    /\ mem_inv bsegs mm /\ munch DW' m0 mm /\ wmono bsegs m0 mm.

  Lemma ax2_aheap' : forall mm, munch DW' m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
Proof using All.
  intros mm MU WM. unfold HUF_DEC_STACK_A in LOS.
  pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
  assert (FST : aclient_range CI LB (ATOP + 4096) (SP + -2352) (SP - (SP + -2352))).
  { unfold aclient_range, aclient_app_range. left. left. lia. }
  destruct HOUT as [[D0 C0] | [pb HPB]].
  - eapply (AI_frame AI L RNG st LB m0 mm [(SP + -2352, SP)] AH); [| exact WM | constructor; [exact FST | constructor]].
    eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as [Hx _].
    split; [exact Hx |]. split; [lia | exact I].
  - eapply (AI_frame AI L RNG st LB m0 mm _ AH MU WM).
    constructor; [exact FST | constructor; [| constructor]].
    cbn [fst snd]. unfold aclient_range. right. left. exists (HB pb DST dcap). cbn [ab_addr ab_size]. split; [exact HPB | lia].
Qed.

  Lemma ax2_magree' : forall mm, munch DW' m0 mm -> wmono bsegs m0 mm ->
    magree bsegs (fun a => aclient_addr CI LB SP a /\ ~ (DST <= a < DST + dcap)) m0 mm.
Proof using All.
  intros mm MU WM. apply (munch_magreeA DW' m0 mm); [exact MU | exact WM |].
  intros a [CA ND]. cbn [outside]. split; [| split; [exact ND | exact I]].
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold HUF_DEC_STACK_A in LOS.
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

  Lemma ax2_unp' : forall mm, munch DW' m0 mm ->
    unpoisoned mm DT (DT + DTL) /\ unpoisoned mm DST (DST + dcap) /\ unpoisoned mm SBL SBH.
Proof using All.
  intros mm MU. unfold HUF_DEC_STACK_A in LOS.
  pose proof ATOP_range as AT. unfold ATOP_MIN, ATOP_MAX in AT.
  pose proof (hb_unpoisoned AI L RNG st LB m0 pdt DT DTL AH HDT) as (_ & _ & DN & DBLK & _).
  pose proof (ablk_lin _ _ DBLK) as (DL1 & DL2 & DL3 & DL4).
  pose proof (ablk_lin _ _ (proj1 SBA)) as (SL1 & SL2 & SL3 & SL4).
  pose proof (shad_in_band DT ltac:(lia)) as SH1.
  pose proof (shad_in_band (DT + DTL - 1) ltac:(lia)) as SH2.
  pose proof (shad_in_band SBL ltac:(lia)) as SH3.
  pose proof (shad_in_band (SBH - 1) ltac:(lia)) as SH4.
  assert (OB : (DST = 0 /\ dcap = 0) \/ (1 <= dcap /\ ablk DST (DST + dcap))).
  { destruct HOUT as [HO | [pb HPB]]; [left; exact HO | right].
    pose proof (hb_unpoisoned AI L RNG st LB m0 pb DST dcap AH HPB) as (_ & _ & BN & BBLK & _). split; [lia | exact BBLK]. }
  split; [| split].
  - eapply unpoisoned_munch; [exact UDT | exact MU |]. cbn [disjoint_from].
    destruct OB as [[D0 C0] | [BN BBLK]]; [unfold KLS in *; lia |].
    pose proof (ablk_lin _ _ BBLK). unfold ablk, AIMG_HI, KLS in *. lia.
  - destruct OB as [[D0 C0] | [BN BBLK]].
    + rewrite D0, C0. apply unpoisoned_nil. lia.
    + pose proof (ablk_lin _ _ BBLK) as (BL1 & BL2 & BL3 & BL4).
      pose proof (shad_in_band DST ltac:(lia)) as SH5.
      pose proof (shad_in_band (DST + dcap - 1) ltac:(lia)) as SH6.
      eapply unpoisoned_munch; [exact UDB | exact MU |]. cbn [disjoint_from]. unfold ablk, AIMG_HI, KLS in *. lia.
  - eapply unpoisoned_munch; [exact USB | exact MU |]. cbn [disjoint_from].
    destruct OB as [[D0 C0] | [BN BBLK]]; [unfold KLS in *; lia |].
    pose proof (ablk_lin _ _ BBLK). unfold ablk, AIMG_HI, KLS in *. lia.
Qed.

  Lemma ax2_ret : forall mm (csB : list cell)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    AX2F mm -> rw_cells bsegs mm (SP + -104) csB -> cells_size csB = 40%nat ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31) FR (Z_to_bv 64 AX2_RET) fc None mm (seg_rom bsegs)).
Proof using All.
  intros mm csB x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 XF FRD CS.
  unfold AX2F in XF. destruct XF as (_ & _ & _ & STK & (g & GAP) & FRC & MI & MU & WM).
  destruct (rw_cells_forget _ _ _ _ FRD) as [dj FRJ]. rewrite CS in FRJ. clear FRD CS.
  pose proof ax2_sp_bounds as SB. unfold HUF_DEC_STACK_A in LOS.
  pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
  unfold AX2_RET.
  repeat zstep.
  release_frame GAP STK (bv_unsigned sp + -104).
  release_frame FRJ STK (bv_unsigned sp + -64).
  release_frame FRC STK (bv_unsigned sp).
  apply evtF_done. unfold huf_dec_postA.
  do 16 eexists. split; [reflexivity|]. split; [exact MI|]. split; [exact STK|].
  split; [exact (ax2_magree' mm MU WM) | exact (ax2_aheap' mm MU WM)].
Time Qed.

  Ltac ax2_walk_to p :=
    repeat (lazymatch goal with
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let K := fresh "K" in destruct c eqn:K; cbv iota
            | |- _ => zstep
            end).

  Lemma ax2_end' : forall mm cw bcw (pad : list byte) pw ps pl
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    AX2F mm -> rw_cells bsegs mm (SP + -104) [C8 cw; C4 bcw; CB 4 pad; C8 pw; C8 ps; C8 pl] ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31) FR (Z_to_bv 64 AX2_FIN) fc None mm (seg_rom bsegs)).
Proof using All.
  intros mm cw bcw pad pw ps pl x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 XF FRD.
  pose proof XF as XF0. unfold AX2F in XF. destruct XF as (_ & _ & _ & STK & (g & GAP) & FRC & MI & MU & WM).
  pose proof ax2_sp_bounds as SB. unfold HUF_DEC_STACK_A in LOS.
  pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
  unfold AX2_FIN.
  let p := eval cbv in AX2_RET in ax2_walk_to p.
  all: eapply ax2_ret; [exact XF0 | exact FRD | reflexivity].
Time Qed.

  Notation PINV P := (P = SS \/ (SS + 1 <= P /\ P + 8 <= SS + n)).
  Definition ax2_bd (mm : amem) (cw : word) (bc : Z) (pad : list byte) (P : Z) : Prop :=
    rw_cells bsegs mm (SP + -104) [C8 cw; C4 (Z_to_bv 64 bc); CB 4 pad; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 (SS + 8))].
  Definition ax2_st (k : Z) (mm : amem) (x1 x5 x6 x7 x9 x10 x11 x12 x14 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) x9 x10 x11 x12 (Z_to_bv 64 (DT + 4)) x14
            (Z_to_bv 64 (2^61)) x16 x17 x18 (Z_to_bv 64 (2^31 - 2^15)) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       FR (Z_to_bv 64 (AHUF_DX2_1X + k)) fc None mm (seg_rom bsegs).
  Notation PE := (Z_to_bv 64 (DST + dcap)).
  Notation DL := (Z_to_bv 64 (tl + 256 * mtl)).
  Notation ZB z := (Z_to_bv 64 z).

  Definition ax2_goal_4772 : Prop := forall mm j cw bcw pad pw (x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    AX2F mm -> rw_cells bsegs mm (SP + -104) [C8 cw; C4 bcw; CB 4 pad; C8 pw; C8 (ZB SS); C8 (ZB (SS + 8))] -> 0 <= j <= dcap ->
    evtF bsegs RNG POST (ax2_st 4772 mm x1 x5 x6 x7 (ZB (DST + j)) x10 x11 x12 PE DL x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Definition ax2_goal_4768 : Prop := forall mm j cw bcw pad pw (x1 x7 x10 x11 x12 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    AX2F mm -> rw_cells bsegs mm (SP + -104) [C8 cw; C4 bcw; CB 4 pad; C8 pw; C8 (ZB SS); C8 (ZB (SS + 8))] -> 1 <= dcap ->
    0 <= j <= dcap ->
    evtF bsegs RNG POST (ax2_st 4768 mm x1 (ZB (- DT - 5)) (ZB (64 - tl)) x7 (ZB (DST + j)) x10 x11 x12 PE DL
                                (ZB (DST + dcap - 2)) x18 x20 x21 x22 x28 x29 x30 x31).
  Definition ax2_goal_3976 : Prop := forall mm j bc P cw pad (x1 x10 x11 x12 x18 x20 x21 x22 x31 : word),
    AX2F mm -> ax2_bd mm cw bc pad P -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= bc <= 64 -> PINV P ->
    evtF bsegs RNG POST (ax2_st 3976 mm x1 (ZB (- DT - 5)) (ZB (64 - tl)) (ZB 65) (ZB (DST + j)) x10 x11 x12 PE DL
                                (ZB (DST + dcap - 2)) x18 x20 x21 x22 (ZB AX2_K8) (ZB 3) (ZB bc) x31).
  Definition ax2_goal_3924 : Prop := forall mm j bc P cw pad (x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    AX2F mm -> ax2_bd mm cw bc pad P -> 0 <= j <= dcap -> 0 <= bc < 2^32 -> (bc <= 64 -> PINV P) ->
    evtF bsegs RNG POST (ax2_st 3924 mm x1 x5 x6 x7 (ZB (DST + j)) x10 x11 x12 PE DL x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Definition ax2_goal_276 : Prop := forall mm j bc P cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    AX2F mm -> ax2_bd mm cw bc pad P -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= bc <= 64 -> PINV P ->
    evtF bsegs RNG POST (ax2_st 276 mm x1 (ZB bc) (ZB (DST + dcap - 9)) (ZB (- DT - 5)) (ZB (DST + j)) x10 (ZB P) x12 PE DL
                                cont x18 x20 x21 x22 (ZB 65) (ZB (64 - tl)) (ZB 1) (ZB AX2_K8)).
  Definition ax2_goal_2272 : Prop := forall mm j bc P cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    AX2F mm -> ax2_bd mm cw bc pad P -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= bc <= 64 -> PINV P ->
    evtF bsegs RNG POST (ax2_st 2272 mm x1 (ZB bc) (ZB (DST + dcap - 7)) (ZB (- DT - 5)) (ZB (DST + j)) x10 (ZB P) x12 PE DL
                                cont x18 x20 x21 x22 (ZB 65) (ZB (64 - tl)) (ZB AX2_K8) (ZB 8)).
  Definition ax2_goal_200 : Prop := forall mm bc P b01 cont pad (x1 x5 x6 x7 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    AX2F mm -> ax2_bd mm cont bc pad P -> 1 <= bc <= 64 -> PINV P -> 8 <= dcap -> 0 <= b01 < 2^16 ->
    evtF bsegs RNG POST (ax2_st 200 mm x1 x5 x6 x7 (ZB DST) (ZB (b01 + 2^16 * (tl + 256 * mtl))) x11 x12 PE DL
                                x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Definition ax2_goal_2052 : Prop := forall mm bc P cont pad (x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    AX2F mm -> ax2_bd mm cont bc pad P -> 1 <= bc <= 64 -> PINV P -> dcap < 8 ->
    evtF bsegs RNG POST (ax2_st 2052 mm x1 x5 x6 x7 (ZB DST) x10 x11 x12 PE DL x17 x18 x20 x21 x22 x28 x29 x30 x31).

End AX2.
End CANSEC1.
