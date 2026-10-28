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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax1 () := "C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begI47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natI45stdpp9bitvector;definitions2bv00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atI47Corelib4Init9Datatypes6option00I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C46Stdlib5Lists4List2InI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedK47Corelib4Init5Logic3and01C35stdpp4base6lookupK46Stdlib9micromega5Tauto8GFormula06I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableK47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K47Corelib4Init5Logic2or01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameK47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic5False00c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax1=ax1_sp_boundsC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_block_boundsC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic6eq_indC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_munchC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z3minC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7gran_okC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow>unpoisoned_nilK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega3Op201c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax1:ax1_blocksc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax18ax1_outbK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergec5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax1:ax1_magreec5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax19ax1_aheapC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax17AX1_EPIC56Stdlib6ZArith6BinInt1Z4lxorK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_xorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_xorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_wordC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_lxorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax17ax1_epiC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax17AX1_END".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition AX1_EPI : Z := 0x84ed8.     (* [comment removed for export] *)
Definition AX1_END : Z := 0x84eb8.     (* [comment removed for export] *)
Definition AX1_TL : Z := 0x84df8.
Definition AX1_TS : Z := 0x84dd8.
Definition AX1_T0 : Z := 0x84dd4.
Definition AX1_TX : Z := 0x84d18.
Definition AX1_HD : Z := 0x849bc.
Definition AX1_RL : Z := 0x847f8.
Definition AX1_R2 : Z := 0x848fc.
Definition AX1_R3 : Z := 0x84810.
Definition AX1_POST : Z := 0x8479c.
Definition AX1_CALL : Z := 0x84798.
Definition AX1_KSB : Z := 0x7fff8000.
Definition AX1_KT15 : Z := 4611686018427387904.
Definition AX1_KL31 : Z := 18446744073709551615.

Section CANSEC1. Context {rc : runConstT}.
Lemma ax1_wr_app : forall m a n1 n2, wr_at bsegs m a n1 -> wr_at bsegs m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 ->
  wr_at bsegs m a (n1 + n2).
Proof.
  intros m a n1 n2 (A0 & A1 & W1) (B0 & B1 & W2) N1 N2. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n1) as [Hl|Hl]; [apply W1; lia|].
  replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2; lia.
Qed.

Lemma ax1_wr_sub : forall m a n a' n', wr_at bsegs m a n -> a <= a' -> a' + n' <= a + n -> wr_at bsegs m a' n'.
Proof.
  intros m a n a' n' (A0 & A1 & W) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W; lia.
Qed.

Lemma ax1_rw_app : forall m A cs1 cs2, rw_cells bsegs m A cs1 -> rw_cells bsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells bsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] R1] [[W2 B2] R2].
  split; [split|].
  - apply cells_wf_app; split; assumption.
  - rewrite cells_bytes_app. apply (proj2 (bytes_at_app bsegs _ _ _ _)). split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. apply ax1_wr_app; [exact R1 | exact R2 | lia | lia].
Qed.

Lemma ax1_rw_split : forall m A cs1 cs2, rw_cells bsegs m A (cs1 ++ cs2) ->
  rw_cells bsegs m A cs1 /\ rw_cells bsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] R].
  apply cells_wf_app in W as [W1 W2]. rewrite cells_bytes_app in B.
  apply (proj1 (bytes_at_app bsegs _ _ _ _)) in B as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite cells_size_app, Nat2Z.inj_add in R.
  split; (split; [split; assumption|]); eapply ax1_wr_sub; [exact R | lia | lia | exact R | lia | lia].
Qed.

Lemma ax1_fr_split : forall m A c1 c2 pd pw a b, rw_cells bsegs m A [C8 c1; C4 c2; CB 4 pd; C8 pw; C8 a; C8 b] ->
  (exists fb, u8arr bsegs m A (map (Z_to_bv 8) fb) /\ zlen fb = 24) /\ rw_cells bsegs m (A + 24) [C8 a; C8 b].
Proof.
  intros m A c1 c2 pd pw a b H.
  destruct (ax1_rw_split m A [C8 c1; C4 c2; CB 4 pd; C8 pw] [C8 a; C8 b] H) as [H1 H2].
  split; [| exact H2].
  destruct (rw_cells_forget _ _ _ _ H1) as [junk HJ]. cbn [cells_size csize] in HJ.
  pose proof (u8arr_of_rw_cells bsegs _ _ _ _ HJ) as U.
  destruct HJ as [[[WJ _] _] _]. cbn [cell_wf] in WJ.
  exists (map bv_unsigned junk). rewrite map_map, length_map, WJ.
  split; [| reflexivity].
  erewrite map_ext; [rewrite map_id; exact U | intros x; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned].
Qed.

Lemma ax1_fr_join : forall m A (fb : list Z) a b, u8arr bsegs m A (map (Z_to_bv 8) fb) -> zlen fb = 24 ->
  rw_cells bsegs m (A + 24) [C8 a; C8 b] -> exists dcs, rw_cells bsegs m A dcs /\ cells_size dcs = 40%nat.
Proof.
  intros m A fb a b U L R.
  pose proof (rw_cells_of_u8arr bsegs m A _ U) as R1.
  exists ([CB (length (map (Z_to_bv 8) fb)) (map (Z_to_bv 8) fb)] ++ [C8 a; C8 b]). split.
  - apply ax1_rw_app; [exact R1 |]. cbn [cells_size csize]. rewrite length_map, Nat.add_0_r.
    replace (Z.of_nat (length fb)) with 24 by lia. exact R.
  - cbn [app cells_size csize]. rewrite length_map. lia.
Qed.

Section AX1.
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
  (* [comment removed for export] *)
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
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

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS11 := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma ax1_sp_bounds : 0x10007fff8000 <= SPF /\ SP <= 2^47 /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP.
Proof using All.
  pose proof ATOP_range as AT. unfold ATOP_MIN, ATOP_MAX in AT.
  pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
  unfold HUF_DEC_STACK_A in LOS. lia.
Qed.

  (* [comment removed for export] *)
  Lemma ax1_blocks : AIMG_HI <= DT /\ DT + DTL <= ATOP /\ DT mod 16 = 0 /\ AIMG_HI <= SBL /\ SBH <= ATOP
                     /\ (0 < dcap -> AIMG_HI <= DST /\ DST + dcap <= ATOP /\ DST mod 16 = 0 /\ ablk DST (DST + dcap)).
Proof using All.
  pose proof (hb_unpoisoned AI L RNG st LB m0 pdt DT DTL AH HDT) as (_ & D16 & _ & DBLK & DTOP & _).
  pose proof (ablk_lin _ _ DBLK) as (D1 & _ & _ & _).
  pose proof (ablk_lin _ _ (proj1 SBA)) as (S1 & _ & S2 & _).
  split; [exact D1|]. split; [exact DTOP|]. split; [exact D16|]. split; [exact S1|]. split; [exact S2|].
  intros DP. destruct HOUT as [[_ D0] | [pb HPB]]; [lia|].
  pose proof (hb_unpoisoned AI L RNG st LB m0 pb DST dcap AH HPB) as (_ & B16 & _ & BBLK & BTOP & _).
  pose proof (ablk_lin _ _ BBLK) as (B1 & _ & _ & _). repeat split; assumption.
Qed.

  (* [comment removed for export] *)
  Definition AX1M (mm : amem) : Prop :=
    (exists buf, u8arr bsegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at bsegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at bsegs mm (DT + 4) cbs
    /\ stk bsegs mm lo SPF
    /\ rw_cells bsegs mm (SP + -88) FRS11
    /\ mem_inv bsegs mm /\ munch DW m0 mm /\ wmono bsegs m0 mm.

  Definition AX1F (mm : amem) (fb : list Z) : Prop :=
    u8arr bsegs mm SPF (map (Z_to_bv 8) fb) /\ zlen fb = 24 /\
    rw_cells bsegs mm (SPF + 24) [C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 (SS + 8))].

  Definition ALINV (P bc : Z) : Prop := 0 <= bc <= 64 /\ (P = SS \/ (SS + 1 <= P /\ P + 8 <= SS + n)).

  (* [comment removed for export] *)
  Lemma ax1_aheap : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
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

  (* [comment removed for export] *)
  Lemma ax1_magree : forall mm, munch DW m0 mm -> wmono bsegs m0 mm ->
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
  Lemma ax1_outb : (DST = 0 /\ dcap = 0) \/ (1 <= dcap /\ AIMG_HI <= DST /\ DST + dcap <= KLS)
                    \/ (1 <= dcap /\ 0x10007fff8000 <= DST /\ DST + dcap <= ATOP).
Proof using All.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax1 ()) ["CANSEC1"; "AX1"] "p'0h02chh11Hh21ah32Hah42zhh52H1h63H13h72H7h84__p1h97__sat18h:7__sat19h;7__sat20h<7__sat21h=7__sat22h>7__sat23h?4__x1h@4__x2hA4__x3hB4__x4hC4__x5hD2pbhE1EhF2H0hG3H10hH3H11hI3H12hJ3H14hK3H15hL3H16hM3H17hN3H18hO3H19hP2H2hQ2H3hR2H4hS2H5hT2H6hU2H8hV2H9hW3HDBhX2HNhY2Q1hZ2Q2h[2Q3h\2Q4h]3RHIh^3RLOh_2_Hh`7__arithha4__ffhb7__sat17hc7__sat24hd7__sat25he8__varmaphf5__withg4cstrhh5cstr0hi1oi001xp&0p;2p;1p;3p;<p;4p;6p;7p;8g00?eR0j21Tg015fj1}Tg016_j3pTg017Xk30BTg00oMR1j2HTg017oR2j2FTg006Tj14Tg008Tj23Tg004fj29Tg004Aj10Tg0090k10?Tg01O[k303Tg00cVm<02Tg00dWk300Tg00eTj3VTg00fGj1`Tg007Rj18Tg00g?j1_Tg00h8j3zTg00i6j4]Tg00ihj1vTg00jJj4uTg00j^j4tTg00k7j1rTg00l0j2qTg00lRj1oTg00mOj1lTg006:j3ATg00nLj1kTg0072j2ETg009fj2jTg00ogk30ATg01FTk10@Tg00=Sj2hTg00Bbj1gTg00CGj1fTg00@@j1eTg00Cgk10>Tg00@^k20=Tg00DJj2YTg00E;j2XTg0087j2ZTg00F?j3[Tg010\j2\Tg011=j1aTg011Vj2WTg0123j2MTg012Pj2NTg00Ecj26Tg0137j2OTg013^j2QTg014Dj2TTg014jj2UTg00Fcj2RTg00GDj2JTg00J;j1|Tg00<>j1{Tg00KYj2^Tg00K;j1yTg00L7j4STg00LUj1xTg00M3j1wTg00M^j2DTg00Ojj3~Tg00T:j2cTg00Nek101Tg00NAj6sTg00Q[k204Tg00R=k205Tg00Rik306Tg00SHk407Tg01RRk308Tg01:Vk609Tg00PMk40:Tg00T]j7nTg00UAk70;Tg01:jk70<Tg00Uej8mTg00VgR3f0R4g00VIR53Ap=7f2R6f1R7/14'1p=:%04#0p=K%04#0#0#0p=L%84#8#8#8p=5%04#0#0#0#0#0#0#0p=IAA374p=<f6R8g0000R9g01;NR:f5R;f4R<f3R=P6J09;A7/14p==1367/14p=?1H:7/14p=@1174,16,1=,1<p=;1H:4p=i1354p=21654p=>1374,16p=PP3P7g00WEP4H0:p=CP7g00WlR>g00XKR?P?g00XkR@P4g00YKFnp=GP6P>P?P?P@P7P4K0;p=BP6P>P?P?P@P7P4K0<p=bP=P>P?P?P@P6P7P4Gmp=dp,4HOUTp,3DSTRA#7p,4dcapRB#7'1RCg01@G%}4?pABp,2LBRD40BREXD9RF,H9RG'FP2PCPGg00YkR2#4RH/3BRIg00[FRJ/3A19ABRKg01gWRL'33:%02RM#0RN#0RO#0RP#0RQ#0RR#K#LRS#0#5#5#5#5#0#K#L#I#4RT/3Ap,2rcRU$0?RV,3KRW5:I'FRX,FCRYP4B03CX4XECP4O1P1P9PFPYP4PUp,2AIp,1Lp,3RNGRFp,2stR1PDp,2m0RDP7PAPBp,2AHP4N<02g01<I,3BRZ,1IRIB00UABR[AVFABR\%`A%82R]#8R^#4,9B#_5VFR_AzDABR`g01=ARaPDPAPBC]Rb%v:Rcg01>6Rdg01>TReg01>mRfP:CuRgPdPePfP:CtRfP6%r1R11q:4Re%o4/<Bg00aRRd%lBg01?K3A%k7,<A['1RhF=X0:%4SRS,E7#71E4S#7%4RRS,9719KS%`7RS1j47#_Ri5VFPaPDPSPiC]'17?47?A3:X]3,H3X^3,H3Ri'@3:D;P0PIP[P\P_P`PcPgPfP=P1PePhF=X0:#i=:biD;PYP4P[P\P_P`PcPgPfP8P1PePhF=X0:#i=:biD;P0P[P\P_P`PbPcPgPff7RSP1PePhF=X0:/@iD;PYP4P0B0AUAKRK%2BRD%4PRP,EARa#7RF,1WRj'1RkP\P_P`PbPcPgPff;RlP1PePhF=X0:/@iD;PY[P4P0PDPjP\P_P`PbPcPgPff?P1PePhF=X0:/@iD;PY[P4P0PWPFP\P_P`PbPcPgPffCP1PePhF=X0:/@iD;PY[P4P\P_P`PbPcPgPffFP1PePhF=X0:/@iD;&0@U%5^#5#5R^#0#5#5#0#K#L#I#I#4%8^#5#5#0#K#L#I#I#4,3V7?Vp,3src,h3R^#g%f^#2%eO$0>p,3cbs'hR^#g%f^#2%eRp,2sp+0=RR/YP%2R%2PR^1ERPRU#2Ri[[1YAP%2A%2aR:\^[%4MR^%4QRQ'X%>^Rh%2Q1Z^QRe#>[R1[%2^Rfg00^2RgA[^Q7UW3%2eRQ\g^3f%0]#8#0#4Rc,X^%2c1Z^cRb#>[R`\hA[^c7VgX3f%2bRb\g^3fp,2tlRc,X^%2c1Z^cR_#>[R\\hA[^c7VgX3f%2_R_\g^3fp,3SBLRc%4ORO'Y%2c%2O1EcORY#2Rm[[1\cO%7ORn#a1WcORo,MO/9Y,<c[1NcO%>ORp16YO,1mRm[1OcO16O516OY?PY5[1QcO%7o\n1TcO1<Yc\ng01?kRn1UcORcePc1\AP%7PRc#aRY1WAPRo,MP/9a,<A[1NAP%>PRq16aP,1:R:[1OAP16P5Rr16Pa?Pa5[1QAP%7o\c1TAP1<aA\cPn1UAPRaePa1\RP1WRPRa,MP/9U,<R\Y1NRP16UP,1iRi\q1ORP16PU?PU5\r1QRP%7a\c1TRP1<UR\cPn1URPRRePRp,2DC16BeRe,1DP0PDPePXP4f9g00^NR01R5P'JPqeRqO1Pif@PqO1P:fG1R5O,J0PpeO1Pmf8PgfMP4P7O2X2fP_^2ffN1R5^,J0PheRhO1P\PlPgfRP4P7O2X2fPb^2ffSPhO1P`f>PgfWP4P7O2X2fPQ^2ffXPhO1P1p-0R1g00_4Rh#|%{hP3P31^3<P6%y3RhCSP7P31^3;P=PhCSCS%x3%w3Rh1D3M1D3]R]'C,Gh1D32R29~3]Rf1D3N'C,Gh5BhRN1c3T/C],Gh%8M,D3,Cf,Gh5BhRf5bh&01?RMPh1c3H/C2,GhR2PhP>P?P?P@PSEs5BhPMABh2NABh2f5bhCdCd204h@P4P6g00b2Rh,Jd20546=AdhdB06357H07babebfX?3X@3XA3XB3XC3W81964R5/3=9?76135<9?T6'FA?H7813H6RH13=<19<6R6/3;3:13T<13685:H'F[[^?3^@3^A3^B3^C3^81P4PZPVPLPAPJPBfjfqO8b`b>b=b4b<b;b4b:b9b4b5b7b6XOeXNDP7P4O2n2001000000121000000b2PXebMbLbKbJb6bIbHbGbVbUb7bTbSbRbQbPb5bFbbb9b:b;b<b=b>bcbdbhbgb1:08CXW_X\FX[WP7P4O2n2001000010121000000X1jXZDP7P4O2n2001000010121000000X1kXYKP7P4O2n2001000010121000000X1[P7P4O2n2001000000121000000W1XXIP7P4O2n2001000000121000000b1XWEXD9P7P4O2n2001000000121100000X1GP4O1n200100000021000011000bio"). Qed.

  Lemma ax1_unp : forall mm, munch DW m0 mm ->
    unpoisoned mm DT (DT + DTL) /\ unpoisoned mm DST (DST + dcap) /\ unpoisoned mm SBL SBH.
Proof using All.
  intros mm MU.
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

  (* [comment removed for export] *)
  Lemma ax1_epi : forall mm (dcs : list cell) (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6 xra : word),
    stk bsegs mm lo SPF -> rw_cells bsegs mm SPF dcs -> cells_size dcs = 40%nat -> rw_cells bsegs mm (SP + -88) FRS11 ->
    mem_inv bsegs mm -> munch DW m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                                 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 AX1_EPI) fc None mm (seg_rom bsegs)).
Proof using All.
  intros mm dcs t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6 xra STK FRD CS FRC MI MU WM.
  unfold AX1_EPI.
  destruct (rw_cells_forget _ _ _ _ FRD) as [dj FRJ]. rewrite CS in FRJ. clear FRD CS.
  pose proof ax1_sp_bounds as SB. unfold HUF_DEC_STACK_A in LOS.
  pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
  do 13 zstep.
  release_frame FRJ STK (bv_unsigned sp + -88). release_frame FRC STK (bv_unsigned sp).
  apply evtF_done. unfold huf_dec_postA.
  do 16 eexists. split; [reflexivity|]. split; [exact MI|]. split; [exact STK|].
  split; [exact (ax1_magree mm MU WM) | exact (ax1_aheap mm MU WM)].
Qed.

  (* [comment removed for export] *)
  Lemma ax1_end : forall mm (dcs : list cell) (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6 xra : word),
    stk bsegs mm lo SPF -> rw_cells bsegs mm SPF dcs -> cells_size dcs = 40%nat -> rw_cells bsegs mm (SP + -88) FRS11 ->
    mem_inv bsegs mm -> munch DW m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                                 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 AX1_END) fc None mm (seg_rom bsegs)).
Proof using All.
  intros mm dcs t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6 xra STK FRD CS FRC MI MU WM.
  unfold AX1_END.
  destruct (rw_cells_forget _ _ _ _ FRD) as [dj FRJ]. rewrite CS in FRJ. clear FRD CS.
  pose proof ax1_sp_bounds as SB. unfold HUF_DEC_STACK_A in LOS.
  pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
  zstep. zstep. zstep. if_cases K.
  - zstep.
    eapply ax1_epi; [exact STK | exact FRJ | reflexivity | exact FRC | exact MI | exact MU | exact WM].
  - zstep. zstep. zstep. zstep. if_cases K2.
    + eapply ax1_epi; [exact STK | exact FRJ | reflexivity | exact FRC | exact MI | exact MU | exact WM].
    + zstep.
      eapply ax1_epi; [exact STK | exact FRJ | reflexivity | exact FRC | exact MI | exact MU | exact WM].
Qed.

End AX1.
End CANSEC1.
