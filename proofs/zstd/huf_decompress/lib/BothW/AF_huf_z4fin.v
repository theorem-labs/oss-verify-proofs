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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4m AF_huf_z4f_defs AF_huf_z4kx.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Startup_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_z4fin () := "C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m<z4_sp_boundsK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atI47Corelib4Init9Datatypes6option00I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC35stdpp4base6lookupK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegI45stdpp9bitvector;definitions2bv00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m3Z4MC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m7z4m_stkC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m4Z4F0K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF7rng_subK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K4ELinuxProcessSemantics5Riscv5Instr5instr08C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m6z4_epiC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC46Stdlib9micromega;ZifyClasses5mkrelC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics5Riscv5Instr5instr00c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin7AZ4_DBCc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin?z4f_frame_factsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m7AZ4_M10C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m6AZ4_M7K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedK46Stdlib9micromega=RingMicromega5Psatz07C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_munchK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin:z4f_blocksC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List<firstn_skipnC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit<rw_cells_appI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4kx8z4kx_ctxc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin7z4f_unpC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit39x2_bytes'C5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4fast=z4_x2tab_factC46Stdlib5Lists4List:length_mapc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin;z4f_slot112c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin7z4f_dtlC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKitAbytes_of_unsignedK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Arr@u64arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64arr_readC35stdpp7tactics<f_equal_helpK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u64arr_store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u64arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr:upd_lengthC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_z4fast9z4m_introC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin7z4f_errC46Stdlib4Bool4Bool>negb_false_iffC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK4ELinuxProcessSemantics5Riscv5Instr5aluop02I46Stdlib;setoid_ring<Ring_polynom3Mon00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_gec5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin8z4f_nextC56Stdlib6ZArith6BinInt1Z6ltb_ltc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin7z4f_ctxc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin<z4m_step_dstK46Stdlib;setoid_ring<Ring_polynom5PExpr03C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4kx4z4_LK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin8z4f_lastC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4kx4z4_TC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4fin8z4f_tailC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eq".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition AZ4_DBC : Z := 151050438420815295.     (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac z4_u64_sok ARR i :=
  lazymatch type of ARR with u64arr ?segs ?mx ?A ?ws =>
    let a := cur_mem_addr in
    pose proof (u64arr_store_ok segs mx A ws i a ARR ltac:(rewrite ?upd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK
  end.
Ltac z4_u64_store ARR i :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mx ?a (le8 ?v)) _) =>
    lazymatch type of ARR with u64arr ?segs mx ?A ?ws =>
      let E := addr_expr a in
      let ARR' := fresh "ARR" in
      assert (ARR' : u64arr segs (write_to_mem mx (wa E) (le8 v)) A (upd ws (Z.to_nat i) v));
      [ replace (wa E) with (wa (A + 8 * i)) by (unfold wa; f_equal; lia);
        apply (u64arr_write segs mx A ws i v ARR); rewrite ?upd_length; lia
      | clear ARR; store_done; rename ARR' into ARR ]
    end
  end.

Ltac z4f_br := try (rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
  rewrite ?(Z.mod_small 0) by lia; rewrite ?Z.mod_small by lia;
  repeat match goal with
  | |- context [(?a <? ?b)] => first [rewrite (proj2 (Z.ltb_ge a b)) by lia | rewrite (proj2 (Z.ltb_lt a b)) by lia]
  end; cbn [Z.b2z Z.lxor negb]; rewrite ?Z.mod_small by lia;
  repeat match goal with
  | |- context [(?a =? ?b)] => first [rewrite (proj2 (Z.eqb_neq a b)) by lia | rewrite (proj2 (Z.eqb_eq a b)) by lia]
  end; cbn [negb]).

Section CANSEC1. Context {rc : runConstT}.
Section Z4FIN.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl lo : Z) (src : list Z) (cbs : list byte) (pdt pb : aptr) (SBL SBH : Z) (cells : list deltX2).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -528).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HDB : In (HB pb DST dcap) LB.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TOK : x2_table_ok cells 11.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^11)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 8192.
  Hypothesis MTL : 11 <= mtl <= 12.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis SG : 3 * seg < dcap.
  Hypothesis NSM : 10 <= n < 2^26.
  Hypothesis SBB : SBL <= SS /\ SS + n <= SBH.
  Hypothesis SBA : ablk SBL SBH /\ SBL mod 8 = 0.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DJ1 : KXGoM.apart DST dcap DT DTL.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  Hypothesis UDT : unpoisoned m0 DT (DT + DTL).
  Hypothesis UDB : unpoisoned m0 DST (DST + dcap).
  Hypothesis USB : unpoisoned m0 SBL SBH.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WDT : rng RNG DT DTL.
  Hypothesis WDB : rng RNG DST dcap.
  Hypothesis WSB : rng RNG SBL (SBH - SBL).
  Hypothesis WDTS : rng RNG (shad DT) (shlen (DTL + 7)).
  Hypothesis WDBS : rng RNG (shad DST) (shlen (dcap + 7)).
  Hypothesis WSBS : rng RNG (shad SBL) (shlen (SBH - SBL + 7)).

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation Z4M := (AF_huf_z4m.Z4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Notation KH pc mm k prev x1 x8 x9 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 x26 x28 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 k) (Z_to_bv 64 seg) (Z_to_bv 64 64) x8 x9 (Z_to_bv 64 prev)
             x11 x12 x13 (Z_to_bv 64 (SP + -136)) (Z_to_bv 64 (SP + -256)) (Z_to_bv 64 AZ4_DBC) (Z_to_bv 64 8)
             x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 0x20d84) x26 (Z_to_bv 64 2147450880) x28 (Z_to_bv 64 2) (Z_to_bv 64 4) x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma z4f_frame_facts : 0x1000 <= SPF /\ SP <= 2^47 /\ lo + 8192 <= SP /\ DST + dcap <= SPF /\ SS + n <= SPF
                          /\ DT + DTL <= SPF /\ 0 <= DST /\ 0 < DT.
Proof using All.
  pose proof (z4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as SPB.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HDT) as (BD1 & BD2 & BD3).
  pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HDB) as (BE1 & BE2 & BE3).
  cbn [ab_addr ab_size] in *.
  destruct SBA as (SBA1 & SBA2). destruct SBB as (SBB1 & SBB2).
  pose proof (Nat2Z.is_nonneg (length src)) as NN.
  unfold ablk, ABase.AIMG_HI, ABase.KLS, HUF_DEC_STACK_A in *. lia.
Qed.

  (* [comment removed for export] *)
  Lemma z4f_done : forall mm w136 ws (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    Z4M mm w136 ws ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) FR (Z_to_bv 64 0x87738) fc None mm (seg_rom bsegs)).
Proof using All.
  intros mm w136 ws x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 HZ.
  assert (ST : stk bsegs mm lo (SP + -104)) by (eapply AF_huf_z4m.z4m_stk; eauto).
  pose proof z4f_frame_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  unfold AF_huf_z4m.Z4M in HZ.
  destruct HZ as (_ & _ & _ & _ & R24 & _ & _ & _ & _ & _ & RFS & MI & MU & WM).
  unfold AF_huf_z4m.Z4F0 in R24. replace (SPF + 24) with (SP + -504) in R24 by lia.
  do 10 zstep.
  rewrite bv_eqb_neq; cycle 1.
  { intros E; apply (f_equal bv_unsigned) in E; rewrite !Z_to_bv_unsigned in E; unfold bv_wrap, bv_modulus in E;
    rewrite !Z.mod_small in E by lia; lia. }
  cbn [negb].
  eapply AF_huf_z4m.z4_epi; eauto.
Qed.

  Lemma z4f_dtl : 8196 <= DTL.
Proof using All.
  unfold DTABLE_BYTES, HufHarness.DT_BYTES.
  assert (2^11 <= 2^mtl) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

  Lemma z4f_blocks : AIMG_HI <= DT /\ DT + DTL <= ATOP /\ DT mod 16 = 0 /\ AIMG_HI <= DST /\ DST + dcap <= ATOP /\ DST mod 16 = 0
                      /\ ablk DST (DST + dcap) /\ AIMG_HI <= SBL /\ SBH <= ATOP.
Proof using All.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (_ & (TB1 & TB2 & TB3 & TB4) & _).
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDB) as (_ & (DB1 & DB2 & DB3 & DB4) & _).
  destruct SBA as (SBA1 & SBA2).
  unfold ablk, ABase.AIMG_HI, ABase.KLS in *.
  repeat split; try lia.
Qed.

  (* [comment removed for export] *)
  Lemma z4f_unp : forall mm, munch DW m0 mm ->
    unpoisoned mm DT (DT + DTL) /\ unpoisoned mm DST (DST + dcap) /\ unpoisoned mm SBL SBH.
Proof using All.
  intros mm MU.
  pose proof z4f_blocks as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof z4f_frame_facts as FF.
  pose proof z4f_dtl as DTL8.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  destruct SBA as (SBA1 & SBA2). destruct SBB as (SBB1 & SBB2).
  unfold ablk, ABase.AIMG_HI, ABase.KLS in *.
  repeat split; (eapply unpoisoned_munch; [eassumption | exact MU |]);
    cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia;
    repeat split; try exact I; Z.div_mod_to_equations; lia.
Qed.

  (* [comment removed for export] *)
  Lemma z4f_slot112 : forall mm w136 ws, Z4M mm w136 ws -> rw_cells bsegs mm (SPF + 128) [C8 (Z_to_bv 64 (DT + 4))].
Proof.
  intros mm w136 ws HZ. unfold AF_huf_z4m.Z4M in HZ.
  destruct HZ as (_ & _ & _ & _ & _ & _ & R128 & _).
  exact (proj1 (proj1 (Startup_kit.rw_cells_app bsegs mm (SPF + 128) [C8 (Z_to_bv 64 (DT + 4))] [C8 w136]) R128)).
Qed.

  (* [comment removed for export] *)
  Lemma z4f_ctx : forall mm w136 ws, Z4M mm w136 ws ->
    z4kx_ctx RNG mm SPF (DT + 4) DT (DT + DTL) DST dcap SS n SBL SBH.
Proof using All.
  intros mm w136 ws HZ.
  pose proof (z4f_slot112 mm w136 ws HZ) as R1.
  unfold AF_huf_z4m.Z4M in HZ.
  destruct HZ as ((buf & BU & BL) & BS & BT & ST1 & RF0 & ST2 & R128 & U64 & WL & ST3 & RFS & MI & MU & WM).
  pose proof z4f_blocks as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof z4f_frame_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof z4f_dtl as DTL8.
  pose proof (z4f_unp mm MU) as (U1 & U2 & U3).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (z4_x2tab_fact mm (DT + 4) cells TOK ltac:(rewrite <- ECB; exact BT)) as TF.
  destruct SBA as (SBA1 & SBA2). destruct SBB as (SBB1 & SBB2).
  unfold z4kx_ctx.
  repeat match goal with |- _ /\ _ => split end.
  all: try assumption.
  all: try (exists cbs; split; [exact BT | exact LCB]).
  all: try (eexists; split; [exact BU | rewrite ?length_map, ?map_length; exact BL]).
  all: try (eexists; split; [exact BS | rewrite ?length_map, ?map_length; reflexivity]).
  all: try (first [ eapply rng_sub; [exact WDT | lia | lia] | eapply rng_sub; [exact WSB | lia | lia]
                  | eapply rng_sub; [exact WSK | lia | lia] ]).
  all: try (replace (DT + DTL - DT) with DTL by lia; exact WDTS).
  all: unfold ablk, ABase.AIMG_HI, ABase.KLS, KXGoM.apart in *; try lia.
Qed.

  (* [comment removed for export] *)
  Lemma z4m_step_dst : forall mm mm' w304 ws,
    Z4M mm w304 ws -> munch [(DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    (exists obuf' : list byte, u8arr bsegs mm' DST obuf' /\ zlen obuf' = dcap) ->
    Z4M mm' w304 ws.
Proof using All.
  intros mm mm' w304 ws HZ MU' WM' MI' (obuf' & OB' & OL').
  pose proof z4f_frame_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof z4f_dtl as DTL8.
  unfold AF_huf_z4m.Z4M in *.
  destruct HZ as ((buf & BU & BL) & BS & BT & ST1 & RF0 & ST2 & R128 & U64 & WL & ST3 & RFS & MI & MU & WM).
  repeat match goal with |- _ /\ _ => split end.
  all: try exact MI'.
  all: try (exists (map bv_unsigned obuf'); rewrite map_map;
            rewrite (map_ext (fun x => Z_to_bv 8 (bv_unsigned x)) (fun x => x)) by (intros; apply Z_to_bv_bv_unsigned);
            rewrite map_id; split; [exact OB' | rewrite ?length_map, ?map_length; exact OL']).
  all: try (eapply wmono_trans; eassumption).
  all: try (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']]; cbn; unfold sub_fp; intros; cbn in *; lia).
  all: try (eapply bytes_at_transport; [eassumption | exact MU' |]; rewrite ?length_map, ?map_length, ?LCB;
            cbn [disjoint_from]; unfold KXGoM.apart in *; split; [lia | exact I]).
  all: try (eapply stk_transport_disjoint; [eassumption | exact MU' | exact WM' |];
            cbn [disjoint_from]; split; [lia | exact I]).
  all: try (eapply rw_cells_transport; [eassumption | exact MU' | exact WM' |];
            cbn [disjoint_from cells_size csize Z.of_nat Z4F0]; split; [lia | exact I]).
  all: try (eapply u64arr_transport; [eassumption | exact MU' | exact WM' |]; rewrite WL;
            cbn [disjoint_from]; split; [lia | exact I]).
  all: try exact WL.
  all: try (exists (map bv_unsigned obuf'); split; [| rewrite length_map; exact OL'];
            rewrite map_map, (map_ext _ (fun b => b)), map_id; [exact OB' |];
            intros b; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; apply Z.mod_small; apply bv_unsigned_in_range).
  all: try (pose proof z4f_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9);
            eapply stk_transport_disjoint; [eassumption | exact MU' | exact WM' |];
            cbn [disjoint_from]; split; [unfold KXGoM.apart in *; lia | exact I]).
Qed.

  (* [comment removed for export] *)
  Lemma z4f_err : forall mm w304 ws (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    Z4M mm w304 ws ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) FR (Z_to_bv 64 0x87730) fc None mm (seg_rom bsegs)).
Proof using All.
  intros mm w304 ws x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 HZ.
  assert (ST : stk bsegs mm lo (SP + -104)) by (eapply AF_huf_z4m.z4m_stk; eauto).
  unfold AF_huf_z4m.Z4M in HZ.
  destruct HZ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RFS & MI & MU & WM).
  do 2 zstep.
  eapply AF_huf_z4m.z4_epi; eauto.
Qed.

  (* [comment removed for export] *)
  Section STREAM.
  Variables (k SE OPk : Z) (w136 : word) (ws : list word).
  Hypothesis K4 : 0 <= k < 4.
  Hypothesis HSE : DST <= OPk <= SE.
  Hypothesis HSE2 : SE <= DST + dcap.
  Hypothesis WOP : nth_error ws (Z.to_nat (4 + k)) = Some (Z_to_bv 64 OPk).
  Notation Z4Mk mm := (Z4M mm w136 ws).

  (* [comment removed for export] *)
  Notation STA pc mm x1 x5 x6 x9 a0 a1 a2 a3 x21 x22 x24 x25 x27 x30 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 (Z_to_bv 64 65) (Z_to_bv 64 (DT + 4)) x9 a0 a1 a2 a3
             (Z_to_bv 64 k) (Z_to_bv 64 (SPF + 264)) (Z_to_bv 64 (2^64 - 1 - (DT + 4))) (Z_to_bv 64 9)
             (Z_to_bv 64 (SPF + 176 + 8 * k)) (Z_to_bv 64 OPk) (Z_to_bv 64 SE) x21 x22 (Z_to_bv 64 0x7fff8000) x24 x25
             (Z_to_bv 64 0x20d53) x27 (Z_to_bv 64 2) (Z_to_bv 64 seg) x30 (Z_to_bv 64 64))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Hypothesis CONT : forall mm (x1 x5 x6 x9 a0 a1 a2 a3 x21 x22 x24 x25 x27 x30 : word),
    Z4M mm w136 (upd ws (Z.to_nat (4 + k)) (Z_to_bv 64 SE)) ->
    evtF bsegs RNG POST (STA 0x875d0 mm x1 x5 x6 x9 a0 a1 a2 a3 x21 x22 x24 x25 x27 x30).

  (* [comment removed for export] *)
  Lemma z4f_next : forall p mm (x1 x5 x6 x9 a0 a1 a3 x21 x22 x24 x25 x27 x30 : word),
    Z4Mk mm -> OPk <= p <= SE ->
    evtF bsegs RNG POST (STA 0x875a8 mm x1 x5 x6 x9 a0 a1 (Z_to_bv 64 p) a3 x21 x22 x24 x25 x27 x30).
Proof using All.
  intros p mm x1 x5 x6 x9 a0 a1 a3 x21 x22 x24 x25 x27 x30 HZ HP.
  pose proof z4f_frame_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof z4f_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
  pose proof z4f_dtl as DTL8.
  unfold AF_huf_z4m.Z4M in HZ.
  destruct HZ as ((buf & BU & BL) & BS & BT & ST1 & RF0 & ST2 & R128 & U64 & WL & ST3 & RFS & MI & MU & WM).
  unfold AF_huf_z4m.Z4F0 in RF0.
  pose proof (u64arr_read bsegs mm (SPF + 144) ws (4 + k) (Z_to_bv 64 OPk) (wa (SPF + 176 + 8 * k)) U64
                ltac:(exact WOP) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  assert (DP : 1 <= DST) by (unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
  do 4 zstep. do 4 (z4f_br; zstep). z4f_br.
  replace (p - OPk + OPk) with p by lia.
  z4_u64_sok U64 (4 + k). zstep. z4_u64_store U64 (4 + k).
  assert (HZ' : Z4M m w136 (upd ws (Z.to_nat (4 + k)) (Z_to_bv 64 p))).
  { unfold AF_huf_z4m.Z4M.
    refine (conj (ex_intro _ buf (conj BU BL)) (conj BS (conj BT (conj ST1 (conj RF0 (conj ST2 (conj R128 (conj U64 (conj _ (conj ST3 (conj RFS (conj MI (conj MU WM))))))))))))).
    rewrite upd_length; exact WL. }
  destruct (Z.eq_dec p SE) as [EP | NP].
  - subst p. zstep. z4f_br.
    replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
    change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
    eapply CONT; exact HZ'.
  - zstep. rewrite bv_eqb_Z, !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
    rewrite !Z.mod_small by lia. rewrite (proj2 (Z.eqb_neq p SE)) by exact NP. cbn [negb].
    eapply z4f_err; exact HZ'.
Qed.


  (* [comment removed for export] *)
  Lemma z4f_last : forall p mm (x1 x5 x6 x9 a0 a1 a3 x21 x22 x24 x25 x27 x30 : word),
    Z4Mk mm -> OPk <= p <= SE ->
    evtF bsegs RNG POST (STA 0x87558 mm x1 x5 x6 x9 a0 a1 (Z_to_bv 64 p) a3 x21 x22 x24 x25 x27 x30).
Proof using All.
  intros p mm x1 x5 x6 x9 a0 a1 a3 x21 x22 x24 x25 x27 x30 HZ HP.
  pose proof z4f_frame_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof z4f_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
  assert (DP : 1 <= DST) by (unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
  pose proof (z4f_ctx mm w136 ws HZ) as CTX.
  destruct (Z_le_gt_dec SE p) as [GE | LT].
  - zstep. z4f_br.
    replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
    change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
    eapply z4f_next; [exact HZ | lia].
  - zstep. z4f_br.
    replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
    change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
    eapply (AF_huf_z4kx.z4_L POST RNG mm FR fc); [exact CTX | lia | lia |].
    intros mm' b0 b1 b3 MU' WM' MI' OB'.
    eapply z4f_next; [eapply z4m_step_dst; eauto | lia].
Qed.

  (* [comment removed for export] *)
  Lemma z4f_tail : forall (fuel : nat) p mm (x1 x5 x6 x9 a0 a1 a3 x21 x22 x24 x27 x30 : word),
    Z4Mk mm -> OPk <= p -> p + 2 <= SE -> SE - p < Z.of_nat fuel ->
    evtF bsegs RNG POST (STA 0x875e0 mm x1 x5 x6 x9 a0 a1 (Z_to_bv 64 p) a3 x21 x22 x24 (Z_to_bv 64 (SE - 2)) x27 x30).
Proof using All.
  intros fuel; induction fuel as [|fuel IH]; intros p mm x1 x5 x6 x9 a0 a1 a3 x21 x22 x24 x27 x30 HZ HP HP2 HF; [lia|].
  pose proof z4f_frame_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof z4f_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
  assert (DP : 1 <= DST) by (unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
  pose proof (z4f_ctx mm w136 ws HZ) as CTX.
  eapply (AF_huf_z4kx.z4_T POST RNG mm FR fc); [exact CTX | lia | lia |].
  intros mm' b0 b1 b3 c6 c30 nb len MU' WM' MI' OB' NB LEN.
  assert (HZ' : Z4Mk mm') by (eapply z4m_step_dst; eauto).
  destruct (Z_le_gt_dec (p + len + 2) SE) as [GO | EX].
  - zstep. z4f_br.
    replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
    change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
    eapply IH; [exact HZ' | lia | lia | lia].
  - zstep. z4f_br. zstep.
    replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
    change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
    eapply z4f_last; [exact HZ' | lia].
Qed.

  (* [comment removed for export] *)
  Lemma z4f_t : forall p mm (x1 x5 x6 x9 a0 a1 a3 x21 x22 x24 x27 x30 : word),
    Z4Mk mm -> OPk <= p <= SE ->
    evtF bsegs RNG POST (STA 0x87554 mm x1 x5 x6 x9 a0 a1 (Z_to_bv 64 p) a3 x21 x22 x24 (Z_to_bv 64 (SE - 2)) x27 x30).
Proof using All.
  intros p mm x1 x5 x6 x9 a0 a1 a3 x21 x22 x24 x27 x30 HZ HP.
  pose proof z4f_frame_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof z4f_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
  assert (DP : 1 <= DST) by (unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
  destruct (Z_le_gt_dec (p + 2) SE) as [GO | EX].
  - zstep. z4f_br.
    replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
    change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
    eapply (z4f_tail (S (Z.to_nat (SE - p)))); [exact HZ | lia | lia | lia].
  - zstep. z4f_br.
    replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
    change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
    eapply z4f_last; [exact HZ | lia].
Qed.

  End STREAM.

End Z4FIN.
End CANSEC1.
