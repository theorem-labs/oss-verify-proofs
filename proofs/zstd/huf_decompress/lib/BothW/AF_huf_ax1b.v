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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_ax1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax1b () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2>neg_desc_shiftC56Stdlib6ZArith6BinInt1Z4onesK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax14AX1MC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax17ax1_unpC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax1:ax1_blocksC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax1=ax1_sp_boundsC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax18ax1_outbI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib5Lists4List:length_mapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk08K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp05K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03C5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac;read_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common5KXTac>read_ranges_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr04K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zle_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac<idx_facts_okC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxm_execC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC5ARocqVerifyHarness?AgentSubmission6Common5KXMem;kx_u8arr_exC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula02C56Stdlib5Arith8PeanoNat3Nat3ltbC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:kx_stk_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC57Corelib7BinNums6PosDef3Pos;of_succ_natK47Corelib4Init5Logic2ex01C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax17ax1_endC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFMC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init5Logic6eq_indK46Stdlib9micromega7EnvRing5PExpr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K47Corelib5Lists7ListDef6Forall02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01C47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr5aluop02I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00K47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0I47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I46Stdlib5Lists4List6Exists00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop05I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1b8ax1_tailc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1b<ax1_neg_descC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6ltb_ltc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1b:ax1_tail0bI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).


(* [comment removed for export] *)
Lemma ax1_neg_desc : forall tl mtl, 1 <= tl <= 12 -> 0 <= mtl <= 255 ->
  Z.land (Z.land (bv_swrap 32 (0 - (tl + 256 * mtl))) 18446744073709551615) 63 = 64 - tl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax1b ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with52Hmh62Hth73mtlh82tlh91zp;1p;2p;3p;4p;6p;7p;8p10000p4p7210g000\R0p4p710p8g001:j12Tg001Xj21Tg0024j13Tg002Yj10Tg003>j27Tg003Yj1UTg0047j2FTg004Tj2DTg0051j29Tg005Nj2ATg0065j2@Tg006Rj2>Tg0072j2;Tg007Pj3<Tg007jj1WTg008Jj1VTg008jj2TTg009Hj1QTg009fj1KTg00:Qj24Tg00;4j2ETg00;Wj1CTg00<9j2BTg00<[j2GTg00=5j2HTg00=aj3ITg00>@j4JTg00?2j4?Tg00@8j1LTg00@Vj1MTg00A4j3NTP0j6OTg00AWj4PTg00BBj7=Tg00Bfj7RTg00CJj8STg00CnR0f1R1g00DLf0R2CPp=5P1g00E3R3g00ERR4P4g00F2R5P2g00FRF=p=6f2R6P3P4P4P5P1P2FRp=:f3R7P3P4P4P5P6P1P2GSp=8g00G2R3#2R8/11%33R9#0#0#2R:,11'7R;g00GWR</11%39#3#3#3R9#3#3#2R=,11'7R>P0%03R?#0#0#0#0R@#U%0@R@#0#0#2/F6,D7,9<'ARA%2?%2@R@'@'>%29,;2f4R9,9@5<0X90P7P6g00H5R?#WRB%V?R?1T01RC%Q0RD%K0RE14081E03R3'5,6E140:,53,6E5:ERF%C4R4PFC81BE5R5P2P6g00HaRFg00IARG'G1H26=<FGdAI0<1CJRGb2b3b4X001182112:'7P;[^00P2P9P6O2b1PBP?PCPDPE140<RC/53,6E140=,53,6E5:ER3P4P3C8P5PGb2b3b4X0011<2112='7P>[^00P2P7P1O2b1C?%L@,;APBP?%M0PD140@,5C,6EP5PGb2b3b411<@P2b19NA@EOW5W6X70X80o"). Qed.

Section Ez2.
Variable zv : list Z.
Variable E : env.
Hypothesis HA : forall j, (j < length zv)%nat -> ev E j = Z_to_bv 64 (nth j zv 0).

Fixpoint ez2 (e : expr) : Z :=
  match e with
  | EAlu ALU_ADD a b => ez2 a + ez2 b
  | EAlu ALU_SUB a b => ez2 a - ez2 b
  | EMd M_MUL a b => ez2 a * ez2 b
  | EAlu ALU_XOR a b => Z.lxor (ez2 a mod 2^64) (ez2 b mod 2^64)
  | EAlu ALU_SLTU a b => Z.b2z (ez2 a mod 2^64 <? ez2 b mod 2^64)
  | EAlu ALU_SRL a (ELit sh) => (ez2 a mod 2^64) / 2^(sh mod 64)
  | EAluw ALU_SRL a (ELit sh) => if Z.eqb sh 3 then (ez2 a mod 2^32) / 8 else ez zv E e
  | _ => ez zv E e
  end.

Lemma ez2_ok : forall e, edenot E e = Z_to_bv 64 (ez2 e).
Proof.
  induction e as [z | j | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | sx0 lo0 n0 e IHe | sx1 k1 i1 n1];
    try exact (ez_ok zv E HA _).
  - destruct op; try exact (ez_ok zv E HA _).
    + cbn [edenot ez2]. rewrite IHa, IHb. exact (ez_ok zv E HA (EAlu ALU_ADD (ELit (ez2 a)) (ELit (ez2 b)))).
    + cbn [edenot ez2]. rewrite IHa, IHb. exact (ez_ok zv E HA (EAlu ALU_SUB (ELit (ez2 a)) (ELit (ez2 b)))).
    + cbn [edenot ez2]. rewrite IHa, IHb. rewrite alu_sltu, v_sltu_b2z, !Z_to_bv_unsigned. reflexivity.
    + cbn [edenot ez2]. rewrite IHa, IHb. rewrite alu_xor. unfold v_xor. rewrite !Z_to_bv_unsigned. reflexivity.
    + destruct b as [sh | | | | | | |]; try exact (ez_ok zv E HA _).
      cbn [edenot ez2]. rewrite IHa. exact (ez_ok zv E HA (EAlu ALU_SRL (ELit (ez2 a)) (ELit sh))).
  - destruct op; try exact (ez_ok zv E HA _).
    destruct b as [sh | | | | | | |]; try exact (ez_ok zv E HA _).
    cbn [ez2]. destruct (Z.eqb_spec sh 3) as [-> | NE]; [| exact (ez_ok zv E HA _)].
    cbn [edenot]. rewrite IHa. rewrite w_srlw. unfold v_srlw. f_equal.
    rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (3 mod 2^Z.of_N 64 mod 32) with 3. rewrite Z.shiftr_div_pow2 by lia.
    change (2^Z.of_N 64) with (2^64). change (2^Z.of_N 32) with (2^32). change (2^(Z.of_N 32 - 1)) with (2^31). change (2^3) with 8.
    Z.div_mod_to_equations. lia.
  - destruct op; try exact (ez_ok zv E HA _).
    cbn [edenot ez2]. rewrite IHa, IHb. exact (ez_ok zv E HA (EMd M_MUL (ELit (ez2 a)) (ELit (ez2 b)))).
Qed.
End Ez2.

Lemma ax1_eqflag : forall A B, A mod 2^64 <> B mod 2^64 ->
  (Z.lxor (1 mod 2^64) (Z.b2z (Z.lxor (A mod 2^64) (B mod 2^64) mod 2^64 <? 1 mod 2^64) mod 2^64) mod 2^Z.of_N 64
     =? 0 mod 2^Z.of_N 64) = false.
Proof.
  intros A B NE.
  pose proof (Z.mod_pos_bound A (2^64) ltac:(lia)) as RA. pose proof (Z.mod_pos_bound B (2^64) ltac:(lia)) as RB.
  pose proof (Z_lxor_range _ _ RA RB) as RX.
  assert (X : Z.lxor (A mod 2^64) (B mod 2^64) <> 0) by (intro HX; exact (NE (proj1 (zb_lxor_eq0 _ _) HX))).
  rewrite (Z.mod_small (Z.lxor (A mod 2^64) (B mod 2^64)) (2^64)) by lia.
  replace (Z.lxor (A mod 2 ^ 64) (B mod 2 ^ 64) <? 1 mod 2 ^ 64) with false by (symmetry; apply Z.ltb_ge; change (1 mod 2^64) with 1; lia).
  vm_compute. reflexivity.
Qed.

Ltac ax1_ez2 := do 3 (try lazymatch goal with |- context [edenot ?E _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      rewrite ?(ez2_ok zv E (kE_atoms zv xs));
      let na := eval vm_compute in (length zv) in
      cbv [ez2 ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb Z.eqb Pos.eqb]
    end end).
Ltac ax1_dj2 := unfold flat, estart, elenZ; cbn [a_base a_off]; ax1_ez2;
  rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (3 mod 64) with 3;
  Z.div_mod_to_equations; lia.
Ltac ax1_br := unfold branch_taken; ax1_ez2; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  first [ apply ax1_eqflag; rewrite ?Z.mod_small by lia; lia
        | first [ apply Bool.negb_true_iff, Z.ltb_ge | apply Z.ltb_lt | apply Bool.negb_false_iff, Z.ltb_lt | apply Z.ltb_ge
                | apply Bool.negb_true_iff, Z.eqb_neq | apply Z.eqb_eq | apply Bool.negb_false_iff, Z.eqb_eq | apply Z.eqb_neq ];
          Z.div_mod_to_equations; lia ].
Ltac ax1_side := try (lazymatch goal with
  | |- flat _ _ _ /\ _ => ax1_dj2
  | |- branch_taken _ _ _ = _ => ax1_br
  end).
Ltac kx_clear := repeat match goal with
  | H : know_ok _ _ _ _ |- _ => clear H
  | H : log_flat _ _ |- _ => clear H
  | H : forall j, (j < _)%nat -> ev _ j = _ |- _ => clear H
  end;
  repeat match goal with X := kx_env _ _ |- _ => clear X end;
  repeat match goal with X := kx_vals _ _ _ _ |- _ => clear X end.

Section CANSEC1. Context {rc : runConstT}.
Section AX1B.
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

  Notation A1 l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      pdt SBL SBH AH HDT HOUT LOA LOS SPT SP16 TOK ECB LCB MTL TLM DC NSM S16 SBB SBA BYS DJ1 DJ2 DJ3 UDT UDB USB
                      WSK WIM WDT WSB WDTS WSBS WDB WDBS) (only parsing).
  Notation AX1M' mm := (AX1M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m0 DST dcap SS DT lo src cbs mm).
  Notation FRM' mm fb := (AX1F sp SS mm fb).

  (* [comment removed for export] *)
  Ltac ax1_tail_run q lo hi :=
    kx_runFm [AX1_TL; AX1_END] 100%nat
          [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange tl 1 12; KZRange (2^tl) 2 4096;
           KZWr (DST + q) 1; KZWr SPF 24; KZDisj (DST + q) 1 (DT + 4) (2 * 2^tl); KZDisj (DST + q) 1 SPF 24;
           KZDisj SPF 24 (DT + 4) (2 * 2^tl);
           KZRange DT 4096 (2^47 - 8192); KZRange q 0 (2^32); KZRange dcap 1 (2^32); KZRange (dcap - q) lo hi;
           KZRange (DST + q) 4096 (2^47 - 1); KZRange SPF 4096 (2^47)]
          [(DT + 4, 2 * 2^tl); (SPF, 24)]
          [(DT + 4, 2 * 2^tl); (DST + q, 1); (SPF, 40)]
          [(DT + 4, 2 * 2^tl); (DST + q, 1)].

  Ltac ax1_tail_post q :=
    kx_post_regs_keep;
    lazymatch goal with H : u8arr bsegs ?mm DST (map _ ?b), HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ mm _ DST b H HL) as (buf' & OUT' & LB'); clear H end;
    lazymatch goal with H : u8arr bsegs ?mm SPF (map _ ?b), HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ mm _ SPF b H HL) as (fb' & FB' & LFB2); clear H end;
    lazymatch goal with H : munch [(lo, SP); (DST, DST + dcap)] m0 ?mm |- _ =>
      let MUW := fresh "MUW" in let WMr := fresh "WMr" in
      pose proof (munch_refl [(SPF, SPF + 24); (DST + q, DST + q + 1)] mm) as MUW; pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SPF, 24); (DST + q, 1)]; kx_munch_wins H [(SPF, 24); (DST + q, 1)] end;
    kx_post_mem_free;
    lazymatch goal with |- context [mem_denot ?E ?mm ?l] => let EM1 := fresh "EM1" in remember (mem_denot E mm l) as m1 eqn:EM1 end;
    unfold KXGoM.apart in DJ1, DJ2, DJ3;
    lazymatch goal with MUW' : munch [(SPF, SPF + 24); (DST + q, DST + q + 1)] ?mm ?m1', WMr' : wmono bsegs ?mm ?m1' |- _ =>
      transport_after_call bsegs mm m1' MUW' WMr' end.

  Ltac ax1_facts :=
    pose proof (A1 ax1_sp_bounds) as SB; pose proof (A1 ax1_blocks) as BK; pose proof (A1 ax1_outb) as OB;
    lazymatch goal with HM : AX1M' ?mm |- _ =>
      destruct HM as ((buf & OUT & LBF) & SRCB & CBS & STK & FRC & MI & MU & WM);
      destruct (A1 ax1_unp mm MU) as (UDT' & UDB' & USB') end;
    destruct BK as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6);
    pose proof ATOP_range as AT; unfold ATOP_MIN, ATOP_MAX in AT; unfold ABase.AIMG_HI, KLS in *;
    unfold AX1_TL, AX1_TS, AX1_T0, AX1_TX, AX1_END, AX1_KSB, AX1_KT15, DTABLE_BYTES, HufHarness.DT_BYTES in *;
    assert (TL1 : 1 <= tl <= 12) by (destruct TOK as (TT & _); unfold HUF_TABLELOG_MAX in TT; lia);
    assert (P2 : 2 <= 2^tl <= 4096) by (split; [replace 2 with (2^1) by reflexivity | replace 4096 with (2^12) by reflexivity]; apply Z.pow_le_mono_r; lia);
    assert (PT : 2^tl <= 2 * 2^mtl) by (replace (2 * 2^mtl) with (2^(mtl+1)) by (rewrite Z.pow_add_r by lia; lia); apply Z.pow_le_mono_r; lia);
    assert (LSRC : zlen (map (Z_to_bv 8) src) = n) by (rewrite length_map; reflexivity); lazymatch goal with HL : zlen ?b = dcap, HO : u8arr _ _ DST (map _ ?b) |- _ => assert (LBF' : zlen (map (Z_to_bv 8) b) = dcap) by (rewrite length_map; exact HL) end; lazymatch goal with HL : zlen ?b = 24 |- _ => assert (LFB' : zlen (map (Z_to_bv 8) b) = 24) by (rewrite length_map; exact HL) end.

  Ltac ax1_dfacts := pose proof (WDB ltac:(lia)) as WDB1; pose proof (WDBS ltac:(lia)) as WDBS1;
    lazymatch goal with BK6 : 0 < dcap -> _ |- _ => destruct (BK6 ltac:(lia)) as (B1 & B2 & B3 & B4) end.

  (* [comment removed for export] *)
  Lemma ax1_tail : forall (cnt : nat) q mm fb (x1 x5 x6 x7 x11 x12 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    Z.of_nat cnt = dcap - q -> 0 <= q < dcap -> AX1M' mm -> FRM' mm fb ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + q))
                               (Z_to_bv 64 (DST + q)) x11 x12 (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (dcap - q))
                               (Z_to_bv 64 AX1_KT15) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 2)
                               (Z_to_bv 64 AX1_KSB) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) x21 x22 x23 x24 x25 s10 s11
                               x28 x29 x30 x31)
                        FR (Z_to_bv 64 AX1_TL) fc None mm (seg_rom bsegs)).
  Proof using All.
    induction cnt as [|cnt IH]; intros q mm fb x1 x5 x6 x7 x11 x12 x21 x22 x23 x24 x25 x28 x29 x30 x31 HC HQ HM (FB & LFB & FS); [lia|].
    ax1_facts. ax1_dfacts.
    destruct (Z.eq_dec (q + 1) dcap) as [QE|QN].
    - ax1_tail_run q 1 1.
      all: lazymatch goal with |- flat _ _ _ /\ _ => ax1_dj2 | _ => idtac end.
      ax1_tail_post q.
      destruct (ax1_fr_join _ _ _ _ _ FB' (eq_trans (f_equal Z.of_nat LFB2) LFB) FS) as (dcs & FRD & CSZ).
      eapply (A1 ax1_end); [eassumption | exact FRD | exact CSZ | eassumption | eassumption | eassumption | eassumption].
    - ax1_tail_run q 2 (2^32).
      all: lazymatch goal with |- flat _ _ _ /\ _ => ax1_dj2 | _ => idtac end.
      ax1_tail_post q.
      replace (DST + q + 1) with (DST + (q + 1)) by lia. replace (dcap + - q + -1) with (dcap - (q + 1)) by lia.
      replace (- DT + -5) with (-1 * DT + -5) by lia.
      eapply IH; [lia | lia | | exact (conj FB' (conj (eq_trans (f_equal Z.of_nat LFB2) LFB) FS))].
      unfold AX1M. split; [exists buf'; split; [exact OUT' | rewrite LB'; exact LBF] |].
      repeat (split; [assumption|]); assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ax1_tail0b : forall j mm fb (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    0 <= j < dcap -> AX1M' mm -> FRM' mm fb ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + j))
                               x10 x11 x12 x13 x14 x15 x16 x17
                               (Z_to_bv 64 AX1_KSB) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl))
                               x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                        FR (Z_to_bv 64 AX1_TS) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros j mm fb x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 HJ HM (FB & LFB & FS).
    pose proof HM as HM0.
    ax1_facts. ax1_dfacts.
    kx_runFm [AX1_TL] 30%nat
      [KZRange tl 1 12; KZRange mtl 1 12; KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange (dcap - j) 1 (2^32);
       KZRange DST 4096 (2^47); KZRange DT 4096 (2^47 - 8192)]
      (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
    kx_post_regs. cbn [mem_denot].
    lazymatch goal with |- context [Z_to_bv 64 (- tl + ?k)] =>
      replace (Z_to_bv 64 (- tl + k)) with (Z_to_bv 64 (64 - tl))
        by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; Z.div_mod_to_equations; lia) end.
    replace (- DT + -5) with (-1 * DT + -5) by lia. try replace (dcap + DST) with (DST + dcap) by lia.
    eapply (ax1_tail (Z.to_nat (dcap - j))); [lia | lia | exact HM | exact (conj FB (conj LFB FS))].
  Qed.

  (* [comment removed for export] *)
  Lemma ax1_tail0 : forall j mm fb (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    0 <= j <= dcap -> AX1M' mm -> FRM' mm fb ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + j))
                               x10 x11 x12 x13 x14 x15 x16 x17
                               (Z_to_bv 64 AX1_KSB) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl))
                               x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                        FR (Z_to_bv 64 AX1_T0) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros j mm fb x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 HJ HM (FB & LFB & FS).
    pose proof HM as HM0.
    ax1_facts.
    destruct (Z.eq_dec j dcap) as [JE|JN].
    - subst j.
      kx_runFmd [AX1_TS; AX1_END] 30%nat [true]
        [KZRange tl 1 12; KZRange mtl 1 12; KZRange dcap 0 (2^32); KZRange DT 4096 (2^47 - 8192)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try (lazymatch goal with |- branch_taken _ _ _ = _ => ax1_ez2; unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned;
                  rewrite Z.ltb_irrefl; reflexivity end).
      kx_post_regs. cbn [mem_denot].
      destruct (ax1_fr_join _ _ _ _ _ FB LFB FS) as (dcs & FRD & CSZ).
      eapply (A1 ax1_end); [eassumption | exact FRD | exact CSZ | eassumption | eassumption | eassumption | eassumption].
    - ax1_dfacts. kx_runFm [AX1_TS; AX1_END] 30%nat
        [KZRange tl 1 12; KZRange mtl 1 12; KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange (dcap - j) 1 (2^32);
         KZRange DST 4096 (2^47); KZRange DT 4096 (2^47 - 8192)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      kx_post_regs. cbn [mem_denot]. try replace (dcap + DST) with (DST + dcap) by lia.
      eapply ax1_tail0b; [lia | exact HM | exact (conj FB (conj LFB FS))].
  Qed.

  Lemma ax1_texit : forall j mm fb (x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    0 <= j <= dcap -> 4 <= dcap -> AX1M' mm -> FRM' mm fb ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 dcap) x9
                               x10 x11 x12 x13 (Z_to_bv 64 (DST + j)) x15 x16 x17
                               (Z_to_bv 64 AX1_KSB) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl))
                               x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                        FR (Z_to_bv 64 AX1_TX) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros j mm fb x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 HJ HD4 HM (FB & LFB & FS).
    pose proof HM as HM0.
    ax1_facts. ax1_dfacts.
    destruct (Z.eq_dec j dcap) as [JE|JN].
    - kx_runFm [AX1_TS; AX1_END] 40%nat
        [KZRange tl 1 12; KZRange mtl 1 12; KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange (dcap - j) 0 0;
         KZRange DST 4096 (2^47); KZRange DT 4096 (2^47 - 8192); KZRange (DST + j) 4096 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      kx_post_regs. cbn [mem_denot].
      destruct (ax1_fr_join _ _ _ _ _ FB LFB FS) as (dcs & FRD & CSZ).
      eapply (A1 ax1_end); [eassumption | exact FRD | exact CSZ | eassumption | eassumption | eassumption | eassumption].
    - kx_runFm [AX1_TS; AX1_END] 40%nat
        [KZRange tl 1 12; KZRange mtl 1 12; KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange (dcap - j) 1 (2^32);
         KZRange DST 4096 (2^47); KZRange DT 4096 (2^47 - 8192); KZRange (DST + j) 4096 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      kx_post_regs. cbn [mem_denot]. try replace (dcap + DST) with (DST + dcap) by lia.
      eapply ax1_tail0b; [lia | exact HM | exact (conj FB (conj LFB FS))].
  Qed.

End AX1B.
End CANSEC1.
