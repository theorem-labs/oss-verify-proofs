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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_ax1 AF_huf_ax1b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax1c () := "C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2Cnth_error_firstn_ltC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4list00I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common5KXTac:find_fieldK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic3notK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX19x1_nbBitsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX17x1_byteC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit29x1_bytes'C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List9nth_errorC47Corelib4Init3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2>x1_bytes'_nth0C47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission6Common5KXTacBztab_fact_bytes_atC47Corelib5Lists7ListDef3nthK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultI47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1c5AX1HKC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax14AX1MC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax17ax1_unpC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax1:ax1_blocksC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax1=ax1_sp_boundsC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax18ax1_outbC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okK47Corelib5Lists7ListDef6Forall01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk08K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp05K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03C5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac;read_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC47Corelib4Init3Nat3addC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission6Common5KXTac>read_ranges_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr04K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zle_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac<idx_facts_okC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxm_execC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC5ARocqVerifyHarness?AgentSubmission6Common5KXMem;kx_u8arr_exC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZK46Stdlib9micromega5Tauto8GFormula02C56Stdlib5Arith8PeanoNat3Nat3ltbC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:kx_stk_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC57Corelib7BinNums6PosDef3Pos;of_succ_natK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltK4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1b:ax1_tail0bC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax17ax1_endC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFMC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01C47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202C46Stdlib9micromega;ZifyClasses7rew_iffC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00C56Stdlib6ZArith4Znat5Nat2Z6inj_leI6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00K47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I46Stdlib5Lists4List6Exists00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1c6ax1_d3c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1c6ax1_d2c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1c6ax1_d1".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).


Section CANSEC1. Context {rc : runConstT}.
Section AX1C.
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

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ax1_ztab : forall mm, bytes_at bsegs mm (DT + 4) cbs -> ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)].
Proof using All.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax1c ()) ["CANSEC1"; "AX1C"] "p'0h07__sat21h11Hh27__sat19h34__x1h44__p1h57__sat25h67__sat23h74__x2h87__sat20h97__sat22h:7__sat24h;4__x3h<2H0h=2H1h>7__arithh?4__ffh@8__varmaphA5__withB1ahC4cstrhD5cstr0hE5cstr1hF7__sat26hG7__sat18hH4__p2hI7__sat17hJ4__x4hK1bi001bhL2HahM4__x5hN7__sat27hO2HfhP4__p3hQ4__p4hR4__p5hS4__x6hT3H17hU1ei011ehV1xhW3z17hX2E0hY3H18hZ4__p6h[4__p7h\7__sat28h]3fhih^3floh_1ih`1zi021zha3z18hb2CEhc2EIhd2H2he2HVhf2Hihg2NBhh2TChi3TCKhj2TLhk2_Hhl3cbshm2mmhn1ni031nho1oi041ohp1ri051rhq1yi061pp%0p%1p&0p&1p;1p;2p;4p;3p;6p;5p;<p;:p;7p;8p;Bg0000R0p4p710g001;R1p4p710R2p8p1001Yp4p70R3p1002Op4p710p8P3p1002kp4p710R3p8p1003Lp4p7210P2p8p10048p4p70P3p8g004nj11Tg005Sk10STg0061k10GTg006TS00k10?Tg0076j1ATg007Tk204Tg0081k40fTg008fk20cTg009ij22Tg00:Ej2zTg00:bk20XTg00;]R3j16Tg00<=k20MTg00=?R2j24Tg00=ZR4j2<Tg00>7R5k20LTg00>Wj4oTg00?7j1>Tg00?\k10ITg00@<j3aTg00@\k60DTg00AWk10_Tg00BUk10]Tg00CKj2{Tg00Ckj1|Tg00DPS01j1bTg00E0k202Tg00EZj2ZTg00FKj27Tg00Fkj2wTg00GSj3vTg00H7R6j25Tg00HSk210Tg00I4k207Tg00INk10RTg00Ink10|Tg00JLk10vTg00K7j2gTg00KZk20NTg00L=j3sTg00L`k20mTg00MBk20kTg00Mnj38k10;Tg00NHk30iTg00Ngk40hTP1j6eTg00OYk20gTg00PUj2HTg00Q7k20eTg00QYk20KTg00R6R1k20dTg00RYk10JTg00S;j2dTg00SUk60HTg00T2k10ETg00TKk10bTg00Tik60aTg00UMk30`Tg00Unj23Tg00VKj2mTg00W<k10CTg00WZk20BTg00X;j1OTg00XZj3nTg00YCk20ATg00Ylk30^Tg00ZOk40\Tg00[0k50[Tg00[\k40>Tg00\7j1WTg00]8k10=Tg00^7j2yTg00^]k10ZTg00_^k30YTg00`=j3xTg00`[k20<Tg00a2k20WTg00aUk30VTg00b2m<0:Tg00bWj2hTg00c9k20TTg00cbk301Tg00dKk209Tg00e7k403Tg00ebR7k20QTg00f:k30~Tg00g@j6tTP0k50{Tg00g\k20xTg00hBk30uTg00hek20tTg00iTk40sTg00ink20rTg00jMm:0qTg00kQk40pTg00kmk20oTg00lKj4_Tg00m6j7qTg00mZj3lTg00nCk205Tg00noj4fTg00oMk60nTg0101k700Tg010Uj8rTg0119k20lTg011Vm<0wTg012;mB0jTg012ak20yTg013;k70zTf2R0f1R8'2f0R9'4p=Gg013_R:/29p=01589,40p=Vg014=R;P8P9g015=H0pp=E%>9#>#>#>p=X%19#1p=}%19#1#1#1p>0@%19#1#1#1#1#1#1#1p=k15:9p=:g016?R<00o9p=]P0g016]R=g017<R>P>g017\R?P<P8g018<R@P9C_g018cRAFqp=@P<P<P8P9Cop=pA8<:9p=\f4RBf3RC?x08;89p=QA8<89p=91289,40p=cA8<9:p>0FP0P=P>P>P?P<P8g019CRDP9C_PAFqp=Y20A<9p=MAl<89p=Bg019jREg01:VRF-058;a9p=DP<P0P8P9Cfp=PP<P<PBPCP0CfP8P9Cfp=K20N<9p=SP8P=P>P>P?P9J0np=;f5RGP=P>P>P?PBP=P>P>P?PCP0K00P8P9Grp=Lf6RHP=P>P>P?PGPBPCP=P>P>P?P0P8P9GrGrp=FP0P=P>P>P?P<P8g01;BRIP9C_PAFqp=U12:8/49p=I20l:9p==207<9p=[P<g01;iRJP<P<P3PBQ01PCg01<HP0P8P9N<0wp=jPJPJPJP<P<P<g01=5Q01Q01Q01P4g01=UPGPBPCP0P8P9NB0jp>0U129:p=JA8<9:,48p=NA8<08,4C00y9p=CAl<899l<0p=RAl<89005Fp=u2059Fp>11AaE899aE0p>08P<PBPCP<P0P8P9CfCfp=iP<P8PDP9C_p=^PCP=P>P>P?P0P8P=P>P>P?P9PAFqK00p=?P0P=P>P>P?P8P9K00p=TP0P=P>P>P?P8P9K0zp=`PJP<P7Q01P6g01>8PGPBPCP0P8P9N<0:p>0PPCP=P>P>P?P0P8P9Grp=~AaE89p>0}P<P8PIP9C_p>0OP<P8P@P9C_p>06g01>ZR@#1RI#1R6#1R7#1RA#1RD#1S02$0SRF$0G&0S7R4$0GR3$0?RK[g01??RLP9p,2DT%A6+04R6p,3cbsS03H0fp,3TOKp,5cellsRMp,2tlRN+0cP2%A@ROg01@4,2N7GNS04%AIRP/zNRQ20X;M'2S05%09S06?V9Q%68/EM-0MN[^_<S07'4S08PLPCP61<PQRRPP20L<<RS00L<RTPSP<P<P<P:P:Co%>@RU#1RV#1S09#ARWCo&0IT3aRTJ0DP9Q04Q08P2Q05Q07PLf7RXP6PRPPPTJ0DP9Q05Q07PLf:RLP6PRPPPTQ03f9R6P<PR12R9X`<p,2rcRY$0_S0:%>US0;#X#X#XRU#1#X#X#1#}$0@#k#k#A&0]YRY%>U#X#X#1#}$0@#k#k#A,2Y3GS0<p,3src,{<RY#|S0=%bY#0S0>Q03,{3RY#|S0?%bYRY#0S0@1{;MS0A#|S0BQ0A#bS0C#0R;p,2sp-02FRF%AARA'ZRU%0F%0A17FA#0[[RA%ADRD,wPRF%:PRZ%0D1zPDR[#:[R\[R]%0PR^g01A<R_AvPD8UWLRD%0[\_^L^R`%>VS0D#1#ARV,wPRa%0V1zPVRb#:[Rc\ZRdAvPV8V_XL^RV%0b\_^L^Rb1wPNRe%0N%:Q[Rf\ZRgAvPN8V_XL^Rh%0Q\_^L^Rip,3SBLRj%A7R7'ZRk%0j%0717j7#0[[R7p,2DCRjp,4dcapRl#0Rm15l[Rl'4R[P2PmPl12RRP9PXg01AX210:P+07PZeRnO1RoPfPLPnO1RpPcf=RqPnO1P\&0IERr&0RERE%]8S0E&0|<Rs&0v<Rt1g<PRu20N<@Rv5s<S0FQ0F3@20mt?RwP9P0g01B>Rxg01B^Ry+0720k90=8xydB0i<:8H0hRyb?b@bAX3<1<P9Rz/2z^3<P9PQO1b>b6b0b2X=lX<mP8P9O2n2001000000121000000bBbIbGb2b8b0b9b6b:bEbDbCb1PYp,3LCBEe%00RY?V0R&0?SRz17CP00gT1p08,HS3817BPRT-0e:%\T20K:T+0d17GP-0K:PxP117HP#\PxPzP8P<P<P:PWCo,HSRx&0JSS0Gn01000000200001pXH,HSS0H58zPKP3Q03%6L1H39S0IDQ20249R1f8RT,215G6'4XK3,d3]OP817XP#\S0JQ0H98zxPzP<Q00PSP<P9P5P<P<P<P9P9n2001106000120102102PWn10110400021010600XUzPx1pTX,HSS0KP9J0H19WXPzP<Q00PSP<P9P5P<P<P<P9P8n2001106000120102102P:n10110400021010600XUzPx1p6T,HSP8J0H%\6%\LP<P:f;S0L,9WPKP3Q03f?S0M#6Q0IDQRx121q9G01'4XK3,d3[X^<19WLP<PW%01S0N?c18,4xXK3,d3X]<Q0:Q0<Q0=Q0>Q0?Q0@Q0BP;PUPAPFP]PDP`fDS0O/ZPQ0O#0fFS0P/7P#0\^[PaPdPVPbPePgPhPiPkP7PjP[P2PmPl&0FPRx$0EP9PoPfPpPcf>R5PnO1P\PrPE&0b<R{PsPtP=P>P>P?1g<:R?9YtuJ0aPwPyb?b@bAg01C>S0Q\xP9b>b:b0b2X=lX<mP8P9O2n2001000000120000000bBbIbGb2b8b0b9b6b:b5bEbDbCb1:0`qP13qP,<PS0R17qP+04,9qQ0:Q0<Q0=Q0>Q0?Q0@Q0BP;PUPAPFP]PDP`fERx/ZPS0S%0xfGS0T/7P#0\^[S0UQ0P/mPS0VQ0P#0fHR=/3P#0\^[S0WPaPdPVPbPePgPhPiPkP7PjP[P2PmPlfNS0XQ0X/3PS0Y,<P'9P9PoPfPpPcQ0MPnO1S0ZP\p-0Rn&0C@-0B<S0[g01C[R@#OS0\#OS0]#OR|#OS0^#MR}5n<S0_%M|S0`20A<@R@'BS0a'BQ0[Q0`5n<S0b/B@S0c,B}/Dr'DPEP{P0%]CS0d9P{BP8P{PB%]BS0e?PB{PBP{DKDKPsPt%SIR|9s<uS0f%>IS0g#1S0h#>#SR~60^<9Ytv&0J>R>PtAYt?~P>PtPtA@t?vS0i1;tHP>PtPt1g<OS0jQ0;#1#SS0;5@tS0k1;tXS0lP>Q0f9YtvELELFFPwPyb?b@bAX3<X7<X;<XJ<X4nWH1<P8S0m004C,99%\B14YHAGOGT1<PGS0n,9B[[[[^3<^7<^;<^J<^4n^HnP912NWS0ofURY/5RS0p17YPPN13YPPYQ0TfMS0TfRS0qf[S0rO:b>b5b0b2XdlX=mP8P9O2n2001000000121000000bBbIbGb2b8b0b9b6b:b5bFbEbDbCb<b1Q0R,9q135PS0R#0S0sQ0R/5QS0RP5PPQ0:Q0<Q0=Q0>Q0?Q0@Q0BP;PUPAPFP]PDP`Q0SQ0UQ0VQ0WPaPdPVPbPePgPhPiPkP7PjP[P2PmPlQ0X#0S0tP9PoPfPpPcQ0ZP\PrPEQ0EPsPtPtQ0i1;tCP>Q0iELPwPyb?b@bAX3<X4nQ06/48%08[^3<^4nP9Q0pPYQ0qO3b>b5b0b2X=lX<mP8P9O2n2001000000121000000bBbIbGb2b8b0b9b6b:b5bFbEbDbCb1Q0:Q0<Q0=Q0>Q0?Q0@Q0BP;PUPAPFP]PDP`Q0SQ0UQ0VQ0WPaPdPVPbPePgPhPiPkP7PjP[P2PmPlPZP9PoPfPpPcQ0ZP\PrPEP{PsAUt?uPwPyb?b@bAPZP9b>b5b0b2X=lX<mP8P9O2n2001000000120000000bBbIbGb2b8b0b9b6b:b5bFbEbDbCb1RZH0\P5PPPQPZQ0:Q0<Q0=Q0>Q0?Q0@Q0BP;PUPAPFP]PDP`Q0SQ0UQ0VQ0WPaPdPVPbPePgPhPiPkP7PjP[P2PmPlQ0X/5RP9PoPfPpPcQ0ZP\PrPE%]0S0W?P8{PsPtPt1;tBQ0f9UtvRZP>PZELPwPyb?b@bAX3<X7<X4nQ0m9V091<P0,58[^3<^7<^4nP9%0YPQPYQ0qO4b>b5b0b2X=lX<mP8P9O2n2001000000121000000bBbIbGb2b8b0b9b6b:b5bFbEbDbCb1I0[H0>Q0sQ0R'4f@S0RQ0M/3PRYP9O2%6Y/EM-0MNP2Q0R/3P#6/EMRY#WRZ12ZN'I&0=YRYQ02#}#ARZ,5Y'IPKP3Q03fBS02#6Q0IDQQ0N?c1WS0N'4XK3,d3P9Q02/3P#6/EM#WRY12YN'IfCS0s/3P#6/EM$0=RY15YZ'IP3PKP3Q03%6xS0mQ0IDQQ0N'4XK3Q0O/3P#6S0N/EM#WS0f,y4RYPKP3Q03Q0O#6S0V1H3YDQ2024YS0UQ0U/2W'I&0R3S0S%6RS0p&0ZMS0E60Y3S0uQ0SPKP3P9Q0m13xPRY#6S0v/EM#W,y4,H3S0wDQWlPKQ0EQ0V5x3Q0w98K9XoKQ0:Q0<Q0]Q0v+0<S0wQ0m58J%=YS0S,<PS0x%=xS0y'9PJP<&0;JQ01&0;<%b8%b9'9A8J8920W8940VXqJXVJQ0wQ0xQ0]PP%[PQ0vQ0SP9XV<S0S%=9XV<S0xPYPY%[YDjJ0UQ0mQ0yQ0SQ0xPxPx%[xDjS01N<0:Q0=Q0>Q0?Q0@Q0BP;1h:=%:=%==RYP=%J=/NYCCfIS0z#=P<fJS0{/3PRY,h:%:Y%=YS0|PY%JYQ0|'NCCfKS0}/3P#=P<PUPAPFP]PDP`fOS0~/ZPS10Q0~#0S11fQS12/7P#0\^[S13fPS14/mPS15Q14#0Q0q/3P#0\^[S0qPaPdPVPbPePgPhPiPkP7PjP[P2PmPlf<S16,<P/95P9PoPfPpPcQ0ZP\20T<PS17Q0^#OS0^#OS18#MRY601<S19Q0_;R@&0CI-0B<=n<YS1:?R}@Q0^#MRIQ0`'BQ18#OS18#O#M,u@+09Q19Q0_Q0c3RS191BY}Q0\#M/B@S0\$11+09+09Q19Q1:Q0a7R}Q17Q18#M601<S18Q0b,BI'uS0bQ0b<08r'D'D408'D'DPEP{P0Q0d9P{GP8P{PGQ0e?PG{PGP{PG%]GS19PGP{DiDKDKPsPtPtQ0g#>S0g#>#SS0b9Ut?PtQ0b,^vC?Q0b=@t?AYtv?S1:5Tt5`tP>PtPtAUt?~Pt1^|~C?PtA@t~?Pt1^|?C?5`tP>PtQ0b9s<u9Yt~S0cP>PtA@t?~S0_Q0l5TtP>PtPtQ0k1;tTS0lP>Q0F=Yt|ELFFFFPwPyb?b@bAX3<X7<X;<XJ<XM<X4nXHn%:BS0FP9PB%JBS0`/N9CCQ0FP0PBQ0`/N0CC1<PH,9G1IHTAGOHLQ0n/9H[[[[[^3<^7<^;<^J<^M<^4n^HnP9Q0of_S0n/5RS0`Q0n/3PS0FQ0nPNPxQ0sQ0OQ0PQ12f\S0^feS1;O<b>bNb6b0X=lX<mP8P9O2n2001000000121000000bBb2b8b0b9b6b:b5bFbNb\babYbWbTbEbDbCH03b1Q0]Q0N+0<Q0V58JPJQ0wPKP3Q0EP9Q0P/3PS0w#6S0N/EM#W,y4,H3DQXnJQ0vQ0:Q0<Q0NQ0A+0QQ0w#=RJQ0C'5Q0NPJQ0SQ0xQ0wQ0wQ0w#[DjQ0AQ0CQ0C#[J0PQ0=Q0>Q0?Q0@Q0BP;Q0z/3PRJ,h:%:J%=JS0zPJ%JJQ0z'NCCQ0|P<PUPAPFP]PDP`Q0X/ZPQ0tQ14/7P#0\^[Q0~/mPQ11Q12/3P#0\^[PaPdPVPbPePgPhPiPkP7PjP[P2PmPlQ16Q0C'5P9PoPfPpPcQ0ZP\Q0]#M/B@RJ9RYIARI}J/Dr'DPEP{PHQ19PCP{DiP0P{PH%]HS0]PBP{DiP8P{DKPsPtPtQ0;9@t?P>Q09#SRJ9Ut?C~S09P>PtPtQ0lPtQ0g#1#SS0g,^vC?1;t6Q1:5TtS1:5`tP>PtPt1;tLS0;Q0g=UtJP>PtPtQ0h#1#S9@t?S0hQ0L,;tS0gP>PtA@tJ|P>PtQ0kQ16,;tS115TtP>AUtv|S0tFFELELFFPwPyb?b@bAX3<X7<X;<XJ<XM<XS<X4nXHnXPnXQnXRn%0CS0X%:C[S0|PXP8PH1NT8S0zCCAVLXBQ16,IX12HGQ0M9GOT15HX[[[[[[^3<^7<^;<^J<^M<^S<^4n^Hn^Pn^Qn^RnP9Q0of^S0M/5RQ0M/3PS0A#0Q0A#JQ0A#:Q0AQ0MPNPQQ0CQ0sPCQ0OQ0~Q0rf`fdOAb>bFb9b8X=lX<mP8P9O2n2001000000121000000bBbGb2b8b0b9b6b:b5bFbNbWbTbEbDbCH03b160~MQ0mP9Etb1Q0uQ0V5x3P3Q0EQ0pQ0VQ0:Q0<Q0mQ0p+0QQ0y%=RS0V'5Q0mQ0yQ01Q0pQ0VQ0SQ0xPRPR%[RDjJ0PQ0=Q0>Q0?Q0@Q0BP;1h:R%:RS0xQ0VPR%JRQ0V'NCCQ0VP<Q0{,h:Q0{#:Q0{#=R:Q0{Q0{#J/N:CCQ0}#=P<PUPAPFP]PDP`Q10Q13Q15Q0qPaPdPVPbPePgPhPiPkP7PjP[P2PmPlQ16/55P9PoPfPpPcQ0ZP\Q18/uIR:Q18Q0[=n<IRI=RY@'uQ17>01<}Q0a'B9RYI20}:r'D408PEQ0d9P{HP0Q0e9P{HP8P{PHQ19?PH{PHP{PHQ0]PHP{DiDKDKPsPtQ09P>PtPtQ0lPt1^v~C?Q1:5`tP>PtPtQ0;PtAs<uJRu,^|C?A@tu?Q0g5Tt5`tP>PtPtQ11PtQ0b00OJC?P>PtQ0cP>PtQ0_1;tq5TtP>PtPtQ0k1;t5P>Q0tELFFFFFFPwPyb?b@bAX3<X7<X;<XJ<XM<XS<X4nXHnXPnXQnXRnXZnX[nQ0|PXP8PGQ0zCCPLPC1<PBR5%J5Q0L'4CCAVqTG1<P6,9TQ0R,I6Q029GO615XT[[[[[[[^3<^7<^;<^J<^M<^S<^4n^Hn^Pn^Qn^Rn^Zn^[nP9Q0oQ0`Q0F#0&0FxQ0xQ0n#JQ0n#:Q0FQ0nPNPQPxQ0sPCQ0OQ0PQ14Q12Q0^Q1;ODb>bNb6b0X=lX<mP8P9O2n2001000000121000000bBb2b8b0b9b6b:b5bFbNb\babYbWbTbEbDbCH03b1I0{EeQ03p,3ECBEeP<Q0f-0x4RxQ06?c9WX`<RQP<Q0fPQQ0:Q0<Q0=Q0>Q0?Q0@Q0BP;PUPAPFP]PDP`Q0}/ZPRQQ0}#0Q0T/7P#0\^[RTfLRX/mPRq%0XQ0Y#0\^[R^PaPdPVPbPePgPhPiPkP7PjP[P2PmPlfT/3P#6/EM#WRX#0R5?cXWP9PoPfPpPcQ0ZP\Q0\,B}/DrRrPEP{PCQ0dPCP{DiPCP{P8P{PCQ0WPCP{DKDKR{PsPtPtQ0iPtQ0D#SR}-06vC?RJP>PtQ0h1;tG5TtRGP>PtPtQ0j=@t}Pt1g<WRu-06}C?R}P>PtQ0iPt206vuC?C~FFPwPyb?b@bAX3<X7<X;<X4nQ06?c98RuQ0X/4BRB12CWR?9GOCROQ0X/4?[[[^3<^7<^;<^4nP9Q0r/5RQ0rPNQ0r/3P#6/EM#WP=fXfaO7R=b>b5b0b2X=lX<mP8P9O2n2001000000121000000bBbIbGb2b8b0b9b6b:b5bFbEbDbCb1Q0f/7ZQ0fQ0:Q0<Q0=Q0>Q0?Q0@Q0BP;PUPAPFP]PDP`PQPTPqP^PaPdPVPbPePgPhPiPkP7PjP[P2PmPlAV5XZP9PoPfPpPcQ0ZP\PrPEP{PsPtPJP>PtPGP>PtP}P>PtQ0iPt1g<Z-0OvC?C~FFPwPyb?b@bAX3<X7<X;<X4nQ0X?VCZ\O\B\u^3<^7<^;<^4nP=b>b5b0b2X=lX<mP8P9O2n2001000000121000000bBbIbGb2b8b0b9b6b:b5bFbEbDbCb180uZEe12xW,IxeQ0UQ0f-0t4EeH0>H0sWkWgP8P9O2n2001000000121000000b1bebcQ0LP9EtW1Q0LP9EtW1P9O1b1P9O1b1WOWXP9O1Q0J$0EQ0GQ0H58zPzQ0GQ00PSPnP9Q0QP_n10110400021000000XUzg01D:Q0KP9EtQ0QPKP3Q03Q0L#6Q0IDQ12169GL1'4XK3,d300r9b1WOWXP9O1n10210010500021110110103P0O1bKbpWOWfX]<X^<X_<N:0qWiWhP8P9O2n2001000000121000000W1WjP8P9O2n2001000000121000000b1WbWmo"). Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Ltac ax1_bdj := unfold flat, estart, elenZ; cbn [a_base a_off]; ax1_ez2;
    repeat match goal with |- context [bv_unsigned (edenot ?E (EAlu ALU_SRL ?x ?s))] =>
      lazymatch s with ELit _ => fail | _ => idtac end;
      let H := fresh "IDX" in
      assert (H : 0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 2^tl)
        by (apply kx_srl_tl_gen; [ax1_ez2; f_equal; lia | lia]);
      let w := fresh "w" in set (w := bv_unsigned (edenot E (EAlu ALU_SRL x s))) in *; clearbody w
    end;
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (3 mod 64) with 3;
    Z.div_mod_to_equations; lia.

  Ltac ax1_body_post j :=
    kx_post_regs_keep;
    lazymatch goal with H : u8arr bsegs ?mm DST (map _ ?b), HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ mm _ DST b H HL) as (buf' & OUT' & LB'); clear H end;
    lazymatch goal with H : u8arr bsegs ?mm SPF (map _ ?b), HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ mm _ SPF b H HL) as (fb' & FB' & LFB2); clear H end;
    lazymatch goal with H : munch [(lo, SP); (DST, DST + dcap)] m0 ?mm |- _ =>
      let MUW := fresh "MUW" in let WMr := fresh "WMr" in
      pose proof (munch_refl [(SPF, SPF + 24); (DST + j, DST + j + 4)] mm) as MUW; pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SPF, 24); (DST + j, 4)]; kx_munch_wins H [(SPF, 24); (DST + j, 4)] end;
    kx_post_mem_free;
    lazymatch goal with |- context [mem_denot ?E ?mm ?l] => let EM1 := fresh "EM1" in remember (mem_denot E mm l) as m1 eqn:EM1 end;
    unfold KXGoM.apart in DJ1, DJ2, DJ3;
    lazymatch goal with MUW' : munch [(SPF, SPF + 24); (DST + j, DST + j + 4)] ?mm ?m1', WMr' : wmono bsegs ?mm ?m1' |- _ =>
      transport_after_call bsegs mm m1' MUW' WMr' end.

  Ltac ax1_body_rng :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ ?r13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      repeat match r13 with context [bv_unsigned (ev ?E ?k)] =>
        lazymatch goal with H : _ <= bv_unsigned (ev E k) <= _ |- _ => fail | _ => idtac end;
        let H := fresh "TV" in kx_range (EVar k) H end end.

  Ltac ax1_body_exit j bc bc_lo bc_hi d_lo d_hi :=
    kx_runFm [AX1_RL; AX1_TX] 30%nat
      [KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange bc bc_lo bc_hi; KZRange j 0 (2^32); KZRange dcap 4 (2^32);
       KZRange (dcap - j) d_lo d_hi; KZRange DT 4096 (2^47 - 8192); KZRange DST 4096 (2^47); KZRange SPF 4096 (2^47);
       KZRange (DST + j) 4096 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z));
    [ax1_side ..];
    kx_post_regs; cbn [mem_denot]; ax1_lstfix;
    eapply (A1 ax1_texit); [lia | lia | eassumption | unfold AX1F; split; [eassumption | split; eassumption]].

  Lemma ax1_body : forall mm fb P fl bc j (x1 x11 x14 x22 x23 x24 x25 x28 : word),
    AX1M' mm -> FRM' mm fb -> 0 <= j <= dcap -> 4 <= dcap -> (fl = 0 \/ (fl = 1 /\ bc <= 7)) -> ALINV' P bc ->
    (j + 4 <= dcap -> forall mm' fb' bc' (x10 x12 x14' x23' x24' x25' x28' : word),
       AX1M' mm' -> FRM' mm' fb' -> ALINV' P bc' ->
       evtF bsegs RNG POST (LST AX1_RL mm' x1 x10 (Z_to_bv 64 P) x12 (Z_to_bv 64 bc') x14' (j + 4) x22 x23' x24' x25' x28')) ->
    evtF bsegs RNG POST (LST AX1_HD mm x1 (Z_to_bv 64 P) x11 (Z_to_bv 64 fl) (Z_to_bv 64 bc) x14 j x22 x23 x24 x25 x28).
  Proof using All.
    intros mm fb P fl bc j x1 x11 x14 x22 x23 x24 x25 x28 HM (FB & LFB & FS) HJ HD4 HFL (HBC & HP) KB.
    pose proof HM as HM0.
    ax1_lfacts. ax1_ldfacts.
    pose proof (ax1_ztab mm CBS) as ZT.
    destruct HFL as [-> | (-> & HB7)]; [ax1_body_exit j bc 0 64 0 (2^32) |].
    destruct (Z_lt_le_dec (dcap - j) 4) as [JL|JH]; [ax1_body_exit j bc 0 7 0 3 |].
    kx_runFm [AX1_RL; AX1_TX] 200%nat
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange tl 1 12; KZRange (2^tl) 2 4096;
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)];
       KZRange bc 0 7; KZRange j 0 (2^32); KZRange dcap 4 (2^32); KZRange (dcap - j) 4 (2^32);
       KZWr (DST + j) 4; KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
       KZDisj (DST + j) 4 (DT + 4) (2 * 2^tl); KZDisj (DST + j) 4 SPF 24;
       KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24;
       KZRange DT 4096 (2^47 - 8192); KZRange DST 4096 (2^47); KZRange SPF 4096 (2^47); KZRange (DST + j) 4096 (2^47 - 4)]
      [(DT + 4, 2 * 2^tl); (SPF, 24)] [(DT + 4, 2 * 2^tl); (DST + j, 4); (SPF, 40)] [(DT + 4, 2 * 2^tl); (DST + j, 4)].
    all: ax1_side.
    all: try (lazymatch goal with |- flat _ _ _ /\ _ => ax1_bdj end).
    ax1_body_post j. ax1_lstfix.
    ax1_body_rng.
    eapply KB; [lia | | | unfold ALINV; split; [lia | exact HP]].
    - unfold AX1M. split; [exists buf'; split; [exact OUT' | first [assumption | unfold zlen in *; rewrite LB'; assumption | lia]] |].
      repeat (split; [assumption|]); assumption.
    - unfold AX1F. split; [exact FB' | split; [rewrite LFB2; exact LFB | assumption]].
  Qed.

End AX1C.
End CANSEC1.
