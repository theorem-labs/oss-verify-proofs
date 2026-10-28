(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Cells.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require PropExec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fa_iface AF_huf_afa AF_huf_afa2 AF_huf_afa3 AF_huf_afa4.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_afa5 () := "C5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invI47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_iface=fast_args_okAI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa7afa_sp0C56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk06K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes6lengthK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega6VarMap1t01C5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_iface?fast_args_postAC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission6Common6KXCell;kx_rwc_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic5proj2K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsK46Stdlib9micromega6VarMap1t03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa:afa_rwc_cbC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC56Stdlib5Arith8PeanoNat3Nat3ltbK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03C47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zk_word_okK46Stdlib5Lists4List7Forall202C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0K47Corelib7Numbers7BinNums8positive03I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litI4ELinuxProcessSemantics5Riscv5Instr5instr00C5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_ifaceDAHUF_FAST_ARGS_STACKK4ELinuxProcessSemantics5Riscv5Instr5aluop01C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa38afa_was0C5ARocqVerifyHarness?AgentSubmission5Plain?RF_huf_fa_iface6jt_lenC56Stdlib6ZArith6BinInt1Z3divC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5nshadC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_munchK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit@rclean_transportC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa8afa_kshzC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9kshz_factC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa7afa_boxC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflK5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk0:K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04C5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7zshz_okC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6zur_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF7zshr_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06C5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula02C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:kx_stk_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wr_at_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<log_apart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_apart_ez_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost9estart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXCell>kx_cell_store8C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC5ARocqVerifyHarness?AgentSubmission6Common6KXPost5ez_okC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_bytes_at_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS<ealign_soundC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26ealignC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z4evenC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa4?afa_even_of_divC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa4@afa_sentinel_addC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z<log2_le_monoC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa48afa_popcK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01C5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_rw_cells_logC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFK47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I47Corelib4Init5Logic5False00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_lec5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa56AFA_J3C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KLOWC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa57afa_wasK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa56AFA_J2C5ARocqVerifyHarness?AgentSubmission5Plain?RF_huf_fa_iface?fast_args_cellsc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa58afa_retx".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Lemma a5_firstn1_skipn : forall (l : list Z) n, (n < length l)%nat -> firstn 1 (skipn n l) = [nth n l 0].
Proof.
  induction l as [|x l IH]; intros n Hn; [cbn in Hn; lia|].
  destruct n as [|n]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hn. lia.
Qed.

Lemma a5_rd1 : forall segs (m : word -> option byte) S (bs : list Z) E j w k,
  bytes_at segs m S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs ->
  ev E j = rdval segs m w 1 false -> w = Z_to_bv 64 (S + k) -> 0 <= k < zlen bs ->
  bv_unsigned (ev E j) = Znth k bs.
Proof.
  intros segs m S bs E j w k HB BY H Hw Hk. subst w. rewrite H. unfold rdval.
  replace (Z_to_bv 64 (S + k)) with (wa (S + Z.of_nat (Z.to_nat k))) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_rdn segs m S _ (Z.to_nat k) 1 HB) by (rewrite length_map; lia).
  rewrite skipn_map, firstn_map, a5_firstn1_skipn by lia.
  assert (R : 0 <= nth (Z.to_nat k) bs 0 < 256).
  { rewrite Forall_forall in BY. apply BY. apply nth_In. lia. }
  unfold Znth. cbn [map extz bytes_le_to_Z]. change (0 ≪ 8) with 0. rewrite Z.lor_0_r.
  rewrite (Z_to_bv_small 8) by (unfold bv_modulus; cbn -[Z.pow]; lia).
  rewrite Z_to_bv_small by (unfold bv_modulus; cbn -[Z.pow]; lia). reflexivity.
Qed.

Lemma a5_byte_rng : forall (bs : list Z) k, Forall (fun c => 0 <= c < 256) bs -> 0 <= k < zlen bs -> 0 <= Znth k bs < 256.
Proof.
  intros bs k BY Hk. unfold Znth. rewrite Forall_forall in BY. apply BY. apply nth_In. lia.
Qed.

Lemma a5_adenot_var : forall E i off z, ev E i = Z_to_bv 64 z -> 0 <= z < 2^64 ->
  adenot E {| a_base := EVar i; a_off := off |} = Z_to_bv 64 (z + off).
Proof.
  intros E i off z H Hz. unfold adenot, PropExec.v_addi. cbn [a_base a_off edenot]. rewrite H, Z_to_bv_small by (unfold bv_modulus; cbn; lia).
  reflexivity.
Qed.

Lemma a5_adenot_ez : forall zv xs a z, 0 <= ez zv (kE zv xs) (a_base a) + a_off a < 2^64 ->
  ez zv (kE zv xs) (a_base a) + a_off a = z -> adenot (kE zv xs) a = wa z.
Proof.
  intros zv xs a z R Hz. apply bv_eq. rewrite adenot_ez by exact R. unfold wa.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite Z.mod_small by lia. exact Hz.
Qed.

Lemma a5_shd_rd : forall segs zv xs (m : word -> option byte) a lo hi x,
  unpoisoned m lo hi -> lo <= x -> x + 1 <= hi ->
  0 <= ez zv (kE zv xs) (a_base a) + a_off a < 2^64 -> ez zv (kE zv xs) (a_base a) + a_off a = shad x ->
  exists bs, rdn segs m (adenot (kE zv xs) a) 1 = Some bs.
Proof.
  intros segs zv xs m a lo hi x U L H R Hz.
  destruct (unp_gran m lo hi x 1 U L ltac:(lia) ltac:(lia)) as (b & Hb & _).
  apply (kx_rd_known_ex segs zv xs m a b (shad x) (shad x + 1)); [| exact R | lia].
  intros s Hs. replace s with (shad x) by lia. exact Hb.
Qed.

Definition a5_ar (P : Prop) : Prop := P.
Ltac a5_clr := lazymatch goal with H : a5_ar _ |- _ => clear - H end.
Ltac a5_lia := a5_clr; unfold a5_ar in *; repeat (match goal with H : _ /\ _ |- _ => destruct H end); Z.div_mod_to_equations; lia.
Ltac a5_zs zv := let na := eval vm_compute in (length zv) in
  cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb].
Ltac a5_fin :=
  try change (2 ^ (3 mod 64)) with 8; try unfold shad, ASHOFF; kx_abstract;
  a5_clr; rewrite ?Z.shiftr_div_pow2 by lia; try change (2 ^ 3) with 8; a5_lia.

Ltac a5_acc :=
  lazymatch goal with
  | |- accP ?RNG ?E (?a, ?n) =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        change E with (kE zv xs);
        match goal with H : rng RNG ?A ?N |- _ =>
          apply (kx_acc_rng zv xs RNG A N a n H ltac:(repeat constructor)); a5_zs zv; a5_fin end
      end
  end.

Ltac a5_rdb HS :=
  lazymatch goal with
  | |- exists bs, rdn ?segs ?m (adenot ?E {| a_base := EVar ?i; a_off := ?off |}) ?k = Some bs =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        change E with (kE zv xs);
        apply (kx_rd_ez segs zv xs m {| a_base := EVar i; a_off := off |} k _ _ ltac:(repeat constructor) HS);
        a5_zs zv; rewrite ?length_map; repeat split; a5_fin
      end
  end.

Ltac a5_rds US :=
  lazymatch goal with
  | |- exists bs, rdn ?segs ?m (adenot ?E ?a) 1 = Some bs =>
      lazymatch a with {| a_base := EAlu ALU_SRL ?X (ELit 3); a_off := _ |} =>
        let b := eval unfold E in E in
        lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
          change E with (kE zv xs);
          apply (a5_shd_rd segs zv xs m a _ _ (ez zv (kE zv xs) X) US); a5_zs zv; a5_fin
        end
      end
  end.

Ltac a5_chk US :=
  lazymatch goal with
  | |- branch_taken BC_LT (edenot ?E (EAlu ALU_SUB (EMd M_MUL (EAlu ALU_SLTU (ELit 0) (EVar ?j))
          (EAlu ALU_ADD (EAlu ALU_ADD (EAlu ALU_AND ?B (ELit 7)) (ELit ?k)) (ELit 1))) (ELit 1)))
        (edenot ?E (EVar ?j)) = true =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let H := fresh "RV" in kx_read_eq j H;
        lazymatch type of H with _ = rdval ?segs ?m (adenot _ ?a) 1 true =>
          change E with (kE zv xs) in H |- *;
          change (EAlu ALU_SUB (EMd M_MUL (EAlu ALU_SLTU (ELit 0) (EVar j))
                   (EAlu ALU_ADD (EAlu ALU_ADD (EAlu ALU_AND B (ELit 7)) (ELit k)) (ELit 1))) (ELit 1))
            with (chk_ob (EVar j) B k);
          apply (chk_ob_unp segs m (kE zv xs) (EVar j) B k _ _ (ez zv (kE zv xs) B) US
                   (ez_ok zv (kE zv xs) (kE_atoms zv xs) B));
          [ a5_zs zv; a5_fin | a5_zs zv; a5_fin | a5_zs zv; a5_fin | a5_lia
          | cbn [edenot]; rewrite H; f_equal; apply a5_adenot_ez; a5_zs zv; a5_fin ]
        end
      end
  end.

Ltac a5_lbr K S bs HS BY :=
  lazymatch goal with
  | |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = _ =>
      let H := fresh "HR" in kx_read_eq j H;
      lazymatch type of H with
      | ev E j = rdval ?segs ?m (adenot E {| a_base := EVar ?i1; a_off := ?off |}) 1 false =>
        lazymatch goal with KXA : forall j, (j < length ?zv)%nat -> ev E j = _ |- _ =>
          let Z1 := fresh "ZR" in
          assert (Z1 : bv_unsigned (ev E j) = Znth K bs);
          [ apply (a5_rd1 segs m S bs E j _ _ HS BY H);
            [ rewrite (a5_adenot_var E i1 off _ (KXA i1 ltac:(apply Nat.ltb_lt; reflexivity))) by (cbv [nth]; a5_lia);
              cbv [nth]; f_equal; a5_lia
            | a5_lia ]
          | clear H;
            unfold branch_taken; cbn [edenot]; rewrite bv_eqb_Z, Z1; change (bv_unsigned (Z_to_bv 64 0)) with 0;
            first [ apply Z.eqb_neq; lia | apply Z.eqb_eq; lia ] ]
        end
      end
  end.

Ltac a5_z :=
  let E := lazymatch goal with
           | |- context [flat ?E _ _] => E | |- context [estart ?E _] => E | |- context [elenZ ?E _] => E end in
  let b := eval unfold E in E in
  lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
    let na := eval vm_compute in (length zv) in
    change E with (kE zv xs); unfold flat;
    repeat match goal with |- _ /\ _ => split end;
    repeat match goal with
    | |- context [estart (kE zv xs) ?a] =>
        rewrite (estart_ez_kE zv xs a); [ | cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; a5_fin ]
    end;
    rewrite ?elenZ_lit by lia;
    cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; a5_fin
  end.

Ltac a5_one HS US :=
  lazymatch goal with
  | |- evtF _ _ _ _ => fail
  | |- region_ok _ _ _ _ => fail
  | |- accP _ _ _ => a5_acc
  | |- exists bs, rdn _ _ (adenot _ {| a_base := EVar _; a_off := _ |}) _ = Some bs => a5_rdb HS
  | |- exists bs, rdn _ _ _ 1 = Some bs => a5_rds US
  | |- branch_taken BC_LT _ _ = true => a5_chk US
  | |- flat _ _ _ => a5_z
  | |- flat _ _ _ /\ _ => a5_z
  | |- branch_taken _ _ _ = _ => w4br
  | |- _ => first [ a5_lia | rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; cbn [cells_size csize]; lia ]
  end.
Lemma a5_add_u : forall z k, 0 <= z -> 0 <= k -> z + k < 2^64 ->
  bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 z) (Z_to_bv 64 k)) = z + k.
Proof.
  intros z k Hz Hk Hzk. pose proof (u_add_eqm (Z_to_bv 64 z) (Z_to_bv 64 k)) as Q. unfold eqm in Q.
  rewrite !Z_to_bv_small in Q by (unfold bv_modulus; cbn; lia).
  destruct Q as (q & Q).
  pose proof (bv_unsigned_in_range 64 (alu64 ALU_ADD (Z_to_bv 64 z) (Z_to_bv 64 k))) as R.
  rewrite Q in R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  rewrite Q. assert (q = 0) by lia. subst q. lia.
Qed.

Lemma a5_adenot_add2 : forall E i1 i2 off z1 z2, ev E i1 = Z_to_bv 64 z1 -> ev E i2 = Z_to_bv 64 z2 ->
  0 <= z1 -> 0 <= z2 -> z1 + z2 < 2^64 ->
  adenot E {| a_base := EAlu ALU_ADD (EVar i1) (EVar i2); a_off := off |} = Z_to_bv 64 (z1 + z2 + off).
Proof.
  intros E i1 i2 off z1 z2 H1 H2 P1 P2 P3. unfold adenot, PropExec.v_addi. cbn [a_base a_off edenot].
  rewrite H1, H2, a5_add_u by lia. reflexivity.
Qed.
Section CANSEC1. Context {rc : runConstT}.

Section AFA5.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (A DST dcap S DT mtl tt tl mtl' : Z) (src : list Z) (ja : list byte) (lo : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis HA : rw_cells bsegs m0 A [CB 152 ja].
  Hypothesis A8 : A mod 8 = 0.
  Hypothesis DESC : bytes_at bsegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 tt; Z_to_bv 8 tl; Z_to_bv 8 mtl'].
  Hypothesis RM1 : 0 <= mtl < 256.
  Hypothesis RTT : 0 <= tt < 256.
  Hypothesis RTL : 0 <= tl < 256.
  Hypothesis RM2 : 0 <= mtl' < 128.
  Hypothesis SRC : bytes_at bsegs m0 S (map (Z_to_bv 8) src).
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis NSM : n < 2^26.
  Hypothesis S0 : 0 < S.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DE : DST + dcap + 8 <= 2^64.
  Hypothesis DT0 : 0 < DT.
  Hypothesis DTL : DT + 4 <= lo.
  Hypothesis SL : 0 < n -> S + n <= lo.
  Hypothesis STK : stk bsegs m0 lo SP.
  Hypothesis LOS : lo <= SP - AHUF_FAST_ARGS_STACK.
  Hypothesis ASP : SP <= A.
  Hypothesis A47 : A + 152 <= 2^47.
  Hypothesis MI : mem_inv bsegs m0.
  Hypothesis UDT : unpoisoned m0 DT (DT + 4).
  Hypothesis USR : 0 < n -> unpoisoned m0 S (S + n).
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= A.
  Hypothesis RHI : A + 152 <= r_hi rstk.
  Hypothesis WFR : rng RNG (SP - AHUF_FAST_ARGS_STACK) AHUF_FAST_ARGS_STACK.
  Hypothesis WA : rng RNG A 152.
  Hypothesis WRS : rrng RNG rstk.
  Hypothesis WDT : rng RNG DT 4.
  Hypothesis WDTS : rng RNG (shad DT) 1.
  Hypothesis WSR : 0 < n -> rng RNG S n /\ rng RNG (shad S) (nshad (n + S mod 8)).
  Hypothesis WIM : rng_aimg RNG.
  
  Hypothesis ART : artcells m0.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis DT8 : DT mod 8 = 0.

  Notation POST := (fast_args_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A DST dcap S DT src tl lo m0).
  Notation FRS := [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation MW := [(SP - AHUF_FAST_ARGS_STACK, SP); (A, A + 152)].

  Ltac a5_crng K S bs HS BY :=
    lazymatch goal with |- 0 <= ?e <= 8 =>
      lazymatch e with context [edenot ?E ?X] =>
        lazymatch X with context [EVar ?j] =>
          let H := fresh "HR" in kx_read_eq j H;
          lazymatch type of H with
          | ev E j = rdval ?segs ?m (adenot E {| a_base := EVar ?i1; a_off := ?off |}) 1 false =>
            lazymatch goal with KXA : forall j, (j < length ?zv)%nat -> ev E j = _ |- _ =>
              let Z1 := fresh "ZR" in
              assert (Z1 : bv_unsigned (ev E j) = Znth K bs);
              [ apply (a5_rd1 segs m S bs E j _ _ HS BY H);
                [ rewrite (a5_adenot_var E i1 off _ (KXA i1 ltac:(apply Nat.ltb_lt; reflexivity))) by (cbv [nth]; a5_lia);
                  cbv [nth]; f_equal; a5_lia
                | a5_lia ]
              | clear H ];
              let lb := fresh "lb" in
              set (lb := Znth K bs) in *;
              cbn [edenot];
              replace (ev E j) with (Z_to_bv 64 lb) by (rewrite <- Z1; apply Z_to_bv_bv_unsigned);
              lazymatch goal with |- 0 <= ?e2 <= 8 =>
                let F := eval pattern lb in e2 in
                lazymatch F with ?f lb =>
                  let BR := fresh "BR" in
                  assert (BR : forall r0, 1 <= r0 < 1 + 255 -> ((0 <=? f r0) && (f r0 <=? 8))%bool = true)
                    by (apply (brute_range (fun r0 => ((0 <=? f r0) && (f r0 <=? 8))%bool) 1 255); vm_compute; reflexivity);
                  specialize (BR lb ltac:(lia)); apply andb_prop in BR; destruct BR as [BR1 BR2];
                  apply Z.leb_le in BR1; apply Z.leb_le in BR2; lia
                end
              end
            end
          end
        end
      end
    end.

  Ltac a5_c14 HC K S bs HS BY :=
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?c) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        assert (HC : 0 <= c <= 8) by first [ lia | a5_crng K S bs HS BY ]
    end.
  Ltac a5_rdz j K S bs HS BY Z1 :=
    let H := fresh "HR" in kx_read_eq j H;
    lazymatch type of H with
    | ev ?E j = rdval ?segs ?m (adenot ?E {| a_base := EAlu ALU_ADD (EVar ?i1) (EVar ?i2); a_off := ?off |}) 1 false =>
      lazymatch goal with KXA : forall j0, (j0 < length ?zv)%nat -> ev E j0 = _ |- _ =>
        assert (Z1 : bv_unsigned (ev E j) = Znth K bs);
        [ apply (a5_rd1 segs m S bs E j _ _ HS BY H);
          [ rewrite (a5_adenot_add2 E i1 i2 off _ _ (KXA i1 ltac:(apply Nat.ltb_lt; reflexivity))
                       (KXA i2 ltac:(apply Nat.ltb_lt; reflexivity))) by (cbv [nth]; a5_lia);
            cbv [nth]; f_equal; a5_lia
          | a5_lia ]
        | clear H ]
      end
    | ev ?E j = rdval ?segs ?m (adenot ?E ?a) 1 false =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        assert (Z1 : bv_unsigned (ev E j) = Znth K bs);
        [ apply (a5_rd1 segs m S bs E j _ _ HS BY H);
          [ change E with (kE zv xs); rewrite (a5_adenot_ez zv xs a (S + K)); [reflexivity | a5_zs zv; a5_fin | a5_zs zv; a5_fin]
          | a5_lia ]
        | clear H ]
      end
    end.

  Ltac a5_lbrz K S bs HS BY :=
    lazymatch goal with
    | |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = _ =>
        let Z1 := fresh "ZR" in a5_rdz j K S bs HS BY Z1;
        unfold branch_taken; cbn [edenot]; rewrite bv_eqb_Z, Z1; change (bv_unsigned (Z_to_bv 64 0)) with 0;
        first [ apply Z.eqb_neq; lia | apply Z.eqb_eq; lia ]
    end.

  Ltac a5_crngz K S bs HS BY :=
    lazymatch goal with |- 0 <= ?e <= 8 =>
      lazymatch e with context [edenot ?E ?X] =>
        lazymatch X with context [EVar ?j] =>
          let Z1 := fresh "ZR" in a5_rdz j K S bs HS BY Z1;
          let lb := fresh "lb" in
          set (lb := Znth K bs) in *;
          cbn [edenot];
          replace (ev E j) with (Z_to_bv 64 lb) by (rewrite <- Z1; apply Z_to_bv_bv_unsigned);
          lazymatch goal with |- 0 <= ?e2 <= 8 =>
            let F := eval pattern lb in e2 in
            lazymatch F with ?f lb =>
              let BR := fresh "BR" in
              assert (BR : forall r0, 1 <= r0 < 1 + 255 -> ((0 <=? f r0) && (f r0 <=? 8))%bool = true)
                by (apply (brute_range (fun r0 => ((0 <=? f r0) && (f r0 <=? 8))%bool) 1 255); vm_compute; reflexivity);
              specialize (BR lb ltac:(lia)); apply andb_prop in BR; destruct BR as [BR1 BR2];
              apply Z.leb_le in BR1; apply Z.leb_le in BR2; lia
            end
          end
        end
      end
    end.

  Ltac a5_c14z HC K S bs HS BY :=
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?c) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        assert (HC : 0 <= c <= 8) by first [ lia | a5_crngz K S bs HS BY ]
    end.

  Ltac a5_c14e HC K S bs HS BY :=
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ ?w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch w with
      | Z_to_bv 64 ?c => assert (HC : 0 <= c <= 8) by first [ lia | a5_crngz K S bs HS BY ]
      | _ =>
          replace w with (Z_to_bv 64 (bv_unsigned w)) by (apply Z_to_bv_bv_unsigned);
          assert (HC : 0 <= bv_unsigned w <= 8) by a5_crngz K S bs HS BY;
          let c := fresh "c3" in set (c := bv_unsigned w) in *
      end
    end.
  Ltac a5_sentv off SENT :=
    lazymatch goal with
    | HLF : log_flat ?E ?log, HKn : know_ok bsegs ?E ?mb ?kn, KA : forall j0, (j0 < length ?zv)%nat -> ev ?E j0 = _ |- _ =>
      let l := eval hnf in log in
      lazymatch l with context [SE {| a_base := _; a_off := off |} _ (EAlu ALU_SLL (EAlu ALU_ADD ?Y (ELit 1)) (EVar ?j))] =>
        let al := eval vm_compute in (ealign kn Y) in
        assert (SENT : bv_unsigned (edenot E (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EVar j))) mod 512 <> 0);
        [ change (edenot E (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EVar j)))
            with (alu64 ALU_SLL (alu64 ALU_ADD (edenot E Y) (Z_to_bv 64 1)) (ev E j));
          apply afa_sentinel_add;
          [ let AL := fresh "AL" in let DV := fresh "DV" in
            destruct (ealign_sound bsegs E mb kn Y HKn) as (AL & DV);
            replace (ealign kn Y) with al in DV by (vm_compute; reflexivity);
            apply (afa_even_of_div _ al); [lia | exact DV]
          | rewrite KA by (apply Nat.ltb_lt; reflexivity); cbv [nth];
            rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); lia ]
        | let SZ := fresh "SENTz" in pose proof SENT as SZ;
          try (let b := eval unfold E in E in
          lazymatch b with kx_env (map (Z_to_bv 64) ?zv') ?xs =>
            let na := eval vm_compute in (length zv') in
            rewrite (ez_ok zv' E (kE_atoms zv' xs) (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EVar j))) in SZ;
            cbv [ez] in SZ; change (length zv') with na in SZ; cbv [nth Nat.ltb Nat.leb] in SZ;
            rewrite ?Z_to_bv_bv_unsigned in SZ
          end) ]
      end
    end.

  Ltac a5_side := try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).

  Lemma a5_stk_rel8 : forall m l0 X v, stk bsegs m l0 X -> rw_cells bsegs m X [C8 v] -> l0 <= X -> stk bsegs m l0 (X + 8).
  Proof. intros m l0 X v H1 H2 H3. exact (stk_release bsegs m l0 X [C8 v] H1 H2 H3). Qed.

  Lemma a5_bvr : forall w : bv 64, 0 <= bv_unsigned w < 2^64.
  Proof. intros w. exact (bv_unsigned_in_range 64 w). Qed.
Ltac a5_log_z zv :=
  let na := eval vm_compute in (length zv) in
  cbn [log_apart_ez log_inside_ez inside]; cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
  repeat (first [exact I | split]); try a5_lia.

Ltac a5_estart_z zv :=
  let na := eval vm_compute in (length zv) in
  lazymatch goal with |- estart ?E ?a = ?A =>
    rewrite (estart_ez zv E (kE_atoms zv _) a);
    [ cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; a5_lia
    | cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; a5_lia ]
  end.

Ltac a5_frame H :=
  lazymatch goal with
  | KXLF : log_flat ?E ?log, HK : know_ok ?segs ?E ?m ?kn |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | bytes_at _ m ?A ?bs =>
          apply (kx_bytes_at_log segs E m log A bs) in H; [ | exact KXLF | change E with (kE zv xs); apply log_apart_ez_ok; a5_log_z zv ]
      | rw_cells _ m ?A ?cs =>
          apply (kx_rw_cells_log segs E m log A cs) in H; [ | exact KXLF | change E with (kE zv xs); apply log_apart_ez_ok; a5_log_z zv ]
      | ro_cells _ m ?A ?cs =>
          apply (kx_ro_cells_log segs E m log A cs) in H; [ | exact KXLF | change E with (kE zv xs); apply log_apart_ez_ok; a5_log_z zv ]
      end
    end
  end.

Ltac a5_munch H :=
  lazymatch goal with
  | KXLF : log_flat ?E ?log, HK : know_ok ?segs ?E ?m ?kn |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | munch ?W ?m0 m =>
          apply (kx_munch_log E W m0 m log) in H; [ | exact KXLF | change E with (kE zv xs); apply log_inside_ez_ok; a5_log_z zv ]
      end
    end
  end.

Ltac a5_cell_gen H W :=
  lazymatch goal with
  | HLF : log_flat ?E ?log |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let na := eval vm_compute in (length zv) in
      lazymatch type of H with
      | rw_cells ?segs m ?A [?c0] =>
          let rec go pre l :=
            lazymatch l with
            | SE ?a W ?v :: ?rest =>
                first [ let Hn := fresh "HC" in
                        assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a W v :: rest)) A
                                       [ltac:(lazymatch W with 8%nat => exact (C8 (edenot E v)) | _ => exact (C4 (edenot E v)) end)])
                          by (first [ eapply (kx_cell_store8 segs E m pre a v rest A)
                                    | eapply (kx_cell_store4 segs E m pre a v rest A) ];
                              [ change (pre ++ SE a W v :: rest) with log; exact HLF
                              | exact H
                              | change E with (kE zv xs); a5_estart_z zv
                              | change E with (kE zv xs); apply log_apart_ez_ok; a5_log_z zv ]);
                        change (pre ++ SE a W v :: rest) with log in Hn;
                        rewrite (ez_ok zv E (kE_atoms zv xs) v) in Hn;
                        cbv [ez] in Hn; change (length zv) with na in Hn; cbv [nth Nat.ltb Nat.leb] in Hn;
                        rewrite ?Z_to_bv_bv_unsigned in Hn;
                        clear H; rename Hn into H
                      | let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest ]
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => fail "a5_cell: no store found for" A
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.
Ltac a5_cell H := a5_cell_gen H 8%nat.
Ltac a5_cell4 H := a5_cell_gen H 4%nat.

Ltac a5_cells_post :=
  repeat match goal with
  | HLF : log_flat ?E ?log, H : rw_cells ?segs ?m ?A [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      let l := eval hnf in log in
      lazymatch A with
      | _ + ?off => tryif kx_log_has_off l off then first [ a5_cell H | a5_cell4 H | a5_frame H ] else a5_frame H
      | _ => first [ a5_cell H | a5_cell4 H | a5_frame H ]
      end
  end;
  try (cbn [cells_size csize]; a5_lia).

Ltac a5_cells_merge :=
  repeat (lazymatch goal with |- rw_cells ?segs ?m ?A (?c :: ?c' :: ?cs) =>
            apply (proj2 (kx_rwc_cons segs m A c (c' :: cs))); split; [eassumption|]; cbn [csize];
            lazymatch goal with
            | |- rw_cells _ _ (?a + ?b + Z.of_nat ?k) _ =>
                tryif is_Zlit b then
                  (let v := eval vm_compute in (b + Z.of_nat k) in replace (a + b + Z.of_nat k) with (a + v) by a5_lia)
                else (let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v)
            | |- rw_cells _ _ (?a + Z.of_nat ?k) _ =>
                let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v
            end end);
  eassumption.

Ltac a5_rwc_norm H :=
  lazymatch type of H with
  | rw_cells _ _ (?a + ?b + Z.of_nat ?k) _ =>
      tryif is_Zlit b then
        (let v := eval vm_compute in (b + Z.of_nat k) in replace (a + b + Z.of_nat k) with (a + v) in H by a5_lia)
      else (let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in H)
  | rw_cells _ _ (?a + Z.of_nat ?k) _ =>
      let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in H
  | _ => idtac
  end.

Ltac a5_cells_split H :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A (?c :: ?c' :: ?cs) =>
      let H1 := fresh "KC" in
      apply (kx_rwc_cons segs m A c (c' :: cs)) in H; destruct H as [H1 H]; cbn [csize] in H; a5_rwc_norm H;
      a5_cells_split H
  | rw_cells _ _ _ [_] => idtac
  end.

  

  Lemma afa_was : rng RNG (2147450880 + Z.shiftr A 3) 19.
Proof using RCL WRS RLO RHI A8.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa5 ()) ["CANSEC1"; "AFA5"] "p;9g02h3l90Tp,2m0p,3RNGp,4rstkp,1Ap,3RCLp,3WRSp,3RLOp,3RHIp,2A8M90o"). Qed.

  Notation CELLS I0 I1 I2 I3 SG b0 b1 b2 b3 w12 w13 w14 :=
    [C8 (Z_to_bv 64 (I1 - 8)); C8 (Z_to_bv 64 (I2 - 8)); C8 (Z_to_bv 64 (I3 - 8)); C8 (Z_to_bv 64 (S + n - 8));
     C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + SG)); C8 (Z_to_bv 64 (DST + 2 * SG)); C8 (Z_to_bv 64 (DST + 3 * SG));
     C8 b0; C8 b1; C8 b2; C8 b3; C8 w12; C8 w13; C8 w14;
     C8 (Z_to_bv 64 I0); C8 (Z_to_bv 64 I1); C8 (Z_to_bv 64 I2); C8 (Z_to_bv 64 I3)] (only parsing).


  
  Definition AFA_J2' : Prop :=
    forall mm (b0 b1 w10 w11 w12 w13 w14 : word) (I0 I1 I2 I3 SG c : Z) (x5 x8 x9 x11 x15 x18 x31 : word),
    I0 = S + 6 -> I1 = I0 + jt_len src 0 -> I2 = I1 + jt_len src 2 -> I3 = I2 + jt_len src 4 ->
    8 <= jt_len src 0 -> 8 <= jt_len src 2 -> 8 <= jt_len src 4 -> I3 + 8 <= S + n ->
    SG = (dcap + 3) / 4 -> 0 < dcap -> 3 * SG < dcap -> tl = 11 -> 0 <= c <= 8 ->
    bv_unsigned b0 mod 512 <> 0 -> bv_unsigned b1 mod 512 <> 0 ->
    rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
    rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
    rw_cells bsegs mm A [C8 (Z_to_bv 64 (I1 - 8)); C8 (Z_to_bv 64 (I2 - 8)); C8 (Z_to_bv 64 (I3 - 8)); C8 (Z_to_bv 64 (S + n - 8));
                         C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + SG)); C8 (Z_to_bv 64 (DST + 2 * SG)); C8 (Z_to_bv 64 (DST + 3 * SG));
                         C8 b0; C8 b1; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14;
                         C8 (Z_to_bv 64 I0); C8 (Z_to_bv 64 I1); C8 (Z_to_bv 64 I2); C8 (Z_to_bv 64 I3)] ->
    bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
    stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880)
                               x8 x9 (Z_to_bv 64 A) x11 (Z_to_bv 64 (I3 - 1))
                               (Z_to_bv 64 S) (Z_to_bv 64 c) x15 (Z_to_bv 64 (S + n - 8)) (Z_to_bv 64 (I3 - 8))
                               x18 (Z_to_bv 64 (DST + 2 * SG)) s4 s5 s6 s7 s8 s9 s10 s11
                               (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (S + n)) (Z_to_bv 64 I3) x31)
                           F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 1772)) fc None mm (seg_rom bsegs)).

  
  Definition AFA_J3 : Prop :=
    forall mm (b0 b1 b2 w11 w12 w13 w14 : word) (I0 I1 I2 I3 SG c : Z) (x5 x8 x9 x11 x15 x17 x18 x30 x31 : word),
    I0 = S + 6 -> I1 = I0 + jt_len src 0 -> I2 = I1 + jt_len src 2 -> I3 = I2 + jt_len src 4 ->
    8 <= jt_len src 0 -> 8 <= jt_len src 2 -> 8 <= jt_len src 4 -> I3 + 8 <= S + n ->
    SG = (dcap + 3) / 4 -> 0 < dcap -> 3 * SG < dcap -> tl = 11 -> 0 <= c <= 8 ->
    bv_unsigned b0 mod 512 <> 0 -> bv_unsigned b1 mod 512 <> 0 -> bv_unsigned b2 mod 512 <> 0 ->
    rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
    rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
    rw_cells bsegs mm A [C8 (Z_to_bv 64 (I1 - 8)); C8 (Z_to_bv 64 (I2 - 8)); C8 (Z_to_bv 64 (I3 - 8)); C8 (Z_to_bv 64 (S + n - 8));
                         C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + SG)); C8 (Z_to_bv 64 (DST + 2 * SG)); C8 (Z_to_bv 64 (DST + 3 * SG));
                         C8 b0; C8 b1; C8 b2; C8 w11; C8 w12; C8 w13; C8 w14;
                         C8 (Z_to_bv 64 I0); C8 (Z_to_bv 64 I1); C8 (Z_to_bv 64 I2); C8 (Z_to_bv 64 I3)] ->
    bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
    stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880)
                               x8 x9 (Z_to_bv 64 A) x11 (Z_to_bv 64 (S + n - 1))
                               (Z_to_bv 64 S) (Z_to_bv 64 c) x15 (Z_to_bv 64 (S + n - 8)) x17
                               x18 (Z_to_bv 64 (DST + 2 * SG)) s4 s5 s6 s7 s8 s9 s10 s11
                               (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (S + n)) x30 x31)
                           F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 2100)) fc None mm (seg_rom bsegs)).

  

  
  Lemma afa_b2 : AFA_J3 -> AFA_J2'.
Proof using All.
  intros K. unfold AFA_J2'.
  intros mm b0 b1 w10 w11 w12 w13 w14 I0 I1 I2 I3 SG c x5 x8 x9 x11 x15 x18 x31 EI0 EI1 EI2 EI3 L0 L2 L4 I3n ESG DC0 SG3 TL HC0 B0 B1
    C40 C32 C24 C16 C08 HAm SRCm STKm MIm MUm WMm.
  pose proof (SL ltac:(lia)) as SLn.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (afa_sp0 sp lo A LOA LOS ASP A47) as SPB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  unfold AHUF_FAST_ARGS_STACK in *.
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof (magree_of_munch bsegs _ m0 mm MUm WMm) as MG.
  unfold rt_got in RGOT. unfold rt_shbase in RSHB.
  pose proof (rw_cells_magree bsegs _ m0 mm _ _ MG RGOT ltac:(intros a Ha; cbn [cells_size csize Nat.add Z.of_nat] in Ha; cbn [outside]; repeat split; lia)) as RGOTm.
  pose proof (rw_cells_magree bsegs _ m0 mm _ _ MG RSHB ltac:(intros a Ha; cbn [cells_size csize Nat.add Z.of_nat] in Ha; cbn [outside]; repeat split; lia)) as RSHBm.
  change (rt_got mm) in RGOTm. change (rt_shbase mm) in RSHBm.
  clear RGOT RSHB RG0 RGRIC RMEM.
  pose proof (USR ltac:(lia)) as USRn. pose proof (WSR ltac:(lia)) as (WSRa & WSRb).
  pose proof (afa_kshz m0 rstk A 152 RCL RLO RHI A8 eq_refl ltac:(lia)) as KSH.
  lazymatch type of KSH with kshz_fact _ ?o ?a ?k => assert (KSHm : kshz_fact mm o a k) end.
  { intros x Hx. rewrite (MUm (Z_to_bv 64 (2147450880 + Z.shiftr x 3))); [apply KSH; exact Hx|].
    rewrite Z_to_bv_small by (unfold bv_modulus; cbn -[Z.pow]; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
    cbn [outside]; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; repeat split; lia. }
  lazymatch type of USRn with ?P _ _ _ => assert (USRm : P mm S (S + n)) end.
  { pose proof USRn as (U0 & U1 & U2). split; [exact U0|]. split; [exact U1|].
    intros G G1 G2 G3. destruct (U2 G G1 G2 G3) as (b & Hb & Hgr). exists b. split; [|exact Hgr].
    rewrite (MUm (wa (ASHOFF + G))); [exact Hb|].
    unfold wa, ASHOFF. rewrite Z_to_bv_small by (unfold bv_modulus; cbn -[Z.pow]; lia). cbn [outside]; repeat split; lia. }
  pose proof afa_was as WAS.
  lazymatch type of WAS with rng _ (?o + Z.shiftr _ 3) _ =>
    assert (WAS2 : rng RNG (o + Z.shiftr A 3) (Z.shiftr (152 + A mod 8 + 7) 3)) by (rewrite A8; exact WAS) end.
  assert (WSRc : rng RNG (shad S) (Z.shiftr (n + S mod 8 + 7) 3)) by exact WSRb.

  assert (KB : 0 <= S + n - 1 - S < n) by lia.
  pose proof (a5_byte_rng src (S + n - 1 - S) BYS KB) as LBR.
  assert (AR : a5_ar (0 < S /\ S + n <= lo /\ lo <= SP - 48 /\ SP <= A /\ A + 152 <= 2^47 /\ n < 2^26 /\
               ATOP + 4096 <= lo /\ ATOP_MIN <= ATOP <= ATOP_MAX /\
               I0 = S + 6 /\ I1 = I0 + jt_len src 0 /\ I2 = I1 + jt_len src 2 /\ I3 = I2 + jt_len src 4 /\
               8 <= jt_len src 0 /\ 8 <= jt_len src 2 /\ 8 <= jt_len src 4 /\ I3 + 8 <= S + n /\ 0 <= c <= 8))
    by (pose proof ATOP_range as ATR0; unfold a5_ar; repeat split; lia).
  unfold ATOP_MIN, ATOP_MAX in AR.
  destruct (Z.eq_dec (Znth (S + n - 1 - S) src) 0) as [LZ|LZ];
  [ let PxS := constr:([AHUF_FAST_ARGS_INIT + 2100] : list Z) in let PxF := constr:(600%nat : nat) in let PxD := eval vm_compute in (true :: repeat false 4096) in let PxK := constr:([KZRange dcap 1 (2^32 - 1); KZRange n 10 (2^26 - 1); KZRange S 1 (2^47); KZRange DST 0 (2^64 - 9); KZRange (DST + dcap) 1 (2^64 - 8); KZRange DT 1 (2^47); KZAlign DT 8; KZRange SP 0x7fff7f801030 (2^47-152); KZRange I0 1 (2^47); KZRange I1 1 (2^47); KZRange I2 1 (2^47); KZRange I3 1 (2^47); KZRange SG 0 (2^30); KZRange c 0 8; KZAlign A 8; KZRange A 1 (2^47); KZWr A 152; KZDisj A 152 S n; KZShZ 2147450880 A 152; KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000] : list kz) in let PxR := constr:([(S, n)] : list (Z * Z)) in let PxW := constr:([(SP - 48, 48); (A, 152); (S, n); (0xb2128, 8); (0xba2f8, 8)] : list (Z * Z)) in let PxU := constr:([(S, n)] : list (Z * Z)) in kx_prepFm PxS PxF PxK PxR PxW PxU; kx_goFL PxD
  | let PxS := constr:([AHUF_FAST_ARGS_INIT + 2100] : list Z) in let PxF := constr:(600%nat : nat) in let PxD := eval vm_compute in (repeat false 4096) in let PxK := constr:([KZRange dcap 1 (2^32 - 1); KZRange n 10 (2^26 - 1); KZRange S 1 (2^47); KZRange DST 0 (2^64 - 9); KZRange (DST + dcap) 1 (2^64 - 8); KZRange DT 1 (2^47); KZAlign DT 8; KZRange SP 0x7fff7f801030 (2^47-152); KZRange I0 1 (2^47); KZRange I1 1 (2^47); KZRange I2 1 (2^47); KZRange I3 1 (2^47); KZRange SG 0 (2^30); KZRange c 0 8; KZAlign A 8; KZRange A 1 (2^47); KZWr A 152; KZDisj A 152 S n; KZShZ 2147450880 A 152; KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000] : list kz) in let PxR := constr:([(S, n)] : list (Z * Z)) in let PxW := constr:([(SP - 48, 48); (A, 152); (S, n); (0xb2128, 8); (0xba2f8, 8)] : list (Z * Z)) in let PxU := constr:([(S, n)] : list (Z * Z)) in kx_prepFm PxS PxF PxK PxR PxW PxU; kx_goFL PxD ].
  all: try a5_lbrz (S + n - 1 - S) S src SRCm BYS.
  all: try (lazymatch goal with |- accP _ _ _ => a5_acc end).
  all: try (lazymatch goal with |- exists bs, rdn _ _ (adenot _ {| a_base := EVar _; a_off := _ |}) _ = Some bs => a5_rdb SRCm end).
  all: try (lazymatch goal with |- exists bs, rdn _ _ _ 1 = Some bs => a5_rds USRm end).
  all: try (lazymatch goal with |- branch_taken BC_LT _ _ = true => a5_chk USRm end).
  all: try (lazymatch goal with |- flat _ _ _ => a5_z | |- flat _ _ _ /\ _ => a5_z end).
  all: try a5_one SRCm USRm.

  all: lazymatch goal with |- evtF _ _ _ _ => (pose proof SRCm as SRC0) | |- _ => idtac end.
  all: lazymatch goal with |- evtF _ _ _ _ => (a5_sentv 80 SENT) | |- _ => idtac end.
  all: lazymatch goal with |- evtF _ _ _ _ => (a5_cells_split HAm) | |- _ => idtac end.
  all: lazymatch goal with |- evtF _ _ _ _ => (a5_cells_post) | |- _ => idtac end.
  all: lazymatch goal with |- evtF _ _ _ _ => (a5_frame SRCm) | |- _ => idtac end.
  all: lazymatch goal with |- evtF _ _ _ _ => (a5_munch MUm) | |- _ => idtac end.
  all: a5_side.
  all: lazymatch goal with |- evtF _ _ _ _ => (kx_post_mem_free) | |- _ => idtac end.
  all: lazymatch goal with |- evtF _ _ _ _ => (lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end) | |- _ => idtac end.
  all: lazymatch goal with |- evtF _ _ _ _ => (kx_post_regs_keep) | |- _ => idtac end.

  all: lazymatch goal with |- evtF _ _ _ _ => (a5_c14e HC (S + n - 1 - S) S src SRC0 BYS) | |- _ => idtac end.
  all: lazymatch goal with |- evtF _ _ _ _ => (try replace (S + n + -1) with (S + n - 1) by lia; try replace (S + n + -8) with (S + n - 8) by lia) | |- _ => idtac end.

  all: try clearbody KXE; try clearbody KXxs.
  all: lazymatch goal with |- evtF _ _ _ _ => (eapply (K m1 b0 b1 _ w11 w12 w13 w14 I0 I1 I2 I3 SG)) | |- _ => idtac end.
  all: try first [ exact TL | exact HC | exact SENT | exact SENTz | assumption ].
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => a5_cells_merge end).
  all: try a5_lia.

Qed.

  
  Lemma afa_b3 : AFA_J3.
Proof using All.
  unfold AFA_J3.
  intros mm b0 b1 b2 w11 w12 w13 w14 I0 I1 I2 I3 SG c x5 x8 x9 x11 x15 x17 x18 x30 x31 EI0 EI1 EI2 EI3 L0 L2 L4 I3n ESG DC0 SG3 TL HC0 B0 B1 B2
    C40 C32 C24 C16 C08 HAm SRCm STKm MIm MUm WMm.
  pose proof (SL ltac:(lia)) as SLn.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (afa_sp0 sp lo A LOA LOS ASP A47) as SPB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  unfold AHUF_FAST_ARGS_STACK in *.
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof (magree_of_munch bsegs _ m0 mm MUm WMm) as MG.
  unfold rt_got in RGOT. unfold rt_shbase in RSHB.
  pose proof (rw_cells_magree bsegs _ m0 mm _ _ MG RGOT ltac:(intros a Ha; cbn [cells_size csize Nat.add Z.of_nat] in Ha; cbn [outside]; repeat split; lia)) as RGOTm.
  pose proof (rw_cells_magree bsegs _ m0 mm _ _ MG RSHB ltac:(intros a Ha; cbn [cells_size csize Nat.add Z.of_nat] in Ha; cbn [outside]; repeat split; lia)) as RSHBm.
  change (rt_got mm) in RGOTm. change (rt_shbase mm) in RSHBm.
  clear RGOT RSHB RG0 RGRIC RMEM.
  pose proof (USR ltac:(lia)) as USRn. pose proof (WSR ltac:(lia)) as (WSRa & WSRb).
  pose proof (afa_kshz m0 rstk A 152 RCL RLO RHI A8 eq_refl ltac:(lia)) as KSH.
  lazymatch type of KSH with kshz_fact _ ?o ?a ?k => assert (KSHm : kshz_fact mm o a k) end.
  { intros x Hx. rewrite (MUm (Z_to_bv 64 (2147450880 + Z.shiftr x 3))); [apply KSH; exact Hx|].
    rewrite Z_to_bv_small by (unfold bv_modulus; cbn -[Z.pow]; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
    cbn [outside]; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; repeat split; lia. }
  lazymatch type of USRn with ?P _ _ _ => assert (USRm : P mm S (S + n)) end.
  { pose proof USRn as (U0 & U1 & U2). split; [exact U0|]. split; [exact U1|].
    intros G G1 G2 G3. destruct (U2 G G1 G2 G3) as (b & Hb & Hgr). exists b. split; [|exact Hgr].
    rewrite (MUm (wa (ASHOFF + G))); [exact Hb|].
    unfold wa, ASHOFF. rewrite Z_to_bv_small by (unfold bv_modulus; cbn -[Z.pow]; lia). cbn [outside]; repeat split; lia. }
  pose proof afa_was as WAS.
  lazymatch type of WAS with rng _ (?o + Z.shiftr _ 3) _ =>
    assert (WAS2 : rng RNG (o + Z.shiftr A 3) (Z.shiftr (152 + A mod 8 + 7) 3)) by (rewrite A8; exact WAS) end.
  assert (WSRc : rng RNG (shad S) (Z.shiftr (n + S mod 8 + 7) 3)) by exact WSRb.

  assert (AR : a5_ar (0 < S /\ S + n <= lo /\ lo <= SP - 48 /\ SP <= A /\ A + 152 <= 2^47 /\ n < 2^26 /\
               ATOP + 4096 <= lo /\ ATOP_MIN <= ATOP <= ATOP_MAX /\
               I0 = S + 6 /\ I1 = I0 + jt_len src 0 /\ I2 = I1 + jt_len src 2 /\ I3 = I2 + jt_len src 4 /\
               8 <= jt_len src 0 /\ 8 <= jt_len src 2 /\ 8 <= jt_len src 4 /\ I3 + 8 <= S + n /\ 0 <= c <= 8))
    by (pose proof ATOP_range as ATR0; unfold a5_ar; repeat split; lia).
  unfold ATOP_MIN, ATOP_MAX in AR.
  assert (F40 : rw_cells bsegs mm (SP + -40) [C8 (Z_to_bv 64 (bv_unsigned s3))]) by (rewrite Z_to_bv_bv_unsigned; exact C40).
  assert (F32 : rw_cells bsegs mm (SP + -32) [C8 (Z_to_bv 64 (bv_unsigned s2))]) by (rewrite Z_to_bv_bv_unsigned; exact C32).
  assert (F24 : rw_cells bsegs mm (SP + -24) [C8 (Z_to_bv 64 (bv_unsigned s1))]) by (rewrite Z_to_bv_bv_unsigned; exact C24).
  assert (F16 : rw_cells bsegs mm (SP + -16) [C8 (Z_to_bv 64 (bv_unsigned s0))]) by (rewrite Z_to_bv_bv_unsigned; exact C16).
  assert (F08 : rw_cells bsegs mm (SP + -8) [C8 (Z_to_bv 64 (bv_unsigned ra))]) by (rewrite Z_to_bv_bv_unsigned; exact C08).
  pose proof (bv_unsigned_in_range 64 s3) as RS3. pose proof (bv_unsigned_in_range 64 s2) as RS2.
  pose proof (bv_unsigned_in_range 64 s1) as RS1. pose proof (bv_unsigned_in_range 64 s0) as RS0.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RS3, RS2, RS1, RS0, RRA; cbn in RS3, RS2, RS1, RS0, RRA.
  let PxS := constr:([] : list Z) in let PxF := constr:(600%nat : nat) in let PxD := eval vm_compute in (repeat false 4096) in let PxK := constr:([KZRange dcap 1 (2^32 - 1); KZRange n 10 (2^26 - 1); KZRange S 1 (2^47); KZRange DST 0 (2^64 - 9); KZRange (DST + dcap) 1 (2^64 - 8); KZRange DT 1 (2^47); KZAlign DT 8; KZRange SP 0x7fff7f801030 (2^47-152); KZRange I0 1 (2^47); KZRange I1 1 (2^47); KZRange I2 1 (2^47); KZRange I3 1 (2^47); KZRange SG 0 (2^30); KZRange c 0 8; KZWord (SP + -40) 8 (bv_unsigned s3); KZWord (SP + -32) 8 (bv_unsigned s2); KZWord (SP + -24) 8 (bv_unsigned s1); KZWord (SP + -16) 8 (bv_unsigned s0); KZWord (SP + -8) 8 (bv_unsigned ra); KZAlign A 8; KZRange A 1 (2^47); KZWr A 152; KZDisj A 152 S n; KZShZ 2147450880 A 152; KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000] : list kz) in let PxR := constr:([(S, n)] : list (Z * Z)) in let PxW := constr:([(SP - 48, 48); (A, 152); (S, n); (0xb2128, 8); (0xba2f8, 8)] : list (Z * Z)) in let PxU := constr:([(S, n)] : list (Z * Z)) in kx_prepFm PxS PxF PxK PxR PxW PxU; kx_goFL PxD.
  all: try (lazymatch goal with |- accP _ _ _ => a5_acc end).
  all: try (lazymatch goal with |- exists bs, rdn _ _ (adenot _ {| a_base := EVar _; a_off := _ |}) _ = Some bs => a5_rdb SRCm end).
  all: try (lazymatch goal with |- exists bs, rdn _ _ _ 1 = Some bs => a5_rds USRm end).
  all: try (lazymatch goal with |- branch_taken BC_LT _ _ = true => a5_chk USRm end).
  all: try (lazymatch goal with |- flat _ _ _ => a5_z | |- flat _ _ _ /\ _ => a5_z end).
  all: try a5_one SRCm USRm.

  clear F40 F32 F24 F16 F08.
  a5_sentv 88 SENT.
  a5_cells_split HAm.
  a5_cells_post.
  a5_frame SRCm. a5_munch MUm.
  all: a5_side.
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  assert (ST : stk bsegs m1 lo SP).
  { pose proof (a5_stk_rel8 _ _ _ _ STKm C40 ltac:(a5_lia)) as T1. replace (SP + -40 + 8) with (SP + -32) in T1 by a5_lia.
    pose proof (a5_stk_rel8 _ _ _ _ T1 C32 ltac:(a5_lia)) as T2. replace (SP + -32 + 8) with (SP + -24) in T2 by a5_lia.
    pose proof (a5_stk_rel8 _ _ _ _ T2 C24 ltac:(a5_lia)) as T3. replace (SP + -24 + 8) with (SP + -16) in T3 by a5_lia.
    pose proof (a5_stk_rel8 _ _ _ _ T3 C16 ltac:(a5_lia)) as T4. replace (SP + -16 + 8) with (SP + -8) in T4 by a5_lia.
    pose proof (a5_stk_rel8 _ _ _ _ T4 C08 ltac:(a5_lia)) as T5. replace (SP + -8 + 8) with SP in T5 by a5_lia.
    exact T5. }
  try clearbody KXE; try clearbody KXxs.
  subst I0 I1 I2 I3 SG.
  lazymatch goal with H : rw_cells bsegs m1 (A + 88) [C8 ?v] |- _ =>
    assert (HAc : rw_cells bsegs m1 A (fast_args_cells DST dcap S DT src (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2) (bv_unsigned v)));
    [ unfold fast_args_cells; cbv zeta; rewrite !Z_to_bv_bv_unsigned; a5_cells_merge |
    assert (OK : fast_args_okA m1 A DST dcap S DT src tl);
    [ unfold fast_args_okA; split; [exact TL|]; split; [a5_lia|]; split; [exact L0|]; split; [exact L2|]; split; [exact L4|];
      split; [a5_lia|]; split; [exact DC0|]; split; [exact SG3|];
      exists (bv_unsigned b0), (bv_unsigned b1), (bv_unsigned b2), (bv_unsigned v);
      split; [apply a5_bvr|]; split; [apply a5_bvr|];
      split; [apply a5_bvr|]; split; [apply a5_bvr|];
      split; [exact B0|]; split; [exact B1|]; split; [exact B2|]; split; [first [exact SENT | exact SENTz]|];
      exact HAc | ] ] end.
  zstep.
  apply evtF_done. unfold fast_args_postA.
  do 14 eexists. exists 1, m1. split; [reflexivity|].
  split; [exact MUm|]. split; [exact WMm|]. split; [exact MI0|]. split; [exact ST|].
  split; [destruct (afa_rwc_cb _ _ _ HAc) as (ja' & HJ); exists ja'; exact HJ|].
  right; right; split; [reflexivity | exact OK].

Qed.

End AFA5.
End CANSEC1.
