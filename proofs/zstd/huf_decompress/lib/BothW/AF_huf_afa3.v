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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fa_iface AF_huf_afa AF_huf_afa2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_afa3 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit7shcleanC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6hull64C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7app_blkC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atI47Corelib4Init5Logic3and00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzC45stdpp9bitvector;definitions;bv_unsignedK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_iface=fast_args_okAI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa7afa_sp0C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk06K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02C47Corelib4Init9Datatypes6lengthK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_iface?fast_args_postAC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission6Common6KXCell;kx_rwc_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic5proj2K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa:afa_rwc_cbC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC56Stdlib5Arith8PeanoNat3Nat3ltbK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03C47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zk_word_okK46Stdlib5Lists4List7Forall202C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic4True00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litI4ELinuxProcessSemantics5Riscv5Instr5instr00C5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_ifaceDAHUF_FAST_ARGS_STACKK4ELinuxProcessSemantics5Riscv5Instr5aluop01c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa38afa_was0C5ARocqVerifyHarness?AgentSubmission5Plain?RF_huf_fa_iface6jt_lenC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit@rclean_transportC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa8afa_kshzC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9kshz_factC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa7afa_boxK5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk0:K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03C5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7zshz_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF7zshr_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08C5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula02C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:kx_stk_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wr_at_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<log_apart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_apart_ez_okC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_bytes_at_logC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiK47Corelib4Init5Logic2or01c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa37afa_retC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK46Stdlib9micromega5Tauto8GFormula06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartC5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_rw_cells_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost9estart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXCell>kx_cell_store8C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC5ARocqVerifyHarness?AgentSubmission6Common6KXPost5ez_okC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revK4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init5Logic4True01C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa37AFA_F18c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa37afa_wasC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KLOWC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHK4ELinuxProcessSemantics5Riscv5Instr5mulop01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa38AFA_E20'".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Lemma afa_was0 : forall m RNG r A, rclean m r -> rrng RNG r -> r_lo r <= A -> A + 152 <= r_hi r -> A mod 8 = 0 ->
  rng RNG (2147450880 + Z.shiftr A 3) 19.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa3 ()) [] "h01Hh11zh22H0h33H13h43H18h53H23h62H7h77__arithh84__ffh94__p1h:4__p2h;8__varmaph<5__with=4__x1h>5__x10h?5__x11h@5__x12hA5__x13hB4__x2hC4__x3hD4__x4hE4__x5hF4__x6hG4__x7hH4__x8hI4__x9hJ1AhK2ABhL2H1hM3H10hN3H11hO3H12hP3H14hQ3H15hR3H16hS3H17hT3H19hU2H2hV3H20hW3H21hX3H22hY3H24hZ3H25h[3H26h\2H3h]2H4h^2H5h_2H6h`2H8ha2H9hb2LThc2RChd3RNGhe2SHhf1Uhg1Whh2WRhi2X1hj2X2hk2X3hl2X4hm2X5hn2X6ho1mhp1qhq2q0hr2q1hs2q2ht2q3hu1rhv2r0hw2r1hx2r2hy2r3hz2r4p&0p;1p;2p;5p;3p;4p;6p;7p;8p10000p4p7210g000\R0p4p710p8g001:j1<Tg001_j1yTg002=j1qTg002`k10STg003Bk20QTg004=k20OTg0056j18Tg005oj23Tg006Kj1@Tg0070j1OTg007Nj24Tg007kj16Tg008dj11Tg009^j10Tg00:Xk502Tg00;Tj27Tg00<0k300Tg00<kj4`Tg00=fj1>Tg00>^j2cTg00?Vj2STg00@3j2lTg00@Sj25Tg00A0k20RTg00AMj2_Tg00Ank103Tg00BGj2NTg00Bdj22Tg00CDj2^Tg00Ckj2]Tg00DRj2\Tg00E8j2ZTg00E^k201Tg00F?j2nTg00FYj19Tg00G8k10PTg00GVk20NTg00H7j3fTg00H`k20MTg00IIj2~Tg00J2j3}Tg00J[j2|Tg00KGk20KTg00L3k10ITg00LSj3xTg00M3k10HTg00MSk10GTg00N1k10FTg00NOk10ETg00O:j2uTg00O]k10DTg00P?j3bTg00Pbj4jTg00QMj2rTg00R0k30BTg00RSk20ATg00S5k20@Tg00Saj3WTg00T;k30=Tg00TZk40<Tg00ULk30?TP0j6iTg00V5j1zTg00Vnk70:Tg00Wfk309Tg00XYj4vTg00YKR0j2BTg00Yfj3oTg00ZOk208Tg00Zmk40JTg00[Kj7kTg00[ok607Tg00\Sk30LTg00]6j8mTg00]Zk606Tg00^>k705Tf0R1#<#<p=Fg00^bR2f1R3/21g00_@R43Wp=T%@1#@p=Xf4R5f3R6f2R7/l3'4<091p=Cg00_^R8P6P71S31Cvp=d1B31,B7p=e%>3/S1p=JP8P6P7P3Cv/B1p=P1343g00`SR8,31'Bp=G1273=W24/B1p=K%11#>p=I%83%61'cp=M1341p=a1318p=w%01#>p=p1l31,47p>041331,B7p==AW214p=D14319W27p=E13471731'Bp=?AW231p=[1~21p=;Ao2319o27p=QAo231p={20821p=VP2P7P3P1H0Jp=R1u21p=YP7g00aHR8g00agR9P9g00bGR:P2P3g00bgP1Cjg00cNR;Fkp=LP3P8P9P9P:P1J07p=t1r21p=:B0L231p=AP6P8P9P9P:P7P3P1Gmp=gP3P8P9P9P:P1J06p=sP3P8P9P9P:P1P;Fkp>0CP7P8P9P9P:P3P1K05p=hP7P8P9P9P:P2P3g00cnP1CjP;Fkp=Hf6R;P8P9P9P:f5R<P5P6P8P9P9P:P7P3P1GmGmp=U1731,B7p>0;1343/B1p>0>g00dUR8#<R=#<R>#<R?#<#FR@#y#q%y?#q$0S[g00e:g00f320Q6320O67%86/37%@>RA#@RB#<#F#ORC,46%65'3%O?R?,T5P0f8RD%8;RE%6;RF%1;%0;I0217EFPD%@8RF#@RE#@RG#X#X#X#X#X#X#<#F#F#F#F#F#F#F#ORHP;%OFRI%OBRBDCP5f:RJ%8D%6D%1D%0DI02f9RK#8%6K'7P0f<RL%8JRM%6JRN400PMPN%1JRO%0JRPC`PL%>ORO%>PPOCd1cMN3ePLPHPJPIPBDCP3f>RN%8L%6L400f=RM#8RO%6MRP%1MRQ%0MRRC`f?RS%>QRQ%>RPQCd1cOP3eP0%8NRP%6NRO%1NRQ%0NRRC`f@RT%>QRQ1JRQ1cPOCPPTPHPNPIPBDCP1%8T%6T%1T%0TC`P0fARO#1RP%8O'3%6O%0ORO'3%O@R@,TP1GPO9KO@3efDROfBRP#IRQ%0P/JQ1MPPCPPOPHPPPIPBDC[P1fCRQ#1%8Q'3%6O%0ORR'3%1ORU/T@1GUR9KR@3eP0fERR#6%0RRU'3%1RRV1GVU9KU@7K@fHRUfFRV#IRW%0V/JW1MVVCPPUPHPVPIPBDC[P1fGRV#6%0V'3%1URV%0URW1GVW7K@7K@P0fIRW#1RV/T@%0WRW1GVW7K@fLRWfJRV#IRX%0V/JX1MVVCPPWPHPVPIPBDC[P1fKRX#1/T@%0WRY%1W/GY7K@P0fMRY#0RZ/T@%1Y/GZfPRZfNR[#IR\%0[/J\1M[[CPPZPHP[PIPBDC[P1fO#0/T@%1Z%0Z'GP0fQR[#1#a%0[#wfTR\fRR]#IR^%0]/J^1M]]CPP\PHP]PIPBDC[P1fSR^#1#a%0\#wfWR\fUR_#IR`%0_/J`1M__CPP0fXR0fVR`#IRa%p`PaCd1M``P0PHP`PIPBDCP1fZR`%I0Ra%p0PaCdfYRa/Maf[Rb%1`Rc#>Rd%0`Re#>Rf/Sd1laIRg,4HRhPBP\P2g00g0R\15c?'4RiB04H`IR`,3114`BRj%0bRk/J1,413=X12P215e?,4\Rl%1bRb/5?Rm,4\R\/3`1S1\,4\7=jX12P2%O=00RI,5a14HmRj14H1R\'314\B15k?,4H/Sj,4j3=X121_c?%D?Rj$03Rk1N?m12b?5Eb[1^b?174?Rbf\#1Rm/2?R\??\?[1]m?17?4Rmf]#1R\/2?R`,7??=`4[1\\?f^#1R\/5?#D\j1Z\?f_#1R\/2?/[\\j15\?P2f`R\#1/2?P21_\?faR\15\?,N?12\?3E\k1^\?fbR\/2?R`??`?\b1]\?fcR\/2?R`,7??=`4\m1\\?fdR`/5?#D\j1Z`?feR`/2?/[`\j15`?P2ff/2?P2fh#0/_?fi#0R`15`?,N?12`?3E\k1^`?fj#0R`/2?Rk??k?\b1]`?fkR`#0Rk/2?Rn,7??=n4\m1\k?fl#0Rk/5?#D\j1Zk?fm#0Rk/2?/[k\j15k?P2fn#0/2?P2foRk#0/_@%D@Rm$03Rnfp#0Ro15o@,N@12o@3E[1^o@174@Rofq#0Rp/2@Rq??q@[1]p@17@4Rpfr#0Rq/2@Rr,7@?=r4[1\q@fs#0Rq/5@#D\m1Zq@ft#0Rq/2@/[q\m15q@P2fu#0/2@P2fv#1/_@fw#1Rq15q@,N@12q@3E\n1^q@fx#1Rq/2@Rn??n@\o1]q@fy#1Rq/2@Rn,7@?=n4\p1\q@fz#1Rq/5@#D\m1Zq@f{#1Rq/2@/[q\m15q@P2f|#1/2@P2P<g00gjRq2014@'nPoeRoO1A?11@PMPoO1A?DD@PR2014?,nqPbeRbO1A?TT?PYPbO1A?UU?P_PbO1A?ZZ?p-0RZg00hPRbg00i<R_#9RU#9#9RY#9Rq#9#9Ro#9Rp#9Rn#9Rr#;%;n&0P8-0N2Rn%;p5f2Rp%;oRo%;qRq%;URU20M2?Rs1~2_5}2R_3Q3Q3Qg00i[Rt'|%9rRr#9Ru#9Rv#;9f2n%;u%;rRr%;YRY9f2n'{3Q%9v#;Af2nrA}2sU,{Y9Qoq7Qp5Q_/|t+0K&0IbRt5xb3x&0HbRb&0G2R_%VJ7R5%VL9R_;7R7%VDf;#V7R<%VKf7R5%VM3R7R67R3&0F2RJ&0E2RpPp%Y@Rq1u24Ro5Lp,tp&0D9R9%:ERY%:G9b2q%:ARA'A5LpCgP9Pp1spSP2%<E#:REg00jG%Y?RqCj-0Cp5hpP9PpPpALpqo,tpRGP9%:FRs9b2q/AE9LpYCgP9PpPpPGP9%@=RE#@#:RU%:=R=9b2q%<FRF#<#:Rr'A5LpCgP9Pp%@F#:Rn9Hpo1spT5hpP9PpPpPGP9%:>R>1r28R89b2q/An5LpCgP9PpALproP9Pp%YC,AU%:FRF5HpP9Pp%:ERE=HpUP9PpALpAoP9PpAHpFYP9PpAHp>EP9%YHR9/A8R81A9=R=5Hp%YB,A=1A9s>0B28,A85Hp5hpFUFUFUFUFUFU20Ap:R:P1P7g00jnR8g00kNR9'n20@17=W89dB0=243H0<R4b8b;b<X=2XB2XC2XD2XE2XF2XG2XH2XI2X>2X?2X@2XA2X9ZW:g00knR9\m1N@M=E5D[B0;NL?P9\jRj1N?<R<=EKN[AEL<M\j20>NP1N?;=EKT\j%DS14SC/3L13LT%DT13ST13NS14HLRL14HMRS'314SB14HN/SL,4L3=[[[[[[[[[[[[^=2^B2^C2^D2^E2^F2^G2^H2^I2^>2^?2^@2^A2^9Z^:ZP117]?%aOPNPOP]PXp+01CPMp+01DRM#0%6M%8M%1MPRPWP^PQP6PVP[P3P0f}f~p+01@P\P`PkOKb7b2b6b3b4b5bzbtb[bZbYb5bXbybsbWbVbTb4bSbxbrbRbQbPb3bObwbqbNbMbab6b_bvbpb^b]b\b2b0PgPtPbP_PJ%YI9HpoP:P4b8b;b<%aIP1b7:0?aIEi13ih14hB1Sli,4i3=ePf%zeEiPd%zcEiK0:WKWgP3P1O2n2001000000121000000W0WnWmP3P1O2n2001000000121000000W0WlP3P1O2n2001000000121000000W0WkP3P1O2n2001000000121000000W0WjP3P1O2n2001000000121000000W0WiP3P1O2n2001000000121000000W0P3P1O2n2001000000121000000W0WfP3P1O2n2001000000121000000WbWeP3P1O2n2001000000121000000W`WUWLWhWcXJ2WuWdWoo"). Qed.

Lemma afa3_shd_ap8 : forall E X B O k,
  bv_unsigned (edenot E X) < 2^47 -> 0 <= O -> O + 2^44 <= 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + 8 <= 2^64 ->
  bv_unsigned (edenot E B) + k + 8 <= O \/ O + 2^44 <= bv_unsigned (edenot E B) + k ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit 8)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit 8) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k HX HO1 HO2 HB1 HB2 HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (bv_unsigned (Z_to_bv 64 8)) with 8.
  change (2 ^ (3 mod 64)) with 8.
  assert (HD : bv_unsigned (edenot E X) / 8 < 2^44)
    by (apply Z.div_lt_upper_bound; [lia | change (8 * 2^44) with (2^47); lia]).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.

Lemma afa3_sltu0 : forall E a, 0 < bv_unsigned (edenot E a) ->
  bv_unsigned (edenot E (EAlu ALU_SLTU (ELit 0) a)) = 1.
Proof.
  intros E a H. change (edenot E (EAlu ALU_SLTU (ELit 0) a)) with (alu64 ALU_SLTU (Z_to_bv 64 0) (edenot E a)).
  unfold alu64, alu. rewrite bv_ltu_Z.
  assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity. rewrite Z0.
  destruct (Z.ltb_spec 0 (bv_unsigned (edenot E a))); [reflexivity | lia].
Qed.

Lemma afa3_nul : forall E x b, bv_unsigned (edenot E x) = 1 -> 1 <= bv_unsigned (edenot E b) ->
  branch_taken BC_EQ (edenot E (EAlu ALU_XOR x (EAlu ALU_SLTU b (ELit 1)))) (edenot E (ELit 0)) = false.
Proof.
  intros E x b Hx Hb.
  change (edenot E (EAlu ALU_XOR x (EAlu ALU_SLTU b (ELit 1)))) with
    (alu64 ALU_XOR (edenot E x) (alu64 ALU_SLTU (edenot E b) (Z_to_bv 64 1))).
  change (edenot E (ELit 0)) with (Z_to_bv 64 0).
  assert (EX : edenot E x = Z_to_bv 64 1) by (apply bv_eq; rewrite Hx; reflexivity).
  rewrite EX. unfold alu64, alu. rewrite bv_ltu_Z.
  assert (Z1 : bv_unsigned (Z_to_bv 64 1) = 1) by reflexivity. rewrite Z1.
  destruct (Z.ltb_spec (bv_unsigned (edenot E b)) 1); [lia | reflexivity].
Qed.

Ltac afa3_ez :=
  lazymatch goal with
  | |- context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite ?(ez_ok zv E (kE_atoms zv xs));
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
      end
  | |- _ => idtac
  end.
Ltac afa3_zs :=
  rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (Z.of_N 64) with 64;
  repeat match goal with |- context [2 ^ (?k mod 64)] =>
    let v := eval vm_compute in (2 ^ (k mod 64)) in change (2 ^ (k mod 64)) with v end;
  repeat match goal with |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) by lia end.
Ltac afa3_wrange :=
  lazymatch goal with |- 0 <= bv_unsigned ?w < 2 ^ 64 =>
    let H := fresh "WR" in pose proof (bv_unsigned_in_range 64 w) as H; unfold bv_modulus in H; cbn in H; lia end.
Ltac afa3_weq :=
  first [ reflexivity
        | rewrite ?Z_to_bv_bv_unsigned; reflexivity
        | f_equal; lia
        | apply bv_eq; rewrite ?Z_to_bv_unsigned, ?Z_to_bv_bv_unsigned; unfold bv_wrap, bv_modulus;
          try change (Z.of_N 64) with 64;
          repeat match goal with |- context [2 ^ (?k mod 64)] =>
            let v := eval vm_compute in (2 ^ (k mod 64)) in change (2 ^ (k mod 64)) with v end;
          repeat match goal with |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) by lia end;
          lia ].
Ltac afa3_cell1 :=
  lazymatch goal with |- rw_cells ?segs ?m ?a [C8 ?v] =>
    first [ eassumption
          | match goal with H : rw_cells segs m a [C8 ?v'] |- _ => replace v with v' by afa3_weq; exact H end
          | match goal with H : rw_cells segs m ?b [C8 ?v'] |- _ =>
              let E := fresh "EA" in assert (E : a = b) by lia; rewrite E; clear E;
              replace v with v' by afa3_weq; exact H end ] end.
Ltac afa3_norm H :=
  lazymatch type of H with
  | rw_cells _ _ (?a + ?b + Z.of_nat ?k) _ =>
      tryif is_Zlit b then
        (let v := eval vm_compute in (b + Z.of_nat k) in replace (a + b + Z.of_nat k) with (a + v) in H by ring)
      else (let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in H)
  | rw_cells _ _ (?a + Z.of_nat ?k) _ =>
      let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in H
  | _ => idtac
  end.
Ltac afa3_split H :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A (?c :: ?c' :: ?cs) =>
      let H1 := fresh "KC" in
      apply (kx_rwc_cons segs m A c (c' :: cs)) in H; destruct H as [H1 H]; cbn [csize] in H; afa3_norm H;
      afa3_split H
  | rw_cells _ _ _ [_] => idtac
  end.
Ltac afa3_merge :=
  repeat (lazymatch goal with |- rw_cells ?segs ?m ?A (?c :: ?c' :: ?cs) =>
            apply (proj2 (kx_rwc_cons segs m A c (c' :: cs))); split; [afa3_cell1|]; cbn [csize];
            lazymatch goal with
            | |- rw_cells _ _ (?a + ?b + Z.of_nat ?k) _ =>
                tryif is_Zlit b then
                  (let v := eval vm_compute in (b + Z.of_nat k) in replace (a + b + Z.of_nat k) with (a + v) by ring)
                else (let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v)
            | |- rw_cells _ _ (?a + Z.of_nat ?k) _ =>
                let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v
            end end);
  afa3_cell1.
Ltac afa3_cell H :=
  lazymatch goal with
  | HLF : log_flat ?E ?log |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let na := eval vm_compute in (length zv) in
      lazymatch type of H with
      | rw_cells ?segs m (?A0 + ?off) [C8 _] =>
        let rec go pre l :=
          lazymatch l with
          | SE {| a_base := ?ab; a_off := off |} 8%nat ?v :: ?rest =>
              let a := constr:({| a_base := ab; a_off := off |}) in
              let Hn := fresh "HC" in
              assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a 8 v :: rest)) (A0 + off) [C8 (edenot E v)])
                by (eapply (kx_cell_store8 segs E m pre a v rest (A0 + off));
                    [ change (pre ++ SE a 8 v :: rest) with log; exact HLF
                    | exact H
                    | change E with (kE zv xs); kx_estart_z zv
                    | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv ]);
              change (pre ++ SE a 8 v :: rest) with log in Hn;
              rewrite (ez_ok zv E (kE_atoms zv xs) v) in Hn;
              cbv [ez] in Hn; change (length zv) with na in Hn; cbv [nth Nat.ltb Nat.leb] in Hn;
              rewrite ?Z_to_bv_bv_unsigned in Hn;
              clear H; rename Hn into H
          | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
          end in
        let l := eval hnf in log in go constr:(@nil sentry) l
      end
    end
  end.
Ltac afa3_cells :=
  repeat match goal with
  | HLF : log_flat ?E ?log, H : rw_cells ?segs ?m ?A [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      first [ afa3_cell H | kx_frame H ]
  end.
Ltac afa3_clr :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch type of T with Prop => idtac | _ => fail end;
      lazymatch T with
      | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | and _ _ => fail | Z.ge _ _ => fail | Z.gt _ _ => fail
      | _ => clear H
      end
  end.
Ltac afa3_flat2 :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (afa3_shd_ap8 E X B O k); afa3_ez; afa3_clr; afa3_zs; unfold ASHOFF in *; lia
  end.
Ltac afa3_brx2 :=
  lazymatch goal with
  | |- branch_taken BC_EQ (edenot _ (EAlu ALU_XOR _ (EAlu ALU_SLTU _ (ELit 1)))) _ = false =>
      apply afa3_nul; [ first [ reflexivity | apply afa3_sltu0; afa3_ez; afa3_clr; afa3_zs; lia ]
                      | afa3_ez; afa3_clr; afa3_zs; lia ]
  | |- branch_taken _ _ _ = _ =>
      afa3_ez; afa3_clr; unfold branch_taken; afa3_zs;
      first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
            | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
  end.
Ltac afa3_side :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- branch_taken _ _ _ = _ => afa3_brx2
  | |- flat _ _ _ /\ _ => afa3_flat2
  | |- 0 <= bv_unsigned _ < 2 ^ 64 => afa3_wrange
  | |- _ => rewrite ?Z.shiftr_div_pow2 by lia; try change (2^3) with 8; cbn [cells_size csize]; lia
  end.
Ltac afa3_lia :=
  lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => rewrite ?length_map; cbn [cells_size csize]; lia end.

Section CANSEC1. Context {rc : runConstT}.

Section AFA3.
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
  Hypothesis DPOS : 0 < dcap -> 0 < DST.

  Notation POST := (fast_args_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A DST dcap S DT src tl lo m0).
  Notation FRS := [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation MW := [(SP - AHUF_FAST_ARGS_STACK, SP); (A, A + 152)].


  
  Ltac afa_facts :=
    pose proof (afa_sp0 sp lo A LOA LOS ASP A47) as SPB;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    pose proof (afa_kshz m0 rstk A 152 RCL RLO RHI A8 eq_refl ltac:(lia)) as KSH;
    pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _);
    assert (RGOT' : rw_cells bsegs m0 0xaf758 [C8 (Z_to_bv 64 0x1494e8); C8 (Z_to_bv 64 0xb51b8); C8 (Z_to_bv 64 0xb79b8);
                                              C8 (Z_to_bv 64 0xb86a8); C8 (Z_to_bv 64 0xb86b0); C8 (Z_to_bv 64 0xb86a0)]) by exact RGOT;
    assert (RSHB' : rw_cells bsegs m0 0xb79b8 [C8 (Z_to_bv 64 0x7fff8000)]) by exact RSHB;
    clear RG0 RGOT RGRIC RMEM RSHB;
    assert (FAP : KXGoM.apart (SP - 48) 48 0x7fff8000 17592186044416) by (unfold KXGoM.apart; lia);
    assert (AAP : KXGoM.apart A 152 0x7fff8000 17592186044416) by (unfold KXGoM.apart; lia);
    unfold AHUF_FAST_ARGS_STACK in *.

  

  Lemma afa_was : rng RNG (2147450880 + Z.shiftr A 3) 19.
Proof using RCL WRS RLO RHI A8.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa3 ()) ["CANSEC1"; "AFA3"] "p;9g03F7l90Tp,2m0p,3RNGp,4rstkp,1Ap,3RCLp,3WRSp,3RLOp,3RHIp,2A8M90o"). Qed.

  Definition AFA_E20' : Prop :=
    forall mm (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : word) (I0 I1 I2 I3 : Z),
    I0 = S + 6 -> I1 = I0 + jt_len src 0 -> I2 = I1 + jt_len src 2 -> I3 = I2 + jt_len src 4 ->
    8 <= jt_len src 0 -> 8 <= jt_len src 2 -> 8 <= jt_len src 4 -> I3 + 8 <= S + n -> 1 <= dcap ->
    rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
    rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
    rw_cells bsegs mm A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                         C8 w14; C8 (Z_to_bv 64 I0); C8 (Z_to_bv 64 I1); C8 (Z_to_bv 64 I2); C8 (Z_to_bv 64 I3)] ->
    bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
    stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp (Z_to_bv 64 (I3 - S)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880)
                               (Z_to_bv 64 I1) (Z_to_bv 64 (jt_len src 4)) (Z_to_bv 64 A) (Z_to_bv 64 DST) (Z_to_bv 64 dcap)
                               (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 9) (Z_to_bv 64 (A + 120)) (Z_to_bv 64 8) (Z_to_bv 64 8)
                               s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (S + n - I3))
                               (Z_to_bv 64 I3) (Z_to_bv 64 I2))
                           F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 572)) fc None mm (seg_rom bsegs)).

  Ltac afa_jtl := unfold jt_len; change (0 + 1) with 1; change (2 + 1) with 3; change (4 + 1) with 5; lia.

  

  
  Definition AFA_F18 : Prop :=
    forall mm (w8 w9 w10 w11 w12 w13 w14 : word) (I0 I1 I2 I3 SG : Z),
    I0 = S + 6 -> I1 = I0 + jt_len src 0 -> I2 = I1 + jt_len src 2 -> I3 = I2 + jt_len src 4 ->
    8 <= jt_len src 0 -> 8 <= jt_len src 2 -> 8 <= jt_len src 4 -> I3 + 8 <= S + n ->
    SG = (dcap + 3) / 4 -> 0 < dcap -> 3 * SG < dcap ->
    rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
    rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
    rw_cells bsegs mm A [C8 (Z_to_bv 64 (I1 - 8)); C8 (Z_to_bv 64 (I2 - 8)); C8 (Z_to_bv 64 (I3 - 8)); C8 (Z_to_bv 64 (S + n - 8));
                         C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + SG)); C8 (Z_to_bv 64 (DST + 2 * SG)); C8 (Z_to_bv 64 (DST + 3 * SG));
                         C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14;
                         C8 (Z_to_bv 64 I0); C8 (Z_to_bv 64 I1); C8 (Z_to_bv 64 I2); C8 (Z_to_bv 64 I3)] ->
    bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
    stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp (Z_to_bv 64 (I1 - 8)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880)
                               (Z_to_bv 64 I1) (Z_to_bv 64 18446744073709551592) (Z_to_bv 64 A) (Z_to_bv 64 7) (Z_to_bv 64 (I1 - 1))
                               (Z_to_bv 64 S) (Z_to_bv 64 (A + 32)) (Z_to_bv 64 (I2 - 8)) (Z_to_bv 64 (S + n - 8)) (Z_to_bv 64 (I3 - 8))
                               (Z_to_bv 64 18446744073709551600) (Z_to_bv 64 (DST + 2 * SG)) s4 s5 s6 s7 s8 s9 s10 s11
                               (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (S + n)) (Z_to_bv 64 I3) (Z_to_bv 64 I2))
                           F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 924)) fc None mm (seg_rom bsegs)).

  Lemma afa_e20_x : dcap <= 3 * ((dcap + 3) / 4) -> AFA_E20'.
Proof using All.
  intros EX3 mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 I0 I1 I2 I3 HI0 HI1 HI2 HI3 L0 L2 L4 HIn DC1
    C40 C32 C24 C16 C08 HAm SRCm STKm MIm MUm WMm.
  pose proof (DPOS ltac:(lia)) as DP1. pose proof (SL ltac:(lia)) as SLn.
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
  assert (SGB : 4 * ((dcap + 3) / 4) <= dcap + 3 < 4 * ((dcap + 3) / 4) + 4)
    by (pose proof (Z.div_mod (dcap + 3) 4 ltac:(lia)); pose proof (Z.mod_pos_bound (dcap + 3) 4 ltac:(lia)); lia).
  rewrite <- (Z_to_bv_bv_unsigned s3) in C40. rewrite <- (Z_to_bv_bv_unsigned s2) in C32.
  rewrite <- (Z_to_bv_bv_unsigned s1) in C24. rewrite <- (Z_to_bv_bv_unsigned s0) in C16.
  rewrite <- (Z_to_bv_bv_unsigned ra) in C08.
  move C40 at bottom. move C32 at bottom. move C24 at bottom. move C16 at bottom. move C08 at bottom.
  (let PxS := constr:(@nil Z) in let PxF := constr:(3000%nat : nat) in
   let PxD := eval vm_compute in (repeat false 8 ++ true :: repeat false 4096) in
   let PxK := constr:([KZRange dcap 1 (2^32 - 1); KZRange n 10 (2^26 - 1); KZRange S 1 (2^47); KZRange DST 1 (2^64 - 9); KZRange (DST + dcap) 2 (2^64 - 8); KZRange DT 1 (2^47); KZAlign DT 8; KZRange SP 0x7fff7f801030 (2^47-152); KZAlign A 8; KZRange A 1 (2^47); KZWr A 152; KZDisj A 152 S n; KZShZ 2147450880 A 152; KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWord (SP + -40) 8 (bv_unsigned s3); KZWord (SP + -32) 8 (bv_unsigned s2); KZWord (SP + -24) 8 (bv_unsigned s1); KZWord (SP + -16) 8 (bv_unsigned s0); KZWord (SP + -8) 8 (bv_unsigned ra); KZDisj A 152 (SP - 48) 48] : list kz) in let PxR := constr:([(S, n)] : list (Z * Z)) in let PxW := constr:([(SP - 48, 48); (A, 152); (S, n); (0xb2128, 8); (0xba2f8, 8)] : list (Z * Z)) in let PxU := constr:([(S, n)] : list (Z * Z)) in kx_prepFm PxS PxF PxK PxR PxW PxU; kx_goFL PxD).
  all: afa3_side.
  try clear KXRUN; try clear HRV; try clear HUR; try clear HUW; try clear HWW; try clear HRR; try clear HTB;
  try clear HSH; try clear KXR0; try clear HSR0; try clear HUR0; try clear HUW0; try clear HWW0; try clear HRR0;
  try clear HTB0; try clear HSH0; try clear HK0; try clear MG; try clear KSH; try clear KSHm; try clear USRm;
  try clear USRn; try clear WSRa; try clear WSRb; try clear WSRc; try clear WAS; try clear WAS2; try clear RSHBm;
  try clear RGOTm.
  afa3_split HAm. rewrite <- (Z.add_0_r A) in KC.
  afa3_cells.
  rewrite Z.add_0_r in KC.
  kx_munch MUm.
  all: try afa3_lia.
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  zstep.
  repeat (match goal with X := _ |- _ => clearbody X end).
  apply evtF_done. unfold fast_args_postA.
  do 14 eexists. exists 0. eexists. split; [reflexivity|].
  split; [exact MUm|]. split; [exact WMm|]. split; [assumption|].
  split.
  { lazymatch goal with |- stk _ ?m _ _ =>
      eassert (FRX : rw_cells bsegs m (SP + -40) [_; _; _; _; _]); [kx_cells_merge|];
      pose proof (stk_release bsegs m lo (SP + -40) _ STKm FRX ltac:(lia)) as STK1;
      lazymatch type of STK1 with stk _ _ _ (?a + Z.of_nat ?k) =>
        let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in STK1;
        replace (bv_unsigned sp) with (a + v) by lia end;
      exact STK1 end. }
  split.
  { lazymatch goal with |- exists _, rw_cells _ ?m A _ =>
      eassert (HAX : rw_cells bsegs m A [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _]); [kx_cells_merge|];
      destruct (afa_rwc_cb m A _ HAX) as (ja' & HJ); exists ja'; exact HJ end. }
  left; reflexivity.
Qed.

  Lemma afa_e20_m : 3 * ((dcap + 3) / 4) < dcap -> AFA_F18 -> AFA_E20'.
Proof using All.
  intros OK3 K mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 I0 I1 I2 I3 HI0 HI1 HI2 HI3 L0 L2 L4 HIn DC1
    C40 C32 C24 C16 C08 HAm SRCm STKm MIm MUm WMm.
  pose proof (DPOS ltac:(lia)) as DP1. pose proof (SL ltac:(lia)) as SLn.
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
  assert (SGB : 4 * ((dcap + 3) / 4) <= dcap + 3 < 4 * ((dcap + 3) / 4) + 4)
    by (pose proof (Z.div_mod (dcap + 3) 4 ltac:(lia)); pose proof (Z.mod_pos_bound (dcap + 3) 4 ltac:(lia)); lia).
  (let PxS := constr:([AHUF_FAST_ARGS_INIT + 924] : list Z) in let PxF := constr:(3000%nat : nat) in
   let PxD := eval vm_compute in (repeat false 4096) in
   let PxK := constr:([KZRange dcap 1 (2^32 - 1); KZRange n 10 (2^26 - 1); KZRange S 1 (2^47); KZRange DST 1 (2^64 - 9); KZRange (DST + dcap) 2 (2^64 - 8); KZRange DT 1 (2^47); KZAlign DT 8; KZRange SP 0x7fff7f801030 (2^47-152); KZAlign A 8; KZRange A 1 (2^47); KZWr A 152; KZDisj A 152 S n; KZShZ 2147450880 A 152; KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000] : list kz) in let PxR := constr:([(S, n)] : list (Z * Z)) in let PxW := constr:([(SP - 48, 48); (A, 152); (S, n); (0xb2128, 8); (0xba2f8, 8)] : list (Z * Z)) in let PxU := constr:([(S, n)] : list (Z * Z)) in kx_prepFm PxS PxF PxK PxR PxW PxU; kx_goFL PxD).
  all: afa3_side.
  try clear KXRUN; try clear HRV; try clear HUR; try clear HUW; try clear HWW; try clear HRR; try clear HTB;
  try clear HSH; try clear KXR0; try clear HSR0; try clear HUR0; try clear HUW0; try clear HWW0; try clear HRR0;
  try clear HTB0; try clear HSH0; try clear HK0; try clear MG; try clear KSH; try clear KSHm; try clear USRm;
  try clear USRn; try clear WSRa; try clear WSRb; try clear WSRc; try clear WAS; try clear WAS2; try clear RSHBm;
  try clear RGOTm.
  afa3_split HAm. rewrite <- (Z.add_0_r A) in KC.
  afa3_cells.
  rewrite Z.add_0_r in KC.
  kx_frame SRCm. kx_munch MUm.
  all: try afa3_lia.
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  repeat (match goal with X := _ |- _ => clearbody X end).
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ ?r5 _ _ _ ?r9 _ ?r11 ?r12 _ ?r14 ?r15 ?r16 ?r17 ?r18 ?r19
                                           _ _ _ _ _ _ _ _ _ ?r29 _ _) _ ?pc _ _ _ _) =>
    replace r5 with (Z_to_bv 64 (I1 - 8)) by afa3_weq;
    replace r9 with (Z_to_bv 64 18446744073709551592) by afa3_weq;
    replace r11 with (Z_to_bv 64 7) by afa3_weq;
    replace r12 with (Z_to_bv 64 (I1 - 1)) by afa3_weq;
    replace r14 with (Z_to_bv 64 (A + 32)) by afa3_weq;
    replace r15 with (Z_to_bv 64 (I2 - 8)) by afa3_weq;
    replace r16 with (Z_to_bv 64 (S + n - 8)) by afa3_weq;
    replace r17 with (Z_to_bv 64 (I3 - 8)) by afa3_weq;
    replace r18 with (Z_to_bv 64 18446744073709551600) by afa3_weq;
    replace r19 with (Z_to_bv 64 (DST + 2 * ((dcap + 3) / 4))) by afa3_weq;
    replace r29 with (Z_to_bv 64 (S + n)) by afa3_weq;
    replace pc with (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 924)) by first [reflexivity | vm_compute; reflexivity]
  end.
  apply (K m1 w8 w9 w10 w11 w12 w13 w14 I0 I1 I2 I3 ((dcap + 3) / 4)).
  all: first [ assumption | reflexivity | lia | afa3_merge | afa3_cell1 ].
Qed.

  Lemma afa_e20 : AFA_F18 -> AFA_E20'.
Proof using All.
  intros K. destruct (Z_lt_ge_dec (3 * ((dcap + 3) / 4)) dcap) as [H | H].
  - exact (afa_e20_m H K).
  - apply afa_e20_x. lia.
Qed.

End AFA3.
End CANSEC1.
