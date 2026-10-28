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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fa_iface AF_huf_afa.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_afa2 () := "C47Corelib7Classes?RelationClasses9ReflexiveK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7mod_0_lC47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions@Z_to_bv_unsignedK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_iface=fast_args_okAI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa7afa_sp0C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk06K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02C47Corelib4Init9Datatypes6lengthK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_iface?fast_args_postAC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission6Common6KXCell;kx_rwc_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic5proj2K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsK46Stdlib9micromega6VarMap1t03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa:afa_rwc_cbC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC56Stdlib5Arith8PeanoNat3Nat3ltbK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03C47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zk_word_okK46Stdlib5Lists4List7Forall202C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litI4ELinuxProcessSemantics5Riscv5Instr5instr00C5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_ifaceDAHUF_FAST_ARGS_STACKK4ELinuxProcessSemantics5Riscv5Instr5aluop01C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit7shcleanC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6hull64C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7app_blkC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'K46Stdlib9micromega=RingMicromega5Psatz06C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFK46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5nshadC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_munchK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit@rclean_transportC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa8afa_kshzC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9kshz_factC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa:afa_cb8_c8C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk0:K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa:zk_byte_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7zshz_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6zur_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF7zshr_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06C5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula02C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:kx_stk_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wr_at_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List=Forall_forallC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List6nth_InI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa<afa_ext_byteC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC5ARocqVerifyHarness?AgentSubmission6Common6KXPost9estart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<log_apart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_apart_ez_okC5ARocqVerifyHarness?AgentSubmission6Common6KXCell>kx_cell_store8C5ARocqVerifyHarness?AgentSubmission6Common6KXPost5ez_okC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_bytes_at_logC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic2or01c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa27afa_retC56Stdlib6ZArith6BinInt1Z6ltb_geK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission5Plain?RF_huf_fa_iface6jt_lenc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa26afa_w0K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_rw_cells_logK47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa27AFA_E20c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_afa27afa_wasC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KLOWC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_lit".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Lemma afa_w0 : forall w : word, 0 <= bv_unsigned w <= 0 -> w = Z_to_bv 64 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa2 ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h52b1h62b2h71nh81Hh92H0h:1wh;1zp;1p;2p;3p;4p;7p;8p;6p-1p10000p4p710p9g000\j13Tg001Aj1WTg001_j12Tg002Bj21Tg002lj26Tg003HR0j2:Tg003cj30Tg004=j3DTg004aj2BTg005Gj2ATg005mj1@Tg006Mj1>Tg006mj2=Tg007Kj1VTg007ij1UTg008Tj2<Tg0097j2RTg009Zj44Tg00:Ej7LTg00:ij1KTg00;Kj8JTg00;oj2CTg00<Qj2ETg00<kj2FTg00=Wj3GTg00>6j4HTg00>hj18Tg00?Fj1ITg00?dj29Tg00@Aj2?Tg00@aj1MTg00A?j3NTg00Abj6OTg00BFj1PTg00B_j2QTg00C@j6;Tg00C^j2STg00DMj7TTf1R1g00E1R2g00EPR3P3g00F0R4f0R5g00FPFTp=5g00G0R6g00GNR7705p=7g00GlR8#3R9#3#3#3#3#3R:#WR;#211;5R<,6716<7':g00HQR<%25R=%21R>P0f2R0#2?015f3R?/1011?1506R@[11011105506%2??001[RAf4#2?0?0\@AD015P5n2001000000120000000W6W5W7PA^6>^5=^7<P5P;P01B;7R<P61A;7R=11;?R?=065X;6R>P6P7P>g00HoR>#@RA%>>R>1=61%V6R@%U6RBP2P3P3P4PBP2P3P3P4P61<67RCg00I[RD1R68R8C4,5BP6P8PDPCC4,5BFL%K3P6P8g00JBR8PCC4,5BGJ1CB4RDP5P0g00JiREg00KIRF'E1F50=0EFdAG671CHRFb1b2b3X4616751657':%71[^46P5P?P0O2b0%89R9%I;'9R?,?7PAP>%M6P@PBP2P3P3P4P61<69=N6;P8PCC4,5BEOPDPFb1b2b3%8:,99#7g00Ki[P5b0%7?#Pe,Q?E;11;0=06=e11;<1S;7E;O4b9W8W:o"). Qed.

Lemma afa_firstn1_skipn : forall (l : list Z) n, (n < length l)%nat -> firstn 1 (skipn n l) = [nth n l 0].
Proof.
  induction l as [|x l IH]; intros n Hn; [cbn in Hn; lia|].
  destruct n as [|n]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hn. lia.
Qed.

Lemma afa_rd1 : forall segs (m : word -> option byte) S (bs : list Z) E j w k,
  bytes_at segs m S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs ->
  ev E j = rdval segs m w 1 false -> w = Z_to_bv 64 (S + k) -> 0 <= k < zlen bs ->
  bv_unsigned (ev E j) = Znth k bs.
Proof.
  intros segs m S bs E j w k HB BY H Hw Hk. subst w. rewrite H. unfold rdval.
  replace (Z_to_bv 64 (S + k)) with (wa (S + Z.of_nat (Z.to_nat k))) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_rdn segs m S _ (Z.to_nat k) 1 HB) by (rewrite length_map; lia).
  rewrite skipn_map, firstn_map, afa_firstn1_skipn by lia.
  assert (R : 0 <= nth (Z.to_nat k) bs 0 < 256).
  { rewrite Forall_forall in BY. apply BY. apply nth_In. lia. }
  unfold Znth. cbn [map extz bytes_le_to_Z]. change (0 ≪ 8) with 0. rewrite Z.lor_0_r.
  rewrite (Z_to_bv_small 8) by (unfold bv_modulus; cbn -[Z.pow]; lia).
  rewrite Z_to_bv_small by (unfold bv_modulus; cbn -[Z.pow]; lia). reflexivity.
Qed.

Lemma afa_byte_rng : forall (bs : list Z) k, Forall (fun c => 0 <= c < 256) bs -> 0 <= k < zlen bs -> 0 <= Znth k bs < 256.
Proof.
  intros bs k BY Hk. unfold Znth. rewrite Forall_forall in BY. apply BY. apply nth_In. lia.
Qed.

Lemma afa_shd_ap8 : forall E X B O k,
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

Ltac afa_zlia := try w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus, ASHOFF in *;
  rewrite ?Z.mod_small by lia; lia.
Ltac afa_flat :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (afa_shd_ap8 E X B O k); afa_zlia
  end.
Ltac afa_rd j bs HS BY :=
  let H := fresh "HR" in kx_read_eq j H;
  lazymatch type of H with
  | ev ?E j = rdval ?segs ?m (adenot ?E {| a_base := EVar ?i1; a_off := ?off |}) 1 false =>
      lazymatch goal with KXA : forall j, (j < length ?zv)%nat -> ev E j = _ |- _ =>
        let Z1 := fresh "ZR" in
        lazymatch type of HS with bytes_at _ _ ?S0 _ =>
        assert (Z1 : bv_unsigned (ev E j) = Znth off bs);
        [ apply (afa_rd1 segs m S0 bs E j _ off HS BY H);
          [ rewrite (afa_adenot_var E i1 off _ (KXA i1 ltac:(vm_compute; lia))) by (cbv [nth]; lia);
            cbv [nth]; reflexivity
          | lia ]
        | clear H ] end
      end
  end.
Ltac afa_br :=
  lazymatch goal with
  | |- branch_taken _ _ _ = _ =>
      w4ez;
      repeat (match goal with H : bv_unsigned (ev ?E ?j) = Znth _ _ |- context [bv_unsigned (ev ?E ?j)] => rewrite H end);
      unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      first [ rewrite ?Z.mod_small by lia;
              first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
                    | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
            | first [ apply Bool.negb_true_iff, Z.ltb_ge | apply Z.ltb_lt
                    | apply Bool.negb_false_iff, Z.ltb_lt | apply Z.ltb_ge ];
              Z.div_mod_to_equations; lia ]
  end.

Section CANSEC1. Context {rc : runConstT}.

Section AFA2.
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
Proof using All.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa2 ()) ["CANSEC1"; "AFA2"] "p'0h01ah11Hh22Hah37__sat52h47__sat54h52H0h63H11h77__sat56h87__sat57h97__sat58h:1zh;3H10h<3H12h=3H13h>3H14h?3H15h@3H16hA3H21hB3H26hC3H31hD3H36hE2H7hF2H8hG2H9hH7__arithhI4__ffhJ4__p1hK4__p2hL7__sat51hM7__sat53hN7__sat55hO7__sat59hP8__varmaphQ5__withR4__x1hS5__x10hT5__x11hU5__x12hV5__x13hW4__x2hX4__x3hY4__x4hZ4__x5h[4__x6h\4__x7h]4__x8h^4__x9h_4cstrh`1rha2ABhb2H1hc3H17hd3H18he3H19hf2H2hg3H20hh3H22hi3H23hj3H24hk3H25hl3H27hm3H28hn3H29ho2H3hp3H30hq3H32hr3H33hs3H34ht3H35hu3H37hv3H38hw3H39hx2H4hy3H40hz3H41h{3H42h|3H43h}3H44h~3H45i003H46i013H47i023H48i033H49i042H5i053H50i062H6i072LTi082SHi091Ui0:1Wi0;7__sat48i0<7__sat49i0=7__sat50i0>7__sat60i0?1qi0@2q0i0A2q1i0B2q2i0C2q3i0D2q4i0E2q5i0F2r0i0G2r1i0H2r2i0I2r3i0J2r4i0K2r5p%0p&0p;1p;5p;2p;3p;4p;6p;7p;8g02mok10TTg02nhk10STg02oak10BTg030[k104Tg031Uk50RTg00lRj24Tg003HR0j23Tg00R2j15Tg000\j10Tg00>hj17Tg032Qk20QTg00S5j21Tg0331k30MTg033dk30HTg034_k40GTg035Zj1vTg00W3j2bTg036Rk40ATg037Dk20>Tg002lj26Tg00@Aj2GTg038<j2CTg00?dj2UTg038Yj2KTg00BFj1xTg039:j2MTg039aj2PTg03:Hj2OTg03:nj2JTg00mRj2hTg00<Qj2_Tg03;Tk10PTg03<Rk10OTg00gRk20NTg00kEk10LTg00iek10JTg00kjj2^Tg00lnj3]Tg00U@j18Tg00RWk10FTg03=Hk20ETg03=ij3WTg03>Rk20DTg03?;j2uTg03?dj3tTg03@Mj2sTg03A9k20@Tg005mk10?Tg00WPj3qTg006Mk10=Tg00@ak10<Tg007Kk10;Tg007ik10:Tg008Tj2mTg00:ik108Tg03Aej3[Tg009Zj4aTg0097j2nTg02RLk305Tg00;ok209Tg00<kk203Tg003cj3VTg00=Wk302Tg00>6k401Tg03BHj2pTg03Bej2\k30CTg03CVj3~Tg00C@j6cTg03D?j1jTg03E8j7}Tg03F0j3dTg006mk20ITg02Bfj4|Tg00DMj7eTg00Abk60KTg02Roj3{Tg00;Kj8fTg02SRj6zTg00:Ej7yTf0R1#5#5p=l%51#5#5#5p=S%01#0p=X%01#0#0#0p=g%01#0#0#0#0#0#0#0p=Yg00G0R2g00GNR37V1p=:1631p=2f2R4f1R5/11'6p>061645/31p=@1b51,14p=?1651,34p=o1145/61p=Ef3R61p45/115V2p=>1431p=F16341451'3p=A1613p=LAV251p=N1451,34p=T1u21p=<Ad2519d24p=IAd251p=r20I21p=HP2P4P5P1C|p=91m21p=QP4g00E1R7g00EPR8P8g00F0R9P2P5g00JBP1Cag00FPR:Fep=BP5P7P8P8P9P1J0Kp=i1n21p=;A{251p==P6P7P8P8P9P4P5P1Gfp=ZP5P7P8P8P9P1Ezp=kP5P7P8P8P9P1P:Fep>07P4P7P8P8P9P5P1Fyp=`P4P7P8P8P9P2P5g00I[P1CaP:Fep=Df6R:P7P8P8P9f5R;f4R<P6P7P8P8P9P4P5P1GfGfp=R11519V24p=w1635/31p>00p,3RCLp,2m0R7p,4rstkR=$0TR>&0S=R?&0B=R@&04=R=I0RRA14>?RB'3P0PAPBp,3RNGRCg00GlRD#5RE#5S00#5S01#5#l#S#SRF#5RG#0#X#g#Y#7RHp,1ARI%7ERJ+0QS02'1RK%0DRL#0RM#5S03#5RN#7RO40MRPP1P0B0H7>?S04P>P?P@P=H0GRQg02Y:P7%v@R7%v=RR/b7RSH0ART20>>?RU'3RV'3S05PPP5Q04Q05P0PQPVPPP1P016@>S0616?=RW%0MRX#XRY#0RZ#7R[,G@R\#:R]1G=[R^#:R_%2@R`g03FY,6=Ra'3Rb'3Rc'3Rd'3S07PP\VReP1Q06Q07P0PWPdPeP1P0P]PcPeP1P0P_PbPeP1P0P`PaPeP1P0PTPUPPP1PCP7PSPKPOp,3WRSP2g03GNRS%7XRX,C@RC'1RP11KORe1bR180619@1KX:2P21C=XRf,1SS0816PKS09A?P1P7oeX:2P2%7LRK/UJ,CI11HCRS11H1Rg11Hf=?SS9EgO3@X:21K@X%:XRg#xRSP@PXPC1G@XRhC>[1M@X%FXRiAAhhX[1P@X14X3Rj14Xh%Lh'3[1O@X%:C\g1J@X1Nh@\gPCP2PhP21KIXPIPX1CIXRh1GIXRCC>\S1MIX%2CS0:?TCX\i1PIX14XC%LC'3\j1OIX%:h\g1JIX1NCI\gPhP2PCP21K=XP=PXPf1G=XRCC>\S1M=XAACCX\i1P=X14XC%LC'3\j1O=X%:f\g1J=X1NC=\gPfP2PCP21K=[%:[RC#xRfP=P[1C=[RhP^C>[1M=[%F[Rk%2^S0;?T^[[1P=[14[3Rl14[^%L^'3[1O=[%:h\C1J=[1N^=\CPhP2P^P21K@[P@P[1C@[R^P\C>\f1M@[%2\S0<?T\[\k1P@[14[\%L\'3\l1O@[%:^\C1J@[1N\@\CP^P2P\P2p,2DTR\/KXP\PX1C\XR^1G\XRlC>\S1M\X%2lS0=?TlX\i1P\X14Xl%Ll'3\j1O\X%:^\g1J\X1Nl\\gP^P2PlP2p,1SRl/KXPlPX1ClXR^1GlXRfC>\S1MlX%2fS0>?TfX\i1PlX14Xf%Lf'3\j1OlX%:^\g1JlX1Nfl\gP^P2PfP2p,3RM1S0?p,3mtlRf#2R^%0ZRZ#0#7Rj,4fRf'3S0@P0P^Pff],1HRSfVRh,1HRmfO,1H=?SS9EmO3@P1p,3RTTS0Ap,2ttRm#2RS14mjRm'3S0BP0PSPmfb,1HRnf[,1HRofTS0C,1H=?nn9EoO3@P1p,3RTLS0Dp,2tlRo#2Rn14ojRo'3S0EP0PnPofg,1HRjf`,1HRpfYRq,1H=?jj9EpO3@P1p,3RM2S0Fp,4mtl'Rp#2Rj%7Z,4pRp'3S0GP0PjPpfl,1HRZfe,1HRrf^Rs,1H=?ZZ9ErO3@P1p,2DCS0Hp,4dcapRr#2RZ%7YRY,UKRt,4rRr'3S0IP0PZPrfqRu,1HRvfj,1HRwfc,1H=?vv9EwO3@P1fNg02cDRw1h3X'_PieRiO1fIRv?AvXPhPiO1fQRh?AhXPs1h3[,_wPkeRkO1AAqq[ffPkO1faRk?Ak[fnPiO1fiRk?AkXfvPiO1AAuuXf~PiO1fyRi?AiXp,2rcRi$0PS0J%0F#S#S#0#X#g#Y#Y#7&0OiRi%SG#S#0#X#g#Y#Y#7,6i3@S0Kp,3src-0N2Ri$0LS0L&0Ji#2S0M1^KYS0N%FKRi%2Y%Ft[S0O[S0P%2KRGg02bhRFA]KY5UW2S0Q%2t\F^2GS0R%5LS0S#lS0T#5#7Rt,^KS0U%2t1UKtRY#F[S0V\iS0WA]Kt5VFX2GS0X%2Y\F^2GS0Y1^K[S0Z%2[RY1UK[Rt#F[S0[\iS0\A]K[5VFX2GS0]%2t\F^2GS0^%0ERt#5Ru#0#7Rk,^KS0_%2k1UKkRq#F[S0`\iS0aA]Kk5VFX2GS0b%2q\F^2GS0cP51h3K,_wPieRiO1Q0`P<PiO1Q0[f7RwPiO1Q0Vf:RKPiO1Q0Op-0RGg00HoRFg02\iRq#8Rk#8Rs#8#8Rh#8#8Rv#8Rx#8Ry#8Rz#<%<y&0FD-0E2Ry%<xRx5W2%<hRh%<sRs%<kRk20D2XR{1u2q5t2Rq3I3I3Ig03HHR|'s%8zRz#8R}#8R~#<9W2y%<}%<zRz%<vRv9W2y'r3I%8~#<AW2yzAW2ysAt2{k'r9Ivh7Ix5Iq/s|+0@&0?FS0d5qF3q&0=FS0e&0<2RFf=R|f<Rq#H39?9<Ff8R<#H?9|F%H:79|794%H|99F|%HK?9;F79|f9Rx#H?9|Ff;Rv#H?9wF79|796795&0;2R6&0:2RhPh%Q[R{1m23Rk5Bh,ih&088R8%;NRs%0tRt#5#;9[2{Q0S#0#5#;R{'=5BhCZP8Phf?Ry,khP2%0t#;Rtg02\B%QXRzCa-07h5`hP8PhPhABhzk,ihR~P8%;ERE9[2z/=t9BhsCZP8PhPhP~P8%;uRu%;LRL9[2z%;MRM'=5BhCZP8PhQ0T#;Rt9Dhkf@R},kh5`hP8PhPhP~P8Q03#0#;R~1n2DRD9[2z/=t5BhCZP8PhABh{kP8PhQ01#;R{=DhsP8PhQ00#0#;Rs9Dh~P8Ph%0N#X#7RN#Q,=u=Dh{P8PhADhsuP8PhABhMkP8%QHR8/=DRD1=8LRL5Dh%QO,=L1=8E>052D,=D5Dh5`hFRFRFRFRFRFR209h9R9P1P4g00JiRDg00KIR8'_20314=VD8dB02235H01R3bIbPbQXR2XW2XX2XY2XZ2X[2X\2X]2X^2XS2XT2XU2XV2XJGWKg00KiR8\CPxP[P|PKC>[f>RK?TqXP8\gRg1pX;R;=wvK[Aw<;w\gfB-00KP|PXP:P}C>\g%:y16|y16y|AE|Ny16yK%:K11HqRq11H|R|11HK=?qq9E|O3@[[[[[[[[[[[[^R2^W2^X2^Y2^Z2^[2^\2^]2^^2^S2^T2^U2^V2^JG^KGP1p+01JRG/4Xf{R2#2fuP2PGftP=P@P?P>PIp+01Cf|p+01Dp+01KfzfAp+01Bp+01IPyp+01Pp+01[p+01cp+01gp,3RHIp,3RLOp,2A8OKbHb9b7b4b3bLb3bMb4bNb7b8b9b_c05b5b6b@bAbBbCbDZ03rZ02ZP5P1O2n2001000010121000000b0Z01pZ00jP5P1O2n2001000010121000000b0X~oX}nP5P1O2n2001000010121000000b0X|mX{SP5P1O2n2001000010121000000b0XzfXy^P5P1O2n2001000010121000000b0c0Kc0EbwbvbubDbtc0Jc0DbsbrbqbCbpc0Ic0CbnbmblbBbkc0Hc0BbjbibhbAbgc0Gc0Abebdbcb@b?c0Fc0@b>b=b<b6b;b`c0?bGbFbEb5b1Q02Q0JQ0KQ0LQ0M1\lX%2l%2XRlQ0>[[Q0UQ0WQ0XQ0YQ0NQ0PQ0QQ0R1\=[%2=Q0;\Y[Q0ZQ0\Q0]Q0^Q0_Q0aQ0bQ0c1\IX%2IQ0:\l[1\\X%2\Q0=\l[fD:0C@[Q0<\YQ0?Q0@P0P^Pf%2JRYP1Q0AQ0BP0PSPmPYP1Q0DQ0EP0PnPoPYP1Q0FQ0GP0PjPpPYP1Q0HQ0IP0PZPrPYP1fMPiO1Q0`fPPiO1Q0[Q0CPiO1Q0OfWPiO1Q0VQ0dQ0ePFP6%QJ9DhkP9P3bIbPbQPYP1bHbOb8b4b3X?rX>ZP5P1O2n2001000000121000000b0X=pX<jP5P1O2n2001000000121000000b0X6oX;nP5P1O2n2001000000121000000b0XGmXFSP5P1O2n2001000000121000000b0XEfX5^P5P1O2n2001000000121000000b0c0;c0<c0=bLb3bMb4bNb7b8b9bOc0>b_b19~IJEcQ09Q08=?PP7oeePR%j=EcP7%j@EcF}XaUZ0:TP5P1O2n2001000000121000000X1VZ06aZ04`P5P1O2n2001000000121000000X1bXx_P5P1O2n2001000000121000000X1cXo]P5P1O2n2001000000121000000X1dXfWP5P1O2n2001000000121000000W1WbP5P1O2n2001000000121000000X1QP5P1O2n2001000000121000000W1Y09P5P1O2n2001000000121000000Z07BZ08AP5P1O2n2001000000121000000b`o"). Qed.

  
  Definition AFA_E20 : Prop :=
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

  

  Ltac afa_lkg HS := repeat match goal with |- context [bv_unsigned (ev ?E ?j)] =>
    lazymatch goal with H : bv_unsigned (ev E j) = _ |- _ => fail | _ => afa_rd j src HS BYS end end.

  Lemma afa_jt_m : AFA_E20 -> 8 <= jt_len src 0 -> 8 <= jt_len src 2 -> 8 <= jt_len src 4 ->
    jt_len src 0 + jt_len src 2 + jt_len src 4 + 14 <= n ->
    forall (t0 t4 t5 t6 : word), tl = 11 -> 1 <= dcap -> 10 <= n -> forall mm (x15 x16 x17 : word),
    rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
    rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
    rw_cells bsegs mm A [CB 152 ja] -> bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
    stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp t0 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) s0 s1 (Z_to_bv 64 A)
                               (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S) (Z_to_bv 64 n) x15 x16 x17
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + dcap)) t4 t5 t6)
                          F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 140)) fc None mm (seg_rom bsegs)).
Proof using All.
  intros E20 HL1 HL2 HL3 HL4 t0 t4 t5 t6 TL DC1 N10 mm x15 x16 x17 C40 C32 C24 C16 C08 HAm SRCm STKm MIm MUm WMm.
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
  assert (HL1' : 8 <= Znth 0 src + 256 * Znth 1 src) by exact HL1.
  assert (HL2' : 8 <= Znth 2 src + 256 * Znth 3 src) by exact HL2.
  assert (HL3' : 8 <= Znth 4 src + 256 * Znth 5 src) by exact HL3.
  assert (HL4' : Znth 0 src + 256 * Znth 1 src + (Znth 2 src + 256 * Znth 3 src) + (Znth 4 src + 256 * Znth 5 src) + 14 <= n)
    by exact HL4.
  pose proof (afa_byte_rng src 0 BYS ltac:(lia)). pose proof (afa_byte_rng src 1 BYS ltac:(lia)).
  pose proof (afa_byte_rng src 2 BYS ltac:(lia)). pose proof (afa_byte_rng src 3 BYS ltac:(lia)).
  pose proof (afa_byte_rng src 4 BYS ltac:(lia)). pose proof (afa_byte_rng src 5 BYS ltac:(lia)).
  let PxS := constr:([AHUF_FAST_ARGS_INIT + 572] : list Z) in let PxF := constr:(3000%nat : nat) in let PxD := eval vm_compute in (repeat false 4096) in let PxK := constr:([KZRange dcap 1 (2^32 - 1); KZRange n 10 (2^26 - 1); KZRange S 1 (2^47); KZRange DST 1 (2^64 - 9); KZRange (DST + dcap) 2 (2^64 - 8); KZRange DT 1 (2^47); KZAlign DT 8; KZRange SP 0x7fff7f801030 (2^47-152); KZAlign A 8; KZRange A 1 (2^47); KZWr A 152; KZDisj A 152 S n; KZShZ 2147450880 A 152; KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000] : list kz) in let PxR := constr:([(S, n)] : list (Z * Z)) in let PxW := constr:([(SP - 48, 48); (A, 152); (S, n); (0xb2128, 8); (0xba2f8, 8)] : list (Z * Z)) in let PxU := constr:([(S, n)] : list (Z * Z)) in kx_prepFm PxS PxF PxK PxR PxW PxU; kx_goFL PxD.
  all: try clear KXRUN.
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => w4ez; afa_lkg SRCm; afa_br end).
  all: try (lazymatch goal with |- flat _ _ _ /\ _ => afa_flat end).
  afa_rd 32%nat src SRCm BYS; afa_rd 33%nat src SRCm BYS; afa_rd 36%nat src SRCm BYS;
    afa_rd 37%nat src SRCm BYS; afa_rd 40%nat src SRCm BYS; afa_rd 41%nat src SRCm BYS.
  apply (rw_cells_split_CB bsegs mm A [] 152 ja [] [120;8;8;8;8]%nat) in HAm; [| reflexivity].
  cbn [app mk_CB_cells] in HAm. kx_cells_split HAm.
  repeat match goal with H : rw_cells bsegs mm ?a [CB 8 ?b] |- _ => apply (afa_cb8_c8 mm a [] [] b) in H; cbn [app] in H end.
  repeat match goal with H : rw_cells bsegs mm (A + _) [C8 _] |- _ => kx_cell H end.
  kx_frame C40. kx_frame C32. kx_frame C24. kx_frame C16. kx_frame C08. kx_frame SRCm.
  match goal with H : rw_cells bsegs mm A [CB _ _] |- _ => kx_frame H end.
  kx_munch MUm.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => cbn [cells_size csize]; rewrite ?length_map; lia end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  try clearbody KXE; try clearbody KXxs.
  match goal with H : rw_cells bsegs m1 A [CB _ _] |- _ =>
    apply (rw_cells_split_CB bsegs m1 A [] 120 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in H; [| reflexivity];
    cbn [app mk_CB_cells] in H; kx_cells_split H end.
  repeat match goal with H : rw_cells bsegs m1 ?a [CB 8 ?b] |- _ => apply (afa_cb8_c8 m1 a [] [] b) in H; cbn [app] in H end.
  unfold AFA_E20 in E20.
  match goal with
  | H0 : rw_cells bsegs m1 (A + 120) [C8 (Z_to_bv 64 ?e0)], H1 : rw_cells bsegs m1 (A + 128) [C8 (Z_to_bv 64 ?e1)],
    H2 : rw_cells bsegs m1 (A + 136) [C8 (Z_to_bv 64 ?e2)], H3 : rw_cells bsegs m1 (A + 144) [C8 (Z_to_bv 64 ?e3)] |- _ =>
    eapply evtF_eq; [| eapply (E20 m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e0 e1 e2 e3)]
  end.
  all: try (lazymatch goal with |- rw_cells _ _ A (_ :: _ :: _) => kx_cells_merge end).
  all: try (lazymatch goal with |- rw_cells _ _ _ [_] => eassumption end).
  all: try (lazymatch goal with |- _ <= _ => lia | |- @eq Z _ _ => first [lia | afa_jtl] end).
  all: try (lazymatch goal with |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal end).
  all: try (lazymatch goal with |- @eq (bvmap 5 word) _ _ => f_equal end).
  all: try (lazymatch goal with |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; first [lia | afa_jtl] end).
  all: try (lazymatch goal with |- stk _ _ _ ?a => replace a with (SP - 40) by lia; assumption end).
  all: try assumption.
Qed.

  Ltac afa_x_rds HS :=
    try afa_rd constr:(32%nat) src HS BYS; try afa_rd constr:(33%nat) src HS BYS;
    try afa_rd constr:(36%nat) src HS BYS; try afa_rd constr:(37%nat) src HS BYS;
    try afa_rd constr:(40%nat) src HS BYS; try afa_rd constr:(41%nat) src HS BYS.
  Ltac afa_x_side HS :=
    lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- branch_taken _ _ _ = _ => afa_x_rds HS; afa_br
    | |- flat _ _ _ /\ _ => afa_flat
    | |- 0 <= bv_unsigned _ < 2 ^ 64 => afa_wrange
    | |- _ => rewrite ?Z.shiftr_div_pow2 by lia; try change (2^3) with 8; cbn [cells_size csize]; lia
    end.
  Ltac afa_x_lia :=
    lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => rewrite ?length_map; cbn [cells_size csize]; lia end.
  Ltac afa_x_cell H :=
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
  Ltac afa_x_cells :=
    repeat match goal with
    | HLF : log_flat ?E ?log, H : rw_cells ?segs ?m ?A [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
        first [ afa_x_cell H | kx_frame H; try afa_x_lia ]
    end.
  Ltac afa_x kd :=
    intros t0 t4 t5 t6 TL DC1 N10 mm x15 x16 x17 C40 C32 C24 C16 C08 HAm SRCm STKm MIm MUm WMm;
    pose proof (DPOS ltac:(lia)) as DP1; pose proof (SL ltac:(lia)) as SLn;
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR;
    pose proof (afa_sp0 sp lo A LOA LOS ASP A47) as SPB;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    unfold AHUF_FAST_ARGS_STACK in *;
    pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _);
    pose proof (magree_of_munch bsegs _ m0 mm MUm WMm) as MG;
    unfold rt_got in RGOT; unfold rt_shbase in RSHB;
    pose proof (rw_cells_magree bsegs _ m0 mm _ _ MG RGOT ltac:(intros a Ha; cbn [cells_size csize Nat.add Z.of_nat] in Ha; cbn [outside]; repeat split; lia)) as RGOTm;
    pose proof (rw_cells_magree bsegs _ m0 mm _ _ MG RSHB ltac:(intros a Ha; cbn [cells_size csize Nat.add Z.of_nat] in Ha; cbn [outside]; repeat split; lia)) as RSHBm;
    change (rt_got mm) in RGOTm; change (rt_shbase mm) in RSHBm;
    clear RGOT RSHB RG0 RGRIC RMEM;
    pose proof (USR ltac:(lia)) as USRn; pose proof (WSR ltac:(lia)) as (WSRa & WSRb);
    pose proof (afa_kshz m0 rstk A 152 RCL RLO RHI A8 eq_refl ltac:(lia)) as KSH;
    lazymatch type of KSH with kshz_fact _ ?o ?a ?k => assert (KSHm : kshz_fact mm o a k) end;
    [ intros x Hx; rewrite (MUm (Z_to_bv 64 (2147450880 + Z.shiftr x 3))); [apply KSH; exact Hx|];
    rewrite Z_to_bv_small by (unfold bv_modulus; cbn -[Z.pow]; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia);
    cbn [outside]; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; repeat split; lia | ];
    lazymatch type of USRn with ?P _ _ _ => assert (USRm : P mm S (S + n)) end;
    [ pose proof USRn as (U0 & U1 & U2); split; [exact U0|]; split; [exact U1|];
    intros G G1 G2 G3; destruct (U2 G G1 G2 G3) as (b & Hb & Hgr); exists b; split; [|exact Hgr];
    rewrite (MUm (wa (ASHOFF + G))); [exact Hb|];
    unfold wa, ASHOFF; rewrite Z_to_bv_small by (unfold bv_modulus; cbn -[Z.pow]; lia); cbn [outside]; repeat split; lia | ];
    pose proof afa_was as WAS;
    lazymatch type of WAS with rng _ (?o + Z.shiftr _ 3) _ =>
    assert (WAS2 : rng RNG (o + Z.shiftr A 3) (Z.shiftr (152 + A mod 8 + 7) 3)) by (rewrite A8; exact WAS) end;
    assert (WSRc : rng RNG (shad S) (Z.shiftr (n + S mod 8 + 7) 3)) by exact WSRb;
    pose proof (afa_byte_rng src 0 BYS ltac:(lia)) as BR0; pose proof (afa_byte_rng src 1 BYS ltac:(lia)) as BR1;
    pose proof (afa_byte_rng src 2 BYS ltac:(lia)) as BR2; pose proof (afa_byte_rng src 3 BYS ltac:(lia)) as BR3;
    pose proof (afa_byte_rng src 4 BYS ltac:(lia)) as BR4; pose proof (afa_byte_rng src 5 BYS ltac:(lia)) as BR5;
    try unfold jt_len in *; try change (0 + 1) with 1 in *; try change (2 + 1) with 3 in *;
    try change (4 + 1) with 5 in *;
    rewrite <- (Z_to_bv_bv_unsigned s3) in C40; rewrite <- (Z_to_bv_bv_unsigned s2) in C32;
    rewrite <- (Z_to_bv_bv_unsigned s1) in C24; rewrite <- (Z_to_bv_bv_unsigned s0) in C16;
    rewrite <- (Z_to_bv_bv_unsigned ra) in C08;
    (let PxS := constr:(@nil Z) in let PxF := constr:(500%nat : nat) in
     let PxD := eval vm_compute in (repeat false kd ++ true :: repeat false 4096) in
     let PxK := constr:([KZRange dcap 1 (2^32 - 1); KZRange n 10 (2^26 - 1); KZRange S 1 (2^47); KZRange DST 1 (2^64 - 9);
      KZRange (DST + dcap) 2 (2^64 - 8); KZRange DT 1 (2^47); KZAlign DT 8;
      KZRange SP 0x7fff7f801030 (2^47-152); KZAlign A 8; KZRange A 1 (2^47); KZWr A 152; KZDisj A 152 S n;
      KZShZ 2147450880 A 152; KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000;
      KZWord (SP + -40) 8 (bv_unsigned s3); KZWord (SP + -32) 8 (bv_unsigned s2);
      KZWord (SP + -24) 8 (bv_unsigned s1); KZWord (SP + -16) 8 (bv_unsigned s0);
      KZWord (SP + -8) 8 (bv_unsigned ra); KZDisj A 152 (SP - 48) 48] : list kz) in
     let PxR := constr:([(S, n)] : list (Z * Z)) in
     let PxW := constr:([(SP - 48, 48); (A, 152); (S, n); (0xb2128, 8); (0xba2f8, 8)] : list (Z * Z)) in
     let PxU := constr:([(S, n)] : list (Z * Z)) in
     kx_prepFm PxS PxF PxK PxR PxW PxU; kx_goFL PxD;
     try (match goal with H : kxl_exec _ _ _ _ _ _ _ = _ |- _ => clear H end));
    afa_x_side SRCm;
    apply (rw_cells_split_CB bsegs mm A [] 152 ja [] [120; 8; 8; 8; 8]%nat) in HAm; [| reflexivity];
    cbn [app mk_CB_cells] in HAm; kx_cells_split HAm;
    repeat (match goal with H : rw_cells bsegs ?m _ [CB 8 _] |- _ =>
              tryif constr_eq m m0 then fail else (apply (afa_cb8_c8 m _ [] []) in H; cbn [app] in H) end);
    afa_x_cells;
    kx_munch MUm;
    try afa_x_lia;
    kx_post_mem_free; try afa_x_lia;
    lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end;
    kx_post_regs_keep;
    zstep;
    repeat (match goal with X := _ |- _ => clearbody X end);
    apply evtF_done; unfold fast_args_postA;
    do 16 eexists; split; [reflexivity|];
    split; [exact MUm|]; split; [exact WMm|]; split; [assumption|];
    split;
    [ lazymatch goal with |- stk _ ?m _ _ =>
        eassert (FRX : rw_cells bsegs m (SP + -40) [_; _; _; _; _]); [kx_cells_merge|];
        pose proof (stk_release bsegs m lo (SP + -40) _ STKm FRX ltac:(lia)) as STK1;
        lazymatch type of STK1 with stk _ _ _ (?a + Z.of_nat ?k) =>
          let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in STK1;
          replace (bv_unsigned sp) with (a + v) by lia end;
        exact STK1 end
    | ];
    split;
    [ lazymatch goal with |- exists _, rw_cells _ ?m A _ =>
        eassert (HAX : rw_cells bsegs m A [_; _; _; _; _]); [kx_cells_merge|];
        destruct (afa_rwc_cb m A _ HAX) as (ja' & HJ); exists ja'; exact HJ end
    | ];
    first [left; reflexivity | right; left; reflexivity].

  Lemma afa_jt_x0 : jt_len src 0 < 8 ->
    forall (t0 t4 t5 t6 : word), tl = 11 -> 1 <= dcap -> 10 <= n -> forall mm (x15 x16 x17 : word),
    rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
    rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
    rw_cells bsegs mm A [CB 152 ja] -> bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
    stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp t0 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) s0 s1 (Z_to_bv 64 A)
                               (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S) (Z_to_bv 64 n) x15 x16 x17
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + dcap)) t4 t5 t6)
                           F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 140)) fc None mm (seg_rom bsegs)).
  Proof using All. intros XC0. afa_x constr:(0%nat). Qed.

  Lemma afa_jt_x1 : 8 <= jt_len src 0 -> jt_len src 2 < 8 ->
    forall (t0 t4 t5 t6 : word), tl = 11 -> 1 <= dcap -> 10 <= n -> forall mm (x15 x16 x17 : word),
    rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
    rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
    rw_cells bsegs mm A [CB 152 ja] -> bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
    stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp t0 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) s0 s1 (Z_to_bv 64 A)
                               (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S) (Z_to_bv 64 n) x15 x16 x17
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + dcap)) t4 t5 t6)
                           F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 140)) fc None mm (seg_rom bsegs)).
  Proof using All. intros XC0 XC1. afa_x constr:(1%nat). Qed.

  Lemma afa_jt_x2 : 8 <= jt_len src 0 -> 8 <= jt_len src 2 -> jt_len src 4 < 8 ->
    forall (t0 t4 t5 t6 : word), tl = 11 -> 1 <= dcap -> 10 <= n -> forall mm (x15 x16 x17 : word),
    rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
    rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
    rw_cells bsegs mm A [CB 152 ja] -> bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
    stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp t0 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) s0 s1 (Z_to_bv 64 A)
                               (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S) (Z_to_bv 64 n) x15 x16 x17
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + dcap)) t4 t5 t6)
                           F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 140)) fc None mm (seg_rom bsegs)).
  Proof using All. intros XC0 XC1 XC2. afa_x constr:(2%nat). Qed.

  Lemma afa_jt_x3 : 8 <= jt_len src 0 -> 8 <= jt_len src 2 -> 8 <= jt_len src 4 -> jt_len src 0 + jt_len src 2 + jt_len src 4 + 6 <= n -> n < jt_len src 0 + jt_len src 2 + jt_len src 4 + 14 ->
    forall (t0 t4 t5 t6 : word), tl = 11 -> 1 <= dcap -> 10 <= n -> forall mm (x15 x16 x17 : word),
    rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
    rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
    rw_cells bsegs mm A [CB 152 ja] -> bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
    stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp t0 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) s0 s1 (Z_to_bv 64 A)
                               (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S) (Z_to_bv 64 n) x15 x16 x17
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + dcap)) t4 t5 t6)
                           F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 140)) fc None mm (seg_rom bsegs)).
  Proof using All. intros XC0 XC1 XC2 XC3 XC4. afa_x constr:(3%nat). Qed.

  Lemma afa_jt_x4 : 8 <= jt_len src 0 -> 8 <= jt_len src 2 -> 8 <= jt_len src 4 -> n < jt_len src 0 + jt_len src 2 + jt_len src 4 + 6 ->
    forall (t0 t4 t5 t6 : word), tl = 11 -> 1 <= dcap -> 10 <= n -> forall mm (x15 x16 x17 : word),
    rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
    rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
    rw_cells bsegs mm A [CB 152 ja] -> bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
    stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp t0 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) s0 s1 (Z_to_bv 64 A)
                               (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S) (Z_to_bv 64 n) x15 x16 x17
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + dcap)) t4 t5 t6)
                           F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 140)) fc None mm (seg_rom bsegs)).
  Proof using All. intros XC0 XC1 XC2 XC3. afa_x constr:(4%nat). Qed.

  Lemma afa_jt : AFA_E20 -> forall (t0 t4 t5 t6 : word), tl = 11 -> 1 <= dcap -> 10 <= n -> forall mm (x15 x16 x17 : word),
    rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
    rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
    rw_cells bsegs mm A [CB 152 ja] -> bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
    stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp t0 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) s0 s1 (Z_to_bv 64 A)
                               (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S) (Z_to_bv 64 n) x15 x16 x17
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + dcap)) t4 t5 t6)
                          F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 140)) fc None mm (seg_rom bsegs)).
Proof using All.
  intros E20.
  destruct (Z_lt_le_dec (jt_len src 0) 8) as [H0|H0]; [exact (afa_jt_x0 H0)|].
  destruct (Z_lt_le_dec (jt_len src 2) 8) as [H1|H1]; [exact (afa_jt_x1 H0 H1)|].
  destruct (Z_lt_le_dec (jt_len src 4) 8) as [H2|H2]; [exact (afa_jt_x2 H0 H1 H2)|].
  destruct (Z_lt_le_dec n (jt_len src 0 + jt_len src 2 + jt_len src 4 + 14)) as [H3|H3].
  - destruct (Z_lt_le_dec n (jt_len src 0 + jt_len src 2 + jt_len src 4 + 6)) as [H4|H4].
    + exact (afa_jt_x4 H0 H1 H2 H4).
    + exact (afa_jt_x3 H0 H1 H2 H4 H3).
  - exact (afa_jt_m E20 H0 H1 H2 H3).
Qed.
End AFA2.
End CANSEC1.
