(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_HufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s1k AF_huf_w4s1x AF_huf_w4s12_iface.
Ltac2 kr_t_AF_huf_w4s1kb () := "C5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4s1k9w4s1_dctxC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4s1k?w4s1_x1tab_factK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr02I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5Plain<RF_huf_iface8x1_bytesC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit29x1_bytes'C47Corelib4Init3Nat3minK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3minI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2@x1_bytes'_lengthC46Stdlib5Lists4List=length_firstnC46Stdlib5Lists4List:length_mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp05K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk09K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk08K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk06K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC47Corelib4Init5Logic5proj2K47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond03C5ARocqVerifyHarness?AgentSubmission6Common5KXTac9idx_factsC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zle_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac<idx_facts_okC47Corelib4Init5Logic6eq_indC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC5ARocqVerifyHarness?AgentSubmission6Common4KXGo5zt_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXMem;kx_u8arr_exC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula02C56Stdlib5Arith8PeanoNat3Nat3ltbC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC57Corelib7BinNums6PosDef3Pos;of_succ_natK47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes6option01C47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zk_word_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06C5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry01C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickI47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib7Numbers7BinNums1Z01I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib4Init9Datatypes4bool02I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv3Sem2w0I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI46Stdlib5Lists4List6Exists00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00c5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4s1kb>w4s1_decB_case".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Notation amem := (word -> option byte).

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.

Definition w4s1_decB_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp y6 y7 y9 y22 w0 : word) (pad1 pad2 pad3 pad4 tb : list byte) (obuf : list Z)
    (SP DST dcap e1 j DT tl rsv DBL DBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 : Z),
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl -> mem_inv bsegs mm ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  bytes_at bsegs mm (DT + 4) tb -> Z.of_nat (length tb) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) -> Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 (Z_to_bv 64 (tl + 256 * rsv)); C8 (Z_to_bv 64 (DST + 3 * e1)); C8 (Z_to_bv 64 (DST + dcap - 3));
     C8 (Z_to_bv 64 e1); C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DST + e1));
     C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * e1)); C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> 0 <= j -> 0 <= e1 -> 3 * e1 + j + 4 <= dcap -> dcap <= 2^32 ->
  0 <= b1 <= 88 -> 0 <= b2 <= 88 -> 0 <= b3 <= 88 -> 0 <= b4 <= 88 ->
  0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
  4096 <= S1 + o1 <= 2^47 -> 4096 <= S2 + o2 <= 2^47 -> 4096 <= S3 + o3 <= 2^47 -> 4096 <= S4 + o4 <= 2^47 ->
  4096 <= DT <= 2^47 -> 2^20 <= SP <= 2^47 ->
  (forall (mm' : amem) (obuf' : list Z) (N1 N2 N3 N4 N5 N6 N7 N8 : Z) (y12 y13 y14 y15 y16 y21 y23 : word),
     munch [(DST, DST + dcap); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 (b1 + (N1 + N5))); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 (b2 + (N2 + N6))); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 (b3 + (N3 + N7))); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 (b4 + (N4 + N8))); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     0 <= N1 <= 12 -> 0 <= N2 <= 12 -> 0 <= N3 <= 12 -> 0 <= N4 <= 12 ->
     0 <= N5 <= 12 -> 0 <= N6 <= 12 -> 0 <= N7 <= 12 -> 0 <= N8 <= 12 ->
     evtF bsegs RNG Q
        (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (b2 + (N2 + N6))) (Z_to_bv 64 (b3 + (N3 + N7)))
                 (Z_to_bv 64 (b4 + (N4 + N8))) (Z_to_bv 64 (j + (DST + e1) + 3)) (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) (Z_to_bv 64 (-20))
                 (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) y12 y13 y14 y15 y16 (Z_to_bv 64 (b1 + (N1 + N5)))
                 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 j) y21 (Z_to_bv 64 (j + (DST + 2 * e1) + 3)) y23
                 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 c4) (Z_to_bv 64 (2^62))
                 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (j + (DST + 3 * e1) + 2)))
            F (Z_to_bv 64 0x8a5f0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (j + DST + 1)) y6 y7
                (Z_to_bv 64 b1) y9 (Z_to_bv 64 (-20)) (Z_to_bv 64 (j + (DST + 3 * e1))) (Z_to_bv 64 (j + (DST + 2 * e1)))
                (Z_to_bv 64 (j + (DST + e1))) (Z_to_bv 64 (j + DST)) (Z_to_bv 64 (j + (DST + 3 * e1) + 1))
                (Z_to_bv 64 (j + (DST + 2 * e1) + 1)) (Z_to_bv 64 (j + (DST + e1) + 1)) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3))
                (Z_to_bv 64 j) (Z_to_bv 64 b3) y22 (Z_to_bv 64 b4) (Z_to_bv 64 0x7fff8000)
                (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 c4) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl))
                (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 b2))
          F (Z_to_bv 64 0x8a1d8) fc None mm (seg_rom bsegs)).

Ltac kxr_ev := lazymatch goal with
  | |- _ <= bv_unsigned (ev ?E ?j) <= _ => let H := fresh "HR" in kx_range (EVar j) H; exact H
  end.

Ltac w4ge_pre tl :=
  lazymatch goal with
  | |- branch_taken _ (edenot ?E ?a) (edenot ?E ?c) = _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let na := eval vm_compute in (length zv) in
        change E with (kE zv xs);
        rewrite (ez_ok zv (kE zv xs) (kE_atoms zv xs) a), (ez_ok zv (kE zv xs) (kE_atoms zv xs) c);
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with |- context [bv_unsigned (edenot ?E' (EAlu ALU_SRL ?x ?s))] =>
          lazymatch goal with _ : 0 <= bv_unsigned (edenot E' (EAlu ALU_SRL x s)) < 2^62 |- _ => fail | _ => idtac end;
          let SB := fresh "SB" in
          assert (SB : 0 <= bv_unsigned (edenot E' (EAlu ALU_SRL x s)) < 2^62)
            by (apply w4_srl_lt62; rewrite (ez_ok zv (kE zv xs) (kE_atoms zv xs) s); cbv [ez]; change (length zv) with na;
                cbv [nth Nat.ltb Nat.leb]; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64);
                rewrite (Z.mod_small _ (2^64)) by lia; rewrite (Z.mod_small _ 64) by lia; lia)
        end;
        kx_abstract;
        unfold branch_taken; try unfold bv_lts;
        rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?zb_signed, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (2 ^ Z.of_N 64) with (2^64);
        rewrite ?Z.mod_small by lia
      end
  end.
Ltac w4ge tl :=
  w4ge_pre tl;
  repeat (match goal with |- context [(?x <? ?y)%Z] =>
            lazymatch x with context [Z.ltb _ _] => fail | _ => idtac end;
            lazymatch y with context [Z.ltb _ _] => fail | _ => idtac end;
            destruct (Z.ltb_spec x y) end; cbv beta iota);
  repeat (match goal with |- context [(?x =? ?y)%Z] => destruct (Z.eqb_spec x y) end; cbv beta iota);
  cbn [negb]; first [reflexivity | exfalso; lia].
Ltac w4fl_pre :=
  lazymatch goal with
  | |- flat ?E ?a1 ?n1 /\ flat ?E ?a2 ?n2 /\ _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let na := eval vm_compute in (length zv) in
        change E with (kE zv xs); unfold flat, elenZ;
        cbn [edenot]; rewrite ?Z_to_bv_unsigned;
        unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); rewrite ?(Z.mod_small 1) by lia;
        rewrite (estart_ez_kE zv xs a1) by (cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
            try change (2 ^ (3 mod 64)) with 8; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia);
        rewrite (estart_ez_kE zv xs a2) by (cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
            try change (2 ^ (3 mod 64)) with 8; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia);
        cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        try change (2 ^ (3 mod 64)) with 8; rewrite ?Z.mod_small by lia
      end
  end.
Ltac w4fl := w4fl_pre; Z.div_mod_to_equations; lia.
Ltac w4m1_post :=
  kx_post_regs_keep;
  lazymatch goal with
  | OUT : u8arr bsegs ?m0 ?D (map (Z_to_bv 8) ?ob), HL : log_flat _ _, HR : 3 * ?ee + ?jj + 4 <= ?dc,
    HS : 2^20 <= ?sp <= 2^47, KK : context [munch ?W _ _] |- _ =>
      let obuf' := fresh "obuf'" in let OUT' := fresh "OUT'" in let LB' := fresh "LB'" in
      destruct (kx_u8arr_ex bsegs _ m0 _ D ob OUT HL) as (obuf' & OUT' & LB');
      repeat match goal with Dk : rw_cells bsegs m0 _ (_ :: _ :: _) |- _ =>
        lazymatch type of Dk with
        | rw_cells _ _ (sp + -376) _ => kx_cells_split Dk
        | rw_cells _ _ (sp + -144) _ => kx_cells_split Dk
        | rw_cells _ _ (sp + -184) _ => kx_cells_split Dk
        | rw_cells _ _ (sp + -224) _ => kx_cells_split Dk
        end end;
      w4_cells_post;
      let MU := fresh "MU" in let WM := fresh "WM" in
      pose proof (munch_refl W m0) as MU; pose proof (wmono_refl bsegs m0) as WM;
      kx_munch_wins MU [(D + jj, 4); (D + ee + jj, 4); (D + 2 * ee + jj, 4); (D + 3 * ee + jj, 4);
                        (sp + -368, 4); (sp + -216, 4); (sp + -176, 4); (sp + -136, 4)];
      kx_post_mem_free;
      eapply KK; [ exact MU | exact WM | eassumption | exact OUT' | rewrite LB'; lia | .. ]
  end.
Theorem w4s1_decB : w4s1_decB_case.
Proof.
  unfold w4s1_decB_case.
  intros Q RNG mm F fc gp tp y6 y7 y9 y22 w0 pad1 pad2 pad3 pad4 tb obuf
    SP DST dcap e1 j DT tl rsv DBL DBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4
    C MI TB TBB TBL TBP OUT LO FR B1 B2 B3 B4 HTL HRS HJ HE HROOM HDC HB1 HB2 HB3 HB4 HC1 HC2 HC3 HC4 HP1 HP2 HP3 HP4 HDT HSP K.
  w4s1_dctx_intro C.
  kx_runFmd [0x8a5f0; 0x8ac7c; 0x8c660] 300%nat (repeat true 64)
      [KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZIdx tl (2^tl); KZRange (2^tl) 2 4096; KZRange tl 1 12; KZRange (64 - tl) 52 63;
       KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange dcap 4 (2^32); KZRange (dcap - 3 * e1 - j) 4 (2^32);
       KZRange (3 * e1 + j) 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47 - 8196); KZRange SP (0x10007fff8000 + 480) (2^47); KZRange (dcap - 2 * e1 - j) 4 (2^32); KZRange (dcap - e1 - j) 4 (2^32); KZRange (dcap - j) 4 (2^32);
       KZRange (DST + e1) 4096 (2^47); KZRange (DST + 2 * e1) 4096 (2^47); KZRange (DST + 3 * e1) 4096 (2^47);
       KZDisj DST dcap 0x7fff8000 17592186044416; KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480;
       KZDisj (DST + j) 4 0x7fff8000 17592186044416; KZDisj (DST + j) 4 (SP + -480) 480; KZDisj (DST + j) 4 (DT + 4) (2 * 2^tl); KZWr (DST + j) 4;
       KZDisj (DST + e1 + j) 4 0x7fff8000 17592186044416; KZDisj (DST + e1 + j) 4 (SP + -480) 480; KZDisj (DST + e1 + j) 4 (DT + 4) (2 * 2^tl); KZWr (DST + e1 + j) 4;
       KZDisj (DST + 2 * e1 + j) 4 0x7fff8000 17592186044416; KZDisj (DST + 2 * e1 + j) 4 (SP + -480) 480; KZDisj (DST + 2 * e1 + j) 4 (DT + 4) (2 * 2^tl); KZWr (DST + 2 * e1 + j) 4;
       KZDisj (DST + 3 * e1 + j) 4 0x7fff8000 17592186044416; KZDisj (DST + 3 * e1 + j) 4 (SP + -480) 480; KZDisj (DST + 3 * e1 + j) 4 (DT + 4) (2 * 2^tl); KZWr (DST + 3 * e1 + j) 4;
       KZWr (SP + -376) 40; KZWr (SP + -144) 40; KZWr (SP + -184) 40; KZWr (SP + -224) 40;
       KZRange (DST + 3 * e1 + j) 4096 (2^47); KZRange (DST + 2 * e1 + j) 4096 (2^47); KZRange (DST + e1 + j) 4096 (2^47);
       KZRange (DST + j) 4096 (2^47); KZRange rsv 0 255;
       KZRange b1 0 88; KZRange b2 0 88; KZRange b3 0 88; KZRange b4 0 88;
       KZRange c1 0 (2^64 - 1); KZRange c2 0 (2^64 - 1); KZRange c3 0 (2^64 - 1); KZRange c4 0 (2^64 - 1);
       KZRange (S1 + o1) 4096 (2^47); KZRange (S2 + o2) 4096 (2^47); KZRange (S3 + o3) 4096 (2^47); KZRange (S4 + o4) 4096 (2^47);
       KZWord (SP + -472) 8 (tl + 256 * rsv); KZWord (SP + -464) 8 (DST + 3 * e1); KZWord (SP + -456) 8 (DST + dcap - 3);
       KZWord (SP + -448) 8 e1; KZWord (SP + -440) 8 c3; KZWord (SP + -432) 8 c2; KZWord (SP + -424) 8 c1;
       KZWord (SP + -416) 8 (DST + e1); KZWord (SP + -408) 8 dcap; KZWord (SP + -400) 8 DST; KZWord (SP + -392) 8 (DST + 2 * e1);
       KZWord (SP + -384) 8 (DST + dcap);
       KZWord (SP + -376) 8 c1; KZWord (SP + -144) 8 c2; KZWord (SP + -184) 8 c3; KZWord (SP + -224) 8 c4;
       KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl); KZWr DST dcap]
      [(DT + 4, 2 * 2^tl)] [(DT + 4, 2 * 2^tl); (SP + -480, 480); (DST, dcap)] [(DT + 4, 2 * 2^tl); (DST, dcap); (DST + j, 4); (DST + e1 + j, 4); (DST + 2 * e1 + j, 4); (DST + 3 * e1 + j, 4)].
  all: try (w4ge tl).
  all: try (unfold KXGoM.apart in AB, AT, AF, ATF).
  all: try w4fl.
  all: try lia.
  all: lazymatch goal with |- evtF _ _ _ _ => w4m1_post | |- _ => idtac end.
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
  all: try kxr_ev.
Qed.

Definition w4s1_rall_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp y12 y13 y14 y15 y16 y21 y23 w0 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap e1 j DT tl rsv DBL DBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 : Z)
    (SS n SBL SBH L1 L2 L3 L4 : Z),
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl -> mem_inv bsegs mm ->
  w4s_src_ctx RNG mm SS n SBL SBH -> KXGoM.apart SS n (SP + -480) 480 -> KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) -> Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 (Z_to_bv 64 (tl + 256 * rsv)); C8 (Z_to_bv 64 (DST + 3 * e1)); C8 (Z_to_bv 64 (DST + dcap - 3));
     C8 (Z_to_bv 64 e1); C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DST + e1));
     C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * e1)); C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> 0 <= j -> 0 <= e1 -> 3 * e1 + j + 4 <= dcap -> dcap <= 2^32 ->
  0 <= o1 -> 0 <= o2 -> 0 <= o3 -> 0 <= o4 ->
  (o1 = 0 /\ 0 <= b1 <= 112) \/ (o1 + 8 <= L1 /\ 0 <= b1 <= 56) ->
  (o2 = 0 /\ 0 <= b2 <= 112) \/ (o2 + 8 <= L2 /\ 0 <= b2 <= 56) ->
  (o3 = 0 /\ 0 <= b3 <= 112) \/ (o3 + 8 <= L3 /\ 0 <= b3 <= 56) ->
  (o4 = 0 /\ 0 <= b4 <= 112) \/ (o4 + 8 <= L4 /\ 0 <= b4 <= 56) ->
  SS <= S1 -> S1 + L1 <= SS + n -> SS <= S2 -> S2 + L2 <= SS + n ->
  SS <= S3 -> S3 + L3 <= SS + n -> SS <= S4 -> S4 + L4 <= SS + n ->
  0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
  4096 <= S1 + o1 <= 2^47 -> 4096 <= S2 + o2 <= 2^47 -> 4096 <= S3 + o3 <= 2^47 -> 4096 <= S4 + o4 <= 2^47 ->
  4096 <= DT <= 2^47 -> 2^20 <= SP <= 2^47 ->
  (forall (mm' : amem) (obuf' : list Z) (o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' : Z) (x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 (Z_to_bv 64 (tl + 256 * rsv)); C8 (Z_to_bv 64 (DST + 3 * e1)); C8 (Z_to_bv 64 (DST + dcap - 3));
        C8 (Z_to_bv 64 e1); C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2'); C8 (Z_to_bv 64 c1'); C8 (Z_to_bv 64 (DST + e1));
        C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * e1)); C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1'); C4 (Z_to_bv 64 b1'); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1')); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2'); C4 (Z_to_bv 64 b2'); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2')); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     8 <= o1 -> o1' = o1 - b1 / 8 -> b1' = b1 mod 8 -> 8 <= o2 -> o2' = o2 - b2 / 8 -> b2' = b2 mod 8 ->
     8 <= o3 -> o3' = o3 - b3 / 8 -> b3' = b3 mod 8 -> 8 <= o4 -> o4' = o4 - b4 / 8 -> b4' = b4 mod 8 ->
     0 <= c1' < 2^64 -> 0 <= c2' < 2^64 -> 0 <= c3' < 2^64 -> 0 <= c4' < 2^64 ->
     3 * e1 + (j + 4) + 4 <= dcap ->
     evtF bsegs RNG Q
       (MS (mkR (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 b2') (Z_to_bv 64 b3') (Z_to_bv 64 b4') x8 x9
                (Z_to_bv 64 (-20)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 b1') (Z_to_bv 64 (S2 + o2')) (Z_to_bv 64 (S3 + o3'))
                (Z_to_bv 64 (j + 4)) (Z_to_bv 64 DST) x22 x23 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (S1 + o1')) (Z_to_bv 64 (DT + 4))
                (Z_to_bv 64 c4') (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1 * DT + -5)) x31)
           F (Z_to_bv 64 AW4_LHEAD) fc None mm' (seg_rom bsegs))) ->
  (forall (mm' : amem) (obuf' : list Z) (o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' : Z) (w40 w48 w56 : word)
          (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 (Z_to_bv 64 (tl + 256 * rsv)); C8 (Z_to_bv 64 (DST + 3 * e1)); C8 (Z_to_bv 64 (DST + dcap - 3));
        C8 (Z_to_bv 64 e1); C8 w40; C8 w48; C8 w56; C8 (Z_to_bv 64 (DST + e1));
        C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * e1)); C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1'); C4 (Z_to_bv 64 b1'); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1')); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2'); C4 (Z_to_bv 64 b2'); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2')); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o1 < 8 /\ o1' = o1 /\ b1' = b1) \/ (8 <= o1 /\ o1' = o1 - b1 / 8 /\ b1' = b1 mod 8) ->
     (o2 < 8 /\ o2' = o2 /\ b2' = b2) \/ (8 <= o2 /\ o2' = o2 - b2 / 8 /\ b2' = b2 mod 8) ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8) ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8) ->
     0 <= c1' < 2^64 -> 0 <= c2' < 2^64 -> 0 <= c3' < 2^64 -> 0 <= c4' < 2^64 ->
     evtF bsegs RNG Q
       (MS (mkR (Z_to_bv 64 (DST + 3 * e1)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + e1 + (j + 4))) x9
                (Z_to_bv 64 (-20)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + (j + 4))) (Z_to_bv 64 (tl + 256 * rsv))
                (Z_to_bv 64 (DST + 3 * e1 + (j + 4))) x21 (Z_to_bv 64 (DST + 2 * e1 + (j + 4))) (Z_to_bv 64 (DST + e1))
                (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) x28 x29 x30 x31)
           F (Z_to_bv 64 AW4_LFIN) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
     (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 b2) (Z_to_bv 64 b3)
              (Z_to_bv 64 b4) (Z_to_bv 64 (j + (DST + e1) + 3)) (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) (Z_to_bv 64 (-20))
              (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) y12 y13 y14 y15 y16 (Z_to_bv 64 b1)
              (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 j) y21 (Z_to_bv 64 (j + (DST + 2 * e1) + 3)) y23
              (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 c4) (Z_to_bv 64 (2^62))
              (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (j + (DST + 3 * e1) + 2)))
         F (Z_to_bv 64 0x8a5f0) fc None mm (seg_rom bsegs)).

End CANSEC1.
