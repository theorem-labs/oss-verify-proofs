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
Ltac2 kr_t_AF_huf_w4s1k () := "C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2Cnth_error_firstn_ltC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission5Plain<RF_huf_iface8x1_bytesC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit29x1_bytes'C47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3minK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2@x1_bytes'_lengthC46Stdlib5Lists4List=length_firstnC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission6Common5KXTac:find_fieldK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2ex00C47Corelib4Init5Logic7f_equalK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX19x1_nbBitsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX17x1_byteC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2>x1_bytes'_nth0C47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission6Common5KXTacBztab_fact_bytes_atC47Corelib5Lists7ListDef3nthK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4s1k9w4s1_dctxC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4s1k?w4s1_x1tab_factC46Stdlib5Lists4List:length_mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp05K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk09K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk08K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk06K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond03C5ARocqVerifyHarness?AgentSubmission6Common5KXTac9idx_factsC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zle_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac<idx_facts_okC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC5ARocqVerifyHarness?AgentSubmission6Common4KXGo5zt_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXMem;kx_u8arr_exC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula02C56Stdlib5Arith8PeanoNat3Nat3ltbC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC57Corelib7BinNums6PosDef3Pos;of_succ_natC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zk_word_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06C5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry01C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib4Init9Datatypes4bool02I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00C4ELinuxProcessSemantics5Riscv3Sem2w0I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI46Stdlib5Lists4List6Exists00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlI47Corelib4Init9Datatypes:comparison00c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4s1k>w4s1_decA_case".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Notation amem := (word -> option byte).

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Lemma w4s1_x1tab_fact : forall mm A cells tl, x1_table_ok cells tl ->
  bytes_at bsegs mm A (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells)) -> ztab_fact bsegs mm A (2 * 2^tl) 2 [(0, 0, 12)].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4s1k ()) [] "p'0h04__x1h14__p1h24__x2h34cstrh47__arithh54__ffh68__varmaph75__with81Hh94__x3h:4__x4h;1bi001bh<4__p2h=4__p3h>4__p4h?1ih@1xhA2H3hB2HfhC4__p5hD2z3hE2H4hF1ei011ehG1ni021nhH2z4hI2E0hJ4__p6hK4__x5hL3fhihM3flohN1yhO1AhP2EIhQ2HBhR2HVhS2HihT2NBhU2P2hV2TChW3TCKhX2TLhY3TOKhZ2_Hh[5cellsh\2mmh]1oi031oh^1ri041rh_2tlh`1zi051zi061pp%0p&0p&1p;1p;2p;3p;4p;6p;5p;<p;:p;7p;8p;Bg0000R0p4p710g001;R1p4p710R2p8p1001Yp4p70R3p1002Op4p710p8P3p1002kp4p710R3p8p1003Lp4p7210P2p8p10048p4p70P3p8p1004np4p70P3p8g005dj17Tg006Ik10STg006gk10CTg007JS00k10;Tg007lk10QTg008Lk20GTg009Oj1jTg009mR3j12Tg00:Mk10gTg00;Mj3OTg00;lk40_Tg00<aR2j20Tg00==j2:Tg00=Zj2uTg00>Uj2iTg00?WR4j25Tg00@4R5k20DTg00@Tj4tTg00A4j1|Tg00AYk10BTg00B9j3eTg00BYk60?Tg00CTj1[Tg00D9R6j19Tg00DYk10fTg00E7k10eTg00EUk10cTg00F@j2lTg00Fck20]Tg00GEk208Tg00G_k20[Tg00HKj33k10RTg00Hek30XTg00IDk410Tg00J6j2dTg00JTk20:Tg00K7k10LTg00KYk50HTg00L@R7j21Tg00L[j4~Tg00M6j1RTg00N7k204Tg00NWk202Tg00Nnj1_Tg00OMk201Tg00OdR8k200Tg00PAk10lTg00P_l<}Tg00QDk20iTg00QfR9j2FTg00RBk20hTg00Rkj3fTg00STk10ATg00T2k20@Tg00TSj3kTg00U<k20>Tg00Uek20=Tg00VQj3pTg00W4j4oTg00W_k10bTP1j6gTg00Xgk30aTg00YIj2PTg00Yik20`Tg00Zej2MTg00[Gk20^Tg00[ik209Tg00\FR1k20\Tg00\ij3STg00]Gk20JTg00^1j2mTg00^Kk607Tg00^hk60ZTg00_Lk30YTg00_mj2=Tg00`Jk206Tg00`gk30WTg00aJk40VTg00akk50UTg00bWj1cTg00cXk10TTg00dWk205Tg00e=k20~Tg00e`k30}Tg00f=R:k20PTg00fUk30|Tg00g[j6rTP0k50zTg00h7k20yTg00h]k30xTg00i@k20wTg00iok40vTg00jIk10uTg00jbk20tTg00kAm:0sTg00lEk40rTg00laj4`Tg00mLj7nTg00n0k60qTg00nTk703Tg00o8j8vTg00o\k20pTg0109m<0ITg010^mB0KTg011Dk20oTg011fj2zTg012@j3sTg012ik20FTg013Uk40nTg0143k70mTf2R0f1R;f0R<':'5p=?100;/1<p=@g014WR=/0<p=41F;<,10p=Eg0155R>P;P<g0165H0rp=B204><p=IP0g0177R?g017VR@P@g0186RAg018VRBP;g0194RCP<C`g019[RDFnp=b1F=<p=AP0P?P@P@PAPBP;g01:;REP<C`PDFnp=>P;P?P@P@PAP<J0qp=Jf5RFP?P@P@PAf4RGP?P@P@PAf3RHP0K03P;P<Gvp=W20p=<p=6208B<p=LPBg01:bRIPBPBP3PGP6PHg01;AP0P;P<N<0Ip=hPIPIPIPBPBPBg01;nP6P6P6P4g01<NPFPGPHP0P;P<NB0Kp>0EPIPIPIPBPBPBg01=1P6P6P6P8g01=QPFPGPHP0P;P<NB0Kp>0kPIPBPBPBP6P6PFPGPHP0P;P<N<0Ip>0j20o=<p=]A3B<=p=G10;=/1<p=VA3B0;,1H/z<p=HA3B;<p=820>B<p=\AsB;<g01>4R8+0Fp=ZAsB;<p=;AsB;<9sB0p=^g01>`R4?e;<p>0<20F;8=e4<p=DAe4;<9e40p=qPBP0P;P<H0np=<20:B<p=YPBP;g01?LR8P<C`p=TPHP?P@P@PAP0P;P?P@P@PAP<PDFnK03p=CP0P?P@P@PAPBP;P8P<C`PDFnp=NP0P?P@P@PAP;P<K03p=KP0P?P@P@PAP;P<K0mp=UPHP?P@P@PAP0P;P<Gvp={f6RDP?P@P@PAPFPGPHP?P@P@PAP0P;P<GvGvp=QA3B;<,10p>0dPBPBP;P<Ctp=wA3B=<p=a10;<,10p=X10<=p=x110;/z<p=yPIPBP:P6P9g01@3PFPGPHP0P;P<M<}p>0OPBP;PCP<C`p>0N11H010;=/1<'zp>0{PBP;PEP<C`p>0Mg01@URE#7RC#7R9#7S01#7#7#7R:$0S$0CQ01$0SR8$0CR3$0;RJ[&0Q>20G;<g01A:RKPGPH%jCRL??L;#2&0g05O3H0_P;20GH0P7%jERMg01AoRN,0H7@H1:LH1u>G%4<RO1:LGRP7E<%2;RQ/BD,iF[^?B3@PKf7RRPD15LPPL20DBBRP00DBRSPPPBPBPBP=P=Ct%|ES02#7RT#7#jRUCt&0BS3eRSJ0?P<10FN9@MF1:LD1u>R1:LRRN9EO<f8RVf9RW,BQ'i[^?B3@P71u>V,0N1:LVRN9EO<f:RX,BQ,iW[^?BPKf;RYPX15LNPLPSJ0?P<1:LW1u>X'01:LYR>9EO<f<RNf=RZ,BQ'i[^?B10L>RQ%7:#7S03#7#7#7#7#jR:,0>R>PLPMPY%INR[#[R\%9[#4R[&0B4R]&0Q4R4&0fBR^&0eBR_&0cBR`1lB=Ra1lBLRb3b20]`ARcP<P0g01C7Rdg01CWRe+0820[<0=3dedB0XB=;H10Reb5b6b7%ALP<b4S04b3RfP\P[p-0RgP]P41dB;RhP_P`P`1lBM20:BERi5>`Rj1J`HS05&0L@RkPjEWPcPeb5b6b7X0BW1A@M<;10M;[^0B^1gP<10ZUPZPRO3b4b3I0HPLPYPUPfP\P[P]P4PhP_P`P`Q051lBUS069>`iS07PkQ07EWPcPeb5b6b7X0BX1g10<US08,1;10;U[^0B^1gP<10MZPZPRO3b4b3I0HC~11Q>PKf?RKf>R>A?LLNRQPLPS%2QR[%RZR\5O3RfPXPI2043\Rj-02[A?LLZRl%9<Rm'0XGIPIg01D7Rn#_Ro#_Rp%IZRq+01Rr%2l002<#9,0lXGI202[rRs#9Rt,0Q%6QRu%9qRv,5LRw+00Rx,0QPBPBP2P<X@BRyP210;<$0lXNBX@BPQPQ%LQR2PtPxPyPy%LmX@IPsPxP[PuPy%6<X@BS09PQPQP2DhPrPwPpPL%LLS0:PqPv%LvJ0EJ0kJ0jM<}%[q%4v%]l%Al%6lRvPl%Gv,VlCHA?LL>#6PBf@Rl#I#9,5LRv-0i<1F<v200<vRqP<18qv9@v<CHfAS0;#I#9,5L-00;PB%_pRv#\Rq20hBLRw%\pRr5fB'ZR2&0AE-0@BRE%_vS0<#\Rv5kBRQ20>BnRn';1Znr+0=AkBEq=^Qn20<2]'D3qP41dBHR2?<0^S0=1dBGRu?<G^S0>7<;P_P`P`1J`DS0?P`%YCRx%|C#YRs'TCC1J`RS0@%Y9R99pBbS0A9N`xS0B5K`5U`PkP`P`1J`VS0CP`ApBbiRt,TsCCA>`ta1J`WS0D5K`5U`PkP`P`A>`bi1J`XS0EPkP`A>`i9PkA>`txC{EWFQPcPeb5b6b7X0BX2BX9BX:BX1gX<gX=gX>gXCgPGP;PH15L0Rs:0dF;CHPRPG15L;Rz1VzVCHA@L0X10HF15LG/0F[[[[^0B^2B^9B^:B^1g^<g^=g^>g^CgP<fBR{,:LR|/0:%GHS0F15L|#AfCS0G#I#9R},5LR~/0H1FH~PHP}P;P|P0PGPDPVO=b4bHbEbDbAb3CoPj&0bZEg2043fB0a3[\Eg%40S0HA?LLK7E0&0;PR\1PHL00`S1w0;,MP331PGLRS-0^=%aS209=S+0\1PFL-09=PdP11PDL#aPdP\P;PBPBP=PUCt,MPRd&0LPS0In01000000200001wRD,MPS0J53\fGR19?LL#2fHRS#R5O3%2X5S31M3<R[53J20J8<Rf10fV5@W'1X;3,m3]BP;1PRL#aS0KQ0J93\dP\PBQ00PPPBP<P5PBPBPBP<P<n2001106000120105105PUn10110300021010600XF\Pd1wVR,MPS0LP<J0718URP\PBQ00PPPBP<P5PBPBPBP<P;n2001106000120105105P=n10110300021010600XF\Pd1wWV,MPP;J07%aW%aXPBP=18UYfLR=9?LL#2fMRd#R5O3%2K5S3=3J[R510fZ9@0f'1X;3,m3[XMB18UXPBPU%4fRj?Xf;,15X;3,m3XLBfKS0M#IR5#[%95#4P]P4P^P_P`P?P@P@PAAN`baJ0ZPcPeb5b6b7%GLg01DVS0N[P<b4b3:0YZL1=ZL,5LRA1PZL+06,8Z%I=R@#[R?%9@#4R@AkBErR5%\oRo/;nR|';AkBEoS0O/;nS0P,;r/D]'DP4A<^02?<;^P_P`ApBbxRE%YTRT60WB9N`iPkP`AN`aTPkAN`iEFQPcPeb5b6b7X0BX2BX9B206z0,8<%aH15LHS0Q,80S0R[[^0B^2B^9BP<1PlL1=lLR}PlP0PVO5b4b3b818ZA1=>LRA#4R~Q0M,:LS0S,FARAP>PLP?P@P]P4PhP_P`P`A>`aiRhQ05PkPhEWPcPeb5b6b7X0BX1g11O;%4;[^0B^1gP<1:LdS05,5L,FlPlPZO3b4b3P?P@Q04b3S04H0VP>PLQ0SQ04P?P@P]P41dB0?<;^S04P_P`P`1J`GS0SAb`iEREPkPEEWPcPeb5b6b7X0BX2BX1gAE0<z1F;s[^0B^2B^1gP<%4lQ05PlPZO4b4b3I0UC~11~AQ0;1=KLRKP<O2%2K/Bd,i=P7%2}fN'BR}#cR7#4?X7d&0T}R}#4Q03#jR77E}fOR}9?LL#2fPRK#R5O3%2{5S3=3J[AXjfURj'1X;3,m3P<1={L#2/BK#cRK#4?XK}Q0G/=L#2fQRK'B$0TR}#4?E}7P3fRR}9?LLR{#2fSRA#R5O3fER~#2S0G5S3=3J[/1jX;3fDRj/=LRZ#2S03/B}#cRl-058RsA?LLKRK#2Rz%R}S0;5O3%2jRE5S3S051M3s53J20J8sS0T#4Q0T;XUPJQ0;=S3E1=~LRs#2R@/BA#c-058,M393J<X]JQ03-01pS0U=3IES0V%6ZS0W,5LS0X%6jR?'8PIPB&0RIP6&0RB%9;/8mA3I;<20~;<40}XNIX@IQ0UQ0XPpPLQ0:Q03Q0WPyQ09PZPZ%LZDhJ0EPEP?PyQ09PjPj%LjDhS0WM<}%I}R}#[S03%9}#4R}%]~%A~%6~RjP~%Gj,V~CHfFR~#6PB1=1LRj#]%Aj%6jRZPj%GZ,VjCH1=SL#6PBAfBwvRj?^5n&0AC-0@B=kBvRC1;rnS0:';1;qoQ0<#_Rm#_#\,Zn+0=R6Q0P9^j51;r|Rr,;C%\mRm9fBwQ0O,;q'ZRC?qC]'D'D7q6'D'DP4Q0>?<02?<;^P_P`P`Q01#YR29b`aP`1Ti2CCA>`2aAN`iaR65K`5U`PkP`P`Ab`aTP`1TxTCCP`A>`TaP`1TxaCC5U`PkP`ApBb29N`TS01PkAN`txC{FQPcPeb5b6b7X0BX2BX9BX:B%AHRt18<HRC%xHRj%G<R5'13yPtP0PH%G0,1jCH15LF,8GQ0Q/8G[[[^0B^2B^9B^:BP<fJRj/=LRtPjPHP;P0PGPNO7b4bHbEbDbAb3CoQ0VPI201p@fTRp#R=S3<1=~LR~#2/Bp#cS0V-058,M353JXGI%IARI-0P@%6sS0>%9IRp'FP@Q0>PyQ09PsPs%LsDhPIPp%LpJ0O%[I%4p%]~%A~%6~RpP~%Gp,V~CHPZPB1;vrA^vq|/D]'DP4Q0=A<^Gu7<;P_P`P`Q0?P`Q02#|#YR|,TiCCQ0@=K`65U`PkP`P`Q0CP`20N|9CCPkP`P`A>`b9RbQ0DPkP`A>`9xPkAb`ixR|C{EWFQPcPeb5b6b7X0BX2BX9BX:BX1gX<gX=gX>g11F59yGCAERGHA@LGW10FG1FGF[[[[^0B^2B^9B^:B^1g^<g^=g^>gP<fV,:LRZ/0:fIR~/=LRp#4%xp%ApPpPZfWRZ#I#9P;P0PXPjP=O<b4bDbAb3Co:0|A@Q0GP<Erb8Q05P3Q0;PzPE20PEz%6KR@,F?PEP?Q0WPzP@PyQ09PKPK%LKDhJ0OQ03P}%]{%A{%6{RKP{%GK,V{CHA?LLA#6PB%]1%A1%61R{P1%G{,V1CH%6SPBAfBwoRo,ZvRvA^Qon,ZmAfBwqQ0:';9^mQ20<v]'D3qP41dBF?<H^?<0u?<;^P_P`P`Q0@P`1TiTCCQ0C=K`65U`PkP`Q0DQ0B5K`Q0A=>`aQ0E5K`5U`PkP`P`1J`YAb`29PkP`Q01PkP`1J`N9K`bPkP|FQEWFQPcPeb5b6b7X0BX2BX9BX:BXKBX1gX<gX=gX>gXCgXJg11D59yFCPVQ0RQ0QPWH0{AEYDG15LR,8DA@LD>1FFD[[[[[^0B^2B^9B^:B^KB^1g^<g^=g^>g^Cg^JgP<1:LZRZ/0:%4tQ0F15LZ#A%xj%AjPtPjPZPHP;P0PGPYPNQ0MO@b4bHbEbDbAb3CoI0zEgPB20y8lRNQ08,1OX`BRGPBPlPGQ03P}1Dr]RrP4Q04P_P`P`PhP`20MixCCR]PkP`P`Q0SP`Q06-0MxCCRxPkQ079K`hFQPcPeb5b6b7X0BX2BX1gAXO<;RO100URG,1HRZQ0H/1G[[^0B^2B^1gP<10MAPAQ0VPHPdO5Rdb4b31Pl7Q03P}PrP4Q04P_P`P]PkP`PxPkP`PhP`1lB7-0NiCCFQPcPeb5b6b7X0BX2BX1gQ0H?E07\Z\O^0B^2B^1gPdb4b3:0xl7Eg%4N?XNUeQ0T20w8lEgC~H0vWZWTP;P<O2n2001000000121000000b8bRbPPYP<ErW8PYP<ErW8P<O1b8P<O1b8WBWIP<O1Q0K$0uQ0IQ0J53\P\Q0IQ00PPPgP<Q0Ng01E3n10110300021000000XF\g01EOQ0LP<ErQ0NA?LLS#2%R~5O3%2Y5S3=3J[10fW9@Xf'1X;3,m300t<b8WBWIP<O1n10210010400021110110102P0O1b;b^WBWSXLBXMBX?BN:0sbUWWWVP;P<O2n2001000000121000000W8WXP;P<O2n2001000000121000000b8WQWYX_BW[XOBW\o"). Qed.

Definition w4s1_dctx (RNG : footprint) (mm : amem) (P DT4 DBL DBH DST dcap tl : Z) : Prop :=
  unpoisoned mm DBL DBH /\ DBL <= DT4 /\ DT4 + 2 * 2^tl <= DBH /\ unpoisoned mm DST (DST + dcap) /\
  rng RNG DT4 (2 * 2^tl) /\ rng RNG DST dcap /\ rng RNG P 480 /\ rng_aimg RNG /\
  rng RNG (shad DBL) (shlen (DBH - DBL + 7)) /\ rng RNG (shad DST) (shlen (dcap + 7)) /\
  DBL mod 8 = 0 /\ DST mod 8 = 0 /\
  0x60d000 <= DT4 /\ DT4 + 8192 <= 2^47 /\ 0x60d000 <= DST /\ DST + dcap <= 2^47 /\
  0x10007fff8000 <= P /\ P + 480 <= 2^47 /\ 0x60d000 <= DBL /\ DBH <= 2^47 /\
  KXGoM.apart DST dcap 0x7fff8000 17592186044416 /\ KXGoM.apart DST dcap DT4 (2 * 2^tl) /\ KXGoM.apart DST dcap P 480 /\
  KXGoM.apart DT4 (2 * 2^tl) P 480.

Ltac w4s1_dctx_intro C :=
  destruct C as (UT & UT1 & UT2 & UD & WT & WD & WF & WI & WTS & WDS & A8a & A8b & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 &
                 AB & AT & AF & ATF).

Section CANSEC1. Context {rc : runConstT}.

Definition w4s1_decA_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 w0 : word) (pad1 pad2 pad3 pad4 tb : list byte) (obuf : list Z)
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
  0 <= b1 <= 64 -> 0 <= b2 <= 64 -> 0 <= b3 <= 64 -> 0 <= b4 <= 64 ->
  0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
  4096 <= S1 + o1 <= 2^47 -> 4096 <= S2 + o2 <= 2^47 -> 4096 <= S3 + o3 <= 2^47 -> 4096 <= S4 + o4 <= 2^47 ->
  4096 <= DT <= 2^47 -> 2^20 <= SP <= 2^47 ->
  (forall (mm' : amem) (obuf' : list Z) (N1 N2 N3 N4 N5 N6 N7 N8 : Z) (y6 y7 y9 y22 : word),
     munch [(DST, DST + dcap); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 (b1 + (N1 + N5))); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 (b2 + (N2 + N6))); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 (b3 + (N3 + N7))); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 (b4 + (N4 + N8))); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     0 <= N1 <= 12 -> 0 <= N2 <= 12 -> 0 <= N3 <= 12 -> 0 <= N4 <= 12 ->
     0 <= N5 <= 12 -> 0 <= N6 <= 12 -> 0 <= N7 <= 12 -> 0 <= N8 <= 12 ->
     evtF bsegs RNG Q
       (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (j + DST + 1)) y6 y7
                (Z_to_bv 64 (b1 + (N1 + N5))) y9 (Z_to_bv 64 (-20)) (Z_to_bv 64 (j + (DST + 3 * e1))) (Z_to_bv 64 (j + (DST + 2 * e1)))
                (Z_to_bv 64 (j + (DST + e1))) (Z_to_bv 64 (j + DST)) (Z_to_bv 64 (j + (DST + 3 * e1) + 1))
                (Z_to_bv 64 (j + (DST + 2 * e1) + 1)) (Z_to_bv 64 (j + (DST + e1) + 1)) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3))
                (Z_to_bv 64 j) (Z_to_bv 64 (b3 + (N3 + N7))) y22 (Z_to_bv 64 (b4 + (N4 + N8))) (Z_to_bv 64 0x7fff8000)
                (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 c4) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl))
                (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (b2 + (N2 + N6))))
           F (Z_to_bv 64 0x8a1d8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 b2) (Z_to_bv 64 b3) (Z_to_bv 64 b4) x8 x9
               (Z_to_bv 64 (-20)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 b1) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3))
               (Z_to_bv 64 j) (Z_to_bv 64 DST) x22 x23 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 c4) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1 * DT + -5)) x31)
          F (Z_to_bv 64 0x89de4) fc None mm (seg_rom bsegs)).

Ltac kxr_ev := lazymatch goal with
  | |- _ <= bv_unsigned (ev ?E ?j) <= _ => let H := fresh "HR" in kx_range (EVar j) H; exact H
  end.

Lemma w4_srl_lt62 : forall E x s, 2 <= bv_unsigned (edenot E s) mod 64 ->
  0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 2^62.
Proof.
  intros E x s H. cbn [edenot].
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E s)) 64 ltac:(lia)) as Hk.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E x)) (2^64) ltac:(lia)) as Ha.
  rewrite <- (Z_to_bv_bv_unsigned (edenot E x)), <- (Z_to_bv_bv_unsigned (edenot E s)), srl_lit_ez, Z_to_bv_unsigned.
  revert H Hk Ha. generalize (bv_unsigned (edenot E s) mod 64) as k. generalize (bv_unsigned (edenot E x) mod 2^64) as a.
  intros a k H Hk Ha.
  assert (H2 : 2^2 <= 2^k) by (apply Z.pow_le_mono_r; lia).
  assert (Hq : 0 <= a / 2^k < 2^62).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    assert (2^2 * 2^62 <= 2^k * 2^62) by (apply Z.mul_le_mono_nonneg_r; lia). change (2^64) with (2^2 * 2^62) in Ha. lia. }
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by lia. lia.
Qed.
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
Theorem w4s1_decA : w4s1_decA_case.
Proof.
  unfold w4s1_decA_case.
  intros Q RNG mm F fc gp tp x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 w0 pad1 pad2 pad3 pad4 tb obuf
    SP DST dcap e1 j DT tl rsv DBL DBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4
    C MI TB TBB TBL TBP OUT LO FR B1 B2 B3 B4 HTL HRS HJ HE HROOM HDC HB1 HB2 HB3 HB4 HC1 HC2 HC3 HC4 HP1 HP2 HP3 HP4 HDT HSP K.
  w4s1_dctx_intro C.
  kx_runFmd [0x8a1d8; 0x8ac7c; 0x8c660] 300%nat (repeat true 64)
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
       KZRange b1 0 64; KZRange b2 0 64; KZRange b3 0 64; KZRange b4 0 64;
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

End CANSEC1.
