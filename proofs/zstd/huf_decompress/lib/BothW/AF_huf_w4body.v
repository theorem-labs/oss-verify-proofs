(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_HufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit2 HufWalkKit3.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_w4body () := "C5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common5KXTac;tab_img_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXTac=ztab_fact_imgK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4body:w4_ctz_tabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission6Common6KXCell;kx_rwc_consK47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk05K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk09K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk06K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common4KXGo6all_roC5ARocqVerifyHarness?AgentSubmission6Common4KXGo9zk_img_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zk_word_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:apart_sub'C5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subC47Corelib4Init5Logic5proj2K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC5ARocqVerifyHarness?AgentSubmission6Common4KXGo5zt_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7all_romC5ARocqVerifyHarness?AgentSubmission6Common4KXGo9zr_ok_imgC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry04K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartI47Corelib4Init5Logic2or00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula02C56Stdlib5Arith8PeanoNat3Nat3ltbC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:kx_stk_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wr_at_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost9estart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<log_apart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_apart_ez_okC5ARocqVerifyHarness?AgentSubmission6Common6KXCell>kx_cell_store8C5ARocqVerifyHarness?AgentSubmission6Common6KXPost5ez_okC47Corelib4Init5Logic6eq_indC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission6Common5KXMem6replayC5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_u8arr_replayC5ARocqVerifyHarness?AgentSubmission6Common5KXMem=replay_lengthK47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4body;w4_nb_boundC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission6Common6KXPost9kx_mul_m1C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okC47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K46Stdlib9micromega=RingMicromega3Op201I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop05I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I47Corelib4Init5Logic5False00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC4ELinuxProcessSemantics5Riscv3Sem2w0I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI46Stdlib5Lists4List6Exists00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00C46Stdlib9micromega8ZifyInst7Inj_Z_Zc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4body<w4_body_stmt".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Notation amem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

Definition w4_body_stmt : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (gp tp : word) (b0 b1 b2 b3 : word) (j1 j5 j7 j8 j9 j10 j11 j12 j13 j15 j16 j17 j19 j20 j25 j30 : word)
         (SP DT4 DBL DBH SBL SBH DST dcap SS n IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 DL OLIM : Z) (obuf tbl sbuf : list byte),
    mem_inv bsegs mm ->
    bytes_at bsegs mm DT4 tbl -> zlen tbl = 4096 ->
    u8arr bsegs mm DST obuf -> zlen obuf = dcap ->
    bytes_at bsegs mm SS sbuf -> zlen sbuf = n ->
    rw_cells bsegs mm (SP + 88) [C8 (Z_to_bv 64 OLIM); C8 (Z_to_bv 64 (OP3 - DL)); C8 (Z_to_bv 64 0xff34); C8 (Z_to_bv 64 (OP2 - DL))] ->
    rw_cells bsegs mm (SP + 120) [C8 (Z_to_bv 64 (OP1 - DL)); C8 (Z_to_bv 64 (OP0 - DL)); C8 (Z_to_bv 64 2147450880)] ->
    rw_cells bsegs mm (SP + 224) [C8 (Z_to_bv 64 0x20dc4); C8 (Z_to_bv 64 DL)] ->
    stk bsegs mm (SP + 144) (SP + 224) -> wr_at bsegs mm (SP + 144) 96 ->
    
    unpoisoned mm DBL DBH -> DBL <= DT4 -> DT4 + 4096 <= DBH ->
    unpoisoned mm DST (DST + dcap) -> unpoisoned mm SBL SBH -> SBL <= SS -> SS + n <= SBH ->
    rng RNG DT4 4096 -> rng RNG DST dcap -> rng RNG SS n -> rng RNG (SP + 88) 152 -> rng_aimg RNG ->
    rng RNG (shad DBL) (shlen (DBH - DBL + 7)) -> rng RNG (shad DST) (shlen (dcap + 7)) -> rng RNG (shad SBL) (shlen (SBH - SBL + 7)) ->
    DBL mod 8 = 0 -> DST mod 8 = 0 -> SBL mod 8 = 0 ->
    
    0x60d000 <= DT4 -> DT4 + 4096 <= 2^47 -> 0x60d000 <= DST -> DST + dcap <= 2^47 -> 0x60d000 <= SS -> SS + n <= 2^47 ->
    0x10007fff8000 <= SP -> SP + 496 <= 2^47 -> 0x60d000 <= DBL -> DBH <= 2^47 -> 0x60d000 <= SBL -> SBH <= 2^47 ->
    KXGoM.apart DST dcap 0x7fff8000 17592186044416 ->
    KXGoM.apart DST dcap DT4 4096 -> KXGoM.apart DST dcap SS n -> KXGoM.apart DST dcap (SP + 88) 152 ->
    KXGoM.apart SS n (SP + 88) 152 -> KXGoM.apart DT4 4096 (SP + 88) 152 ->
    
    SS + 7 <= IP0 -> IP0 + 8 <= SS + n -> SS + 7 <= IP1 -> IP1 + 8 <= SS + n ->
    SS + 7 <= IP2 -> IP2 + 8 <= SS + n -> SS + 7 <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 -> OP0 + 5 <= DST + dcap -> DST <= OP1 -> OP1 + 5 <= DST + dcap ->
    DST <= OP2 -> OP2 + 5 <= DST + dcap -> DST <= OP3 -> OP3 + 5 <= DST + dcap ->
    0 <= DL <= 2^40 -> DL <= OP0 -> DL <= OP1 -> DL <= OP2 -> DL <= OP3 -> 0 <= OLIM < 2^47 ->
    (forall (mm' : amem) (b0' b1' b2' b3' : word) (nb0 nb1 nb2 nb3 : Z)
            (k1 k5 k7 k8 k9 k12 k13 k15 k16 k17 k19 k20 k25 k30 : word),
       munch [(DST, DST + dcap); (SP + 144, SP + 224); (SP + 232, SP + 240)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
       stk bsegs mm' (SP + 144) (SP + 224) ->
       rw_cells bsegs mm' (SP + 224) [C8 (Z_to_bv 64 0x20dc4); C8 (Z_to_bv 64 (DL + 5))] ->
       (exists obuf', u8arr bsegs mm' DST obuf' /\ length obuf' = length obuf) ->
       0 <= nb0 <= 7 -> 0 <= nb1 <= 7 -> 0 <= nb2 <= 7 -> 0 <= nb3 <= 7 ->
       evtF bsegs RNG Q (MS (mkR k1 (Z_to_bv 64 SP) gp tp k5 b0' k7 k8 k9 (Z_to_bv 64 OLIM) (Z_to_bv 64 (OP3 + 5)) k12 k13
                                (Z_to_bv 64 2147450880) k15 k16 k17 (Z_to_bv 64 DT4) k19 k20 b2' (Z_to_bv 64 (IP0 - nb0)) b3'
                                (Z_to_bv 64 (IP1 - nb1)) k25 (Z_to_bv 64 (OP3 - DL)) (Z_to_bv 64 (IP3 - nb3))
                                (Z_to_bv 64 0x20dc4) b1' k30 (Z_to_bv 64 (IP2 - nb2)))
                           F (Z_to_bv 64 0x8f7ac) fc None mm' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR j1 (Z_to_bv 64 SP) gp tp j5 b0 j7 j8 j9 j10 j11 j12 j13 (Z_to_bv 64 2147450880) j15 j16 j17
                             (Z_to_bv 64 DT4) j19 j20 b2 (Z_to_bv 64 IP0) b3 (Z_to_bv 64 IP1) j25 (Z_to_bv 64 (OP3 - DL))
                             (Z_to_bv 64 IP3) (Z_to_bv 64 0x20dc4) b1 j30 (Z_to_bv 64 IP2))
                        F (Z_to_bv 64 0x8ef70) fc None mm (seg_rom bsegs)).


Lemma w4_ctz_tab : forall mm, mem_inv bsegs mm -> ztab_fact bsegs mm 0x20d93 64 1 [(0, 0, 63)].
Proof.
  intros mm MI. apply ztab_fact_img; [exact MI | lia | vm_compute; reflexivity].
Qed.

Lemma w4_nb_bound : forall u, 0 <= u <= 63 -> 0 <= u / 8 <= 7.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4body ()) [] "h04__x1h17__arithh24__ffh34__p1h48__varmaph55__with61Hh72Huh81up;2p;1p;6p;3p;4p;5p;7p;8g00Adj20Tg007Uj13Tg008:j17Tg00KDj26Tg004Yj18Tg00K_j2:Tg009Xj1RTg00:Xj1HTg00L<j2CTg00;Vj1BTg00<4j1ATg00<_j24Tg00LZj2>Tg00M=j6TTg00Maj1STg00>Qj2QTg00?3j2NTg00?Mj2MTg00@9j3GTg00@Sj3FTg00A2j4DTg00;8j1ETg00NCj22Tg00N_j4ITg00O@j3JTg00Ocj2KTg00P@j5@Tg00Plj4LTg00=Bj4<Tg00=mj7?Tg00QGj7OTg00Qkj8PTg00F6R0f1R1g00I=f0R2C<p=;P1g00G^R3g00H=R4P4g00H]R5P2g00IdF?p=1f2R6P3P4P4P5P1P2FOp==f3R7P3P4P4P5P6P1P2GPp=5P0P1g00ROP2C<p=9g00FTR8/02R9g00D\R:#3#3R;#3#3#3#7R<,02R='6%8:#8#8#7R>,:1R?,08%7;R;,0?P1P>p-0R@g00G2RA#RRB%HARA1C01RC%B0RD%A0RE1408RF1>0:R:';,1ERGPEP3P4P4P5P7ETR75=E%S4R4PGC51QE5R5P2P6g00JDRGg00JdR3'N1M26=GG3dAF081CDR3b2b4b5X00W316911081[^00^3@P2106<P6P1O3b1PBPA%E0PD140>R9,9F,1EP5P3b2b4b5128>P2b1RFCIP1P>P>PFPBPAPCPDPE140<,;:,1E9=E7P4AJ099,9:,1EC5P5P3b2b4b5X00X3@161=1K>>,21[^00^3@P21086P6P1O3b1D@12?>1:6>/2>PBPAPCPDPE19:9,1EP4140;,;:,1EC5P5P3b2b4b5X00122>101;[^00P2f4/:>P1O2b1UP2O1b6CLW7X80o"). Qed.


Ltac w4_bounds :=
  lazymatch goal with
  | |- 0 <= bv_unsigned (ev ?E ?j) mod 2 ^ 64 / 2 ^ (3 mod 64) <= 7 =>
      let H := fresh "H" in let HR := fresh "HR" in
      kx_range (EVar j) H;
      pose proof (bv_unsigned_in_range 64 (ev E j)) as HR; unfold bv_modulus in HR; change (2 ^ Z.of_N 64) with (2^64) in HR;
      rewrite (Z.mod_small _ _ HR);
      change (2 ^ (3 mod 64)) with 8;
      exact (w4_nb_bound _ H)
  end.


From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4m AF_huf_w4m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3b Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require I_asan_memcpy.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AFrameD.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Import KXS.

Module W4FSC.
Import KXS.

Lemma w4f_shd_ap : forall E X B O k w H,
  bv_unsigned (edenot E X) < H -> 0 <= O -> O + H / 8 + 1 <= 2^64 -> 0 < w < 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + w <= 2^64 ->
  bv_unsigned (edenot E B) + k + w <= O \/ O + H / 8 + 1 <= bv_unsigned (edenot E B) + k ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit w)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k w H HX HO1 HO2 HW HB1 HB2 HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (2 ^ (3 mod 64)) with 8.
  rewrite (Z_to_bv_unsigned 64 w). unfold bv_wrap, bv_modulus. rewrite (Z.mod_small w) by lia.
  assert (HD : bv_unsigned (edenot E X) / 8 <= H / 8) by (apply Z.div_le_mono; lia).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.

Ltac w4f_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac w4fxb :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E ?X) < _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite (ez_ok zv E (kE_atoms zv xs) X);
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [?c mod 64] => w4f_zlit c; let v := eval vm_compute in (c mod 64) in change (c mod 64) with v
        end;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
        first [lia | Z.div_mod_to_equations; lia]
      end
  end.

Lemma w4f_shd_ap2 : forall E X B O k w H,
  bv_unsigned (edenot E X) < H ->
  0 <= O /\ O + H / 8 + 1 <= 2^64 /\ 0 < w < 2^64 ->
  0 <= bv_unsigned (edenot E B) + k /\ bv_unsigned (edenot E B) + k + w <= 2^64 /\
  (bv_unsigned (edenot E B) + k + w <= O \/ O + H / 8 + 1 <= bv_unsigned (edenot E B) + k) ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit w)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k w H HX (HO1 & HO2 & HW) (HB1 & HB2 & HAP).
  apply (w4f_shd_ap E X B O k w H); assumption.
Qed.

Ltac w4f_aplia :=
  first [ match goal with H : KXGoM.apart ?a _ _ _ |- context [?a] =>
            let H' := fresh "AP" in pose proof H as H'; unfold KXGoM.apart in H'; lia end
        | match goal with H : KXGoM.apart _ _ _ _ |- _ =>
            let H' := fresh "AP" in pose proof H as H'; unfold KXGoM.apart in H'; lia end ].

Ltac w4fshd H :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ _ =>
      apply (w4f_shd_ap2 E X B O k w H);
      [ w4fxb
      | lia
      | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
        split; [lia | split; [lia | w4f_aplia]] ]
  end.
Lemma w4f_rd_nb : forall m A z,
  ztab_fact bsegs m A 4096 2 [(0, 0, 11)] -> A <= z < A + 4096 -> (z - A) mod 2 = 0 ->
  bv_unsigned (rdval bsegs m (Z_to_bv 64 z) 2 false) mod 64 <= 11.
Proof.
  intros m A z ZT HZ HM.
  assert (FF : find_field ((z - A) mod 2) [(0, 0, 11)] = Some (0, 11)) by (rewrite HM; reflexivity).
  destruct (ZT z HZ 0 11 FF) as (b & RB & HB).
  unfold rdval. cbn [rdn] in RB |- *.
  revert RB.
  lazymatch goal with |- (match ?x with Some _ => _ | None => _ end) = _ -> _ => destruct x as [b0|] eqn:L0 end;
    [| discriminate].
  intros RB. injection RB as Eb. subst b0.
  cbn beta iota.
  match goal with |- context [m ?X] =>
    destruct (m X) as [b1|] eqn:L1; [| destruct (seg_rom bsegs X) as [b1|] eqn:L2] end;
  cbn beta iota; unfold extz;
  rewrite ?bytes_le_to_Z_le_val; cbn [map le_val];
  rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
  try (pose proof (bv_unsigned_in_range _ b1) as R1; unfold bv_modulus in R1; change (Z.of_N 8) with 8 in R1);
  Z.div_mod_to_equations; lia.
Qed.

Lemma w4f_mod_div : forall a n m, 0 < n -> (n | m) -> 0 < m -> (a mod m) mod n = a mod n.
Proof.
  intros a n m Hn [c Hc] Hm. subst m.
  rewrite (Z.div_mod a (c * n)) at 2 by lia.
  rewrite Z.add_comm. replace (c * n * (a / (c * n))) with ((c * (a / (c * n))) * n) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma w4f_lb_shift : forall p s k x, 0 <= p -> 0 <= k <= s -> p + s <= 63 ->
  x mod 2^(p+1) <> 0 -> ((x * 2^k) mod 2^64) mod 2^(p + s + 1) <> 0.
Proof.
  intros p s k x Hp Hk Hps Hl.
  assert (P1 : 0 < 2^(p+s+1)) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  assert (P3 : 0 < 2^(p+s+1-k)) by (apply Z.pow_pos_nonneg; lia).
  assert (P4 : 0 < 2^(p+1)) by (apply Z.pow_pos_nonneg; lia).
  assert (D1 : (2^(p+s+1) | 2^64)).
  { exists (2^(63 - p - s)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (D2 : (2^(p+1) | 2^(p+s+1-k))).
  { exists (2^(s - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite (w4f_mod_div (x * 2^k) (2^(p+s+1)) (2^64) P1 D1 ltac:(lia)).
  replace (2^(p+s+1)) with (2^(p+s+1-k) * 2^k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r by lia.
  intro HZ. apply Z.mul_eq_0 in HZ. destruct HZ as [HZ|HZ]; [|lia].
  apply Hl. rewrite <- (w4f_mod_div x (2^(p+1)) (2^(p+s+1-k)) P4 D2 P3), HZ. reflexivity.
Qed.

Lemma w4f_sll_lb : forall (B : Z) (e : word) p, 0 <= p -> p + 11 <= 63 -> 0 <= B < 2^64 ->
  B mod 2^(p+1) <> 0 -> bv_unsigned e mod 64 <= 11 ->
  0 <= bv_unsigned (alu64 ALU_SLL (Z_to_bv 64 B) e) < 2^64 /\
  bv_unsigned (alu64 ALU_SLL (Z_to_bv 64 B) e) mod 2^(p + 11 + 1) <> 0.
Proof.
  intros B e p Hp Hp2 HB HL HE.
  rewrite u_sll64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite (Z.mod_small B) by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned e) 64 ltac:(lia)) as HK.
  split; [apply Z.mod_pos_bound; lia |].
  apply (w4f_lb_shift p 11 (bv_unsigned e mod 64) B); [lia | lia | lia | exact HL].
Qed.

Lemma w4f_rd_nb2 : forall m A (x : word) k,
  ztab_fact bsegs m A 4096 2 [(0, 0, 11)] -> A <= bv_unsigned x + k < A + 4096 -> (bv_unsigned x + k - A) mod 2 = 0 ->
  bv_unsigned (rdval bsegs m (v_addi x k) 2 false) mod 64 <= 11.
Proof.
  intros m A x k ZT H1 H2. unfold v_addi. exact (w4f_rd_nb m A (bv_unsigned x + k) ZT H1 H2).
Qed.

Ltac w4f_nb_read ZT TA :=
  lazymatch goal with
  | |- bv_unsigned (rdval _ ?m (adenot ?E ?a) 2 false) mod 64 <= 11 =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        cbv [adenot a_base a_off];
        apply (w4f_rd_nb2 m TA); [exact ZT | |];
        rewrite (ez_ok zv E (kE_atoms zv xs)); rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (Z.of_N 64) with 64;
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [?c mod 64] => w4f_zlit c; let v := eval vm_compute in (c mod 64) in change (c mod 64) with v
        end;
        Z.div_mod_to_equations; lia
      end
  end.

Ltac w4f_bits A p ZT TA HB LBb e :=
  lazymatch goal with
  | H : rw_cells _ _ A [C8 (edenot ?E (EAlu ALU_SLL (EVar ?j) (EVar ?r)))] |- _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let HR := fresh "HR" in kx_read_eq r HR;
        let NB := fresh "NB" in
        assert (NB : bv_unsigned (ev E r) mod 64 <= 11) by (rewrite HR; w4f_nb_read ZT TA);
        clear HR;
        cbn [edenot] in H;
        set (e := ev E r) in *;
        change E with (kE zv xs) in H;
        rewrite (kE_atoms zv xs j ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)) in H;
        cbn [nth] in H;
        lazymatch type of H with
        | rw_cells _ _ _ [C8 (alu64 ALU_SLL (Z_to_bv 64 ?B) e)] =>
            let BR := fresh "BR" in let BL := fresh "BL" in
            pose proof (w4f_sll_lb B e p ltac:(lia) ltac:(lia) HB LBb NB) as [BR BL]
        end
      end
  end.

Lemma w4f_srl58 : forall E X, 0 <= bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58))) < 64.
Proof.
  intros E X. pose proof (bv_unsigned_in_range _ (edenot E X)) as [R0 R1]. unfold bv_modulus in R1.
  change (Z.of_N 64) with 64 in R1.
  cbn [edenot]. rewrite u_srl64. change (bv_unsigned (Z_to_bv 64 58) mod 64) with 58.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | change (2^58 * 64) with (2^64); lia]].
Qed.

Lemma w4f_ctz_rd : forall m E X off,
  ztab_fact bsegs m off 64 1 [(0, 0, 63)] -> 0 <= off -> off + 64 <= 2^64 ->
  exists bs, rdn bsegs m (adenot E (SA (EAlu ALU_SRL X (ELit 58)) off)) 1 = Some bs.
Proof.
  intros m E X off ZT H0 H1. pose proof (w4f_srl58 E X) as HV.
  cbv [adenot a_base a_off]. unfold v_addi.
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  assert (FF : find_field ((u + off - off) mod 1) [(0, 0, 63)] = Some (0, 63)) by (rewrite Z.mod_1_r; reflexivity).
  destruct (ZT (u + off) ltac:(lia) 0 63 FF) as (b & RB & _). exists [b]. exact RB.
Qed.

Lemma w4f_ctz_acc : forall RNG E X off, rng RNG off 64 -> accP RNG E (SA (EAlu ALU_SRL X (ELit 58)) off, 1%nat).
Proof.
  intros RNG E X off (R0 & R1 & R2). pose proof (w4f_srl58 E X) as HV.
  unfold accP. cbn [fst snd].
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  change (RNG (bv_unsigned (Z_to_bv 64 (u + off))) 1%nat).
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite Z.mod_small by lia. apply R2; cbn; lia.
Qed.

Lemma w4f_ctz_ap : forall E X B O k w,
  0 <= O -> O + 64 <= 2^64 -> 0 < w < 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + w <= 2^64 ->
  bv_unsigned (edenot E B) + k + w <= O \/ O + 64 <= bv_unsigned (edenot E B) + k ->
  (flat E (SA (EAlu ALU_SRL X (ELit 58)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit w)) /\
   (estart E (SA (EAlu ALU_SRL X (ELit 58)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
    estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 58)) O))) /\
  (flat E (SA B k) (elenZ E (ELit w)) /\ flat E (SA (EAlu ALU_SRL X (ELit 58)) O) (elenZ E (ELit 1)) /\
   (estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 58)) O) \/
    estart E (SA (EAlu ALU_SRL X (ELit 58)) O) + elenZ E (ELit 1) <= estart E (SA B k))).
Proof.
  intros E X B O k w HO1 HO2 HW HB1 HB2 HAP. pose proof (w4f_srl58 E X) as HV.
  unfold flat, estart, elenZ. cbn [a_base a_off].
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  change (edenot E (ELit 1)) with (Z_to_bv 64 1). change (edenot E (ELit w)) with (Z_to_bv 64 w).
  change (bv_unsigned (Z_to_bv 64 1)) with 1.
  rewrite (Z_to_bv_unsigned 64 w). unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64. rewrite (Z.mod_small w) by lia.
  repeat split; lia.
Qed.

Ltac w4f_rngs :=
  repeat match goal with
  | |- context [EVar ?j] =>
      lazymatch goal with
      | _ : _ <= bv_unsigned (ev _ j) <= _ |- _ => fail
      | _ => let H := fresh "HR" in kx_range (EVar j) H
      end
  end.

Ltac w4fctz :=
  lazymatch goal with
  | |- exists bs, rdn _ ?m (adenot ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O)) 1 = Some bs =>
      eapply (w4f_ctz_rd m E X O); [eassumption | lia | lia]
  | |- accP ?R ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O, 1%nat) => apply (w4f_ctz_acc R E X O); assumption
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ _ =>
      apply (proj1 (w4f_ctz_ap E X B O k w ltac:(lia) ltac:(lia) ltac:(lia) ltac:(w4uz) ltac:(w4uz) ltac:(w4uz)))
  | |- flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ flat ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O) _ /\ _ =>
      apply (proj2 (w4f_ctz_ap E X B O k w ltac:(lia) ltac:(lia) ltac:(lia) ltac:(w4uz) ltac:(w4uz) ltac:(w4uz)))
  end.

Lemma w4f_br_nz : forall E P B,
  bv_unsigned (edenot E B) <= 64 -> 64 < bv_unsigned (edenot E P) ->
  branch_taken BC_NE
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P (EAlu ALU_SRL B (ELit 3))) (ELit 1))))
    (edenot E (ELit 0)) = true.
Proof.
  intros E P B HB HP.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64, u_srl64.
  change (bv_unsigned (Z_to_bv 64 3) mod 64) with 3. change (2 ^ 3) with 8.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
    { apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8) <> 0).
    { assert (HB8 : bv_unsigned (edenot E B) / 8 <= 8) by (apply Z.div_le_upper_bound; lia).
      intros H0. pose proof (Z.lxor_eq _ _ H0). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)) 1); [lia|].
  reflexivity.
Qed.

Lemma w4f_lit_acc : forall RNG E off (n : nat) lo len, (1 <= n)%nat -> rng RNG lo len -> lo <= off -> off + Z.of_nat n <= lo + len ->
  accP RNG E (SA (ELit 0) off, n).
Proof.
  intros RNG E off n lo len HN (R0 & R1 & R2) H1 H2.
  unfold accP. cbn [fst snd].
  change (RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + off))) n).
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite Z.mod_small by lia. apply R2; lia.
Qed.

Ltac w4fbr :=
  lazymatch goal with
  | |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR ?P (EAlu ALU_SRL ?B (ELit 3))) (ELit 1))))
         (edenot ?E (ELit 0)) = true => w4f_rngs; apply (w4f_br_nz E P B); w4uz
  end.

Ltac w4facc WIM :=
  lazymatch goal with
  | |- accP ?R ?E (SA (ELit 0) ?O, ?n) => eapply (w4f_lit_acc R E O n); [lia | exact WIM | lia | cbn; lia]
  end.

Lemma w4f_mod2_64 : forall x, (x mod 2^64) mod 2 = x mod 2.
Proof. intros x. apply (w4f_mod_div x 2 (2^64)); [lia | exists (2^63); reflexivity | lia]. Qed.

Lemma w4f_ev_add : forall E a b, bv_unsigned (edenot E a) mod 2 = 0 -> bv_unsigned (edenot E b) mod 2 = 0 ->
  bv_unsigned (edenot E (EAlu ALU_ADD a b)) mod 2 = 0.
Proof. intros E a b Ha Hb. cbn [edenot]. rewrite u_add64, w4f_mod2_64, Z.add_mod by lia. rewrite Ha, Hb. reflexivity. Qed.

Lemma w4f_ev_mul : forall E c b, c mod 2 = 0 -> bv_unsigned (edenot E (EMd M_MUL (ELit c) b)) mod 2 = 0.
Proof.
  intros E c b Hc. cbn [edenot]. rewrite u_mul64, w4f_mod2_64, Z.mul_mod by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64. rewrite w4f_mod2_64, Hc. reflexivity.
Qed.

Lemma w4f_ev_and : forall E b m, m mod 2 = 0 -> bv_unsigned (edenot E (EAlu ALU_AND b (ELit m))) mod 2 = 0.
Proof.
  intros E b m Hm. cbn [edenot]. rewrite u_and64, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  set (x := bv_unsigned (edenot E b)). set (y := m mod 2^64).
  assert (Hy : Z.land y (Z.ones 1) = 0) by (rewrite Z.land_ones by lia; change (2^1) with 2; unfold y; rewrite w4f_mod2_64; exact Hm).
  assert (H : Z.land x y mod 2 = Z.land (Z.land x y) (Z.ones 1)) by (rewrite Z.land_ones by lia; reflexivity).
  rewrite H, <- Z.land_assoc, Hy. apply Z.land_0_r.
Qed.

Ltac w4f_ev :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E (EAlu ALU_ADD ?a ?b)) mod 2 = 0 => apply (w4f_ev_add E a b); w4f_ev
  | |- bv_unsigned (edenot ?E (EMd M_MUL (ELit ?c) ?b)) mod 2 = 0 => apply (w4f_ev_mul E c b); reflexivity
  | |- bv_unsigned (edenot ?E (EAlu ALU_AND ?b (ELit ?m))) mod 2 = 0 => apply (w4f_ev_and E b m); reflexivity
  end.

Lemma w4f_rl_bits : forall E Y V, bv_unsigned (edenot E Y) mod 2 = 0 ->
  0 <= bv_unsigned (edenot E (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EAlu ALU_AND V (ELit 7)))) < 2^64 /\
  bv_unsigned (edenot E (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EAlu ALU_AND V (ELit 7)))) mod 2^8 <> 0.
Proof.
  intros E Y V HY.
  pose proof (bv_unsigned_in_range _ (edenot E Y)) as [Y0 Y1]. unfold bv_modulus in Y1. change (Z.of_N 64) with 64 in Y1.
  pose proof (bv_unsigned_in_range _ (edenot E V)) as [V0 _].
  cbn [edenot]. rewrite u_sll64, u_add64, u_and64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 7)) with 7.
  set (y := bv_unsigned (edenot E Y)) in *. set (v := bv_unsigned (edenot E V)) in *.
  assert (HY2 : y + 1 < 2^64) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (y + 1)) by lia.
  assert (HO : (y + 1) mod 2^(0+1) <> 0) by (change (2^(0+1)) with 2; Z.div_mod_to_equations; lia).
  assert (HL : 0 <= Z.land v 7 <= 7).
  { assert (E7 : Z.land v 7 = v mod 2^3) by (rewrite <- Z.land_ones by lia; reflexivity). rewrite E7.
    pose proof (Z.mod_pos_bound v (2^3) ltac:(lia)). change (2^3) with 8 in *. lia. }
  rewrite (Z.mod_small (Z.land v 7) 64) by lia.
  split; [apply Z.mod_pos_bound; lia |].
  change (2^8) with (2^(0+7+1)).
  apply (w4f_lb_shift 0 7 (Z.land v 7) (y + 1)); [lia | lia | lia | exact HO].
Qed.

Ltac w4f_rlb A c :=
  lazymatch goal with
  | H : rw_cells _ _ A [C8 (edenot ?E (EAlu ALU_SLL (EAlu ALU_ADD ?Y (ELit 1)) (EAlu ALU_AND ?V (ELit 7))))] |- _ =>
      let BR := fresh "BR" in let BL := fresh "BL" in
      pose proof (w4f_rl_bits E Y V ltac:(w4f_ev)) as [BR BL];
      set (c := edenot E (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EAlu ALU_AND V (ELit 7)))) in *; clearbody c
  end.

Lemma w4f_ctz_val : forall m E X off, ztab_fact bsegs m off 64 1 [(0, 0, 63)] -> 0 <= off -> off + 64 <= 2^64 ->
  bv_unsigned (rdval bsegs m (adenot E (SA (EAlu ALU_SRL X (ELit 58)) off)) 1 false) <= 63.
Proof.
  intros m E X off ZT H0 H1. pose proof (w4f_srl58 E X) as HV.
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  change (bv_unsigned (rdval bsegs m (Z_to_bv 64 (u + off)) 1 false) <= 63).
  assert (FF : find_field ((u + off - off) mod 1) [(0, 0, 63)] = Some (0, 63)) by (rewrite Z.mod_1_r; reflexivity).
  destruct (ZT (u + off) ltac:(lia) 0 63 FF) as (b & RB & HB).
  unfold rdval. rewrite RB. unfold extz. cbn beta iota.
  rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (bv_unsigned_in_range _ b) as [B0 B1]. unfold bv_modulus in B1. change (Z.of_N 8) with 8 in B1.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite Z.mod_small by lia. lia.
Qed.

Ltac w4f_rlnb A nb :=
  lazymatch goal with
  | H : rw_cells _ _ A [C8 (Z_to_bv 64 (?S + (?i + -1 * (bv_unsigned ?Z mod ?M / ?D))))] |- _ =>
      lazymatch Z with
      | ?f ?j =>
          let HR := fresh "HR" in kx_read_eq j HR;
          let HV := fresh "HV" in
          lazymatch type of HR with
          | ?L = ?R =>
              assert (HV : 0 <= bv_unsigned L <= 63)
                by (rewrite HR; pose proof (bv_unsigned_in_range _ R) as [? _];
                    split; [lia | eapply w4f_ctz_val; [eassumption | lia | lia]]);
              change (0 <= bv_unsigned Z <= 63) in HV
          end;
          clear HR;
          let NB := fresh "NB" in
          assert (NB : 0 <= bv_unsigned Z mod M / D <= 7)
            by (change D with 8; change M with (2^64); rewrite Z.mod_small by lia;
                assert (bv_unsigned Z / 8 < 8) by (apply Z.div_lt_upper_bound; lia);
                assert (0 <= bv_unsigned Z / 8) by (apply Z.div_pos; lia); lia);
          set (nb := bv_unsigned Z mod M / D) in *; clearbody nb
      end
  end.

Ltac w4f_cell_gen H W off :=
  lazymatch goal with
  | HLF : log_flat ?E ?log |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | rw_cells ?segs m ?A [?c0] =>
          let rec go pre l :=
            lazymatch l with
            | SE ?a W ?v :: ?rest =>
                tryif (lazymatch a with {| a_base := _; a_off := off |} => idtac end) then
                  first [ let Hn := fresh "HC" in
                          assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a W v :: rest)) A
                                         [ltac:(lazymatch W with 8%nat => exact (C8 (edenot E v)) | _ => exact (C4 (edenot E v)) end)])
                            by (first [ eapply (kx_cell_store8 segs E m pre a v rest A)
                                      | eapply (kx_cell_store4 segs E m pre a v rest A) ];
                                [ change (pre ++ SE a W v :: rest) with log; exact HLF
                                | exact H
                                | change E with (kE zv xs); kx_estart_z zv
                                | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv ]);
                          change (pre ++ SE a W v :: rest) with log in Hn;
                          rewrite (ez_ok zv E (kE_atoms zv xs) v) in Hn;
                          let EQ := fresh "HCe" in let pf := w4_ez_pf zv E v in pose proof pf as EQ; rewrite EQ in Hn; clear EQ;
                          rewrite ?Z_to_bv_bv_unsigned in Hn;
                          clear H; rename Hn into H
                        | let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest ]
                else (let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest)
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => fail "w4f_cell: no store found for" A
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.

Ltac w4f_cells_post :=
  repeat match goal with
  | HLF : log_flat ?E ?log, H : rw_cells ?segs ?m ?A [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      let l := eval hnf in log in
      lazymatch A with
      | _ + ?off => tryif kx_log_has_off l off
                    then first [ w4f_cell_gen H 8%nat off | w4f_cell_gen H 4%nat off | w4_cell H | w4_cell4 H | kx_frame H ]
                    else kx_frame H
      | _ => first [ w4_cell H | w4_cell4 H | kx_frame H ]
      end
  end.

Ltac w4f_frame3 MU :=
  repeat match goal with
  | H : rw_cells ?segs ?m (?P + ?off) [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      lazymatch type of MU with munch ?W m ?m' =>
        first [ constr_eq off 288 | constr_eq off 328 | constr_eq off 368 ];
        let H' := fresh "HF" in
        pose proof (AFrameD.cells_frameD W m m' (P + off) [c] H MU ltac:(cbn [disjoint_from cells_size csize]; lia)) as H';
        clear H; rename H' into H
      end
  end.

End W4FSC.
Import W4FSC.


Section CANSEC1. Context {rc : runConstT}.
Section W4F.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (pdt pb : aptr) (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -480).
  Notation n := (zlen src).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HDB : In (HB pb DST dcap) LB.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis LCB : zlen cbs = 4096.
  Hypothesis MTL : 10 <= mtl <= 12.
  Variable cells : list deltX1.
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells).
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis NSM : 10 <= n < 2^26.
  Hypothesis SBB : SBL <= SS /\ SS + n <= SBH.
  Hypothesis SBA : ablk SBL SBH /\ SBL mod 8 = 0.
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
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Hypothesis w4_blocks : AIMG_HI <= DT /\ DT + DTL <= ATOP /\ DT mod 16 = 0 /\ AIMG_HI <= DST /\ DST + dcap <= ATOP /\ DST mod 16 = 0
                    /\ ablk DST (DST + dcap) /\ AIMG_HI <= SBL /\ SBH <= ATOP.
  Hypothesis w4_unp : forall mm, munch DW m0 mm ->
    unpoisoned mm DT (DT + DTL) /\ unpoisoned mm DST (DST + dcap) /\ unpoisoned mm SBL SBH.
  Hypothesis w4_dtl : 4100 <= DTL.
  Notation W4FX := (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).

  Definition w4_ist (P pc : Z) (x8 x9 x10 x12 x18 x19 x20 x22 x25 : word) (mm : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (P + 296)) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (-24)) (Z_to_bv 64 2) (Z_to_bv 64 3)
            x8 x9 x10 (Z_to_bv 64 (-1 * DT + -5)) x12 (Z_to_bv 64 (P + 256)) (Z_to_bv 64 (P + 336))
            (Z_to_bv 64 (-17)) (Z_to_bv 64 (-16)) (Z_to_bv 64 (-25)) x18 x19 x20 (Z_to_bv 64 AW4_K21) x22
            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) (Z_to_bv 64 (DT + 4))
            (Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 6) (Z_to_bv 64 (-8)))
       FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs).

  Definition w4_lo (o0 o1 o2 o3 : Z) (po4 : word) : list cell :=
    [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3)); C8 po4].
  Definition w4_li (i0 i1 i2 i3 : Z) (pi4 : word) : list cell :=
    [C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3)); C8 pi4].
  Definition w4_lb (b0 b1 b2 b3 : Z) (pb4 : word) : list cell :=
    [C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 b1); C8 (Z_to_bv 64 b2); C8 (Z_to_bv 64 b3); C8 pb4].

  Lemma w4_ablk_ap : forall a b, ablk a b -> a <= b -> KXGoM.apart a (b - a) ASHOFF (ATOP / 8 + 1).
  Proof.
    intros a b H HL. pose proof (@ATOP_lo rc). pose proof (@ATOP_hi rc).
    unfold KXGoM.apart, ablk, AIMG_HI, KLS, ASHOFF in *. lia.
  Qed.

  Lemma w4_stk_ap : forall a, ATOP + 4096 <= a -> KXGoM.apart a 480 ASHOFF (ATOP / 8 + 1).
  Proof.
    intros a H. pose proof (@ATOP_lo rc). pose proof (@ATOP_hi rc).
    unfold KXGoM.apart, ASHOFF in *. lia.
  Qed.

  Lemma w4_tab11 : forall mm, tl = 11 -> bytes_at bsegs mm (DT + 4) cbs -> ztab_fact bsegs mm (DT + 4) 4096 2 [(0, 0, 11)].
  Proof using All.
    intros mm T11 BA z HZ lo' hi' FF.
    pose proof TOK as (TL1 & TL2 & TC). rewrite T11 in TL2, TC, ECB.
    cbn [find_field] in FF. revert FF.
    destruct (Z.eqb_spec 0 ((z - (DT + 4)) mod 2)) as [E0|E0]; intro FF; [injection FF as <- <- | discriminate FF].
    set (v := (z - (DT + 4)) / 2).
    assert (HZv : z = DT + 4 + 2 * v) by (pose proof (Z.div_mod (z - (DT + 4)) 2 ltac:(lia)); unfold v; lia).
    assert (Hv : 0 <= v < 2^11) by (unfold v; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    rewrite ECB in BA. change (x1_bytes cells) with (x1_bytes' cells) in BA.
    unfold FseNCount.Zlength in TL2.
    destruct (x1_cell_rd bsegs mm (DT + 4) cells (Z.to_nat (2 * 2 ^ 11)) v BA ltac:(lia)
                ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)) as [R0 _].
    destruct (TC v Hv) as [NB _].
    rewrite HZv. exists (Z_to_bv 8 (x1_nbBits (nth (Z.to_nat v) cells x1_default))).
    rewrite <- ov_rdn. split; [exact R0 |].
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 8) with 8.
    rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma w4_tr : forall (mm mm' : amem) (fr mid l256 l296 l336 l256' l296' l336' : list cell) (buf' : list Z),
    W4FX mm fr mid l256 l296 l336 ->
    munch [(SPF + 256, SPF + 376); (DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    u8arr bsegs mm' DST (map (Z_to_bv 8) buf') -> zlen buf' = dcap ->
    rw_cells bsegs mm' (SPF + 256) l256' -> cells_size l256' = 40%nat ->
    rw_cells bsegs mm' (SPF + 296) l296' -> cells_size l296' = 40%nat ->
    rw_cells bsegs mm' (SPF + 336) l336' -> cells_size l336' = 40%nat ->
    W4FX mm' fr mid l256' l296' l336'.
  Proof using All.
    intros mm mm' fr mid l256 l296 l336 l256' l296' l336' buf' HW MU' WM' MI' OUT' LOUT2 C256' L256' C296' L296' C336' L336'.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof w4_dtl as HDTL.
    pose proof DJ1 as DJ1u. pose proof DJ2 as DJ2u. unfold KXGoM.apart in DJ1u, DJ2u.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
              (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))).
    - exists buf'. split; assumption.
    - eapply bytes_at_transport; [exact SRCB | exact MU' | cbn [disjoint_from]; rewrite length_map; lia].
    - eapply bytes_at_transport; [exact TB | exact MU' | cbn [disjoint_from]; lia].
    - eapply bytes_at_transport; [exact DTH | exact MU' | cbn [disjoint_from length]; lia].
    - eapply stk_transport_disjoint; [exact STK | exact MU' | exact WM' | cbn [disjoint_from]; lia].
    - eapply rw_cells_transport; [exact FRC | exact MU' | exact WM' | cbn [disjoint_from]; rewrite FRL; lia].
    - exact FRL.
    - eapply rw_cells_transport; [exact MIDC | exact MU' | exact WM' | cbn [disjoint_from]; rewrite MIDL; lia].
    - exact MIDL.
    - exact C256'.
    - exact L256'.
    - exact C296'.
    - exact L296'.
    - exact C336'.
    - exact L336'.
    - eapply rw_cells_transport; [exact FRSC | exact MU' | exact WM' | cbn [disjoint_from cells_size csize]; lia].
    - exact MI'.
    - eapply munch_trans; [exact MU |].
      apply (munch_weaken [(SPF + 256, SPF + 376); (DST, DST + dcap)]); [| exact MU'].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & Hx2 & _). repeat split; lia.
    - eapply wmono_trans; [exact WM | exact WM'].
  Qed.

  Definition w4_fr (w0 w8 w16 : word) : list cell :=
    [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 AW4_M5); C8 (Z_to_bv 64 AW4_M7); C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT);
     C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap));
     C8 (Z_to_bv 64 SS)].

  Lemma w4_d0 : forall (Q : machine_state -> Prop) (mm : amem) (fr mid : list cell) (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 : Z)
      (po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25 : word),
    tl = 11 ->
    W4FX mm fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
    0 <= o0 -> o0 + 5 <= dcap -> 0 <= o1 -> o1 + 5 <= dcap -> 0 <= o2 -> o2 + 5 <= dcap -> 0 <= o3 -> o3 + 5 <= dcap ->
    0 <= B0 < 2^64 -> 0 <= B1 < 2^64 -> 0 <= B2 < 2^64 -> 0 <= B3 < 2^64 ->
    B0 mod 2^9 <> 0 -> B1 mod 2^9 <> 0 -> B2 mod 2^9 <> 0 -> B3 mod 2^9 <> 0 ->
    (forall (mm' : amem) (C0 C1 C2 C3 : Z) (y9 y10 y12 y18 y19 y20 y22 y25 : word),
       W4FX mm' fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb C0 C1 C2 C3 pb4) ->
       0 <= C0 < 2^64 -> 0 <= C1 < 2^64 -> 0 <= C2 < 2^64 -> 0 <= C3 < 2^64 ->
       C0 mod 2^20 <> 0 -> C1 mod 2^20 <> 0 -> C2 mod 2^20 <> 0 -> C3 mod 2^20 <> 0 ->
       evtF bsegs RNG Q (w4_ist SPF 0x88330 x8 y9 y10 y12 y18 y19 y20 y22 y25 mm')) ->
    evtF bsegs RNG Q (w4_ist SPF 0x88170 x8 x9 x10 x12 x18 x19 x20 x22 x25 mm).
  Proof using All.
    intros Q mm fr mid o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25
      T11 HW HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 K.
    pose proof (w4_tab11 mm T11) as ZT0.
    unfold w4_lo, w4_li, w4_lb in HW, K. pose proof HW as HW0.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof (ZT0 TB) as ZT. clear ZT0.
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof w4_dtl as HDTL.
    pose proof (w4_unp mm MU) as (UDT' & UDB' & USB').
    pose proof (@ATOP_lo rc) as HAL. pose proof (@ATOP_hi rc) as HAH.
    pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (_ & (KDT & _) & _).
    assert (UT : unpoisoned mm DT (DT + 4100)) by (eapply unpoisoned_sub; [exact UDT' | lia | lia]).
    assert (RP : rng RNG SPF 480) by (eapply rng_sub; [exact WSK | lia | lia]).
    assert (RT : rng RNG (DT + 4) 4096) by (eapply rng_sub; [exact WDT | lia | lia]).
    assert (RTS : rng RNG (shad DT) (shlen (4100 + 7))).
    { eapply rng_sub; [exact WDTS | lia |].
      assert (shlen (4100 + 7) <= shlen (DTL + 7)) by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; apply Z.div_le_mono; lia).
      lia. }
    assert (AS1 : KXGoM.apart DST dcap ASHOFF (ATOP / 8 + 1)).
    { pose proof (w4_ablk_ap DST (DST + dcap) BK7 ltac:(lia)) as H. replace (DST + dcap - DST) with dcap in H by lia. exact H. }
    assert (AS2 : KXGoM.apart DT 4100 ASHOFF (ATOP / 8 + 1)).
    { pose proof (w4_ablk_ap DT (DT + DTL) KDT ltac:(lia)) as H. unfold KXGoM.apart in H |- *. lia. }
    assert (AS3 : KXGoM.apart SPF 480 ASHOFF (ATOP / 8 + 1)) by (apply w4_stk_ap; lia).
    assert (DJ1' : KXGoM.apart DST dcap (DT + 4) 4096) by (unfold KXGoM.apart in *; lia).
    assert (DJ2' : KXGoM.apart DST dcap SPF 480) by (unfold KXGoM.apart in *; lia).
    assert (DJ3' : KXGoM.apart SPF 480 (DT + 4) 4096) by (unfold KXGoM.apart in *; lia).
    assert (HDT' : 2^20 <= DT <= 2^47 - 4100) by (unfold AIMG_HI in BK1; lia).
    assert (HDST : 2^20 <= DST <= 2^47 - 1) by (unfold AIMG_HI in BK4; lia).
    assert (HDE : DST + dcap <= 2^47) by lia.
    assert (HP : 2^20 <= SPF <= 2^47 - 480) by lia.
    assert (HAT1 : DT + 4100 <= ATOP) by lia.
    assert (HAT3 : ATOP + 4096 <= SPF) by lia.
    assert (DT16 : DT mod 16 = 0) by exact BK3.
    assert (LOUT' : zlen (map (Z_to_bv 8) buf) = dcap) by (rewrite length_map; exact LOUT).
    unfold ASHOFF in AS1, AS2, AS3.
    set (P := SPF) in *. assert (HPE : P = SPF) by reflexivity. clearbody P.
    assert (K' : forall (mm' : amem) (c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 : word) (buf' : list Z),
              munch [(P + 336, P + 368); (DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
              u8arr bsegs mm' DST (map (Z_to_bv 8) buf') -> zlen buf' = dcap ->
              rw_cells bsegs mm' (P + 336) [C8 c0; C8 c1; C8 c2; C8 c3; C8 pb4] ->
              bv_unsigned c0 mod 2^20 <> 0 -> bv_unsigned c1 mod 2^20 <> 0 ->
              bv_unsigned c2 mod 2^20 <> 0 -> bv_unsigned c3 mod 2^20 <> 0 ->
              evtF bsegs RNG Q (w4_ist P 0x88330 x8 y9 y10 y12 y18 y19 y20 y22 y25 mm')).
    { intros mm' c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 buf' MU' WM' MI' OUT' LOUT2 C336' LC0 LC1 LC2 LC3.
      pose proof (bv_unsigned_in_range _ c0) as R0. pose proof (bv_unsigned_in_range _ c1) as R1.
      pose proof (bv_unsigned_in_range _ c2) as R2. pose proof (bv_unsigned_in_range _ c3) as R3.
      unfold bv_modulus in R0, R1, R2, R3. change (Z.of_N 64) with 64 in R0, R1, R2, R3.
      apply (K mm' (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3) y9 y10 y12 y18 y19 y20 y22 y25);
        [| lia | lia | lia | lia | exact LC0 | exact LC1 | exact LC2 | exact LC3].
      subst P.
      apply (w4_tr mm mm' fr mid _ _ _ _ _ _ buf' HW0);
        [ apply (munch_weaken [(SPF + 336, SPF + 368); (DST, DST + dcap)]); [| exact MU'];
          intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (Hx1 & Hx2 & _); repeat split; lia
        | exact WM' | exact MI' | exact OUT' | exact LOUT2
        | eapply rw_cells_transport; [exact C256 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L256L; lia]
        | exact L256L
        | eapply rw_cells_transport; [exact C296 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L296L; lia]
        | exact L296L
        | rewrite !Z_to_bv_bv_unsigned; exact C336'
        | reflexivity ]. }
    clear - ZT TB LCB OUT LOUT' MI C256 C336 UT UDB' RP RT WDB RTS WDBS HDT' HDST HDE HP DC DT16
      HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 DJ1' DJ2' DJ3' AS1 AS2 AS3 HAT1 BK5 BK6 HAT3 HAH K'.
    unfold w4_ist in K' |- *.
    cbv [AW4_KSB AW4_K21 AW4_KTB] in K' |- *.
    (kx_prepFm [0x88330; 0x88ddc; 0x88dec; 0x88df8; 0x88e08; 0x88e14; 0x88e24; 0x88e30; 0x88e40; 0x8cb6c] 400%nat
      [KZTab (DT + 4) 4096 2 [(0, 0, 11)]; KZAlign DT 16;
       KZRange DT (2^20) (2^47 - 4100); KZRange DST (2^20) (2^47 - 1); KZRange dcap 1 (2^32); KZRange P (2^20) (2^47 - 480);
       KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
       KZRange (DST + o0) (2^20) (2^47 - 1); KZRange (DST + o1) (2^20) (2^47 - 1);
       KZRange (DST + o2) (2^20) (2^47 - 1); KZRange (DST + o3) (2^20) (2^47 - 1);
       KZRange B0 0 (2^64 - 1); KZRange B1 0 (2^64 - 1); KZRange B2 0 (2^64 - 1); KZRange B3 0 (2^64 - 1);
       KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
       KZWord (P + 336) 8 B0; KZWord (P + 344) 8 B1; KZWord (P + 352) 8 B2; KZWord (P + 360) 8 B3;
       KZWr (P + 256) 40; KZWr (P + 336) 40;
       KZWr (DST + o0) 1; KZWr (DST + o1) 1; KZWr (DST + o2) 1; KZWr (DST + o3) 1;
       KZDisj (DST + o0) 1 (DT + 4) 4096; KZDisj (DST + o1) 1 (DT + 4) 4096;
       KZDisj (DST + o2) 1 (DT + 4) 4096; KZDisj (DST + o3) 1 (DT + 4) 4096;
       KZDisj (DST + o0) 1 P 480; KZDisj (DST + o1) 1 P 480; KZDisj (DST + o2) 1 P 480; KZDisj (DST + o3) 1 P 480;
       KZDisj P 480 (DT + 4) 4096]
      [(DT + 4, 4096)]
      [(P, 480); (DT + 4, 4096); (DST + o0, 1); (DST + o1, 1); (DST + o2, 1); (DST + o3, 1)]
      [(DT + 4, 4096); (DST + o0, 1); (DST + o1, 1); (DST + o2, 1); (DST + o3, 1)];
      let D := eval vm_compute in (repeat true 256) in kx_goFL D).
    all: try w4br.
    all: try (w4fshd ATOP).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end).
    lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_d0: side goal left" end.
    kx_post_regs_keep.
    pose proof (munch_refl [(P + 336, P + 368); (DST, DST + dcap)] mm) as MU0.
    pose proof (wmono_refl bsegs mm) as WM0.
    kx_munch_wins MU0 [(P + 336, 32); (DST + o0, 1); (DST + o1, 1); (DST + o2, 1); (DST + o3, 1)].
    kx_post_mem_free.
    kx_cells_split C336. w4f_frame3 MU0. w4f_cells_post.
    lazymatch goal with HLF : KXS.log_flat ?E ?lg |- context [KXS.mem_denot ?E mm ?lg] =>
      destruct (kx_u8arr_ex bsegs E mm lg DST buf OUT HLF) as (buf' & OUT' & LOUT2)
    end.
    w4f_bits (P + 336) 8 ZT (DT + 4) HB0 LB0 e0.
    w4f_bits (P + 344) 8 ZT (DT + 4) HB1 LB1 e1.
    w4f_bits (P + 352) 8 ZT (DT + 4) HB2 LB2 e2.
    w4f_bits (P + 360) 8 ZT (DT + 4) HB3 LB3 e3.
    lazymatch goal with |- context [KXS.mem_denot ?E mm ?lg] => set (mm' := KXS.mem_denot E mm lg) in * end.
    try change (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (-1 * DT + -5)).
    eapply (K' mm' (alu64 ALU_SLL (Z_to_bv 64 B0) e0) (alu64 ALU_SLL (Z_to_bv 64 B1) e1)
                   (alu64 ALU_SLL (Z_to_bv 64 B2) e2) (alu64 ALU_SLL (Z_to_bv 64 B3) e3)).
    all: try assumption.
    all: try (rewrite LOUT2; rewrite length_map in LOUT'; exact LOUT').
    all: try kx_cells_merge.
  Qed.
  Lemma w4_d1 : forall (Q : machine_state -> Prop) (mm : amem) (fr mid : list cell) (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 : Z)
      (po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25 : word),
    tl = 11 ->
    W4FX mm fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
    0 <= o0 -> o0 + 5 <= dcap -> 0 <= o1 -> o1 + 5 <= dcap -> 0 <= o2 -> o2 + 5 <= dcap -> 0 <= o3 -> o3 + 5 <= dcap ->
    0 <= B0 < 2^64 -> 0 <= B1 < 2^64 -> 0 <= B2 < 2^64 -> 0 <= B3 < 2^64 ->
    B0 mod 2^20 <> 0 -> B1 mod 2^20 <> 0 -> B2 mod 2^20 <> 0 -> B3 mod 2^20 <> 0 ->
    (forall (mm' : amem) (C0 C1 C2 C3 : Z) (y9 y10 y12 y18 y19 y20 y22 y25 : word),
       W4FX mm' fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb C0 C1 C2 C3 pb4) ->
       0 <= C0 < 2^64 -> 0 <= C1 < 2^64 -> 0 <= C2 < 2^64 -> 0 <= C3 < 2^64 ->
       C0 mod 2^31 <> 0 -> C1 mod 2^31 <> 0 -> C2 mod 2^31 <> 0 -> C3 mod 2^31 <> 0 ->
       evtF bsegs RNG Q (w4_ist SPF 0x884d8 x8 y9 y10 y12 y18 y19 y20 y22 y25 mm')) ->
    evtF bsegs RNG Q (w4_ist SPF 0x88330 x8 x9 x10 x12 x18 x19 x20 x22 x25 mm).
  Proof using All.
    intros Q mm fr mid o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25
      T11 HW HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 K.
    pose proof (w4_tab11 mm T11) as ZT0.
    unfold w4_lo, w4_li, w4_lb in HW, K. pose proof HW as HW0.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof (ZT0 TB) as ZT. clear ZT0.
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof w4_dtl as HDTL.
    pose proof (w4_unp mm MU) as (UDT' & UDB' & USB').
    pose proof (@ATOP_lo rc) as HAL. pose proof (@ATOP_hi rc) as HAH.
    pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (_ & (KDT & _) & _).
    assert (UT : unpoisoned mm DT (DT + 4100)) by (eapply unpoisoned_sub; [exact UDT' | lia | lia]).
    assert (RP : rng RNG SPF 480) by (eapply rng_sub; [exact WSK | lia | lia]).
    assert (RT : rng RNG (DT + 4) 4096) by (eapply rng_sub; [exact WDT | lia | lia]).
    assert (RTS : rng RNG (shad DT) (shlen (4100 + 7))).
    { eapply rng_sub; [exact WDTS | lia |].
      assert (shlen (4100 + 7) <= shlen (DTL + 7)) by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; apply Z.div_le_mono; lia).
      lia. }
    assert (AS1 : KXGoM.apart DST dcap ASHOFF (ATOP / 8 + 1)).
    { pose proof (w4_ablk_ap DST (DST + dcap) BK7 ltac:(lia)) as H. replace (DST + dcap - DST) with dcap in H by lia. exact H. }
    assert (AS2 : KXGoM.apart DT 4100 ASHOFF (ATOP / 8 + 1)).
    { pose proof (w4_ablk_ap DT (DT + DTL) KDT ltac:(lia)) as H. unfold KXGoM.apart in H |- *. lia. }
    assert (AS3 : KXGoM.apart SPF 480 ASHOFF (ATOP / 8 + 1)) by (apply w4_stk_ap; lia).
    assert (DJ1' : KXGoM.apart DST dcap (DT + 4) 4096) by (unfold KXGoM.apart in *; lia).
    assert (DJ2' : KXGoM.apart DST dcap SPF 480) by (unfold KXGoM.apart in *; lia).
    assert (DJ3' : KXGoM.apart SPF 480 (DT + 4) 4096) by (unfold KXGoM.apart in *; lia).
    assert (HDT' : 2^20 <= DT <= 2^47 - 4100) by (unfold AIMG_HI in BK1; lia).
    assert (HDST : 2^20 <= DST <= 2^47 - 1) by (unfold AIMG_HI in BK4; lia).
    assert (HDE : DST + dcap <= 2^47) by lia.
    assert (HP : 2^20 <= SPF <= 2^47 - 480) by lia.
    assert (HAT1 : DT + 4100 <= ATOP) by lia.
    assert (HAT3 : ATOP + 4096 <= SPF) by lia.
    assert (DT16 : DT mod 16 = 0) by exact BK3.
    assert (LOUT' : zlen (map (Z_to_bv 8) buf) = dcap) by (rewrite length_map; exact LOUT).
    unfold ASHOFF in AS1, AS2, AS3.
    set (P := SPF) in *. assert (HPE : P = SPF) by reflexivity. clearbody P.
    assert (K' : forall (mm' : amem) (c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 : word) (buf' : list Z),
              munch [(P + 336, P + 368); (DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
              u8arr bsegs mm' DST (map (Z_to_bv 8) buf') -> zlen buf' = dcap ->
              rw_cells bsegs mm' (P + 336) [C8 c0; C8 c1; C8 c2; C8 c3; C8 pb4] ->
              bv_unsigned c0 mod 2^31 <> 0 -> bv_unsigned c1 mod 2^31 <> 0 ->
              bv_unsigned c2 mod 2^31 <> 0 -> bv_unsigned c3 mod 2^31 <> 0 ->
              evtF bsegs RNG Q (w4_ist P 0x884d8 x8 y9 y10 y12 y18 y19 y20 y22 y25 mm')).
    { intros mm' c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 buf' MU' WM' MI' OUT' LOUT2 C336' LC0 LC1 LC2 LC3.
      pose proof (bv_unsigned_in_range _ c0) as R0. pose proof (bv_unsigned_in_range _ c1) as R1.
      pose proof (bv_unsigned_in_range _ c2) as R2. pose proof (bv_unsigned_in_range _ c3) as R3.
      unfold bv_modulus in R0, R1, R2, R3. change (Z.of_N 64) with 64 in R0, R1, R2, R3.
      apply (K mm' (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3) y9 y10 y12 y18 y19 y20 y22 y25);
        [| lia | lia | lia | lia | exact LC0 | exact LC1 | exact LC2 | exact LC3].
      subst P.
      apply (w4_tr mm mm' fr mid _ _ _ _ _ _ buf' HW0);
        [ apply (munch_weaken [(SPF + 336, SPF + 368); (DST, DST + dcap)]); [| exact MU'];
          intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (Hx1 & Hx2 & _); repeat split; lia
        | exact WM' | exact MI' | exact OUT' | exact LOUT2
        | eapply rw_cells_transport; [exact C256 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L256L; lia]
        | exact L256L
        | eapply rw_cells_transport; [exact C296 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L296L; lia]
        | exact L296L
        | rewrite !Z_to_bv_bv_unsigned; exact C336'
        | reflexivity ]. }
    clear - ZT TB LCB OUT LOUT' MI C256 C336 UT UDB' RP RT WDB RTS WDBS HDT' HDST HDE HP DC DT16
      HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 DJ1' DJ2' DJ3' AS1 AS2 AS3 HAT1 BK5 BK6 HAT3 HAH K'.
    unfold w4_ist in K' |- *.
    cbv [AW4_KSB AW4_K21 AW4_KTB] in K' |- *.
    (kx_prepFm [0x884d8; 0x88e4c; 0x88e5c; 0x88e68; 0x88e78; 0x88e84; 0x88e94; 0x88ea0; 0x88eb0; 0x8cb6c] 400%nat
      [KZTab (DT + 4) 4096 2 [(0, 0, 11)]; KZAlign DT 16;
       KZRange DT (2^20) (2^47 - 4100); KZRange DST (2^20) (2^47 - 1); KZRange dcap 1 (2^32); KZRange P (2^20) (2^47 - 480);
       KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
       KZRange (DST + o0) (2^20) (2^47 - 1); KZRange (DST + o1) (2^20) (2^47 - 1);
       KZRange (DST + o2) (2^20) (2^47 - 1); KZRange (DST + o3) (2^20) (2^47 - 1);
       KZRange B0 0 (2^64 - 1); KZRange B1 0 (2^64 - 1); KZRange B2 0 (2^64 - 1); KZRange B3 0 (2^64 - 1);
       KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
       KZWord (P + 336) 8 B0; KZWord (P + 344) 8 B1; KZWord (P + 352) 8 B2; KZWord (P + 360) 8 B3;
       KZWr (P + 256) 40; KZWr (P + 336) 40;
       KZWr (DST + o0 + 1) 1; KZWr (DST + o1 + 1) 1; KZWr (DST + o2 + 1) 1; KZWr (DST + o3 + 1) 1;
       KZDisj (DST + o0 + 1) 1 (DT + 4) 4096; KZDisj (DST + o1 + 1) 1 (DT + 4) 4096;
       KZDisj (DST + o2 + 1) 1 (DT + 4) 4096; KZDisj (DST + o3 + 1) 1 (DT + 4) 4096;
       KZDisj (DST + o0 + 1) 1 P 480; KZDisj (DST + o1 + 1) 1 P 480; KZDisj (DST + o2 + 1) 1 P 480; KZDisj (DST + o3 + 1) 1 P 480;
       KZDisj P 480 (DT + 4) 4096]
      [(DT + 4, 4096)]
      [(P, 480); (DT + 4, 4096); (DST + o0 + 1, 1); (DST + o1 + 1, 1); (DST + o2 + 1, 1); (DST + o3 + 1, 1)]
      [(DT + 4, 4096); (DST + o0 + 1, 1); (DST + o1 + 1, 1); (DST + o2 + 1, 1); (DST + o3 + 1, 1)];
      let D := eval vm_compute in (repeat true 256) in kx_goFL D).
    all: try w4br.
    all: try (w4fshd ATOP).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end).
    lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_d0: side goal left" end.
    kx_post_regs_keep.
    pose proof (munch_refl [(P + 336, P + 368); (DST, DST + dcap)] mm) as MU0.
    pose proof (wmono_refl bsegs mm) as WM0.
    kx_munch_wins MU0 [(P + 336, 32); (DST + o0 + 1, 1); (DST + o1 + 1, 1); (DST + o2 + 1, 1); (DST + o3 + 1, 1)].
    kx_post_mem_free.
    kx_cells_split C336. w4f_frame3 MU0. w4f_cells_post.
    lazymatch goal with HLF : KXS.log_flat ?E ?lg |- context [KXS.mem_denot ?E mm ?lg] =>
      destruct (kx_u8arr_ex bsegs E mm lg DST buf OUT HLF) as (buf' & OUT' & LOUT2)
    end.
    w4f_bits (P + 336) 19 ZT (DT + 4) HB0 LB0 e0.
    w4f_bits (P + 344) 19 ZT (DT + 4) HB1 LB1 e1.
    w4f_bits (P + 352) 19 ZT (DT + 4) HB2 LB2 e2.
    w4f_bits (P + 360) 19 ZT (DT + 4) HB3 LB3 e3.
    lazymatch goal with |- context [KXS.mem_denot ?E mm ?lg] => set (mm' := KXS.mem_denot E mm lg) in * end.
    try change (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (-1 * DT + -5)).
    eapply (K' mm' (alu64 ALU_SLL (Z_to_bv 64 B0) e0) (alu64 ALU_SLL (Z_to_bv 64 B1) e1)
                   (alu64 ALU_SLL (Z_to_bv 64 B2) e2) (alu64 ALU_SLL (Z_to_bv 64 B3) e3)).
    all: try assumption.
    all: try (rewrite LOUT2; rewrite length_map in LOUT'; exact LOUT').
    all: try kx_cells_merge.
  Qed.
  Lemma w4_d2 : forall (Q : machine_state -> Prop) (mm : amem) (fr mid : list cell) (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 : Z)
      (po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25 : word),
    tl = 11 ->
    W4FX mm fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
    0 <= o0 -> o0 + 5 <= dcap -> 0 <= o1 -> o1 + 5 <= dcap -> 0 <= o2 -> o2 + 5 <= dcap -> 0 <= o3 -> o3 + 5 <= dcap ->
    0 <= B0 < 2^64 -> 0 <= B1 < 2^64 -> 0 <= B2 < 2^64 -> 0 <= B3 < 2^64 ->
    B0 mod 2^31 <> 0 -> B1 mod 2^31 <> 0 -> B2 mod 2^31 <> 0 -> B3 mod 2^31 <> 0 ->
    (forall (mm' : amem) (C0 C1 C2 C3 : Z) (y9 y10 y12 y18 y19 y20 y22 y25 : word),
       W4FX mm' fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb C0 C1 C2 C3 pb4) ->
       0 <= C0 < 2^64 -> 0 <= C1 < 2^64 -> 0 <= C2 < 2^64 -> 0 <= C3 < 2^64 ->
       C0 mod 2^42 <> 0 -> C1 mod 2^42 <> 0 -> C2 mod 2^42 <> 0 -> C3 mod 2^42 <> 0 ->
       evtF bsegs RNG Q (w4_ist SPF 0x88678 x8 y9 y10 y12 y18 y19 y20 y22 y25 mm')) ->
    evtF bsegs RNG Q (w4_ist SPF 0x884d8 x8 x9 x10 x12 x18 x19 x20 x22 x25 mm).
  Proof using All.
    intros Q mm fr mid o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25
      T11 HW HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 K.
    pose proof (w4_tab11 mm T11) as ZT0.
    unfold w4_lo, w4_li, w4_lb in HW, K. pose proof HW as HW0.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof (ZT0 TB) as ZT. clear ZT0.
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof w4_dtl as HDTL.
    pose proof (w4_unp mm MU) as (UDT' & UDB' & USB').
    pose proof (@ATOP_lo rc) as HAL. pose proof (@ATOP_hi rc) as HAH.
    pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (_ & (KDT & _) & _).
    assert (UT : unpoisoned mm DT (DT + 4100)) by (eapply unpoisoned_sub; [exact UDT' | lia | lia]).
    assert (RP : rng RNG SPF 480) by (eapply rng_sub; [exact WSK | lia | lia]).
    assert (RT : rng RNG (DT + 4) 4096) by (eapply rng_sub; [exact WDT | lia | lia]).
    assert (RTS : rng RNG (shad DT) (shlen (4100 + 7))).
    { eapply rng_sub; [exact WDTS | lia |].
      assert (shlen (4100 + 7) <= shlen (DTL + 7)) by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; apply Z.div_le_mono; lia).
      lia. }
    assert (AS1 : KXGoM.apart DST dcap ASHOFF (ATOP / 8 + 1)).
    { pose proof (w4_ablk_ap DST (DST + dcap) BK7 ltac:(lia)) as H. replace (DST + dcap - DST) with dcap in H by lia. exact H. }
    assert (AS2 : KXGoM.apart DT 4100 ASHOFF (ATOP / 8 + 1)).
    { pose proof (w4_ablk_ap DT (DT + DTL) KDT ltac:(lia)) as H. unfold KXGoM.apart in H |- *. lia. }
    assert (AS3 : KXGoM.apart SPF 480 ASHOFF (ATOP / 8 + 1)) by (apply w4_stk_ap; lia).
    assert (DJ1' : KXGoM.apart DST dcap (DT + 4) 4096) by (unfold KXGoM.apart in *; lia).
    assert (DJ2' : KXGoM.apart DST dcap SPF 480) by (unfold KXGoM.apart in *; lia).
    assert (DJ3' : KXGoM.apart SPF 480 (DT + 4) 4096) by (unfold KXGoM.apart in *; lia).
    assert (HDT' : 2^20 <= DT <= 2^47 - 4100) by (unfold AIMG_HI in BK1; lia).
    assert (HDST : 2^20 <= DST <= 2^47 - 1) by (unfold AIMG_HI in BK4; lia).
    assert (HDE : DST + dcap <= 2^47) by lia.
    assert (HP : 2^20 <= SPF <= 2^47 - 480) by lia.
    assert (HAT1 : DT + 4100 <= ATOP) by lia.
    assert (HAT3 : ATOP + 4096 <= SPF) by lia.
    assert (DT16 : DT mod 16 = 0) by exact BK3.
    assert (LOUT' : zlen (map (Z_to_bv 8) buf) = dcap) by (rewrite length_map; exact LOUT).
    unfold ASHOFF in AS1, AS2, AS3.
    set (P := SPF) in *. assert (HPE : P = SPF) by reflexivity. clearbody P.
    assert (K' : forall (mm' : amem) (c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 : word) (buf' : list Z),
              munch [(P + 336, P + 368); (DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
              u8arr bsegs mm' DST (map (Z_to_bv 8) buf') -> zlen buf' = dcap ->
              rw_cells bsegs mm' (P + 336) [C8 c0; C8 c1; C8 c2; C8 c3; C8 pb4] ->
              bv_unsigned c0 mod 2^42 <> 0 -> bv_unsigned c1 mod 2^42 <> 0 ->
              bv_unsigned c2 mod 2^42 <> 0 -> bv_unsigned c3 mod 2^42 <> 0 ->
              evtF bsegs RNG Q (w4_ist P 0x88678 x8 y9 y10 y12 y18 y19 y20 y22 y25 mm')).
    { intros mm' c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 buf' MU' WM' MI' OUT' LOUT2 C336' LC0 LC1 LC2 LC3.
      pose proof (bv_unsigned_in_range _ c0) as R0. pose proof (bv_unsigned_in_range _ c1) as R1.
      pose proof (bv_unsigned_in_range _ c2) as R2. pose proof (bv_unsigned_in_range _ c3) as R3.
      unfold bv_modulus in R0, R1, R2, R3. change (Z.of_N 64) with 64 in R0, R1, R2, R3.
      apply (K mm' (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3) y9 y10 y12 y18 y19 y20 y22 y25);
        [| lia | lia | lia | lia | exact LC0 | exact LC1 | exact LC2 | exact LC3].
      subst P.
      apply (w4_tr mm mm' fr mid _ _ _ _ _ _ buf' HW0);
        [ apply (munch_weaken [(SPF + 336, SPF + 368); (DST, DST + dcap)]); [| exact MU'];
          intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (Hx1 & Hx2 & _); repeat split; lia
        | exact WM' | exact MI' | exact OUT' | exact LOUT2
        | eapply rw_cells_transport; [exact C256 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L256L; lia]
        | exact L256L
        | eapply rw_cells_transport; [exact C296 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L296L; lia]
        | exact L296L
        | rewrite !Z_to_bv_bv_unsigned; exact C336'
        | reflexivity ]. }
    clear - ZT TB LCB OUT LOUT' MI C256 C336 UT UDB' RP RT WDB RTS WDBS HDT' HDST HDE HP DC DT16
      HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 DJ1' DJ2' DJ3' AS1 AS2 AS3 HAT1 BK5 BK6 HAT3 HAH K'.
    unfold w4_ist in K' |- *.
    cbv [AW4_KSB AW4_K21 AW4_KTB] in K' |- *.
    (kx_prepFm [0x88678; 0x88ebc; 0x88ecc; 0x88ed8; 0x88ee8; 0x88ef4; 0x88f04; 0x88f10; 0x88f20; 0x8cb6c] 400%nat
      [KZTab (DT + 4) 4096 2 [(0, 0, 11)]; KZAlign DT 16;
       KZRange DT (2^20) (2^47 - 4100); KZRange DST (2^20) (2^47 - 1); KZRange dcap 1 (2^32); KZRange P (2^20) (2^47 - 480);
       KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
       KZRange (DST + o0) (2^20) (2^47 - 1); KZRange (DST + o1) (2^20) (2^47 - 1);
       KZRange (DST + o2) (2^20) (2^47 - 1); KZRange (DST + o3) (2^20) (2^47 - 1);
       KZRange B0 0 (2^64 - 1); KZRange B1 0 (2^64 - 1); KZRange B2 0 (2^64 - 1); KZRange B3 0 (2^64 - 1);
       KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
       KZWord (P + 336) 8 B0; KZWord (P + 344) 8 B1; KZWord (P + 352) 8 B2; KZWord (P + 360) 8 B3;
       KZWr (P + 256) 40; KZWr (P + 336) 40;
       KZWr (DST + o0 + 2) 1; KZWr (DST + o1 + 2) 1; KZWr (DST + o2 + 2) 1; KZWr (DST + o3 + 2) 1;
       KZDisj (DST + o0 + 2) 1 (DT + 4) 4096; KZDisj (DST + o1 + 2) 1 (DT + 4) 4096;
       KZDisj (DST + o2 + 2) 1 (DT + 4) 4096; KZDisj (DST + o3 + 2) 1 (DT + 4) 4096;
       KZDisj (DST + o0 + 2) 1 P 480; KZDisj (DST + o1 + 2) 1 P 480; KZDisj (DST + o2 + 2) 1 P 480; KZDisj (DST + o3 + 2) 1 P 480;
       KZDisj P 480 (DT + 4) 4096]
      [(DT + 4, 4096)]
      [(P, 480); (DT + 4, 4096); (DST + o0 + 2, 1); (DST + o1 + 2, 1); (DST + o2 + 2, 1); (DST + o3 + 2, 1)]
      [(DT + 4, 4096); (DST + o0 + 2, 1); (DST + o1 + 2, 1); (DST + o2 + 2, 1); (DST + o3 + 2, 1)];
      let D := eval vm_compute in (repeat true 256) in kx_goFL D).
    all: try w4br.
    all: try (w4fshd ATOP).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end).
    lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_d0: side goal left" end.
    kx_post_regs_keep.
    pose proof (munch_refl [(P + 336, P + 368); (DST, DST + dcap)] mm) as MU0.
    pose proof (wmono_refl bsegs mm) as WM0.
    kx_munch_wins MU0 [(P + 336, 32); (DST + o0 + 2, 1); (DST + o1 + 2, 1); (DST + o2 + 2, 1); (DST + o3 + 2, 1)].
    kx_post_mem_free.
    kx_cells_split C336. w4f_frame3 MU0. w4f_cells_post.
    lazymatch goal with HLF : KXS.log_flat ?E ?lg |- context [KXS.mem_denot ?E mm ?lg] =>
      destruct (kx_u8arr_ex bsegs E mm lg DST buf OUT HLF) as (buf' & OUT' & LOUT2)
    end.
    w4f_bits (P + 336) 30 ZT (DT + 4) HB0 LB0 e0.
    w4f_bits (P + 344) 30 ZT (DT + 4) HB1 LB1 e1.
    w4f_bits (P + 352) 30 ZT (DT + 4) HB2 LB2 e2.
    w4f_bits (P + 360) 30 ZT (DT + 4) HB3 LB3 e3.
    lazymatch goal with |- context [KXS.mem_denot ?E mm ?lg] => set (mm' := KXS.mem_denot E mm lg) in * end.
    try change (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (-1 * DT + -5)).
    eapply (K' mm' (alu64 ALU_SLL (Z_to_bv 64 B0) e0) (alu64 ALU_SLL (Z_to_bv 64 B1) e1)
                   (alu64 ALU_SLL (Z_to_bv 64 B2) e2) (alu64 ALU_SLL (Z_to_bv 64 B3) e3)).
    all: try assumption.
    all: try (rewrite LOUT2; rewrite length_map in LOUT'; exact LOUT').
    all: try kx_cells_merge.
  Qed.
  Lemma w4_d3 : forall (Q : machine_state -> Prop) (mm : amem) (fr mid : list cell) (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 : Z)
      (po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25 : word),
    tl = 11 ->
    W4FX mm fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
    0 <= o0 -> o0 + 5 <= dcap -> 0 <= o1 -> o1 + 5 <= dcap -> 0 <= o2 -> o2 + 5 <= dcap -> 0 <= o3 -> o3 + 5 <= dcap ->
    0 <= B0 < 2^64 -> 0 <= B1 < 2^64 -> 0 <= B2 < 2^64 -> 0 <= B3 < 2^64 ->
    B0 mod 2^42 <> 0 -> B1 mod 2^42 <> 0 -> B2 mod 2^42 <> 0 -> B3 mod 2^42 <> 0 ->
    (forall (mm' : amem) (C0 C1 C2 C3 : Z) (y9 y10 y12 y18 y19 y20 y22 y25 : word),
       W4FX mm' fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb C0 C1 C2 C3 pb4) ->
       0 <= C0 < 2^64 -> 0 <= C1 < 2^64 -> 0 <= C2 < 2^64 -> 0 <= C3 < 2^64 ->
       C0 mod 2^53 <> 0 -> C1 mod 2^53 <> 0 -> C2 mod 2^53 <> 0 -> C3 mod 2^53 <> 0 ->
       evtF bsegs RNG Q (w4_ist SPF 0x88818 x8 y9 y10 y12 y18 y19 y20 y22 y25 mm')) ->
    evtF bsegs RNG Q (w4_ist SPF 0x88678 x8 x9 x10 x12 x18 x19 x20 x22 x25 mm).
  Proof using All.
    intros Q mm fr mid o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25
      T11 HW HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 K.
    pose proof (w4_tab11 mm T11) as ZT0.
    unfold w4_lo, w4_li, w4_lb in HW, K. pose proof HW as HW0.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof (ZT0 TB) as ZT. clear ZT0.
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof w4_dtl as HDTL.
    pose proof (w4_unp mm MU) as (UDT' & UDB' & USB').
    pose proof (@ATOP_lo rc) as HAL. pose proof (@ATOP_hi rc) as HAH.
    pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (_ & (KDT & _) & _).
    assert (UT : unpoisoned mm DT (DT + 4100)) by (eapply unpoisoned_sub; [exact UDT' | lia | lia]).
    assert (RP : rng RNG SPF 480) by (eapply rng_sub; [exact WSK | lia | lia]).
    assert (RT : rng RNG (DT + 4) 4096) by (eapply rng_sub; [exact WDT | lia | lia]).
    assert (RTS : rng RNG (shad DT) (shlen (4100 + 7))).
    { eapply rng_sub; [exact WDTS | lia |].
      assert (shlen (4100 + 7) <= shlen (DTL + 7)) by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; apply Z.div_le_mono; lia).
      lia. }
    assert (AS1 : KXGoM.apart DST dcap ASHOFF (ATOP / 8 + 1)).
    { pose proof (w4_ablk_ap DST (DST + dcap) BK7 ltac:(lia)) as H. replace (DST + dcap - DST) with dcap in H by lia. exact H. }
    assert (AS2 : KXGoM.apart DT 4100 ASHOFF (ATOP / 8 + 1)).
    { pose proof (w4_ablk_ap DT (DT + DTL) KDT ltac:(lia)) as H. unfold KXGoM.apart in H |- *. lia. }
    assert (AS3 : KXGoM.apart SPF 480 ASHOFF (ATOP / 8 + 1)) by (apply w4_stk_ap; lia).
    assert (DJ1' : KXGoM.apart DST dcap (DT + 4) 4096) by (unfold KXGoM.apart in *; lia).
    assert (DJ2' : KXGoM.apart DST dcap SPF 480) by (unfold KXGoM.apart in *; lia).
    assert (DJ3' : KXGoM.apart SPF 480 (DT + 4) 4096) by (unfold KXGoM.apart in *; lia).
    assert (HDT' : 2^20 <= DT <= 2^47 - 4100) by (unfold AIMG_HI in BK1; lia).
    assert (HDST : 2^20 <= DST <= 2^47 - 1) by (unfold AIMG_HI in BK4; lia).
    assert (HDE : DST + dcap <= 2^47) by lia.
    assert (HP : 2^20 <= SPF <= 2^47 - 480) by lia.
    assert (HAT1 : DT + 4100 <= ATOP) by lia.
    assert (HAT3 : ATOP + 4096 <= SPF) by lia.
    assert (DT16 : DT mod 16 = 0) by exact BK3.
    assert (LOUT' : zlen (map (Z_to_bv 8) buf) = dcap) by (rewrite length_map; exact LOUT).
    unfold ASHOFF in AS1, AS2, AS3.
    set (P := SPF) in *. assert (HPE : P = SPF) by reflexivity. clearbody P.
    assert (K' : forall (mm' : amem) (c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 : word) (buf' : list Z),
              munch [(P + 336, P + 368); (DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
              u8arr bsegs mm' DST (map (Z_to_bv 8) buf') -> zlen buf' = dcap ->
              rw_cells bsegs mm' (P + 336) [C8 c0; C8 c1; C8 c2; C8 c3; C8 pb4] ->
              bv_unsigned c0 mod 2^53 <> 0 -> bv_unsigned c1 mod 2^53 <> 0 ->
              bv_unsigned c2 mod 2^53 <> 0 -> bv_unsigned c3 mod 2^53 <> 0 ->
              evtF bsegs RNG Q (w4_ist P 0x88818 x8 y9 y10 y12 y18 y19 y20 y22 y25 mm')).
    { intros mm' c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 buf' MU' WM' MI' OUT' LOUT2 C336' LC0 LC1 LC2 LC3.
      pose proof (bv_unsigned_in_range _ c0) as R0. pose proof (bv_unsigned_in_range _ c1) as R1.
      pose proof (bv_unsigned_in_range _ c2) as R2. pose proof (bv_unsigned_in_range _ c3) as R3.
      unfold bv_modulus in R0, R1, R2, R3. change (Z.of_N 64) with 64 in R0, R1, R2, R3.
      apply (K mm' (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3) y9 y10 y12 y18 y19 y20 y22 y25);
        [| lia | lia | lia | lia | exact LC0 | exact LC1 | exact LC2 | exact LC3].
      subst P.
      apply (w4_tr mm mm' fr mid _ _ _ _ _ _ buf' HW0);
        [ apply (munch_weaken [(SPF + 336, SPF + 368); (DST, DST + dcap)]); [| exact MU'];
          intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (Hx1 & Hx2 & _); repeat split; lia
        | exact WM' | exact MI' | exact OUT' | exact LOUT2
        | eapply rw_cells_transport; [exact C256 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L256L; lia]
        | exact L256L
        | eapply rw_cells_transport; [exact C296 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L296L; lia]
        | exact L296L
        | rewrite !Z_to_bv_bv_unsigned; exact C336'
        | reflexivity ]. }
    clear - ZT TB LCB OUT LOUT' MI C256 C336 UT UDB' RP RT WDB RTS WDBS HDT' HDST HDE HP DC DT16
      HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 DJ1' DJ2' DJ3' AS1 AS2 AS3 HAT1 BK5 BK6 HAT3 HAH K'.
    unfold w4_ist in K' |- *.
    cbv [AW4_KSB AW4_K21 AW4_KTB] in K' |- *.
    (kx_prepFm [0x88818; 0x88f2c; 0x88f3c; 0x88f48; 0x88f58; 0x88f64; 0x88f74; 0x88f80; 0x88f90; 0x8cb6c] 400%nat
      [KZTab (DT + 4) 4096 2 [(0, 0, 11)]; KZAlign DT 16;
       KZRange DT (2^20) (2^47 - 4100); KZRange DST (2^20) (2^47 - 1); KZRange dcap 1 (2^32); KZRange P (2^20) (2^47 - 480);
       KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
       KZRange (DST + o0) (2^20) (2^47 - 1); KZRange (DST + o1) (2^20) (2^47 - 1);
       KZRange (DST + o2) (2^20) (2^47 - 1); KZRange (DST + o3) (2^20) (2^47 - 1);
       KZRange B0 0 (2^64 - 1); KZRange B1 0 (2^64 - 1); KZRange B2 0 (2^64 - 1); KZRange B3 0 (2^64 - 1);
       KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
       KZWord (P + 336) 8 B0; KZWord (P + 344) 8 B1; KZWord (P + 352) 8 B2; KZWord (P + 360) 8 B3;
       KZWr (P + 256) 40; KZWr (P + 336) 40;
       KZWr (DST + o0 + 3) 1; KZWr (DST + o1 + 3) 1; KZWr (DST + o2 + 3) 1; KZWr (DST + o3 + 3) 1;
       KZDisj (DST + o0 + 3) 1 (DT + 4) 4096; KZDisj (DST + o1 + 3) 1 (DT + 4) 4096;
       KZDisj (DST + o2 + 3) 1 (DT + 4) 4096; KZDisj (DST + o3 + 3) 1 (DT + 4) 4096;
       KZDisj (DST + o0 + 3) 1 P 480; KZDisj (DST + o1 + 3) 1 P 480; KZDisj (DST + o2 + 3) 1 P 480; KZDisj (DST + o3 + 3) 1 P 480;
       KZDisj P 480 (DT + 4) 4096]
      [(DT + 4, 4096)]
      [(P, 480); (DT + 4, 4096); (DST + o0 + 3, 1); (DST + o1 + 3, 1); (DST + o2 + 3, 1); (DST + o3 + 3, 1)]
      [(DT + 4, 4096); (DST + o0 + 3, 1); (DST + o1 + 3, 1); (DST + o2 + 3, 1); (DST + o3 + 3, 1)];
      let D := eval vm_compute in (repeat true 256) in kx_goFL D).
    all: try w4br.
    all: try (w4fshd ATOP).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end).
    lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_d0: side goal left" end.
    kx_post_regs_keep.
    pose proof (munch_refl [(P + 336, P + 368); (DST, DST + dcap)] mm) as MU0.
    pose proof (wmono_refl bsegs mm) as WM0.
    kx_munch_wins MU0 [(P + 336, 32); (DST + o0 + 3, 1); (DST + o1 + 3, 1); (DST + o2 + 3, 1); (DST + o3 + 3, 1)].
    kx_post_mem_free.
    kx_cells_split C336. w4f_frame3 MU0. w4f_cells_post.
    lazymatch goal with HLF : KXS.log_flat ?E ?lg |- context [KXS.mem_denot ?E mm ?lg] =>
      destruct (kx_u8arr_ex bsegs E mm lg DST buf OUT HLF) as (buf' & OUT' & LOUT2)
    end.
    w4f_bits (P + 336) 41 ZT (DT + 4) HB0 LB0 e0.
    w4f_bits (P + 344) 41 ZT (DT + 4) HB1 LB1 e1.
    w4f_bits (P + 352) 41 ZT (DT + 4) HB2 LB2 e2.
    w4f_bits (P + 360) 41 ZT (DT + 4) HB3 LB3 e3.
    lazymatch goal with |- context [KXS.mem_denot ?E mm ?lg] => set (mm' := KXS.mem_denot E mm lg) in * end.
    try change (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (-1 * DT + -5)).
    eapply (K' mm' (alu64 ALU_SLL (Z_to_bv 64 B0) e0) (alu64 ALU_SLL (Z_to_bv 64 B1) e1)
                   (alu64 ALU_SLL (Z_to_bv 64 B2) e2) (alu64 ALU_SLL (Z_to_bv 64 B3) e3)).
    all: try assumption.
    all: try (rewrite LOUT2; rewrite length_map in LOUT'; exact LOUT').
    all: try kx_cells_merge.
  Qed.

  Definition w4_c117 (Q : machine_state -> Prop) (b0 b1 b2 b3 : Z) : Prop :=
    forall (mm : amem) (w0 w8 w16 po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25 : word),
      W4FX mm (w4_fr w0 w8 w16) (fast_args_cells DST dcap SS DT src b0 b1 b2 b3)
           (w4_lo 0 ((dcap + 3) / 4) (2 * ((dcap + 3) / 4)) (3 * ((dcap + 3) / 4)) po4)
           (w4_li (jt_len src 0 - 2) (jt_len src 0 + jt_len src 2 - 2) (jt_len src 0 + jt_len src 2 + jt_len src 4 - 2)
                  (n - 8) pi4)
           (w4_lb b0 b1 b2 b3 pb4) ->
      evtF bsegs RNG Q (w4_ist SPF 0x880d8 x8 x9 x10 x12 x18 x19 x20 x22 x25 mm).

End W4F.
End CANSEC1.
