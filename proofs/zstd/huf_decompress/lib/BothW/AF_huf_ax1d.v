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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_ax1 AF_huf_ax1b AF_huf_ax1c.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax1d () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions8bv_swrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr06K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS=swrap32_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z8mul_commK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1c5AX1HKC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax14AX1MI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax17ax1_unpC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax1:ax1_blocksC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax1=ax1_sp_boundsC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax18ax1_outbC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:length_mapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04C5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac;read_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common5KXTac>read_ranges_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp05C5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxm_execC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1b9ax1_tail0C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission6Common6KXPost9kx_mul_m1C56Stdlib5Arith8PeanoNat3Nat3ltbC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFMC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1c6ax1_d0C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okK46Stdlib9micromega5Tauto8GFormula06K47Corelib5Lists7ListDef6Forall02C46Stdlib9micromega;ZifyClasses5mkrelC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00C56Stdlib6ZArith4Znat5Nat2Z6inj_leI5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSK4ELinuxProcessSemantics5Riscv5Instr5aluop07I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_gec5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1d>ax1_signed_litK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1d6ax1_rlc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1d9ax1_land7c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1d:ax1_srliw3C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3b2zK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwK4ELinuxProcessSemantics5Riscv5Instr5instr03C56Stdlib6ZArith6BinInt1Z:mul_div_lec5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1d9ax1_subw8C47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC56Stdlib6ZArith6BinInt1Z7add_0_rK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z4lxorK4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop06C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1d8ax1_headC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z8inj_succC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1d8ax1_loopC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1b<ax1_neg_descC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_default".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).


Lemma ax1_signed_lit : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax1d ()) [] "h04__x1h11zh27__arithh34__ffh48__varmaph55__with62Hzp;1p;2p;3p;4p;8p;6p;7g0000j10Tg000Uj15Tg0013j12Tg001Xj28Tg0025j1YTg002Rj2;Tg002nj26Tg003Jj27Tg003ej1>Tg004Cj2ETg004jj33Tg005Dj2=Tg005aj2@Tg006>j1XTg006^j1UTg007>j2TTg007\j1QTg008:j1PTg008ej2NTg009Hj2:Tg009kj39Tg00:Nj3MTg00;1j3GTg00;Tj44Tg00<?j2FTg00<aj2HTg00=;j2ITg00=gj3JTg00>Fj4KTg00?8j2LTg00?Xj2DTg00@;j1CTg00@]j8BTg00AAj3OTg00Adj6?Tg00BBj2ATg00Bhj2RTg00CPj2STg00D=j7WTg00Daj7VTf1R0g00EER1g00EdR2P2g00FDR3f0R4g00FdFWp=1f2R5P1P2P2P3P0P4FVp=<g00GDR6g00GbR7#0R8#5R9%27#2#2#2#2R:#5'8R;#Y/;4164;'7R<P6%08#0#0#0#0R8#>R=/E0R>A3645X16P61=0;R?1@4;=365X16g00HGR@#XRA%U@R@1T60RB%Q6RC%P6RDP61N67R71:69RE%>:596R:5M6RF=G6:g00I3P7C4'11FD3RGP4P5g00IZRHg00J:RI'H1I45=3HIdg00JZRI=J60CKRHb3b4b5X061=4;/@;=364^06P4P5O1b2%58,89R9,L?PAP@PBPCPDP1P2P2P3P61D6:g00K8R3P7C4,1DP6P7g00K_R7P:C4,1D5<D%C2P61:6IP3PFC4,1DP6PFP7A96E=C4,1D5<DGBPGPHb3b4b5X061;I?16?9'7\<^06P4P5P0O2b29O?9E?A36>0e1A=0,R=1S=0E?W6W1o"). Qed.

(* [comment removed for export] *)
Lemma ax1_srliw3 : forall b, 0 <= b <= 64 -> bv_swrap 32 (bv_wrap 32 b ≫ 3) = b / 8.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax1d ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__p1h61zh71Hh81bp;2p;1p;3p;6p;4p;5p;7p;8p100LFp4p7210g00AdR0p4p710p8g002Rj20Tg0000j14Tg000Uj12Tg003Jj21Tg003ej1CTg0013j18Tg00M2j2ATg004Cj2@Tg00MRj2<Tg004jj3:Tg001Xj29Tg002nj23Tg006>j1ETg006^j1`Tg007>j2]Tg007\j1WTg008:j1VTg009Hj26Tg008ej2UTg00Moj6OTg00@;j1NTg00<?j2MTg00<aj2LTg00=;j2KTg00=gj3HTg00>Fj4ITg00NSj1JTg00O1j4GTg009kj3?Tg00ORj3FTg00P5j2PTg00PRj5QTg00Q>j4RTg00QYj2STg00R^j3TTP0j6DTg00SGj2_Tg00Smj1^Tg00TKj1\Tg00U4j3XTg00;Tj4BTg00D=j7YTg00Daj7ZTg00@]j8[Tg00GDR0f1R1g00K8f0R2CBp=>P1g00EER3g00EdR4P4g00FDR5P2g00FdFYp=5f2R6P3P4P4P5P1P2FZp=7f3R7P3P4P4P5P6P1P2G[p==P0P1g00K_P2CBp=;g00JZR8/02R9g00GbR:#4R;#4#4R<#4#4R=#4#2R>,02R?'1R@P0P1%C=RA%8:RB#2RC,A2'@%2<R<,<6RD5:0X60P0%2;R;/9C,<11@A2=:0DX601<1<RD108D%8B#8#8RB#2,9;RE,3DP1P<p-0RDg00HGRF#ERG%`FRF1]01RH%W0RI%V0RJ1608RK1U0:R:'>,5JRLPJP3P4P4P5P7EOR757J%N4R4PLC=1MJ5R5P2P6g00IZR3g00J:RM'L1K26=:3MdAH081CIRMb2b3b4X00W511911081R9[^00^5DP2106>P6P1O3b1PGPF%J0R3PI160<RN,;K,5JP5PMb2b3b4138<P2b1ROCGP1P<PEPOPGPFPHPIPJ160>,>:,5JR>97J7P4160;R7%CB5?09F0N,;:,5JC=P5PMb2b3b4X00X5D111?1P<E,31[^00^5DP21086P6P1O3b1DQCR'S1A1CPGPFP3PI160C,>K,5JP5PMb2b3b4108CP2b19T1CED1_A1PGPFPHPIPJA7JL>P4A?07A,;:,5J97JLC=P5PMb2b3b4X00%2=,9;,31,19\@^00P2P6P1O2b1%^A,9;,31,19e%\A,31,19e9XA1EDW7X80o"). Qed.
Lemma ax1_land7 : forall b, 0 <= b -> Z.land b 7 = b mod 8.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax1d ()) [] "h01Hh17__arithh24__ffh38__varmaph45__with51bh61zp;2p;1p;3p;4p;7p;6g002Rj26Tg0000j12Tg000Uj11Tg0013j17Tg001Xj2GTg00?8j20Tg004jj33Tg00<aj24Tg00U`j1<Tg00V>j2;Tg006>j18Tg006^j19Tg00NSj1:Tg007\j1FTg008:j1ETg009Hj25Tg00;Tj4DTg00D=j7CTg00<?j2BTg00=;j2?Tg00=gj3@Tg00>Fj4ATg00V\j3>Tg00Adj6=Tg00GDR0g00JZR1f0R2'6P0f1R3g00GbR4#2R5#1%74#1R4'G'0f2R6%25#2#1R5'09302X601035,40%<4,;3g00HGR5#8%95%:0%F0%E0R5g00EEg00EdR7P7g00FDR7P01501g00K81504CDg00FdFC1B57P2P6g00IZR7g00J:R5'41?26=375dA@013CAb2b3b41614P2b19>34E=W0W5o"). Qed.

Lemma ax1_subw8 : forall b x, 0 <= x -> 8 * x <= b <= 64 ->
  bv_swrap 32 (b - Z.land (x ≪ 3) 18446744073709551615) = b - 8 * x.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax1d ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h54__x2h61zh72H1h82H2h91bh:1xp;1p;2p;3p;4p;6p;7p;8g0000j16Tg000Uj17Tg00P5j25Tg002Rj22Tg003Jj2;Tg0013j10Tg001Xj2CTg003ej1ATg00V>j2KTg005aj28Tg004Cj2OTg004jj3ETg00?8j2dTg00W?j1GTg00W^j2>Tg00XGj2[Tg00Y0j3ZTg00YYj3:Tg00ZBj2FTg006>j1XTg00Znj3BTg006^j1WTg007>j2VTg00NSj1UTg00[Nj4TTg007\j1STg008:j1RTg009Hj29Tg008ej2ITg00ORj3@Tg00@;j1QTg00;1j3PTg009kj3HTg00;Tj4DTg00<?j2jTg00<aj2iTg00=;j2hTg00=gj3gTg00>Fj4fTg002nj2MTg00QYj2cTg00[lj2_Tg00Adj6<Tg00\Nj2^Tg00AAj3]Tg00U`j1\Tg00V\j3`Tg00]:j2aTg00]Zj3bTg00D=j7NTg00Daj7eTg00@]j8YTg00JZR0f0R1'2p=3%01#0p=J%01#0#0#0#0#0#0#0p=4f2R2g00EER3g00EdR4P4g00FDR5g00GDR6f1R7g00K8P1CDg00FdR8FNp=1P2P3P4P4P5P7P1Fep==P7P3P4P4P5P1P8FNp=Lf3R8P3P4P4P5P2P7P1GYp=?%31g00GbR3#6R9#6#6R:#7R;/57R</22%6:#6R:#6R=#7R>,22';P6%79R?%03R@#7RA'C,52%A:R:f4RB%0@#JR@#0#J#4#4#4#4#4#4#4#7,K1'8'O15;8RC,8BRD5E6X66P6152;RE1C?>RF'dRG18B1,O:=E6DX66RDP6PEPDP615;2R:PD188:g00HGR:g00^CRD#GRH#GRI,>6RJ1[6;1>6H5Z61>6DRD5:65:6g00^bRH'F%X:RK3B%W:RLP61V62P7%U6RMCTRN%S6RO%R6RP196;RQ1I69R95@6RR1I63R351P196>RS91P35=P%Q4R4PP1960RT=1P9P4AP63RRR91PTP6PRg00K_RR196?RU%A@5H6CD,LP5=PC?C?1jP5R5P1P2g00IZRVg00J:RW'i1h12=EVWdAg607CfR0b1b2b3X46X5612<1121>';%32182CRC#3%7@,C?,MC';[[^46^56P1P8PBP7P2O4b0'cPE1_2;E<PGA:6DJ/FH,^D%GI,>6A:6JD5:6/FH=B:K5B:PLPNPOPPA@6Q3=1P9A1P9S5=PP4PPA1PT3P4A@63QR391PTP6P3PR%A=9H6UCD,LP5=PC?C?P5P0b1b2b3X46X5615;1/27127>';%37%3E1MEF';[[^46^56P1PBP8P7P2O4b09]EFE<%\>,KEPKPLPMPOA1PTSP5P0b1b2b3%3>P1b09`E>E<1a2APKPLPMPO196A91PTP5P0b1b2b3%3AP1b09b2AE<W8W7X:6X96o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section AX1D.
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

  (* [comment removed for export] *)
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
  Lemma ax1_rl0 : forall mm fb bc j (x1 x10 x12 x14 x22 x23 x24 x25 x28 : word),
    AX1M' mm -> FRM' mm fb -> 0 <= j <= dcap -> 4 <= dcap -> 0 <= bc <= 64 ->
    (forall mm' fb' fl bc' P' (x11 x14' x22' x23' x24' x25' x28' : word),
        AX1M' mm' -> FRM' mm' fb' -> (fl = 0 \/ (fl = 1 /\ bc' <= 7)) -> ALINV' P' bc' ->
        evtF bsegs RNG POST (LST AX1_HD mm' x1 (Z_to_bv 64 P') x11 (Z_to_bv 64 fl) (Z_to_bv 64 bc') x14' j x22' x23' x24' x25' x28')) ->
    evtF bsegs RNG POST (LST AX1_RL mm x1 x10 (Z_to_bv 64 SS) x12 (Z_to_bv 64 bc) x14 j x22 x23 x24 x25 x28).
  Proof using All.
    intros mm fb bc j x1 x10 x12 x14 x22 x23 x24 x25 x28 HM (FB & LFB & FS) HJ HD4 HBC KB.
    pose proof HM as HM0.
    ax1_lfacts. ax1_ldfacts.
    kx_runFm [AX1_HD] 80%nat
        [KZRange bc 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange SPF 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 4 (2^32);
         KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS n; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, n); (SPF, 24)] [(SS, n); (SPF, 40)] [(SS, n)].
    all: ax1_side.
    ax1_rl_post.
    ax1_ez2. ax1_lstfix.
    eapply KB; [ | | ax1_fl | unfold ALINV; lia].
    - unfold AX1M. split; [exists buf; split; assumption |]. repeat (split; [assumption|]); assumption.
    - unfold AX1F. split; [exact FB' | split; [rewrite LFB2; exact LFB | assumption]].
  Qed.

  (* [comment removed for export] *)
  Lemma ax1_rlFa : forall mm fb d q r j (x1 x10 x12 x14 x22 x23 x24 x25 x28 : word),
    AX1M' mm -> FRM' mm fb -> 0 <= j <= dcap -> 4 <= dcap -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    8 <= d -> SS + d + 8 <= SS + n -> d <> q ->
    (forall mm' fb' fl bc' P' (x11 x14' x22' x23' x24' x25' x28' : word),
        AX1M' mm' -> FRM' mm' fb' -> (fl = 0 \/ (fl = 1 /\ bc' <= 7)) -> ALINV' P' bc' ->
        evtF bsegs RNG POST (LST AX1_HD mm' x1 (Z_to_bv 64 P') x11 (Z_to_bv 64 fl) (Z_to_bv 64 bc') x14' j x22' x23' x24' x25' x28')) ->
    evtF bsegs RNG POST (LST AX1_RL mm x1 x10 (Z_to_bv 64 (SS + d)) x12 (Z_to_bv 64 (8 * q + r)) x14 j x22 x23 x24 x25 x28).
  Proof using All.
    intros mm fb d q r j x1 x10 x12 x14 x22 x23 x24 x25 x28 HM (FB & LFB & FS) HJ HD4 HQ HR HBC P1 P2' HC KB.
    pose proof HM as HM0.
    ax1_lfacts. ax1_ldfacts.
    
    kx_runFm [AX1_R2] 20%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange d 8 (2^26); KZRange SPF 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 4 (2^32);
         KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS n; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, n); (SPF, 24)] [(SS, n); (SPF, 40)] [(SS, n)].
    all: ax1_side.
    kx_post_regs. cbn [mem_denot]. ax1_ez2.
    replace ((8 * q + r) mod 2 ^ 32 / 8) with q by (Z.div_mod_to_equations; lia).
    kx_clear.
    kx_runFm [AX1_HD] 60%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange d 8 (2^26); KZRange SPF 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 4 (2^32);
         KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 (SS + d - q) 8; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [((SS + d - q), 8); (SPF, 24)] [((SS + d - q), 8); (SPF, 40)] [((SS + d - q), 8)].
    all: ax1_side.
    ax1_rl_post.
    ax1_ez2. ax1_lstfix.
    eapply KB; [ | | ax1_fl | unfold ALINV; lia].
    - unfold AX1M. split; [exists buf; split; assumption |]. repeat (split; [assumption|]); assumption.
    - unfold AX1F. split; [exact FB' | split; [rewrite LFB2; exact LFB | assumption]].
  Qed.
  Lemma ax1_rlFb : forall mm fb d q r j (x1 x10 x12 x14 x22 x23 x24 x25 x28 : word),
    AX1M' mm -> FRM' mm fb -> 0 <= j <= dcap -> 4 <= dcap -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    8 <= d -> SS + d + 8 <= SS + n -> d = q ->
    (forall mm' fb' fl bc' P' (x11 x14' x22' x23' x24' x25' x28' : word),
        AX1M' mm' -> FRM' mm' fb' -> (fl = 0 \/ (fl = 1 /\ bc' <= 7)) -> ALINV' P' bc' ->
        evtF bsegs RNG POST (LST AX1_HD mm' x1 (Z_to_bv 64 P') x11 (Z_to_bv 64 fl) (Z_to_bv 64 bc') x14' j x22' x23' x24' x25' x28')) ->
    evtF bsegs RNG POST (LST AX1_RL mm x1 x10 (Z_to_bv 64 (SS + d)) x12 (Z_to_bv 64 (8 * q + r)) x14 j x22 x23 x24 x25 x28).
  Proof using All.
    intros mm fb d q r j x1 x10 x12 x14 x22 x23 x24 x25 x28 HM (FB & LFB & FS) HJ HD4 HQ HR HBC P1 P2' HC KB.
    pose proof HM as HM0.
    assert (Q8 : d = 8 /\ q = 8 /\ r = 0) by lia. destruct Q8 as (-> & -> & ->). change (8 * 8 + 0) with 64.
    ax1_lfacts. ax1_ldfacts.
    kx_runFm [AX1_R2] 20%nat
        [ KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange SPF 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 4 (2^32);
         KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS n; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, n); (SPF, 24)] [(SS, n); (SPF, 40)] [(SS, n)].
    all: ax1_side.
    kx_post_regs. cbn [mem_denot]. ax1_ez2.
    kx_clear.
    kx_runFm [AX1_HD] 60%nat
        [ KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange SPF 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 4 (2^32);
         KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS 8; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, 8); (SPF, 24)] [(SS, 8); (SPF, 40)] [(SS, 8)].
    all: ax1_side.
    ax1_rl_post.
    ax1_ez2. ax1_lstfix.
    eapply KB; [ | | ax1_fl | unfold ALINV; lia].
    - unfold AX1M. split; [exists buf; split; assumption |]. repeat (split; [assumption|]); assumption.
    - unfold AX1F. split; [exact FB' | split; [rewrite LFB2; exact LFB | assumption]].
  Qed.

  Lemma ax1_rlS1 : forall mm fb d q r j (x1 x10 x12 x14 x22 x23 x24 x25 x28 : word),
    AX1M' mm -> FRM' mm fb -> 0 <= j <= dcap -> 4 <= dcap -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    1 <= d <= 7 -> SS + d + 8 <= SS + n -> q <= d ->
    (forall mm' fb' fl bc' P' (x11 x14' x22' x23' x24' x25' x28' : word),
        AX1M' mm' -> FRM' mm' fb' -> (fl = 0 \/ (fl = 1 /\ bc' <= 7)) -> ALINV' P' bc' ->
        evtF bsegs RNG POST (LST AX1_HD mm' x1 (Z_to_bv 64 P') x11 (Z_to_bv 64 fl) (Z_to_bv 64 bc') x14' j x22' x23' x24' x25' x28')) ->
    evtF bsegs RNG POST (LST AX1_RL mm x1 x10 (Z_to_bv 64 (SS + d)) x12 (Z_to_bv 64 (8 * q + r)) x14 j x22 x23 x24 x25 x28).
  Proof using All.
    intros mm fb d q r j x1 x10 x12 x14 x22 x23 x24 x25 x28 HM (FB & LFB & FS) HJ HD4 HQ HR HBC P1 P2' HC KB.
    pose proof HM as HM0.
    ax1_lfacts. ax1_ldfacts.
    kx_runFm [AX1_R3] 20%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange d 1 7; KZRange SPF 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 4 (2^32);
         KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS n; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, n); (SPF, 24)] [(SS, n); (SPF, 40)] [(SS, n)].
    all: ax1_side.
    kx_post_regs. cbn [mem_denot]. ax1_ez2.
    replace ((8 * q + r) mod 2 ^ 32 / 8) with q by (Z.div_mod_to_equations; lia).
    kx_clear.
    kx_runFmd [AX1_HD] 60%nat (false :: true :: repeat false 100)
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange d 1 7; KZRange SPF 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 4 (2^32);
         KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 (SS + d - q) 8; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [((SS + d - q), 8); (SPF, 24)] [((SS + d - q), 8); (SPF, 40)] [((SS + d - q), 8)].
    all: ax1_side.
    ax1_rl_post.
    ax1_ez2. ax1_lstfix.
    eapply KB; [ | | ax1_fl | unfold ALINV; lia].
    - unfold AX1M. split; [exists buf; split; assumption |]. repeat (split; [assumption|]); assumption.
    - unfold AX1F. split; [exact FB' | split; [rewrite LFB2; exact LFB | assumption]].
  Qed.
  Lemma ax1_rlS2 : forall mm fb d q r j (x1 x10 x12 x14 x22 x23 x24 x25 x28 : word),
    AX1M' mm -> FRM' mm fb -> 0 <= j <= dcap -> 4 <= dcap -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    1 <= d <= 7 -> SS + d + 8 <= SS + n -> d < q ->
    (forall mm' fb' fl bc' P' (x11 x14' x22' x23' x24' x25' x28' : word),
        AX1M' mm' -> FRM' mm' fb' -> (fl = 0 \/ (fl = 1 /\ bc' <= 7)) -> ALINV' P' bc' ->
        evtF bsegs RNG POST (LST AX1_HD mm' x1 (Z_to_bv 64 P') x11 (Z_to_bv 64 fl) (Z_to_bv 64 bc') x14' j x22' x23' x24' x25' x28')) ->
    evtF bsegs RNG POST (LST AX1_RL mm x1 x10 (Z_to_bv 64 (SS + d)) x12 (Z_to_bv 64 (8 * q + r)) x14 j x22 x23 x24 x25 x28).
  Proof using All.
    intros mm fb d q r j x1 x10 x12 x14 x22 x23 x24 x25 x28 HM (FB & LFB & FS) HJ HD4 HQ HR HBC P1 P2' HC KB.
    pose proof HM as HM0.
    ax1_lfacts. ax1_ldfacts.
    kx_runFm [AX1_R3] 20%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange d 1 7; KZRange SPF 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 4 (2^32);
         KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS n; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, n); (SPF, 24)] [(SS, n); (SPF, 40)] [(SS, n)].
    all: ax1_side.
    kx_post_regs. cbn [mem_denot]. ax1_ez2.
    replace ((8 * q + r) mod 2 ^ 32 / 8) with q by (Z.div_mod_to_equations; lia).
    kx_clear.
    kx_runFmd [AX1_HD] 60%nat (repeat false 100)
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^26); KZRange SS 4096 (2^47);
         KZRange (SS + n) 4096 (2^47); KZRange d 1 7; KZRange SPF 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 4 (2^32);
         KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 8192);
         KZWr SPF 24; KZWord (SPF + 24) 8 SS; KZWord (SPF + 32) 8 (SS + 8);
         KZDisj SPF 24 SS 8; KZDisj SPF 24 (DT + 4) (2 * 2^tl); KZDisj DST dcap SPF 24]
        [(SS, 8); (SPF, 24)] [(SS, 8); (SPF, 40)] [(SS, 8)].
    all: ax1_side.
    ax1_rl_post.
    ax1_ez2. ax1_lstfix.
    eapply KB; [ | | ax1_fl | unfold ALINV; lia].
    - unfold AX1M. split; [exists buf; split; assumption |]. repeat (split; [assumption|]); assumption.
    - unfold AX1F. split; [exact FB' | split; [rewrite LFB2; exact LFB | assumption]].
  Qed.

  Lemma ax1_rl : forall mm fb P bc j (x1 x10 x12 x14 x22 x23 x24 x25 x28 : word),
    AX1M' mm -> FRM' mm fb -> 0 <= j <= dcap -> 4 <= dcap -> ALINV' P bc ->
    (forall mm' fb' fl bc' P' (x11 x14' x22' x23' x24' x25' x28' : word),
        AX1M' mm' -> FRM' mm' fb' -> (fl = 0 \/ (fl = 1 /\ bc' <= 7)) -> ALINV' P' bc' ->
        evtF bsegs RNG POST (LST AX1_HD mm' x1 (Z_to_bv 64 P') x11 (Z_to_bv 64 fl) (Z_to_bv 64 bc') x14' j x22' x23' x24' x25' x28')) ->
    evtF bsegs RNG POST (LST AX1_RL mm x1 x10 (Z_to_bv 64 P) x12 (Z_to_bv 64 bc) x14 j x22 x23 x24 x25 x28).
  Proof using All.
    intros mm fb P bc j x1 x10 x12 x14 x22 x23 x24 x25 x28 HM HF HJ HD4 (HBC & HP) KB.
    destruct HP as [-> | (P1 & P2)]; [exact (ax1_rl0 mm fb bc j x1 x10 x12 x14 x22 x23 x24 x25 x28 HM HF HJ HD4 HBC KB) |].
    pose proof (A1 ax1_sp_bounds) as SB.
    replace P with (SS + (P - SS)) by lia. remember (P - SS) as d eqn:ED.
    assert (QR : bc = 8 * (bc / 8) + bc mod 8 /\ 0 <= bc / 8 <= 8 /\ 0 <= bc mod 8 <= 7) by (Z.div_mod_to_equations; lia).
    destruct QR as (QE & HQ & HR). rewrite QE. remember (bc / 8) as q eqn:EQ. remember (bc mod 8) as r eqn:ER.
    destruct (Z_lt_le_dec d 8) as [D8 | D8].
    - destruct (Z_le_gt_dec q d) as [QD | QD].
      + eapply ax1_rlS1; eauto; lia.
      + eapply ax1_rlS2; eauto; lia.
    - destruct (Z.eq_dec d q) as [QD | QD].
      + eapply ax1_rlFb; eauto; lia.
      + eapply ax1_rlFa; eauto; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ax1_loopF : forall (fuel : nat) mm fb P bc j (x1 x10 x12 x14 x22 x23 x24 x25 x28 : word),
    dcap - j < Z.of_nat fuel -> AX1M' mm -> FRM' mm fb -> ALINV' P bc -> 0 <= j <= dcap -> 4 <= dcap ->
    evtF bsegs RNG POST (LST AX1_RL mm x1 x10 (Z_to_bv 64 P) x12 (Z_to_bv 64 bc) x14 j x22 x23 x24 x25 x28).
  Proof using All.
    induction fuel as [|fuel IH]; intros mm fb P bc j x1 x10 x12 x14 x22 x23 x24 x25 x28 HF0 HM HF HL HJ HD4; [lia|].
    eapply ax1_rl; [exact HM | exact HF | exact HJ | exact HD4 | exact HL |].
    intros mm' fb' fl bc' P' x11 x14' x22' x23' x24' x25' x28' HM' HF' HFL HL'.
    eapply (A1 ax1_body); [exact HM' | exact HF' | exact HJ | exact HD4 | exact HFL | exact HL' |].
    intros HJ4 mm2 fb2 bc2 x10' x12' x14'' x23'' x24'' x25'' x28'' HM2 HF2 HL2.
    eapply IH; [lia | exact HM2 | exact HF2 | exact HL2 | lia | exact HD4].
  Qed.

  (* [comment removed for export] *)
  Lemma ax1_loop : forall mm fb P bc j (x1 x10 x12 x14 x22 x23 x24 x25 x28 : word),
    AX1M' mm -> FRM' mm fb -> ALINV' P bc -> 0 <= j <= dcap -> 4 <= dcap ->
    evtF bsegs RNG POST (LST AX1_RL mm x1 x10 (Z_to_bv 64 P) x12 (Z_to_bv 64 bc) x14 j x22 x23 x24 x25 x28).
  Proof using All.
    intros mm fb P bc j x1 x10 x12 x14 x22 x23 x24 x25 x28 HM HF HL HJ HD4.
    exact (ax1_loopF (S (Z.to_nat (dcap - j))) mm fb P bc j x1 x10 x12 x14 x22 x23 x24 x25 x28 ltac:(lia) HM HF HL HJ HD4).
  Qed.
End AX1D.
End CANSEC1.
