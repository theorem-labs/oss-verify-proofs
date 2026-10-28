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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_ax2 AF_huf_w4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax2f () := "K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6shiftrK47Corelib4Init5Logic3and01C47Corelib4Init5Logic8eq_ind_rI47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedK46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit28sgtz_andC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax24AX2MI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27ax2_unpC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2:ax2_blocksC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2=ax2_sp_boundsC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:length_mapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2f?ax2f_signed_litC45stdpp9bitvector;definitions7bv_wrapK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenK46Stdlib9micromega7EnvRing3Pol01C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega=RingMicromega5Psatz07C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp05C5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2c9ax2_closeC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC56Stdlib5Arith8PeanoNat3Nat3ltbC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2c:ax2_srliw3C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr04c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2f:ax2_land32C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge?zb_shl_shr_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landK4ELinuxProcessSemantics5Riscv5Instr5instr08C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC47Corelib5Lists7ListDef3nthK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K46Stdlib9micromega:ZMicromega;ZArithProof01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5aluop07I46Stdlib5Lists4List6Exists00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop03C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax28ax2_outbC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow?unpoisoned_fullC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=bytes_at_readC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3>le4_four_bytesC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sltC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sltC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le4C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2f?ax2_desc_shiftsc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2f8ax2_elseK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC47Corelib4Init5Logic8iff_reflC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2e:ax2_l4loopC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2d:ax2_l5loopC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2b<ax2_neg_descC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2f<ax2_sgtz_andC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9v_slt_b2zC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leI4ELinuxProcessSemantics5Riscv3Sem4core00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFK47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section AX2F.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr) (SBL SBH : Z).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -64).
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
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
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

  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).

  Notation A2 l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      pdt SBL SBH AH HDT HOUT LOA LOS SPT SP16 TOK ECB LCB MTL TLM DC NSM S16 SBB SBA BYS DJ1 DJ2 DJ3 UDT UDB USB
                      WSK WIM WDT WSB WDTS WSBS WDB WDBS) (only parsing).
  Notation AX2M' mm := (AX2M ra sp s0 s1 s2 s3 s4 s5 m0 DST dcap SS DT lo src cbs mm).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Notation G2 l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs) (only parsing).
  Notation S5ST := (ax2_st sp gp tp s7 s8 s9 s10 s11 FR fc dcap DT).
  Notation S5BD := (ax2_bd sp SS).
  Notation S5F := (AX2F ra sp s0 s1 s2 s3 s4 s5 s6 m0 DST dcap SS DT lo src cbs).
  Notation PINV P := (P = SS \/ (SS + 1 <= P /\ P + 8 <= SS + n)).
  Notation ZB z := (Z_to_bv 64 z).
  Notation PE := (Z_to_bv 64 (DST + dcap)).
  Notation DL := (Z_to_bv 64 (tl + 256 * mtl)).

  Ltac s5ez :=
    try lazymatch goal with
    | |- context [edenot ?E _] =>
        let b := eval unfold E in E in
        lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
          rewrite ?(ez_ok zv E (kE_atoms zv xs));
          let na := eval vm_compute in (length zv) in
          cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
        end
    end.
  Ltac s5br :=
    lazymatch goal with
    | |- branch_taken _ _ _ = _ =>
        s5ez; unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        rewrite ?Z.mod_small by lia;
        first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
              | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
    end.
  Lemma s5_srlw3 : forall E a, 0 <= bv_unsigned (edenot E a) < 2^31 ->
    bv_unsigned (edenot E (EAluw ALU_SRL a (ELit 3))) = bv_unsigned (edenot E a) / 8.
  Proof using.
    intros E a H. clear - H. cbn [edenot].
    rewrite (u_srlw_small (edenot E a) (Z_to_bv 64 3) 3); [reflexivity | reflexivity | lia |].
    change (2 ^ (3 mod 32)) with 8. apply Z.div_lt_upper_bound; lia.
  Qed.
  Lemma s5_srlw_srl : forall E a, 0 <= bv_unsigned (edenot E a) < 2^31 ->
    edenot E (EAlu ALU_SRL a (ELit 3)) = edenot E (EAluw ALU_SRL a (ELit 3)).
  Proof using.
    intros E a H. clear - H. apply bv_eq. rewrite u_srl_lit, (s5_srlw3 E a H). reflexivity.
  Qed.
  Ltac s5w :=
    repeat match goal with
    | |- context [edenot ?E ?e] =>
        match e with context [EAluw ALU_SRL ?a (ELit 3)] =>
          rewrite <- (esubst_sound E (EAluw ALU_SRL a (ELit 3)) (EAlu ALU_SRL a (ELit 3)) e)
            by (apply s5_srlw_srl; s5ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
                change (Z.of_N 64) with 64; rewrite Z.mod_small by lia; lia);
          let e' := eval vm_compute in (esubst (EAluw ALU_SRL a (ELit 3)) (EAlu ALU_SRL a (ELit 3)) e) in
          change (esubst (EAluw ALU_SRL a (ELit 3)) (EAlu ALU_SRL a (ELit 3)) e) with e'
        end
    end.
  Ltac s5ezu := s5ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64 in *;
    change (3 mod 64) with 3 in *; rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8 in *.
  Ltac s5z := cbn [a_base a_off]; s5ezu;
    rewrite ?s5_srlw3 by (s5ezu; rewrite Z.mod_small by lia; lia); s5ezu;
    unfold ASHOFF in *; Z.div_mod_to_equations; lia.
  Ltac s5dj := unfold flat, estart, elenZ; cbn [a_base a_off]; s5ezu; s5z.
  Lemma s5_rd : forall (m : amem) E (a : saddr) A (bs : list byte) k,
    bytes_at bsegs m A bs -> A <= estart E a -> estart E a + Z.of_nat k <= A + Z.of_nat (length bs) ->
    exists r, rdn bsegs m (adenot E a) k = Some r.
  Proof using.
    intros m E a A bs k H H1 H2. clear - H H1 H2.
    set (N := Z.to_nat (estart E a - A)).
    exists (firstn k (skipn N bs)).
    change (adenot E a) with (wa (estart E a)).
    replace (estart E a) with (A + Z.of_nat N) by (unfold N; lia).
    apply bytes_at_rdn; [exact H | unfold N; lia].
  Qed.
  Ltac s5rd H := eapply s5_rd; [exact H | unfold estart; s5z | unfold estart; rewrite ?length_map; s5z].
  Ltac s5zl := Z.div_mod_to_equations; lia.
  Ltac s5zs := rewrite ?Z.shiftr_div_pow2 by lia;
    repeat match goal with |- context [?a mod 64] => rewrite (Z.mod_small a 64) by lia end;
    repeat match goal with |- context [2 ^ ?k] =>
      let v := eval vm_compute in (2 ^ k) in tryif is_Zlit v then change (2 ^ k) with v else fail end.
  Ltac s5dec :=
    repeat match goal with
    | |- context [Z.lxor ?x ?y <? 1] =>
        replace (Z.lxor x y <? 1) with false by
          (symmetry; apply Z.ltb_ge;
           assert (0 <= Z.lxor x y) by (apply (proj2 (Z.lxor_nonneg x y)); split; intro; s5zl);
           assert (Z.lxor x y <> 0) by (rewrite Z.lxor_eq_0_iff; s5zl); lia)
    | |- context [?a =? ?b] =>
        first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; s5zl)
              | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; s5zl) ]
    | |- context [?a <? ?b] =>
        first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; s5zl)
              | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; s5zl) ]
    end.
  Ltac s5ev :=
    unfold branch_taken; cbn [edenot]; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?bv_lts_lxor;
    repeat (progress (rewrite ?u_add64, ?u_sub64, ?u_and64, ?u_xor64, ?u_sltu64, ?u_srl64, ?u_sll64, ?u_mul64, ?u_lit64));
    repeat (lazymatch goal with |- context [ev ?E ?j] =>
      lazymatch goal with KA : forall j, _ -> ev E j = _ |- _ => rewrite (KA j) by (vm_compute; lia) end end);
    cbn [nth]; rewrite ?u_lit64; unfold two64;
    repeat match goal with |- context [?a mod 64] => rewrite (Z.mod_small a 64) by lia end;
    repeat match goal with |- context [?a mod 2 ^ ?k] => rewrite (Z.mod_small a (2 ^ k)) by s5zl end;
    repeat match goal with |- context [2 ^ ?k] =>
      let v := eval vm_compute in (2 ^ k) in tryif is_Zlit v then change (2 ^ k) with v else fail end;
    s5dec; cbn iota; try reflexivity.
  Ltac s5facts mm MU :=
    pose proof (A2 ax2_sp_bounds) as SB; pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB');
    unfold HUF_DEC_STACK_A in LOS; destruct SBB as (SB1 & SB2);
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6);
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR; unfold AIMG_HI, KLS in *; unfold ablk, AIMG_HI, KLS in SBA;
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity);
    pose proof TOK as (TL & _ & _); unfold HUF_TABLELOG_MAX in TL;
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia);
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia);
    unfold DTABLE_BYTES, HufHarness.DT_BYTES in *.
  Ltac s5pre k :=
    unfold ax2_st; let p := eval cbv in (AHUF_DX2_1X + k) in change (AHUF_DX2_1X + k) with p;
    let v := eval vm_compute in (2^61) in change (2^61) with v;
    let v := eval vm_compute in (2^31 - 2^15) in change (2^31 - 2^15) with v.
  Lemma s5_lxor_lt1 : forall x y, 0 <= x -> 0 <= y -> (Z.lxor x y <? 1) = (x =? y).
  Proof using.
    intros x y Hx Hy. clear - Hx Hy. destruct (Z.eqb_spec x y) as [E | E].
    - subst y. rewrite Z.lxor_nilpotent. reflexivity.
    - apply Z.ltb_ge. assert (0 <= Z.lxor x y) by (apply Z.lxor_nonneg; lia).
      assert (Z.lxor x y <> 0) by (rewrite Z.lxor_eq_0_iff; exact E). lia.
  Qed.
  Ltac s5brz :=
    lazymatch goal with |- branch_taken _ _ _ = _ =>
      unfold branch_taken; cbn [edenot]; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?bv_lts_lxor;
      repeat (progress (rewrite ?u_add64, ?u_sub64, ?u_and64, ?u_xor64, ?u_sltu64, ?u_srl64, ?u_sll64, ?u_mul64, ?u_lit64));
      repeat (lazymatch goal with |- context [ev ?E ?j] =>
        lazymatch goal with KA : forall j, _ -> ev E j = _ |- _ => rewrite (KA j) by (vm_compute; lia) end end);
      cbn [nth]; rewrite ?u_lit64; unfold two64;
      let v := eval vm_compute in (2^64) in change (2^64) with v;
      repeat match goal with |- context [?a mod ?m] =>
        tryif is_Zlit a then (let w := eval vm_compute in (a mod m) in change (a mod m) with w) else fail end;
      repeat match goal with |- context [?a mod ?m] =>
        lazymatch a with context [_ mod _] => fail | _ => rewrite (Z.mod_small a m) by lia end end;
      rewrite ?s5_lxor_lt1 by lia;
      repeat match goal with |- context [if (?x =? ?y) then _ else _] => destruct (Z.eqb_spec x y) end;
      repeat match goal with |- context [if (?x <? ?y) then _ else _] => destruct (Z.ltb_spec x y) end;
      cbn iota; first [reflexivity | exfalso; lia]
    end.
  Ltac s5side H :=
    lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- branch_taken _ _ _ = _ => try s5w; first [ s5brz | s5br | w4br | s5ev | idtac ]
    | |- kentry_ok _ _ _ _ => first [ w4word4 | idtac ]
    | |- exists _, rdn _ _ _ _ = Some _ => try s5w; first [ s5rd H | idtac ]
    | |- _ => try s5w; first [ s5dj | idtac ]
    end.

  Definition s5_k3924 : Prop := forall mm bc P cw pad (x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    S5F mm -> S5BD mm cw bc pad P -> 0 <= bc < 2^32 -> (bc <= 64 -> PINV P) ->
    evtF bsegs RNG POST (S5ST 3924 mm x1 x5 x6 x7 (ZB DST) x10 x11 x12 PE DL x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Lemma s5_k3924_ok : G2 ax2_goal_3924 -> s5_k3924.
  Proof using All.
    intros G. unfold s5_k3924. intros mm bc P cw pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 HF HB HBC HP.
    replace (ZB DST) with (ZB (DST + 0)) by (f_equal; lia).
    exact (G mm 0 bc P cw pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 HF HB ltac:(lia) HBC HP).
  Qed.
  Ltac s5fin K P' bc' :=
    lazymatch goal with H : u8arr bsegs ?m DST (map _ ?b), HL : log_flat _ _ |- _ =>
      let buf' := fresh "buf'" in let OUT' := fresh "OUT'" in let LB' := fresh "LB'" in
      destruct (kx_u8arr_ex bsegs _ m _ DST b H HL) as (buf' & OUT' & LB'); clear H end;
    kx_post_mem_free;
    lazymatch goal with |- context [mem_denot ?E ?m ?l] =>
      let mm' := fresh "mm'" in let EM := fresh "EM" in remember (mem_denot E m l) as mm' eqn:EM; clear EM end;
    lazymatch goal with H : rw_cells _ ?m (SP + -88) [C8 ?v] |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      let EV := fresh "EV" in
      assert (EV : v = ZB P') by (s5w; s5ez; f_equal; s5ezu; s5zs; s5zl); try rewrite EV in H; clear EV end;
    lazymatch goal with H : rw_cells _ ?m (SP + -96) [C4 ?v] |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      let EV := fresh "EV" in
      assert (EV : v = ZB bc')
        by first [ s5ez; f_equal; s5ezu; s5zs; s5zl | s5w; s5ez; f_equal; s5ezu; s5zs; s5zl ];
      try rewrite EV in H; clear EV end;
    try replace (dcap + DST) with (DST + dcap) by lia;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      let XF' := fresh "XF'" in
      assert (XF' : S5F m)
        by (unfold AX2F; split; [eexists; split; [eassumption | lia] |];
            repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]);
      eapply (K m bc' P'); [exact XF' | unfold ax2_bd; kx_cells_merge | lia | intros; lia] end.

  Ltac s5pc :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?e) _ _ _ _) => eval cbv in (e - AHUF_DX2_1X) end.
  Ltac s5walk2 :=
    repeat lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let K := fresh "K" in destruct c eqn:K; cbv iota
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
        let o := s5pc in
        let s := eval cbv in (orb (Z.eqb o 276) (orb (Z.eqb o 2272) (orb (Z.eqb o 3924) (orb (Z.leb 5300 o) (Z.ltb o 200))))) in
        lazymatch s with true => fail | false => zstep end
    end.
  Lemma s5_sx32 : forall z, 0 <= z < 2^31 -> Mem.sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
  Proof using.
    intros z Hz. clear - Hz. unfold Mem.sx32. rewrite Z_to_bv_unsigned. f_equal.
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
    Z.div_mod_to_equations; lia.
  Qed.
  Lemma s5_neg_desc : forall tl mtl, 1 <= tl <= 12 -> 0 <= mtl <= 255 ->
    Z.land (Z.land (bv_swrap 32 (0 - (tl + 256 * mtl))) (2^64 - 1)) 63 = 64 - tl.
  Proof using.
    intros t m Ht Hm. clear - Ht Hm.
    assert (E : bv_swrap 32 (0 - (t + 256 * m)) = - (t + 256 * m)).
    { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. Z.div_mod_to_equations; lia. }
    rewrite E. change 63 with (2^6 - 1). rewrite !zb_land_mask by lia.
    Z.div_mod_to_equations; lia.
  Qed.
  Ltac s5r200 LO X5 SX :=
    let v := eval vm_compute in (2^64 - 1) in change v with (2^64 - 1);
    rewrite ?SX; rewrite ?(LO (DT + 4)) by lia; rewrite ?X5; rewrite ?(LO (tl + 256 * mtl)) by lia;
    rewrite ?s5_neg_desc by lia;
    repeat match goal with |- context [?a <? ?b] =>
      first [ replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)
            | replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) ] end;
    try replace (DST + dcap + -9) with (DST + dcap - 9) by lia;
    try replace (DST + dcap + -7) with (DST + dcap - 7) by lia;
    replace (ZB DST) with (ZB (DST + 0)) by (f_equal; lia);
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?a30 ?a31) _ _ _ _ _ _) =>
      first [ replace a31 with (ZB AX2_K8) by (vm_compute; reflexivity)
            | replace a30 with (ZB AX2_K8) by (vm_compute; reflexivity) | idtac ] end.
  Ltac s5bad SX :=
    exfalso; match goal with K : negb (bv_ltu (Mem.sx32 (ZB ?b)) (ZB 65)) = true |- _ =>
      rewrite SX, bv_ltu_Z, !Z_to_bv_unsigned in K; unfold bv_wrap, bv_modulus in K; cbn [Z.of_N] in K;
      rewrite !Z.mod_small in K by lia; apply Bool.negb_true_iff, Z.ltb_ge in K; lia end.
  Lemma s5_sm_a : forall mm q r off cont pad (x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    s5_k3924 -> S5F mm -> S5BD mm cont (8 * q + r) pad (SS + off) -> 0 <= q <= 8 -> 0 <= r <= 7 -> 1 <= 8 * q + r <= 64 ->
    8 <= off -> off + 8 <= n -> 0 <= dcap < 8 ->
    evtF bsegs RNG POST (S5ST 2052 mm x1 x5 x6 x7 (ZB DST) x10 x11 x12 PE DL x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Proof using All.
    intros mm q r off cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 K HF HB HQ HR HBC HP1 HP2 HDC.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    s5facts mm MU. clear BYS TOK ECB AH HDT HOUT.
    unfold ax2_bd in HB. kx_cells_split HB.
    s5pre 2052.
    let s1 := eval cbv in (AHUF_DX2_1X + 3924) in
    kx_runFm [s1] 120%nat
      [KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n 1 (2^26); KZRange off 8 (2^26);
       KZRange (n - off) 8 (2^26); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64;
       KZWord (SP + -96) 4 (8 * q + r); KZWord (SP + -88) 8 (SS + off); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZWr (SP + -104) 8; KZWr (SP + -96) 4; KZWr (SP + -88) 8; KZDisj (SP + -104) 40 SS n; KZRange dcap 0 7]
      [(SS, n)] [(SS, n); (SP + -112, 112)] [(SS, n)].
    all: try (s5side SRCB).
    all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "SIDE" g end.
    kx_post_regs. kx_cells_post. kx_frame FRC. kx_frame SRCB. kx_frame CBS. kx_munch MU.
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
    s5fin K (SS + off - q) r.
  Time Qed.

  Lemma s5_sm_b : forall mm bc cont pad (x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    s5_k3924 -> S5F mm -> S5BD mm cont bc pad SS -> 1 <= bc <= 64 -> 0 <= dcap < 8 ->
    evtF bsegs RNG POST (S5ST 2052 mm x1 x5 x6 x7 (ZB DST) x10 x11 x12 PE DL x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Proof using All.
    intros mm bc cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 K HF HB HBC HDC.
    pose proof (K mm bc SS cont pad) as K0. clear K.
    pose proof HF as HF0. pose proof HB as HB0.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    s5facts mm MU. clear BYS TOK ECB AH HDT HOUT.
    unfold ax2_bd in HB. kx_cells_split HB.
    s5pre 2052.
    let s1 := eval cbv in (AHUF_DX2_1X + 3924) in
    kx_runFm [s1] 60%nat
      [KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n 1 (2^26); KZRange bc 1 64;
       KZWord (SP + -96) 4 bc; KZWord (SP + -88) 8 SS; KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZDisj (SP + -104) 40 SS n; KZRange dcap 0 7]
      [(SS, n)] [(SS, n); (SP + -112, 112)] [(SS, n)].
    all: try (s5side SRCB).
    all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "SIDE" g end.
    kx_post_regs.
    lazymatch goal with |- context [mem_denot ?E mm []] => change (mem_denot E mm []) with mm end.
    try replace (dcap + DST) with (DST + dcap) by lia.
    eapply K0; [exact HF0 | exact HB0 | lia | intros; left; reflexivity].
  Time Qed.

  Lemma s5_sval0 : forall b : byte, sval b = 0 -> b = Z_to_bv 8 0.
  Proof using.
    intros b H. clear - H. apply bv_eq. rewrite Z_to_bv_unsigned.
    pose proof (bv_unsigned_in_range 8 b) as R.
    unfold sval, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. cbn [Z.of_N] in *.
    change (2 ^ 8) with 256 in *. change (256 / 2) with 128 in *. Z.div_mod_to_equations. lia.
  Qed.
  Lemma s5_kshz : forall (m : amem) A b, m (wa (shad A)) = Some b -> sval b = 0 -> kshz_fact m ASHOFF A 1.
  Proof using.
    intros m A b H1 H2 x Hx. clear - H1 H2 Hx. assert (x = A) by lia. subst x.
    rewrite (s5_sval0 b H2) in H1. exact H1.
  Qed.
  Lemma s5_kshz8 : forall (m : amem) A b, m (wa (shad (8 * (A / 8)))) = Some b -> sval b = 0 -> kshz_fact m ASHOFF A 1.
  Proof using.
    intros m A b H1 H2 x Hx. clear - H1 H2 Hx. assert (x = A) by lia. subst x.
    rewrite (s5_sval0 b H2) in H1. unfold wa, shad in H1.
    rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *.
    rewrite (Z.mul_comm 8), Z.div_mul in H1 by lia. exact H1.
  Qed.
  Lemma s5_shrd : forall (m : amem) E (a : saddr) A b, m (wa (shad A)) = Some b -> estart E a = shad A ->
    rdval bsegs m (adenot E a) 1 true = Z_to_bv 64 (sval b).
  Proof using.
    intros m E a A b H1 H2. clear - H1 H2. rewrite adenot_wa, H2. unfold rdval. cbn [rdn]. rewrite H1.
    cbv iota beta. unfold extz, sval, bv_signed. cbv iota. do 2 f_equal.
    rewrite bytes_le_to_Z_le_val. cbn. lia.
  Qed.
  Ltac s5shc mm USB A :=
    let HA := fresh "HA" in
    let b := fresh "b" in let MB := fresh "MB" in let B0 := fresh "B0" in let B1 := fresh "B1" in
    assert (HA : SBL + 7 <= A /\ A + 1 <= SBH) by lia;
    destruct (unp_gran mm SBL SBH A 1 USB ltac:(lia) (proj2 HA) ltac:(lia)) as (b & MB & [B0 | B1]);
    [ pose proof (s5_kshz mm A b MB B0) as KS; clear B0;
      assert (RS : rng RNG (ASHOFF + Z.shiftr A 3) (Z.shiftr (1 + A mod 8 + 7) 3))
        by (apply (rng_sub RNG _ _ _ _ WSBS); clear - HA SBA; unfold shad, shlen;
            rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia);
      let o := eval vm_compute in ASHOFF in
      pose proof KS as KS'; pose proof RS as RS'; change ASHOFF with o in KS', RS'
    | assert (SV : 1 <= sval b <= 7 /\ A mod 8 < sval b) by (clear - B1; lia); clear B1;
      let b0 := fresh "b0" in let MB0 := fresh "MB0" in let C0 := fresh "C0" in let C1 := fresh "C1" in
      assert (HA0 : SBL <= 8 * ((A - 7) / 8) /\ 8 * ((A - 7) / 8) + 8 <= SBH)
        by (clear - HA SV SBA; destruct SBA as (_ & SA8); Z.div_mod_to_equations; lia);
      destruct (unp_gran mm SBL SBH (8 * ((A - 7) / 8)) 8 USB (proj1 HA0) (proj2 HA0) ltac:(lia)) as (b0 & MB0 & [C0 | C1]);
      [ pose proof (s5_kshz8 mm (A - 7) b0 MB0 C0) as KS; clear C0;
        assert (RS : rng RNG (ASHOFF + Z.shiftr (A - 7) 3) (Z.shiftr (1 + (A - 7) mod 8 + 7) 3))
          by (apply (rng_sub RNG _ _ _ _ WSBS); clear - HA SBA; unfold shad, shlen;
              rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia);
        let o := eval vm_compute in ASHOFF in
        pose proof KS as KS'; pose proof RS as RS'; change ASHOFF with o in KS', RS'
      | exfalso; clear - C1; Z.div_mod_to_equations; lia ] ].
  Ltac s5shbr :=
    s5ez; unfold branch_taken; try unfold bv_lts;
    rewrite ?bv_eqb_Z, ?zb_signed, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
    rewrite ?(u_and_mask _ _ 7 3) by first [lia | reflexivity]; s5ezu;
    repeat match goal with |- context [Z.land ?x 7] =>
      replace (Z.land x 7) with (x mod 8) by (change 7 with (2^3 - 1); rewrite zb_land_mask by lia; reflexivity) end;
    lazymatch goal with SV : 1 <= sval _ <= 7 /\ _ |- _ => clear - SV end;
    rewrite ?Z.mod_small by lia;
    repeat match goal with |- context [if (?x <? ?y)%Z then _ else _] => destruct (Z.ltb_spec x y) end;
    cbv iota;
    repeat match goal with |- context [(?x <? ?y)%Z] => destruct (Z.ltb_spec x y) end;
    repeat match goal with |- context [(?x =? ?y)%Z] => destruct (Z.eqb_spec x y) end;
    cbn [negb]; first [reflexivity | exfalso; Z.div_mod_to_equations; lia].
  Ltac s5shside mm MB :=
    lazymatch goal with |- branch_taken _ _ _ = _ =>
      match goal with |- context [edenot ?E (EVar ?j)] =>
        let H := fresh "H" in kx_read_eq j H; change (edenot E (EVar j)) with (ev E j); rewrite H; clear H;
        rewrite (s5_shrd mm E _ _ _ MB)
          by (unfold estart, shad; cbn [a_base a_off]; s5ezu; unfold ASHOFF in *; Z.div_mod_to_equations; lia)
      end;
      s5shbr
    end.
  Ltac s5r0 kz A SB :=
    let s1 := eval cbv in (AHUF_DX2_1X + 3924) in
    let kz' := eval cbv [app] in (kz ++ [KZShZ ASHOFF A 1]) in
    kx_runFL [s1] 120%nat kz' [(SS, n)] [(SS, n); (SP + -112, 112)] [(SS, n)];
    try (s5side SB).
  Ltac s5r1 kz A SB mm MB :=
    let s1 := eval cbv in (AHUF_DX2_1X + 3924) in
    let S := constr:([s1] : list Z) in
    let kz' := eval cbv [app] in (kz ++ [KZShZ ASHOFF (A - 7) 1]) in
    let R := constr:([(SS, n)] : list (Z * Z)) in
    let W := constr:([(SS, n); (SP + -112, 112)] : list (Z * Z)) in
    let D := eval vm_compute in ([false; false; false; true] ++ repeat false 4092) in
    kx_prepFm S 120%nat kz' R W R; kx_goFL D;
    try (s5shside mm MB); try (s5side SB).
  Ltac s5kzc off q r :=
    constr:([KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n 9 (2^26); KZRange off 1 7;
       KZRange (n - off) 8 (2^26); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange (off - q) 1 7;
       KZWord (SP + -96) 4 (8 * q + r); KZWord (SP + -88) 8 (SS + off); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZWr (SP + -104) 8; KZWr (SP + -96) 4; KZWr (SP + -88) 8; KZDisj (SP + -104) 40 SS n; KZRange dcap 0 7]).
  Ltac s5kzd off q r :=
    constr:([KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n 9 (2^26); KZRange off 1 7;
       KZRange (n - off) 8 (2^26); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange (q - off) 1 8;
       KZWord (SP + -96) 4 (8 * q + r); KZWord (SP + -88) 8 (SS + off); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZWr (SP + -104) 8; KZWr (SP + -96) 4; KZWr (SP + -88) 8; KZDisj (SP + -104) 40 SS n; KZRange dcap 0 7]).
  Ltac s5kze off r :=
    constr:([KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n 9 (2^26); KZRange off 1 7;
       KZRange (n - off) 8 (2^26); KZRange r 0 7; KZRange (8 * off + r) 8 63;
       KZWord (SP + -96) 4 (8 * off + r); KZWord (SP + -88) 8 (SS + off); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZWr (SP + -104) 8; KZWr (SP + -96) 4; KZWr (SP + -88) 8; KZDisj (SP + -104) 40 SS n; KZRange dcap 0 7]).

  Lemma s5_sm_c : forall mm q r off cont pad (x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    s5_k3924 -> S5F mm -> S5BD mm cont (8 * q + r) pad (SS + off) -> 0 <= q <= 8 -> 0 <= r <= 7 -> 1 <= 8 * q + r <= 64 ->
    1 <= off <= 7 -> q < off -> off + 8 <= n -> 0 <= dcap < 8 ->
    evtF bsegs RNG POST (S5ST 2052 mm x1 x5 x6 x7 (ZB DST) x10 x11 x12 PE DL x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Proof using All.
    intros mm q r off cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 K HF HB HQ HR HBC HP1 HQO HP2 HDC.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    s5facts mm MU. clear BYS TOK ECB AH HDT HOUT.
    unfold ax2_bd in HB. kx_cells_split HB.
    s5pre 2052.
    s5shc mm USB' (SS + off - q + 7).
    - let kz := s5kzc off q r in s5r0 kz (SS + off - q + 7) SRCB.
      kx_post_regs. kx_cells_post. kx_frame FRC. kx_frame SRCB. kx_frame CBS. kx_munch MU.
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
      s5fin K (SS + off - q) r.
    - let kz := s5kzc off q r in s5r1 kz (SS + off - q + 7) SRCB mm MB.
      kx_post_regs. kx_cells_post. kx_frame FRC. kx_frame SRCB. kx_frame CBS. kx_munch MU.
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
      s5fin K (SS + off - q) r.
  Time Qed.

  Lemma s5_sm_e : forall mm q r off cont pad (x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    s5_k3924 -> S5F mm -> S5BD mm cont (8 * q + r) pad (SS + off) -> 0 <= r <= 7 ->
    1 <= off <= 7 -> q = off -> off + 8 <= n -> 0 <= dcap < 8 ->
    evtF bsegs RNG POST (S5ST 2052 mm x1 x5 x6 x7 (ZB DST) x10 x11 x12 PE DL x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Proof using All.
    intros mm q r off cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 K HF HB HR HP1 HQO HP2 HDC.
    subst q.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    s5facts mm MU. clear BYS TOK ECB AH HDT HOUT.
    unfold ax2_bd in HB. kx_cells_split HB.
    s5pre 2052.
    s5shc mm USB' (SS + 7).
    - let kz := s5kze off r in s5r0 kz (SS + 7) SRCB.
      kx_post_regs. kx_cells_post. kx_frame FRC. kx_frame SRCB. kx_frame CBS. kx_munch MU.
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
      s5fin K SS r.
    - let kz := s5kze off r in s5r1 kz (SS + 7) SRCB mm MB.
      kx_post_regs. kx_cells_post. kx_frame FRC. kx_frame SRCB. kx_frame CBS. kx_munch MU.
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
      s5fin K SS r.
  Time Qed.

  Lemma s5_sm_d : forall mm q r off cont pad (x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    s5_k3924 -> S5F mm -> S5BD mm cont (8 * q + r) pad (SS + off) -> 0 <= q <= 8 -> 0 <= r <= 7 -> 1 <= 8 * q + r <= 64 ->
    1 <= off <= 7 -> off < q -> off + 8 <= n -> 0 <= dcap < 8 ->
    evtF bsegs RNG POST (S5ST 2052 mm x1 x5 x6 x7 (ZB DST) x10 x11 x12 PE DL x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Proof using All.
    intros mm q r off cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 K HF HB HQ HR HBC HP1 HQO HP2 HDC.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    s5facts mm MU. clear BYS TOK ECB AH HDT HOUT.
    unfold ax2_bd in HB. kx_cells_split HB.
    s5pre 2052.
    s5shc mm USB' (SS + 7).
    - let kz := s5kzd off q r in s5r0 kz (SS + 7) SRCB.
      kx_post_regs. kx_cells_post. kx_frame FRC. kx_frame SRCB. kx_frame CBS. kx_munch MU.
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
      s5fin K SS (8 * q + r - 8 * off).
    - let kz := s5kzd off q r in s5r1 kz (SS + 7) SRCB mm MB.
      kx_post_regs. kx_cells_post. kx_frame FRC. kx_frame SRCB. kx_frame CBS. kx_munch MU.
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
      s5fin K SS (8 * q + r - 8 * off).
  Time Qed.

  Lemma ax2_goal_2052_ok : G2 ax2_goal_3924 -> G2 ax2_goal_2052.
  Proof using All.
    intros G. pose proof (s5_k3924_ok G) as K. clear G. unfold ax2_goal_2052.
    intros mm bc P cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 HF HB HBC HP HDC.
    assert (HDC' : 0 <= dcap < 8) by lia.
    destruct HP as [HP | (HP1 & HP2)].
    - subst P. exact (s5_sm_b mm bc cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 K HF HB HBC HDC').
    - pose proof (Z.div_mod bc 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound bc 8 ltac:(lia)) as MB.
      assert (HQ : 0 <= bc / 8 <= 8) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
      replace bc with (8 * (bc / 8) + bc mod 8) in HB by lia.
      replace P with (SS + (P - SS)) in HB by lia.
      destruct (Z_le_gt_dec 8 (P - SS)) as [HO | HO].
      + exact (s5_sm_a mm (bc / 8) (bc mod 8) (P - SS) cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31
                 K HF HB HQ ltac:(lia) ltac:(lia) HO ltac:(lia) HDC').
      + destruct (Z_le_gt_dec (bc / 8) (P - SS)) as [HQO | HQO].
        * destruct (Z.eq_dec (bc / 8) (P - SS)) as [HE | HE].
          -- exact (s5_sm_e mm (bc / 8) (bc mod 8) (P - SS) cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31
                      K HF HB ltac:(lia) ltac:(lia) HE ltac:(lia) HDC').
          -- exact (s5_sm_c mm (bc / 8) (bc mod 8) (P - SS) cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31
                      K HF HB HQ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HDC').
        * exact (s5_sm_d mm (bc / 8) (bc mod 8) (P - SS) cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31
                   K HF HB HQ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HDC').
  Time Qed.

  Lemma ax2_goal_200_ok : G2 ax2_goal_276 -> G2 ax2_goal_2272 -> G2 ax2_goal_3924 -> G2 ax2_goal_200.
  Proof using All.
    intros G76 G72 _. unfold ax2_goal_200.
    intros mm bc P b01 cont pad x1 x5 x6 x7 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 XM BM HB HP HD HB01.
    pose proof XM as XM0. destruct XM as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof BM as BM0. unfold ax2_bd in BM.
    s5facts mm MU. destruct (B6 ltac:(lia)) as (D1 & D2 & D3 & D4).
    assert (SX : Mem.sx32 (ZB bc) = ZB bc) by (apply s5_sx32; lia).
    assert (LO : forall y, 0 <= y < 2^64 -> Z.land y (2^64 - 1) = y)
      by (intros y Hy; rewrite zb_land_mask by lia; apply Z.mod_small; lia).
    assert (X5 : ZB (Z.lxor (DT + 4) (2^64 - 1)) = ZB (- DT - 5)).
    { rewrite lxor_ones64 by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      rewrite <- (Z.mod_add (- DT - 5) 1 (2^64)) by lia. f_equal. lia. }
    unfold ax2_st.
    s5walk2.
    all: try kx_mkR_foldF.
    all: try (let o := s5pc in lazymatch o with 276 => fail | 2272 => fail | _ => s5bad SX end).
    all: try (s5r200 LO X5 SX).
    all: let o := s5pc in lazymatch o with
      | 276 => eapply (G76 mm 0 bc P cont cont pad); [exact XM0 | exact BM0 | lia | lia | lia | exact HP]
      | 2272 => eapply (G72 mm 0 bc P cont cont pad); [exact XM0 | exact BM0 | lia | lia | lia | exact HP] end.
  Time Qed.

End AX2F.
End CANSEC1.
