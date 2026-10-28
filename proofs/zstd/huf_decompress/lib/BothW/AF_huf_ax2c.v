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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_ax2 AF_huf_ax2b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax2c () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS=swrap32_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax24AX2MC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t03C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2b8ax2_lastC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2:ax2_blocksC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax28ax2_outbI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2=ax2_sp_boundsC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC47Corelib4Init5Logic6eq_indC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2b7ax2_nrlC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2c<ax2_nrl_exitC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z8inj_succC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2c8ax2_nrl0I47Corelib4Init5Logic2ex00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27ax2_unpC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27ax2_tabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk08K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp05K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk09K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03C5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond03K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06C5ARocqVerifyHarness?AgentSubmission6Common5KXTac9idx_factsC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zle_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac<idx_facts_okC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC5ARocqVerifyHarness?AgentSubmission6Common4KXGo5zt_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr04K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC5ARocqVerifyHarness?AgentSubmission6Common5KXMem;kx_u8arr_exC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula02C56Stdlib5Arith8PeanoNat3Nat3ltbC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:kx_stk_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC57Corelib7BinNums6PosDef3Pos;of_succ_natK47Corelib4Init5Logic2ex01C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202C46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI46Stdlib5Lists4List6Exists00K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC56Stdlib6ZArith6BinInt1Z3oppC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2c9ax2_nrl0sC5ARocqVerifyHarness?AgentSubmission6Common6KXPost9kx_mul_m1C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega7EnvRing5PExpr06K47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2c9ax2_r2decC5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2c8ax2_r2rlc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2c:ax2_srliw3C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z4lxorK4ELinuxProcessSemantics5Riscv5Instr5aluop06c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2c:ax2_r2headC47Corelib4Init9Datatypes7nat_indK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C46Stdlib5Lists4List2InK4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2c:ax2_r2loopC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2b<ax2_neg_descI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section AX2C.
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


  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Notation HEAD2 pc mm k pt bits t2 a1 a4 a5 x18 x19 x20 x21 t5 xra :=
    (MS (mkR xra (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap)) t2 (Z_to_bv 64 64)
             (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 (DST + k)) a1 (Z_to_bv 64 SS) (Z_to_bv 64 (SS + pt)) a4 a5 (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 2147450880) x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 bits) t5
             (Z_to_bv 64 (64 - tl)))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)


  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Notation PINV P := (P = SS \/ (SS + 1 <= P /\ P + 8 <= SS + n)).
  Notation ZB z := (Z_to_bv 64 z).
  Notation PE := (ZB (DST + dcap)).
  Notation DL := (ZB (tl + 256 * mtl)).
  Notation XF := (AX2F ra sp s0 s1 s2 s3 s4 s5 s6 m0 DST dcap SS DT lo src cbs).
  Notation BD := (ax2_bd sp SS).
  Notation ST := (ax2_st sp gp tp s7 s8 s9 s10 s11 FR fc dcap DT).
  Notation L2 k mm x1 j x10 x11 x12 x18 x20 x21 x22 x30 x31 :=
    (ST k mm x1 (ZB (- DT - 5)) (ZB (64 - tl)) (ZB 65) (ZB (DST + j)) x10 x11 x12 PE DL (ZB (DST + dcap - 2))
        x18 x20 x21 x22 (ZB AX2_K8) (ZB 3) x30 x31).
  Notation G4772 := (ax2_goal_4772 AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs).
  Notation G4768 := (ax2_goal_4768 AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs).
  Notation G3976 := (ax2_goal_3976 AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs).
  Notation G3924 := (ax2_goal_3924 AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs).

  Ltac ax2_l2rl_ez :=
    repeat lazymatch goal with
    | |- context [edenot ?E _] =>
        let b := eval unfold E in E in
        lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
          rewrite ?(ez_ok zv E (kE_atoms zv xs));
          let na := eval vm_compute in (length zv) in
          cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
        end
    end.

  Lemma ax2_l2rl_rd1 : forall m A bs a, bytes_at bsegs m A bs -> A <= a -> a + 1 <= A + zlen bs ->
    exists b, rdn bsegs m (wa a) 1 = Some b.
  Proof.
    intros m A bs a HB H1 H2.
    pose proof (bytes_at_rdn bsegs m A bs (Z.to_nat (a - A)) 1 HB ltac:(lia)) as R.
    rewrite Z2Nat.id in R by lia. replace (A + (a - A)) with a in R by lia. eexists; exact R.
  Time Qed.

  Ltac ax2_l2rl_br CL :=
    lazymatch goal with
    | KXA : forall j, (j < length _)%nat -> ev ?E j = _ |- branch_taken _ (edenot ?E _) _ = _ =>
        cbn [edenot]; unfold branch_taken; rewrite ?bv_eqb_Z, ?bv_ltu_Z;
        repeat (rewrite u_xor64 || rewrite u_sltu64 || rewrite u_add64 || rewrite u_sub64);
        repeat match goal with |- context [ev E ?jj] => rewrite (KXA jj) by (cbn [length]; lia) end;
        cbn [nth]; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64%N) with 64;
        repeat match goal with |- context [?y mod 2 ^ 64] => rewrite (Z.mod_small y (2 ^ 64)) by CL end;
        repeat match goal with |- context [(Z.lxor ?a ?b <? 1)%Z] =>
          let H1 := fresh "HL1" in let H2 := fresh "HL2" in
          assert (H1 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; split; intros _; CL);
          assert (H2 : Z.lxor a b <> 0) by (rewrite zb_lxor_eq0; CL);
          replace (Z.lxor a b <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia) end;
        reflexivity
    end.

  Ltac ax2_l2rl_chk U CL CLD :=
    lazymatch goal with
    | |- branch_taken BC_LT (edenot ?E (EAlu ALU_SUB (EMd M_MUL (EAlu ALU_SLTU (ELit 0) ?X)
            (EAlu ALU_ADD (EAlu ALU_ADD (EAlu ALU_AND ?B (ELit 7)) (ELit ?k)) (ELit 1))) (ELit 1))) (edenot ?E ?X) = true =>
        change (EAlu ALU_SUB (EMd M_MUL (EAlu ALU_SLTU (ELit 0) X)
            (EAlu ALU_ADD (EAlu ALU_ADD (EAlu ALU_AND B (ELit 7)) (ELit k)) (ELit 1))) (ELit 1)) with (chk_ob X B k);
        let x := fresh "x" in let HX := fresh "HX" in
        remember (bv_unsigned (edenot E B)) as x eqn:HX;
        eapply (chk_ob_unp bsegs _ E X B k _ _ x U);
        [ rewrite HX; symmetry; apply Z_to_bv_bv_unsigned
        | rewrite HX; let RG := fresh "RG" in pose proof (bv_unsigned_in_range 64 (edenot E B)) as RG;
          unfold bv_modulus in RG; change (2 ^ Z.of_N 64) with (2 ^ 64) in RG; clear - RG; lia
        | rewrite HX; ax2_l2rl_ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64%N) with 64;
          repeat match goal with |- context [?y mod 2 ^ 64] => rewrite (Z.mod_small y (2 ^ 64)) by CL end; CL
        | rewrite HX; ax2_l2rl_ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64%N) with 64;
          repeat match goal with |- context [?y mod 2 ^ 64] => rewrite (Z.mod_small y (2 ^ 64)) by CL end; CL
        | lia
        | let jj := lazymatch goal with |- edenot _ (EVar ?jj) = _ => jj end in
          let HR := fresh "HR" in kx_read_eq jj HR; cbn [edenot]; rewrite HR; clear HR;
          f_equal; rewrite adenot_wa; f_equal; unfold estart; cbn [a_base a_off]; rewrite HX; ax2_l2rl_ez;
          rewrite ?Z_to_bv_unsigned; unfold shad, ASHOFF, bv_wrap, bv_modulus; change (Z.of_N 64%N) with 64;
          rewrite ?Z.shiftr_div_pow2 by lia; change (3 mod 64) with 3 in *; change (2 ^ 3) with 8 in *;
          repeat match goal with |- context [?y mod 2 ^ 64] => rewrite (Z.mod_small y (2 ^ 64)) by CLD end;
          CLD ]
    end.

  Ltac ax2_l2rl_sdw U mm CL CLD :=
    lazymatch goal with
    | |- exists _, rdn _ _ (adenot ?E {| a_base := EAlu ALU_ADD _ (EAlu ALU_ADD _ (EAlu ALU_SRL ?B (ELit 3))); a_off := 0 |}) 1 = Some _ =>
        let x := fresh "x" in let HX := fresh "HX" in
        remember (bv_unsigned (edenot E B)) as x eqn:HX;
        let b := fresh "b" in let HBb := fresh "HBb" in
        destruct (unp_gran mm _ _ x 1 U
                    ltac:(rewrite HX; ax2_l2rl_ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
                          change (Z.of_N 64%N) with 64;
                          repeat match goal with |- context [?y mod 2 ^ 64] => rewrite (Z.mod_small y (2 ^ 64)) by CL end; CL)
                    ltac:(rewrite HX; ax2_l2rl_ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
                          change (Z.of_N 64%N) with 64;
                          repeat match goal with |- context [?y mod 2 ^ 64] => rewrite (Z.mod_small y (2 ^ 64)) by CL end; CL)
                    ltac:(lia)) as (b & HBb & _);
        exists [b]; rewrite <- (rdn1_some bsegs mm _ b HBb);
        f_equal; rewrite adenot_wa; f_equal; unfold estart; cbn [a_base a_off]; rewrite HX; ax2_l2rl_ez;
        rewrite ?Z_to_bv_unsigned; unfold shad, ASHOFF, bv_wrap, bv_modulus; change (Z.of_N 64%N) with 64;
        rewrite ?Z.shiftr_div_pow2 by lia; change (3 mod 64) with 3 in *; change (2 ^ 3) with 8 in *;
        repeat match goal with |- context [?y mod 2 ^ 64] => rewrite (Z.mod_small y (2 ^ 64)) by CLD end;
        CLD
    end.

  Ltac ax2_l2rl_pre mm XM BM KB :=
    let XM0 := fresh "XM0" in pose proof XM as XM0;
    destruct XM as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM);
    unfold ax2_bd in BM; unfold ax2_st; unfold ax2_st in KB;
    pose proof (A2 ax2_sp_bounds) as SB; unfold HUF_DEC_STACK_A in LOS;
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6);
    lazymatch goal with HMU : munch _ m0 mm |- _ => pose proof (A2 ax2_unp' mm HMU) as (UDT' & UDB' & USB') end;
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR; unfold AIMG_HI, KLS in *;
    destruct SBA as (SBK & SB8); pose proof (A2 ax2_outb) as OB;
    assert (DSR : 4096 <= DST /\ DST + dcap <= 2^47) by lia; clear OB;
    assert (LSM : zlen (map (Z_to_bv 8) src) = n) by (rewrite length_map; reflexivity);
    assert (SNS : SS + n + 4096 <= SP + -112) by lia;
    let p := eval cbv in (AHUF_DX2_1X + 3976) in change (AHUF_DX2_1X + 3976) with p;
    let p := eval cbv in (AHUF_DX2_1X + 4428) in change (AHUF_DX2_1X + 4428) with p in KB.

  Lemma ax2_l2rl_far : forall mm j bc P cw pad (x1 x10 x11 x12 x18 x20 x21 x22 x31 : word),
    XF mm -> BD mm cw bc pad P -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= bc <= 64 -> PINV P -> SS + 8 <= P ->
    (forall mm' fl bc' P' cw' pad' (x11' x12' x18' x20' x21' x22' x30' x31' : word),
       XF mm' -> BD mm' cw' bc' pad' P' -> (fl = 0 \/ (fl = 1 /\ bc' <= 7)) -> 0 <= bc' <= 64 -> PINV P' ->
       evtF bsegs RNG POST (L2 4428 mm' x1 j (ZB fl) x11' x12' x18' x20' x21' x22' x30' x31')) ->
    evtF bsegs RNG POST (L2 3976 mm x1 j x10 x11 x12 x18 x20 x21 x22 (ZB bc) x31).
  Proof using All.
    intros mm j bc P cw pad x1 x10 x11 x12 x18 x20 x21 x22 x31 XM BM HD HJ HB HP HF KB.
    destruct HP as [HP | (HP1 & HP2)]; [lia |].
    assert (OF : exists off, P = SS + off) by (exists (P - SS); lia).
    destruct OF as (off & ->).
    ax2_l2rl_pre mm XM BM KB.
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= r <= 7 /\ 0 <= q <= 8)
      by (exists (bc / 8), (bc mod 8); Z.div_mod_to_equations; lia).
    destruct QR as (q & r & -> & RR & QQ).
    kx_runFm [AHUF_DX2_1X + 4428] 120%nat
      [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
       KZRange off 8 (2^26); KZRange (off - q) 0 (2^26); KZRange (n - off) 8 (2^26); KZRange n 9 (2^26);
       KZRange (n - (off - q)) 8 (2^26); KZRange (SS + (off - q)) 16 (2^47);
       KZWr (SP + -104) 40; KZDisj (SP + -104) 40 SS n;
       KZWord (SP + -88) 8 (SS + off); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZRange SP 8192 (2^47); KZRange SS 16 (2^47); KZRange (SS + n) 16 (2^47); KZRange (SS + off) 16 (2^47);
       KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4097 (2^47)]
      [(SS, n); (SS + (off - q), 8)] [(SS, n); (SP + -112, 112); (SS + (off - q), 8)] [(SS, n); (SS + (off - q), 8)].
    all: lazymatch goal with
      | |- evtF _ _ _ _ => idtac
      | |- exists _, rdn _ _ _ _ = Some _ =>
          first [ rewrite adenot_wa; unfold estart; cbn [a_base a_off]; ax2_l2rl_ez;
                  rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64%N) with 64;
                  lazymatch goal with |- exists _, rdn _ _ (wa ?a) 1 = Some _ =>
                    match goal with |- context [?x mod 2 ^ 64] =>
                      rewrite (Z.mod_small x (2 ^ 64)) by (clear - HP2 SNS QQ SB HF S16 NSM; lia) end;
                    eapply (ax2_l2rl_rd1 mm SS (map (Z_to_bv 8) src) _ SRCB);
                      [ clear - HF QQ; lia | rewrite LSM; clear - HP2 QQ HF; lia ]
                  end
                | ax2_l2rl_sdw USB' mm ltac:(clear - HP2 SNS QQ SB HF S16 NSM SBB; lia)
                    ltac:(clear - HP2 SNS QQ SB HF S16 NSM SBB; Z.div_mod_to_equations; lia) ]
      | |- branch_taken BC_LT _ _ = true =>
          ax2_l2rl_chk USB' ltac:(clear - HP2 SNS QQ SB HF S16 NSM SBB; lia)
            ltac:(clear - HP2 SNS QQ SB HF S16 NSM SBB; Z.div_mod_to_equations; lia)
      | |- branch_taken _ _ _ = _ =>
          ax2_l2rl_br ltac:(clear - HP2 SNS QQ SB HF S16 NSM SBB; lia)
      | |- accP _ _ _ =>
          unfold accP; cbn [fst snd]; rewrite adenot_wa; unfold estart; cbn [a_base a_off]; ax2_l2rl_ez;
          rewrite ?Z_to_bv_unsigned; unfold wa, bv_wrap, bv_modulus; change (Z.of_N 64%N) with 64;
          rewrite ?Z.shiftr_div_pow2 by lia; change (3 mod 64) with 3 in *; change (2 ^ 3) with 8 in *;
          repeat match goal with |- context [?y mod 2 ^ 64] =>
            rewrite (Z.mod_small y (2 ^ 64)) by (clear - HP2 SNS QQ SB HF S16 NSM SBB; Z.div_mod_to_equations; lia) end;
          let WR := fresh "WR" in pose proof WSBS as (_ & _ & WR); apply WR;
          unfold shad, shlen, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
          clear - HP2 SNS QQ SB HF S16 NSM SBB SB8; Z.div_mod_to_equations; lia
      | |- _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off]; ax2_l2rl_ez;
          rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64%N) with 64;
          repeat rewrite Z.mod_small by (clear - HP2 SNS QQ SB HF S16 NSM; lia);
          clear - HP2 SNS QQ SB HF S16 NSM; lia
      end.
    kx_post_regs_keep.
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    assert (CBL : DT + 4 + zlen cbs <= SP + -112) by (rewrite LCB; lia). clear DTLb.
    kx_cells_split BM.
    kx_cell KC. kx_cell4 KC0. kx_frame KC1. kx_cell KC2.
    kx_frame KC3. kx_frame BM. kx_frame GAP. kx_frame FRC.
    kx_frame SRCB. kx_frame CBS. kx_munch MU.
    lazymatch goal with HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ mm _ DST buf OUT HL) as (buf' & OUT' & LB'); clear OUT end.
    kx_post_mem_free.
    all: lazymatch goal with
      | |- evtF _ _ _ _ => idtac
      | |- _ => cbn [cells_size csize]; clear - SB; lia
      end.
    eapply (KB _ 1 r (-1 * q + (off + SS)) _ pad).
    - unfold AX2F. split; [exists buf'; split; [exact OUT' | rewrite LB'; exact LBF] |].
      split; [exact SRCB |]. split; [exact CBS |]. split; [eassumption |]. split; [exists g; exact GAP |].
      split; [exact FRC |]. split; [eassumption |]. split; eassumption.
    - unfold ax2_bd. kx_cells_merge.
    - right; split; [reflexivity | lia].
    - lia.
    - destruct (Z.eq_dec off q); [left; lia | right; lia].
  Time Qed.

  Lemma ax2_l2rl_near_rd1 : forall m A bs a, bytes_at bsegs m A bs -> A <= a -> a + 1 <= A + zlen bs ->
    exists b, rdn bsegs m (wa a) 1 = Some b.
  Proof.
    intros m A bs a HB H1 H2.
    pose proof (bytes_at_rdn bsegs m A bs (Z.to_nat (a - A)) 1 HB ltac:(lia)) as R.
    rewrite Z2Nat.id in R by lia. replace (A + (a - A)) with a in R by lia. eexists; exact R.
  Time Qed.

  Ltac ax2_l2rl_near_z CL :=
    ax2_l2rl_ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64%N) with 64;
    try change (3 mod 64) with 3; try change (2 ^ 3) with 8;
    repeat match goal with |- context [?y mod 2 ^ 64] => rewrite (Z.mod_small y (2 ^ 64)) by CL end.

  Ltac ax2_l2rl_near_chk U CL CLD :=
    lazymatch goal with
    | |- branch_taken BC_LT (edenot ?E (EAlu ALU_SUB (EMd M_MUL (EAlu ALU_SLTU (ELit 0) ?X)
            (EAlu ALU_ADD (EAlu ALU_ADD (EAlu ALU_AND ?B (ELit 7)) (ELit ?k)) (ELit 1))) (ELit 1))) (edenot ?E ?X) = true =>
        change (EAlu ALU_SUB (EMd M_MUL (EAlu ALU_SLTU (ELit 0) X)
            (EAlu ALU_ADD (EAlu ALU_ADD (EAlu ALU_AND B (ELit 7)) (ELit k)) (ELit 1))) (ELit 1)) with (chk_ob X B k);
        let x := fresh "x" in let HX := fresh "HX" in
        remember (bv_unsigned (edenot E B)) as x eqn:HX;
        eapply (chk_ob_unp bsegs _ E X B k _ _ x U);
        [ rewrite HX; symmetry; apply Z_to_bv_bv_unsigned
        | rewrite HX; let RG := fresh "RG" in pose proof (bv_unsigned_in_range 64 (edenot E B)) as RG;
          unfold bv_modulus in RG; change (2 ^ Z.of_N 64) with (2 ^ 64) in RG; clear - RG; lia
        | rewrite HX; ax2_l2rl_near_z CL; CL
        | rewrite HX; ax2_l2rl_near_z CL; CL
        | lia
        | lazymatch goal with
          | |- edenot _ (EVar ?jj) = _ =>
              let HR := fresh "HR" in kx_read_eq jj HR; cbn [edenot]; rewrite HR; clear HR;
              f_equal; rewrite adenot_wa; f_equal; unfold estart; cbn [a_base a_off]; rewrite HX; ax2_l2rl_ez;
              rewrite ?Z_to_bv_unsigned; unfold shad, ASHOFF, bv_wrap, bv_modulus; change (Z.of_N 64%N) with 64;
              rewrite ?Z.shiftr_div_pow2 by lia; change (3 mod 64) with 3 in *; change (2 ^ 3) with 8 in *;
              repeat match goal with |- context [?y mod 2 ^ 64] => rewrite (Z.mod_small y (2 ^ 64)) by CLD end;
              first [ CLD | lazymatch goal with |- ?g => fail 2 "CHKRD" g end ]
          | |- ?g => fail 1 "CHKX" g
          end ]
    end.

  Ltac ax2_l2rl_near_br CL :=
    lazymatch goal with
    | KXA : forall j, (j < length _)%nat -> ev ?E j = _ |- branch_taken _ (edenot ?E _) _ = _ =>
        cbn [edenot]; unfold branch_taken; rewrite ?bv_eqb_Z, ?bv_ltu_Z;
        repeat (rewrite u_xor64 || rewrite u_sltu64 || rewrite u_add64 || rewrite u_sub64);
        repeat match goal with |- context [ev E ?jj] => rewrite (KXA jj) by (cbn [length]; lia) end;
        cbn [nth]; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64%N) with 64;
        repeat match goal with |- context [?y mod 2 ^ 64] => rewrite (Z.mod_small y (2 ^ 64)) by CL end;
        repeat match goal with |- context [(Z.lxor ?a ?b <? 1)%Z] =>
          let H1 := fresh "HL1" in let H2 := fresh "HL2" in
          assert (H1 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; split; intros _; CL);
          assert (H2 : Z.lxor a b <> 0) by (rewrite zb_lxor_eq0; CL);
          replace (Z.lxor a b <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia) end;
        first [ reflexivity | apply Z.eqb_neq; CL | apply Z.eqb_eq; CL | apply Z.ltb_lt; CL | apply Z.ltb_ge; CL
              | apply Bool.negb_true_iff, Z.ltb_ge; CL | apply Bool.negb_false_iff, Z.ltb_lt; CL
              | lazymatch goal with |- ?g => fail 2 "BR" g end ]
    end.

  Ltac ax2_l2rl_near_side SRCB LSM U CL CLD :=
    lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- exists _, rdn _ _ _ _ = Some _ =>
        rewrite adenot_wa; unfold estart; cbn [a_base a_off]; ax2_l2rl_near_z CL;
        eapply (ax2_l2rl_near_rd1 _ SS (map (Z_to_bv 8) src) _ SRCB); [CL | rewrite LSM; CL]
    | |- branch_taken BC_LT (edenot _ (EAlu ALU_SUB (EMd M_MUL (EAlu ALU_SLTU (ELit 0) _) _) (ELit 1))) _ = true =>
        ax2_l2rl_near_chk U CL CLD
    | |- branch_taken _ _ _ = _ => ax2_l2rl_near_br CL
    | |- _ => unfold flat, estart, elenZ; cbn [a_base a_off]; ax2_l2rl_near_z CLD; CLD
    end.

  Ltac ax2_l2rl_near_pre mm XM BM KB :=
    let XM0 := fresh "XM0" in pose proof XM as XM0;
    destruct XM as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM);
    unfold ax2_bd in BM; unfold ax2_st; unfold ax2_st in KB;
    pose proof (A2 ax2_sp_bounds) as SB; unfold HUF_DEC_STACK_A in LOS;
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6);
    lazymatch goal with HMU : munch _ m0 mm |- _ => pose proof (A2 ax2_unp' mm HMU) as (UDT' & UDB' & USB') end;
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR; unfold AIMG_HI, KLS in *;
    destruct SBA as (SBK & SB8); pose proof (A2 ax2_outb) as OB;
    assert (DSR : 4096 <= DST /\ DST + dcap <= 2^47) by lia; clear OB;
    assert (LSM : zlen (map (Z_to_bv 8) src) = n) by (rewrite length_map; reflexivity);
    assert (SNS : SS + n + 4096 <= SP + -112) by lia;
    let p := eval cbv in (AHUF_DX2_1X + 3976) in change (AHUF_DX2_1X + 3976) with p;
    let p := eval cbv in (AHUF_DX2_1X + 4428) in change (AHUF_DX2_1X + 4428) with p in KB.

  Lemma ax2_l2rl_near_a : forall mm j q r off cw pad (x1 x10 x11 x12 x18 x20 x21 x22 x31 : word),
    XF mm -> BD mm cw (8 * q + r) pad (SS + off) -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= r <= 7 -> 0 <= q <= 8 ->
    8 * q + r <= 64 -> 1 <= off <= 7 -> SS + off + 8 <= SS + n -> q <= off ->
    (forall mm' fl bc' P' cw' pad' (x11' x12' x18' x20' x21' x22' x30' x31' : word),
       XF mm' -> BD mm' cw' bc' pad' P' -> (fl = 0 \/ (fl = 1 /\ bc' <= 7)) -> 0 <= bc' <= 64 -> PINV P' ->
       evtF bsegs RNG POST (L2 4428 mm' x1 j (ZB fl) x11' x12' x18' x20' x21' x22' x30' x31')) ->
    evtF bsegs RNG POST (L2 3976 mm x1 j x10 x11 x12 x18 x20 x21 x22 (ZB (8 * q + r)) x31).
  Proof using All.
    intros mm j q r off cw pad x1 x10 x11 x12 x18 x20 x21 x22 x31 XM BM HD HJ RR QQ QB HN HP2 QO KB.
    ax2_l2rl_near_pre mm XM BM KB.
    change (2^31 - 2^15) with 2147450880.
    kx_runFm [AHUF_DX2_1X + 4428] 120%nat
      [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
       KZRange off 1 7; KZRange (off - q) 0 7; KZRange (n - off) 8 (2^26); KZRange n 9 (2^26);
       KZRange (n - (off - q)) 8 (2^26); KZRange (SS + (off - q)) 16 (2^47);
       KZWr (SP + -104) 40; KZDisj (SP + -104) 40 SS n;
       KZWord (SP + -88) 8 (SS + off); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZRange SP 8192 (2^47); KZRange SS 16 (2^47); KZRange (SS + n) 16 (2^47); KZRange (SS + off) 16 (2^47);
       KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4097 (2^47)]
      [(SS, n); (SS + (off - q), 8)] [(SS, n); (SP + -112, 112); (SS + (off - q), 8)] [(SS, n); (SS + (off - q), 8)].
    all: ax2_l2rl_near_side SRCB LSM USB' ltac:(clear - HP2 SNS QQ RR QB SB HN QO S16 NSM SBB; lia)
      ltac:(clear - HP2 SNS QQ RR QB SB HN QO S16 NSM SBB; Z.div_mod_to_equations; lia).
    kx_post_regs_keep.
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    assert (CBL : DT + 4 + zlen cbs <= SP + -112) by (rewrite LCB; lia). clear DTLb.
    kx_cells_split BM.
    kx_cell KC. kx_cell4 KC0. kx_frame KC1. kx_cell KC2.
    kx_frame KC3. kx_frame BM. kx_frame GAP. kx_frame FRC.
    kx_frame SRCB. kx_frame CBS. kx_munch MU.
    lazymatch goal with HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ mm _ DST buf OUT HL) as (buf' & OUT' & LB'); clear OUT end.
    kx_post_mem_free.
    all: lazymatch goal with
      | |- evtF _ _ _ _ => idtac
      | |- _ => cbn [cells_size csize]; clear - SB; lia
      end.
    eapply (KB _ 1 r (-1 * q + (off + SS)) _ pad).
    - unfold AX2F. split; [exists buf'; split; [exact OUT' | rewrite LB'; exact LBF] |].
      split; [exact SRCB |]. split; [exact CBS |]. split; [eassumption |]. split; [exists g; exact GAP |].
      split; [exact FRC |]. split; [eassumption |]. split; eassumption.
    - unfold ax2_bd. kx_cells_merge.
    - right; split; [reflexivity | lia].
    - lia.
    - destruct (Z.eq_dec off q); [left; lia | right; lia].
  Time Qed.

  Lemma ax2_l2rl_near_b : forall mm j q r off cw pad (x1 x10 x11 x12 x18 x20 x21 x22 x31 : word),
    XF mm -> BD mm cw (8 * q + r) pad (SS + off) -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= r <= 7 -> 0 <= q <= 8 ->
    8 * q + r <= 64 -> 1 <= off <= 7 -> SS + off + 8 <= SS + n -> off < q ->
    (forall mm' fl bc' P' cw' pad' (x11' x12' x18' x20' x21' x22' x30' x31' : word),
       XF mm' -> BD mm' cw' bc' pad' P' -> (fl = 0 \/ (fl = 1 /\ bc' <= 7)) -> 0 <= bc' <= 64 -> PINV P' ->
       evtF bsegs RNG POST (L2 4428 mm' x1 j (ZB fl) x11' x12' x18' x20' x21' x22' x30' x31')) ->
    evtF bsegs RNG POST (L2 3976 mm x1 j x10 x11 x12 x18 x20 x21 x22 (ZB (8 * q + r)) x31).
  Proof using All.
    intros mm j q r off cw pad x1 x10 x11 x12 x18 x20 x21 x22 x31 XM BM HD HJ RR QQ QB HN HP2 QO KB.
    ax2_l2rl_near_pre mm XM BM KB.
    change (2^31 - 2^15) with 2147450880.
    kx_runFm [AHUF_DX2_1X + 4428] 120%nat
      [KZRange q 1 8; KZRange r 0 7; KZRange (8 * q + r) 8 64;
       KZRange off 1 7; KZRange (q - off) 1 8; KZRange (n - off) 8 (2^26); KZRange n 9 (2^26);
       KZWr (SP + -104) 40; KZDisj (SP + -104) 40 SS n;
       KZWord (SP + -88) 8 (SS + off); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZRange SP 8192 (2^47); KZRange SS 16 (2^47); KZRange (SS + n) 16 (2^47); KZRange (SS + off) 16 (2^47);
       KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4097 (2^47)]
      [(SS, n); (SS, 8)] [(SS, n); (SP + -112, 112); (SS, 8)] [(SS, n); (SS, 8)].
    all: ax2_l2rl_near_side SRCB LSM USB' ltac:(clear - HP2 SNS QQ RR QB SB HN QO S16 NSM SBB; lia)
      ltac:(clear - HP2 SNS QQ RR QB SB HN QO S16 NSM SBB; Z.div_mod_to_equations; lia).
    kx_post_regs_keep.
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    assert (CBL : DT + 4 + zlen cbs <= SP + -112) by (rewrite LCB; lia). clear DTLb.
    kx_cells_split BM.
    kx_cell KC. kx_cell4 KC0. kx_frame KC1. kx_cell KC2.
    kx_frame KC3. kx_frame BM. kx_frame GAP. kx_frame FRC.
    kx_frame SRCB. kx_frame CBS. kx_munch MU.
    lazymatch goal with HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ mm _ DST buf OUT HL) as (buf' & OUT' & LB'); clear OUT end.
    kx_post_mem_free.
    all: lazymatch goal with
      | |- evtF _ _ _ _ => idtac
      | |- _ => cbn [cells_size csize]; clear - SB; lia
      end.
    eapply (KB _ 0 _ _ _ pad).
    - unfold AX2F. split; [exists buf'; split; [exact OUT' | rewrite LB'; exact LBF] |].
      split; [exact SRCB |]. split; [exact CBS |]. split; [eassumption |]. split; [exists g; exact GAP |].
      split; [exact FRC |]. split; [eassumption |]. split; eassumption.
    - unfold ax2_bd. kx_cells_merge.
    - left; reflexivity.
    - lia.
    - left; lia.
  Time Qed.

  Lemma ax2_l2rl_near : forall mm j bc P cw pad (x1 x10 x11 x12 x18 x20 x21 x22 x31 : word),
    XF mm -> BD mm cw bc pad P -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= bc <= 64 -> PINV P -> SS + 1 <= P <= SS + 7 ->
    (forall mm' fl bc' P' cw' pad' (x11' x12' x18' x20' x21' x22' x30' x31' : word),
       XF mm' -> BD mm' cw' bc' pad' P' -> (fl = 0 \/ (fl = 1 /\ bc' <= 7)) -> 0 <= bc' <= 64 -> PINV P' ->
       evtF bsegs RNG POST (L2 4428 mm' x1 j (ZB fl) x11' x12' x18' x20' x21' x22' x30' x31')) ->
    evtF bsegs RNG POST (L2 3976 mm x1 j x10 x11 x12 x18 x20 x21 x22 (ZB bc) x31).
  Proof using All.
    intros mm j bc P cw pad x1 x10 x11 x12 x18 x20 x21 x22 x31 XM BM HD HJ HB HP HN KB.
    destruct HP as [HP | (HP1 & HP2)]; [lia |].
    assert (OF : exists off, P = SS + off) by (exists (P - SS); lia).
    destruct OF as (off & ->).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= r <= 7 /\ 0 <= q <= 8)
      by (exists (bc / 8), (bc mod 8); Z.div_mod_to_equations; lia).
    destruct QR as (q & r & -> & RR & QQ).
    destruct (Z_le_gt_dec q off) as [QO | QO].
    - eapply ax2_l2rl_near_a; [exact XM | exact BM | exact HD | exact HJ | exact RR | exact QQ | lia | lia | lia | lia | exact KB].
    - eapply ax2_l2rl_near_b; [exact XM | exact BM | exact HD | exact HJ | exact RR | exact QQ | lia | lia | lia | lia | exact KB].
  Time Qed.

  Lemma ax2_l2rl : forall mm j bc P cw pad (x1 x10 x11 x12 x18 x20 x21 x22 x31 : word),
    XF mm -> BD mm cw bc pad P -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= bc <= 64 -> PINV P ->
    (forall mm' fl bc' P' cw' pad' (x11' x12' x18' x20' x21' x22' x30' x31' : word),
       XF mm' -> BD mm' cw' bc' pad' P' -> (fl = 0 \/ (fl = 1 /\ bc' <= 7)) -> 0 <= bc' <= 64 -> PINV P' ->
       evtF bsegs RNG POST (L2 4428 mm' x1 j (ZB fl) x11' x12' x18' x20' x21' x22' x30' x31')) ->
    evtF bsegs RNG POST (L2 3976 mm x1 j x10 x11 x12 x18 x20 x21 x22 (ZB bc) x31).
  Proof using All.
    intros mm j bc P cw pad x1 x10 x11 x12 x18 x20 x21 x22 x31 XM BM HD HJ HB HP KB.
    destruct HP as [-> | HP].
    2: { destruct (Z_le_gt_dec (SS + 8) P) as [F | F].
         - eapply ax2_l2rl_far; [exact XM | exact BM | exact HD | exact HJ | exact HB | right; exact HP | exact F | exact KB].
         - eapply ax2_l2rl_near; [exact XM | exact BM | exact HD | exact HJ | exact HB | right; exact HP | lia | exact KB]. }
    ax2_l2rl_pre mm XM BM KB.
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= r <= 7 /\ 0 <= q <= 8)
      by (exists (bc / 8), (bc mod 8); Z.div_mod_to_equations; lia).
    destruct QR as (q & r & -> & RR & QQ).
    kx_runFm [AHUF_DX2_1X + 4428] 120%nat
      [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
       KZWr (SP + -104) 40; KZDisj (SP + -104) 40 SS n;
       KZWord (SP + -88) 8 SS; KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZRange SP 8192 (2^47); KZRange SS 16 (2^47); KZRange (SS + n) 16 (2^47); KZRange n 1 (2^26);
       KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4097 (2^47)]
      [(SS, n)] [(SS, n); (SP + -112, 112)] [(SS, n)].
    kx_post_regs_keep. cbn [mem_denot].
    eapply (KB mm 0 (8 * q + r) SS cw pad); [exact XM0 | exact BM | left; reflexivity | lia | left; reflexivity].
  Time Qed.

  Lemma ax2_l2body_w4ok : forall segs zv xs m a v b c A cs k V,
    zatoms_lt (length zv) a = true -> zatoms_lt (length zv) v = true -> zsa a = SA b c ->
    0 <= zden zv a - c < 2^64 -> 0 <= zden zv a < 2^64 -> 0 <= zden zv v < 2^64 -> zden zv a + 4 <= 2^64 ->
    rw_cells segs m A cs -> cell_at cs k = Some (C4 V) -> zden zv a = A + Z.of_nat k -> V = Z_to_bv 64 (zden zv v) ->
    kentry_ok segs (kE zv xs) m (zk_ent (ZKWord a 4 v)).
  Proof.
    intros segs zv xs m a v b c A cs k V HA HV HS R1 R2 R3 R4 [CA WR] HC HE HVe.
    cbn [kentry_ok zk_ent].
    assert (ES : estart (kE zv xs) (zsa a) = zden zv a) by (eapply estart_zsa_split; eauto).
    split; [lia|]. split.
    - unfold flat. rewrite ES. lia.
    - rewrite adenot_wa, ES, HE, (zle_ok zv xs v HV), <- HVe.
      destruct CA as [WF BA].
      destruct (cell_at_split cs k (C4 V) (C4 V) HC) as (pre & post & -> & HK & _).
      apply cells_wf_app in WF as [WFp WFr].
      assert (LEN : (k + 4 <= length (cells_bytes (pre ++ C4 V :: post)))%nat).
      { rewrite cells_bytes_app, length_app. cbn [cells_bytes]. rewrite length_app.
        pose proof (cbytes_length (C4 V) I) as L4. cbn [csize] in L4.
        rewrite L4, (cells_bytes_length pre WFp). lia. }
      pose proof (bytes_at_rdn segs m A _ k 4 BA LEN) as RD.
      unfold wa in *. etransitivity; [exact RD|]. f_equal.
      rewrite cells_bytes_app. cbn [cells_bytes cbytes].
      rewrite <- HK, <- (cells_bytes_length pre WFp), skipn_app_exact.
      unfold le4. reflexivity.
  Time Qed.

  Fixpoint ax2_l2body_c4off (off : nat) (cs : list cell) : list nat :=
    match cs with
    | [] => []
    | C4 _ :: r => off :: ax2_l2body_c4off (off + 4) r
    | c :: r => ax2_l2body_c4off (off + csize c) r
    end.

  Ltac ax2_l2body_w4try segs zv xs m a v b c A cs H ks :=
    lazymatch ks with
    | nil => fail
    | cons ?k ?rest =>
        first [ eapply (ax2_l2body_w4ok segs zv xs m a v b c A cs k _);
                [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
                | kx_arith | kx_arith | kx_arith | kx_arith | exact H | reflexivity
                | cbv [zden nth]; lia | cbv [zden nth]; f_equal; first [reflexivity | lia] ]
              | ax2_l2body_w4try segs zv xs m a v b c A cs H rest ]
    end.

  Ltac ax2_l2body_w4core segs zv xs m a v :=
    let s1 := eval vm_compute in (zsa a) in
    lazymatch s1 with SA ?b ?c =>
      match goal with H : rw_cells segs m ?A ?cs |- _ =>
        let ks := eval vm_compute in (ax2_l2body_c4off 0 cs) in
        ax2_l2body_w4try segs zv xs m a v b c A cs H ks end
    end.

  Ltac ax2_l2body_w4 :=
    lazymatch goal with
    | |- kentry_ok ?segs (kE ?zv ?xs) ?m (zk_ent (ZKWord ?a 4 ?v)) => ax2_l2body_w4core segs zv xs m a v
    | |- kentry_ok ?segs ?E ?m (zk_ent (ZKWord ?a 4 ?v)) =>
        let e := eval unfold E in E in
        lazymatch e with kx_env (map (Z_to_bv 64) ?zv) ?xs => ax2_l2body_w4core segs zv xs m a v end
    end.

  Ltac ax2_l2body_zs zv na :=
    cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
    kx_tbl_idx tl; kx_abstract;
    unfold bv_wrap, bv_modulus, KXGoM.apart in *; change (2 ^ Z.of_N 64) with (2^64) in *; rewrite ?Z.mod_small by lia;
    try change (3 mod 64) with 3 in *; try change (2 ^ 3) with 8 in *.

  Ltac ax2_l2body_dj :=
    lazymatch goal with EE := kx_env (map (Z_to_bv 64) ?zv) ?xs |- _ =>
      let na := eval vm_compute in (length zv) in
      change EE with (kE zv xs); unfold flat, elenZ;
      repeat match goal with |- context [estart (kE zv xs) ?a] =>
        rewrite (estart_ez_kE zv xs a); [| ax2_l2body_zs zv na; Z.div_mod_to_equations; lia] end;
      cbn [edenot]; rewrite ?Z_to_bv_unsigned;
      ax2_l2body_zs zv na; Z.div_mod_to_equations; lia
    end.

  Ltac ax2_l2body_xf :=
    lazymatch goal with OUT' : u8arr _ _ DST (map _ ?b'), LB' : length ?b' = length ?b, LBF : Z.of_nat (length ?b) = dcap |- _ =>
      unfold AX2F; split; [exists b'; split; [exact OUT' | rewrite LB'; exact LBF] |];
      repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]
    end.

  Ltac ax2_l2body_rng :=
    repeat match goal with |- context [bv_unsigned (ev ?E ?i)] =>
      lazymatch goal with _ : _ <= bv_unsigned (ev E i) <= _ |- _ => fail | _ => idtac end;
      let R := fresh "R" in kx_range (EVar i) R end.

  Ltac ax2_l2body_x G8 XM0 BM HJ :=
    try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end);
    kx_post_regs_keep;
    lazymatch goal with |- context [mem_denot ?E ?mm []] => change (mem_denot E mm []) with mm end;
    eapply G8; [exact XM0 | exact BM | assumption | exact HJ].

  Ltac ax2_l2body_post BM SRCB CBS FRC MU :=
    kx_post_regs_keep;
    lazymatch goal with H : u8arr bsegs ?mm DST (map _ ?b), HL : log_flat _ _ |- _ =>
      let buf' := fresh "buf'" in let OUT' := fresh "OUT'" in let LB' := fresh "LB'" in
      destruct (kx_u8arr_ex bsegs _ mm _ DST b H HL) as (buf' & OUT' & LB'); clear H end;
    kx_cells_split BM; kx_cells_post; kx_frame SRCB; kx_frame CBS; kx_frame FRC; kx_munch MU; kx_post_mem_free;
    try replace (- DT + -5) with (- DT - 5) by lia;
    try change (Z_to_bv 64 2305843009213693952) with (Z_to_bv 64 (2^61));
    try change (Z_to_bv 64 2147450880) with (Z_to_bv 64 (2^31 - 2^15));
    try change (Z_to_bv 64 134656) with (Z_to_bv 64 AX2_K8).

  Lemma ax2_l2body_run : forall mm j bc P cw pad (x1 x11 x12 x18 x20 x21 x22 x30 x31 : word),
    G4768 -> XF mm -> BD mm cw bc pad P -> 1 <= dcap -> 0 <= j -> j + 2 <= dcap -> 0 <= bc <= 7 -> PINV P ->
    (forall mm' j' bc' P' cw' pad' (x10' x11' x12' x18' x20' x21' x22' x31' : word),
       XF mm' -> BD mm' cw' bc' pad' P' -> j < j' <= dcap -> 0 <= bc' <= 64 -> PINV P' ->
       evtF bsegs RNG POST (L2 3976 mm' x1 j' x10' x11' x12' x18' x20' x21' x22' (ZB bc') x31')) ->
    evtF bsegs RNG POST (L2 4428 mm x1 j (ZB 1) x11 x12 x18 x20 x21 x22 x30 x31).
  Proof using All.
    intros mm j bc P cw pad x1 x11 x12 x18 x20 x21 x22 x30 x31 G8 XM BM D1 HJ HS HB HP KH.
    unfold ax2_st in KH.
    pose proof XM as XM0. destruct XM as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    unfold ax2_bd in BM. unfold ax2_st.
    pose proof (A2 ax2_sp_bounds) as SB. unfold HUF_DEC_STACK_A in LOS.
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6). destruct (B6 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI, KLS in *.
    replace (- DT - 5) with (-1 * DT + -5) by lia.
    let p := eval cbv in (AHUF_DX2_1X + 4428) in change (AHUF_DX2_1X + 4428) with p.
    pose proof (A2 ax2_tab mm CBS) as TBL.
    pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB').
    pose proof (WDB ltac:(lia)) as WDB'. pose proof (WDBS ltac:(lia)) as WDBS'.
    pose proof TOK as (TL & TC & TCK). unfold HUF_TABLELOG_MAX in TL. unfold FseNCount.Zlength in TC.
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    clear TCK TC ECB. unfold ablk in Q4. unfold AIMG_HI, KLS in Q4.
    change (2 ^ 31 - 2 ^ 15) with 2147450880. change (2 ^ 61) with 2305843009213693952. unfold AX2_K8.
    rewrite <- (Z_to_bv_bv_unsigned cw) in BM.
    pose proof (bv_unsigned_in_range 64 cw) as RCW. unfold bv_modulus in RCW. cbn in RCW.
    kx_runFL [AHUF_DX2_1X + 3976; AHUF_DX2_1X + 4768] 80%nat
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange tl 1 12;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
       KZWr (DST + j) 2; KZWr (SP + -104) 40;
       KZDisj (DST + j) 2 (DT + 4) (4 * 2^tl); KZDisj (DST + j) 2 (SP + -104) 40; KZDisj (SP + -104) 40 (DT + 4) (4 * 2^tl);
       KZRange DT 4096 (2^47); KZRange DST 4096 (2^47); KZRange j 0 (2^32); KZRange dcap 1 (2^32);
       KZRange (dcap - j) 2 (2^32); KZRange (DST + j) 4096 (2^47); KZRange bc 0 7; KZRange (SP + -112) 4096 (2^47);
       KZWord (SP + -96) 4 bc; KZWord (SP + -104) 8 (bv_unsigned cw)]
      [(DT + 4, 4 * 2^tl)]
      [(DT + 4, 4 * 2^tl); (DST + j, 2); (SP + -112, 112)]
      [(DT + 4, 4 * 2^tl); (DST + j, 2)].
    all: try ax2_l2body_w4.
    all: try (lazymatch goal with |- flat _ _ _ /\ _ => ax2_l2body_dj | |- flat _ _ _ => ax2_l2body_dj end).
    all: try (lazymatch goal with |- exists _, rdn _ _ _ _ = _ => kx_rd end).
    all: lazymatch goal with |- evtF _ _ _ _ => idtac end.
    all: unfold KXGoM.apart in DJ1, DJ2, DJ3.
    all: ax2_l2body_post BM SRCB CBS FRC MU.
    all: eapply KH; [ax2_l2body_xf | unfold ax2_bd; kx_cells_merge | ax2_l2body_rng; lia | ax2_l2body_rng; lia | exact HP].
  Time Qed.

  Lemma ax2_l2body : forall mm j fl bc P cw pad (x1 x11 x12 x18 x20 x21 x22 x30 x31 : word),
    G4768 -> XF mm -> BD mm cw bc pad P -> 1 <= dcap -> 0 <= j <= dcap -> (fl = 0 \/ (fl = 1 /\ bc <= 7)) -> 0 <= bc <= 64 ->
    PINV P ->
    (forall mm' j' bc' P' cw' pad' (x10' x11' x12' x18' x20' x21' x22' x31' : word),
       XF mm' -> BD mm' cw' bc' pad' P' -> j < j' <= dcap -> 0 <= bc' <= 64 -> PINV P' ->
       evtF bsegs RNG POST (L2 3976 mm' x1 j' x10' x11' x12' x18' x20' x21' x22' (ZB bc') x31')) ->
    evtF bsegs RNG POST (L2 4428 mm x1 j (ZB fl) x11 x12 x18 x20 x21 x22 x30 x31).
  Proof using All.
    intros mm j fl bc P cw pad x1 x11 x12 x18 x20 x21 x22 x30 x31 G8 XM BM D1 HJ HF HB HP KH.
    destruct HF as [HF | [HF HB7]]; subst fl.
    2: destruct (Z_lt_le_dec (dcap - j) 2) as [HS | HS].
    3: exact (ax2_l2body_run mm j bc P cw pad x1 x11 x12 x18 x20 x21 x22 x30 x31 G8 XM BM D1 ltac:(lia) ltac:(lia) ltac:(lia) HP KH).
    all: pose proof XM as XM0; destruct XM as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    all: unfold ax2_bd in BM; unfold ax2_st.
    all: pose proof (A2 ax2_sp_bounds) as SB; unfold HUF_DEC_STACK_A in LOS.
    all: pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6); destruct (B6 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
    all: pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR; unfold AIMG_HI, KLS in *.
    all: replace (- DT - 5) with (-1 * DT + -5) by lia.
    all: let p := eval cbv in (AHUF_DX2_1X + 4428) in change (AHUF_DX2_1X + 4428) with p.
    - kx_runFL [AHUF_DX2_1X + 4768] 20%nat [KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: ax2_l2body_x G8 XM0 BM HJ.
    - kx_runFL [AHUF_DX2_1X + 4768] 20%nat
        [KZRange (dcap - j) 0 1; KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: ax2_l2body_x G8 XM0 BM HJ.
  Time Qed.

  Lemma ax2_goal_3976_ok : G4768 -> G3976.
  Proof using All.
    intros G8.
    assert (IND : forall (k : nat) mm j bc P cw pad (x1 x10 x11 x12 x18 x20 x21 x22 x31 : word),
      dcap - j <= Z.of_nat k -> XF mm -> BD mm cw bc pad P -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= bc <= 64 -> PINV P ->
      evtF bsegs RNG POST (L2 3976 mm x1 j x10 x11 x12 x18 x20 x21 x22 (ZB bc) x31)).
    { induction k as [|k IH]; intros mm j bc P cw pad x1 x10 x11 x12 x18 x20 x21 x22 x31 HK XM BM HD HJ HB HP;
        (eapply ax2_l2rl; [exact XM | exact BM | exact HD | exact HJ | exact HB | exact HP |]);
        intros mm' fl bc' P' cw' pad' x11' x12' x18' x20' x21' x22' x30' x31' XM' BM' HF HB' HP';
        (eapply ax2_l2body; [exact G8 | exact XM' | exact BM' | exact HD | exact HJ | exact HF | exact HB' | exact HP' |]);
        intros mm2 j2 bc2 P2 cw2 pad2 y10 y11 y12 y18 y20 y21 y22 y31 XM2 BM2 HJ2 HB2 HP2.
      - lia.
      - eapply IH; [lia | exact XM2 | exact BM2 | exact HD | lia | exact HB2 | exact HP2]. }
    intros mm j bc P cw pad x1 x10 x11 x12 x18 x20 x21 x22 x31 XM BM HD HJ HB HP.
    exact (IND (Z.to_nat (dcap - j)) mm j bc P cw pad x1 x10 x11 x12 x18 x20 x21 x22 x31 ltac:(lia) XM BM HD HJ HB HP).
  Time Qed.

  Ltac ax2_goal_3924_ok_pc :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?e) _ _ _ _) => eval cbv in (e - AHUF_DX2_1X) end.

  Ltac ax2_goal_3924_ok_walk :=
    repeat lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let K := fresh "K" in destruct c eqn:K; cbv iota
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
        let o := ax2_goal_3924_ok_pc in
        let s := eval cbv in (orb (Z.eqb o 3976) (orb (Z.eqb o 4768) (orb (Z.eqb o 4772) (orb (Z.eqb o 4492) (Z.leb 4800 o))))) in
        lazymatch s with true => fail | false => zstep end
    end.

  Ltac ax2_goal_3924_ok_kz LO ZX :=
    repeat match goal with
    | K : ?c = ?b |- _ =>
        lazymatch c with context [bv_ltu] => idtac | context [bv_eqb] => idtac end;
        lazymatch b with true => idtac | false => idtac end;
        rewrite ?ZX, ?Z.land_0_r in K; repeat (rewrite LO in K by lia);
        rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned in K; try unfold bv_wrap, bv_modulus in K; cbn [Z.of_N] in K;
        repeat (rewrite Z.mod_small in K by lia);
        lazymatch type of K with
        | negb _ = true => apply Bool.negb_true_iff in K
        | negb _ = false => apply Bool.negb_false_iff in K
        | _ => idtac end;
        lazymatch type of K with
        | (_ <? _) = true => apply Z.ltb_lt in K
        | (_ <? _) = false => apply Z.ltb_ge in K
        | (_ =? _) = true => apply Z.eqb_eq in K
        | (_ =? _) = false => apply Z.eqb_neq in K end
    end.

  Ltac ax2_goal_3924_ok_regs LO X5 :=
    try rewrite (LO (DT + 4)) by lia; try rewrite (LO (tl + 256 * mtl)) by lia; try rewrite X5; try rewrite ax2_neg_desc by lia;
    try replace (DST + dcap + -2) with (DST + dcap - 2) by lia.

  Ltac ax2_goal_3924_ok_xf :=
    unfold AX2F; split; [eexists; split; eassumption |];
    repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption].

  Lemma ax2_goal_3924_ok : G3976 -> G4768 -> G4772 -> G3924.
  Proof using All.
    intros G76 G68 G72.
    unfold ax2_goal_3924.
    intros mm j bc P cw pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 XM BM HJ HB HP.
    pose proof XM as XM0. destruct XM as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof BM as BM0. unfold ax2_bd in BM.
    pose proof (A2 ax2_sp_bounds) as SB. unfold HUF_DEC_STACK_A in LOS.
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof TOK as (TL & TC & TCK); unfold HUF_TABLELOG_MAX in TL.
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (DSP : 0 <= DST /\ DST + dcap + 4096 <= SP - 2352 /\ (1 <= dcap -> 4096 <= DST))
      by (pose proof (A2 ax2_outb) as OB; unfold AIMG_HI, KLS in *; lia).
    destruct DSP as (DS0 & DS1 & DS2).
    unfold AIMG_HI, KLS in *.
    assert (LO : forall y, 0 <= y < 2^64 -> Z.land y 18446744073709551615 = y).
    { intros y Hy. change 18446744073709551615 with (2^64 - 1). rewrite zb_land_mask by lia. apply Z.mod_small; lia. }
    assert (X5 : ZB (Z.lxor (DT + 4) 18446744073709551615) = ZB (- DT - 5)).
    { apply Z_to_bv_eqm. first [rewrite zb_lxor_ones by lia | change 18446744073709551615 with (2^64 - 1); rewrite lxor_ones64 by lia].
      rewrite <- (Z.mod_add (- DT - 5) 1 (2^64)) by lia. f_equal. lia. }
    assert (ZX : zx32 (ZB bc) = ZB bc).
    { unfold zx32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      rewrite (Z.mod_small bc (2 ^ 64)) by lia. rewrite (Z.mod_small bc (2 ^ 32)) by lia. reflexivity. }
    unfold ax2_st.
    ax2_goal_3924_ok_walk.
    all: let o := ax2_goal_3924_ok_pc in
      lazymatch o with
      | 4772 => eapply G72; [exact XM0 | exact BM | exact HJ]
      | 4768 => kx_mkR_foldF; ax2_goal_3924_ok_regs LO X5; eapply G68; [ax2_goal_3924_ok_xf | eassumption | ax2_goal_3924_ok_kz LO ZX; lia | exact HJ]
      | 3976 => ax2_goal_3924_ok_kz LO ZX; kx_mkR_foldF; try rewrite ZX; ax2_goal_3924_ok_regs LO X5;
          lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?a) _ _ _) _ _ _ _ _ _) =>
            replace a with AX2_K8 by (vm_compute; reflexivity) end;
          eapply G76; [exact XM0 | exact BM0 | first [lia | apply HP; lia] ..]
      | _ => exfalso; ax2_goal_3924_ok_kz LO ZX; lia
      end.
  Time Qed.

End AX2C.
End CANSEC1.
