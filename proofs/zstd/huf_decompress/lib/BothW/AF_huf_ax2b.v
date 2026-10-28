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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_ax2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax2b () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2>neg_desc_shiftC56Stdlib6ZArith6BinInt1Z4onesK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax24AX2MC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2:ax2_blocksC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax28ax2_outbI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2=ax2_sp_boundsK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27ax2_endC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27ax2_unpC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2b7ax2_idxC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27ax2_tabK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk08K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp05K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk09K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenK46Stdlib9micromega=RingMicromega5Psatz07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC47Corelib4Init5Logic5proj2K46Stdlib9micromega7EnvRing3Pol01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06C5ARocqVerifyHarness?AgentSubmission6Common5KXTac9idx_factsC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zle_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac<idx_facts_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC5ARocqVerifyHarness?AgentSubmission6Common4KXGo5zt_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXMem;kx_u8arr_exC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega5Tauto8GFormula02C56Stdlib5Arith8PeanoNat3Nat3ltbC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:kx_stk_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC57Corelib7BinNums6PosDef3Pos;of_succ_natK47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr04C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC56Stdlib6ZArith6BinInt1Z6eqb_eqc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2b<ax2_neg_descC5ARocqVerifyHarness?AgentSubmission6Common7SFModel<mod64_land63C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz04K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okK46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K46Stdlib9micromega:ZMicromega;ZArithProof01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultK47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07I46Stdlib5Lists4List6Exists00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C47Corelib4Init5Logic8iff_reflK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond03C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2b8ax2_lastC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z8inj_succ".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Lemma ax2_neg_desc : forall tl mtl, 1 <= tl <= 12 -> 0 <= mtl <= 255 ->
  Z.land (Z.land (bv_swrap 32 (0 - (tl + 256 * mtl))) 18446744073709551615) 63 = 64 - tl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_ax2b ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with52Hmh62Hth73mtlh82tlh91zp;1p;2p;3p;4p;6p;7p;8p10000p4p7210g000\R0p4p710p8g001:j12Tg001Xj21Tg0024j13Tg002Yj10Tg003>j27Tg003Yj1UTg0047j2FTg004Tj2DTg0051j29Tg005Nj2ATg0065j2@Tg006Rj2>Tg0072j2;Tg007Pj3<Tg007jj1WTg008Jj1VTg008jj2TTg009Hj1QTg009fj1KTg00:Qj24Tg00;4j2ETg00;Wj1CTg00<9j2BTg00<[j2GTg00=5j2HTg00=aj3ITg00>@j4JTg00?2j4?Tg00@8j1LTg00@Vj1MTg00A4j3NTP0j6OTg00AWj4PTg00BBj7=Tg00Bfj7RTg00CJj8STg00CnR0f1R1g00DLf0R2CPp=5P1g00E3R3g00ERR4P4g00F2R5P2g00FRF=p=6f2R6P3P4P4P5P1P2FRp=:f3R7P3P4P4P5P6P1P2GSp=8g00G2R3#2R8/11%33R9#0#0#2R:,11'7R;g00GWR</11%39#3#3#3R9#3#3#2R=,11'7R>P0%03R?#0#0#0#0R@#U%0@R@#0#0#2/F6,D7,9<'ARA%2?%2@R@'@'>%29,;2f4R9,9@5<0X90P7P6g00H5R?#WRB%V?R?1T01RC%Q0RD%K0RE14081E03R3'5,6E140:,53,6E5:ERF%C4R4PFC81BE5R5P2P6g00HaRFg00IARG'G1H26=<FGdAI0<1CJRGb2b3b4X001182112:'7P;[^00P2P9P6O2b1PBP?PCPDPE140<RC/53,6E140=,53,6E5:ER3P4P3C8P5PGb2b3b4X0011<2112='7P>[^00P2P7P1O2b1C?%L@,;APBP?%M0PD140@,5C,6EP5PGb2b3b411<@P2b19NA@EOW5W6X70X80o"). Qed.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section AX2B.
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

  Notation DW := [(SP + -56, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS6 := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

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

  Notation G2 l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs) (only parsing).
  Notation ZB z := (Z_to_bv 64 z).
  Notation TXF := (AX2F ra sp s0 s1 s2 s3 s4 s5 s6 m0 DST dcap SS DT lo src cbs).
  Notation TST := (ax2_st sp gp tp s7 s8 s9 s10 s11 FR fc dcap DT).
  Notation PE := (ZB (DST + dcap)).
  Notation DL := (ZB (tl + 256 * mtl)).
  Notation TBD mm cw bcw pad pw := (rw_cells bsegs mm (SP + -104) [C8 cw; C4 bcw; CB 4 pad; C8 pw; C8 (ZB SS); C8 (ZB (SS + 8))]).

  Tactic Notation "ax2b_runD" uconstr(STOPS) uconstr(FUEL) uconstr(D0) uconstr(KZS) uconstr(RRS) uconstr(WWS) uconstr(UWS) :=
    let S := constr:(STOPS : list Z) in let Fu := constr:(FUEL : nat) in
    let D := eval vm_compute in (D0 : list bool) in
    let K := constr:(KZS : list kz) in let R := constr:(RRS : list (Z * Z)) in let W := constr:(WWS : list (Z * Z)) in
    let U := constr:(UWS : list (Z * Z)) in
    kx_prepFm S Fu K R W U; kx_goFL D.

  Ltac t1ez :=
    try lazymatch goal with
    | |- context [edenot ?E _] =>
        let b := eval unfold E in E in
        lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
          rewrite ?(ez_ok zv E (kE_atoms zv xs));
          let na := eval vm_compute in (length zv) in
          cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
        end
    end.
  Ltac t1br :=
    lazymatch goal with
    | |- branch_taken _ _ _ = _ =>
        t1ez; unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        rewrite ?Z.mod_small by lia;
        first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
              | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
    end.
  Ltac t1dj := unfold flat, estart, elenZ; cbn [a_base a_off]; t1ez;
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64 in *;
    Z.div_mod_to_equations; lia.
  Ltac t1side :=
    lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- branch_taken _ _ _ = _ => try t1br
    | |- flat _ _ _ /\ _ => try t1dj
    | |- flat _ _ _ => idtac
    | |- exists _, _ => idtac
    | _ => try (unfold KXGoM.apart in *; lia)
    end.

  Ltac t1ctx HF :=
    let HF0 := fresh "HF0" in pose proof HF as HF0;
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM);
    pose proof (A2 ax2_sp_bounds) as SB; pose proof (A2 ax2_unp' _ MU) as (UDT' & UDB' & USB');
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6); pose proof (A2 ax2_outb) as OB;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR;
    pose proof TOK as (TL & TC & TCK); unfold HUF_TABLELOG_MAX in TL;
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia);
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia);
    pose proof (ax2_x2tab_fact _ (DT + 4) cells tl TOK ltac:(rewrite <- ECB; exact CBS)) as TAB;
    unfold HUF_DEC_STACK_A in LOS;
    unfold ABase.AIMG_HI, KLS in *; try unfold AIMG_HI in *.

  Ltac t1lits k :=
    unfold ax2_st;
    let p := eval cbv in (AHUF_DX2_1X + k) in change (AHUF_DX2_1X + k) with p;
    let a := eval cbv in (2^61) in change (2^61) with a;
    let b := eval cbv in (2^31 - 2^15) in change (2^31 - 2^15) with b;
    try replace (- DT - 5) with (-1 * DT + -5) by lia.

  Ltac t1pc := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?e) _ _ _ _) => eval cbv in (e - AHUF_DX2_1X) end.

  Ltac t1walk SL :=
    repeat lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let K := fresh "K" in destruct c eqn:K; cbv iota
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
        let o := t1pc in
        let s := eval cbv in (orb (existsb (Z.eqb o) SL) (Z.leb 5300 o)) in
        lazymatch s with true => fail | false => zstep end
    end.

  Ltac t1kz :=
    repeat match goal with
    | K : ?c = ?b |- _ =>
        lazymatch c with context [bv_ltu] => idtac | context [bv_eqb] => idtac end;
        lazymatch b with true => idtac | false => idtac end;
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

  Ltac t1ezu := t1ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64 in *;
    change (3 mod 64) with 3 in *; rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8 in *.
  Ltac t1zl := Z.div_mod_to_equations; lia.

  Lemma t1_idx : forall E a s, bv_unsigned (edenot E s) mod 64 = 64 - tl -> 1 <= tl <= 12 ->
    0 <= bv_unsigned (edenot E (EAlu ALU_SRL a s)) < 2^tl.
  Proof using.
    intros E a s H T. clear - H T. cbn [edenot]. rewrite u_srl64, H.
    pose proof (bv_unsigned_in_range 64 (edenot E a)) as R. unfold bv_modulus in R. change (Z.of_N 64) with 64 in R.
    split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] |].
    apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
    rewrite <- Z.pow_add_r by lia. replace (64 - tl + tl) with 64 by lia. lia.
  Qed.

  Ltac t1ix :=
    repeat match goal with |- context [bv_unsigned (edenot ?E (EAlu ALU_SRL ?a ?s))] =>
      let B := fresh "IXB" in let v := fresh "ix" in
      pose proof (t1_idx E a s ltac:(t1ezu; t1zl) ltac:(lia)) as B;
      set (v := bv_unsigned (edenot E (EAlu ALU_SRL a s))) in *; clearbody v
    end.
  Ltac t1z := cbn [a_base a_off]; t1ezu; unfold ASHOFF in *; t1zl.
  Ltac t1dj2 := unfold flat, estart, elenZ; cbn [a_base a_off]; t1ezu; t1ix; t1z.

  Lemma t1_rd : forall (m : amem) E (a : saddr) A (bs : list byte) k,
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
  Ltac t1clr :=
    repeat match goal with
    | H : know_ok _ _ _ _ |- _ => clear H
    | H : log_flat _ _ |- _ => clear H
    | H : forall j, (j < _)%nat -> ev _ j = _ |- _ => clear H
    end;
    repeat match goal with X := kx_env _ _ |- _ => clear X end;
    repeat match goal with X := kx_vals _ _ _ _ |- _ => clear X end.

  Ltac t1only := lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "S1LEFT" g end.
  Ltac t1rd1 H := eapply t1_rd; [exact (proj2 (proj1 H)) | unfold estart; t1z
                  | unfold estart; rewrite cells_bytes_length by exact (proj1 (proj1 H)); cbn [cells_size csize]; t1z].
  Ltac t1rdc := lazymatch goal with |- exists bs, rdn _ _ (adenot _ {| a_base := _; a_off := ?o |}) _ = Some bs =>
    first [ lazymatch goal with H : rw_cells _ _ (_ + o) _ |- _ => t1rd1 H end
          | match goal with H : rw_cells _ _ _ _ |- _ => t1rd1 H end
          | match goal with H : bytes_at _ _ _ _ |- _ =>
              eapply t1_rd; [exact H | unfold estart; t1z | unfold estart; rewrite ?length_map; t1z] end ] end.
  Ltac t1side2 := t1side; try t1rdc;
    try (lazymatch goal with |- flat _ _ _ => t1dj end);
    try (lazymatch goal with |- flat _ _ _ => t1dj2 | |- flat _ _ _ /\ _ => t1dj2 end);
    try (lazymatch goal with
         | |- evtF _ _ _ _ => fail
         | |- branch_taken _ _ _ = _ => fail
         | _ => intros; unfold zlen in *; rewrite ?length_map in *; lia end).

  Ltac t1krf v :=
    lazymatch goal with HK : know_ok _ ?E ?mb ?kn |- _ =>
      let f := constr:(fun e : kentry => match e with KRange (EVar w) _ _ => Nat.eqb w v | _ => false end) in
      let r := eval vm_compute in (List.find f kn) in
      lazymatch r with Some ?e =>
        let KR := fresh "KR" in
        assert (KR : kentry_ok bsegs E mb e)
          by (apply (proj1 (@List.Forall_forall _ (kentry_ok bsegs E mb) kn) HK); clear HK;
              cbn [In]; repeat (first [left; reflexivity | right]));
        cbn [kentry_ok edenot] in KR
      end
    end.

  Ltac t1fz := lazymatch goal with |- evtF _ _ _ _ => idtac | |- _ => fail 1 "t1fz: goal left after a post step" end.

  Ltac t1post S C F M L :=
    kx_post_regs;
    lazymatch goal with
    | |- context [mem_denot _ _ []] => cbn [mem_denot]
    | _ =>
      let D1 := fresh "D1" in let D2 := fresh "D2" in let D3 := fresh "D3" in
      pose proof DJ1 as D1; pose proof DJ2 as D2; pose proof DJ3 as D3; unfold KXGoM.apart in D1, D2, D3;
      let LSM := fresh "LSM" in assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity);
      kx_cells_post; t1fz;
      kx_frame S; t1fz; kx_frame C; t1fz; kx_frame F; t1fz; kx_munch M; t1fz;
      let b := fresh "buf" in let o := fresh "OUT" in let lb := fresh "LB" in
      lazymatch goal with H : u8arr bsegs ?m DST (map _ ?bb), HL : log_flat _ _ |- _ =>
        destruct (kx_u8arr_ex bsegs _ m _ DST bb H HL) as (b & o & lb); clear H end;
      kx_post_mem_free; t1fz;
      lazymatch goal with |- context [mem_denot ?E ?m0' ?l] =>
        let mm' := fresh "mm" in let EM := fresh "EM" in remember (mem_denot E m0' l) as mm' eqn:EM; clear EM end;
      unfold zlen in L; rewrite <- lb in L; clear lb D1 D2 D3 LSM
    end.

  Ltac t1remk :=
    repeat match goal with H : ztab_fact _ _ _ _ _ _ |- _ => clear H end;
    lazymatch goal with C : bytes_at bsegs ?m (DT + 4) cbs |- _ =>
      let T := fresh "TAB" in pose proof (ax2_x2tab_fact _ (DT + 4) cells tl TOK ltac:(rewrite <- ECB; exact C)) as T end;
    repeat match goal with H : unpoisoned ?m _ _ |- _ => lazymatch m with m0 => fail | _ => clear H end end;
    lazymatch goal with M : munch _ m0 ?m |- _ =>
      let u1 := fresh "UDT'" in let u2 := fresh "UDB'" in let u3 := fresh "USB'" in
      pose proof (A2 ax2_unp' _ M) as (u1 & u2 & u3) end.

  Ltac t1lit :=
    repeat match goal with |- context [bv_unsigned (Z_to_bv 64 (Zpos ?p))] =>
      change (bv_unsigned (Z_to_bv 64 (Zpos p))) with (Zpos p) end.

  Ltac t1xf :=
    unfold AX2F; split; [eexists; split; [eassumption | unfold zlen in *; first [eassumption | lia]] |];
    repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption].

  Ltac t1r2 k D j X :=
    let s1 := eval cbv in (AHUF_DX2_1X + k) in
    ax2b_runD [s1] 80%nat D
      [KZRange X 0 4095; KZRange (2^tl - X - 1) 0 4095; KZRange (2^tl) 2 4096; KZRange tl 1 12; KZRange mtl 1 12;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
       KZWr (DST + j) 1; KZWr (SP + -104) 8; KZWr (SP + -96) 4;
       KZDisj (DST + j) 1 (DT + 4) (4 * 2^tl); KZDisj (DST + j) 1 (SP + -104) 40;
       KZDisj (SP + -104) 40 (DT + 4) (4 * 2^tl);
       KZRange DT 0 (2^47); KZRange DST 0 (2^47); KZRange j 0 (2^32); KZRange dcap 1 (2^32);
       KZRange (dcap - j) 1 (2^32); KZRange (DST + j) 0 (2^47); KZRange SP 0 (2^47)]
      [(DT + 4, 4 * 2^tl)]
      [(DT + 4, 4 * 2^tl); (DST + j, 1); (SP + -112, 112)]
      [(DT + 4, 4 * 2^tl); (DST + j, 1)].

  Ltac t1remv v w R :=
    try (lazymatch goal with |- context [edenot ?E (EVar v)] => change (edenot E (EVar v)) with (ev E v) in * end);
    lazymatch goal with |- context [ev ?E v] =>
      let EW := fresh "EW" in remember (ev E v) as w eqn:EW; clear EW end;
    pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; cbn in R.

  Lemma t1_last : forall mm j cw bcw pad pw (x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    TXF mm -> TBD mm cw bcw pad pw -> 0 <= j < dcap ->
    evtF bsegs RNG POST (TST 4776 mm x1 x5 x6 x7 (ZB (DST + j)) x10 x11 x12 PE DL x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Proof using All.
    intros mm j cw bcw pad pw x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 HF HBD HJ.
    t1ctx HF. destruct (B6 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
    pose proof (WDB ltac:(lia)) as WDB'; pose proof (WDBS ltac:(lia)) as WDBS'.
    kx_cells_split HBD.
    t1lits 4776.
    let s1 := eval cbv in (AHUF_DX2_1X + 4804) in
    ax2b_runD [s1] 20%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange tl 1 12; KZRange mtl 1 12;
       KZWr (SP + -104) 8; KZWr (SP + -96) 4;
       KZRange DT 0 (2^47); KZRange DST 0 (2^47); KZRange j 0 (2^32); KZRange dcap 1 (2^32);
       KZRange (dcap - j) 1 (2^32); KZRange (DST + j) 0 (2^47); KZRange SP 0 (2^47)]
      (@nil (Z * Z)) [(SP + -112, 112)] (@nil (Z * Z)).
    all: t1side2.
    all: t1only.
    kx_post_regs. cbn [mem_denot].
    lazymatch goal with |- context [edenot ?E (EAlu ALU_SRL ?a ?s)] =>
      let IXB := fresh "IXB" in
      pose proof (t1_idx E a s ltac:(t1ezu; t1zl) ltac:(lia)) as IXB;
      let X := fresh "X" in
      set (X := bv_unsigned (edenot E (EAlu ALU_SRL a s))) in *;
      assert (EXw : edenot E (EAlu ALU_SRL a s) = ZB X) by (unfold X; symmetry; apply Z_to_bv_bv_unsigned);
      rewrite EXw; clear EXw; clearbody X
    end.
    t1clr.
    let s1 := eval cbv in (AHUF_DX2_1X + 5256) in
    ax2b_runD [s1] 80%nat [false]
      [KZRange X 0 4095; KZRange (2^tl - X - 1) 0 4095; KZRange (2^tl) 2 4096; KZRange tl 1 12; KZRange mtl 1 12;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
       KZWr (DST + j) 1; KZWr (SP + -104) 8; KZWr (SP + -96) 4;
       KZDisj (DST + j) 1 (DT + 4) (4 * 2^tl); KZDisj (DST + j) 1 (SP + -104) 40;
       KZDisj (SP + -104) 40 (DT + 4) (4 * 2^tl);
       KZRange DT 0 (2^47); KZRange DST 0 (2^47); KZRange j 0 (2^32); KZRange dcap 1 (2^32);
       KZRange (dcap - j) 1 (2^32); KZRange (DST + j) 0 (2^47); KZRange SP 0 (2^47)]
      [(DT + 4, 4 * 2^tl)]
      [(DT + 4, 4 * 2^tl); (DST + j, 1); (SP + -112, 112)]
      [(DT + 4, 4 * 2^tl); (DST + j, 1)].
    all: t1side2.
    all: t1only.
    t1krf 34%nat.
    t1post SRCB CBS FRC MU LBF.
    lazymatch goal with KR : _ <= bv_unsigned (ev ?E 34) <= _ |- _ =>
      try change (edenot E (EVar 34)) with (ev E 34) in *;
      remember (ev E 34) as w34 eqn:EW34; clear EW34 end.
    assert (W34 : w34 = ZB 1 \/ w34 = ZB 2).
    { destruct (Z.eq_dec (bv_unsigned w34) 1); [left | right]; apply bv_eq; rewrite Z_to_bv_unsigned;
      unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite Z.mod_small by lia; lia. }
    t1clr.
    t1remk.
    destruct W34 as [W34 | W34]; subst w34; t1lit.
    - t1r2 5256%Z (repeat false 64) j X.
      all: t1side2.
      all: t1only.
      t1post SRCB CBS FRC MU LBF.
      eapply (A2 ax2_end'); [t1xf | kx_cells_merge].
    - t1r2 5256%Z (@nil bool) j X.
      all: t1side2.
      all: t1only.
      t1post SRCB CBS FRC MU LBF.
      t1remv 33%nat bc RBC.
      t1clr.
      t1remk.
      destruct (Z_lt_le_dec 63 (bv_unsigned bc)) as [BC | BC].
      + t1r2 5256%Z (true :: repeat false 63) j X.
        all: t1side2.
        all: t1only.
        t1post SRCB CBS FRC MU LBF.
        eapply (A2 ax2_end'); [t1xf | kx_cells_merge].
      + t1r2 5256%Z [false] j X.
        all: t1side2.
        all: t1only.
        t1post SRCB CBS FRC MU LBF.
        lazymatch goal with |- context [edenot ?E (EAluw ALU_ADD ?a ?b)] =>
          remember (edenot E (EAluw ALU_ADD a b)) as sw eqn:ESW; clear ESW end.
        pose proof (bv_unsigned_in_range 64 sw) as RSW; unfold bv_modulus in RSW; cbn in RSW.
        t1clr.
        t1remk.
        destruct (Z_lt_le_dec (bv_unsigned sw) 64) as [SW | SW].
        * t1r2 5256%Z (true :: repeat false 63) j X.
          all: t1side2.
          all: t1only.
          t1post SRCB CBS FRC MU LBF.
          eapply (A2 ax2_end'); [t1xf | kx_cells_merge].
        * t1r2 5256%Z (repeat false 64) j X.
          all: t1side2.
          all: t1only.
          t1post SRCB CBS FRC MU LBF.
          eapply (A2 ax2_end'); [t1xf | kx_cells_merge].
  Time Qed.

  Lemma ax2_goal_4772_ok : G2 ax2_goal_4772.
  Proof using All.
    unfold ax2_goal_4772.
    intros mm j cw bcw pad pw x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 HF HBD HJ.
    pose proof HF as HF0.
    pose proof (A2 ax2_outb) as OB. pose proof (A2 ax2_sp_bounds) as SB.
    unfold ABase.AIMG_HI, KLS in *; try unfold AIMG_HI in *.
    unfold ax2_st.
    t1walk [4776; 5256].
    all: let o := t1pc in
      lazymatch o with
      | 4776 => t1kz; eapply t1_last; [exact HF0 | exact HBD | lia]
      | 5256 => eapply (A2 ax2_end'); [exact HF0 | exact HBD]
      | _ => exfalso; t1kz; lia
      end.
  Time Qed.

  Lemma t1_loop : forall (k : nat) mm j cw bcw pad pw (x1 x7 x10 x11 x12 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    dcap - j <= Z.of_nat k -> TXF mm -> TBD mm cw bcw pad pw -> 0 <= j -> j + 2 <= dcap ->
    evtF bsegs RNG POST (TST 4936 mm x1 (ZB (- DT - 5)) (ZB (64 - tl)) x7 (ZB (DST + j)) x10 x11 x12 PE DL
                                (ZB (DST + dcap - 2)) x18 x20 x21 x22 x28 x29 x30 x31).
  Proof using All.
    induction k as [|k IH]; intros mm j cw bcw pad pw x1 x7 x10 x11 x12 x18 x20 x21 x22 x28 x29 x30 x31 HKJ HF HBD HJ HJ2;
      [lia|].
    t1ctx HF. destruct (B6 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
    pose proof (WDB ltac:(lia)) as WDB'; pose proof (WDBS ltac:(lia)) as WDBS'.
    kx_cells_split HBD.
    t1lits 4936.
    let s1 := eval cbv in (AHUF_DX2_1X + 5116) in
    ax2b_runD [s1] 120%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange tl 1 12;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
       KZWr (DST + j) 2; KZWr (SP + -104) 8; KZWr (SP + -96) 4;
       KZDisj (DST + j) 2 (DT + 4) (4 * 2^tl); KZDisj (DST + j) 2 (SP + -104) 40;
       KZDisj (SP + -104) 40 (DT + 4) (4 * 2^tl);
       KZRange DT 0 (2^47); KZRange DST 0 (2^47); KZRange j 0 (2^32); KZRange dcap 2 (2^32);
       KZRange (dcap - j) 2 (2^32); KZRange (DST + j) 0 (2^47); KZRange SP 0 (2^47)]
      [(DT + 4, 4 * 2^tl)]
      [(DT + 4, 4 * 2^tl); (DST + j, 2); (SP + -112, 112)]
      [(DT + 4, 4 * 2^tl); (DST + j, 2)].
    all: t1side2.
    all: t1only.
    t1krf 38%nat.
    t1post SRCB CBS FRC MU LBF.
    lazymatch goal with KR : _ <= bv_unsigned (ev ?E 38) <= _ |- _ =>
      try change (edenot E (EVar 38)) with (ev E 38) in *;
      remember (ev E 38) as w38 eqn:EW38; clear EW38 end.
    assert (W38 : w38 = ZB 1 \/ w38 = ZB 2).
    { destruct (Z.eq_dec (bv_unsigned w38) 1); [left | right]; apply bv_eq; rewrite Z_to_bv_unsigned;
      unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite Z.mod_small by lia; lia. }
    t1clr.
    t1remk.
    destruct (Z_le_gt_dec (j + bv_unsigned w38) (dcap - 2)) as [LC | LC];
      destruct W38 as [W38 | W38]; subst w38; t1lit;
      repeat match goal with H : context [bv_unsigned (Z_to_bv 64 (Zpos ?p))] |- _ =>
        change (bv_unsigned (Z_to_bv 64 (Zpos p))) with (Zpos p) in H end.
    all: let s1 := eval cbv in (AHUF_DX2_1X + 4936) in let s2 := eval cbv in (AHUF_DX2_1X + 4772) in
      let D := lazymatch type of LC with _ <= _ => constr:(true :: repeat false 63) | _ > _ => constr:(repeat false 64) end in
      ax2b_runD [s1; s2] 20%nat D
        [KZRange (2^tl) 2 4096; KZRange tl 1 12; KZRange mtl 1 12;
         KZWr (SP + -104) 8; KZWr (SP + -96) 4;
         KZRange DT 0 (2^47); KZRange DST 0 (2^47); KZRange j 0 (2^32); KZRange dcap 2 (2^32);
         KZRange (dcap - j) 2 (2^32); KZRange (DST + j) 0 (2^47); KZRange SP 0 (2^47)]
        (@nil (Z * Z)) [(SP + -112, 112)] (@nil (Z * Z)).
    all: t1side2.
    all: t1only.
    all: t1post SRCB CBS FRC MU LBF.
    all: try replace (dcap + DST + -2) with (DST + dcap - 2) by lia;
      try replace (dcap + DST) with (DST + dcap) by lia;
      try replace (- DT + -5) with (- DT - 5) by lia;
      try replace (- tl + 64) with (64 - tl) by lia;
      try replace (DST + j + 1) with (DST + (j + 1)) by lia;
      try replace (DST + j + 2) with (DST + (j + 2)) by lia.
    all: let o := t1pc in
      lazymatch o with
      | 4936 => eapply IH; [lia | t1xf | kx_cells_merge | lia | lia]
      | 4772 => pose proof ax2_goal_4772_ok as G4; unfold ax2_goal_4772 in G4; eapply G4; [t1xf | kx_cells_merge | lia]
      end.
  Time Qed.

  Lemma ax2_goal_4768_ok : G2 ax2_goal_4768.
  Proof using All.
    unfold ax2_goal_4768.
    intros mm j cw bcw pad pw x1 x7 x10 x11 x12 x18 x20 x21 x22 x28 x29 x30 x31 HF HBD HD HJ.
    pose proof HF as HF0.
    pose proof (A2 ax2_outb) as OB. pose proof (A2 ax2_sp_bounds) as SB.
    unfold ABase.AIMG_HI, KLS in *; try unfold AIMG_HI in *.
    unfold ax2_st.
    t1walk [4936; 4772].
    all: let o := t1pc in
      lazymatch o with
      | 4936 => t1kz; eapply (t1_loop (Z.to_nat (dcap - j))); [lia | exact HF0 | exact HBD | lia | lia]
      | 4772 => t1kz; pose proof ax2_goal_4772_ok as G4; unfold ax2_goal_4772 in G4; eapply G4; [exact HF0 | exact HBD | lia]
      | _ => exfalso; t1kz; lia
      end.
  Time Qed.

End AX2B.
End CANSEC1.
