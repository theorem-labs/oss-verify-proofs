(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2 HufWalkKit3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell KXCell2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_ax2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax2e () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions8bv_swrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr06K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC59OSSVerify5KrLib6Common5KXTac4zregC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib6Common4KXGo>Forall_map_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac4ztabC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac4zshzC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW:AF_huf_ax24AX2MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<AH_huf_iface=huf_dec_postAC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib5BothW:AF_huf_ax27ax2_unpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<AH_huf_iface<DTABLE_BYTESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AF_huf_ax2:ax2_blocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib5BothW:AF_huf_ax2=ax2_sp_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AF_huf_ax28ax2_outbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX2;x2_table_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount7ZlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib4Spec=HufPure_HufX2:x2_cell_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM5apartC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib3Lib8RunConst:ATOP_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AF_huf_ax27ax2_tabC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib6Common5KXTac9ztab_factC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib6Common5KXTac2kEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS9kentry_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8KXBridge4zexp02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common5KXTac2zk08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8KXBridge4zexp01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8KXBridge4zexp04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common5KXTac2zk01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8KXBridge4zexp03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8KXBridge4zexp05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common5KXTac2zk09C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common5KXTac2zk04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common5KXTac2zk03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo;atom_rangesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac6zk_entC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge4zdenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo;zk_range_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX25saddr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac3zsaC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib6Common4KXGo8zk_wr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM9apart_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo:zk_disj_okC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib6Common4KXGo>atom_ranges_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX28sidecond03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX28sidecond05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac9idx_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac6zle_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac<idx_facts_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib6Common7KXSound3KXS7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac6shz_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo6shz_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac6tab_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac3zleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo5zt_okC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib6Common4KXGo7tabs_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac9region_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib6Common5KXTac6zr_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo>zr_ok_bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoF6win_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoF5zw_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM6unp_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM5zu_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM8unp_raccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM:zur_ok_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoF8shz_raccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGoCForall2_map_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge9zatoms_ltC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C59OSSVerify5KrLib6Common8KXBridge:kx_regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge2zxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge5lnormC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge4mkRlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge7kx_valsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge6kx_envC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac7kE_atomC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common6KXExec3KX22evC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX29sym_state01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX27scripts01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXChk8kxl_execC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge<reads_scopedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM6rv_chkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM9rv_chk_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXChk5rv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXChk>kxl_know_finalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge:rfull_mkRlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM8sc_auto3C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC69OSSVerify5KrLib6Common7KXSound3KXS9scs_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS8sc_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM<kx_scs_bulk3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM9acc_auto3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXFoot4accPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM@kx_accs_ok_part3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS8log_flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost<kx_regs_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS9mem_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem;kx_u8arr_exC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost;kx_log_in_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost<kx_log_in_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost7win_ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem:log_insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX26a_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost2ezC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX25a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS5elenZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula02C56Stdlib5Arith8PeanoNat3Nat3ltbC69OSSVerify5KrLib6Common7KXSound3KXS9elenZ_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost<estart_ez_kEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost?log_inside_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem<kx_munch_logC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib6Common5KXMem:kx_stk_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem<kx_wmono_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost;kx_log_wr_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost<kx_log_wr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem>kx_mem_inv_logC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos;of_succ_natK47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib6Common6KXExec3KX26erangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost<kx_erange_evC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib4LibA5StepF9stepF_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltK4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib5BothW;AF_huf_ax2c9ax2_closeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge7kx_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost8kE_atomsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost?kx_regs_keep_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXChk<kx_run_evtFLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM<kx_pendingFmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06K69OSSVerify5KrLib6Common6KXExec3KX24expr05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K69OSSVerify5KrLib6Common6KXExec3KX28sidecond06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX28sidecond01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202K69OSSVerify5KrLib6Common6KXExec3KX26sentry01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C59OSSVerify5KrLib6Common6KXPost7kx_pickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I59OSSVerify5KrLib6Common5KXTac2zk00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I69OSSVerify5KrLib6Common6KXExec3KX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop02I69OSSVerify5KrLib6Common6KXExec3KX28sidecond00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8KXBridge4zexp00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX24expr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I69OSSVerify5KrLib6Common6KXExec3KX26sentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5BothW5ABase3KLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX1@HUF_TABLELOG_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec=HufPure_HufX26deltX200C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX2:x2_defaultC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib3Lib8RunConst8ATOP_MINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst8ATOP_MAXC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00K4ELinuxProcessSemantics5Riscv5Instr5aluop03I69OSSVerify5KrLib6Common6KXExec3KX23env00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX29sym_state00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib6Common6KXPost9kx_mul_m1C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5BothW;AF_huf_ax2e9ax2_l4decC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsc59OSSVerify5KrLib5BothW;AF_huf_ax2e>ax2_signed_litC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapK4ELinuxProcessSemantics5Riscv5Instr5instr0<C59OSSVerify5KrLib3Lib8PropExec7v_srliwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu32C59OSSVerify5KrLib3Lib8PropExec7w_srliwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib3Lib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc59OSSVerify5KrLib5BothW;AF_huf_ax2e8ax2_l4rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_ax2c:ax2_srliw3C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib3Lib8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3b2zK4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib3Lib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=C59OSSVerify5KrLib3Lib8PropExec6v_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6w_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4lxorK4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5aluop06C47Corelib4Init5Logic8iff_reflc59OSSVerify5KrLib5BothW;AF_huf_ax2e:ax2_l4headC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z8inj_succ".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section AX2E.
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Notation XA l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs) (only parsing).
  Notation XST := (ax2_st sp gp tp s7 s8 s9 s10 s11 FR fc dcap DT).
  Notation XBD := (ax2_bd sp SS).
  Notation XF := (AX2F ra sp s0 s1 s2 s3 s4 s5 s6 m0 DST dcap SS DT lo src cbs).
  Notation PINV P := (P = SS \/ (SS + 1 <= P /\ P + 8 <= SS + n)).
  Notation ZB z := (Z_to_bv 64 z).
  Notation PE := (Z_to_bv 64 (DST + dcap)).
  Notation DL := (Z_to_bv 64 (tl + 256 * mtl)).

  Ltac x4ez :=
    try lazymatch goal with
    | |- context [edenot ?E _] =>
        let b := eval unfold E in E in
        lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
          rewrite ?(ez_ok zv E (kE_atoms zv xs));
          let na := eval vm_compute in (length zv) in
          cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
        end
    end.
  Ltac x4br :=
    lazymatch goal with
    | |- branch_taken _ _ _ = _ =>
        x4ez; unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        rewrite ?Z.mod_small by lia;
        first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
              | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
    end.
  Lemma x4_srlw3 : forall E a, 0 <= bv_unsigned (edenot E a) < 2^31 ->
    bv_unsigned (edenot E (EAluw ALU_SRL a (ELit 3))) = bv_unsigned (edenot E a) / 8.
  Proof using.
    intros E a H. clear - H. cbn [edenot].
    rewrite (u_srlw_small (edenot E a) (Z_to_bv 64 3) 3); [reflexivity | reflexivity | lia |].
    change (2 ^ (3 mod 32)) with 8. apply Z.div_lt_upper_bound; lia.
  Qed.
  Lemma x4_srlw_srl : forall E a, 0 <= bv_unsigned (edenot E a) < 2^31 ->
    edenot E (EAlu ALU_SRL a (ELit 3)) = edenot E (EAluw ALU_SRL a (ELit 3)).
  Proof using.
    intros E a H. clear - H. apply bv_eq. rewrite u_srl_lit, (x4_srlw3 E a H). reflexivity.
  Qed.
  Ltac x4w :=
    repeat match goal with
    | |- context [edenot ?E ?e] =>
        match e with context [EAluw ALU_SRL ?a (ELit 3)] =>
          rewrite <- (esubst_sound E (EAluw ALU_SRL a (ELit 3)) (EAlu ALU_SRL a (ELit 3)) e)
            by (apply x4_srlw_srl; x4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
                change (Z.of_N 64) with 64; rewrite Z.mod_small by lia; lia);
          let e' := eval vm_compute in (esubst (EAluw ALU_SRL a (ELit 3)) (EAlu ALU_SRL a (ELit 3)) e) in
          change (esubst (EAluw ALU_SRL a (ELit 3)) (EAlu ALU_SRL a (ELit 3)) e) with e'
        end
    end.
  Ltac x4ezu := x4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64 in *;
    change (3 mod 64) with 3 in *; rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8 in *.
  Ltac x4z := cbn [a_base a_off]; x4ezu;
    rewrite ?x4_srlw3 by (x4ezu; rewrite Z.mod_small by lia; lia); x4ezu;
    unfold ASHOFF in *; Z.div_mod_to_equations; lia.
  Ltac x4zshow := cbn [a_base a_off]; x4ezu;
    rewrite ?x4_srlw3 by (x4ezu; rewrite Z.mod_small by lia; lia); x4ezu; unfold ASHOFF in *.
  Lemma x4_idx : forall E a s, bv_unsigned (edenot E s) = 64 - tl -> 1 <= tl <= 12 ->
    0 <= bv_unsigned (edenot E (EAlu ALU_SRL a s)) < 2^tl.
  Proof using.
    intros E a s H T. clear - H T. cbn [edenot]. rewrite u_srl64, H, Z.mod_small by lia.
    pose proof (bv_unsigned_in_range 64 (edenot E a)) as R. unfold bv_modulus in R. change (Z.of_N 64) with 64 in R.
    split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] |].
    apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
    rewrite <- Z.pow_add_r by lia. replace (64 - tl + tl) with 64 by lia. lia.
  Qed.
  Ltac x4ix :=
    repeat match goal with |- context [bv_unsigned (edenot ?E (EAlu ALU_SRL ?a ?s))] =>
      let B := fresh "IXB" in let v := fresh "ix" in
      pose proof (x4_idx E a s ltac:(x4ezu; rewrite Z.mod_small by lia; lia) ltac:(lia)) as B;
      set (v := bv_unsigned (edenot E (EAlu ALU_SRL a s))) in *; clearbody v
    end.
  Ltac x4dj := unfold flat, estart, elenZ; cbn [a_base a_off]; x4ezu; x4ix; x4z.
  Lemma x4_rd : forall (m : amem) E (a : saddr) A (bs : list byte) k,
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
  Ltac x4rd H := eapply x4_rd; [exact H | unfold estart; x4z | unfold estart; rewrite ?length_map; x4z].
  Ltac x4zl := Z.div_mod_to_equations; lia.
  Ltac x4zs := rewrite ?Z.shiftr_div_pow2 by lia;
    repeat match goal with |- context [?a mod 64] => rewrite (Z.mod_small a 64) by lia end;
    repeat match goal with |- context [2 ^ ?k] =>
      let v := eval vm_compute in (2 ^ k) in tryif is_Zlit v then change (2 ^ k) with v else fail end.
  Ltac x4dec :=
    repeat match goal with
    | |- context [Z.lxor ?x ?y <? 1] =>
        replace (Z.lxor x y <? 1) with false by
          (symmetry; apply Z.ltb_ge;
           assert (0 <= Z.lxor x y) by (apply (proj2 (Z.lxor_nonneg x y)); split; intro; x4zl);
           assert (Z.lxor x y <> 0) by (rewrite Z.lxor_eq_0_iff; x4zl); lia)
    | |- context [?a =? ?b] =>
        first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; x4zl)
              | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; x4zl) ]
    | |- context [?a <? ?b] =>
        first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; x4zl)
              | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; x4zl) ]
    end.
  Ltac x4ev :=
    unfold branch_taken; cbn [edenot]; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?bv_lts_lxor;
    repeat (rewrite ?u_add64, ?u_sub64, ?u_and64, ?u_xor64, ?u_sltu64, ?u_srl64, ?u_sll64, ?u_mul64, ?u_lit64);
    repeat (lazymatch goal with |- context [ev ?E ?j] =>
      lazymatch goal with KA : forall j, _ -> ev E j = _ |- _ => rewrite (KA j) by (vm_compute; lia) end end);
    cbn [nth]; rewrite ?u_lit64; unfold two64;
    repeat match goal with |- context [?a mod 64] => rewrite (Z.mod_small a 64) by lia end;
    repeat match goal with |- context [?a mod 2 ^ ?k] => rewrite (Z.mod_small a (2 ^ k)) by x4zl end;
    repeat match goal with |- context [2 ^ ?k] =>
      let v := eval vm_compute in (2 ^ k) in tryif is_Zlit v then change (2 ^ k) with v else fail end;
    x4dec; cbn iota; try reflexivity.

  Notation S4 k mm x1 x5 x9 x10 x11 x12 x17 x18 x20 x21 x22 :=
    (XST k mm x1 x5 (ZB (DST + dcap - 7)) (ZB (- DT - 5)) x9 x10 x11 x12 PE DL x17 x18 x20 x21 x22
         (ZB 65) (ZB (64 - tl)) (ZB AX2_K8) (ZB 8)).
  Definition x4_s2272 (j : Z) : Prop := forall mm bc P cont cw pad,
    XF mm -> XBD mm cw bc pad P -> 0 <= j <= dcap -> 1 <= dcap -> 0 <= bc <= 64 -> PINV P ->
    forall (x1 x10 x12 x18 x20 x21 x22 : word),
    evtF bsegs RNG POST (S4 2272 mm x1 (ZB bc) (ZB (DST + j)) x10 (ZB P) x12 cont x18 x20 x21 x22).
  Definition x4_h2272 (jb : Z) : Prop := forall j, jb < j <= dcap -> x4_s2272 j.
  Definition x4_g2724 (j : Z) : Prop := forall mm bc P fl cont cw pad,
    XF mm -> XBD mm cw bc pad P -> 0 <= j <= dcap -> 1 <= dcap -> PINV P ->
    (fl = 1 /\ 0 <= bc <= 7 \/ fl = 0 /\ 0 <= bc <= 64) ->
    forall (x1 x11 x18 x20 x21 x22 : word),
    evtF bsegs RNG POST (S4 2724 mm x1 (ZB bc) (ZB (DST + j)) (ZB P) x11 (ZB fl) cont x18 x20 x21 x22).
  Definition x4_gm (k room bm jb : Z) : Prop := forall mm j bc P i cont cw pad,
    XF mm -> XBD mm cw bc pad P -> 0 <= jb < j -> j + room <= dcap -> 0 <= bc <= bm -> PINV P -> 0 <= i < 2^tl ->
    forall (x1 x12 x18 x20 x21 x22 : word),
    evtF bsegs RNG POST (S4 k mm x1 (ZB bc) (ZB (DST + j)) (ZB P) (ZB (DT + 4 * i + 4)) x12 cont x18 x20 x21 x22).
  Notation G3924 := (XA ax2_goal_3924).

  Ltac x4facts mm MU :=
    pose proof (A2 ax2_sp_bounds) as SB; pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB');
    unfold HUF_DEC_STACK_A in LOS; destruct SBB as (SB1 & SB2);
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6); destruct (B6 ltac:(lia)) as (D1 & D2 & D3 & D4);
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR; unfold AIMG_HI, KLS in *; unfold ablk, AIMG_HI, KLS in SBA;
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity);
    pose proof TOK as (TL & _ & _); unfold HUF_TABLELOG_MAX in TL;
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia);
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia);
    unfold DTABLE_BYTES, HufHarness.DT_BYTES in *.
  Ltac x4pre k :=
    unfold ax2_st; let p := eval cbv in (AHUF_DX2_1X + k) in change (AHUF_DX2_1X + k) with p;
    let v := eval vm_compute in AX2_K8 in change AX2_K8 with v;
    replace (- DT - 5) with (-1 * DT + -5) by lia;
    let v := eval vm_compute in (2^61) in change (2^61) with v;
    let v := eval vm_compute in (2^31 - 2^15) in change (2^31 - 2^15) with v.
  Ltac x4side H :=
    lazymatch goal with |- evtF _ _ _ _ => idtac | |- _ =>
      try x4w; first [ x4br | x4dj | x4rd H | x4ev | idtac ] end.

  Lemma x4_rl_a : forall mm j q r off cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    XF mm -> XBD mm cw (8 * q + r) pad (SS + off) -> 0 <= j <= dcap -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    8 <= off -> off + 8 <= n -> 1 <= dcap ->
    (forall mm' cw' pad' cont' (x11' x18' x20' x21' x22' : word),
       XF mm' -> XBD mm' cw' r pad' (SS + off - q) ->
       evtF bsegs RNG POST (S4 2724 mm' x1 (ZB r) (ZB (DST + j)) (ZB (SS + off - q)) x11' (ZB 1) cont' x18' x20' x21' x22')) ->
    evtF bsegs RNG POST (S4 2272 mm x1 (ZB (8 * q + r)) (ZB (DST + j)) x10 (ZB (SS + off)) x12 cont x18 x20 x21 x22).
  Proof using All.
    intros mm j q r off cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HJ HQ HR HBC HP1 HP2 HD1 K.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    x4facts mm MU. clear BYS TOK ECB AH HDT HOUT.
    unfold ax2_bd in HB. kx_cells_split HB.
    x4pre 2272.
    let s1 := eval cbv in (AHUF_DX2_1X + 2724) in
    kx_runFm [s1] 120%nat
      [KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n 1 (2^26); KZRange off 8 (2^26);
       KZRange (n - off) 8 (2^26); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
       KZWord (SP + -88) 8 (SS + off); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZWr (SP + -104) 8; KZWr (SP + -96) 4; KZWr (SP + -88) 8; KZDisj (SP + -104) 40 SS n;
       KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange j 0 (2^32); KZRange (dcap - j) 0 (2^32)]
      [(SS, n)] [(SS, n); (SP + -112, 112)] [(SS, n)].
    all: x4side SRCB.
    all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "SIDE" g end.
    kx_post_regs. kx_cells_post. kx_frame FRC. kx_frame SRCB. kx_frame CBS. kx_munch MU.
    lazymatch goal with H : u8arr bsegs ?m DST (map _ ?b), HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ m _ DST b H HL) as (buf' & OUT' & LB'); clear H end.
    kx_post_mem_free.
    lazymatch goal with |- context [mem_denot ?E mm ?l] => remember (mem_denot E mm l) as mm' eqn:EM; clear EM end.
    assert (EQ : bv_unsigned (edenot KXE (EAluw ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 4)) (EVar 5)) (ELit 3))) = q)
      by (rewrite x4_srlw3 by (x4ezu; rewrite Z.mod_small by lia; lia); x4ezu; rewrite Z.mod_small by lia; x4zl).
    rewrite EQ. clear EQ.
    lazymatch goal with H : rw_cells _ mm' (SP + -88) [C8 ?v] |- _ =>
      assert (EV : v = ZB (SS + off - q)) by (x4w; x4ez; f_equal; x4ezu; x4zs; x4zl); rewrite EV in H; clear EV end.
    lazymatch goal with H : rw_cells _ mm' (SP + -96) [C4 ?v] |- _ =>
      assert (EV : v = ZB r) by (x4ez; f_equal; x4ezu; x4zs; x4zl); try rewrite EV in H; clear EV end.
    replace (SS + (off + - q)) with (SS + off - q) by lia. replace (- tl + 64) with (64 - tl) by lia.
    assert (XF' : XF mm')
      by (unfold AX2F; split; [exists buf'; split; [exact OUT' | unfold zlen in *; rewrite LB'; exact LBF] |];
          repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]).
    eapply K; [exact XF' | unfold ax2_bd; kx_cells_merge |..].
    all: try lia.
    all: lazymatch goal with |- ?g => fail 0 "LEFT" g end.
  Time Qed.

  Lemma x4_rl_b : forall mm j bc cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    x4_g2724 j -> XF mm -> XBD mm cw bc pad SS -> 0 <= j <= dcap -> 0 <= bc <= 64 -> 1 <= dcap ->
    evtF bsegs RNG POST (S4 2272 mm x1 (ZB bc) (ZB (DST + j)) x10 (ZB SS) x12 cont x18 x20 x21 x22).
  Proof using All.
    intros mm j bc cont cw pad x1 x10 x12 x18 x20 x21 x22 K HF HB HJ HBC HD1.
    pose proof (K mm bc SS 0 cont cw pad HF HB HJ HD1 (or_introl eq_refl) (or_intror (conj eq_refl HBC))) as K0.
    clear K.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    x4facts mm MU. clear BYS TOK ECB AH HDT HOUT.
    unfold ax2_bd in HB. kx_cells_split HB.
    x4pre 2272.
    let s1 := eval cbv in (AHUF_DX2_1X + 2724) in
    kx_runFm [s1] 60%nat
      [KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n 1 (2^26); KZRange bc 0 64;
       KZWord (SP + -88) 8 SS; KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZWr (SP + -104) 8; KZWr (SP + -96) 4; KZWr (SP + -88) 8; KZDisj (SP + -104) 40 SS n;
       KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange j 0 (2^32); KZRange (dcap - j) 0 (2^32)]
      [(SS, n)] [(SS, n); (SP + -112, 112)] [(SS, n)].
    all: x4side SRCB.
    all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "SIDE" g end.
    kx_post_regs.
    lazymatch goal with |- context [mem_denot ?E mm []] => change (mem_denot E mm []) with mm end.
    replace (- tl + 64) with (64 - tl) by lia.
    eapply K0.
  Time Qed.

  Lemma x4_loop :
    (forall j, x4_g2724 j -> x4_s2272 j) ->
    (forall j, x4_gm 2952 6 19 j -> x4_g2724 j) ->
    (forall jb, x4_gm 3120 4 31 jb -> x4_gm 2952 6 19 jb) ->
    (forall jb, x4_gm 3288 2 43 jb -> x4_gm 3120 4 31 jb) ->
    (forall jb, x4_h2272 jb -> x4_gm 3288 2 43 jb) ->
    forall j, x4_s2272 j.
  Proof using All.
    intros RL B1 M2 M3 M4.
    assert (IND : forall k : nat, forall j, dcap - j < Z.of_nat k -> x4_s2272 j).
    { induction k as [|k IH]; intros j Hj.
      - unfold x4_s2272. intros. exfalso. lia.
      - apply RL, B1, M2, M3, M4. intros j' Hj'. apply IH. lia. }
    intros j. apply (IND (S (Z.to_nat (dcap - j)))). lia.
  Time Qed.

  Lemma x4_top : (forall j, x4_s2272 j) -> XA ax2_goal_2272.
  Proof using All.
    intros H. unfold ax2_goal_2272. intros mm j bc P cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD HJ HBC HP.
    exact (H j mm bc P cont cw pad HF HB HJ HD HBC HP x1 x10 x12 x18 x20 x21 x22).
  Time Qed.

  Ltac x4m_run mm MU CBS k :=
    pose proof (A2 ax2_outb) as OB; x4facts mm MU; pose proof (A2 ax2_tab mm CBS) as TB;
    pose proof (WDB ltac:(lia)) as WDB'; pose proof (WDBS ltac:(lia)) as WDBS';
    clear BYS TOK ECB AH HDT HOUT;
    lazymatch goal with HB : XBD _ _ _ _ _ |- _ => unfold ax2_bd in HB; kx_cells_split HB end;
    x4pre k.
  Ltac x4sd := lazymatch goal with |- evtF _ _ _ _ => idtac | |- _ => unfold KXGoM.apart in *; rewrite ?LCB; lia end.
  Ltac x4m_post FRC SRCB CBS MU LBF bc j :=
    let RNB := fresh "RNB" in let RLN := fresh "RLN" in
    lazymatch goal with |- context [ZB (bc + bv_unsigned (ev ?E ?a))] => kx_range (EVar a) RNB end;
    lazymatch goal with |- context [ZB (DST + (j + bv_unsigned (ev ?E ?a)))] => kx_range (EVar a) RLN end;
    kx_cells_post; x4sd; kx_frame FRC; x4sd; kx_frame SRCB; x4sd; kx_frame CBS; x4sd; kx_munch MU; x4sd;
    let buf' := fresh "buf'" in let OUT' := fresh "OUT'" in let LB' := fresh "LB'" in
    lazymatch goal with H : u8arr bsegs ?m DST (map _ ?b), HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ m _ DST b H HL) as (buf' & OUT' & LB'); clear H end;
    kx_post_mem_free;
    let m' := fresh "mm'" in let EM := fresh "EM" in
    lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m' eqn:EM; clear EM end;
    lazymatch goal with |- context [ZB (bc + ?nb)] =>
      lazymatch goal with H : rw_cells _ m' (SP + -96) [C4 ?v] |- _ =>
        let EV := fresh "EV" in
        assert (EV : v = ZB (bc + nb)) by (x4ez; f_equal; x4ezu; x4zs; x4zl); try rewrite EV in H; clear EV end end;
    try replace (- tl + 64) with (64 - tl) by lia;
    x4ix;
    let XF' := fresh "XF'" in
    assert (XF' : XF m')
      by (unfold AX2F; split; [exists buf'; split; [exact OUT' | unfold zlen in *; rewrite LB'; exact LBF] |];
          repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]).

  Lemma x4_m3 : forall jb, x4_gm 3288 2 43 jb -> x4_gm 3120 4 31 jb.
  Proof using All.
    intros jb K mm j bc P i cont cw pad HF HB HJ HJD HBC HP HI x1 x12 x18 x20 x21 x22.
    unfold x4_gm in K.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    x4m_run mm MU CBS 3120.
    let s1 := eval cbv in (AHUF_DX2_1X + 3288) in let s2 := eval cbv in (AHUF_DX2_1X + 3924) in
    let s3 := eval cbv in (AHUF_DX2_1X + 2272) in
    kx_runFL [s1; s2; s3] 90%nat
      [KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
       KZIdx tl (2^tl); KZRange (2^tl) 2 4096; KZRange tl 1 12; KZRange (64 - tl) 52 63;
       KZRange i 0 4095; KZRange (2^tl - i - 1) 0 4095;
       KZRange SP 4096 (2^47); KZRange DT 4096 (2^47); KZRange bc 0 31;
       KZRange DST 4096 (2^47); KZRange dcap 5 (2^32); KZRange j 1 (2^32); KZRange (dcap - j) 4 (2^32);
       KZRange (DST + j) 4096 (2^47); KZRange (DST + dcap) 4101 (2^47);
       KZWr DST dcap; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap (SP + -112) 112;
       KZWr (SP + -96) 4; KZDisj (SP + -96) 4 (DT + 4) (4 * 2^tl); KZDisj DST dcap (SP + -96) 4]
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap); (SP + -112, 112)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
    all: x4side SRCB.
    all: let n := numgoals in lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "SIDE" n g end.
    kx_post_regs. x4m_post FRC SRCB CBS MU LBF bc j.
    eapply K; [exact XF' | unfold ax2_bd; kx_cells_merge |..].
    all: try assumption; try lia.
    all: lazymatch goal with |- ?g => fail 0 "LEFT" g end.
  Time Qed.

  Lemma x4_m4 : forall jb, G3924 -> x4_h2272 jb -> x4_gm 3288 2 43 jb.
  Proof using All.
    intros jb G K mm j bc P i cont cw pad HF HB HJ HJD HBC HP HI x1 x12 x18 x20 x21 x22.
    unfold x4_h2272, x4_s2272 in K.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    x4m_run mm MU CBS 3288.
    let s2 := eval cbv in (AHUF_DX2_1X + 3924) in
    let s3 := eval cbv in (AHUF_DX2_1X + 2272) in
    kx_runFL [s2; s3] 90%nat
      [KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
       KZIdx tl (2^tl); KZRange (2^tl) 2 4096; KZRange tl 1 12; KZRange (64 - tl) 52 63;
       KZRange i 0 4095; KZRange (2^tl - i - 1) 0 4095;
       KZRange SP 4096 (2^47); KZRange DT 4096 (2^47); KZRange bc 0 43;
       KZRange DST 4096 (2^47); KZRange dcap 3 (2^32); KZRange j 1 (2^32); KZRange (dcap - j) 2 (2^32);
       KZRange (DST + j) 4096 (2^47); KZRange (DST + dcap) 4099 (2^47);
       KZWr DST dcap; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap (SP + -112) 112;
       KZWr (SP + -96) 4; KZDisj (SP + -96) 4 (DT + 4) (4 * 2^tl); KZDisj DST dcap (SP + -96) 4]
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap); (SP + -112, 112)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
    all: x4side SRCB.
    all: let n := numgoals in lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "SIDE" n g end.
    all: kx_post_regs.
    all: let p := eval cbv in (AHUF_DX2_1X + 2272) in
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (ZB p) _ _ _ _) =>
          x4m_post FRC SRCB CBS MU LBF bc j; eapply K; [lia | exact XF' | unfold ax2_bd; kx_cells_merge |..]
      | |- _ => idtac end.
    all: try assumption; try lia.
    all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "LEFT" g end.
  Time Qed.

  Ltac x4run k j bc bhi dlo rlo rhi SRCB :=
    let s1 := eval cbv in (AHUF_DX2_1X + k) in let s2 := eval cbv in (AHUF_DX2_1X + 3924) in
    let s3 := eval cbv in (AHUF_DX2_1X + 2272) in let de := eval vm_compute in (4096 + dlo) in
    kx_runFL [s1; s2; s3] 90%nat
      [KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
       KZIdx tl (2^tl); KZRange (2^tl) 2 4096; KZRange tl 1 12; KZRange (64 - tl) 52 63;
       KZRange SP 4096 (2^47); KZRange DT 4096 (2^47); KZRange bc 0 bhi;
       KZRange DST 4096 (2^47); KZRange dcap dlo (2^32); KZRange j 0 (2^32); KZRange (dcap - j) rlo rhi;
       KZRange (DST + j) 4096 (2^47); KZRange (DST + dcap) de (2^47);
       KZWr DST dcap; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap (SP + -112) 112;
       KZWr (SP + -96) 4; KZDisj (SP + -96) 4 (DT + 4) (4 * 2^tl); KZDisj DST dcap (SP + -96) 4]
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap); (SP + -112, 112)] [(DT + 4, 4 * 2^tl); (DST, dcap)];
    x4side SRCB;
    lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "SIDE" g end.
  Ltac x4exit G0 :=
    kx_post_regs;
    lazymatch goal with |- context [mem_denot ?E ?m []] => change (mem_denot E m []) with m end;
    try replace (- tl + 64) with (64 - tl) by lia;
    eapply G0.
  Ltac x4lk K j bc FRC SRCB CBS MU LBF :=
    let buf' := fresh "buf'" in let OUT' := fresh "OUT'" in let LB' := fresh "LB'" in
    let RL := fresh "RL" in let RN := fresh "RN" in let EV := fresh "EV" in
    let mm' := fresh "mm'" in let EM := fresh "EM" in let XF' := fresh "XF'" in
    unfold KXGoM.apart in DJ1, DJ2, DJ3;
    kx_post_regs; kx_cells_post; kx_frame FRC; kx_frame SRCB; kx_frame CBS; kx_munch MU;
    lazymatch goal with H : u8arr bsegs ?m DST (map _ ?b), HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ m _ DST b H HL) as (buf' & OUT' & LB'); clear H end;
    kx_post_mem_free;
    lazymatch goal with |- context [ZB (DST + (j + bv_unsigned (ev ?E ?i)))] => kx_range (EVar i) RL end;
    lazymatch goal with |- context [ZB (bc + bv_unsigned (ev ?E ?i))] =>
      kx_range (EVar i) RN;
      lazymatch goal with H : rw_cells _ _ (SP + -96) [C4 ?v] |- _ =>
        assert (EV : v = ZB (bc + bv_unsigned (ev E i))) by (x4ez; f_equal; x4ezu; x4zs; x4zl);
        try rewrite EV in H; clear EV end
    end;
    lazymatch goal with |- context [mem_denot ?E ?m ?l] => remember (mem_denot E m l) as mm' eqn:EM; clear EM end;
    try replace (- tl + 64) with (64 - tl) by lia;
    assert (XF' : XF mm')
      by (unfold AX2F; split; [exists buf'; split; [exact OUT' | unfold zlen in *; rewrite LB'; exact LBF] |];
          repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]);
    eapply K; [exact XF' | unfold ax2_bd; kx_cells_merge | ..];
    first [ assumption | lia | apply x4_idx; [x4ezu; rewrite Z.mod_small by lia; lia | lia] ].

  Lemma x4_b1 : forall j, G3924 -> x4_gm 2952 6 19 j -> x4_g2724 j.
  Proof using All.
    intros j G K mm bc P fl cont cw pad HF HB HJ HD1 HP HFL x1 x11 x18 x20 x21 x22.
    unfold ax2_goal_3924 in G. unfold x4_gm in K.
    assert (G0 : forall (x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
      evtF bsegs RNG POST (XST 3924 mm x1 x5 x6 x7 (ZB (DST + j)) x10 x11 x12 PE DL x17 x18 x20 x21 x22 x28 x29 x30 x31))
      by (intros; eapply G; [exact HF | exact HB | lia | destruct HFL as [[_ ?] | [_ ?]]; x4zs; lia | intros; exact HP]).
    clear G.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_outb) as OB. x4facts mm MU. pose proof (A2 ax2_tab mm CBS) as TB.
    pose proof (WDB ltac:(lia)) as WDB'. pose proof (WDBS ltac:(lia)) as WDBS'.
    clear BYS TOK ECB AH HDT HOUT.
    unfold ax2_bd in HB. kx_cells_split HB.
    x4pre 2724.
    destruct HFL as [(-> & HBC) | (-> & HBC)]; destruct (Z_lt_le_dec (dcap - j) 8) as [HR | HR].
    - x4run 2952 j bc 7 1 0 7 SRCB. x4exit G0.
    - x4run 2952 j bc 7 8 8 (2^32) SRCB. x4lk K j bc FRC SRCB CBS MU LBF.
    - x4run 2952 j bc 64 1 0 7 SRCB. x4exit G0.
    - x4run 2952 j bc 64 8 8 (2^32) SRCB. x4exit G0.
  Time Qed.

  Lemma x4_m2 : forall jb, x4_gm 3120 4 31 jb -> x4_gm 2952 6 19 jb.
  Proof using All.
    intros jb K mm j bc P i cont cw pad HF HB HJ HJD HBC HP HI x1 x12 x18 x20 x21 x22.
    unfold x4_gm in K.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_outb) as OB. x4facts mm MU. pose proof (A2 ax2_tab mm CBS) as TB.
    pose proof (WDB ltac:(lia)) as WDB'. pose proof (WDBS ltac:(lia)) as WDBS'.
    clear BYS TOK ECB AH HDT HOUT.
    unfold ax2_bd in HB. kx_cells_split HB.
    x4pre 2952.
    let s1 := eval cbv in (AHUF_DX2_1X + 3120) in let s2 := eval cbv in (AHUF_DX2_1X + 3924) in
    let s3 := eval cbv in (AHUF_DX2_1X + 2272) in
    kx_runFL [s1; s2; s3] 90%nat
      [KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
       KZIdx tl (2^tl); KZRange (2^tl) 2 4096; KZRange tl 1 12; KZRange (64 - tl) 52 63;
       KZRange i 0 4095; KZRange (2^tl - i - 1) 0 4095;
       KZRange SP 4096 (2^47); KZRange DT 4096 (2^47); KZRange bc 0 19;
       KZRange DST 4096 (2^47); KZRange dcap 7 (2^32); KZRange j 1 (2^32); KZRange (dcap - j) 6 (2^32);
       KZRange (DST + j) 4096 (2^47); KZRange (DST + dcap) 4103 (2^47);
       KZWr DST dcap; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap (SP + -112) 112;
       KZWr (SP + -96) 4; KZDisj (SP + -96) 4 (DT + 4) (4 * 2^tl); KZDisj DST dcap (SP + -96) 4]
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap); (SP + -112, 112)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
    all: x4side SRCB.
    all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "SIDE" g end.
    x4lk K j bc FRC SRCB CBS MU LBF.
  Time Qed.

  Ltac x4rlw ofs ql qh bh q r j SB :=
    let s1 := eval cbv in (AHUF_DX2_1X + 2724) in
    let nl := eval vm_compute in (8 + ofs) in
    let bl := eval vm_compute in (8 * ql) in
    kx_runFm [s1] 120%nat
      [KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n nl (2^26);
       KZRange (n - ofs) 8 (2^26); KZRange q ql qh; KZRange r 0 7; KZRange (8 * q + r) bl bh;
       KZWord (SP + -88) 8 (SS + ofs); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZWr (SP + -104) 8; KZWr (SP + -96) 4; KZWr (SP + -88) 8; KZDisj (SP + -104) 40 SS n;
       KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange j 0 (2^32); KZRange (dcap - j) 0 (2^32)]
      [(SS, n)] [(SS, n); (SP + -112, 112)] [(SS, n)];
      x4side SB;
      lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "SIDE" g end.
  Ltac x4rlq mm q Pn bn K0 LB0 F1 F2 F3 MU0 :=
    kx_post_regs; kx_cells_post; kx_frame F1; kx_frame F2; kx_frame F3; kx_munch MU0;
    let b := fresh "buf'" in let O := fresh "OUT'" in let L := fresh "LB'" in
    lazymatch goal with H : u8arr bsegs ?m DST (map _ ?b0), HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ m _ DST b0 H HL) as (b & O & L); clear H | |- _ => fail 0 "M1" end;
    kx_post_mem_free;
    let m' := fresh "mm'" in let EM := fresh "EM" in
    lazymatch goal with |- context [mem_denot ?E mm ?l] => remember (mem_denot E mm l) as m' eqn:EM; clear EM
      | |- _ => fail 0 "M2" end;
    let EQ := fresh "EQ" in
    lazymatch goal with |- context [bv_unsigned (edenot ?E (EAluw ALU_SRL ?a (ELit 3)))] =>
      assert (EQ : bv_unsigned (edenot E (EAluw ALU_SRL a (ELit 3))) = q)
        by (rewrite x4_srlw3 by (x4ezu; rewrite Z.mod_small by lia; lia); x4ezu; rewrite Z.mod_small by lia; x4zl);
      rewrite EQ; clear EQ | |- _ => idtac end;
    lazymatch goal with H : rw_cells _ _ (SP + -88) [C8 ?v] |- _ =>
      let EV := fresh "EV" in
      tryif constr_eq v (ZB Pn) then idtac else
      (assert (EV : v = ZB Pn) by (x4w; x4ez; f_equal; x4ezu; x4zs; x4zl); rewrite EV in H; clear EV)
      | |- _ => fail 0 "M4" end;
    lazymatch goal with H : rw_cells _ _ (SP + -96) [C4 ?v] |- _ =>
      let EV := fresh "EV" in
      tryif constr_eq v (ZB bn) then idtac else
      (assert (EV : v = ZB bn) by (x4ez; f_equal; x4ezu; rewrite ?x4_srlw3 by (x4ezu; rewrite Z.mod_small by lia; lia); x4ezu; x4zs; x4zl); try rewrite EV in H; clear EV)
      | |- _ => fail 0 "M5" end;
    repeat match goal with |- context [Z_to_bv 64 ?e] =>
      lazymatch e with context [q] =>
        tryif first [constr_eq e Pn | constr_eq e bn] then fail else
        first [replace e with bn by lia | replace e with Pn by lia] end end;
    replace (- tl + 64) with (64 - tl) by lia;
    let XF' := fresh "XF'" in
    assert (XF' : XF m')
      by (unfold AX2F; split; [exists b; split; [exact O | unfold zlen in *; rewrite L; exact LB0] |];
          repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]);
    eapply K0; [exact XF' | unfold ax2_bd; kx_cells_merge |..];
      try lia;
      lazymatch goal with |- ?g => fail 0 "LEFT" g end.
  Ltac x4rlw0 ofs j SB :=
    let s1 := eval cbv in (AHUF_DX2_1X + 2724) in
    let nl := eval vm_compute in (8 + ofs) in
    kx_runFm [s1] 120%nat
      [KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n nl (2^26); KZRange (n - ofs) 8 (2^26);
       KZWord (SP + -88) 8 (SS + ofs); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZWr (SP + -104) 8; KZWr (SP + -96) 4; KZWr (SP + -88) 8; KZDisj (SP + -104) 40 SS n;
       KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange j 0 (2^32); KZRange (dcap - j) 0 (2^32)]
      [(SS, n)] [(SS, n); (SP + -112, 112)] [(SS, n)];
      x4side SB;
      lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail 0 "SIDE" g end.
  Lemma x4_rl_c1 : forall mm j q r off cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    x4_g2724 j -> XF mm -> XBD mm cw (8 * q + r) pad (SS + off) -> 0 <= j <= dcap -> 0 <= q <= 8 -> 0 <= r <= 7 ->
    8 * q + r <= 64 -> 1 <= off <= 7 -> q <= off -> off + 8 <= n -> 1 <= dcap ->
    evtF bsegs RNG POST (S4 2272 mm x1 (ZB (8 * q + r)) (ZB (DST + j)) x10 (ZB (SS + off)) x12 cont x18 x20 x21 x22).
  Proof using All.
    intros mm j q r off cont cw pad x1 x10 x12 x18 x20 x21 x22 K HF HB HJ HQ HR HBC HP1 HQO HP2 HD1.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    x4facts mm MU. clear BYS TOK ECB AH HDT HOUT.
    unfold ax2_bd in HB. kx_cells_split HB.
    x4pre 2272. unfold x4_g2724 in K.
    assert (HO : off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7) by lia.
    destruct HO as [HO|[HO|[HO|[HO|[HO|[HO|HO]]]]]]; subst off;
      [ x4rlw 1 0 1 15 q r j SRCB; x4rlq mm q (SS + 1 - q) r K LBF FRC SRCB CBS MU
      | x4rlw 2 0 2 23 q r j SRCB; x4rlq mm q (SS + 2 - q) r K LBF FRC SRCB CBS MU
      | x4rlw 3 0 3 31 q r j SRCB; x4rlq mm q (SS + 3 - q) r K LBF FRC SRCB CBS MU
      | x4rlw 4 0 4 39 q r j SRCB; x4rlq mm q (SS + 4 - q) r K LBF FRC SRCB CBS MU
      | x4rlw 5 0 5 47 q r j SRCB; x4rlq mm q (SS + 5 - q) r K LBF FRC SRCB CBS MU
      | x4rlw 6 0 6 55 q r j SRCB; x4rlq mm q (SS + 6 - q) r K LBF FRC SRCB CBS MU
      | x4rlw 7 0 7 63 q r j SRCB; x4rlq mm q (SS + 7 - q) r K LBF FRC SRCB CBS MU ].
  Time Qed.

  Lemma x4_rl_c2 : forall mm j q r off cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    x4_g2724 j -> XF mm -> XBD mm cw (8 * q + r) pad (SS + off) -> 0 <= j <= dcap -> 0 <= q <= 8 -> 0 <= r <= 7 ->
    8 * q + r <= 64 -> 1 <= off <= 7 -> off < q -> off + 8 <= n -> 1 <= dcap ->
    evtF bsegs RNG POST (S4 2272 mm x1 (ZB (8 * q + r)) (ZB (DST + j)) x10 (ZB (SS + off)) x12 cont x18 x20 x21 x22).
  Proof using All.
    intros mm j q r off cont cw pad x1 x10 x12 x18 x20 x21 x22 K HF HB HJ HQ HR HBC HP1 HOQ HP2 HD1.
    destruct HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    x4facts mm MU. clear BYS TOK ECB AH HDT HOUT.
    unfold ax2_bd in HB. kx_cells_split HB.
    x4pre 2272. unfold x4_g2724 in K.
    assert (HO : off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7) by lia.
    destruct HO as [HO|[HO|[HO|[HO|[HO|[HO|HO]]]]]]; subst off.
    - x4rlw 1 2 8 64 q r j SRCB; x4rlq mm q SS (8 * q + r - 8 * 1) K LBF FRC SRCB CBS MU.
    - x4rlw 2 3 8 64 q r j SRCB; x4rlq mm q SS (8 * q + r - 8 * 2) K LBF FRC SRCB CBS MU.
    - x4rlw 3 4 8 64 q r j SRCB; x4rlq mm q SS (8 * q + r - 8 * 3) K LBF FRC SRCB CBS MU.
    - x4rlw 4 5 8 64 q r j SRCB; x4rlq mm q SS (8 * q + r - 8 * 4) K LBF FRC SRCB CBS MU.
    - x4rlw 5 6 8 64 q r j SRCB; x4rlq mm q SS (8 * q + r - 8 * 5) K LBF FRC SRCB CBS MU.
    - x4rlw 6 7 8 64 q r j SRCB; x4rlq mm q SS (8 * q + r - 8 * 6) K LBF FRC SRCB CBS MU.
    - assert (q = 8) by lia. assert (r = 0) by lia. subst q r.
      x4rlw0 7 j SRCB; x4rlq mm 8 SS 8 K LBF FRC SRCB CBS MU.
  Time Qed.

  Lemma x4_rl : forall j, x4_g2724 j -> x4_s2272 j.
  Proof using All.
    intros j K. unfold x4_s2272.
    intros mm bc P cont cw pad HF HB HJ HD1 HBC HP x1 x10 x12 x18 x20 x21 x22.
    destruct HP as [HP | HP].
    - subst P. exact (x4_rl_b mm j bc cont cw pad x1 x10 x12 x18 x20 x21 x22 K HF HB HJ HBC HD1).
    - pose proof (Z.div_mod bc 8 ltac:(lia)) as HBE.
      pose proof (Z.mod_pos_bound bc 8 ltac:(lia)) as HR.
      assert (HQ : 0 <= bc / 8 <= 8) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
      set (q := bc / 8) in *. set (r := bc mod 8) in *. clearbody q r. subst bc.
      set (off := P - SS) in *. assert (HPo : P = SS + off) by (unfold off; lia). clearbody off. subst P.
      destruct (Z_lt_le_dec off 8) as [Ho | Ho].
      + destruct (Z_le_gt_dec q off) as [Hq | Hq].
        * exact (x4_rl_c1 mm j q r off cont cw pad x1 x10 x12 x18 x20 x21 x22 K HF HB HJ HQ ltac:(lia) ltac:(lia)
                   ltac:(lia) Hq ltac:(lia) HD1).
        * exact (x4_rl_c2 mm j q r off cont cw pad x1 x10 x12 x18 x20 x21 x22 K HF HB HJ HQ ltac:(lia) ltac:(lia)
                   ltac:(lia) ltac:(lia) ltac:(lia) HD1).
      + apply (x4_rl_a mm j q r off cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HJ HQ ltac:(lia) ltac:(lia) Ho
                 ltac:(lia) HD1).
        intros mm' cw' pad' cont' x11' x18' x20' x21' x22' HF' HB'.
        refine (K mm' r (SS + off - q) 1 cont' cw' pad' HF' HB' HJ HD1 _ _ x1 x11' x18' x20' x21' x22').
        1: destruct (Z.eq_dec (off - q) 0); [left | right]; lia.
        1: left; lia.
  Time Qed.

  Lemma ax2_goal_2272_ok : G3924 -> XA ax2_goal_2272.
  Proof using All.
    intros G. apply x4_top, x4_loop;
      [exact x4_rl | intros j; exact (x4_b1 j G) | exact x4_m2 | exact x4_m3 | intros jb; exact (x4_m4 jb G)].
  Time Qed.

End AX2E.
End CANSEC1.
