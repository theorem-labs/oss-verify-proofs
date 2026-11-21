(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (12 recorded proofs replaced by written proofs (stderr_sink_frame, stderr_sink_flags, flags40_8 and 9 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio Driver.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_memset F_memcpy Stdio_kit F_syscalls StdioFiles.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_printf_iface F_printf_core F_vfprintf.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_pieces Printf_fmts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_vfprintf_stdout.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import Printf_bridge.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg Stdio_kit2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_fprintf () := "C47Corelib7Classes?RelationClasses9ReflexiveC59OSSVerify5KrLib5Plain>F_printf_iface?sink_frame_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface;SINK_stderrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes3fstI47Corelib4Init5Logic2or00I47Corelib5Lists7ListDef6Forall00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib5Plain:StdioFiles:file_cellsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib6Common<F_fmt_fp_libDForall_disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes3appK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5Plain:StdioFiles;GLOBALS_TOPC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib5PlainAF_vfprintf_stdoutEfile_cells_flags_byteC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib5PlainAF_vfprintf_stdout<land_mod_lowC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib5Plain>F_printf_iface?sink_flags_stmtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib5PlainAF_vfprintf_stdout=land_sub_maskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9F_fprintf9flags40_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainAF_vfprintf_stdout9land_low7C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainAF_vfprintf_stdout;sx32_mod128C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:land_assocC56Stdlib6ZArith6BinInt1Z8land_0_rc59OSSVerify5KrLib5Plain9F_fprintf:flags40_32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z@land_lor_distr_rC56Stdlib6ZArith6BinInt1Z7lor_0_rC59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdio_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9F_fprintfAstderr_sink_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface@printf_core_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_pieces>implM_post_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=F_printf_coreAprintf_core_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_pieces5outskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Printf_bridge<FLUSH_stderrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree>impl_ret_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model<printf_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface:OUT_stderrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_ifaceCfwritex_stderr_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_ifaceFstdio_write_flush_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_ifaceFstdio_write_flush_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree:impl_ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface<stderr_wfileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8pass1_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5Plain>F_printf_iface7args_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model=printf_piecesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib6Common<Printf_model8fp_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9F_fprintfDvfprintf_stderr_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib5PlainDF_printf_core_common9zb_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface<OUTFP_stderrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega=RingMicromega5Psatz02K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast=munch_write_nC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib5Lists7ListDef5skipnK4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib5Plain>F_printf_ifaceAprintf_core1_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib3Lib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5low32C59OSSVerify5KrLib3Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc59OSSVerify5KrLib5Plain9F_fprintf>sflags_noerr_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec<Z_land_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib5PlainDF_printf_core_common<rw_CB_lengthC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib5Plain9F_fprintfAstderr_sink_flagsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface@printf_core_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9F_fprintf?sflags_noerr_32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5Plain:F_vfprintf:args_ok_vfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface;fpcall_stmtC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib5Plain>F_printf_iface:TOPOK_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface2SRC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3b2zK4ELinuxProcessSemantics5Riscv5Instr5instr0;C59OSSVerify5KrLib3Lib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu32C59OSSVerify5KrLib3Lib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9alu_sltiuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_vfprintf6rwc_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib3Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9F_fprintf?sflags_final_40C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9F_fprintf>sflags_olderr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;v_sltiu_b2zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_piecesAprintf_model_outsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C59OSSVerify5KrLib3Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib9StoreFastFbytes_at_write_other_nC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C59OSSVerify5KrLib3Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast;stk_write_nC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface<STATIC_SPLITC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib5Plain:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_vfprintf8VF_FRAMEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface8VF_DEPTHC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib5Plain=F_printf_coreBprintf_core1_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_ifaceAprintf_core1_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface8PC_DEPTHC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C59OSSVerify5KrLib5Plain:F_vfprintf=towrite_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface<towrite_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainAF_vfprintf_stdout:topok_noneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface9OUT_DEPTHC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c59OSSVerify5KrLib5Plain9F_fprintfDvfprintf_stderr_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9Stdio_kitBrw_cells_bytes_at'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface=FPRINTF_DEPTHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9F_fprintfEvfprintf_stderr_proofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9F_fprintf@fprintf_gen_stmtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC46Stdlib5Lists4List=Forall_forallC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltI46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib5Plain>F_printf_ifaceAfprintf_diag_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=stderr_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Printf_bridge<impl_tforallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9impl_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9F_fprintf?vf_to_diag_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree?impl_epost_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface9diag_argsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Printf_bridgeBoutsk_flush_leavesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Printf_bridge=stderr_bridgeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stderr_fprintfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9F_fprintfAfprintf_gen_proofC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_usageC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appK59OSSVerify5KrLib6Common<Printf_model4parg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:Stdio_kit2<fmt_bytes_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9F_fprintf>forall_range_bC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_piecesCprintf_pieces_usageC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBpieces_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_piecesIprintf_pieces_cannot_openC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioApieces_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_piecesHprintf_pieces_read_errorC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_ifaceAfprintf_diag_stmtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI59OSSVerify5KrLib4Spec6Driver8diag_msg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts;A_FMT_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts9FMT_usageC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C59OSSVerify5KrLib6Common;Printf_fmtsAA_FMT_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts?FMT_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts@A_FMT_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts>FMT_read_errorC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>pieces_too_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts=A_FMT_too_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts;FMT_too_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_piecesEprintf_pieces_too_bigC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg07C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM psegs c s Q ms) | _ => idtac end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StderrSinkProofs.
  Context {St : Type}.
  Variable B : Z.
  Let SINK := SINK_stderr (St:=St) B.

  Lemma stderr_sink_frame : sink_frame_stmt RSTDERR B 80 SINK.
  Proof using .
    unfold sink_frame_stmt. intros W m m' [buf st] (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO) MU WM D1 D2.
    exists flags, mode, tail, rest.
    split; [|split; [exact FL32 | split; [exact FL8 | split; [| split; [exact LEN | split; [exact BHI | exact BLO]]]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed.

  Lemma stderr_sink_flags : sink_flags_stmt RSTDERR SINK.
  Proof using B.
    unfold sink_flags_stmt. intros m [buf st] (flags & mode & tail & rest & FC & FL32 & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. exact FL32.
  Qed.
End StderrSinkProofs.

(* [comment removed for export] *)
Lemma flags40_8 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma flags40_32 : forall f, Z.land f 40 = 0 -> Z.land f 32 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma sflags_noerr_8 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_8. exact H.
Qed.
Lemma sflags_noerr_32 : forall (flags : word),
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 32 = 0.
Proof.
  intros flags. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 32) with 0. apply Z.land_0_r.
Qed.
Lemma sflags_olderr0 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof. intros flags H. rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_32. exact H. Qed.
Lemma sflags_final_40 : forall (flags2 : word), Z.land (bv_unsigned flags2) 32 = 0 -> Z.land (bv_unsigned flags2) 8 = 0 ->
  Z.land (Z.lor (bv_unsigned (sx32 flags2)) 0) 40 = 0.
Proof.
  intros flags2 H32 H8. rewrite Z.lor_0_r. rewrite land_low7, sx32_mod128, <- land_low7 by lia.
  replace 40 with (Z.lor 32 8) by reflexivity. rewrite Z.land_lor_distr_r, H32, H8. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stderr.
  Context {St : Type}.
  Hypothesis FWE : fwritex_stderr_stmt.
  Hypothesis FLS : stdio_write_flush_stmt.

  Definition vfprintf_stderr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
    fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ stderr_wfile m'
      /\ ssp_cells m' canary.

  Definition vfprintf_stderr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stderr_wfile m ->
      bytes_at psegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDERR (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk psegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->
      ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      Monad.implM psegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x20070) fc None m (seg_rom psegs)).

  Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
  Proof using FLS FWE.
    unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [psegs] in SSP1, SSP2. fold psegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    (* [comment removed for export] *)
    apply (printf_model_outs psegs OUT_stderr (OUTFP_stderr (St:=St)) fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    carve_frame 368%nat ST.
    do 12 zs. do 14 zs.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [psegs] in SSP1, SSP2. fold psegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit.
    do 10 zs.
    pose proof towrite_proof as TW. unfold towrite_stmt in TW.
    eapply evt_cut.
    { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
      rewrite unsigned_lit; [apply sflags_noerr_8; exact FL40|].
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    cbv beta. intros ms' P. clear TW.
    destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. do 6 zs.
    set (B := bv_unsigned sp + -352) in *.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB psegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
    match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
    match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
    pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
    replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
    (* [comment removed for export] *)
    ileave.
    pose proof (printf_core_proof (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr (OUTFP_stderr (St:=St))
                  (stderr_sink_frame B) (stderr_sink_flags B) (topok_none) (FWE St B)) as PC2.
    unfold printf_core_stmt in PC2.
    assert (FR3 : 0 <= Z.land (bv_unsigned (sx32 flags)) 18446744073709551583 < 2^64).
    { pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    eapply implM_bind.
    { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
        clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
      all: try lia. all: try exact I.
      - unfold SINK_stderr. cbn [fst].
        exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, jb.
        change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. cbn [zb map app].
        split; [exact FCt|]. rewrite unsigned_lit by lia.
        split; [apply sflags_noerr_32|]. split; [apply sflags_noerr_8; exact FL40|]. split; [exact BUFc|].
        unfold zlength. rewrite LJB. unfold GLOBALS_TOP. subst B. lia.
      - exact BY.
      - exact HF.
      - reflexivity.
      - exact APC.
      - exact VAA.
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
      - rewrite FPC. apply Forall_nil.
      - exact STc.
      - split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM. }
    cbv beta. intros r' [buf3 st3] ms' P. clear PC2 MU1.
    unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m3 MUc WMc; clear MUc WMc end.
    ienter. fix_ret.
    pose proof SNK3 as SNK3'. destruct SNK3' as (flags2 & mode2 & tail2 & rest2 & FC3 & FL32 & FL8 & BUF3 & LEN3 & BHI3 & BLO3). cbn [fst] in FC3, BUF3, LEN3.
    unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [psegs] in SSP1, SSP2. fold psegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs.
    ileave. unfold FLUSH_stderr, Monad.implM. cbv beta iota.
    pose proof (FLS St B) as FL. unfold stdio_write_flush_stmt in FL.
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 1024) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
    eapply impl_ebind.
    { unfold Monad.implM in FL.
      eapply FL with (lo := bv_unsigned sp + -368 - 1024) (canary := canary); clear FL; rewrite ?unsigned_lit by lia; unfold OUT_DEPTH, GLOBALS_TOP.
      all: try lia.
      - exact SNK3.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact ST4b.
      - split; [exact SSP1 | exact SSP2].
      - assumption. }
    cbv beta. intros [[] st4] ms' P.
    unfold stdio_write_flush_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (z5 & z6 & z7 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & SNK4 & SSP4).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m4 MUc WMc; clear MUc WMc end.
    apply impl_ret_intro. cbn [snd]. fix_ret.
    cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
    destruct SNK4 as (flags4 & mode4 & tail4 & rest4 & FC4 & FL32' & FL8' & BUF4 & LEN4 & _ & _). cbn [fst snd] in FC4, BUF4, LEN4.
    unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [psegs] in SSP1, SSP2. fold psegs in SSP1, SSP2.
    (* [comment removed for export] *)
    do 9 zs.
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 1024)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 1024)%Z _ |- _ =>
      pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
    pose proof (rw_CB_length _ _ _ _ BUF4) as LB4.
    lazymatch goal with A1 : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, A2 : rw_cells _ ?mm (bv_unsigned sp + -360)%Z _,
                        BU : rw_cells _ ?mm B [CB 80 ?bb], FR : rw_cells _ ?mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
      assert (FALL : rw_cells psegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
      [ apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [exact A1|];
        apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
        apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
        cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
      | clear A1 A2 BU FR ] end.
    cbn [app] in FALL.
    release_frame FALL ST5 (bv_unsigned sp).
    apply evt_done. subst QQ. cbn [epost fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST5|].
    split.
    { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags4)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode4, 0, 0, tail4.
      split; [unfold file_cells; exact FC4|].
      rewrite (sflags_olderr0 flags FL40). rewrite unsigned_lit; [apply sflags_final_40; [exact FL32' | exact FL8']|].
      rewrite Z.lor_0_r. pose proof (bv_unsigned_in_range 64 (sx32 flags4)) as R4. unfold bv_modulus in R4. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R4. lia. }
    split; [exact SSP1 | exact SSP2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fprintf_gen_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A ->
      stderr_wfile m ->
      bytes_at psegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      args_ok RSTDERR (q - 80 - 352) 80 m lo q (q - 80 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk psegs m lo q -> (lo <= q - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->
      ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      Monad.implM psegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f980) fc None m (seg_rom psegs)).

  Theorem fprintf_gen_proof : fprintf_gen_stmt.
  Proof using FLS FWE.
    unfold fprintf_gen_stmt. intros until canary. cbv zeta.
    intros -> -> SF BY HF P1 AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA.
    unfold FPRINTF_DEPTH, VF_FRAME, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [psegs] in SSP1, SSP2. fold psegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    carve_frame 80%nat ST.
    do 17 zs.
    apply (proj1 (rw_cells_app psegs _ _ [_;_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -48)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.
    (* [comment removed for export] *)
    ileave.
    pose proof vfprintf_stderr_proof as VF. unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
    eapply implM_post_evt.
    { eapply VF with (A := A) (VA := bv_unsigned sp + -48) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args) (lo := lo) (canary := canary);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
      all: try reflexivity. all: try lia.
      - exists flags, mode, e, wend, tail. split; [unfold file_cells; exact FC | exact FL40].
      - exact BY.
      - exact HF.
      - exact P1.
      - exact VAA.
      - eapply args_ok_vf; [| | exact MU]; [|lia].
        replace (bv_unsigned sp + -80 - 352)%Z with (bv_unsigned sp - 80 - 352)%Z by lia.
        replace (bv_unsigned sp + -80 - 368)%Z with (bv_unsigned sp - 80 - 368)%Z by lia. exact AOK.
      - exact PP.
      - exact FPC.
      - exact ST.
      - split; [exact SSP1 | exact SSP2].
      - exact MI.
      - exact FRM. }
    cbv beta. intros [] [b4 st4] ms' P. clear VF MU1. cbn [snd] in P.
    unfold vfprintf_stderr_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    change psegs with psegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -48)%Z ?rest |- _ =>
      assert (FALL : rw_cells psegs mm (bv_unsigned sp + -80) (hd ++ rest));
      [ apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
      | clear FR VAC ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evt_done. subst QQ. cbn [fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|]. split; [exact SF3|]. split; [exact SSP1 | exact SSP2].
  Qed.
End Stderr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma forall_range_b : forall l, forallb (fun c => (0 <=? c) && (c <? 256))%bool l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
  intros l H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc. specialize (H c Hc).
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma vf_to_diag_post : forall St ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (st st' : St) ms,
  vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st' ms -> st' = st ->
  fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms.
Proof.
  intros until ms. intros (x5 & x6 & x7 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI & FRM & FOK & ST & SF & SSP) Est.
  exists x5, x6, x7, a0, a1, a2, a3, a4, a5, a6, a7, x28, x29, x30, x31, Ft, fc', m'.
  repeat (split; [assumption|]). exact Est.
Qed.

Theorem fprintf_diag_proof : forall St : Type, @fprintf_diag_stmt St.
Proof.
ltac2:(KReplay.run1 (kr_t_F_fprintf ()) [] "p'0h03ms'h13AB0h21Hh34LZS0h44cstrh55cstr0h64__x1h71pi001ph87__arithh95cstr1h:4__ffh;8__varmaph<5__with=4__x2h>2bsh?2ABh@2DAhA5slackhB4__p1hC7__sat12hD7__sat13hE7__sat14hF7__sat15hG7__sat16hH4__x3hI4__x4hJ4__x5hK1xi011xhL2H0hM2H1hN2H2hO2HahP3Ha1hQ2BYhR2DJhS2GAhT2H3hU2H4hV2HFhW3LENhX3LZShY3SLKhZ1nh[1ri021rh\2s'h]4__p2h^1ai031ah_1ci041ch`1mha4pathi054pathhb2pshc1ui061uhd1yhe2BRhf1Fhg2FGhh3FLShi3FRMhj3FWEhk3GLOhl2H'hm3Ha0hn2Huho2LOhp2MIhq3QHIhr2R2hs2Rqht2SFhu3SSPhv2SThw2Sthx2a0hy2a1hz2a2h{2a3h|2a4h}2a5h~2a6i072a7i085argv0i091bi0:3bufi0;6canaryi0<1di0=1ei0>2fci0?2gpi0@2loi0A2rai0B1si0C2s0i0D2s1i0E3s10i0F3s11i0G2s2i0H2s3i0I2s4i0J2s5i0K2s6i0L2s7i0M2s8i0N2s9i0O2spi0P2sti0Q2t0i0R2t1i0S2t2i0T2t3i0U2t4i0V2t5i0W2t6i0X2tpi0Y1li0Z1qp%0p%1p%2p%3p&0p&1p;1p;2p;3p;6p;4p;Gp;Op;7p;Hp;:p;Jp;8p;Ip;Fp;5p;<p;9p;Bp200S00g00nSR0p4p710p8Q00g014eR1p4p710p8Q00g01J3R2p4p710p8Q00g04fPR3p4p710p8Q00g04gMR4p4p741110p8Q00g015dR5p4p710p8Q00g0080R6p4p7210p8Q00g04hRR7p4p710p8Q00g04iIR8p4p741110p8Q00g04jAR9p4p710p8Q00g019^R:p4p710p8Q00g04eER;p4p710p8Q00g01?MR<p4p710p8Q00g04kER=p4p741110p8g0054j16Tg005Yk104Tg0067k10FTg008Mj1ETg002jk21OTg006Zk11@Tg01A:k115Tg00]Vj2gTg00HCj3;k10PTg00=Aj21Tg04lCj6cTg03JIk41NTg01D=j2:Tg009PS01j20Tg0092j1@Tg00?Ck20LTg00CQj2DTg01HDk210Tg03K;k20|Tg01ICk10yTg01N;k20STg01Nnk10xTg00?`S02j23Tg004Tk100Tg0044S03j24TP:j1UTP5j1TTg00=kj1|Tg00;aj49TP6j3KTP2lG?Tg01K<lOLTg01Knk10lTg01LPk11nTg01MIj7NTg01VBk11ZTP3k31VTg00oHk41STg03GTk61MTg00:Ik30JTP;mH1KmI0NmF06Tg01W8R;k11JTP1k61Ik50VTP<j4\k20[Tg04mFk41;TP4m:1:Tg04nQk101TP9mJ17TP8m:16Tg04oIk814TP=m:11Tg050Ok20~Tg051Mk30{Tg04^Ck10zTg052Sk10TTg053Nj1]Tg00@Uj1>Tg00QXj3JTg00>Kj2CTg00@;S04k20GTg054Jj1pTg009lR=j22Tg01OWk50tTg01PRj2=Tg01Q2k10sTg00PFk30ETg00BIR8j1FTg054gk20BTg055>k30rTg00bdk60DTg055]k10qTg00G=k209Tg056\k30;Tg01XMk20pTg01Y0k30oTg03LUm<0nTg03M:k40mTg00OgR9k10CTg042Uk31qTg020Rk11pTg0210k41oTg02cDk61cTg01YMk105Tg00DQk11bTg00Dok11aTg00EMk11`Tg00F8k20fTg00F[k21YTg00GWk21XTg00H]k31WTg00I<k41UTg035ck20<Tg057Uk708Tg04_Hk21RTg033Ik21QTg04_ek21PTg04`Ck30ATg058Wk20=Tg00L_k20>Tg00M=j2wTg00Bik20_Tg00Cmk30^Tg059Zk20kTg00`4j2YTg05:Kk21HTg02CEk11GTg05:lk20\Tg01X0k21FTg05;Ik21ETg05<0k21DTg05<Wk21BTg05==k21>Tg05=ck21=Tg021Sk20ITg03hSk30YTg03i<k219Tg00`Tk30]Tg00N;k40ZTg01DZm90bTg05>_k218Tg01n8k10MTg00R8k407Tg02Vlk30XTg03:6k30WTg00M`j4{Tg05?lk10dTg05@gj1eTg05Aik21TTg05C<k10eTg05D7j1dTg05E8k213Tg05FJk112Tg05GIk11[TP0k70OTg044>k21\TP7k21]Tg03ITk41^Tg00;@k31_Tg00:fj2zTg03eYm<0gTg03KomB0UTg00Rnk40iTg00SYk70hTg03e5k60}Tg00a7k71fTg03Nbk81gTg03Mak41hTg00Ink31iTg03ffk71jTg03N?k31kTf0R7#6#6p=Z%E7#Ep=[%E7#6p=i%67#Ep=r%67#6#6#@p=`g00ZMR0/07p>1?g00UPR4/07p=5%E7#E#E#Ep=^%67#6#6#6p=Mf7R<g00T=R1g00WiR3f6R2f5R6P3f4R5f3R:I0Vf2R>f1R?P7K0Op=71437p=IAK3?7p=tP7P?P>P:P5P6P2P<f8R@f9S05f:S06f;S07f<RAf=S08f>S09f?S0:f@S0;fARBfBRCfCRDfDREfERFg00XiRGfFRHfGRINI0Np=QAK3?79K:>p=OAK3>?9K5:=;67p=oP5P:21\>?P7C\p=SP3P?PGP7C9p=aP5P1P3P:P>P?P7K0Op>0jP6P1P321]5:P>P?P7K0Op=bP1P5P:B0E>?7H1^p=j1D47p=hg00U2RJ@1_?7p=X1CJ7p=<12>?/27p=8100>10?7'3p=P1D<21265/0:10>?'z/37'3p=W%p:/Y>/0?/37p=f13?7,3>p=V1Y>?/07p=~12?7#pp>0w125:/0>/z?/37p>0R1C?7,2>p>0Q10>?/z7p=H12>?/07p=G100?/37p>0v%>?>0E>7p>0u%F7,2?p>0:10?7,3>p=q1=J7p=}g00\VS0<g00]6S0=7;7p=_A;J?7p=k209J7p=ng048OR0P0PJPJP9P8P8P:g05HTP>P?P7N<0gp>1mP0P0P0PJPJPJg05I8P8P8P8P=g05IXP6P5P:P>P?P7NB0Up>1lP0PJPJPJP8P8P6P5P:P>P?P7N<0gp>1ePJPJPJPJPJPJP=P7P?P>P=P:P5P6P2P<P@Q05NB0Up>1d20fJ7p=BP>g00WJR=P3P3g00XIS0>PJP?g00VcP7H0iPGK0hp=A%67#@p>0c1z>?/37p>0310>?,z:/37p>1L1=?7#Fp=sP?P=P3P3Q0>P7J0}p>0aP>P=P3P3Q0>P?P7K1fp>0HPJP?g00e8P7H0ip>0?P?P=P3P3Q0>P7PGK0hp>0@P:P=P3P3Q0>P>P?P7L1gp=R1=J7#Fp>0`1=J?#F,2>/27#pp=l1D>?/37p>1CPJP>P?P7H1hp=uB1iJ?7p=xP>P=P3P3Q0>P?P7K1jp>021=J7#F,2?p>1<10?7,z>p>1AB1kJ?7p=yP2P6P5P:P>P?P7C{C{p=mP?g00[NS0?P7g04A]S0@C{p>0KAJ>?79J5:p=vQ00g05J;S0Ag00YIS0B#6S0C#6S0D#6S0E#ZS0F#6S0G$04R=$0FRGQ0C#ES0H$0401OGQ0F$04S0I$0FQ0E$04S0J$0FR9$1@\GfSRKg01;`g01>=&156fNRLQ0B#Z#[#i#i#r#[#i#`S0K,g=5;GfYRMP<PLfMRNP6fWRO,1=EcP1P@P2fXRP,1=H1N11=MS0Lg04\2':,0<&1?@f[RQ,1=Q0C#@S0MQ0H#ES0N#ES0O#ES0P#@S0Q+0LRR'DQ05-10AQ08-0|1Q0:$0yf_RS-0S=11=SRT#5&0x=S0R,DT'3&00JRU$00S0SfdRV,4URWPW%UVP7%TVPUPV%|JS0TQ0;C9feRW,4URXg04=IRYfgRZPWPVfcR[fbR\f^R]f]R^fTR_PKfRR`fQRafPRbfORcPLPNfLRdfKRePHPCPBPEAKUZ?P7MG?W0W>V3P\faRff`RgPSP]P^f\RhPQfZRiPMPPPOfVRjfURkP_PKP`PaPbPcPLPNPdPefJRlfIRmfHRnPIPHPFPEMOLPDQ0B#E#^#Z#[#M#`,g=S0UPC&0lGS0VPB&1n1S0WFNG7S0Xg04;mRoP1&1Z1Rp%IWRqPWPUP3Q0T>1VW?ffRrQ0MP7Q0TH1SZ0:UPBJ1MPZPWPVP[P\P]P^P_PKP`PaPbPcPLPNPdPePHPCPBPEPD1tZ?P7MHQX0YX7qPrPVP[P\PfP^PhPKP`PaPbPcPLPNPdPePlPFPBQ0;PDPCB0J3r71tr7NH1KX7qP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnPIPHPFMOLPEQ0UPDQ0VPCQ0WFNS0YP1PWP?Q0TPBPZPWPVP[P\P]P^P_PKP`PaPbPcPLPNPdPePHPCPBPEPDP?P7MHQX0YX\WQ0YPoP1Pp%IXRs$1JRtPX%UWP3P?%TWPUPWQ0TPBC9J1IRX14UZS0Z#IRufiRvPZPrPWPVPgPSPjPkP_PKP`PaPbPcPLPNPnPEPDPHPUPv14UvS0[P?COP7MG?X0YX7uRwP?P7C\P;Pup-0RxP?Q0?fhRyPUPy14UyS0\P7PEEon1011020002001010Z'3X0YX[tPZPWPVP[P\P]P^P_PKP`PaPbPcPLPNPdPePHPCPBPEPDPUPZQ0ZP?CORzP7MHQX0YX7s-0[sQ0YP1PoPpPtP;14Ur#IRpPxP7Q0?PZPUPZQ0ZP7PDEon1011020002001010ZX[tPXPZPWPVP[P\P]P^P_PKP`PaPbPcPLPNPdPePHPCPBPEPzP7MG?X0YX7s-0[sQ0YPWP?Q0TPBH1;P7N:1:P;PpQ0\#IRpfjRsPyPZPrPWPfPgPOPjPkP_PKP`PaPbPcPLPmPFPEPIPUPs14UsS0]P?CORzP7MG?X0YX7pRXP?P7C\P;PpPxP?Q0?PvPUPvQ0[P7PFEon1011020002001010Z'3Q0[#IR;fkRoPvPyPZPrP\PfPPPOPjPkP_PKP`PaPbPcPlPHPFPnPIPUPo14UoS0^P?COP7MHQX0YX7;R{P>P?C\[^0YP7PuPw&01uP7C\Q0?'3Q02PpPX&01pP?C\Q0?P;P{&01;P>C\P7Q0]#IR;flR{PsPvPyPZP[P\PMPPPOPjPkP_PKP`PaPbPePIPHPmPUP{14U{RpP?COP7MG?X0YX7;RX&01;P:C\Q0?Q0@%IpRwfnR|P{PoPsPvPWPVPQPiPMPPPOPjPkP_PKP`PNPmPnPePlPUP|14U|R}P?COP7MHQX0YX7w&01wP6C\eWNWMP?P7O2n2001000000120000000WLX0YQ03P3Q0\P;PXP;P?P7DSA;szH'3Q0^#IRzfmR;PoPsPvPyPVP[PiPMPPPOPjPkP_PKP`PaPdPnPIPlPmPUP;14U;S0_P?COP7MHQX0YX7zPzP>P?DS[^0YP7P3%I}RzfpRXP|P;P{PoPZPrP^PhPQPiPMPPPOPjPkP_PcPePlPNPUPX14UXP?COP7MG?X0YX7zS0`PzP3P}P>P?C9RwP7DSP|PUP|P}PwPlEo'3foS0a,4US0b#IRwfqR~Q0aP|P;P{PyPZP]P^PhPQPiPMPPPOPjPkPbPdPePLPNPUP~14U~S0cP?COP7MHQX0YX7wS0dPwP3Q0bP:P>C9P?DS[^0Y^7pP7Q0^Q03PUP{PzQ0`Pz1a}?RzP7DSP|PUP|P}PzPlEo'3PwQ0dPwQ0b/a>P?DS[^0YP7Q0aQ0c#IRwfsRzP~PXQ0aP|PsPvPgPSP]P^PhPQPiPMPPPOP`PLPNPbPUPz14UzS0bP?COP7MG?X0YX7wPwQ0cPUP~P>P?C9'aRwP7DSP~PUP~Q0cPwPNEo'3Q02frS0d,4US0`#IRwftRpQ0dP~PXQ0aPoPsPfPgPSP]P^PhPQPiPMPPPKPcPLPaPUPp14UpS0eP?COP7MG?X0YX7wPwQ0`PUQ0dP:P>C9'aRwP?DSQ0dPUQ0dQ0`PwPLEoQ0b#IS0fQ0ffuRwPzQ0dP~PXP{PoP\PfPgPSP]P^PhPQPiPMP_PbPcP`PaPUPw14UwS0gP?COP7MHQX0YW7Q0fQ0bPUPzP5P:C9'aP>DSP7Q0e#IS0bQ0bfvS0fPpPzQ0dP~P;P{P[P\PfPgPSP]P^PhPQPiPkPaPbPKPUQ0fQ0f,4US0hP?COP7MG?X0YW7Q0bQ0ePUPpP6P5C9'aP:DSPwPUPwQ0gQ0gPUPwP2P6C9'aPaEoQ0fPpPzQ0dP~P;P{P[P\PfPgPSP]P^PhPQPiPkPaPbPKP`P2P6P?P7NJ17Q0h#IS0eQ0efxS0bQ0fPwPpPzQ0aP|PWPVP[P\PfPgPSP]P^PhPOPKP`PkP_PUQ0bQ0b,4UP?COP7MHQX0YW7Q0eQ0hPUQ0fP<P2C9'aP6DSeWNWMP?P7O2n2001000000120000000WLX0YW\Z09UP?P7O2n200110000012110Y10BW7n01106000101Xc3P?P7O2n2001100000121106100X^uP7O1n10110=00020111103X[tN:16L14Q03P3PrPyPrPWPVP[PSP]PkP_PKP`PaPbPcPLPNPdPIPDPCPFPE1ty?P7MHQPvPZPrPWPVPgPSPjPkP_PKP`PaPbPcPLPNPnPEPDPHPFB0J3v>1tv>P?NI0N[^0YP7P3P{PsPvPyPZP[P\PMPPPOPjPkP_PKP`PaPbPePIPHPmPnP3P{P>P?C9,t{P7MHQP;PoPsPvPyPVP[PiPMPPPOPjPkP_PKP`PaPdPnPIPlPmP3P;P:P>C9Rt:0J3;1t;tP?NI0N[^0Y`0BsP7PoPvPyPZPrP\PfPPPOPjPkP_PKP`PaPbPcPlPHPFPnPI1ao?,toP7MHQP7WlX0YX\vn01106000100Xc3P?P7O2n200110000012010610BX^qN:11PW20~W?PBPWP[P\PfPgPhPQP`PaPbPcPLPNPdPePlPmPEQ0;Q0:PCPBNF06Q0YI0jRqeW2WbQ0SQ0XPq[]bQ08>0{VA&0zVQ0AP7PDPiPMPB11=[S0AEcPZPZP?PDPZPWPVP[P\P]P^P_PKP`PaPbPcPLPNPdPePHPCPBPEPDNF06PWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnPIMOLPHQ0UPFQ0VPEQ0WFNS0SEb]@PV&0T7PEPQPiPC11=VS0XEcP5%]?Q02g05K6S0Y,g=S039;Gh&009RqPH11=hS0^P9%>>Q0J/g4Rt=J97S0JDj%h7Q0G#ZS0e#@S0i,D7'3X_JS0j/X>Q0^%<>S0kQ0B#@Ru38S0lQ0E#@R<1C97S0EQ0kg04EgQ0i':S0kQ0lQ0EPE11=rS0mQ0^Q0^Q0l;PRGWCf3VXAq+0GS0lQ0[Q0[%UvS0n%]>%TvS0oPUPvQ0TPFC9S0pQ0]P{PsPvPyPZP[P\PMPPPOPjPkP_PKP`PaPbPePIPHPmAKU{?P7MG?X0YW>V3S0]PZPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmMOLPnQ0UPIQ0VPHQ0WFNS0qG7P7Q039;G]PmPTP9%>6Q0JDjQ0j/X6%<6S03=8TuS0rP<Q0EQ03Q0kQ0rQ0EPI11=vS03PTQ0r=PTRGWCf3VXAq-0GqS0rQ04PqPl11=gRTP9%>2Q0JDjQ0j/X2%<2S0s=8TuS0tP<Q0EQ0sQ0kQ0tQ0EPn11=sS0sPTQ0t=PTRGWCf3VXAqS0tQ0_Q0_%U;S0u%]2%T;S0vPUP;Q0TPmC9S0wPXP|P;P{PoPZPrP^PhPQPiPMPPPOPjPkP_PcPePlPNAKUX?P7MG?X0YX>}V3S0xPoPsPvPyPZPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNMOLPdQ0UPeQ0VPlQ0WFNS0yG7P7Pd11=\S0zP9%>@Q0JDjQ0j/X@Q0z%<@R};8uRTP<Q0EP}Q0kPTQ0EPl11={Q0zQ0z?PTRGWCf3VS0{Q02PNQ0AP9Q05#>AJ9t?DjS0|Q0jQ05'XQ0AQ05#<S0};8uRT#p1C9?R}7~<Q0}Q0kPTP}Pe11=;S0}Q0AQ0A?PTRGW3VS0AQ0cQ0c%U~S0~Q06#]%T~S10PUP~Q0TPNC9S11Q0`PpQ0dP~PXQ0aPoPsPfPgPSP]P^PhPQPiPMPPPKPcPLPaAKUp?P7MG?X0YW>V3S0`Q0aP|P;P{PoPsPvPyPZPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaMOLPbQ0UPcQ0VPLQ0WFNS12G7P7Pc11=WP9Q07#>AJ9t:DjS13Q0j/XAQ0m%<AS14;8uRT#p1C95R}7~<Q14Q0kPTP}PL11=XQ0mQ0m?PTRGW3VS0mQ02Q0jQ08'XS1411=ZRTQ08#<S15;8uR}P<1C96S16Q15Q0kP}Q16Pc11=~PTAPT}RGWCfS16Q0gQ0g%UwS15Q09#]%TwS17PUPwQ0TPaC9S18Q0hQ0bQ0fPwPpPzQ0aP|PWPVP[P\PfPgPSP]P^PhPOPKP`PkQ0b=KU?P7MG?X0YW>V3S0hPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkMOLP_Q0UPKQ0VP`Q0WFNS19G7P7Q0jQ0:'XS1:Q0sQ0;#<R};8uRTP<1C9@R@P}Q0kPTP@P`11=pQ0sQ0s?PTRGWCfS0sQ0211=oRT%<BS1;;8uR@#pQ05,C9R}7~<S1<Q1;Q0kP@P}PK11=wR}PTAPT@RGWS1;fyS1=,4US1>Q1>Q1=#US1?%]CQ1=#TS1@PUQ1=Q0TPkC9S1AfzS1B,4Uf|S1CQ1BQ1=Q0bfwS1DPzQ0dPvPyPZPrPWPVP[P\PfPgPQPOPjPMQ1C=KU?P7MG?X0YW>V3S1EQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVP[P\PfPgPSP]P^PhPQPiPMMOLPPQ0UPOQ0VPjQ0WFNS1FG7P7Q0}%<D'200wuQ07,C97~<S0}%<ER@Q0k11=|RT?8@uR@1C9APjQ0b,1=PTAPT@RGWS1GQ02%<FR@Q0k'DS1HQ0a,1=RT?8@uR@Q08,C9POQ1=,1=S1I/0TAPT@RI0RS1Jf}S1K,4US1LQ1LQ1K#US1M%]HQ1K#TS1NPUQ1KQ0TPMC9S1Of~S1P,4Up+01AS1QQ1PQ1KQ1Cf{S1RQ1DQ0fP;P{PoPsPvPyPZPrPWPVPSPQPiP^Q1Q=KU?P7MG?X0YW>V3S1SQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVP[P\PfPgPSP]P^MOLPhQ0UPQQ0VPiQ0WFNS1TG7P7%<IQ0k'DS1UQ0d,1=R@%<n;8uRTQ0;,C9PiQ1C,1=RA/0@AP@TRI0RS1VQ0211=zRT%<m;8uR@@0Q9BQ1K,1=/0T7HQS1WAPT@RS1Xp+01BS1Y,4US1ZQ1ZQ1Y#US1[%]lQ1Y#TS1\PUQ1YQ0TP^C9S1]p+01CS1^,4Up+01ES1_Q1^Q1YQ1Qp+01@S1`Q1RQ1BP~PXQ0aP|P;P{PoPsPvPyP[PSP]PfQ1_=KU?P7MG?X0YW>V3S1aQ1`Q1PQ1KQ1CQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVP[P\PfMOLPgQ0UPSQ0VP]Q0WFNS1bG7P7%<e,2}1C9D78uQ1`,1=/0}7H^S1cQ0f,1=R}%<d,2}?GuR+0vS1dP1PfQ1D,1=R}AJ9tF:0u9NR@PBI0tS1e%5}1=9@-0:}Q0MQ0G#@S0G+0LR}3qS1f&0sLS1g%>L,=9%}L5;0S1hP0%>cR@AJ9tIRT60E9,=9Q1B,1=S1i#5S1jQ1i%F7S1k'2;q}XZ0P?1=9@1=9T+0BS1lB0r9@TJ0DS1mQ1I#5Q1IQ1l+0:;q}S1lP0%>b,=9Q1R,1=S1I#5Q1IAJ9tmS1n,=9-0B7+0:;q}XZ0P7%}bRTP?J0DS1oQ1jQ1iAJ9tn,=9-0BT+0:;q}S1jPKp+01GS1ip+01FS1pQ1_p+01DS1qQ1^Q1YQ1QQ1`Q1PQ1KQ1CQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVQ0Yg05L9S1rg04F`S1s&0qaQ1s#|S1t3JS1u%]aS1vQ0B#ES1w#ES1x#6S1y#@%<aS1z'2P[P\P]PNPSPWQ0YQ1rPOQ0<Q0=+09S0=Q0YQ1r#>60;1#_d%>aS0<,=9RT%}aS1{5;0%FTRtQ1{#FS1|'kR@P0PJ&0P0P8&0PJ%F?Q1k'kA;0?720p?740oXd0XK0PTPt%ntQ1{Q1|Q1|#nN<0nP>H0mRtP@%5ART%}`S1{1=9lS1}$0CS1~+0BS20#FS21,2AS22/0}S23'3Q1{#FS24Q1}#FS25/2u'2,2A=qT}R8PTQ23PTP7XKJS23Q24127uXKJS26Q25O1S27'2S28O1S29,2AS2:/0}209xTA;xTTe:1qTTPJPJQ01Q23Q0110?7$1pXdJXKJQ22Q2:Q23Q23Q23PJPJg04Jd12?7H1o#nX`JXZJPAPA%nAQ21Q29Q23Q23Q1k#nXK0Q20Q28Q1{Q24Q24#nQ1~Q27Q26Q1}Q25Q25#nH1mJ1lJ1eN:1dP}P}%n}1k}}eN<0nJ1cP?H0mR0P81=9eRT$05S25%FT#5S1}%>_,=9RT$05S26%FT#5S27%}kRT$05S1~%FT#5S24g00[jS1{#|S28Q1{$00S20&1bJS1k&1aJS23&1`JRT20fJ4S29Q0B#Z#M#[#M#[#r#@S21#B3AQ0>-1YTS0>P7P>Q0=21X7>#_dB1WJ4?H1US2:b:b;b<Q21#5P7b8b9b5b4b1b3Q0Y,04eg05M:S21g05M`S22g05NFS013;Q21Q22Q21Q21PxP7g04BeS22Q0?Q22n011040003000000Y0=Q0@Q01P7J0DQ22Q2200<7b2WKS22Q0YQ1r,CJ;G}dK08Q1rQ0=21R47Q0i-1Q7+1PX_JS01Q1r60AJ#_d+0=Q0=PrPAP9%>`Q0JDjQ0j/X`%<`=8AuS0JP<Q0E%hAQ0JQ0E'2S0EQ1i,1=S21/0A7HVQ0EQ0K'0Q0KQ1y#E#`S1y'2S2;PAQ0EQ21Q0H#ZS2<#6$0cS2=':S2>Q0N#6#MS0N#@S2?':S2@'0Q2@Q2=;GAQ0EQ2>Q0O#6#`S0O':S2>'0Q2>?G<AQ0J/0R403403H1L3VCf3VXAqS0J-0GqS2>PqQ0JPmPWQ1IP9Q0<Q1nDjS1nQ0j/XaS0jQ1IQ1|;8uS1|#p1s9mRA7~<S0<Q1I#hS0EQ1|/2ARAQ1p,1=S2@Q1I'0S2A7H[S2BQ0KQ2;Q1I'0S2C5HAS2DQ2@Q2=':S2EQ2?':S2FQ2FQ2=Q1I3GS2G5HAS2HQ2EQ0O':S2EQ2EQ1I7G<S2I5HAS2JQ1|/0RS1|'3S2K'3S2L'3S2M'3S2N'3S2O'3S2P'3S2QPFQ0jQ2PPBQ0<Q2OQ08Q0EQ2NPtP@P0P8Q25Q1}Q26Q27Q1~Q24Q28Q2020>J?S2RQ23PTQ0B#6#[#Z#i#M#M#`S2S#BQ0B,wJRA5ATS2T20aT:60HTS2U&0l3S2VQ2900?A-0@TCRQ0>Q2:b:b;b<X6JXBxQ2S/07S2W/3?S2X%h?[^6J^BxP7Q1Y,1=S2Y&0`OS2Z;8uS2[/0RS2\Q2YQ06O3b8b9S2]b5b4b1b3Q2BQ2MPtP@P0P8Q25Q1}Q26Q27Q1~Q24Q0MQ0Q+0_S2^Q0M#hS2_Q0Q#5%hR[[S2`Q0M#5S2aQ0?Q0MQ0Q<0^?UWOS0QQ2aQ0?%5R[]OS2bQ1^,1=?lPuS2c00k<S2dQ2c#5%5<S2cQ1_,1=?liuS2e/Y<#5[[S2fQ0MQ0G+0_S2gQ2_Q0G#5%h}[[S2_Q2aQ0?Q0MQ0G<0^?UWOS0GQ2aQ0?%5}[]OS2aQ2@?lQu01H<S0?A;J<4S2h$1GQ21?lhuS21Q2100\<-1F<Q21/Y<S2i'2'k[S2jQ2101E<S21%h<p+01HS2k,1=?l^uS2l/Y<S2m#5Q2m/D<'3[S2mQ2l01D<S2l1D<4p+01IS2n,1=?l]uS2o/Y<S2pQ2p/0461C<[S2pQ2o01B<S2oQ2hp+01JS2q,1=?lSuS2r00\<=;J4[S2sQ2r01><S2rQ2hp+01K,1=?lguS2t/Y<Q2t'k[S2hQ0@Q2t01=<S2teS0@Q2tQ28Q2020>J5Q1k7u>S2u20>J6S2vQ1k7u:7u?Q23PTQ0C,wJS0C,xA%Bu'xS2wQ1w,wJ'xS1wQ0D,wJS2x5ATQ0H,wJ=ATA602TS0HQ2VQ0HCRQ0>Q2:b:b;b<X6JX=JXHJXIJXJJA87?uS0H/2>10577H:A8?>uS2y/2:S2z106?7H5[^6J^=J^HJ^IJ^JJP7p+01W,1=S2{Pp1s9iS2|&0`\S2}p+01M,1=S2~PHO6b8p+01LS30,1=S3101<f1s9M78uS32p+01V,1=S33Q31'07HzebUbTbNbMbLb2S34bCbDbEbFbGb9b5b4b1b3Q2DQ2LPtP@P0P8Q25Q1}Q26Q27Q1~Q24Q28Q20Q2RQ23PTQ2UQ2V20aT5S2UQ0K#BQ1y#B'x=ATA602TCRQ0>Q2:b:b;b<X6JXBxX]xQ2XQ2;>1A:?[^6J^Bx^]xP7Q2[1s9cQ0K3GQ2\Q2YQ06O4b8b9S2\b5b4b1b3Q2HQ2KPtP@P0P8Q25Q1}Q26Q27Q1~Q24Q2^Q2`Q0QQ2bQ2dQ2fQ2gQ2_Q0GQ2aQ0?Q2jQ21Q2mQ2lQ2pQ2oQ2sQ2rQ2hQ0@Q2tQ1{g00Yn$0CS2[$0CS2X$0C-0IJQ2X-0IJQ2[-0IJ60YJ60YJg04B9+19Q283JS1{Q20Q2uQ1kQ2v7u:7u?S2uQ23PTQ1x,wJS2vQ2xQ0N#6#`S0N#BS2['y5ATS2XQ2VPTQ1wQ2v5ATQ2x=ATA602TS2vQ2VQ1wQ2xQ2=#BS2;'yS2xQ2?#B'yS1y5ATQ1yQ2;'x=ATA602TCRCRQ0>Q2:b:b;b<X6JX=JXHJXIJXJJQ0N,::,05S1yQ2z105?7H6S2z12>:?8u5S2;Q2=,:6S35Q2?':R6Q2==G6>3H[[^6J^=J^HJ^IJ^JJP7PpQ2{Q2|Q2}Q2~P{PHO7S2~b8Q32Q33Q2=':R6Q2?':R:Q2=Q315G:3HebUbTbNbMbLb2S33bCbDbEbFbGb9b5b4b1b3Q2JQ1|PtP@P0P8Q25Q1}Q26Q27Q1~Q24Q2^Q2`Q0QQ2bQ2dQ2fQ2gQ2_Q0GQ2aQ0?Q2jQ21Q2mQ2lQ2pQ2oQ2sQ2rQ2hQ0@Q2tQ1{Q20Q2uQ23PTQ2XQ2VPTQ2vQ2VQ1wQ2xQ0O#B'yR:5AT%B<,x:=ATA602TCRCRQ0>Q2:b:b;b<X6JX=JXHJXIJXJJQ1yQ2zQ2;Q35Q0O':R:AG:<>3H[[^6J^=J^HJ^IJ^JJQ2~b8Q32Q0O,:6R6Q319G6<3HebUbTbNbMbLb2S32bCbDbEbFbGb9b5b4b1b3PtP@P0P8Q25Q1}Q26Q27Q1~Q24Q28Q2020>J>Q1k7u?S2~Q23PTQ2UQ2wQ0M#BS1yQ0P$0460]JR65ATR:60HTQ2VP:CRQ0>Q2:b:b;b<X6JX=JXBxQ0H=q>RQ2y/0R[^6J^=J^BxP7Q2SQ2Y'0Q2ZQ2YQ06O4b8b9S2Yb5b4b1b3FmFmFmFmQ1nQ0jQ1IQ1z;8uRuP<1C9mRxQ0E12uxRxQ2A7H[Q0K,0xQ2CQ2F,0xQ2GQ2E,0xQ2I10uR4034034033VCf3VS2CeH0Z+0KQ0KQ2FQ2=PWP[Q2@Q2EPGQ1RPGQ1BPGQ1=PGQ0bPGQ1DPGQ0f%|GS2EDvDvDvQ1uN90bS2@ePtP@P0P8Q25Q1}Q26Q27Q1~Q24Q28Q20Q2RQ23PTQ1x#^#^#^#^#^#^#^#@Ru#BQ0i#B'y-0?A-0@TRxQ2VPxCRQ0>Q2:b:b;b<X6JQ0i,:uRu,D71D?u[^6JP7Q2ZQ0:O2b8b9S2Zb5b4b1b3Q1zQ0k'DS0ke-18a14JJ/4J/4J/4JRu$00%|u+09S0iPhPtP@P0P8Q25Q1}Q26Q27Q1~Q24Q28Q20Q2~Q23PTQ0CQ2['y9ATARuQ2VPuCRQ0>Q2:b:b;b<X6JX=JS2[Q0N,:?,07Q0N,:>,0?[^6J^=JS0NP7Q31PvPfO3b8b9S0Cb5b4b1b3PtP@P0P8Q25Q1}Q26Q27Q1~Q24Q28Q20Q2RQ23PTQ2TQ2VQ2TCRQ0>Q2:b:b;b<X6JS2TQ2WQ2S/0?[^6JS2WP7PvPgO2b8b9S2Sb5b4b1b3PtP@P0P8Q25Q1}Q26Q27Q1~Q24Q28Q20Q2RQ23PT20?A6-0@TR6Q2VP6CRQ0>Q2:b:b;b<X6JS2V1D7R1D?R[^6JS2RP7Q31PSO2b8b9S31b5b4b1b3P1PWg048nS27g00UnS26g049kS1},g=$0MQ26#|S253JS2~H07RRP1PWQ1}Q26&0M\Q253JH07R6B0XR6PB0WR6PC{S1xPOPjQ22Q0e#M#MS0e#@S2FQ0Y'0dQ22Q0YQ1r,sJQ0D#ER6#iS0D#6#M#M#`RR3GdOlQ2n,4US0YQ0YQ2n#US1rQ1vQ2n#TS1vPUQ2nQ0TPVC9S2GQ2q,4UQ30Q2qQ2nQ2kQ1iQ1^Q1YQ0bQ1DQ0fPwPpPzQ0dP~PXQ0aPsPrPWPyQ30=KU?P7MG?X0YW>V3S30Q1iQ1pQ1_Q1qQ1^Q1YQ1QQ1`Q1PQ1KQ1CQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyMOLPZQ0UPrQ0VPWQ0WFNS2kG7eb?b?bXb?WSWRP?P7O2n2001000000121000000W2WWP?P7O2n2001000000121000000W2WYP?P7O2n2001000000121000000W2WVP?P7O2n2001000000121000000W2WQP?P7O2n2001000000121000000W2XAqP?P7O2n2011000000121101000W2WPP?P7O2n2011000000121000000O2PyPy&0T?PEPyPrPWPVP[PSP]PkP_PKP`PaPbPcPLPNPdPIPDPCPFPENF06S2nPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnMOLPIQ0UPHQ0VPFQ0WFNS2qEbeW@Z08UP7O1&0d7PEPQPiPCQ0XEcP5%e?Q02g05NlRA,g=Ru9;GhQ0lQ0[Q0[Q0n%e>Q0oQ0pQ0]Q0qG7P7A;G]uQ0rQ04PqQ0tQ0_Q0_Q0u%e2Q0vQ0wQ0xQ0yG7P7Q0{Q02Q0|Q0AQ0cQ0cQ0~Q06#eQ10Q11Q0`Q12G7P7Q13Q0mQ02Q14Q16Q0gQ0gQ15Q09#eQ17Q18Q0hQ19G7P7Q1:Q0sQ02Q1<Q1;Q1>Q1>Q1?%eCQ1@Q1AQ1EQ1FG7P7Q0}Q1GQ02Q1HQ1JQ1LQ1LQ1M%eHQ1NQ1OQ1SQ1TG7P7Q1UQ1VQ02Q1WQ1XQ1ZQ1ZQ1[%elQ1\Q1]Q1aQ1bG7P7Q1cQ1dQ1eQ1fQ1gQ1hQ1mQ1lQ1oQ1jPKQ1iQ1pQ1_Q1qQ1^Q1YQ1QQ1`Q1PQ1KQ1CQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVPAg05P5RuQ1u%eaS2I&0c6Q1z'2P[P\P]PNPSPWPAPuPOQ0=%>u:0;1A#_dPtP@P0P8%>K,=9R6$05Rx%F6#5R61=9dR9$05R:%F9#5R9Q1~Q24Q28Q20Q1kQ23Q29Q0B#6#M#r#[#i#r#`S2A#B5ATQ0>Q2:b:b;b<Q2A#5P7b8b9b5b4b1b3104AeQ221CJu=GA}dK08Q0=Q01>0AJu#_d-0=uQ0=Q2>PqQ0JPmQ1nQ2QPFQ0jQ2PPBQ0<Q2OQ08Q0EQ2NPtP@P0P8PxP6P:P9Q2]b5b4b1b3Q2BQ2MPtP@P0P8PxP6P:P9Q1~Q24Q2^Q2`Q0QQ2bQ2gQ2_Q0GQ2aQ2e00k<S2MQ2e#5Q2cQ2i#5[[R<Q34bCbDbEbFbGb9b5b4b1b3Q2DQ2LPtP@P0P8PxP6P:P9Q2\b5b4b1b3Q2HQ2KPtP@P0P8PxP6P:P9Q1~Q24Q2^Q2`Q0QQ2bQ2gQ2_Q0GQ2aQ2MP<Q33bCbDbEbFbGb9b5b4b1b3Q2JQ1|PtP@P0P8PxP6P:P9Q1~Q24Q2^Q2`Q0QQ2bQ2gQ2_Q0GQ2aQ2MP<Q32bCbDbEbFbGb9b5b4b1b3PtP@P0P8PxP6P:P9Q2Yb5b4b1b3FmFmFmFmQ2CeH0Z+0KQ2@eS2@PtP@P0P8PxP6P:P9Q2Zb5b4b1b3Q0keR<-1TaQ0iPhPtP@P0P8PxP6P:P9Q0Cb5b4b1b3S0CPtP@P0P8PxP6P:P9Q2Sb5b4b1b3S2SPtP@P0P8PxP6P:P9Q31b5b4b1b3S31Q1xPOPjQ22Q2F/0AdQ221sJu=GARdOlQ0YQ0YQ1rQ2IQ1vQ2GQ30Q2kG7eb?b?bXb?WSWRP?P7O2n2001000000121000000W2WWP?P7O2n2001000000121000000W2WYP?P7O2n2001000000121000000W2WVP?P7O2n2001000000121000000W2WQP?P7O2n2001000000121000000W2XAqP?P7O2n2011000000121101000W2WPP?P7O2n2011000000121000000O2PyPy&0d?PEQ2nQ2qEbeW@XaUP7O1&0e7PEPQPiPCQ0XEcP5%d?Q02g05Q<R5,g=RA9;GhQ0lQ0[Q0[Q0n%d>Q0oQ0pQ0]Q0qG7P7A;G]AQ0rQ04PqQ0tQ0_Q0_Q0u%d2Q0vQ0wQ0xQ0yG7P7Q0{Q02Q0|Q0AQ0cQ0cQ0~Q06#dQ10Q11Q0`Q12G7P7Q13Q0mQ02Q14Q16Q0gQ0gQ15Q09#dQ17Q18Q0hQ19G7P7Q1:Q0sQ02Q1<Q1;Q1>Q1>Q1?%dCQ1@Q1AQ1EQ1FG7P7Q0}Q1GQ02Q1HQ1JQ1LQ1LQ1M%dHQ1NQ1OQ1SQ1TG7P7Q1UQ1VQ02Q1WQ1XQ1ZQ1ZQ1[%dlQ1\Q1]Q1aQ1bG7P7Q1cQ1dQ1eQ1fQ1gQ1hQ1mQ1lQ1oQ1jPKQ1iQ1pQ1_Q1qQ1^Q1YQ1QQ1`Q1PQ1KQ1CQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVP5g05RDRoQ1u%daR{Q2<#@Q1z'2P[P\P]PNPSPWP5PoPOQ0=%>o:0;15#_dPtP@P0P8PxP6P:P9Q1~Q24Q28Q20Q1kQ23Q29Q0B#Z#M#^#r#[#r#@R9#B5ATQ0>Q2:b:b;b<%59P7b8b9b5b4b1b31045eQ221CJo=G5}dK08Q0=Q01>0AJo#_d-0=oQ0=Q2@213a<Q0iPhQ0CQ2SQ31Q1xPOPjQ22Q2F/05dQ221sJo=G5RdOlQ0YQ0YQ1rP{Q1vQ2GQ30Q2kG7eb?b?bXb?WSWRP?P7O2n2001000000121000000W2WWP?P7O2n2001000000121000000W2WYP?P7O2n2001000000121000000W2WVP?P7O2n2001000000121000000W2WQP?P7O2n2001000000121000000W2XAqP?P7O2n2011000000121101000W2WPP?P7O2n2011000000121000000O2PyPy&0e?PEQ2nQ2qEbeW@XaUP7O1g05SJRqPCPMPPQ0;Q0zEcPrPrPqPCPrPVP[P\PfP^PhPKP`PaPbPcPLPNPdPePlPFPBQ0;PDPCNF06RqPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnPIPHMOLPFQ0UPEQ0VPDQ0WFNR{Eb00<7W@g05TER5PCPMPPQ0;Q0zEcP>g05U@RoQ02g05V>R<,g=R99;GiQ0LQ0MQ0F#@+0LR:'YQ0e#6#Z#M#`R6'kQ0ZQ0Z%UZP3Po%TZI0VPUPZQ0TPDC9Q0\PsPyPZPrPWPfPgPOPjPkP_PKP`PaPbPcPLPmPFPEPIAKUs?P7MG?X0YW>V3Q0SI0jP7A;Gh9Q0^/Y:/k620S=^11=^R9#5Q0R,D9'3P2PvPyPZPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnPIP<g05WCRVQ1s&126Q1t3JRWPoQ0D#@PHPFPBP>PCPnP<PVQ06Q0=%>V:0;1<#_dQ28Q20Q1kQ23Q29Q0B#Z#M#[#i#i#r#[#@R>#B5ATQ0>Q2:b:b;b<%5>P7b8104<eQ22B0Q<JVR4/0}dK08Q0=Q01>0AJV#_d-0=VQ0=%561D6:'3RV11=]/Y:/k6R:'3PVP:Q28Q20Q1kQ23Q29%B6R65ATQ1yQ0I60]J-0?6-0@T60HTQ0>Q2:b:b;b<PVP7b8P?C{+0KQ0K11=yRyQ2=':R=Q2?':Q2=PnPHPyQ0O,:=PGP]PGP^PGPhPGPQPGPiPGPMQ2EDvDvDvPWN90beg05XFQ0iQ0:Q2[Q0NP7Q03PIQ0:O3b8Q2TQ2WP7PIQ09O2b8Q2VQ2RP7Q03Q08O2b8P1PnQ27Q2~H07RWP1PnQ1}Q26&0MFQ253JH07R1Q07:0XW1Q07:0WW1C{Q06Q05Q22Q2F/0<dQ22104RdOlbrWnWPP?P7O2n2001000000121000000O2PrPrP5PCPqP{EbeW@g05YUR5PCPMPPQ0;Q0zEcPrPrP5PCPqP{Eb00<7W@g05ZPR5PCPMPPQ0;Q0zEcPrPrP5PCPqP{Eb00<7W@n0110<000711108111051110500010000Q06O1bgbeP[P[P\Q0:P[PfPgPSP]PiPMPbPcPLPNPdPePlPmPnPIPCQ09Q08Q0;Q0:NF06PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnPIPHPFPEPDMOLPCQ0UPBQ0VQ0;Q0WFNEbebsWiWpWuWqWkWoWvW@WmWtWhWjZ0;GZ0@JY0PW`Y0>WfZ0WGZ0VGZ0UGZ0TGZ0FGZ0EGZ0NGZ0MGZ0LGZ0KGZ0JGZ0IGZ0HGZ0GGZ07GX~GX}GX|GX{GXzGXyGXxGZ0DGZ0CGZ0SGZ0RGZ0QGZ0XGZ0?GZ0OGY0AY0<&1[7eWwo"). Qed.
