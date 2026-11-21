(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import F_memset F_memcpy Stdio_kit F_syscalls StdioFiles.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import F_printf_iface F_printf_core F_vfprintf.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_pieces Printf_fmts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import F_vfprintf_stdout.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import Printf_bridge.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg Stdio_kit2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_fprintf () := "C47Corelib7Classes?RelationClasses9ReflexiveC59OSSVerify5KrLib5Ubsan>F_printf_iface?sink_frame_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface;SINK_stderrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes3fstI47Corelib4Init5Logic2or00I47Corelib5Lists7ListDef6Forall00K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib5Ubsan:StdioFiles:file_cellsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib6Common<F_fmt_fp_libDForall_disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes3appK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5Ubsan:StdioFiles;GLOBALS_TOPC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib5UbsanAF_vfprintf_stdoutEfile_cells_flags_byteC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib5UbsanAF_vfprintf_stdout<land_mod_lowC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib5Ubsan>F_printf_iface?sink_flags_stmtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib5UbsanAF_vfprintf_stdout=land_sub_maskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9F_fprintf9flags40_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5UbsanAF_vfprintf_stdout9land_low7C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5UbsanAF_vfprintf_stdout;sx32_mod128C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:land_assocC56Stdlib6ZArith6BinInt1Z8land_0_rc59OSSVerify5KrLib5Ubsan9F_fprintf:flags40_32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z@land_lor_distr_rC56Stdlib6ZArith6BinInt1Z7lor_0_rC59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdio_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9F_fprintfAstderr_sink_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface@printf_core_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_pieces>implM_post_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=F_printf_coreAprintf_core_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_pieces5outskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Printf_bridge<FLUSH_stderrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree>impl_ret_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model<printf_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface:OUT_stderrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_ifaceCfwritex_stderr_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_ifaceFstdio_write_flush_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_ifaceFstdio_write_flush_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree:impl_ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface<stderr_wfileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8pass1_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5Ubsan>F_printf_iface7args_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model=printf_piecesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib6Common<Printf_model8fp_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9F_fprintfDvfprintf_stderr_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib5UbsanDF_printf_core_common9zb_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface<OUTFP_stderrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega=RingMicromega5Psatz02K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast=munch_write_nC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib5Lists7ListDef5skipnK4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib5Ubsan>F_printf_ifaceAprintf_core1_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib3Lib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5low32C59OSSVerify5KrLib3Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc59OSSVerify5KrLib5Ubsan9F_fprintf>sflags_noerr_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec<Z_land_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib5UbsanDF_printf_core_common<rw_CB_lengthC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib5Ubsan9F_fprintfAstderr_sink_flagsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface@printf_core_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9F_fprintf?sflags_noerr_32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5Ubsan:F_vfprintf:args_ok_vfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface;fpcall_stmtC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib5Ubsan>F_printf_iface:TOPOK_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface2SRC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3b2zK4ELinuxProcessSemantics5Riscv5Instr5instr0;C59OSSVerify5KrLib3Lib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu32C59OSSVerify5KrLib3Lib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9alu_sltiuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:F_vfprintf6rwc_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib3Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9F_fprintf?sflags_final_40C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9F_fprintf>sflags_olderr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;v_sltiu_b2zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_piecesAprintf_model_outsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C59OSSVerify5KrLib3Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib9StoreFastFbytes_at_write_other_nC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C59OSSVerify5KrLib3Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast;stk_write_nC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface<STATIC_SPLITC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib5Ubsan:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:F_vfprintf8VF_FRAMEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface8VF_DEPTHC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib5Ubsan=F_printf_coreBprintf_core1_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_ifaceAprintf_core1_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface8PC_DEPTHC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C59OSSVerify5KrLib5Ubsan:F_vfprintf=towrite_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface<towrite_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5UbsanAF_vfprintf_stdout:topok_noneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface9OUT_DEPTHC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c59OSSVerify5KrLib5Ubsan9F_fprintfDvfprintf_stderr_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9Stdio_kitBrw_cells_bytes_at'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface=FPRINTF_DEPTHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9F_fprintfEvfprintf_stderr_proofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9F_fprintf@fprintf_gen_stmtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC46Stdlib5Lists4List=Forall_forallC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltI46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib5Ubsan>F_printf_ifaceAfprintf_diag_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=stderr_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Printf_bridge<impl_tforallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9impl_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9F_fprintf?vf_to_diag_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree?impl_epost_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface9diag_argsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Printf_bridgeBoutsk_flush_leavesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Printf_bridge=stderr_bridgeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stderr_fprintfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9F_fprintfAfprintf_gen_proofC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_usageC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appK59OSSVerify5KrLib6Common<Printf_model4parg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:Stdio_kit2<fmt_bytes_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9F_fprintf>forall_range_bC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_piecesCprintf_pieces_usageC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBpieces_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_piecesIprintf_pieces_cannot_openC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioApieces_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_piecesHprintf_pieces_read_errorC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_ifaceAfprintf_diag_stmtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI59OSSVerify5KrLib4Spec6Driver8diag_msg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts;A_FMT_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts9FMT_usageC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C59OSSVerify5KrLib6Common;Printf_fmtsAA_FMT_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts?FMT_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts@A_FMT_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts>FMT_read_errorC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>pieces_too_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts=A_FMT_too_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts;FMT_too_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_piecesEprintf_pieces_too_bigC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg07C1?~~~~~~~~~~~~~~~".
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
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM usegs c s Q ms) | _ => idtac end.

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
               Ft (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
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
      bytes_at usegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDERR (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk usegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x240ec) fc None m (seg_rom usegs)).

  Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
  Proof using FLS FWE.
    unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    (* [comment removed for export] *)
    apply (printf_model_outs usegs OUT_stderr (OUTFP_stderr (St:=St)) fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
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
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
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
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. do 6 zs.
    set (B := bv_unsigned sp + -352) in *.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB usegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
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
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
    ienter. fix_ret.
    pose proof SNK3 as SNK3'. destruct SNK3' as (flags2 & mode2 & tail2 & rest2 & FC3 & FL32 & FL8 & BUF3 & LEN3 & BHI3 & BLO3). cbn [fst] in FC3, BUF3, LEN3.
    unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
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
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m4 MUc WMc; clear MUc WMc end.
    apply impl_ret_intro. cbn [snd]. fix_ret.
    cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
    destruct SNK4 as (flags4 & mode4 & tail4 & rest4 & FC4 & FL32' & FL8' & BUF4 & LEN4 & _ & _). cbn [fst snd] in FC4, BUF4, LEN4.
    unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
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
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact A1|];
        apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
        apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
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
      bytes_at usegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      args_ok RSTDERR (q - 80 - 352) 80 m lo q (q - 80 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk usegs m lo q -> (lo <= q - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x239fc) fc None m (seg_rom usegs)).

  Theorem fprintf_gen_proof : fprintf_gen_stmt.
  Proof using FLS FWE.
    unfold fprintf_gen_stmt. intros until canary. cbv zeta.
    intros -> -> SF BY HF P1 AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA.
    unfold FPRINTF_DEPTH, VF_FRAME, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    carve_frame 80%nat ST.
    do 17 zs.
    apply (proj1 (rw_cells_app usegs _ _ [_;_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
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
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    change usegs with usegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -48)%Z ?rest |- _ =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -80) (hd ++ rest));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
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
ltac2:(KReplay.run1 (kr_t_F_fprintf ()) [] "p'0h03ms'h13AB0h21Hh34LZS0h44cstrh55cstr0h64__x1h71pi001ph87__arithh95cstr1h:4__ffh;8__varmaph<5__with=4__x2h>2bsh?2ABh@2DAhA5slackhB4__p1hC7__sat12hD7__sat13hE7__sat14hF7__sat15hG7__sat16hH4__x3hI4__x4hJ4__x5hK1xi011xhL2H0hM2H1hN2H2hO2HahP3Ha1hQ2BYhR2DJhS2GAhT2H3hU2H4hV2HFhW3LENhX3LZShY3SLKhZ1nh[1ri021rh\2s'h]4__p2h^1ai031ah_1ci041ch`1mha4pathi054pathhb2pshc1ui061uhd1yhe2BRhf1Fhg2FGhh3FLShi3FRMhj3FWEhk3GLOhl2H'hm3Ha0hn2Huho2LOhp2MIhq3QHIhr2R2hs2Rqht2SFhu3SSPhv2SThw2Sthx2a0hy2a1hz2a2h{2a3h|2a4h}2a5h~2a6i072a7i085argv0i091bi0:3bufi0;6canaryi0<1di0=1ei0>2fci0?2gpi0@2loi0A2rai0B1si0C2s0i0D2s1i0E3s10i0F3s11i0G2s2i0H2s3i0I2s4i0J2s5i0K2s6i0L2s7i0M2s8i0N2s9i0O2spi0P2sti0Q2t0i0R2t1i0S2t2i0T2t3i0U2t4i0V2t5i0W2t6i0X2tpi0Y1li0Z1qp%0p%1p%2p%3p&0p&1p;1p;2p;3p;6p;4p;Gp;Op;7p;Hp;:p;Jp;8p;Ip;Fp;5p;<p;9p;Bp200S00g00nSR0p4p710p8Q00g014eR1p4p710p8Q00g01J3R2p4p710p8Q00g04fPR3p4p710p8Q00g04gMR4p4p741110p8Q00g015dR5p4p710p8Q00g0080R6p4p7210p8Q00g04hRR7p4p710p8Q00g04iIR8p4p741110p8Q00g04jAR9p4p710p8Q00g019^R:p4p710p8Q00g04eER;p4p710p8Q00g01?MR<p4p710p8Q00g04kER=p4p741110p8g0054j17Tg005Yk105Tg0067k10GTg00;<j1>Tg002jk21PTg006Zk11@Tg01A:k115Tg00]Vj2nTg00HCj3;k10QTg00=Aj21Tg04lCj6_Tg03JIk41OTg01D=j2:Tg008kS01j20Tg008Mj1CTg00?Ck20MTg00CQj2FTg01HDk210Tg03K;k20|Tg01ICk10yTg01N;k20TTg01Nnk10xTg00?`S02j22Tg004Tk100Tg0044S03j24TP:j1STP5j1TTg00=kj1uTg00;aj48TP6j3KTP2lGATg01K<lOMTg01Knk10lTg01LPk11nTg01MIj7NTg01VBk11ZTP3k31WTg00oHk41STg03GTk61NTg009dk30KTP;mH1KmI0NmF02Tg01W8R;k11JTP1k61Ik50WTP<j4]k20\Tg04mFk41;TP4m:1:Tg04nQk101TP9mJ17TP8m:16Tg04oIk814TP=m:11Tg050Ok20~Tg051Mk30{Tg04^Ck10zTg052Sk10UTg053Nj1[Tg00@Uj1?Tg00QXj3JTg00>Kj2ETg00@;S04k20HTg054Jj1pTg009GR=j23Tg01OWk50tTg01PRj2<Tg01Q2k10sTg00PFk30FTg00BIR8j1DTg054gk20@Tg055>k30rTg00bdk60ETg055]k10qTg00G=k20:Tg056\k309Tg01XMk20pTg01Y0k30oTg03LUm<0nTg03M:k40mTg00OgR9k10CTg042Uk31qTg020Rk11pTg0210k41oTg02cDk61cTg01YMk106Tg00DQk11bTg00Dok11aTg00EMk11`Tg00F8k20fTg00F[k21YTg00GWk21XTg00H]k31VTg00I<k41UTg035ck208Tg057Uk707Tg04_Hk21RTg033Ik21QTg04_ek21MTg04`Ck30=Tg058Wk20<Tg00L_k20ATg00M=j2yTg00Bik20`Tg00Cmk30_Tg059Zk20kTg00`4j2XTg05:Kk21HTg02CEk11GTg05:lk20]Tg01X0k21FTg05;Ik21ETg05<0k21DTg05<Wk21BTg05==k21>Tg05=ck21=Tg021Sk20JTg03hSk30ZTg03i<k219Tg00`Tk30^Tg00N;k40[Tg01DZm90cTg05>_k218Tg01n8k10PTg00R8k40BTg02Vlk30YTg03:6k30XTg00M`j4xTg05?lk10dTg05@gj1`Tg05Aik21TTg05C<k10eTg05D7j1aTg05E8k213Tg05FJk112Tg05GIk11[TP0k70OTg044>k21\TP7k21]Tg03ITk41^Tg00:[k31_Tg00:Aj2|Tg03eYm<0gTg03KomB0VTg00Rnk40iTg00SYk70hTg03e5k60}Tg00a7k71fTg03Nbk81gTg03Mak41hTg00Ink31iTg03ffk71jTg03N?k31kTf0R7#7#7p=t%77#>p=Y%>7#7p=h%>7#>p=e%77#7#7#Cp=dg00ZMR0/07p>1?g00UPR4/07p=5%>7#>#>#>p=g%77#Cp>0Df7R<g00T=R1g00WiR3f6R2f5R6P3f4R5f3R:I0Wf2R>f1R?P7K0Op=61437p=HAK3?7p=sP7P?P>P:P5P6P2P<f8R@f9S05f:S06f;S07f<RAf=S08f>S09f?S0:f@S0;fARBfBRCfCRDfDREfERFg00XiRGfFRHfGRINI0Np=PAK3?79K:>p=LAK3>?9K5:=;67p=mP5P:21\>?P7C]p=RP3P?PGP7C8p=bP5P1P3P:P>P?P7K0Op>0jP6P1P321]5:P>P?P7K0Op=\P1P5P:B0F>?7H1^p=i1F47p=fg00U2RJ@1_?7p=W1EJ7p==13>?/37p=9100>10?7'2p=O1F<21365/0:10>?'|/27'2p=V%p:/X>/0?/27p=c12?7,2>p=U1X>?/07p=~13?7#pp>0w135:/0>/|?/27p>0S1E?7,3>p>0R10>?/|7p=I13>?/07p=G100?/27p>0v%??>0F>7p>0u%D7,3?p>0;10?7,2>p=r1<J7p=}g00\VS0<g00]6S0=7;7p=ZA;J?7p=j20:J7p=og048OR0P0PJPJP9P8P8P:g05HTP>P?P7N<0gp>1mP0P0P0PJPJPJg05I8P8P8P8P=g05IXP6P5P:P>P?P7NB0Vp>1lP0PJPJPJP8P8P6P5P:P>P?P7N<0gp>1ePJPJPJPJPJPJP=P7P?P>P=P:P5P6P2P<P@Q05NB0Vp>1d%77#7#7#7p=^20fJ7p=BP>g00WJR=P3P3g00XIS0>PJP?g00VcP7H0iPGK0hp=@1|>?/27p>0410>?,|:/27p>1L1<?7#Dp=qP?P=P3P3Q0>P7J0}p>0bP>P=P3P3Q0>P?P7K1fp>0IPJP?g00e8P7H0ip>0>P?P=P3P3Q0>P7PGK0hp>0?P:P=P3P3Q0>P>P?P7L1gp=Q1<J7#Dp>0a1<J?#D,3>/37#pp=k1F>?/27p>1CPJP>P?P7H1hp=wB1iJ?7p=zP>P=P3P3Q0>P?P7K1jp>031<J7#D,3?p>1<10?7,|>p>1AB1kJ?7p={P2P6P5P:P>P?P7CxCxp=lP?g00[NS0?P7g04A]S0@Cxp>0LAJ>?79J5:p=vQ00g05J;S0Ag00YIS0B#7S0C#7S0D#7S0E#tS0F#7S0G$05R=$0GRGQ0C#>S0H$0501PGQ0F$05S0I$0GQ0E$05S0J$0GR9$1@\GfSRKg01;`g01>=&156fNRLQ0B#Y#Y#h#h#h#e#Y#dS0K,n=5;GfYRMP<PLfMRNP6fWRO,1=E_P1P@P2fXRP,1=H1O11=MS0Lg04\2':,0<&1?@f[RQ,1=Q0C#CS0MQ0H#>S0N#>S0O#>S0P#CS0Q+0MRR'FQ05-10AQ08-0|1Q0:$0yf_RS-0T=11=SRT#5&0x=S0R,FT'2&00JRU$00S0SfdRV,4URWPW%SVP7%TVPUPV%uJS0TQ0;C8feRW,4URXg04=IRYfgRZPWPVfcR[fbR\f^R]f]R^fTR_PKfRR`fQRafPRbfORcPLPNfLRdfKRePHPCPBPEAKUZ?P7MGAW0W>V3P\faRff`RgPSP]P^f\RhPQfZRiPMPPPOfVRjfURkP_PKP`PaPbPcPLPNPdPefJRlfIRmfHRnPIPHPFPEMOMPDQ0B#t#Y#e#t#e#g#h$0D,n=S0UPC&0lGS0VPB&1n1S0WFNG6S0Xg04;mRoP1&1Z1Rp%HWRqPWPUP3Q0T>1WW?ffRrQ0MP7Q0TH1SZ0:UPBJ1NPZPWPVP[P\P]P^P_PKP`PaPbPcPLPNPdPePHPCPBPEPD1sZ?P7MHPX0YX7qPrPVP[P\PfP^PhPKP`PaPbPcPLPNPdPePlPFPBQ0;PDPCB0K3r71sr7NH1KX7qP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnPIPHPFMOMPEQ0UPDQ0VPCQ0WFNS0YP1PWP?Q0TPBPZPWPVP[P\P]P^P_PKP`PaPbPcPLPNPdPePHPCPBPEPDP?P7MHPX0YX\WQ0YPoP1Pp%HXRs$1JRtPX%SWP3P?%TWPUPWQ0TPBC8J1IRX14UZS0Z#HRufiRvPZPrPWPVPgPSPjPkP_PKP`PaPbPcPLPNPnPEPDPHPUPv14UvS0[P?CLP7MGAX0YX7uRwP?P7C]P;Pup-0RxP?Q0?fhRyPUPy14UyS0\P7PEEmn1011020002001010Z'2X0YX[tPZPWPVP[P\P]P^P_PKP`PaPbPcPLPNPdPePHPCPBPEPDPUPZQ0ZP?CLRzP7MHPX0YX7s-0\sQ0YP1PoPpPtP;14Ur#HRpPxP7Q0?PZPUPZQ0ZP7PDEmn1011020002001010ZX[tPXPZPWPVP[P\P]P^P_PKP`PaPbPcPLPNPdPePHPCPBPEPzP7MGAX0YX7s-0\sQ0YPWP?Q0TPBH1;P7N:1:P;PpQ0\#HRpfjRsPyPZPrPWPfPgPOPjPkP_PKP`PaPbPcPLPmPFPEPIPUPs14UsS0]P?CLRzP7MGAX0YX7pRXP?P7C]P;PpPxP?Q0?PvPUPvQ0[P7PFEmn1011020002001010Z'2Q0[#HR;fkRoPvPyPZPrP\PfPPPOPjPkP_PKP`PaPbPcPlPHPFPnPIPUPo14UoS0^P?CLP7MHPX0YX7;R{P>P?C][^0YP7PuPw&01uP7C]Q0?'2Q02PpPX&01pP?C]Q0?P;P{&01;P>C]P7Q0]#HR;flR{PsPvPyPZP[P\PMPPPOPjPkP_PKP`PaPbPePIPHPmPUP{14U{RpP?CLP7MGAX0YX7;RX&01;P:C]Q0?Q0@%HpRwfnR|P{PoPsPvPWPVPQPiPMPPPOPjPkP_PKP`PNPmPnPePlPUP|14U|R}P?CLP7MHPX0YX7w&01wP6C]eWNWMP?P7O2n2001000000120000000WLX0YQ03P3Q0\P;PXP;P?P7DRA;szH'2Q0^#HRzfmR;PoPsPvPyPVP[PiPMPPPOPjPkP_PKP`PaPdPnPIPlPmPUP;14U;S0_P?CLP7MHPX0YX7zPzP>P?DR[^0YP7P3%H}RzfpRXP|P;P{PoPZPrP^PhPQPiPMPPPOPjPkP_PcPePlPNPUPX14UXP?CLP7MGAX0YX7zS0`PzP3P}P>P?C8RwP7DRP|PUP|P}PwPlEm'2foS0a,4US0b#HRwfqR~Q0aP|P;P{PyPZP]P^PhPQPiPMPPPOPjPkPbPdPePLPNPUP~14U~S0cP?CLP7MHPX0YX7wS0dPwP3Q0bP:P>C8P?DR[^0Y^7pP7Q0^Q03PUP{PzQ0`Pz1b}?RzP7DRP|PUP|P}PzPlEm'2PwQ0dPwQ0b/b>P?DR[^0YP7Q0aQ0c#HRwfsRzP~PXQ0aP|PsPvPgPSP]P^PhPQPiPMPPPOP`PLPNPbPUPz14UzS0bP?CLP7MGAX0YX7wPwQ0cPUP~P>P?C8'bRwP7DRP~PUP~Q0cPwPNEm'2Q02frS0d,4US0`#HRwftRpQ0dP~PXQ0aPoPsPfPgPSP]P^PhPQPiPMPPPKPcPLPaPUPp14UpS0eP?CLP7MGAX0YX7wPwQ0`PUQ0dP:P>C8'bRwP?DRQ0dPUQ0dQ0`PwPLEmQ0b#HS0fQ0ffuRwPzQ0dP~PXP{PoP\PfPgPSP]P^PhPQPiPMP_PbPcP`PaPUPw14UwS0gP?CLP7MHPX0YW7Q0fQ0bPUPzP5P:C8'bP>DRP7Q0e#HS0bQ0bfvS0fPpPzQ0dP~P;P{P[P\PfPgPSP]P^PhPQPiPkPaPbPKPUQ0fQ0f,4US0hP?CLP7MGAX0YW7Q0bQ0ePUPpP6P5C8'bP:DRPwPUPwQ0gQ0gPUPwP2P6C8'bPaEmQ0fPpPzQ0dP~P;P{P[P\PfPgPSP]P^PhPQPiPkPaPbPKP`P2P6P?P7NJ17Q0h#HS0eQ0efxS0bQ0fPwPpPzQ0aP|PWPVP[P\PfPgPSP]P^PhPOPKP`PkP_PUQ0bQ0b,4UP?CLP7MHPX0YW7Q0eQ0hPUQ0fP<P2C8'bP6DReWNWMP?P7O2n2001000000120000000WLX0YW\Z09UP?P7O2n200110000012110Y10BW7n01106000101Xc3P?P7O2n2001100000121106100X^uP7O1n10110=00020111103X[tN:16L14Q03P3PrPyPrPWPVP[PSP]PkP_PKP`PaPbPcPLPNPdPIPDPCPFPE1sy?P7MHPPvPZPrPWPVPgPSPjPkP_PKP`PaPbPcPLPNPnPEPDPHPFB0K3v>1sv>P?NI0N[^0YP7P3P{PsPvPyPZP[P\PMPPPOPjPkP_PKP`PaPbPePIPHPmPnP3P{P>P?C8,s{P7MHPP;PoPsPvPyPVP[PiPMPPPOPjPkP_PKP`PaPdPnPIPlPmP3P;P:P>C8Rt:0K3;1s;tP?NI0N[^0Y`0BsP7PoPvPyPZPrP\PfPPPOPjPkP_PKP`PaPbPcPlPHPFPnPI1bo?,soP7MHPP7WlX0YX\vn01106000100Xc3P?P7O2n200110000012010610BX^qN:11PW20~W?PBPWP[P\PfPgPhPQP`PaPbPcPLPNPdPePlPmPEQ0;Q0:PCPBNF02Q0YI0jRqeW2WbQ0SQ0XPq[]bQ08>0{VA&0zVQ0AP7PDPiPMPB11=[S0AE_PZPZP?PDPZPWPVP[P\P]P^P_PKP`PaPbPcPLPNPdPePHPCPBPEPDNF02PWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnPIMOMPHQ0UPFQ0VPEQ0WFNS0SE\]@PV&0U7PEPQPiPC11=VS0XE_P5%[?Q02g05K6S0Y,n=S039;Gh&009RqPH11=hS0^P9%?>Q0J/n4Rt=J97S0JDi%f7Q0G#tS0e#CS0i,F7'2X_JS0j/W>Q0^%=>S0kQ0B#CRu39S0lQ0E#CR<1E97S0EQ0kg04EgQ0i':S0kQ0lQ0EPE11=rS0mQ0^Q0^Q0l;ORGVCc3UXAq+0HS0lQ0[Q0[%SvS0n%[>%TvS0oPUPvQ0TPFC8S0pQ0]P{PsPvPyPZP[P\PMPPPOPjPkP_PKP`PaPbPePIPHPmAKU{?P7MGAX0YW>V3S0]PZPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmMOMPnQ0UPIQ0VPHQ0WFNS0qG6P7Q039;G]PmPTP9%?6Q0JDiQ0j/W6%=6S03=9TuS0rP<Q0EQ03Q0kQ0rQ0EPI11=vS03PTQ0r=OTRGVCc3UXAq-0HqS0rQ04PqPl11=gRTP9%?2Q0JDiQ0j/W2%=2S0s=9TuS0tP<Q0EQ0sQ0kQ0tQ0EPn11=sS0sPTQ0t=OTRGVCc3UXAqS0tQ0_Q0_%S;S0u%[2%T;S0vPUP;Q0TPmC8S0wPXP|P;P{PoPZPrP^PhPQPiPMPPPOPjPkP_PcPePlPNAKUX?P7MGAX0YX>}V3S0xPoPsPvPyPZPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNMOMPdQ0UPeQ0VPlQ0WFNS0yG6P7Pd11=\S0zP9%?@Q0JDiQ0j/W@Q0z%=@R};9uRTP<Q0EP}Q0kPTQ0EPl11={Q0zQ0z?OTRGVCc3US0{Q02PNQ0AP9Q05#?AJ9t?DiS0|Q0jQ05'WQ0AQ05#=S0};9uRT#p1E9?R}7~<Q0}Q0kPTP}Pe11=;S0}Q0AQ0A?OTRGV3US0AQ0cQ0c%S~S0~Q06#[%T~S10PUP~Q0TPNC8S11Q0`PpQ0dP~PXQ0aPoPsPfPgPSP]P^PhPQPiPMPPPKPcPLPaAKUp?P7MGAX0YW>V3S0`Q0aP|P;P{PoPsPvPyPZPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaMOMPbQ0UPcQ0VPLQ0WFNS12G6P7Pc11=WP9Q07#?AJ9t:DiS13Q0j/WAQ0m%=AS14;9uRT#p1E95R}7~<Q14Q0kPTP}PL11=XQ0mQ0m?OTRGV3US0mQ02Q0jQ08'WS1411=ZRTQ08#=S15;9uR}P<1E96S16Q15Q0kP}Q16Pc11=~PTAOT}RGVCcS16Q0gQ0g%SwS15Q09#[%TwS17PUPwQ0TPaC8S18Q0hQ0bQ0fPwPpPzQ0aP|PWPVP[P\PfPgPSP]P^PhPOPKP`PkQ0b=KU?P7MGAX0YW>V3S0hPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkMOMP_Q0UPKQ0VP`Q0WFNS19G6P7Q0jQ0:'WS1:Q0sQ0;#=R};9uRTP<1E9@R@P}Q0kPTP@P`11=pQ0sQ0s?OTRGVCcS0sQ0211=oRT%=BS1;;9uR@#pQ05,E9R}7~<S1<Q1;Q0kP@P}PK11=wR}PTAOT@RGVS1;fyS1=,4US1>Q1>Q1=#SS1?%[CQ1=#TS1@PUQ1=Q0TPkC8S1AfzS1B,4Uf|S1CQ1BQ1=Q0bfwS1DPzQ0dPvPyPZPrPWPVP[P\PfPgPQPOPjPMQ1C=KU?P7MGAX0YW>V3S1EQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVP[P\PfPgPSP]P^PhPQPiPMMOMPPQ0UPOQ0VPjQ0WFNS1FG6P7Q0}%=D'300wuQ07,E97~<S0}%=ER@Q0k11=|RT?9@uR@1E9APjQ0b,1=PTAOT@RGVS1GQ02%=FR@Q0k'FS1HQ0a,1=RT?9@uR@Q08,E9POQ1=,1=S1I/0TAOT@RI0SS1Jf}S1K,4US1LQ1LQ1K#SS1M%[HQ1K#TS1NPUQ1KQ0TPMC8S1Of~S1P,4Up+01AS1QQ1PQ1KQ1Cf{S1RQ1DQ0fP;P{PoPsPvPyPZPrPWPVPSPQPiP^Q1Q=KU?P7MGAX0YW>V3S1SQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVP[P\PfPgPSP]P^MOMPhQ0UPQQ0VPiQ0WFNS1TG6P7%=IQ0k'FS1UQ0d,1=R@%=n;9uRTQ0;,E9PiQ1C,1=RA/0@AO@TRI0SS1VQ0211=zRT%=m;9uR@@0R9BQ1K,1=/0T7IQS1WAOT@RS1Xp+01BS1Y,4US1ZQ1ZQ1Y#SS1[%[lQ1Y#TS1\PUQ1YQ0TP^C8S1]p+01CS1^,4Up+01ES1_Q1^Q1YQ1Qp+01@S1`Q1RQ1BP~PXQ0aP|P;P{PoPsPvPyP[PSP]PfQ1_=KU?P7MGAX0YW>V3S1aQ1`Q1PQ1KQ1CQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVP[P\PfMOMPgQ0UPSQ0VP]Q0WFNS1bG6P7%=e,3}1E9D79uQ1`,1=/0}7I^S1cQ0f,1=R}%=d,3}?GuR+0vS1dP1PfQ1D,1=R}AJ9tF:0u9NR@PBI0tS1e%5}1<9@-0;}Q0MQ0G#CS1f+0MR}3rS1g&0sLS1h%?L,<9%}L5;0S1iP0%?cR@AJ9tIRT60F9,<9Q1B,1=S1j#5S1kQ1j%D7S1l'3;r}XZ0P?1<9@1<9T+0@S1mB0r9@TJ0ES1nQ1I#5Q1IQ1m+0;;r}S1mP0%?b,<9Q1R,1=S1I#5Q1IAJ9tmS1o,<9-0@7+0;;r}XZ0P7%}bRTP?J0ES1pQ1kQ1jAJ9tn,<9-0@T+0;;r}S1kPKp+01GS1jp+01FS1qQ1_p+01DS1rQ1^Q1YQ1QQ1`Q1PQ1KQ1CQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVQ0Yg05L9S1sg04F`S1t&0qaQ1t#uS1u3JS1v%[aS1wQ0B#>S1x#>S1y#7S1z#C%=aS1{'3P[P\P]PNPSPWQ0YQ1sPOQ0<Q0=+0:S0=Q0YQ1s#?6091#Zd%?aS0<,<9RT%}aS1|5;0%DTRtQ1|#DS1}'jR@P0PJ&0Q0P8&0QJ%D?Q1l'jA;0?720p?740oXd0XK0PTPt%otQ1|Q1}Q1}#oN<0nP>H0mRtP@%5ART%}`S1|1<9lS1~$0CS20+0@S21#DS22,3AS23/0}S24'2Q1|#DS25Q1~#DS26/3u'3,3A=rT}R8PTQ24PTP7XKJS24Q25137uXKJS27Q26O1S28'3S29O1S2:,3AS2;/0}20:xTA;xTTe:1qTTPJPJQ01Q24Q0110?7$1pXdJXKJQ23Q2;Q24Q24Q24PJPJg04Jd13?7H1o#oX`JXZJPAPA%oAQ22Q2:Q24Q24Q1l#oXK0Q21Q29Q1|Q25Q25#oQ20Q28Q27Q1~Q26Q26#oH1mJ1lJ1eN:1dP}P}%o}1j}}eN<0nJ1cP?H0mR0P81<9eRT$06S26%DT#5S1~%?_,<9RT$06S27%DT#5S28%}kRT$06S20%DT#5S25g00[jS1|#uS29Q1|$00S21&1bJS1l&1aJS24&1`JRT20fJ4S2:Q0G#eS0G#^#e#Y#CS22#B3@Q0>-1YTS0>P7P>Q0=21X7>#ZdB1VJ4?H1US2;b:b;b<Q22#5P7b8b9b5b4b1b3Q0Y,04eg05M:S22g05M`S23g05NFS013;Q22Q23Q22Q22PxP7g04BeS23Q0?Q23n011040003000000Y0=Q0@Q01P7J0EQ23Q230087b2WKS23Q0YQ1s,EJ;G}dK07Q1sQ0=21R47Q0i-1Q7+1MX_JS01Q1s60=J#Zd+0<Q0=PrPAP9%?`Q0JDiQ0j/W`%=`=9AuS0JP<Q0E%fAQ0JQ0E'3S0EQ1j,1=S22/0A7IVQ0EQ0K'0Q0KQ1z#>#dS1z'3S2<PAQ0EQ22Q0H#tS2=#7$0DS2>':S2?Q0N#7#^S0N#CS2@':S2A'0Q2AQ2>;GAQ0EQ2?Q0O#7#dS0O':S2?'0Q2??G<AQ0J/0R404404H1L3UCc3UXAqS0J-0HqS2?PqQ0JPmPWQ1IP9Q0<Q1oDiS1oQ0j/WaS0jQ1IQ1};9uS1}#p1q9mRA7~<S0<Q1I#fS0EQ1}/3ARAQ1q,1=S2AQ1I'0S2B7I[S2CQ0KQ2<Q1I'0S2D5IAS2EQ2AQ2>':S2FQ2@':S2GQ2GQ2>Q1I3GS2H5IAS2IQ2FQ0O':S2FQ2FQ1I7G<S2J5IAS2KQ1}/0RS1}'2S2L'2S2M'2S2N'2S2O'2S2P'2S2Q'2S2RPFQ0jQ2QPBQ0<Q2PQ08Q0EQ2OPtP@P0P8Q26Q1~Q27Q28Q20Q25Q29Q2120AJ?S2SQ24PTQ0B#7#e#h#h#^#^#dS2T#BQ0B,yJRA5@TS2U20bT:60ITS2V&0l3S2WQ2:00>A-0?TCQQ0>Q2;b:b;b<X6JXBxQ2T/07S2X/2?S2Y%f?[^6J^BxP7Q1Y,1=S2Z&0aOS2[;9uS2\/0RS2]Q2ZQ06O3b8b9S2^b5b4b1b3Q2CQ2NPtP@P0P8Q26Q1~Q27Q28Q20Q25Q0MQ0Q+0`S2_Q0M#fS2`Q0Q#5%fR[[S2aQ0M#5S2bQ0?Q0MQ0Q<0_?UWOS0QQ2bQ0?%5R[]OS2cQ1^,1=?kPuS2d00k<S2eQ2d#5%5<S2dQ1_,1=?kiuS2f/X<#5[[S2gQ0MQ1f+0`S2hQ2`Q1f#5%f}[[S2`Q2bQ0?Q0MQ1f<0_?UWOS1fQ2bQ0?%5}[]OS2bQ2A?kQu01H<S0?A;J<4S2i$1GQ22?khuS22Q2200]<-1F<Q22/X<S2j'3'j[S2kQ2201E<S22%f<p+01HS2l,1=?k^uS2m/X<S2n#5Q2n/F<'2[S2nQ2m01D<S2m1F<4p+01IS2o,1=?k]uS2p/X<S2qQ2q/0461C<[S2qQ2p01B<S2pQ2ip+01JS2r,1=?kSuS2s00]<=;J4[S2tQ2s01><S2sQ2ip+01K,1=?kguS2u/X<Q2u'j[S2iQ0@Q2u01=<S2ueS0@Q2uQ29Q2120AJ5Q1l7w>S2v20AJ6S2wQ1l7w:7w?Q24PTQ0C,yJS0C,zA%Bu'zS2xQ1x,yJ'zS1xQ0D,yJS2y5@TQ0H,yJ=@TA603TS0HQ2WQ0HCQQ0>Q2;b:b;b<X6JX=JXHJXIJXJJA97?uS0H/3>10577I:A9?>uS2z/3:S2{106?7I5[^6J^=J^HJ^IJ^JJP7p+01W,1=S2|Pp1q9iS2}&0a\S2~p+01M,1=S30PHO6b8p+01LS31,1=S3201<f1q9M79uS33p+01V,1=S34Q32'07IzebUbTbNbMbLb2S35bCbDbEbFbGb9b5b4b1b3Q2EQ2MPtP@P0P8Q26Q1~Q27Q28Q20Q25Q29Q21Q2SQ24PTQ2VQ2W20bT5S2VQ0K#BQ1z#B'z=@TA603TCQQ0>Q2;b:b;b<X6JXBxX]xQ2YQ2<>1A:?[^6J^Bx^]xP7Q2\1q9cQ0K3GQ2]Q2ZQ06O4b8b9S2]b5b4b1b3Q2IQ2LPtP@P0P8Q26Q1~Q27Q28Q20Q25Q2_Q2aQ0QQ2cQ2eQ2gQ2hQ2`Q1fQ2bQ0?Q2kQ22Q2nQ2mQ2qQ2pQ2tQ2sQ2iQ0@Q2uQ1|g00Yn$0CS2\$0CS2Y$0C-0JJQ2Y-0JJQ2\-0JJ60ZJ60ZJg04B9+19Q293JS1|Q21Q2vQ1lQ2w7w:7w?S2vQ24PTQ1y,yJS2wQ2yQ0N#7#dS0N#BS2\'{5@TS2YQ2WPTQ1xQ2w5@TQ2y=@TA603TS2wQ2WQ1xQ2yQ2>#BS2<'{S2yQ2@#B'{S1z5@TQ1zQ2<'z=@TA603TCQCQQ0>Q2;b:b;b<X6JX=JXHJXIJXJJQ0N,::,05S1zQ2{105?7I6S2{13>:?9u5S2<Q2>,:6S36Q2@':R6Q2>=G6>3I[[^6J^=J^HJ^IJ^JJP7PpQ2|Q2}Q2~Q30P{PHO7S30b8Q33Q34Q2>':R6Q2@':R:Q2>Q325G:3IebUbTbNbMbLb2S34bCbDbEbFbGb9b5b4b1b3Q2KQ1}PtP@P0P8Q26Q1~Q27Q28Q20Q25Q2_Q2aQ0QQ2cQ2eQ2gQ2hQ2`Q1fQ2bQ0?Q2kQ22Q2nQ2mQ2qQ2pQ2tQ2sQ2iQ0@Q2uQ1|Q21Q2vQ24PTQ2YQ2WPTQ2wQ2WQ1xQ2yQ0O#B'{R:5@T%B<,z:=@TA603TCQCQQ0>Q2;b:b;b<X6JX=JXHJXIJXJJQ1zQ2{Q2<Q36Q0O':R:AG:<>3I[[^6J^=J^HJ^IJ^JJQ30b8Q33Q0O,:6R6Q329G6<3IebUbTbNbMbLb2S33bCbDbEbFbGb9b5b4b1b3PtP@P0P8Q26Q1~Q27Q28Q20Q25Q29Q2120AJ>Q1l7w?S30Q24PTQ2VQ2xQ0M#BS1zQ0P$0560^JR65@TR:60ITQ2WP:CQQ0>Q2;b:b;b<X6JX=JXBxQ0H=r>RQ2z/0R[^6J^=J^BxP7Q2TQ2Z'0Q2[Q2ZQ06O4b8b9S2Zb5b4b1b3FlFlFlFlQ1oQ0jQ1IQ1{;9uRuP<1E9mRxQ0E13uxRxQ2B7I[Q0K,0xQ2DQ2G,0xQ2HQ2F,0xQ2J10uR4044044043UCc3US2DeH0[+0LQ0KQ2GQ2>PWP[Q2AQ2FPGQ1RPGQ1BPGQ1=PGQ0bPGQ1DPGQ0f%uGS2FDvDvDvQ1vN90cS2AePtP@P0P8Q26Q1~Q27Q28Q20Q25Q29Q21Q2SQ24PTQ1y#g#g#g#g#g#g#g#CRu#BQ0i#B'{-0>A-0?TRxQ2WPxCQQ0>Q2;b:b;b<X6JQ0i,:uRu,F71F?u[^6JP7Q2[Q0:O2b8b9S2[b5b4b1b3Q1{Q0k'FS0ke-18a14JJ/4J/4J/4JRu$00%uu+0:S0iPhPtP@P0P8Q26Q1~Q27Q28Q20Q25Q29Q21Q30Q24PTQ0CQ2\'{9@TARuQ2WPuCQQ0>Q2;b:b;b<X6JX=JS2\Q0N,:?,07Q0N,:>,0?[^6J^=JS0NP7Q32PvPfO3b8b9S0Cb5b4b1b3PtP@P0P8Q26Q1~Q27Q28Q20Q25Q29Q21Q2SQ24PTQ2UQ2WQ2UCQQ0>Q2;b:b;b<X6JS2UQ2XQ2T/0?[^6JS2XP7PvPgO2b8b9S2Tb5b4b1b3PtP@P0P8Q26Q1~Q27Q28Q20Q25Q29Q21Q2SQ24PT20>A6-0?TR6Q2WP6CQQ0>Q2;b:b;b<X6JS2W1F7R1F?R[^6JS2SP7Q32PSO2b8b9S32b5b4b1b3P1PWg048nS28g00UnS27g049kS1~,n=$0PQ27#uS263JS30H0BRRP1PWQ1~Q27&0P\Q263JH0BR6B0YR6PB0XR6PCxS1yPOPjQ23Q0e#^#^S0e#CS2GQ0Y'0dQ23Q0YQ1s,qJQ0B#Y#Y#t#^#^#dR63GdOlQ2o,4US0YQ0YQ2o#SS0BQ1wQ2o#TS1wPUQ2oQ0TPVC8S1sQ2r,4UQ31Q2rQ2oQ2lQ1jQ1^Q1YQ0bQ1DQ0fPwPpPzQ0dP~PXQ0aPsPrPWPyQ31=KU?P7MGAX0YW>V3S31Q1jQ1qQ1_Q1rQ1^Q1YQ1QQ1`Q1PQ1KQ1CQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyMOMPZQ0UPrQ0VPWQ0WFNS2lG6eb?b?bXb?WSWRP?P7O2n2001000000121000000W2WWP?P7O2n2001000000121000000W2WYP?P7O2n2001000000121000000W2WVP?P7O2n2001000000121000000W2WQP?P7O2n2001000000121000000W2XAqP?P7O2n2011000000121101000W2WPP?P7O2n2011000000121000000O2PyPy&0U?PEPyPrPWPVP[PSP]PkP_PKP`PaPbPcPLPNPdPIPDPCPFPENF02S2oPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnMOMPIQ0UPHQ0VPFQ0WFNS2rE\eW@Z08UP7O1&0d7PEPQPiPCQ0XE_P5%`?Q02g05NlRR,n=RA9;GhQ0lQ0[Q0[Q0n%`>Q0oQ0pQ0]Q0qG6P7A;G]AQ0rQ04PqQ0tQ0_Q0_Q0u%`2Q0vQ0wQ0xQ0yG6P7Q0{Q02Q0|Q0AQ0cQ0cQ0~Q06#`Q10Q11Q0`Q12G6P7Q13Q0mQ02Q14Q16Q0gQ0gQ15Q09#`Q17Q18Q0hQ19G6P7Q1:Q0sQ02Q1<Q1;Q1>Q1>Q1?%`CQ1@Q1AQ1EQ1FG6P7Q0}Q1GQ02Q1HQ1JQ1LQ1LQ1M%`HQ1NQ1OQ1SQ1TG6P7Q1UQ1VQ02Q1WQ1XQ1ZQ1ZQ1[%`lQ1\Q1]Q1aQ1bG6P7Q1cQ1dQ1eQ1gQ1hQ1iQ1nQ1mQ1pQ1kPKQ1jQ1qQ1_Q1rQ1^Q1YQ1QQ1`Q1PQ1KQ1CQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVPRg05P5RAQ1v%`aS2HQ0D#>S0D$0DQ1{'3P[P\P]PNPSPWPRPAPOQ0=%?A:091R#ZdPtP@P0P8%?K,<9Ru$06Rx%Du#5Ru1<9dR9$06R:%D9#5R9Q20Q25Q29Q21Q1lQ24Q2:Q0G#>S0G#hS2J#Y#dS2B#B5@TQ0>Q2;b:b;b<Q2B#5P7b8b9b5b4b1b3104ReQ231EJA=GR}dK07Q0=Q01>0=JA#Zd-0<AQ0=Q2?PqQ0JPmQ1oQ2RPFQ0jQ2QPBQ0<Q2PQ08Q0EQ2OPtP@P0P8PxPuP:P9Q2^b5b4b1b3Q2CQ2NPtP@P0P8PxPuP:P9Q20Q25Q2_Q2aQ0QQ2cQ2hQ2`Q1fQ2bQ2f00k<S2NQ2f#5Q2dQ2j#5[[R<Q35bCbDbEbFbGb9b5b4b1b3Q2EQ2MPtP@P0P8PxPuP:P9Q2]b5b4b1b3Q2IQ2LPtP@P0P8PxPuP:P9Q20Q25Q2_Q2aQ0QQ2cQ2hQ2`Q1fQ2bQ2NP<Q34bCbDbEbFbGb9b5b4b1b3Q2KQ1}PtP@P0P8PxPuP:P9Q20Q25Q2_Q2aQ0QQ2cQ2hQ2`Q1fQ2bQ2NP<Q33bCbDbEbFbGb9b5b4b1b3PtP@P0P8PxPuP:P9Q2Zb5b4b1b3FlFlFlFlQ2DeH0[+0LQ2AeS2APtP@P0P8PxPuP:P9Q2[b5b4b1b3Q0keR<-1TaQ0iPhPtP@P0P8PxPuP:P9Q0Cb5b4b1b3S0CPtP@P0P8PxPuP:P9Q2Tb5b4b1b3S2TPtP@P0P8PxPuP:P9Q32b5b4b1b3S32Q1yPOPjQ23Q2G/0RdQ231qJA=GR6dOlQ0YQ0YQ0BQ2HQ1wQ1sQ31Q2lG6eb?b?bXb?WSWRP?P7O2n2001000000121000000W2WWP?P7O2n2001000000121000000W2WYP?P7O2n2001000000121000000W2WVP?P7O2n2001000000121000000W2WQP?P7O2n2001000000121000000W2XAqP?P7O2n2011000000121101000W2WPP?P7O2n2011000000121000000O2PyPy&0d?PEQ2oQ2rE\eW@XaUP7O1&0e7PEPQPiPCQ0XE_P5%a?Q02g05Q<R5,n=RR9;GhQ0lQ0[Q0[Q0n%a>Q0oQ0pQ0]Q0qG6P7A;G]RQ0rQ04PqQ0tQ0_Q0_Q0u%a2Q0vQ0wQ0xQ0yG6P7Q0{Q02Q0|Q0AQ0cQ0cQ0~Q06#aQ10Q11Q0`Q12G6P7Q13Q0mQ02Q14Q16Q0gQ0gQ15Q09#aQ17Q18Q0hQ19G6P7Q1:Q0sQ02Q1<Q1;Q1>Q1>Q1?%aCQ1@Q1AQ1EQ1FG6P7Q0}Q1GQ02Q1HQ1JQ1LQ1LQ1M%aHQ1NQ1OQ1SQ1TG6P7Q1UQ1VQ02Q1WQ1XQ1ZQ1ZQ1[%alQ1\Q1]Q1aQ1bG6P7Q1cQ1dQ1eQ1gQ1hQ1iQ1nQ1mQ1pQ1kPKQ1jQ1qQ1_Q1rQ1^Q1YQ1QQ1`Q1PQ1KQ1CQ1RQ1BQ1=Q0bQ1DQ0fPwPpPzQ0dP~PXQ0aP|P;P{PoPsPvPyPZPrPWPVP5g05RDRoQ1v%aaR{Q2=#CQ1{'3P[P\P]PNPSPWP5PoPOQ0=%?o:0915#ZdPtP@P0P8PxPuP:P9Q20Q25Q29Q21Q1lQ24Q2:Q2J#>#e#Y#CR9#B5@TQ0>Q2;b:b;b<%59P7b8b9b5b4b1b31045eQ231EJo=G5}dK07Q0=Q01>0=Jo#Zd-0<oQ0=Q2A213a<Q0iPhQ0CQ2TQ32Q1yPOPjQ23Q2G/05dQ231qJo=G56dOlQ0YQ0YQ0BP{Q1wQ1sQ31Q2lG6eb?b?bXb?WSWRP?P7O2n2001000000121000000W2WWP?P7O2n2001000000121000000W2WYP?P7O2n2001000000121000000W2WVP?P7O2n2001000000121000000W2WQP?P7O2n2001000000121000000W2XAqP?P7O2n2011000000121101000W2WPP?P7O2n2011000000121000000O2PyPy&0e?PEQ2oQ2rE\eW@XaUP7O1g05SJRqPCPMPPQ0;Q0zE_PrPrPqPCPrPVP[P\PfP^PhPKP`PaPbPcPLPNPdPePlPFPBQ0;PDPCNF02RqPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnPIPHMOMPFQ0UPEQ0VPDQ0WFNR{E\0087W@g05TER5PCPMPPQ0;Q0zE_P>g05U@RoQ02g05V>R<,n=R99;GiQ0LQ0MQ0F#C+0MR:'XQ0e#7#t#^#dRu'jQ0ZQ0Z%SZP3Po%TZI0WPUPZQ0TPDC8Q0\PsPyPZPrPWPfPgPOPjPkP_PKP`PaPbPcPLPmPFPEPIAKUs?P7MGAX0YW>V3Q0SI0jP7A;Gh9Q0^/X:/ju20T=^11=^R9#5Q0R,F9'2P2PvPyPZPrPWPVP[P\PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnPIP<g05WCRVQ1t&12uQ1u3JRWPoQ0D#>$0DPHPFPBP>PCPnP<PVQ06Q0=%?V:091<#ZdQ29Q21Q1lQ24Q2:Q0G#7#h#Y#e#CR>#B5@TQ0>Q2;b:b;b<%5>P7b8104<eQ23B0R<JVR4/0}dK07Q0=Q01>0=JV#Zd-0<VQ0=%5u1Fu:'2RV11=]/X:/juR:'2PVP:Q29Q21Q1lQ24Q2:%BuRu5@TQ1zQ0I60^J-0>u-0?T60ITQ0>Q2;b:b;b<PVP7b8P?Cx+0LQ0K11=yRyQ2>':R=Q2@':Q2>PnPHPyQ0O,:=PGP]PGP^PGPhPGPQPGPiPGPMQ2FDvDvDvPWN90ceg05XFQ0iQ0:Q2\Q0NP7Q03PIQ0:O3b8Q2UQ2XP7PIQ09O2b8Q2WQ2SP7Q03Q08O2b8P1PnQ28Q30H0BRWP1PnQ1~Q27&0PFQ263JH0BR1Q07:0YW1Q07:0XW1CxQ06Q05Q23Q2G/0<dQ231046dOlbrWnWPP?P7O2n2001000000121000000O2PrPrP5PCPqP{E\eW@g05YUR5PCPMPPQ0;Q0zE_PrPrP5PCPqP{E\0087W@g05ZPR5PCPMPPQ0;Q0zE_PrPrP5PCPqP{E\0087W@n0110<000711108111051110500010000Q06O1bgbeP[P[P\Q0:P[PfPgPSP]PiPMPbPcPLPNPdPePlPmPnPIPCQ09Q08Q0;Q0:NF02PfPgPSP]P^PhPQPiPMPPPOPjPkP_PKP`PaPbPcPLPNPdPePlPmPnPIPHPFPEPDMOMPCQ0UPBQ0VQ0;Q0WFNE\ebsWiWpWuWqWkWoWvW@WmWtWhWjZ0;GZ0@JY0PW`Y0>WfZ0WGZ0VGZ0UGZ0TGZ0FGZ0EGZ0NGZ0MGZ0LGZ0KGZ0JGZ0IGZ0HGZ0GGZ07GX~GX}GX|GX{GXzGXyGXxGZ0DGZ0CGZ0SGZ0RGZ0QGZ0XGZ0?GZ0OGY0AY0<&1[7eWwo"). Qed.
