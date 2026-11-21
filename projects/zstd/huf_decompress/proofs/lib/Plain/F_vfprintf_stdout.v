(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (18 recorded proofs replaced by written proofs (land_mod_low, dec128, land_sub_mask and 15 more)). *)
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
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg Stdio_kit2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_vfprintf_stdout () := "C47Corelib7Classes?RelationClasses9ReflexiveC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z:land_assocC47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses5mkappK47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib5Lists4List8map_consK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z8land_0_lK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulc59OSSVerify5KrLib5PlainAF_vfprintf_stdout=mod_128_of_32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;SFW1_lemmas:swrap32_eqC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic5False00K46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib5PlainAF_vfprintf_stdout<land_mod_lowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdout=land_sub_maskC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdout9land_low7C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdout;sx32_mod128C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z8land_0_rC56Stdlib6ZArith6BinInt1Z@land_lor_distr_lC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface?sink_frame_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface;SINK_stdoutC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec5Stdio9so_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio8so_firstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9so_lbf_nlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles:file_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio8to_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstI47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<F_fmt_fp_libDForall_disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef6firstnC59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6shiftrC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:Stdio_kit2@rw_cells_recast3C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib5PlainAF_vfprintf_stdoutEfile_cells_flags_byteC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib5Plain>F_printf_iface?sink_flags_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface:topok_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface:TOPOK_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib5Plain=F_printf_coreAprintf_core_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_pieces5outskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_towriteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdoutAstdout_sink_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdout;implM_upd_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model<printf_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface<OUTFP_stdoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_ifaceCfwritex_stdout_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles;stdout_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8pass1_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface7args_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model=printf_piecesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib6Common<Printf_model8fp_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdoutDvfprintf_stdout_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common9zb_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common<rw_CB_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast=munch_write_nC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib5Lists7ListDef5skipnC4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib5Plain>F_printf_ifaceAprintf_core1_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib3Lib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5low32C59OSSVerify5KrLib3Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc59OSSVerify5KrLib5PlainAF_vfprintf_stdoutAstdout_sink_flagsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface@printf_core_stmtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdout?flags_noerr_104C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec<Z_land_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface@printf_core_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_vfprintf:args_ok_vfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface;fpcall_stmtC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib5Plain>F_printf_iface2SRC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9alu_sltiuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3b2zC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK4ELinuxProcessSemantics5Riscv5Instr5instr0;C59OSSVerify5KrLib3Lib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu32C59OSSVerify5KrLib3Lib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_vfprintf6rwc_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib3Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdout?flags_olderr_72C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:lor_nonnegC59OSSVerify5KrLib3Lib5Bytes;lor_lt_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7lor_0_lC59OSSVerify5KrLib6Common;SFW1_lemmas>land_W64_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;v_sltiu_b2zC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdout@flags_noerr_nowrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_piecesAprintf_model_outsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5Stdio9stdout_st01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C59OSSVerify5KrLib3Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib3Lib9StoreFastFbytes_at_write_other_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast;stk_write_nC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface<STATIC_SPLITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_vfprintf8VF_FRAMEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface8VF_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles;GLOBALS_TOPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib5Plain=F_printf_coreBprintf_core1_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_ifaceAprintf_core1_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface8PC_DEPTHC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c59OSSVerify5KrLib5PlainAF_vfprintf_stdout:topok_noneC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop05C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_vfprintf=towrite_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface<towrite_stmtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdoutDvfprintf_stdout_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio:out_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_fwritexC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib6Common=Printf_pieces>implM_post_evtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdoutEvfprintf_stdout_proofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdout@out_pieces_outskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface@emit_printf_postC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib4Spec6Driver6s_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_pct_dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9Stdio_kitBrw_cells_bytes_at'C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_pieces9pct_d_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5PlainAF_vfprintf_stdout?stdout_file_stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:Stdio_kit2<fmt_bytes_atC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib6Common=Printf_piecesCprintf_pieces_pct_dC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface@emit_printf_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface:EMIT_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts;A_FMT_pct_dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts9FMT_pct_dC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03".
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
Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
  intros f c k Hk Hc. rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma dec128 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 128)) = true -> forall x, 0 <= x < 128 -> P x = true.
Proof.
  intros P H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma land_sub_mask : forall u a b, Z.land a b = b -> Z.land u a = 0 -> Z.land u b = 0.
Proof. intros u a b Hab Hu. rewrite <- Hab, Z.land_assoc, Hu. apply Z.land_0_l. Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof.
  intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
  rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

(* [comment removed for export] *)
Lemma flags_noerr_nowr : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.
Lemma flags_noerr_104 : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 104 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 104) with 72.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact H.
Qed.
Lemma flags_olderr_72 : forall (flags2 flags : word), Z.land (bv_unsigned flags2) 104 = 0 ->
  Z.land (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32)) 72 = 0.
Proof.
  intros flags2 flags H. rewrite Z.land_lor_distr_l. rewrite <- (Z.land_assoc _ 32 72). change (Z.land 32 72) with 0. rewrite Z.land_0_r, Z.lor_0_r.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdoutSinkProofs.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Let SINK := SINK_stdout (St:=St) get_so.

  Lemma stdout_sink_frame : sink_frame_stmt RSTDOUT RSTDOUT_BUF 1024 SINK.
  Proof using get_so.
    unfold sink_frame_stmt. intros W m m' st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN) MU WM D1 D2.
    split; [exact ACT|]. exists flags, mode, tail, bufbytes.
    split; [|split; [exact FL | split; [| split; [exact PFX | exact LEN]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed.

  Lemma file_cells_flags_byte : forall m A flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
    rw_cells psegs m A (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
    rw_cells psegs m A [CB 1 [Z_to_bv 8 (bv_unsigned flags)]].
  Proof using .
    intros until tail. intros FC. unfold file_cells in FC.
    apply (proj1 (rw_cells_app psegs m A [_] _)) in FC. destruct FC as [F0 _].
    pose proof (rw_cells_recast3 m A _ [CB 1 [Z_to_bv 8 (bv_unsigned flags)]; CB 3 (Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8))] F0
                  ltac:(cbn; repeat split) ltac:(reflexivity)) as F1.
    apply (proj1 (rw_cells_app psegs m A [_] _)) in F1. exact (proj1 F1).
  Qed.

  Lemma stdout_sink_flags : sink_flags_stmt RSTDOUT SINK.
  Proof using get_so.
    unfold sink_flags_stmt. intros m st (ACT & flags & mode & tail & bufbytes & FC & FL & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. eapply land_sub_mask; [|exact FL]. reflexivity.
  Qed.

  Lemma topok_none : topok_stmt TOPOK_none.
  Proof using . unfold topok_stmt, TOPOK_none. intros. exact I. Qed.
End StdoutSinkProofs.

Lemma implM_upd_l {St B} : forall (f : St -> St) (k : unit -> M St B) s Q ms,
  Monad.implM psegs (k tt) (f s) Q ms -> Monad.implM psegs (mbind (mupd f) k) s Q ms.
Proof. intros. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stdout.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
  Hypothesis FWX : fwritex_stdout_stmt.

  Let OUT := stdout_fwritex get_so set_so.
  Let SINK := SINK_stdout (St:=St) get_so.

  Definition vfprintf_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  Definition vfprintf_stdout_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stdout_file m (get_so st) ->
      bytes_at psegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk psegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->
      ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      Monad.implM psegs (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
        (vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x20070) fc None m (seg_rom psegs)).

  Theorem vfprintf_stdout_proof : vfprintf_stdout_stmt.
  Proof using FWX GS SS.
    unfold vfprintf_stdout_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [psegs] in SSP1, SSP2. fold psegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & PFX & BLEN & INACT). unfold file_cells in FC.
    pose proof (rw_CB_length _ _ _ _ BUF) as LBB.
    (* [comment removed for export] *)
    unfold stdout_towrite, upd_so. apply implM_upd_l.
    apply (printf_model_outs psegs OUT (OUTFP_stdout (St:=St)) fmt args ps r (fun _ => mret tt) _ _ _ PP).
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
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
    destruct (so_active (get_so st)) eqn:ACT.
    - (* [comment removed for export] *)
      if_lit. cbv beta iota in FC.
      zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        - unfold SINK, SINK_stdout. rewrite GS, ACT. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode, tail, bufbytes.
          split; [unfold file_cells; exact FC|]. split; [exact FL'|]. split; [exact BUF|]. split; [exact PFX | exact BLEN].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - exact FRM. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m3 MUc WMc; clear MUc WMc end.
      apply implM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [psegs] in SSP1, SSP2. fold psegs in SSP1, SSP2.
      (* [comment removed for export] *)
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      (* [comment removed for export] *)
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      (* [comment removed for export] *)
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells psegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
      split; [exact ST3|].
      split.
      { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
        rewrite ACT3. split; [unfold file_cells; exact FC3|].
        split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
        rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
        pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
        unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
        split; [apply Z.lor_nonneg; lia|].
        apply (lor_lt_pow2 _ _ 64); lia. }
      split; [exact SSP1 | exact SSP2].
    - (* [comment removed for export] *)
      if_lit. cbv beta iota in FC. zs. zs. zs.
      pose proof towrite_proof as TW. unfold towrite_stmt in TW.
      eapply evt_cut.
      { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
        rewrite unsigned_lit; [apply flags_noerr_nowr; exact FL72|].
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      cbv beta. intros ms' P. clear TW.
      destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
      rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      fix_ret.
      zs. if_lit. zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        - unfold SINK, SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, bufbytes.
          change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
          split; [exact FCt|]. split; [exact FL'|]. split; [exact BUF|]. split; [reflexivity | lia].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - exact FRM. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m3 MUc WMc; clear MUc WMc end.
      apply implM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [psegs] in SSP1, SSP2. fold psegs in SSP1, SSP2.
      (* [comment removed for export] *)
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      (* [comment removed for export] *)
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      (* [comment removed for export] *)
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells psegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
      split; [exact ST3|].
      split.
      { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
        rewrite ACT3. split; [unfold file_cells; exact FC3|].
        split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
        rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
        pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
        unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
        split; [apply Z.lor_nonneg; lia|].
        apply (lor_lt_pow2 _ _ 64); lia. }
      split; [exact SSP1 | exact SSP2].
  Qed.
End Stdout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stdout_file_stk : forall m m' so lo hi, stdout_file m so -> munch [(lo, hi)] m m' -> wmono psegs m m' -> GLOBALS_TOP <= lo -> stdout_file m' so.
Proof.
  unfold GLOBALS_TOP.
  intros m m' so lo hi (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM Hlo.
  exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
  - eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia].
  - eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.

Lemma out_pieces_outsk : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) ps,
  out_pieces get_so set_so ps = outsk (stdout_fwritex get_so set_so) ps (mret tt).
Proof. intros St get_so set_so ps. induction ps as [|p ps IH]; cbn [out_pieces outsk]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Theorem emit_printf_proof : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
  emit_printf_stmt get_so set_so.
Proof.
  intros St get_so set_so. unfold emit_printf_stmt. intros until v. intros GS SS FWX SF VR VA1 ST LO GLO QHI SSP MI FRM.
  unfold EMIT_DEPTH, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
  (* [comment removed for export] *)
  unfold s_emit, stdout_vprintf.
  rewrite (out_pieces_outsk St get_so set_so (pieces_pct_d v)).
  ienter.
  carve_frame 80%nat ST.
  do 15 zs.
  (* [comment removed for export] *)
  do 7 zs.
  apply (proj1 (rw_cells_app psegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
  replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
  pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
  change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
  ileave.
  pose proof (vfprintf_stdout_proof get_so set_so GS SS FWX) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
  eapply implM_post_evt.
  { eapply VF with (A := A_FMT_pct_d) (VA := bv_unsigned sp + -56) (fmt := FMT_pct_d) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i v])
                   (r := pct_d_len v) (lo := lo) (canary := canary);
      clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
    all: try reflexivity. all: try lia.
    - eapply stdout_file_stk; [exact SF | exact MU1 | exact WM | unfold GLOBALS_TOP; lia].
    - apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_pct_d; lia | vm_compute; discriminate].
    - unfold FMT_pct_d. forall_range.
    - exact VAA.
    - cbn [args_ok arg_ok]. split; [|exact I]. split; [lia | exact VA1].
    - apply printf_pieces_pct_d. lia.
    - exact ST.
    - split; [exact SSP1 | exact SSP2].
    - exact MI.
    - exact FRM.
    - unfold A_FMT_pct_d, FMT_pct_d. cbn [length]. lia.
    - unfold A_FMT_pct_d, FMT_pct_d. cbn [length]. lia. }
  cbv beta. intros [] st' ms' P. clear MU1.
  unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
  fix_ret.
  zs. zs. zs.
  lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?rest |- _ =>
    assert (FALL : rw_cells psegs mm (bv_unsigned sp + -80) (hd ++ rest));
    [ apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
    | clear FR VAC ] end.
  cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  apply evt_done. unfold emit_printf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
Qed.
