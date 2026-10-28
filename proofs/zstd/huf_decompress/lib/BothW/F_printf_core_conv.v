(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import Stdio_kit Stdio_kitI F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import Printf_zfacts F_printf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import F_printf_core_common.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_printf_core_conv () := "C5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface;fpcall_stmtC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF6implAMC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4convC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common6S_HEADC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_17C46Stdlib5Lists4List?nth_error_skipnC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common7ctx_allC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common4finvK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common8lo_cellsK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface7args_okI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission6Common9SoftFloat9f128_of_dC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model3d_wC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model3d_pC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4d_flC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model3d_tC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common3sfxC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model8fp_callsI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common3FokC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim4znthC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model9conv_typeC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4d_tyK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4d_xpC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common1WC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common8hi_cellsC5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib2zbK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common4POSTC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW9F_pop_arg7va_areaC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common9zb_lengthC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64s_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sC47Corelib4Init3Nat3mulK47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface6arg_okC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib5Arith8PeanoNat3Nat3addC46Stdlib5Lists4List9nth_errorC47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List;skipn_skipnC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common8lo_splitC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common:lo_cells14K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common?conv_type_casesC5ARocqVerifyHarness?AgentSubmission5BothW=Printf_zfacts?conv_type_rangeC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common;land_bound'C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common9nzmask_eqC5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4munrC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3minC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model9conv_tailC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model:dec_digitsC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model8conv_intK5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4parg01C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00I47Corelib4Init5Logic2or00K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3b2zC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission5BothW9F_pop_arg:pop_arg_loC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common4FokdI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common=pop_arg_callqC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common9sink_callC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common9Fok_transC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C46Stdlib4Bool4Bool>negb_false_iffC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common;zbytes_readC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common7fmt_rngC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuK4ELinuxProcessSemantics5Riscv5Instr5instr0:C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_sltiuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9alu_sltiuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z3lebC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge=bv_lts_zero_rC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC56Stdlib6ZArith6BinInt1Z6leb_gtC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common8fl_shl50C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geK4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common:jt1_read_sC5ARocqVerifyHarness?AgentSubmission3Lib2FP9bv_lit_eqK46Stdlib9micromega:ZMicromega;ZArithProof03K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common7lo_joinC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common:arg_ok_s_WC47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6leb_leC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common>land_land_sameC56Stdlib6ZArith6BinInt1Z8land_0_lC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;v_sltiu_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common6u8_litC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF?implAM_from_evtC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF<implAM_unr_lK5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4parg02C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common:jt1_read_dC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common8sx32_intC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model;printf_loopK5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4parg03C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common:jt1_read_uC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx32C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common9zx32_uintC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common:jt1_read_xK5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4parg04C56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common=conv_type_dblC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common;jt1_read_fpC5ARocqVerifyHarness?AgentSubmission6Common9SoftFloat4lo64C5ARocqVerifyHarness?AgentSubmission6Common9SoftFloat4hi64C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common?f128_of_d_rangeC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common6S_CONVC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06C47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model:hex_digitsC47Corelib4Init9Datatypes3orbC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4mretK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission5BothW9F_pop_arg:pop_arg_hiC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportK46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5inregK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common<implAM_eq_msC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission6Common5FmtFp7INT_MAXI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls7got_sspC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9ssp_guardI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission6Common<Printf_model5T_PTRC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model5T_INTC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model6T_UINTC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model5T_DBLC5ARocqVerifyHarness?AgentSubmission6Common5FmtFp:INTMAX_MAXC5ARocqVerifyHarness?AgentSubmission6Common5FmtFp8MARK_POSC5ARocqVerifyHarness?AgentSubmission6Common5FmtFp7PAD_POSC5ARocqVerifyHarness?AgentSubmission6Common5FmtFp8ALT_FORMI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop03C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litI5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00K47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission6Common<Printf_model3dir00I5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4parg00C5ARocqVerifyHarness?AgentSubmission6Common5FmtFp8LEFT_ADJC5ARocqVerifyHarness?AgentSubmission6Common5FmtFp8ZERO_PADI47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize04C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5msize03K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Local Ltac acc_hint ::= lazymatch goal with |- acc_in _ (wa ?e, ?n) => change (wa e) with (Z_to_bv 64 e : word); solve_acc1 end.
  Local Ltac acc_enrich ::=
    repeat match goal with
    | H : nth_error ?l ?k = Some ?x |- _ =>
        lazymatch goal with _ : (k < length l)%nat |- _ => fail | _ => pose proof (nth_error_some_bound l k x H) end
    end;
    rewrite ?u32s_length, ?u64s_length, ?length_app, ?repeat_length, ?zb_length in *; cbn [length] in *; unfold zlength in *.
  Context {St : Type}.
  Variables (Fp B BS : Z) (RB : region) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS RB SINK TOPOK OUT.
  Hypothesis HSTRN : strnlen_a_stmt.
  Variables (RNG : footprint) (rstk rfmt : region).
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 2^47)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 724992)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((737200 <= Fp /\ Fp + 232 <= 762616) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((6345432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  Hypothesis KH : (KHIGH <= lo)%Z.
  Hypothesis RSK : (r_lo rstk <= lo /\ q <= r_hi rstk)%Z.
  Hypothesis RFM : inreg rfmt A (zlength fmt).
  Hypothesis RPF : inreg rfmt 68436 9.
  Hypothesis RBI : inreg RB B BS.
  Hypothesis RG_stk : rng RNG lo (q - lo).
  Hypothesis RG_img : rng_aimg RNG.
  Hypothesis RG_ap : rng RNG AP 8.
  Hypothesis RG_va : rng RNG VA (8 * zlength slots).
  Hypothesis RG_F : rng RNG Fp 232.
  Hypothesis RG_B : rng RNG B BS.
  Hypothesis RG_fmt : rng RNG A (zlength fmt).
  Hypothesis RR_stk : rrng RNG rstk.
  Hypothesis RR_fmt : rrng RNG rfmt.
  Hypothesis RR_B : rrng RNG RB.
  Hypothesis ENV0 : ashenv m0.
  Hypothesis RC_stk : rclean m0 rstk.
  Hypothesis RC_fmt : rclean m0 rfmt.
  Hypothesis RC_B : rclean m0 RB.

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_printf_core_common.ctx_all RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation appW_W := (F_printf_core_common.appW_W Fp B BS RB q m0 lo AP VA LO SEP_F HAP KH RBI RC_B).
  Local Notation ashsafe_W := (F_printf_core_common.ashsafe_W Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP KH).
  Local Notation env_now := (F_printf_core_common.env_now Fp B BS q m0 lo AP VA LO GLO SEP_F SEP_B HAP KH ENV0).
  Local Notation rc_now := (F_printf_core_common.rc_now Fp B BS RB q m0 lo AP VA LO SEP_F HAP KH RBI RC_B).
  Local Notation arg_ok_s_W := (F_printf_core_common.arg_ok_s_W Fp B BS RNG q lo fmt AP slots).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  (* [comment removed for export] *)
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS RB RNG q m0 lo fmt AP VA slots LO SEP_F HAP KH RBI RC_B).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS RB RNG q m0 lo fmt AP VA slots LO SEP_F HAP KH RBI RC_B).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq RNG q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA RG_stk RG_img RG_ap RG_va).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq Fp B BS RB HSTRN RNG q gp tp m0 lo AP VA LO GLO QHI SEP_F SEP_B HAP KH RBI RG_stk RG_img ENV0 RC_B).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS RB SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS RB SINK TOPOK OUTFP TOK RNG q gp tp m0 lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS RB SINK RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS RB SINK RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS RB SINK TOPOK OUTFP RNG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  (* [comment removed for export] *)
  Ltac len_norm := unfold zlength, zrepeat; rewrite ?repeat_length, ?zb_length, ?length_map, ?length_firstn, ?length_skipn, ?length_app; cbn [length]; try rewrite !Z2Nat.id by lia.
  Ltac inreg_side := solve [ unfold inreg in *; len_norm; unfold zlength in *; lia ].
  Ltac rng_side :=
    lazymatch goal with |- rng ?RNG0 ?lo' ?len' =>
      first [ assumption
            | match goal with H : rng RNG0 ?lo ?len |- _ => apply (rng_sub' RNG0 lo len lo' len' H); solve [len_norm; unfold zlength in *; lia] end ]
    end.
  Ltac body_reg_stk := exists rstk; split; [ exact RC_stk | split; [ inreg_side | exact RR_stk ] ].
  Ltac hypMU := match goal with H : munch _ m0 _ |- _ => exact H end.
  Ltac hypWM := match goal with H : wmono _ m0 _ |- _ => exact H end.
  (* [comment removed for export] *)
  Ltac memset_pad PADa :=
    eapply (memset_callZ RNG (r_lo rstk) (r_hi rstk) (r_rlo rstk) (r_rhi rstk));
    [ exact PADa | match goal with H : mem_inv _ _ |- _ => exact H end | lia | lia | lia | lia
    | match goal with H : stk _ _ _ _ |- _ => exact H end | lia | exact KH
    | eapply env_now; [ hypMU | hypWM ]
    | apply rclean_shclean; eapply rc_now; [ exact RC_stk | hypMU | hypWM ]
    | lia | lia | lia | lia | exact RG_img | rng_side | rng_side | exact RR_stk ].
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
    try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
         lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
    try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
         lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
    unfold zlength in *; hush.
  Ltac hyp :=
    lazymatch goal with
    | |- rw_cells _ ?m ?A ?cs =>
        match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
    | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
    end.
  Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
  Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evtF_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
    eapply implAM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  (* [comment removed for export] *)
  Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
    end.
  Local Ltac transport_call_extra segs W m m' MU WM ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ eapply (sink_call W m m' st) in H;
                [ | exact MU | exact WM
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    end.
  Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
  Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
  Local Ltac mem_after_store ::= mem_after_store_fast.
  Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
  Local Ltac lia ::= lia3.
  Ltac out_call_with r :=
    ileave; eapply implAM_bind;
    [ eapply (out_callq r);
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 732688 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 6214544 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | |
      | hypMU | hypWM
      | first [ assumption | idtac ]
      | first [ inreg_side | idtac ]
      | first [ rng_side | idtac ]
      | first [ assumption | idtac ] ]
    | cbv beta ].
  Tactic Notation "out_call" constr(r) := out_call_with r.
  Tactic Notation "out_call" := out_call_with rfmt.
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call bsegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [bsegs bsegs] in *; fold bsegs in *.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    let rb := fresh "rb" in let RCb := fresh "RCb" in let IRb := fresh "IRb" in let RRb := fresh "RRb" in let RGb := fresh "RGb" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & (rb & RCb & IRb & RRb) & RGb & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & PFlo & PFhi & Hi4 & Hfl & HnI & Hnp & Hplp);
    pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
    pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
    let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
  Ltac mk_tinv :=
    lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      unfold tinv, body_loc;
      split; [mk_finv|];
      split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
      split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
      split; [match goal with H : SINK m _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
      split; [lia|];
      split; [assumption|];
      split; [assumption|];
      split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
      split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [first [assumption | reflexivity | lia | zl] |];
      split; [match goal with H : rclean m0 ?r, H2 : inreg ?r _ _, H3 : rrng _ ?r |- _ => exists r; split; [exact H| split; [exact H2| exact H3]] end |];
      split; [assumption|];
      repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
    end.

  Hypothesis HS_CV_D : S_CV_D.
  Hypothesis HS_CV_U : S_CV_U.
  Hypothesis HS_CV_X : S_CV_X.
  Hypothesis HS_CV_S : S_CV_S.
  Hypothesis HS_CV_FP : S_CV_FP.

  (* [comment removed for export] *)
  Lemma L_CONV : S_CONV.
Proof using SFR SFL HF LO GLO QHI HA SEP_F SEP_B HAP HVA VAHI RG_stk RG_img RG_ap RG_va RG_F RG_fmt HS_CV_D HS_CV_U HS_CV_X HS_CV_S HS_CV_FP.
    intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Ht CT Hfl Hw Hp XP Hc.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
    cbn [args_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
    assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
    { rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
    assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
    { replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
    rewrite <- ESK' in AOK.
    destruct (lo_split _ _ _ _ _ _ _ _ _ _ LOW) as (LOW14 & ARGC & J128). unfold lo_cells14, ssp_guard in LOW14. clear LOW.
    pose proof (conv_type_cases _ _ CT) as CASES. pose proof (conv_type_range _ _ CT) as TR.
    pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
    unfold conv. cbv zeta. unfold LEFT_ADJ, ZERO_PAD.
    destruct a as [sv | iv | uv | dd];
      [ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_DBL) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l] ].
    1: assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
    2: assert (TDI : (d_t d = 100 \/ d_t d = 105)%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
    3: assert (TUX : (d_t d = 117 \/ (d_t d = 120 \/ d_t d = 88))%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
    4: assert (TFP : conv_type (d_t d) = Some T_DBL) by (rewrite <- ETY; exact CT).
    4: pose proof (proj1 (conv_type_dbl _ TFP)) as TFR.
    3: destruct TUX as [T117 | TX];
         [ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t d =? 117)%Z with false by (symmetry; apply Z.eqb_neq; lia) ].
    all: ienter; zs; br K; zs; zs; zs; zs.
    all: callx (eapply pop_arg_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_DBL; lia]).
    all: idtac.
    all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC'; rewrite ETY in ARGC'; cbn [pop_arg_lo pop_arg_hi F_pop_arg.T_PTR F_pop_arg.T_INT F_pop_arg.T_UINT F_pop_arg.T_DBL T_PTR T_INT T_UINT T_DBL Z.eqb Pos.eqb] in ARGC' end.
    all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
    all: zs.
    all: match goal with H : SINK ?mm _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB) end; zs; zs; zs; br K1; clear FLC.
    all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
    all: zsto 0xa834c%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; br K2a; zsto 0xa8360%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
      [ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
      | assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
        rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
    all: zsto 0xa8370%Z; zs; br K3; zsto 0xa8384%Z.
    all: replace (Z.shiftl (d_t d + -65) 2 + 140000)%Z with (140000 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).
    all: first [ the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_fp _ _ M TFP) as RD1) ].
    all: zs; zs; zs.
    all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
    all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
      lazymatch pc with
      | 689192%Z =>
          rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          match goal with MUc : munch _ m0 mm |- _ =>
            destruct (arg_ok_s_W _ _ _ _ AOK1 MUc) as (slack & STR & SRNG & SPAD & P0 & SD1 & SD2 & SD3 & SD4 & SD5 & RGS & rs & RCS & IRS & RRS) end;
          stmt (HS_CV_S fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                 (xp := d_xp d) (P := bv_unsigned slot) (s := sv) (slack := slack));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | exact P0 | exact SD1 | exact SD2 | exact SD3 | exact SD5
          | exact RGS | exists rs; split; [exact RCS | split; [exact IRS | exact RRS]]
          | subst fl'; rewrite ?land_land_same; reflexivity ]
      | 689120%Z =>
          destruct AOK1 as [Hiv Emod];
          rewrite (sx32_int slot iv Hiv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_D fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hiv ]
      | 689432%Z =>
          destruct AOK1 as [Huv Emod];
          rewrite (zx32_uint slot uv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_U fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv ]
      | 689552%Z =>
          destruct AOK1 as [Huv Emod];
          rewrite (zx32_uint slot uv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_X fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv | exact TX ]
      | 689040%Z =>
          cbn [arg_ok] in AOK1; rewrite AOK1 in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          unfold LEFT_ADJ, ZERO_PAD in FPC1;
          first [ rewrite (proj2 (Z.eqb_eq _ _) K2) in FPC1 | rewrite (proj2 (Z.eqb_neq _ _) K2') in FPC1 ]; rewrite ?ift, ?iff in FPC1;
          stmt (HS_CV_FP fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (y := f128_of_d dd) (t := d_t d));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | subst fl'; exact FPC1 | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | apply f128_of_d_range | exact TFP ]
      end end.
  Qed.
End PrintfCore.
End CANSEC1.
