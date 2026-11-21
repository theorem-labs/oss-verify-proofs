(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (L_T1); out_call's ssp cells at this binary's got_ssp and ssp_guard (0xb2dd0, 0x60d2d0)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import Stdio_kit Stdio_kitI F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import Printf_zfacts F_printf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import F_printf_core_common.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_printf_core_t1 () := "C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_printf_iface;fpcall_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF6implAMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4mpadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common6S_HEADC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:map_repeatK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib5BothWDF_printf_core_common7ctx_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common4tinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common3FokC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothWDF_printf_core_common4finvC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib5BothWDF_printf_core_common8lo_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib5BothW>F_printf_iface7args_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib5BothW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4rrngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common3sfxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common4POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common5tregsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8fp_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common8body_locC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef5skipnC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib5BothW9Stdio_kit5inregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common8hi_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common9zb_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zrepeatC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib4LibA5StepF=rng_acc_litZ'C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib6Common7SFModel;signed_of_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;printf_loopC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib5BothWDF_printf_core_common<implAM_eq_msC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z9leb_spec0I47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib5BothW6MonadF<implAM_unr_lC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC45stdpp9bitvector;definitions8bv_swrapK4ELinuxProcessSemantics5Riscv5Instr5instr0=C59OSSVerify5KrLib3Lib8PropExec6v_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C59OSSVerify5KrLib3Lib8PropExec6w_subwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Tac7sum_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC56Stdlib6ZArith4Znat5Z2Nat2idK4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib5BothW:Stdio_kitI<memset_postZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5r_rloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5r_rhiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common7env_nowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common6rc_nowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit>rclean_shcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:Stdio_kitI<memset_callZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC47Corelib5Lists7ListDef6repeatC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01I47Corelib4Init5Logic2or00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common9sink_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib3Mem3zxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemAzext_extract_byteC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib3Lib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC59OSSVerify5KrLib3Lib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib3Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib5BothW9Stdio_kitBrw_cells_bytes_at'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib5BothWDF_printf_core_common9out_postqC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List;repeat_specC46Stdlib5Lists4List=repeat_lengthK47Corelib4Init5Logic3and01C59OSSVerify5KrLib5BothW:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWDF_printf_core_common9out_callqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac>rw_cells_mergeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5BothW6MonadF?implAM_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6ExElim:ex_elim_16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF;implAM_bindC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib3Lib7ZBridge5zr_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6ExElim:ex_elim_15C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;SFW1_lemmas=swrap32_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib5BothWDF_printf_core_common4S_T1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib4LibA5StepF9stepF_genC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappC59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW9Stdio_kit6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib6Common5FmtFp8LEFT_ADJC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8ZERO_PADC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z7inj_addI47Corelib4Init5Logic4True00K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I46Stdlib5Lists4List6Exists00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C59OSSVerify5KrImgGTgt_huf_decompress_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~".
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
        [ match goal with H : rw_cells _ _ 732624 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 6345424 _ |- _ => exact H end ]
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

  Hypothesis HS_T2 : S_T2.

  (* [comment removed for export] *)
  Lemma L_T1 : S_T1.
  Proof.
    intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
           TI FRM FOK Hc Hw Hwq Hcw Hfl0.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
    replace (Z.land fl 73728 =? 0)%Z with true by (rewrite Hfl0; reflexivity). cbn [negb orb].
    ienter. zs. zs. brf K2.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.leb_le _ _)) by lia.
      stmt (HS_T2 fuel HH) as NX2.
      jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
        [ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
    - rewrite (proj2 (Z.leb_gt _ _)) by lia.
      destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implAM_unr_l|].
      set (n4 := (wq - (pl + pq))%Z) in *.
      zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
      zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
      zs. zs.
      apply (rw_cells_split_CB bsegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
      cbn [mk_CB_cells app] in PAD.
      apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
      cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
      zs. callx (memset_pad PADa).
      fix_rsegs. rename MI0 into MI.
      match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
      rewrite (Z.mod_small 32 256) in PADa by lia.
      zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. zs. br K5. clear FLC.
      zs. zs. zs. zs.
      pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
      out_call rstk.
      1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
      1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
      1:{ lia. } 1:{ lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }   (* [comment removed for export] *)
      match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
      match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
        assert (PAD : rw_cells bsegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
        [ cbn [app]; apply (proj2 (rw_cells_app bsegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
        | apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
          replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
      end.
      stmt (HS_T2 fuel HH) as NX2.
      jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
        [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.
End PrintfCore.
End CANSEC1.
