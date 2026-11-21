(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of fl_shl52, L_CV_D replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import SFModel Arr SysStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FP ITree Nodes Decode.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Bytes PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Printf_mlib Printf_zfacts.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import FX_lib F_memset F_memcpy F_memchr I_strnlen F_fwritex F_pop_arg F_printf_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import PrintfModel. (* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import F_printf_core_common.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_m2s I_consts.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import IcptSpec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import F_achk.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
Ltac2 kr_t_F_printf_core_cvd () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z4onesK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC69OSSVerify5KrLib2K53B236FX_lib<zb_land_pow2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K54Spec5Monad5implMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23>F_printf_iface;fpcall_stmtC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC69OSSVerify5KrLib2K53Lib5ITree4implC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec;PrintfModel8conv_intC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23DF_printf_core_common6S_HEADC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree5epostC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53B23DF_printf_core_common7ctx_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23DF_printf_core_common4finvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53B23DF_printf_core_common8lo_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef5skipnC69OSSVerify5KrLib2K53B23>F_printf_iface7args_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53B23DF_printf_core_common3sfxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec;PrintfModel8fp_callsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C69OSSVerify5KrLib2K53B23>F_printf_iface4frm0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23DF_printf_core_common3FokC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib2K53B23DF_printf_core_common1WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23DF_printf_core_common8hi_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236FX_lib2zbC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Monad1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec;PrintfModel:dec_digitsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23DF_printf_core_common4POSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec;PrintfModel;printf_loopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B239F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23DF_printf_core_common9zb_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K53Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC69OSSVerify5KrLib2K53Lib6MState:interp_effC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib2K56Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC69OSSVerify5KrLib2K53Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib2K53Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC69OSSVerify5KrLib2K56Common8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4tgetC4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K53Lib6MState8step_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib2K53Lib7ZBridge=bv_lts_zero_rC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib2K53Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC69OSSVerify5KrLib2K56Common8PropExec5v_subC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib2K56Common8PropExec7alu_subC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C69OSSVerify5KrLib2K53Lib8StepFast8sf_congTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib2K53Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_store_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C69OSSVerify5KrLib2K53Lib8StepFast7sf_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_install_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphI47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib2K53B23DF_printf_core_common:sink_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast=munch_write_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast;stk_write_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC69OSSVerify5KrLib2K56Common8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib2K53Lib8StepFast6sf_ad1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_addr_ztobvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_store8_directC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C69OSSVerify5KrLib2K53Lib8StepFast7sf_btgtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_modC69OSSVerify5KrLib2K53Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C69OSSVerify5KrLib2K53B23DF_printf_core_common7pfx_subC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib2K53B23DF_printf_core_common;implM_eq_msC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236FX_lib7le8_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast:sf_evt_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z6ltb_geC69OSSVerify5KrLib2K56Common8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC69OSSVerify5KrLib2K56Common8PropExec8alu_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C69OSSVerify5KrLib2K53Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23AF_printf_core_cvd8fl_shl52C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init9Datatypes4negbC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6eqb_eqC69OSSVerify5KrLib2K56Common8PropExec6v_andiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC69OSSVerify5KrLib2K56Common8PropExec8alu_andiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23DF_printf_core_common;land_bound'C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC4ELinuxProcessSemantics5Riscv7Prelude4tsetC69OSSVerify5KrLib2K53Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23DF_printf_core_common6S_CV_DC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z3b2zC69OSSVerify5KrLib2K54Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC69OSSVerify5KrLib2K53Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib2K53Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53Lib9StoreFastFbytes_at_write_other_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast@ro_cells_frame_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec;PrintfModel7INT_MAXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib2K53B239FX_Layout7got_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B239FX_Layout9ssp_guardC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec;PrintfModel:INTMAX_MAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec;PrintfModel8MARK_POSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec;PrintfModel7PAD_POSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI69OSSVerify5KrLib2K53Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w0C69OSSVerify5KrLib2K53Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leI69OSSVerify5KrLib2K54Spec;PrintfModel4parg00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop01C69OSSVerify5KrLib2K53B236F_achk9SHADOW_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236F_achk9SHADOW_HIC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:".   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)

Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS X1 N1 X2 N2 : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS X1 N1 X2 N2 SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS X1 N1 X2 N2 SINK TOPOK OUT.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 2^63)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 2224128)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((2270128 <= Fp /\ Fp + 232 <= 2367488) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((7962336 <= B /\ B + BS <= lo /\ B + BS <= 7970816) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis SEP_X1 : (AP + 8 <= X1 /\ X1 + N1 <= VA /\ 0 <= N1)%Z.                 (* [comment removed for export] *)
  Hypothesis SEP_X2 : (7970816 <= X2 /\ X2 + N2 <= lo /\ 0 <= N2 /\ (X2 + N2 <= SHADOW_LO \/ SHADOW_HI <= X2))%Z.   (* [comment removed for export] *)
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  (* [comment removed for export] *)
  Hypothesis RIP : rip_stmt.
  Hypothesis HA0 : aext m0 lo q A fmt B BS X2 N2.

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS X1 N1 X2 N2 q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS X1 N1 X2 N2 SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS X1 N1 X2 N2 ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS X1 N1 X2 N2 SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS X1 N1 X2 N2 SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS X1 N1 X2 N2 q m0 lo A fmt AP VA slots LO SEP_F SEP_B SEP_X1 SEP_X2 HAP HA0).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS X1 N1 X2 N2 q m0 lo A fmt AP VA slots LO SEP_F SEP_B SEP_X1 SEP_X2 HAP HA0).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq Fp B BS X1 N1 X2 N2 q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B SEP_X1 SEP_X2 HAP RIP HA0).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS X1 N1 X2 N2 SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B SEP_X1 SEP_X2 HAP BS0 HA0).
  Local Notation memset_callq := (F_printf_core_common.memset_callq Fp B BS X1 N1 X2 N2 q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B SEP_X1 SEP_X2 HAP RIP HA0).
  Local Notation memset_postq := (F_printf_core_common.memset_postq q gp tp lo).
  Local Notation chkr_W := (F_printf_core_common.chkr_W Fp B BS X1 N1 X2 N2 q m0 lo A fmt AP VA LO SEP_F SEP_B SEP_X1 SEP_X2 HAP HA0).
  Local Notation ictx_W := (F_printf_core_common.ictx_W Fp B BS X1 N1 X2 N2 q m0 lo A fmt AP VA LO SEP_F SEP_B SEP_X1 SEP_X2 HAP HA0).
  Local Notation hsh := (F_printf_core_common.hsh B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation chkr_stack0 := (F_printf_core_common.chkr_stack0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation chkr_fmt0 := (F_printf_core_common.chkr_fmt0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation chkr_pfx0 := (F_printf_core_common.chkr_pfx0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation chkr_xdig0 := (F_printf_core_common.chkr_xdig0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation chkr_nulls0 := (F_printf_core_common.chkr_nulls0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation arg_ok_chk := (F_printf_core_common.arg_ok_chk Fp B BS X1 N1 X2 N2).
  Local Notation chkr_buf0 := (F_printf_core_common.chkr_buf0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS X1 N1 X2 N2 SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B SEP_X1 SEP_X2 HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS X1 N1 X2 N2 SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS X1 N1 X2 N2 SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS X1 N1 X2 N2 q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS X1 N1 X2 N2 q lo AP VA LO GLO SEP_F SEP_B SEP_X1 SEP_X2 HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
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
  Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
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
  Ltac chk0_tac :=
    first [ apply chkr_stack0; try unfold zrepeat; unfold zlength in *; rewrite ?repeat_length, ?Z2Nat.id by lia; lia
          | apply chkr_fmt0; unfold zlength in *; lia
          | apply chkr_pfx0; unfold PFX_A, zlength in *; lia
          | apply chkr_xdig0; unfold XDIG_A, zlength in *; lia
          | match goal with H : chkr m0 ?b ?n |- chkr m0 _ _ => apply (chkr_sub m0 b n _ _ H); unfold zlength in *; lia end ].
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : ro_cells _ _ 2257528 _ |- _ => exact H end
        | match goal with H : ro_cells _ _ 7833176 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | |
      | match goal with H : munch _ m0 _ |- _ => exact H end
      | match goal with H : wmono _ m0 _ |- _ => exact H end
      | chk0_tac ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call asegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac. (* [comment removed for export] *)
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp & BCHK);
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
      repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
    end.

  Hypothesis HS_FMTU : S_FMTU.

  (* [comment removed for export] *)
  Lemma fl_shl52 : forall fl, (0 <= fl < 131072)%Z ->
    (Z.land (Z.shiftl fl 52) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 2048 = 0)%Z.
Proof using .
    clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
    change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia.
    change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    split; intros H; Z.div_mod_to_equations; nia.
  Qed.

  Lemma L_CV_D : S_CV_D.
Proof using BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR SEP_X1 SEP_X2.
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp i pfx s2s za pl plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hi.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    stmt (HS_FMTU fuel HH) as NX.
    pose proof (Z.mod_pos_bound i (2^64) ltac:(lia)) as RA.
    set (argi := (i mod 2^64)%Z) in *.
    unfold INTMAX_MAX, MARK_POS, PAD_POS.
    ienter.
    zs. zs. brf K1.
    - (* [comment removed for export] *)
      zs. zs. zs. zs. zs. zs. zs. zs.
      replace (Z_to_bv 64 (0 - argi)) with (Z_to_bv 64 ((- argi) mod 2 ^ 64)) in * by (apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; f_equal; lia).
      replace (9223372036854775807 <? argi)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      pose proof (Z.mod_pos_bound (- argi) (2^64) ltac:(lia)) as RB.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := ((- argi) mod 2 ^ 64)%Z) (prefix := [45%Z]) (PFXA := 71319%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | intros mq MIq; exact (pfx_sub mq 0 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - replace (9223372036854775807 <? argi)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      zs. zs. zs. zs. zs. brf K2.
      + (* [comment removed for export] *)
        assert (HM : Z.land fl 2048 <> 0%Z) by (intros E; apply (proj2 (fl_shl52 fl Hfl)) in E; lia).
        replace (Z.land fl 2048 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact HM). cbn [negb].
        zs. zs. zs.
        jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [43%Z]) (PFXA := 71320%Z));
          [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
          | intros mq MIq; exact (pfx_sub mq 1 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
      + assert (HM : Z.land fl 2048 = 0%Z) by (apply (proj1 (fl_shl52 fl Hfl)); lia).
        replace (Z.land fl 2048 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact HM). cbn [negb].
        zs. zs. zs. zs. zs.
        pose proof (land_bound' fl 1 ltac:(lia) ltac:(lia)) as B1.
        assert (C1 : (Z.land fl 1 = 0 \/ Z.land fl 1 = 1)%Z).
        { pose proof (Z.land_ones fl 1 ltac:(lia)) as E. change (Z.ones 1) with 1%Z in E. change (2^1)%Z with 2%Z in E. rewrite E.
          pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia. }
        destruct C1 as [E1 | E1]; rewrite E1 in *.
        * (* [comment removed for export] *)
          cbn [Z.eqb negb Z.mul Z.add].
          jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := []) (PFXA := 71319%Z));
            [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
        * (* [comment removed for export] *)
          cbn [Z.eqb negb Z.mul Z.add].
          jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [32%Z]) (PFXA := 71321%Z));
            [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | intros mq MIq; exact (pfx_sub mq 2 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
  Qed.
End PrintfCore.
