(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Monad Stdio Canon PrintfModel.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Printf_pieces Printf_bridge.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import R_small R_m2s I_consts I_qck RT_iface RT_frmkit RT_frmbridge RT_frmrom D_iface D_defs D_kit D_clx.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import X_bridge X_bridge2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import I_iodefs I_lift F_achk F_printf_iface Printf_stdio_iface F_stdout_write F_fwritex_stdout F_vfprintf_stdout I_pcbits I_pchead I_pcfmt I_vprintfw I_vpbridge F_fwrite FX_lib F_pop_arg F_pkit X_open I_read.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_I_vprintf () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib2K53A028RT_iface3rtsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9rng_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53A028RT_iface7fs_sizeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53A028RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53A028RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic2or02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2ex00K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53A028RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53A028RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53A028RT_iface3ARTC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltK69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_consts=region_in_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegc69OSSVerify5KrLib2K53A029I_vprintf=rng_class_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025I_qck8qc_wordsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025I_qck3al8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00C69OSSVerify5KrLib2K53A02@F_fwritex_stdoutDfwritex_stdout_proofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02>F_stdout_writeDstdout_writefn_proofC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init5Peano2ltC69OSSVerify5KrLib2K53A028RT_iface8so_linesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C69OSSVerify5KrLib2K53A028I_iodefs8OUT_repAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6io_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7call_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4PMfdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_iodefs8ERR_repAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS4cpsEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface:af_sp0_winC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC69OSSVerify5KrLib2K53Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib2K53A02:I_vprintfw7pfcellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026F_achk4ictxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC69OSSVerify5KrLib2K53A026I_lift9chk_ok_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025I_qck6chk_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029I_memcpyw6icellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029I_memsetw9icells_msC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:I_strnlenw9icells_snC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025R_m2s9m2s_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_pchead4pctxC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026I_pcrr6pcellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027FX_Exit;stdout_fileC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K53Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:I_vpbridge9emit_progC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree5epostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:I_vprintfw9vpwA_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:I_vprintfw=vprintf_walkAC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit>agree_of_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit9agree_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_iodefsAstdout_file_agreeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53A028I_pcbits3zb8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027I_pcfmt9img_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026FX_lib2zbC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib2K53A025D_kit>rw_cells_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib2K53A029F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit>ro_cells_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029FX_Layout9ssp_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026F_achk5in_rlC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula01C69OSSVerify5KrLib2K53A026F_achk:ictx_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026F_achk4chkrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026F_achk:chkr_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame9stk_splitC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib2K53A028RT_iface<af_acc_stackC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A029I_vprintf7chkr_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow5sh_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026F_achk7rod_chkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_clxCclient_static_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface=af_acc_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02AF_vfprintf_stdoutEvfprintf_stdout_proofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02AF_vfprintf_stdoutDvfprintf_stdout_stmtC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K54Spec;PrintfModel4parg03C1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C69OSSVerify5KrLib2K54Spec;PrintfModel8pass1_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec;PrintfModel=printf_piecesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K54Spec;PrintfModel8fp_callsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02>F_printf_iface4frm0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2K54Spec5Stdio>stdout_towriteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52PGBPrintf_stdio_iface:OUT_stdoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Monad4mretC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52PG=Printf_pieces5outskC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02AF_vfprintf_stdoutDvfprintf_stdout_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Monad5implMC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr05K79OSSVerify5KrLib2K53Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K53Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K53A02:I_vpbridge7vso_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:I_vprintfw=vprintf_walkBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC69OSSVerify5KrLib2K53A026X_open;munch_mergeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame9stk_mergeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028F_fwrite?impl_post_evt''C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree8impl_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface:emit0_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:I_vpbridge7leaf_soC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:I_vpbridge;leaves_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52PG=Printf_bridge<impl_tforallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree9impl_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8rt_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4ARTMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defsBASTA_PM_mat_stableC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC69OSSVerify5KrLib2K53A02:I_vpbridge8tok_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4frmWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3ASTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8af_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026I_read=aclient_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_iodefsCstderr_wfile0_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs;ASTA_conseqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlgArealizes_nonemptyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K52AS8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_frmbridge?impl_realizes_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG8X_bridge2TTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg>t_emit_has_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:I_vpbridge7TT_emitC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53Lib5RzCPS:t_emit_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9emit0_outC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg9t_eq_reflC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC69OSSVerify5KrLib2K52AS8ShapeAlg:t_eq_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_ifaceGvprintf_emit0_icontractC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Canon3evwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface:rt_pres_fpC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree4implC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02>F_printf_iface7args_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K54Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C69OSSVerify5KrLib2K53A028RT_iface9e_vprintfC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2K53A028I_iodefs6IO_FPAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8RT_STACKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026F_achk5PFX_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026F_achk6XDIG_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026F_achk7NULLS_AC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op201I69OSSVerify5KrLib2K53Lib5Nodes4node00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib2K53A026F_pkit8VF_FRAMEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02>F_printf_iface8VF_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029FX_Layout;GLOBALS_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8FMT_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53A025R_m2s>kHighShadowEndC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53A029FX_Layout7got_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029FX_Layout9ssp_guardC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026F_achk3ICRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026F_achk9SHADOW_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026F_achk9SHADOW_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:I_vpbridge7vso_setC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:I_vpbridge6vso_GSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:I_vpbridge6vso_SSC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K54Spec;PrintfModel4parg00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio=pieces_emit_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029FX_Layout<STATIC_SPLITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs8asegs_wxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs;asegs_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029RT_frmrom9asegs_frmC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00".
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pf_consts (m : mem) : Prop :=
  pfcells m /\ ictx m /\ acc asegs m 0x1522f 4 /\ acc asegs m PFX_A 10 /\ acc asegs m XDIG_A 16 /\ acc asegs m NULLS_A 7
  (* [comment removed for export] *)
  /\ acc asegs m 0x166f3 17 /\ acc asegs m 0x201b4 21 /\ acc asegs m 0x201c9 23 /\ acc asegs m 0x1b48e 33.

Section XVprintf.
Variable RT : rt_sig.


Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_PF : forall Σ m, ART RT Σ m -> pf_consts m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Lemma rng_class_sub : forall Σ p n p' n', rng_class RT Σ p n -> p <= p' -> p' + n' <= p + n -> rng_class RT Σ p' n'.
Proof.
  (* LPS 727298f3: the plain proof of leptonica/edge_fuzzer's copy, in place of the recorded replay
     ([rng_class]'s stack bound changed) *)
  intros Σ p n p' n' H H1 H2. unfold rng_class in *.
  destruct H as [(q & k & IN & A1 & A2) | [(f & k & IN & A1 & A2) | [(A1 & A2) | (A1 & A2)]]].
  - left. exists q, k. split; [exact IN| lia].
  - right; left. exists f, k. split; [exact IN| lia].
  - right; right; left. lia.
  - right; right; right. lia.
Qed.

(* [comment removed for export] *)
Lemma chkr_of : forall Σ m p n, ART RT Σ m -> 0 < n <= 2^40 -> acc asegs m p n -> rng_class RT Σ p n -> chkr m p n.
Proof using AF_SHW.
  intros Σ m p n ART0 Hn AC RC. split; [exact AC|]. split.
  - intros i Hi. destruct (AF_SHW Σ m (p + i) 1 ART0 ltac:(lia) (rng_class_sub Σ p n (p + i) 1 RC ltac:(lia) ltac:(lia))) as (QW & _).
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & _). exists w1. exact W1.
  - destruct (AF_SHW Σ m p n ART0 ltac:(lia) RC) as (_ & RIM). split; [exact RIM| lia].
Qed.

Theorem vprintf_ok : vprintf_emit0_icontract RT OUT_repA ERR_repA IO_FPA.
Proof using AF RIP AF_SHW AF_PF.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so ap lo
    Ha0 Ha1 VA APS SO HFD OUT0 (g & SG1 & SG2) ART0 MI0 CALL.
  subst a0 a1. intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  destruct (AF_PF Σ m ART0) as (PFC & IC & ACCF & ACCP & ACCX & ACCN & _).
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  assert (CHKF : chk_ok m 0x1522f 4).
  { apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia|]. intros _. split; [exact ACCF|]. right; right; right. ul. }
  assert (PCX : pctx m).
  { destruct IC as ((G2 & G1 & RM & SHC & RI) & _ & _ & M2S). split; [exact M2S| split; assumption]. }
  (* [comment removed for export] *)
  set (Qfin := fun (x : unit * stdout_st) (ms' : machine_state) => exists (m3 : mem),
         (exists (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
            ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7'
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m3 (seg_rom asegs))
         /\ munch [(lo, usp); (0x102318, 0x102318 + 232); (0x660558, 0x660558 + 1024)] m m3 /\ wmono asegs m m3
         /\ mem_inv asegs m3 /\ stk asegs m3 lo usp /\ stdout_file m3 (snd x)).
  assert (IMPL : impl asegs (at_node asegs) (emit_prog so) (epost Qfin)
                   (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m)).
  assert (L1 : lo <= usp - 2416) by ul.
  assert (L2 : kHighShadowEnd + 8 <= lo) by ul.
  assert (L3 : usp <= 2^47) by ul.
  pose proof (rw_cells_bound asegs m ap _ VA) as APB. cbn [cells_size csize Nat.add] in APB.
  assert (L4 : 0 <= ap < 2^63) by ul.
  { eapply impl_evt;
      [exact (vprintf_walkA RIP usp ap lo ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m ST L1 L2 L3 SPA L4 CHKF PCX PFC MI0)|].
    intros ms1 (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & -> & MU1 & WM1 & MI1 & ST1 & FRf & FRv).
    assert (AG1 : agree_on (fun x => x < usp - 2416 \/ usp <= x) m m1).
    { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [lia| exact I]. }
    assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; ul).
    (* [comment removed for export] *)
    assert (SF1 : stdout_file m1 (vso_get so)).
    { apply (stdout_file_agree so m m1); [| exact WM1| exact OUT0]. apply (agree_sub _ _ _ _ AG1). intros x Hx. ul. }
    assert (BY1 : bytes_at asegs m1 0x1522f (zb [37; 100; 10; 0])) by (apply img_bytes; [exact MI1 | lia | cbn; lia | vm_compute; reflexivity]).
    assert (VA1 : va_area m1 ap [Z_to_bv 64 0]).
    { pose proof (rw_cells_agree asegs m m1 _ _ VA ltac:(apply (agree_sub _ _ _ _ AG1); intros x Hx; cbn [cells_size csize Nat.add] in Hx; ul) WM1) as V.
      exact (proj2 (proj1 V)). }
    assert (SSP1 : ssp_cells m1 g).
    { split.
      - apply (ro_cells_agree asegs m m1 _ _ SG1). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul.
      - apply (ro_cells_agree asegs m m1 _ _ SG2). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul. }
    assert (IC1 : ictx m1) by (apply (ictx_munch _ m m1 IC MU1 WM1); intros ?x ?Hx; cbn [in_rl ICR outside] in *; ul).
    assert (CHM : forall p n, chkr m p n -> chkr m1 p n).
    { intros p n H. apply (chkr_munch _ m m1 p n H MU1). intros x Hx. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hx. ul. }
    pose proof (stk_split asegs m1 lo (lo + 64) (usp + -96) ST1 ltac:(ul)) as (ST1a & ST1b).
    assert (STKC : forall p n, lo + 64 <= p -> p + n <= usp + -96 -> chkr m1 p n).
    { intros p n H1 H2. apply CHM. destruct (Z_lt_le_dec 0 n) as [NP|NN].
      - apply (chkr_of Σ m p n ART0); [ul| | ].
        + apply (af_acc_stack RT AF Σ m p n ART0); ul.
        + right; right; left. ul.
      - split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul. }
    assert (FMTC : chkr m1 0x1522f 4) by (apply CHM; apply (chkr_of Σ m _ _ ART0); [lia| exact ACCF| right; right; right; ul]).
    assert (ROD : rod_chk m1).
    { split; [| split]; apply CHM; (apply (chkr_of Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]). }
    assert (CHBUF : chkr m1 RSTDOUT_BUF 1024).
    { apply CHM. apply (chkr_of Σ m _ _ ART0); [lia| | right; right; right; ul].
      apply (af_acc_static RT AF Σ m _ _ ART0); [lia|]. intros i Hi.
      split; [apply client_static_intro; lia| lia]. }
    pose proof (vfprintf_stdout_proof vso_get vso_set vso_GS vso_SS
                  (fwritex_stdout_proof RIP (fun St get set GS SS => stdout_writefn_proof get set GS SS)) RIP) as VF.
    unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
    pose proof (VF (Z_to_bv 64 0x5a108) (Z_to_bv 64 (usp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 86575) (Z_to_bv 64 1057560)
                  (Z_to_bv 64 1057560) (Z_to_bv 64 86575) (Z_to_bv 64 ap) a3' a4' a5' a6' a7' (Z_to_bv 64 ap) s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6' F fc m1 so 0x1522f ap [37; 100; 10; 0] [Z_to_bv 64 0] [PA_i 0] pieces_emit_0 2 (lo + 64) g) as IM.
    clear VF. unfold Monad.implM in IM.
    eapply impl_post_evt''.
    { apply IM; clear IM; rewrite ?EU96.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact SF1.
      - exact BY1.
      - repeat constructor; lia.
      - vm_compute; reflexivity.
      - exact VA1.
      - cbn [args_ok arg_ok]. split; [| exact I]. split; [lia| reflexivity].
      - vm_compute; reflexivity.
      - vm_compute; reflexivity.
      - exact ST1b.
      - unfold VF_DEPTH; ul.
      - unfold GLOBALS_TOP; ul.
      - ul.
      - exact SSP1.
      - exact MI1.
      - exact I.
      - lia.
      - unfold zlength, STATIC_SPLIT; cbn; lia.
      - lia.
      - unfold zlength; cbn; lia.
      - ul.
      - exact IC1.
      - exact STKC.
      - exact FMTC.
      - exact ROD.
      - exact CHBUF. }
    intros [|[xr st']] ms2 H2; [apply evt_done; exact I|].
    cbn [epost fst snd] in H2 |- *.
    destruct H2 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc2 & m2 & -> & MU2 & WM2 & MI2
                    & _ & _ & ST2 & SF2 & SSP2).
    rewrite EU96 in MU2, ST2.
    rewrite (ret_pc_even 0x5a108) by lia.
    assert (AG2 : agree_on (fun x => usp + -96 <= x) m1 m2).
    { apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn. split; [lia|]. split; [ul| split; [ul| exact I]]. }
    pose proof (rw_cells_agree asegs m1 m2 _ _ FRf ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRf2.
    pose proof (rw_cells_agree asegs m1 m2 _ _ FRv ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRv2.
    eapply evt_mono.
    { apply (vprintf_walkB usp ap (lo + 64) junk (Z_to_bv 64 0x5a108) ra gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 86575) (Z_to_bv 64 1057560)
               b0 b1 b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 ap) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 Ft fc2 m2
               ST2 ltac:(lia) L3 FRf2 FRv2 MI2). }
    intros ms3 ((w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & RS3) & ST3).
    exists m2. split.
    { rewrite RS3. do 17 eexists. reflexivity. }
    split.
    { apply (munch_merge [(usp - 2416, usp)] [(lo + 64, usp + -96); (0x102318, 0x102318 + 232); (0x660558, 0x660558 + 1024)] _ m m1 m2 MU1 MU2).
      intros x Hx. cbn in Hx |- *. intuition lia. }
    split; [exact (wmono_trans asegs m m1 m2 WM1 WM2)|]. split; [exact MI2|].
    split; [| exact SF2]. apply (stk_merge asegs m2 lo (lo + 64) usp); [| exact ST3| ul].
    exact (stk_transport_disjoint asegs _ _ _ _ _ ST1a MU2 WM2 ltac:(cbn [disjoint_from]; ul)). }
  assert (IMPL2 : impl asegs (at_node asegs) (emit_prog so) (epost (fun x ms' => Qfin x ms' /\ snd x = emit0_next so))
                   (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m)).
  { eapply impl_mono; [eapply impl_tforall; [exact (leaves_emit so SO)| exact IMPL]|].
    intros [|x] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I| split; assumption]. }
  (* [comment removed for export] *)
  assert (RZ : realizes asegs c (TT (emit_prog so) (fun _ => t_emit [] T))).
  { apply (impl_realizes_f asegs SEGTOP_A asegs_wx asegs_below asegs_frm [1] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
             (fun x ms' => Qfin x ms' /\ snd x = emit0_next so) (fun _ => t_emit [] T)
             (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m) c
             (ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| | exact (tok_emit so SO)| exact Hc| exact IMPL2|].
    - intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
    - intros mo (_ & _ & _ & HRD). exact HRD.
    - intros x ms' c' (HQ & HX) Hc'.
      assert (R : realizes asegs c' T).
      { apply Hk. eapply ASTA_conseq; [exact Hc'|]. intros ms <-.
        destruct HQ as (m3 & (v & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->)
                        & MU3 & WM3 & MI3 & ST3 & SF3).
        exists v, m3. split.
        { rewrite ESP. do 16 eexists. reflexivity. }
        split; [split; [| split; [exact MI3| split; [exact WM3| exact ST3]]]|].
        - apply (af_frame RT AF Σ m m3 lo ART0); [ul| | exact WM3].
          intros a Ha. apply MU3. cbn. split; [intros Hin; apply Ha; left; ul|].
          split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia|].
          split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia| exact I].
        - split; [| split].
          + intros a Ha Hout. apply MU3. cbn in Hout |- *. destruct Hout as (O1 & O2 & O3 & _). split; [| split; [lia| split; [lia| exact I]]].
            destruct (aclient_split RT AF Σ m usp _ ART0 Ha); ul.
          + rewrite <- HX. exact SF3.
          + intros ERR0. apply (stderr_wfile0_agree m m3); [| exact WM3| exact ERR0].
            apply (agree_of_munch _ _ _ _ MU3). intros y Hy. cbn. split; [ul| split; [lia| split; [lia| exact I]]]. }
      eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty asegs _ _ R). }
  eapply rz_conseq; [exact RZ|].
  eapply t_eq_trans; [apply (TT_emit so (fun _ => t_emit [] T) SO (t_emit_has_nil [] T))|].
  eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.
End XVprintf.
