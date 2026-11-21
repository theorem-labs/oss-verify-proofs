(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded (KReplay) proof of fwrite_ok re-proved by tactics after leptonica/kernel_fuzzer's text at this binary's addresses, with the channel-reader premise of impl_realizes_f discharged from PMfd). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Monad Stdio Canon.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import R_small R_m2s I_consts RT_iface RT_frmkit RT_frmbridge RT_frmrom D_iface D_defs D_kit D_clx FX_Stdio_iface F_towrite F_fwrite.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import X_bridge X_bridge2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import I_readw2 I_read I_fwritew I_iodefs X_open.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_I_fwrite () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List9app_nil_rC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List7map_mapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List7map_extK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K52AG6Shadow7acc_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_consts=acc_word_zeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib2K53Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53A028I_consts8LIT_BLK1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_consts8LIT_BLK2C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib5Lists4List6map_idC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_mapC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC45stdpp9bitvector;definitions:bv_modulusK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08I46Stdlib5Lists4List6Exists00K46Stdlib9micromega=RingMicromega3Op205K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C69OSSVerify5KrLib2K54Spec5Canon3evwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio8to_bytesC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib2K53A028RT_iface3rtsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init5Logic2or00C69OSSVerify5KrLib2K53A028RT_iface;checked_srcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C69OSSVerify5KrLib2K53A028I_iodefs8ERR_repAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6io_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7call_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4PMfdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_iodefs8OUT_repAC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53A028RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface:af_sp0_winC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib2K53Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025R_m2s9m2s_cellsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028I_fwrite9lit_wordsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3powC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02C46Stdlib5Lists4List:length_mapC69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02>FX_Stdio_iface=stderr_wfile0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K53Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree5epostC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2K53A029I_fwritew<fwrite_walkAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit>agree_of_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit9agree_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_iodefsCstderr_wfile0_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit>bytes_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028I_fwriteEmap_to_bytes_unsignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit>ro_cells_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029FX_Layout9ssp_cellsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028I_fwriteDForall_unsigned_byteC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib2K53A028F_fwriteAfwrite_diag_proofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio=stderr_fwriteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Monad1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02>FX_Stdio_iface@fwrite_diag_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Monad5implMC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK79OSSVerify5KrLib2K53Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K53Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit>rw_cells_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53A025D_kit;agree_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029I_fwritew<fwrite_walkBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula02C47Corelib4Init5Logic7and_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC69OSSVerify5KrLib2K53A026X_open;munch_mergeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028F_fwrite?impl_post_evt''C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree8impl_evtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC69OSSVerify5KrLib2K54Spec5Stdio<stdio_writevC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Monad4mretC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG8X_bridge3tokC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC69OSSVerify5KrLib2K54Spec5Stdio9iov_startC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio7WV_FUELC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib5Lists4List6concatC69OSSVerify5KrLib2K54Spec5Stdio9iov_totalC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG9X_bridge2;tok_wv_loopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8rt_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4ARTMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defsBASTA_PM_mat_stableC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC69OSSVerify5KrLib2K53A028RT_iface4frmWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3ASTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_clxCclient_static_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8af_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026I_read=aclient_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_iodefsAstdout_file_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs;ASTA_conseqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlgArealizes_nonemptyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K52AS8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_frmbridge?impl_realizes_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG8X_bridge2TTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio7wv_bodyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Monad5mloopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg>t_emit_has_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG9X_bridge2:TT_wv_loopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:t_emit_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg9t_eq_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg:t_eq_transC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028I_fwrite<evw_to_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_ifaceGfwrite_stderr_icontractC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface:rt_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS4cpsEC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib2K54Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree4implC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z3maxI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C69OSSVerify5KrLib2K53A028RT_iface8e_fwriteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_iodefs6IO_FPAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2K53A028RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8RT_STACKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026Layout=g_asan_initedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_consts;g_REAL_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_consts6RS_PADC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_consts=g_REAL_fwriteC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega:ZMicromega;ZArithProof01I69OSSVerify5KrLib2K53Lib5Nodes4node00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib2K53A028RT_iface;STDERR_FILEC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K54Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53A028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_consts;e_musl_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_consts=e_musl_fwriteC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53A029FX_Layout7got_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029FX_Layout9ssp_guardC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029F_towrite=towrite_proofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02>FX_Stdio_iface<FWRITE_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029FX_Layout;GLOBALS_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3SHBC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison02C69OSSVerify5KrLib2K53A025R_m2s;kHighMemEndC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs8asegs_wxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs;asegs_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029RT_frmrom9asegs_frmC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma lit_words : forall m, acc asegs m LIT_BLK1 128 -> acc asegs m LIT_BLK2 128 ->
  ro_cells asegs m 0x7fffc580 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] /\ ro_cells asegs m 0x7ffface0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
ltac2:(KReplay.run1 (kr_t_I_fwrite ()) [] "h07__arithh14__ffh28__varmaph35__with41lh52_Hh61mh72B1h82B2h92B3h:2B4h;1Hh<1ah=3bs1h>3bs2h?1nh@4segshA2H1hB2H2hC2W1hD2W2hE2W3hF2W4p;1p;4p;2p;3p;9p;6p;5p;7p10000p4p70g000`R0p4p710R1p8g001>R2p4p710R3g001\R4p4p710R5p8P3P1p8p10028p4p70R6p1002fp4p7210p8P6P5p8P6P3p8P6p1003Bp4p73110R6p8p1003^p4p7210R3P5p8P3P1p8P6P1p8p1004Jp4p7210P1p8g004fj13Tg005Kj1QTg005ij1PTg006Lj1gTg006nj4RTg007cj1=Tg008Hj2OTg008bj1ITg009@j1HTg009`j1KTg00:@j1eTg00:^j1dTg00;<j1^Tg00;gj2ZTg00<Ij2YTg00=5j3XTg00=Oj3WTg00=nj4VTg00>`j2<Tg00?<j24Tg00?Yl9DTg00@Rj4CTg00ATj1BTg00BJj2UTg00C0j1TTg00Chj3MTg00DHj1LTg00EBj1NTg00F?R1j27Tg00FZj1STg00GMj3ATP2j2fTP4j6GTg00Gjj4>Tg00HEj49Tg00I=j2JTg00I]j1FTg00J=j5cTg00K9j1;Tg00KXj1]TP0j6ETg00LRj2`Tg00M5j4\Tg00M`j7aTg00NDj3bTg00Ngj4[Tf0R0#3#3p=2%30#Ip=_%=0#3p=6%30#3#3#Ip=8g00O`R4/`0p=@f2R2g00P>g00P]R6P6g00Q=R6P4f1R3g00Q]P0C\g00RDFap=:Ab430p=?g00RdR5P2P3P0C[p=1%=0#=p=5P5P2P3P0C9p=0g00S\R7#3R8#2R9#3#2R:#QR;#P%Q9#PR<#g[R=P5P0g00TA%_:R>CRP5P3g00U>P>CRP2%69#=#6#2R9#2#2#8R?g00V;R@,O4RAP5P2P?P>P?%I:R:P3g00VYRB#HRC%KBRB%e4RD%d4RE%^4RF%@?RG;:G1ZF6R6P0P2g00WERHg00WeRI'O1Y02=XHIdAW4@3CVRIb1b2b31<??P0b0PCPBPDPE%@:RH,?G%@>RJ,?GRK5:FP6PIb1b2b314?:14?>RL'<P0b0M9DCC%B?g00XERM1U;@R@#TR;%HM3MRN512f3RO%69#2#8R9PAP5POP?P>P9P:P2PCPBPDPE%@9RP9:FGP6PIb1b2b31<?9P0b0PCPBPDPE1?PH=:FKP6PIb1b2b3149:/<LP0b0M9DCC%B9=1ONf4R9%58#2#5#6R8#2#2#8RLPAP5P9PLP>PLP:P2PCPBPDPE%@LRK=:FKP6PIb1b2b31<LLP0b0PCPBPDPE1?KH1?KJRJ5:FP6PIb1b2b314L:14L>RP'<P0b0M9DCC%BL=19Nf5R?%68#2#8R8PAP5P?PLP>P8P:POPCPBPDPE%@8R>9:FKP6PIb1b2b31<L8P0b0PCPBPDPE1?>H=:FJP6PIb1b2b3148:/<PP0b0M9DCC%B8=1?NP1%LNR8f6RP%=7#5#5#5#5#5#5#5R7#6#2#6#=#6#2R:#3#8RI%NNR630f7RJAMM;NRN71I%37#6#5#2#5#6R7#3#8R;=1JN'7POf9RJ?0I6P1P8f:%=:#8R:;06f;RM?1INA1M;N'7PPf=?0:6P1P8f>?0;6f?RM?1INA1M;N'7PJfA?0;6P1P8fB%=7#8R7;06fCRM?1INA1M;N'7f<RMfE?076%K<R6%S@RF%H<5A<R>fGRH?0I0X46PMPF1f<FRMEGfFRE?0IFP6P>fHRD?0:0X46PJPFPMEGA0H:FP6P>fIRH?0;0X46PPPFPMEGA0D;FP6P>fJRD?070X46POPFPMEGA0H7FA1DINA1D;N%LNRH%NNR790DIR:g00Y=RJ17JJg00YYRBPJPJPBPBC>C>PHeRBP6PFfKRJAA<F0RC70IX46g00Z5#KRLP1P9POP2AA<30C9P?P9POP2C9P?P91J<2#F,4OP3C9'7R1[P9POP2P3C9P9PO1J<3#F,42P0C9'7P?P9POAA<23C9[RKPPP?P9AA<O2C9\1P9POP2P3P0DcP0n2001000000120000000X>6X=6X<4X6=W@R1PK^>6^=6^<4^6=^@LRLP0P5PJPIPFPFA0JIF1J<FR<#FR=,4I=0JFP9g00[4R9g00[S#;#;#;#;#;#;#;#;R4fLRK%F0R?,4I;0FX?9POP<%]@R@EEC>O6b;P>PMEEP:eC>PHA0D;7R7PBP6PFA0J;CX46P1PLP0P5PJP;PFPFA0J;F14;==0JFP2P9P414;?=0KFX?9P3P<P@EEC>O6b;P>PMEEP7eC>C>b:b9b8b7A1EINA1E;N'7eW:X58P3P0O2n2001000000121000000W9X58P3P0O2n2001000000121000000W8X58P3P0O2n2001000000121000000W7X58P3P0O2n2001000000121000000bFbEbDbCA12INA12;N'7eWBWAW6o"). Qed.

Lemma map_to_bytes_unsigned : forall (s : list byte), map (fun z => Z_to_bv 8 z) (map bv_unsigned s) = s.
Proof.
ltac2:(KReplay.run1 (kr_t_I_fwrite ()) [] "h02b1h12b2h21nh31xh41zh51Hh61bh71lh81sp;1p;2p;4p;3p;6g004fj14Tg005Kj1ATg005ij12Tg009`j17Tg00\2j20j1=Tg00BJj25Tg002fj43Tg00=5j31Tg00\\j2<Tg00]7j3;Tg00][j28Tg00^Aj29Tg00_4j3:Tg00_`j2@Tg000`j66Tg004Jj6?Tg003Bj6>Tg00S\#4#4#4#AR0#2R1#7R2P2P1P1f0R3,00,50X31R4P3C3R5f1R69123X72R7P2P1P1P3X31R2P3C3P71<13P5P1P1P4P2g00`OR2%23R4%26R5g00F?f2R7#2?163g00O`R8f3R9/07109631R:[10761073518%29?176[R;f4#2?197\:A;763P3n2001000000120000000W1W0W2P;^15^04^22P3P01006R2,50R4P6P8180210079183X4819069:0210041@02E6O4b5X61P3E?E6P8P11503X48R2P1P8%=0R0P3C3C3P1P8P1P0P2P3E>E6W8o"). Qed.

Lemma Forall_unsigned_byte : forall (s : list byte), Forall (fun c => 0 <= c < 256) (map bv_unsigned s).
Proof.
ltac2:(KReplay.run1 (kr_t_I_fwrite ()) [] "h01xh11Ah21Ph31lh41Bh51Hh64__x1h71fh81Rh92_Hh:7__arithh;4__ffh<8__varmaph=5__with>1bh?1ch@1sp;1p;4p;3p;5p;2p;7p;8g004fj11Tg005Kj1RTg005ij1BTg009`j14Tg002fj48Tg00`mj30Tg00aNR0j5FTg00\2j1Aj26Tg00>`j23Tg008bj1?Tg00amj22Tg00F?R1j25Tg00bIj37Tg00b`j3QTg00^Aj2PTg00cBj1OTg009@j1NTg00ckj2LTg00:^j1ETg00;<j1DTg00LRj2:Tg00dIj2CTg00M5j49Tg00dlj7@Tg00ePj1GTg00f2j8HTg00;gj2ITg008Hj2JTg00<Ij2KTg00=5j3>Tg00=Oj3=Tg00=nj4MTg00M`j7<Tf1R2g00P>R3g00P]R4P4g00Q=R5f0R6g00RDF<p=;g00S\R7#1#1#1R8#RR9#BR:#4P0p4p710R;P0p4p7210R0P2\2R<p-0R=\2R>f3R?#4R@P1f4RAP?f2RBP6C890?2f5RCP?PAP6O1O1X0C;02RD[PBP?P6O1O1X0A=0A6PCPAP?P2C890AB[REf6PCPAPBC890C?\DPAP?PBP2P6DFP6n2001000000120000000W3W2W7W4W1PE^3@^2>^7<^40^1;P6P:g00O`R;%A9g00V;R0/36%18#1#1#1#1#?R8,26'5R<X?;P2g00fVp4p710R>P=\6R=%42R@P1A0B26A7A6BPAP2O1[^0?R1[A7?62P?P2O1[^0BA0?B2[REA0A?B\1AQB26P6n2001000000120000000W3W2W1PE^3@^2=^1>P6P:1696R>,3012>8'5X0:PBA7:6?1P921692R>,30%O9,2>'5g00VYR>#N%4>1L;2%E;%D;R>P3P4P4P5P>P3P4P4P5P;1:;0g00Q]1C;7R7C9,;>P;P7g00g31:;8C9,;>F@R7%G4P7GH1I>5P6PBg00WER>g00WeR5'J1K6B=>>5dA=;02CMb;b<b=X6;13021228'5\<^6;P6169?P2O2b:b8W9X>:O4b5O6b5W@o"). Qed.

Lemma evw_to_bytes : forall fd (l : list Z), evw fd l = map (WriteEv (Z_to_bv 64 fd)) (to_bytes l).
Proof.
ltac2:(KReplay.run1 (kr_t_I_fwrite ()) [] "h01lh11bh22fdh31xp;1p;2p;4p;3p;6g009`j16Tg004fj10Tg005Kj13Tg00BJj22j17Tg00gZj25j1:Tg002fj41Tg00=5j34Tg008Hj2<Tg005ij1;Tg003Bj68Tg000`j69Tg00hPj2>Tg00iFj1=Tg00O`R0%60g00jAR1#6R2P0P1g00S\#0#0#0R3#0#0#0#3R4f2'2%33R3f0R5'2R6'5X30P5C1R7P0P1f3,24/56X10f1R6C1=425X021<27%;3R7P11246#:R4P0P7%73R3P5C1C1P0P7P1P3P4P5E8E91>65P7P1P4%=5C1542eW0W2o"). Qed.

Section XFwrite.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_ICPT : forall Σ m, ART RT Σ m -> icpt_consts m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, STDERR_FILE in *; lia.

Theorem fwrite_ok : fwrite_stderr_icontract RT OUT_repA ERR_repA IO_FPA.
Proof using AF AF_ICPT.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sa s errp lo
    Ha0 Ha1 Ha2 Ha3 Herrp Hlen Hsa HB CHK HFD ERR0 (g & SG1 & SG2) ART0 MI0 CALL.
  subst a0 a1 a2 a3 errp.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  destruct (AF_ICPT Σ m ART0) as (AI & RR & M2S & ACCP & RF & ACC1 & ACC2).
  destruct (lit_words m ACC1 ACC2) as (W1 & W2).
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  set (len := Z.of_nat (length s)) in *.
  set (s' := map bv_unsigned s).
  assert (LS' : zlength s' = len) by (unfold zlength, s'; rewrite length_map; reflexivity).
  assert (SAR : 0x166c0 <= sa /\ sa + len <= 0x22c80) by (destruct Hsa as [->| ->]; lia).
  (* [comment removed for export] *)
  set (Qfin := fun (x : unit * unit) (ms' : machine_state) => exists (m3 : mem),
         (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
            ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m3 (seg_rom asegs))
         /\ munch [(lo, usp); (0x102228, 0x102310)] m m3 /\ wmono asegs m m3 /\ mem_inv asegs m3 /\ stk asegs m3 lo usp
         /\ stderr_wfile0 m3).
  assert (IMPL : impl asegs (at_node asegs) ((stderr_fwrite s' : @M unit unit) tt) (epost Qfin)
                   (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 len) (Z_to_bv 64 1)
                      (Z_to_bv 64 STDERR_FILE) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fwrite m)).
  { eapply impl_evt;
      [exact (fwrite_walkA usp sa len STDERR_FILE ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo ST LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) ltac:(ul) RF AI MI0)|].
    intros ms1 (m1 & junk & -> & MU1 & WM1 & MI1 & FRb & FRt & ST1).
    assert (AG1 : agree_on (fun x => x < usp - 2144) m m1).
    { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [lia| exact I]. }
    assert (ERR1 : stderr_wfile0 m1).
    { apply (stderr_wfile0_agree m m1); [| exact WM1| exact ERR0]. apply (agree_sub _ _ _ _ AG1). intros x Hx. ul. }
    assert (HB1 : bytes_at asegs m1 (bv_unsigned (Z_to_bv 64 sa)) (map (fun z => Z_to_bv 8 z) s')).
    { rewrite unsigned_lit by lia. unfold s'. rewrite map_to_bytes_unsigned.
      apply (bytes_at_agree asegs m m1 _ _ HB). apply (agree_sub _ _ _ _ AG1). intros x Hx. fold len in Hx. ul. }
    assert (SSP1 : ssp_cells m1 g).
    { split.
      - apply (ro_cells_agree asegs m m1 _ _ SG1). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul.
      - apply (ro_cells_agree asegs m m1 _ _ SG2). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul. }
    assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; ul).
    pose proof (@fwrite_diag_proof unit towrite_proof (Z_to_bv 64 0x589a4) (Z_to_bv 64 (usp + -2128)) gp tp t0 t1 t2
                  (Z_to_bv 64 usp) (Z_to_bv 64 len) (Z_to_bv 64 sa) (Z_to_bv 64 len) (Z_to_bv 64 1) (Z_to_bv 64 STDERR_FILE)
                  (Z_to_bv 64 0xf0450) a5 a6 a7 (Z_to_bv 64 sa) (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 tt lo g s' ERR1 HB1 (Forall_unsigned_byte s) ltac:(rewrite LS'; lia)
                  ltac:(rewrite LS'; reflexivity) eq_refl eq_refl ltac:(rewrite EU1; exact ST1) ltac:(rewrite EU1; unfold FWRITE_DEPTH; ul)
                  ltac:(unfold GLOBALS_TOP; ul) ltac:(rewrite unsigned_lit by lia; rewrite LS'; left; ul)
                  ltac:(rewrite unsigned_lit by lia; rewrite LS'; left; ul) SSP1 MI1) as IM.
    unfold implM in IM.
    eapply impl_post_evt''; [exact IM|].
    intros [|[xr st']] ms2 H2; [apply evt_done; exact I|].
    cbn [epost fst snd] in H2 |- *.
    destruct H2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2
                    & ST2 & ERR2 & SSP2 & _).
    rewrite EU1 in MU2, ST2.
    rewrite (ret_pc_even 0x589a4) by lia.
    assert (AG2 : agree_on (fun x => usp - 2128 <= x \/ ((0xfdb10 <= x < 0xfdb30) \/ (0x10cc78 <= x < 0x10cc80) \/ (0x10d960 <= x < 0x10d978)) \/ (SHB <= x < 0x10007fff8000)) m1 m2).
    { apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn. unfold SHB in Hx. split; [lia|]. split; [ul| exact I]. }
    pose proof (rw_cells_agree asegs m1 m2 _ _ FRb ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; left; lia) WM2) as FRb2.
    pose proof (rw_cells_agree asegs m1 m2 _ _ FRt ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; left; lia) WM2) as FRt2.
    assert (AG12 : agree_on (fun x => ((0xfdb10 <= x < 0xfdb30) \/ (0x10cc78 <= x < 0x10cc80) \/ (0x10d960 <= x < 0x10d978)) \/ (SHB <= x < 0x10007fff8000)) m m2).
    { apply (agree_trans _ m m1 m2); [apply (agree_sub _ _ _ _ AG1); intros x Hx; unfold SHB in Hx; ul|].
      apply (agree_sub _ _ _ _ AG2). intros x Hx. right. exact Hx. }
    assert (M2S2 : m2s_cells m2).
    { destruct M2S as (G1 & G2 & G3). split; [| split].
      - apply (rw_cells_agree asegs m m2 _ _ G1); [| exact (wmono_trans asegs m m1 m2 WM1 WM2)].
        apply (agree_sub _ _ _ _ AG12). intros x Hx. cbn in Hx. lia.
      - apply (rw_cells_agree asegs m m2 _ _ G2); [| exact (wmono_trans asegs m m1 m2 WM1 WM2)].
        apply (agree_sub _ _ _ _ AG12). intros x Hx. cbn in Hx. lia.
      - apply (rw_cells_agree asegs m m2 _ _ G3); [| exact (wmono_trans asegs m m1 m2 WM1 WM2)].
        apply (agree_sub _ _ _ _ AG12). intros x Hx. cbn in Hx. lia. }
    assert (W1' : ro_cells asegs m2 0x7fffc580 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
    { apply (ro_cells_agree asegs m m2 _ _ W1). apply (agree_sub _ _ _ _ AG12). intros x Hx. cbn in Hx. unfold SHB. lia. }
    assert (W2' : ro_cells asegs m2 0x7ffface0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
    { apply (ro_cells_agree asegs m m2 _ _ W2). apply (agree_sub _ _ _ _ AG12). intros x Hx. cbn in Hx. unfold SHB. lia. }
    eapply evt_mono.
    { apply (fwrite_walkB usp sa len STDERR_FILE ra gp tp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3' t4' t5' t6' F fc m2 lo junk ST2 LO0 ltac:(ul) ltac:(ul) Hsa ltac:(lia) ltac:(ul) M2S2 W2' W1' FRb2 FRt2 MI2). }
    intros ms3 (RS3 & ST3). exists m2. split; [exact RS3|].
    split.
    { apply (munch_merge [(usp - 2144, usp)] [(lo, usp + -2128); (0x102228, 0x102228 + 232)] _ m m1 m2 MU1 MU2).
      intros x Hx. cbn in Hx |- *. unfold RT_STACK in *. intuition lia. }
    split; [exact (wmono_trans asegs m m1 m2 WM1 WM2)|]. split; [exact MI2|]. split; [exact ST3| exact ERR2]. }
  (* [comment removed for export] *)
  assert (TOK : tok [2] ((stderr_fwrite s' : @M unit unit) tt)).
  { unfold stderr_fwrite. rewrite LS'. replace (0 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold stdio_writev. apply tok_wv_loop; [left; reflexivity| cbn; lia| |];
      unfold WV_FUEL, iov_start, iov_total; cbn [concat]; rewrite app_nil_r; rewrite LS'; lia. }
  assert (RZ : realizes asegs c (TT ((stderr_fwrite s' : @M unit unit) tt) (fun _ => t_emit [] T))).
  { apply (impl_realizes_f asegs SEGTOP_A asegs_wx asegs_below asegs_frm [2] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo) Qfin
             (fun _ => t_emit [] T)
             (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 len) (Z_to_bv 64 1)
                (Z_to_bv 64 STDERR_FILE) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fwrite m) c
             (ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| | exact TOK| exact Hc| exact IMPL|].
    - intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
    - intros mo (_ & _ & _ & HRD). exact HRD.
    - intros x ms' c' HQ Hc'.
      assert (R : realizes asegs c' T).
      { apply Hk. eapply ASTA_conseq; [exact Hc'|]. intros ms <-.
        destruct HQ as (m3 & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->) & MU3 & WM3 & MI3
                        & ST3 & ERR3).
        exists (Z_to_bv 64 1), m3. split.
        { rewrite ESP. do 16 eexists. reflexivity. }
        split; [split; [| split; [exact MI3| split; [exact WM3| exact ST3]]]|].
        - apply (af_frame RT AF Σ m m3 lo ART0); [ul| | exact WM3].
          intros a Ha. apply MU3. cbn. split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
          intros Hin. apply Ha. right; left. apply client_static_intro. lia.
        - split; [| split; [exact ERR3|]].
          + intros a Ha Hout. apply MU3. cbn in Hout |- *. destruct Hout as (O1 & O2 & O3 & _). split; [| split; [exact O1| exact I]].
            destruct (aclient_split RT AF Σ m usp _ ART0 Ha); ul.
          + intros so0 OUT. apply (stdout_file_agree so0 m m3); [| exact WM3| exact OUT].
            apply (agree_of_munch _ _ _ _ MU3). intros y Hy. cbn. split; [ul| split; [lia| exact I]]. }
      eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty asegs _ _ R). }
  eapply rz_conseq; [exact RZ|].
  unfold stderr_fwrite. rewrite LS'. replace (0 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold stdio_writev.
  eapply t_eq_trans.
  { apply (TT_wv_loop (WV_FUEL (iov_start [] s')) 2 (iov_start [] s') tt (fun _ => t_emit [] T)); [cbn; lia| | | apply t_emit_has_nil];
      unfold WV_FUEL, iov_start, iov_total; cbn [concat]; rewrite app_nil_r; rewrite LS'; lia. }
  cbn [iov_start concat]. rewrite app_nil_r. rewrite <- evw_to_bytes.
  eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.

End XFwrite.
