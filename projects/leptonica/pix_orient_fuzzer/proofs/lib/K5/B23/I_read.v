(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the reservation the system-call return clears; the m_channel_reader conjunct; the recorded proofs of nretA_MSsvc_w, read_file_ok, read_dir_ok replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_small R_m2s R_thread I_consts RT_iface RT_frmkit D_iface D_defs D_kit D_clx D_rlkit X_open I_readw I_readw2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_I_read () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions6bv_addK47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K53B235D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K52AG6Shadow5sh_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53B235D_kit9agree_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit>bytes_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K53B238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3SHBC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C46Stdlib6ZArith:ZArith_dec8Z_lt_decI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib2K53B236I_read7acc_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow7acc_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238I_consts=acc_word_zeroC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rC69OSSVerify5KrLib2K53Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238I_consts6RS_PADC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236Layout<g_read_stageC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C69OSSVerify5KrLib2K53B238RT_iface3rtsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C69OSSVerify5KrLib2K53B235D_clxCclient_static_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53B238RT_iface=af_live_rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib2K53B238RT_iface7fs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface?af_frames_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=shiftl_nonnegC56Stdlib6ZArith6BinInt1Z6shiftlC47Corelib4Init5Logic3iffC69OSSVerify5KrLib2K53B238RT_iface:af_sp0_winC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53B238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K53B238RT_iface;checked_dstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC69OSSVerify5KrLib2K53B238RT_iface7call_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC69OSSVerify5KrLib2K53B238RT_iface4PMfdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC69OSSVerify5KrLib2K53B238RT_iface6ret_stC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53B238RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface:rt_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC69OSSVerify5KrLib2K53Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235R_m2s9m2s_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC69OSSVerify5KrLib2K53B237D_rlkit<stage_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface=af_acc_staticC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236I_read;stage_wordsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2K53B237I_readw:read_walkAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState5MSsvcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs8asta_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs;ASTA_unpackC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame?wr_at_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8rt_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface4ARTMC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C69OSSVerify5KrLib2K53Lib5RzCPS5nretAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defsBASTA_PM_mat_stableC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53Lib5Nodes4aregC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC69OSSVerify5KrLib2K53B238RT_iface;af_with_fdsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface4frmWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3ASTC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=length_firstnC4ELinuxProcessSemantics?LinuxProcessSem2FsCfile_read_unguardedC69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC69OSSVerify5KrLib2K53Lib7SysStepCapply_mem_deliveredC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7SysStep:mkR_set_a0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236I_read=nretA_MSsvc_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3MemCbytes_at_write_sameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib2K53Lib3Mem>wr_at_store_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib2K53Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indC69OSSVerify5KrLib2K53B236X_open;munch_mergeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula02C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clx=stage_static'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8af_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236I_read=aclient_splitC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C69OSSVerify5KrLib2K53B235D_kit>agree_of_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs;ASTA_conseqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit>ro_cells_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC69OSSVerify5KrLib2K53B237I_readw>read_walkB_eofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS<cps_realizesC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtC69OSSVerify5KrLib2K53B238I_readw2=read_walkB_qcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236I_read<acc_agree_shC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238I_readw2>read_walkB_ripC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B239RT_frmkit?ast_read_file_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_ifaceCread_icontract_fileC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8entry_stC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9rng_classC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53B235D_kit>rw_cells_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6e_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8RT_STACKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236Layout=g_asan_initedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238I_consts;g_REAL_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238I_consts8LIT_BLK1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238I_consts8LIT_BLK2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238I_consts=g_REAL_fwriteC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53B238I_consts;e_musl_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238I_consts=e_musl_fwriteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs8asegs_wxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs;asegs_belowC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C69OSSVerify5KrLib2K53B236X_open8pc_93368C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02C69OSSVerify5KrLib2K53B235R_m2s;kHighMemEndC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib2K53B238RT_iface:errno_cellC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Nodes6efferrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib2K53B236X_open;nretA_MSsvcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237I_readw>read_walkB_errC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B239RT_frmkit>ast_read_dir_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_ifaceBread_icontract_dirC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C4ELinuxProcessSemantics?LinuxProcessSem5State6EISDIR".
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma nretA_MSsvc_w : forall R F pc x8 fc rv m ro r ws,
  nretA (MSsvc R F pc x8 fc rv m ro) (mkEffect r ws []) = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4)%bv fc None
    (apply_writes (apply_zeros (apply_unmaps m []) []) ws) ro.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma acc_agree_sh : forall m m' a n, acc asegs m a n -> 0 <= a -> a + n <= USTACK_TOP ->
  agree_on (fun x => SHB <= x < 0x10007fff8000) m m' -> acc asegs m' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_I_read ()) [] "p'0h01bh11xi001xh24__p1h34__p2h44__x1h54__x2h64__x3h74__x4h82H0h93Hx0h:7__arithh;4__ffh<4__p3h=8__varmaph>5__with?4__x5h@4__x6hA1mhB1nhC2AGhD1HhE2H1hF2H2hG2H3hH2H4hI2HahJ2HbhK2HihL2HnhM3HokhN2HxhO6__sat0hP1ahQ1ehR1ihS2m'hT1qhU1rhV1yp&0p;1p;4p;2p;3p;6p;7p;<p;Bp;8g003Qj11Tg004[j1`Tg0059j1^Tg005\k10>Tg00@[j4eTg00APR0j20Tg00Amj24Tg007>j1GTg00BIk30<Tg00CCj1=Tg00::j1dTg00D9j3<Tg00DYj27Tg00EPR1j22Tg00EkR2j2VTg00FEj2xTg00FeR3j1UTg0046j1:Tg00GER4j23Tg00Gaj2MTg00H>j1HTg00H]j1WTg00I;j4iTg00I^j6[Tg00JGj4ZTg00Jnj2gTg00K_j2BTg00LHj2YTg006>k10=Tg00M4j2RTg00MRk10;Tg00N0k10:Tg00NNk108Tg00O9j2CTg00O\j2DTg00P?j3NTg00Pbk106Tg00QDk205Tg00>9j2cTg00Qfk204Tg00RRj3ETg00Rlk300Tg00SKj4~Tg00T=j2|Tg00T^j1{Tg00U7j2aTg00UTj2ITg00V4j2zTg00V[j2yTg00WBj2wTg00Whj2vTg00XNj2uTg00Y7j3_Tg00Y`j1sTg00Z>j2tTg00Z_j3rTg00[Hj4PTg00\3j6pTg00\Wj3oTg00]:j4bTg00]Uj6}Tg00^Pj7nTg00_Pk401Tg00_jk402Tg00`bl<mTg00aGlBlTg00amm<03Tg00bRj3kTg00c;k407Tg00cYj7fTg00d=j8XTg00daj6jTg00eEk709Tf0R5#1#1p=Og00eiR6/45p=5%15#1#1#1p=S%:5#:#:#:p=>%15#1#1#1#1#1#1#1p=@f2R7f1R8/35'2p=;g00fGR9P7P8P5H02p=6%:5#:p=qg00g?R:/c5p=?g00g]R;P:P:P:P3P3f5R3f4R<f3R=P7P8P5M<mp=hP:P:P:P:P:P:P0P5P8P7P0P=P<P3f6R0f7R>f8R?f9R@MBlp=]P:P:P4P>P4P0P3P<P=P7P8P5N<03p=\Ak:85p=8P:P7P8P5H07p=FP7g00h<R4g00h[RAPAg00i;RBP:P8g00i[P5CPg00jBRCFfp=9P0P4PAPAPBP3P<P=P4PAPAPBP7P8P5GXGXp=LP8P4PAPAPBP5Ejp=JP7P4PAPAPBP8P5K09p=KP:P8g00jbP5CPp=QP8P4PAPAPBP5PCFfp=AP=P4PAPAPBP7P8P5GXp=Tg00>SRC#1RD#1RE#1RF#1#ORG#`#^%`F#^RH$0>[RIP9P=P8P5Ce%5710=7g00kI'4g00lHRJ/45%1G#O#SRG#>#>#>#>#1#O#S#@#GRK7;5X1:RL@0<03%55?;53P3P8P5O2f:RM10?7RN#=%dHRO9<H5RP36175N'2X0H,VHP2PHf;R210@=RN#=;6P175N'2X0H10M<RN#==62P175N'2X0H,VHP5f=RN1023RQ#=;6P175Q'2P1f>R1f<RQ/00RR#=A<H8O36178Rf?RR101?RS#=RT;6P175S'2X0H,VHP5f@RSA<H=O76T10R@,7<PHfBRTfARU/02RV#=RW;6P175V'2X0HP310SMRV#=RPA<H3ORX56U173VP9PTPUPPPXP8PL14W5A<H0O,xH#U,0W7;5RWX1:PTPUP2%:CRO#q#>#>#>#1#O#S#@#GRL/48138KRX10TQRQ%GFRF'M/0LRP/48RVg00m=RY#HRZ#UR[,0PR\,38R]'2%GCR^,0P9;V8R_PVP]PVP5X1:R]P^O1R`,0PRa,38%WVP]1385#WXV:X1:RVP8P8%?8P\PaP]P]P]P:P:g00m\1085Ci#?XA:XB:RaPPPP%?PP[P`P]P]%U5#?X1;PZP^%?^EhR;M:]G\E[P5CZP_fC/0NRN/gF%5N%5FR_fERP/0RR\/MFRb#5[[p-0Rcg00n@Rd%HZRe#HRf#HRg,B:Rh1B:fRf1B:YRY'8'8g00nlRi'Y1B:eRe1B:ZRZ'8,8h/Yi%ddRj5<d3<&0=dRk1R:=&0;:Rl7F71R:<Rm?F<l7F8&0::Rn&08:RoPo1C:6Rp1D:DRq1D:ERE5N:Rr59o&06ARsPo1C:FRt99opPs%:D,D:RD99opFLPsPo1C:LRu9N:DRv1D:CRw59o1Jo05KoPsPoA9opE1Jo>5KoPsPoA9opqPsA9ouwFLFL205oBRuP5P7g00oXRxg0108Ry'c20457=ExydB00:68C~Ryb;b=b>X4:X5:X6:X7:X2cW31087#5%53\_[10<LR_/48/23%5<Rx/2>14L<\x[[[^4:^5:^6:^7:^2c^3cP5fDRx,3R10bL/0^,3<PbPRPPP<P8P7P1PTO:b:bOb91|QFAE:F6RQ#{1MNF,aF1INF'09E:N[1zNF136FRN10x1R1/IFRR#5?;RF[1y1F13F61I\FR1,3F1416'2[1w\FfF/0SRS/MF=E:6\Q1vSFfGRS/0URU/IF=E:U\Q1MUFP:fH/0T/IFP:108LRT/4?RU10T[R6,3?R\'210T^9;U?R1PUP\PU10T`R\,3?%WUP]PVP?P?%??P6P\P]P]P]PaPTPT%?TP[P`P;M:]G\E[P>CZP11u:FR1%Hg,B:5_:%sC,t:=r:fA_:1Y,8Z,8e'8,8h'8/Yi=<djPk1R:09Fm71R:3?F=l7F8PnPo1Jo?1C:^9N:v,Qw,Ao5KoPsPoPo1Qpt,AoPs%1O,D:Rv99op1Jo@5KoCTPsPoPoPoP4PAPAPBP:Ptg010XRBPpCP,AoEpPsP:PrPBAo:tD=N:vCP,AoCTPsPo1JoM1D:ORO,QE,Ao5KoPsPoAN:qO%OG#@#@#@#@#GRG,C:59oPs1C:K,Qw,AoCTFLFLPuPyb;b=b>X4:X5:X6:X7:X?:X@:X2cX3cX<c10_^9;05%5>/2@\Ng011?\Q10<01aF>/0?5E:[A;2031030/4G133K[[[[[^4:^5:^6:^7:^?:^@:^2c^3c^<cP5%5P137F10=L/4MP7P=PPfJfKPMP8P>P?PxPSO>b:b9bUbTbHbGbFbEb8Cb14J8/2XeXNWX1:E}FnP5CbH01WMWJP8P5O2n2001000000121000000W8X0HP8P5O2n2001000000121100000bQWKXR:P9P0P3P<CeeWCWLWIWDXB:XP:XSIWAo"). Qed.

Lemma acc_app : forall m a n k, acc asegs m a n -> acc asegs m (a + n) k -> 0 <= n -> acc asegs m a (n + k).
Proof.
ltac2:(KReplay.run1 (kr_t_I_read ()) [] "p'0h04__x1h14__x2h24__p1h34__x3h47__arithh54__ffh68__varmaph75__with81Lh91bh:1Hh;2H1h<2H2h=2Hih>2Hnh?1ah@1ihA1khB1mhC1ni001nhD1si011shE1zi021lp;1p;4p;2p;3p;6p;7p;8g003Qj13Tg004[j1HTg0059j1BTg005\j1NTg00@[j4?Tg00APj20Tg00GEj21Tg00EPj22Tg011\j2RTg00T^j1<Tg012@R0j2LTg00CCj1ATg00::j1JTg00D9j3`Tg00_jj4ETg00DYj2GTg00Ekj2FTg006>j1XTg00M4j2DTg00MRj1WTg00c;j4CTg00N0j1VTg00NNj1UTg00O\j2=Tg00Pbj1TTg00O9j2QTg00[Hj47Tg00QDj2MTg00>9j2OTg00Qfj2PTg00RRj3;Tg00Rlj3KTg00SKj4STg00P?j39Tg0046j1aTg012`j3ITg013Cj2:Tg00\3j6_Tg001[j6^Tg00Amj2]Tg00cYj7ZTg00daj6[Tg00eEj7\Tg00d=j8YTg00eiR1f0R2']p=4g00g?R3f1R4g00jbP2C7p=>P4g00h<R5g00h[R6P6g00i;R7P2g00jBFZp=5P4P5P6P6P7P2E[p=@f2R8P5P6P6P7P4P2F\p=6f3R9P5P6P6P7P8P4P2GYp=8g00>SR:#3R;#3#3R<#3#3#3#H#B%H<#BR<#N[g00fGR=P9P8P4C?P=f4R>1098P4C?%49%42f5R?/0>,12'2f6R@,R4114@RA%<A'LP0f7R0,18RA%<AP=f;RAf:RB/0>RC#A%J<9`<2RDCE1G2C'2X9<,F<P2f8,19REP0P>p-0RFg00n@RG#JRH%XGRGP31D38RIP4%W3CC%V3RJ%U3RK1=3:RL1=3;R;'>,5KRM%T6RNPKP31Q31ROg00i[RPPLC7,5KRQ1@K>56KPNA6KQMC8C81MK7RQP2P8g00oXRRg0108RS'O1P28=;RSdAK314CSR1b5b6b7X03X13W21124RS%44/29%481189'2[[^03^13^2FP2f9RR,0BRT,1?PBP?P4P>O5b4O2W8P2O1%<EPHPGP3PIP41D39CCRIPJP3A93L;%a:,=3R:=I3;593g010XA93L:C7,5KPQP1b5b6b7X03X13X3310241:84'010285;3^03^13^33P2P?PBPAO3b41:>R,0T=;3CP310AB1:?BRC'0P=f>%A4PDCE1G24'2X9<,F<XE3P0PCPHPGPIPJPKPKP5P6P6P7PME_PNPK1@K?A93;:,>L,5K56KPNP3POPPAI3L;R;C7,5K1>;:,5K56KC8C8PQP1b5b6b7X03X13X33X2Fg011?\S1089,14,2>1:89R4#4114>'2[[^03^13^33^2FP2%4@PBPAP@P8P?O6b4O210A?P2E^b:W8P2O1n200110100021010211100bDW=X@3P=P@P?10>9C?eW>W<W;XA3XC3X?3WBo"). Qed.

(* [comment removed for export] *)
Lemma stage_words : forall m, acc asegs m RS_PAD 16 -> acc asegs m g_read_stage 112 ->
  ro_cells asegs m 0x800E4E20 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
ltac2:(KReplay.run1 (kr_t_I_read ()) [] "h07__arithh14__ffh28__varmaph35__with41lh51mh62B1h72B2h82_Hh91ah:3bs1h;3bs2h<4segsh=1Hh>2H0h?2H1h@2H2hA2W1hB2W2hC1np;1p;4p;2p;3p;7p;9p;6p;5g003Qj11Tg004[j1PTg0059j1LTg005\j1fTg007>j1:Tg00@[j4FTg00::j1HTg006>j1GTg00MRj1eTg00N0j1cTg00NNj1`Tg00O9j2;Tg00QDj2\Tg00>9j2RTg00Qfj2[Tg00RRj3ZTg00Rlj3YTg00SKj4XTg00Amj2<Tg013`j7WTg00APj27Tg00P?j3ATg014Zl9OTg015Sj4NTg00CCj1MTg008oj2VTg016Uj1UTg00D9j3KTg017Mj4>Tg018Fj1QTg019@j1JTg00EPR0j2ETg00]:j4DTg01:=j1dTg01;0j3=Tg01;Mj2bTg001[j6TTg00_jj48Tg00FEj2ITg00Fej1BTg01;kj5_Tg00H>j19Tg01<gj1^Tg000`j6STg0046j1CTg00[Hj4]Tg00cYj7aTf0R1#1#1p=2%C1#Cp=4%11#1#1#1p=3%11#Cp=6%C1#1p=5g00g?R2f1R3g00i[P1C]p=?P3g00h<g00h[R4P4g00i;R4P1g00jBFap=@g00fGR5f2R6P3P1C8p=0g00>SR7#1#2R8#1R9#2R:#PR;#L%P8#LR8#f[R<P5P1g01=a%:9R9CFP5P3g01>\%47#3#:R=CFP6%47#6#5#6#4#2#6#3#3#:R>P9P=P3P1g00n@R?#HR@%G?R?%e2RA%c2RB%`2RCg00eiRD,;21;29RE'?'@1\C4R4P1P6g00oXRFg0108RG'R1[16=ZFGdAY2D3CXRGb1b2b31<D9P1b0FWP5P6P>179=R9CFf3RFP>1R2DRHP5PFP>P9P>%::R:P1P@P?PAPB1;2>RI/?I,@CP4PGb1b2b31<>>P1b0P@P?PAPB1;2:RJ9A2I1;2=9A2E9A2IRE'?,@CP4PGb1b2b317>:17>9R='<P1b0M9OCNP5PF%M>g01?[RK1V;DRD#UR;%HK3KRLC>f4RM%47#6#5#6#4#2#6#6#2#3#:RNPHP5PMP>P9PNP:P3P@P?PAPB1;2NR9,?I,@CP4PGb1b2b31<>NP1b0P@P?PAPBAA29J/?E,@CP4PGb1b2b317N:/<=P1b0M9OCNP5PM%MNPLC>P0%QLRNf5R=%17#2#3#3#4#5#6#2#4#5#2#5#3#:R:%JLRG30P5f6R4P:AKK;LRLC>P3f8?0:GP0PNf9%17#2#3#3#4#5#6#2#4#5#2#5#5#2#:R7;0GP5f:P:PLC>PMf<?07G%QLRGf=R;%JL70:RKg01@SRC1ECCg00@?REPCPCPEPECDCDPGe%G8RG%dDREf>RCA=8E170:X4GPG%H89=8ER9A0C:1X4GPMPE1b8ERJETA0;:EPGP9f??071X4GP3PEPJETA0C7Eg01@o#GRCP0PMPFP6A=831C8P=PMPFP6C8P=PM1I86#B,7FP3C8'ER0[PMPFP6P3C8PMPF1I83#B,76P1C8'EP=PMPFA=863C8[R7P4P=PMA=8F6C8\0PMPFP6P3P1D_P1n2001000000120000000X;GX:GX92X5<W<P7^;G^:G^92^5<^<CP1P5f@RCP:PEPEA0C:E1I8ER8#B,7:=0CEP6g00g]RCg00m=#9#9#9#9#9#9#9#9fA%B1,7:;0EXCCP3P8%^DESCDO6b>b7b6P9PJESPKeCDW7X8NP3P1O2n2001000000121000000W6X8NP3P1O2n2001000000121000000bBbAb=P5P6P:PLC>eW@W?W5o"). Qed.

Section XRead.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_ICPT : forall Σ m, ART RT Σ m -> icpt_consts m.
Hypothesis RIP : rip_stmt.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.

(* [comment removed for export] *)
Lemma aclient_split : forall Σ m usp a, ART RT Σ m -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
  usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
ltac2:(KReplay.run1 (kr_t_I_read ()) ["XRead"] "p'0h01Hh14__p1h24__x1h34__x2h41nh51kh61ph72H0h84__p2h94__x3h:4__x4h;4__x5h<7__arithh=4__ffh>8__varmaph?5__with@1fhA3HinhB2H1hC2H2hD2HfhE2_HhF3_H0hG4__p3hH4__x6hI4ART0hJ1EhK3H10hL3H11hM2H3hN2H4hO2H5hP2H6hQ2H7hR2H8hS2H9hT2HphU1ahV1mhW1qhX2q0hY1rhZ2r0h[3usph\2Σi001xp%0p&0p;1p;3p;2p;4p;5p;8p;6p;7g01Ank10STg003Qj11Tg004[j1wTg0059j1~Tg005\k10PTg01Bfk30OTg01C^j2JTg01DZj26Tg01EXk40>Tg01FTj1gTg01GVj2WTg01HRj2LTg01IPj2KTg01JUR0j29Tg00Amj20Tg00::k10NTg006>k10MTg00M4j2dTg00MRk10FTg00N0k10DTg00NNk10BTg00O\j2uTg00Pbk109Tg00QDk206Tg00>9k205Tg00Qfk204Tg00RRj3QTg00Rlk301Tg00SKk400Tg00GEj24Tg01Jok30RTg01KIk20QTg007>j1ATg01LNj5|Tg00APj22Tg01MOj2BTg00H>j1aTg00K_j2XTg00LHj2{Tg00D9j3zTg0046j1ITg00O9j2TTg00P?j3_Tg012`j3kTg01NJj3cTg006^j2yTg00EkR1j2VTg01Ndk80ETg013Cj2@Tg01Ofj3PTg01P=j1mTg01Q9k80@Tg00EPR2j23Tg00Fej1tTg01R=k20=Tg01Rdj2sTg01SDk20<Tg00CCj1>Tg01S]k50;Tg00T=j2rTg00T^k10:Tg00Gaj2YTg00U7j2iTg00UTj2=Tg00V4j2qTg00V[j2pTg00WBj2nTg00Whj2vTg00Y`k108Tg00Z>k207Tg00Z_k30CTg00XNj2oTg00Y7j3jTg00[Hj4fTg00\3k60GTg00\Wk30HTg00c;k40ITg00cYk70JTg00dak60KTg00eEk70LTg00d=k803Tg00bRk302Tg01T\j4}Tf0R3#1#1p=^f3R4f2R5'0f1R6/43'3p=F1B63g01U<R7'@,45p=;1463,35p=`g00g?R8P5P6P3H0Ip=E1u83p=RP8P6g00i[P3Cfp=SP6g00h<R9g00h[R:P:g00i;R;P3g00jBK0Jp=8P6P9P:P:P;P3J0Kp=ZP5P9P:P:P;P6P3K0Lp=?P4P9P:P:P;P5P6P3L03p=:1056/33p=C1056/93p=7%13#1#1#1#1#1#1#1p=GB02863p=N%I3#Ip=H%13#1#1#1p=lP8P6g00jbP3Cfp=O1@63,45p=M1@37,46p=bP8P8P6P3C}p=[1J639P45p=<f4R<10451463'3'3p=D1463,35,34p=x1B63/@7p=\g01V:R=/03p=U1056/33,34p=e1363,35p>0AP8g00g]R>P6P3C}p=]%m3,26p=51@37p>0?g00eiR?9Q83p=hp,2RTR@$0Sg00>SRA#1RB#1RC#1RD#1#^RE#w#~%wD#~$0P[B0O@451J@<16@<P5P6H0>P0P4P5P5g00kIRFCF%g5f5RG,J@/W516@GRH/L51KH5'9'9'910<4RHf6RI9;4@'9P3A`H4F10G<f7RH9;<@p-0RJg00n@RK$0NRL&0MKRM1d85&0F8RN7E6RO&0D8RP&0B8RQ1u8ARR%RBRS'S,8QRT1ZQ<RU5?Q&09:RVPTC:206Q;RTP3P5g00oXRWg0108RX+0520435=QWXdB018?6H00RXb=b>b?X28X38W1AC3651065[^28^38^1JP314GFPGPIP6O4b<40RW0P3O1%g41J@I/W416@IRW/L41KW4'9'9'9P0%g<1J@H/W<16@HRW/L<1KW<'9'9f8RW9;G@97IGP3%gG10HIf9RY9;I@20QI3%^E#GRZ#AR[PIPIP=CFP@p,2AFR\f:R]PYPID|12=7S001B@]R=10=F3Cg00m=R^#aR_#aS01,X8S021X8_S031X8^S04'N'Ng00nlS05'{=zKLS06PMPOPPPQ%IA#H#^#H#1#I#1#l#G#ARO,T8R^%1Z#^#lRZ#AR_,T8R`5_8/SS,8Q=?QUPVPQ1ZQG1OR^,8Q5?QPVAk8S`S07,OR,8QS08C:C:PTPXb=b>b?X28X38X1JX8J12O_?C65A`<6OAM54_[[^28^38^1J^8JP310[Yf<RO,B@R`%GZ#G#G#A'0P`PYP6P5O6b<f;RZ9;W@R^ebBb73cW0P3O11J@W/WG16@WRU/LG1KUG'9'9P01J@Y/WI16@YRU/LI1KUI'91bH=97WHP31J@]/WH10YWP1P81y88R=1[63RUP@f=RaC<P6P]P]1263RbDDX48,V8X681bY`R`P3P=PUP@f?RcC<106ORdPOPbCxX48,V8P1P8P=1[53P@f@RbC<P5PaPa1253DDX48A;a@bP3P=1[<3P@fBReC<P<PcPc12<3DDP2P=1[G6P@fCRfC<PGPbPb12G6CFfARgfDRh7;@P3P=1[H4P@fERiC<PWPfPf12W<CFP@P\fGRjfFRkPYPGPfP6L0E14?YRl12YGRm1\@j%UYRn97m[CeQ06PM1d8<S09?E5N1d8GS0:?E4N7E6S0;PPPQ1ZQHRm%RCRC%IB#RS0<5_8RB%IARo#R9k8SRp'S,8QS0=1ZQWS0>5?Q5?QPVPQ1ZQYS0?1ORB,8Q5?QPV1ORp,8QS0@C:C:PTPXb=b>b?X28X38X98X:8X;8X1JX8JXGJ124<1@65'0Rp>0AGI12<GRq9`W6AM54<S0A[[^28^38^98^:8^;8^1J^8J^GJP310Zk12ZH%UZ77[14?ZPHPZP7fIRr,B@RsPkP6P5O:b<b0WTWAP6P3O2n2001000000121000000W0X48P6P3O2n2001000000121100000W0X68P6P3O2n20010000001211000007c^W0P3O116@]R^/LH1K^H'9P016@ZR0/LW1K0WA7]Y`P316@OR`/LY10Z]S0BA;]@aS0CP1P81y8>R01]63R^16@c3PS0DPdPO%m3Rd,26Rt%ADRu'@RvCxX5>,V>X@8f>Rw9;Z@S0EP316@g9P0^S0FP6PwPwPvDDX5>,V>P1P>1]5316@e5P0S0GP5Pc125dRv=McuCeX5>A;c@eS0HP31]<316@h5P0S0IP<Pg12<dRd=MguCeP21]G616@i5P0S0J15G6R^=Meu9CGeA;f@kS0KP31]H416@j5P0S0L15W<R0=Miu9CWiP@P\PrfHRfPYPGPiP6L0@S0MPl15YGRl&0?sA7l[nP=PUP@fKRlC<15OW1256Rn/0O775[^48^68'3CeS0NP214?]S0O15]IRsfJRx,\@%U]97s[P=PUP@fLRsC<15aYRy10na775[^48^68'33CS0PA;f@lS0QP314?ORzfMR{,\@%Ua97y[P=PUP@fOR|C<15bOR}10nb775[^48^68'35CyRyP215w]R]fNR~,\@'0S0R%Uw97][P=PUP@fPR]C<15gaRa10ng775[^48^68'3S0SA;s@|S0TP31\@],0}R}%Ug97a[P=PUP@fSRUC<15hb10nh775[^48^68'3Rn%AERE%twR=+0=1sE=,0?10?E+0<Q06PMQ0;PPPQQ0=PVPQ1T8uR=9k8B,OR,8Q9?QmPVQ0@C:C:PTPXb=b>b?X28X38X98X:8X;8X1J1@qu9`I6Q0A[\p^28^38^98^:8^;8^1JP3fQRp,0h%tb,sEPhP7fT,B@R7PpP4PZO8b<bJfRRE,B@Rb,b|eWFWCP6P3O2n2001000000121000000W0WEP6P3O2n2001000000121000000b0WDWAP6P3O2n2001000000121000000W0X5>P6P3O2n2001000000121100000W0X@8P6P3O2n20010000001211000003cW0P3O11K`YQ0BQ0CP1P8Q0D%>6R`POPO%>tRtDDX5>,V>X@8Q0EP3Q0FP`PwPwPtDDX5>,V>P1P>Q0G%>5PcPc%>vDDX5>Q0HP3Q0I%><PgPg%>dDDP2Q0J%>GPePe%>^CFQ0KP3Q0L%>WPiPi%>0CFQ0MQ0NP2Q0OQ0PQ0QP3P2Q0RQ0SQ0TP3P@P\PEPpP~D|Q0010bF7CbP@P\PUPEP|I0;%IoRE#I#H#H#H#H#H#H#1#^#l#GR\#G#G#ARb1B@U'01rhu%huRh$0:RF1Yiu,iu1=iu'29Q8i[1qiu14?uRiP?1=kuR2P2PuCF[1pku14u?Rk1=juR2,4u102?'3[1nju1Yfu#h\h1vfu1=ru=Q8r\h1YruP81=xuP815lj/ru15sfRf1Yfu,iu1=fu'25Q8\F1qfuP?15{rRr/=uRfPfPuCF\i1pru15~xR~/=uRr,4u10r?'3\k1n~u15|lRl/Yu#h\h1vlu15]sR]/=u=Q8]\h1Y]uP815p{/=uP8Q01#aR{#aR]#a,X8&08A-0781X8]60C8%AE,o81X8{5j8Q021o8uR{Q035j8Q049j8{'N'N'N'N'NQ05'{=zKLPM1d8I?E4NQ0:7E5Q09?EIN7E6PPPQPQ1T8?RP/O=,8QPV%RDRD,SP,8QQ0>5?QC:PVPQPQPQP9P:P:P;P8P=g010XR;PPCf,8QJ0GPVP8Q0<%1o#R5_8RoP;B0H8=C=_8DCf,8QC:PVPQ1T8b/SS,8QPVPQQ07,So,8QPVPQQ0?%A\R\,T89_8C,OR,8Q5?QPVQ08C:C:C:C:C:PTPXb=b>b?X28X38X98X:8X;8XH8X1JX8JAC?IH\ig011?\h12GI1iu</2H5Q8[10b412IH1@<_'012I\9`Z<AMGI_[[[[[^28^38^98^:8^;8^H8^1J^8JP312Y\f`R\'0146uP6%m|PUP5fc,B@P\PIPHPcPePxO=b<bZbXbLbKbSbRbQbYbWbPbObNbMbB1bp7eb7b0XFnXC}P6P3O2n2001000000121000000X0yXEzP6P3O2n2001000000121000000b0WDWAP6P3O2n2001000000121000000W0X5>P6P3O2n2001000000121100000W0X@8P6P3O2n20010000001211000003cW0P3O1n200100000021100011000W7P3O1n200100000021100011000W7P3O1n200100000021100011000W7P3O1n200100000021000011000W7WIXU8X[8WVW\o"). Qed.

Theorem read_file_ok : read_icontract_file RT.
Proof using AF AF_ICPT RIP.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    fd buf count p off data lo Ha0 Ha1 Ha2 HBUF Hfd Hcnt Hb0 Hbt CHK HLK HFS ART0 MI0 CALL bs.
  subst a0 a1 a2 buf.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  destruct (AF_ICPT Σ m ART0) as (AI & RR & M2S & ACCP & _).
  destruct CHK as (CHKa & CHKcl & CHKwr). destruct (CHKa ltac:(lia)) as (ACCB & _).
  assert (ACC112 : acc asegs m g_read_stage 112).
  { apply (af_acc_static RT AF Σ m _ 112 ART0); [ul|]. intros i Hi. split; [apply stage_static; lia| unfold g_read_stage; lia]. }
  pose proof (stage_words m ACCP ACC112) as SW.
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  pose proof (read_walkA usp fd count ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) RR AI MI0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ F0 fs0 _ _ W1') Hc). intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & junk & junk1 & -> & MU1 & WM1 & MI1 & FRb & FRt & FRr & ST1) & Hc1').
  set (msA := MSsvc (mkR (Z_to_bv 64 0x21e330) (Z_to_bv 64 (usp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 g_read_stage)
                       (Z_to_bv 64 fd) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x218c54) (Z_to_bv 64 63) fc None m1 (seg_rom asegs)) in *.
  assert (WR1 : wr_at asegs m1 g_read_stage count) by exact (wr_at_transport asegs m m1 _ _ CHKwr WM1).
  unfold ASTA in Hc1'.
  apply (ast_read_file_f asegs SEGTOP_A asegs_wx asegs_below (rt_allow RT Σ) (eq msA) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           (fun ms => nretA msA (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 g_read_stage) bs) []) = ms)
           (fun mo => ARTM RT Σ mo /\ PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0 mo)
           fd g_read_stage count p off data); [lia| lia| ul| exact (ASTA_PM_mat_stable RT AF Σ _ fs0)| | | exact Hc1'|].
  - intros ms <-. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact WR1| reflexivity].
  - intros mo (HAR & HF & HF2 & HRD). rewrite HF, HF2. split; [exact HLK|]. split; [exact HFS|].
    split; [apply (af_with_fds RT AF); exact HAR| split; [reflexivity| split; [exact HF2| exact HRD]]].
  - intros c2 Hc2.
    set (r := Z.of_nat (length bs)) in *.
    assert (Hr : 0 <= r <= count).
    { subst r bs. rewrite file_read_unguarded, length_firstn. unfold word_to_nat. rewrite unsigned_lit by lia. lia. }
    set (m2 := write_to_mem m1 (wa g_read_stage) bs).
    assert (EQ : nretA msA (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 g_read_stage) bs) [])
                 = MS (mkR (Z_to_bv 64 0x21e330) (Z_to_bv 64 (usp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 g_read_stage)
                        (Z_to_bv 64 r) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                        (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11
                        t3 t4 t5 t6)
                   F (Z_to_bv 64 0x218c58) fc None m2 (seg_rom asegs)).
    { unfold msA. rewrite nretA_MSsvc_w, mkR_set_a0, pc_93368, apply_mem_delivered. reflexivity. }
    rewrite EQ in Hc2. clear EQ.
    (* [comment removed for export] *)
    assert (BS2 : bytes_at asegs m2 g_read_stage bs) by (apply bytes_at_write_same; ul).
    assert (MU2 : munch [(g_read_stage, g_read_stage + r)] m1 m2).
    { apply munch_write; [apply munch_refl| ul| ul|]. unfold inside. cbn. lia. }
    assert (WM2 : wmono asegs m1 m2) by (apply wmono_write, wmono_refl).
    assert (MI2 : mem_inv asegs m2).
    { apply mem_inv_store; [exact MI1|]. rewrite <- (Z.add_0_r g_read_stage). apply (wr_at_store_ok asegs m1 _ count 0 _ WR1); lia. }
    (* [comment removed for export] *)
    assert (MU12 : munch [(usp - 2144, usp); (g_read_stage, g_read_stage + r)] m m2).
    { apply (munch_merge [(usp - 2144, usp)] [(g_read_stage, g_read_stage + r)] _ m m1 m2 MU1 MU2).
      intros x Hx. cbn in Hx |- *. intuition lia. }
    assert (WM12 : wmono asegs m m2) by exact (wmono_trans asegs m m1 m2 WM1 WM2).
    (* [comment removed for export] *)
    assert (FIN : forall c3 m3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ASTA RT Σ (PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0)
        (eq (MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m3 (seg_rom asegs))) c3 ->
      munch [(usp + -2208, usp)] m2 m3 -> wmono asegs m2 m3 -> mem_inv asegs m3 -> stk asegs m3 lo usp ->
      realizes asegs c3 T).
    { intros c3 m3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc3 MU3 WM3 MI3 ST3. apply Hk.
      assert (MUT : munch [(usp - 2208, usp); (g_read_stage, g_read_stage + r)] m m3).
      { apply (munch_merge _ [(usp + -2208, usp)] _ m m2 m3 MU12 MU3). intros x Hx. cbn in Hx |- *. intuition lia. }
      eapply ASTA_conseq; [exact Hc3|]. intros ms <-. exists m3. split.
      { rewrite ESP. do 16 eexists. reflexivity. }
      split; [split; [| split; [exact MI3| split; [exact (wmono_trans asegs m m2 m3 WM12 WM3)| exact ST3]]]|].
      - apply (af_frame RT AF Σ m m3 (usp - 2304) ART0); [ul| | exact (wmono_trans asegs m m2 m3 WM12 WM3)].
        intros a Ha. apply MUT. cbn. split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
        intros Hin. apply Ha. right; left. apply stage_static'. lia.
      - split.
        + intros a Ha Hout. apply MUT. cbn in Hout |- *. split; [| exact Hout].
          destruct (aclient_split Σ m usp _ ART0 Ha); ul.
        + apply (bytes_at_agree asegs m2 m3 _ _ BS2). apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn. ul. }
    (* [comment removed for export] *)
    assert (AG2 : agree_on (fun x => usp - 2144 <= x < usp) m1 m2) by (apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn; ul).
    assert (AGS : agree_on (fun x => 0x225d20 <= x < 0x2457b8 \/ SHB <= x < 0x10007fff8000) m m2).
    { apply (agree_of_munch _ _ _ _ MU12). intros x Hx. cbn. unfold SHB in Hx. split; [ul| split; [| exact I]]. ul. }
    pose proof (rw_cells_agree asegs m1 m2 _ _ FRr ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRr2.
    pose proof (rw_cells_agree asegs m1 m2 _ _ FRb ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRb2.
    pose proof (rw_cells_agree asegs m1 m2 _ _ FRt ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRt2.
    assert (ST2 : stk asegs m2 lo (usp + -2144)) by (apply stk_write; [exact ST1| ul| ul]).
    assert (M2S2 : m2s_cells m2).
    { destruct M2S as (G1 & G2 & G3). split; [| split].
      - apply (rw_cells_agree asegs m m2 _ _ G1); [| exact WM12]. apply (agree_sub _ _ _ _ AGS). intros x Hx. cbn in Hx. lia.
      - apply (rw_cells_agree asegs m m2 _ _ G2); [| exact WM12]. apply (agree_sub _ _ _ _ AGS). intros x Hx. cbn in Hx. lia.
      - apply (rw_cells_agree asegs m m2 _ _ G3); [| exact WM12]. apply (agree_sub _ _ _ _ AGS). intros x Hx. cbn in Hx. lia. }
    assert (SW2 : ro_cells asegs m2 0x800E4E20 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
    { apply (ro_cells_agree asegs m m2 _ _ SW). apply (agree_sub _ _ _ _ AGS). intros x Hx. cbn in Hx. unfold SHB. lia. }
    destruct (Z.eq_dec r 0) as [R0|R0]; [|destruct (Z_le_gt_dec r 64) as [R64|R64]].
    + (* [comment removed for export] *)
      rewrite R0 in Hc2.
      pose proof (read_walkB_eof usp fd count ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo junk junk1
                    ST2 LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) FRr2 FRb2 FRt2 MI2) as W2.
      lazymatch type of W2 with evt asegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes asegs _ _ _ c2 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc2). intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & ((t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->) & ST3) & Hc3').
      rewrite <- R0 in Hc3'.
      exact (FIN c3 m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc3' (munch_refl _ _) (wmono_refl asegs _) MI2 ST3).
    + (* [comment removed for export] *)
      pose proof (read_walkB_qc usp fd count r ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo junk junk1
                    ST2 LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) ltac:(lia) M2S2 SW2 FRr2 FRb2 FRt2 MI2) as W2.
      lazymatch type of W2 with evt asegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes asegs _ _ _ c2 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc2). intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & ((t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->) & ST3) & Hc3').
      exact (FIN c3 m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc3' (munch_refl _ _) (wmono_refl asegs _) MI2 ST3).
    + (* [comment removed for export] *)
      assert (ACC2 : acc asegs m2 g_read_stage r).
      { apply (acc_agree_sh m m2); [apply (acc_sub asegs m _ _ g_read_stage r ACCB); lia| ul| ul|].
        apply (agree_sub _ _ _ _ AGS). intros x Hx. right. exact Hx. }
      pose proof (read_walkB_rip RIP usp fd count r ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo junk junk1
                    ST2 LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) ltac:(lia) M2S2 ACC2 FRr2 FRb2 FRt2 MI2) as W2.
      lazymatch type of W2 with evt asegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes asegs _ _ _ c2 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc2). intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->) & MU3 & WM3 & MI3 & ST3) & Hc3').
      exact (FIN c3 m3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc3' MU3 WM3 MI3 ST3).
Qed.

Theorem read_dir_ok : read_icontract_dir RT.
Proof using AF AF_ICPT.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    fd buf count lo Ha0 Ha1 Ha2 HBUF Hfd Hcnt Hb0 Hbt CHK HLK HERRS HTP (errv & ERR0) ART0 MI0 CALL.
  subst a0 a1 a2 buf tp.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  destruct (AF_ICPT Σ m ART0) as (AI & RR & M2S & ACCP & _).
  destruct CHK as (CHKa & CHKcl & CHKwr).
  assert (EE : errno_cell (Z_to_bv 64 0x777e98) = 0x777df4) by (unfold errno_cell; rewrite unsigned_lit by lia; reflexivity).
  rewrite EE in ERR0, HERRS, Hk.
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  pose proof (read_walkA usp fd count ra gp (Z_to_bv 64 0x777e98) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo ST LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) RR AI MI0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ F0 fs0 _ _ W1') Hc). intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & junk & junk1 & -> & MU1 & WM1 & MI1 & FRb & FRt & FRr & ST1) & Hc1').
  set (msA := MSsvc (mkR (Z_to_bv 64 0x21e330) (Z_to_bv 64 (usp + -2144)) gp (Z_to_bv 64 0x777e98) t0 t1 t2 (Z_to_bv 64 usp)
                       (Z_to_bv 64 g_read_stage) (Z_to_bv 64 fd) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1)
                       s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x218c54) (Z_to_bv 64 63) fc None m1 (seg_rom asegs)) in *.
  unfold ASTA in Hc1'.
  apply (ast_read_dir_f asegs SEGTOP_A asegs_wx asegs_below (rt_allow RT Σ) (eq msA) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           (fun ms => nretA msA (efferr EISDIR) = ms) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           fd g_read_stage count); [lia| lia| ul| ul| exact (ASTA_PM_mat_stable RT AF Σ _ fs0)| | | exact Hc1'|].
  - intros ms <-. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - intros mo (HAR & HF & HF2 & HRD). rewrite HF. split; [exact HLK|]. split; [exact HAR| exact (conj HF (conj HF2 HRD))].
  - intros c2 Hc2.
    assert (EQ : nretA msA (efferr EISDIR)
                 = MS (mkR (Z_to_bv 64 0x21e330) (Z_to_bv 64 (usp + -2144)) gp (Z_to_bv 64 0x777e98) t0 t1 t2 (Z_to_bv 64 usp)
                        (Z_to_bv 64 g_read_stage) (Z_to_bv 64 (- 21)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0)
                        (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1)
                        s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x218c58) fc None m1 (seg_rom asegs)).
    { unfold msA, efferr, eff0, errno_ret. rewrite nretA_MSsvc, mkR_set_a0, pc_93368. reflexivity. }
    rewrite EQ in Hc2. clear EQ.
    assert (ERR1 : rw_cells asegs m1 0x777df4 [C4 errv]).
    { apply (rw_cells_agree asegs m m1 _ _ ERR0); [| exact WM1].
      apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    pose proof (read_walkB_err usp fd count 21 ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo junk junk1 errv
                  ST1 LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) ltac:(lia) ERR1 FRr FRb FRt MI1) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc2). intros c3 Hc3. apply Hk.
    destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & RS & MU3 & WM3 & MI3 & ERR3 & ST3) & Hc3').
    assert (MUT : munch [(usp - 2144, usp); (0x777df4, 0x777df8)] m m3).
    { apply (munch_merge [(usp - 2144, usp)] [(usp + -2144, usp); (0x777df4, 0x777df8)] _ m m1 m3 MU1 MU3).
      intros x Hx. cbn in Hx |- *. intuition lia. }
    assert (WMT : wmono asegs m m3) by exact (wmono_trans asegs m m1 m3 WM1 WM3).
    eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m3. split.
    { rewrite ESP. destruct RS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
      do 16 eexists. reflexivity. }
    split; [split; [| split; [exact MI3| split; [exact WMT| exact ST3]]]|].
    + apply (af_frame RT AF Σ m m3 (usp - 2304) ART0); [ul| | exact WMT].
      intros a Ha. apply MUT. cbn. split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
      intros Hin. apply Ha. right; left. replace (bv_unsigned a) with (0x777df4 + (bv_unsigned a - 0x777df4)) by lia.
      apply HERRS. lia.
    + intros a Ha Hout. apply MUT. cbn in Hout |- *. split; [| exact Hout].
      destruct (aclient_split Σ m usp _ ART0 Ha); ul.
Qed.

End XRead.
