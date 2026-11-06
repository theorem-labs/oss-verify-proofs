(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe Stdio Driver PState Prog StepB LB_Logic.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_PStdio () := "C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_exIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio@stdio_write_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio6upd_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe4assnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic6mspecLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic;mspecL_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec8LB_Logic4liveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib3Lib5Nodes>minv_preservedC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState9set_so_psC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic;mspecL_upd'C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio5rd_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic;mspecL_munrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9iov_totalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode:dec_writevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec5Stdio;iov_advanceC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib5Nodes4eff0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1Z02K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef3mapI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_sysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic9mspecL_ifC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_seqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indC59OSSVerify5KrLib4Spec5Stdio8to_bytesC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4unit01K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02c59OSSVerify5KrLib4Spec9LB_PStdioBstdio_write_loop_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdio_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9WRITE_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9so_lbf_nlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio8so_firstC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5Stdio9stdout_st01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio=stdio_write_LC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio8upd_so_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBstdout_stdio_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio7rd_so_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9so_activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes6efferrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9dec_ioctlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdioDstdout_stdio_write_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_writefnC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode4sret00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio:TIOCGWINSZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOTTYC59OSSVerify5KrLib4Spec5Stdio>stdout_towriteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec5Stdio=after_last_nlC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnc59OSSVerify5KrLib4Spec9LB_PStdio@stdout_writefn_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_fwritexC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec5Stdio=STDOUT_BUFSIZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio@stdout_towrite_LC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio@stdout_fwritex_LC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib4Spec5Stdio:out_piecesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio<out_pieces_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_vprintfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioAstdout_exit_flushC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=stderr_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio?INTERNAL_BUFSIZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio?stderr_pieces_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stderr_fprintfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=stderr_fwriteC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver7IOStyle00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver>read_loop_bodyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_diagC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic;mspecL_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic=mspecL_if_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic;mspecL_pureC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic@mspecL_pointwiseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic;mspecL_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_usageC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio@stderr_fprintf_LC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBpieces_cannot_openC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioApieces_read_errorC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio?stderr_fwrite_LC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver8diag_msg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio:pieces_oomC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>pieces_too_bigC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio@pieces_short_hdrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBpieces_cfg_overrunC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_pct_dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio@stdout_vprintf_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_emitC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes9Empty_set00C59OSSVerify5KrLib4Spec4Prog;new_handlerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6DecodeAnstep_dec_set_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode;dec_set_tidC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC59OSSVerify5KrLib3Lib5NodesAm_vmmaps_with_tidC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio<I_after_nodeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEC59OSSVerify5KrLib4Spec4Prog7startupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_exitC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode?nstep_exit_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:exit_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog2ioC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c59OSSVerify5KrLib4Spec9LB_PStdioCstdout_exit_flush_LC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List:length_appC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib4Spec6Driver<u8s_of_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00K47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I59OSSVerify5KrLib4Spec6Driver5rd_st00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00C59OSSVerify5KrLib4Spec6Driver6rd_capC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_diagC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Driver6rd_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:rd_contentC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum02C56Stdlib5Arith8PeanoNat3Nat3eqbc59OSSVerify5KrLib4Spec9LB_PStdio7rd_invLC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_gtc59OSSVerify5KrLib4Spec9LB_PStdio?pow2_le_1024_rdC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init5Logic3notC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib7Sorting;Permutation;Permutation03C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K59OSSVerify5KrLib4Spec6Driver5rd_st01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega7EnvRing5PExpr04K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode>nstep_dec_readC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertK59OSSVerify5KrLib3Lib6Decode8read_ans01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode8read_ans02C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib5NodesAm_vmmaps_with_fdsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio?own_after_nodeLC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC59OSSVerify5KrLib3Lib6DecodeIlength_file_read_le_countC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7eqb_neqC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib4Spec9LB_PStdio>zlength_u8s_rdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio>zlength_app_rdC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum01K47Corelib4Init9Datatypes4prod01C46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula05C4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC59OSSVerify5KrLib4Spec6Driver9MAX_INPUTC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode8read_ans00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFC4ELinuxProcessSemantics?LinuxProcessSem5State6EISDIRI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06K47Corelib4Init9Datatypes:comparison03K59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode>nstep_dec_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_openC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8alloc_fdK59OSSVerify5KrLib3Lib6Decode4sret01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode4sret02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_PStdio@read_loop_body_LC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode?nstep_dec_closeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9dec_closeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_removeC59OSSVerify5KrLib4Spec6Driver8read_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9READ_FUELC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib4Spec6Prelim4znthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver4le16C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitc59OSSVerify5KrLib4Spec9LB_PStdio:read_all_LC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC47Corelib7Classes?RelationClassesCPreOrder_TransitiveC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib5Lists4List<length_skipnC47Corelib7Classes?RelationClasses<transitivityC59OSSVerify5KrLib4Spec8LB_Logic=mspecL_pure_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:main_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver4le32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec6Driver7HDR_MINC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC59OSSVerify5KrLib4Spec6Driver9COUNT_MAXC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_preorder".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StdioL.
Variable B : Z.
Variable I : assn PState.
Hypothesis I_minv : forall s mo, I s mo -> minv mo /\ m_halted mo = None.
Hypothesis I_fds : forall s mo mo', I s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> I s mo'.
Hypothesis I_live : forall s mo, I s mo -> live mo <= B.
Hypothesis I_so : forall s mo v, I s mo -> I (set_so_ps v s) mo.

Lemma I_after_node : forall s mo n rsp mo' evs,
  I s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> I s mo' /\ live mo' <= B.
Proof.
  intros s mo n rsp mo' evs Ho Hst Hvm. destruct (I_minv _ _ Ho) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hst) as [Hh' Hmi'].
  assert (Ho' : I s mo') by (eapply I_fds; eauto). split; [exact Ho'| exact (I_live _ _ Ho')].
Qed.

Local Notation mspecL := (mspecL B).
Local Ltac ret_I := apply mspecL_ret; intros ? ? HH; exact HH.

Lemma upd_so_L : forall f, mspecL I (upd_so ps_so set_so_ps f) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h01sh12Hoh21fh32mop;1p;2p;6p;4g00K;R0j10Tg00L1R1j24Tg00Lkj62Tg005Yj41Tg007Cj63Tg00MiR2P2[g00ERR2p,1BR3p,1IR4g00NdR5P4UR6f1R7f0R8#0O1/48X02g00FKP4P7P8O2p,4I_sof2R9P7f3%09O1P8O4W1W3X02E2P2P3P5P4P2P0P1P8C1P6E3eW2o"). Qed.

Lemma rd_so_L : mspecL I (rd_so ps_so) (fun _ => I).
Proof. unfold rd_so. eapply mspecL_bind; [apply mspecL_get|]. intros s0. apply mspecL_ret. intros s mo [_ H]. exact H. Qed.

Lemma stdio_write_loop_L : forall fd fuel iov, mspecL I (stdio_write_loop fuel fd iov) (fun _ => I).
Proof.
  intros fd fuel. induction fuel as [|fuel IH]; intros iov; cbn [stdio_write_loop]; [apply mspecL_munr|].
  eapply mspecL_seq.
  - apply mspecL_sys; [intros; exact Logic.I|]. intros s mo Ho rsp mo' evs Hst.
    assert (Hvm : mo' = mo) by (destruct Hst as [-> _]; reflexivity). subst mo'.
    split; [exact (I_live _ _ Ho)| intros; exact Ho].
  - intros cnt. apply mspecL_if; intros _; [ret_I| apply IH].
Qed.

Lemma stdio_write_L : forall fd buf s, mspecL I (stdio_write fd buf s) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "p'0h02_Hh13bufi003bufh22fdh31si011li021zp;1p;2p;3p;4p;5p;:p;6g00;SR0j16Tg000mj21Tg00ijj22Tg00jGj27Tg00jdj2?Tg00^5j15Tg00c\j13Tg00\Aj1;Tg00kXj30Tg004Yj4:Tg00=^j34Tg00S[j58Tg00l8j39Tg00acl:>Tg00m>j4=Tg007Cj6<Tg00eTR1%61R2g00ERR3p,1BR4g00NdR5g00n9f1R6,11R7f0R8,11'2R9'7R:1?35P3%59#3f2R9P0P1%62R;P6%;2R<9028f3R=A029<502n10110000020020102101C:p,1IR>P>V5R?g00g0R@g00hj74:P3P4P5P>P?D8W0g00iJ94@:1119/27#5#3P0P1P;P9A026<f4A02=<502n1011000002002010210159=W0M:>P3P4P5P>P3P9P6P8C=P?E<eX32W1W2o"). Qed.

Lemma stdout_stdio_write_L : forall s, mspecL I (stdout_stdio_write ps_so set_so_ps s) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h02soh12_Hh21sp;1p;2p;4p;5p;3p;;p;6g00;Sj1?Tg00Rfj2>Tg00\aj12Tg00o2j11Tg00m>j4=Tg00\Aj1:Tg00ohj13Tg010aj14Tg011Yj45Tg005Yj46Tg012Tj57Tg013Ij38Tg014Jj19Tg00b_l;0Tg015Fj4<Tg007Cj6;Tg00eTR0#?g00ERR1p,1BR2g00MiR3g00NdR4g00K;R5,>1P1P4P4P1g00JV#2R6f0R7#1R8f1R9C=R:P1P5g00L1R;g00hj%:0%37%47C5X03R0C6V4R<D7X03p,1IR=P=P=V4R>g016HP1P2P4P4P:P<P=P=P>A8689%90X14M;0X03M;0P1P2P4P=P1P5P;P7C<P>E;eW2o"). Qed.

Lemma stdout_writefn_L : forall s, mspecL I (stdout_writefn ps_so set_so_ps s) (fun _ => I).
Proof.
  intros s. unfold stdout_writefn. eapply mspecL_seq; [apply rd_so_L|]. intros so.
  eapply mspecL_seq; [| intros _; apply stdout_stdio_write_L].
  apply mspecL_if; intros _; [|ret_I].
  eapply mspecL_seq; [apply upd_so_L|]. intros _.
  eapply mspecL_seq with (R := I).
  - apply mspecL_sys; [intros; exact Logic.I|]. intros st mo Ho rsp mo' evs (-> & -> & ->). split; [exact (I_live _ _ Ho)| intros; exact Ho].
  - intros [e|v]; [apply upd_so_L| apply mspecL_munr].
Qed.

Lemma stdout_towrite_L : mspecL I (stdout_towrite ps_so set_so_ps) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h02sop;1p;4p;3p;6g017Cj17Tg00\Aj16Tg00ohj10Tg010aj11Tg011Yj45Tg014Jj12Tg01?Jj33Tg007Cj64Tg00MiR0g00g0P0f0R0#7P0g00hjg00eT#6%00%10C5n0100000020000W0#2g00ERR0p,1Bg00NdR1p,1IR2g00K;g00L1530P2V1E4eo"). Qed.

Lemma stdout_fwritex_L : forall s, mspecL I (stdout_fwritex ps_so set_so_ps s) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h02_Hh12soh22HHh32moh41sh52s0p;1p;3p;2p;4p;5p;7p;;p;6p;:g00;Sj1STg01?Jj3RTg00Rfj2ITg003hj2FTg00o2j1QTg000mj2ATg01@Hj2JTg00jGj25Tg00ohj1@Tg01@ej13Tg00^5j14Tg00^Uj37Tg00P8j3PTg017Cj1OTg01Abj3<Tg010aj1LTg011Yj41Tg012Tj5=Tg01B@j1>Tg00Qij7HTg014Jj1BTg00b_l;;Tg01CDj4GTg007Cj6KTg01;gj4ETg01DBj3MTg005Yj4NTg00=^j3CTg00acl:DTg00ERR0g00K;R1g00L1R2f0R3CEp=6g00eTR4f1R5;M3p=0P0P1P2P3CNp=2P0g00NdR6P6P5P3D=p=?g00g0R7g00hj7C3p=:g00iJ9C73p=8P0f7P6f6R8f5R9f4R:f3R;f2R<P5P3M:Dp=9%S4P0p,1BR=P6P6AR012P0g00MiR>P61I01R?P71F06R@g01D_%Q3RA,A4'J1A4<'5RB%6<RCP7P@%@3RDP7P@g00hLRE%3<RF'5%4F=74<#6g00gPR<9P06RFn0100000020000%O3RG%3:RH#4RI=<4:,0APD%L3RJC1X1>#2V6'?PG10A;PDPJC1X1>#2n0100000020000RKn0100000020000X1>RLD=V6p,1IRMPMPMV6RNg01E\P0P=P>P6P?PLPMPMPNg016HP=PBPCPKPMPN%:B%>;W0%8BP=%@5RBP7P@%3;RK,5E%4K=74;#6PFn0100000020000PG%39#4R;=<49,0APDPJC1X1>#2V6'?PG10A:PDPJC1X1>#2PMPN%:BP0P=P6P6P7P@15EHRHA74I:#6RIPFn0100000020000PG%38#4=<48,0APDPJC1X1>R8#2V6PMPMPNP=PHPIPFPMPN%:HA74;9#>W0%8HP0P=P6P<PMPNg00FKPMP5P3O2P3W2W3X50FHW0G9%B8X06M;;W0%8BPG10A9PDPJC1X1>#BW0G9W0G9X1>M;;X06M;;P0P=P6PMP0P1P2P3CGPNEKeW4o"). Qed.

Lemma out_pieces_L : forall ps, mspecL I (out_pieces ps_so set_so_ps ps) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h02psh12HHh22IHh32_Hh42moh51ph61sp;1p;7p;4p;;p;3p;5p;6g00;Sj12Tg00Qij73Tg00\Aj1;Tg01CDj4:Tg01F`j19Tg00b_l;4Tg00kXj35Tg01Gdj56Tg01HFj47Tg007Cj68Tg00ERR0g00K;R1g00L1R2f0R3C7p=0P0f3g00NdR4f2R5f1R6P3E8p=1g00eT#2R7#2R8P7p,1BR9p,1IR:%03P:V4R;C1R<X08P0P9P4g00gPP:P;g00FKP:P6P3O2P3W1W4X60F3P9P:%;7#0P;C1eP0P9P4P4P0P1P2P5C:%05V4P:P:P;%95P6X34M;4P9P:A5756#0P;C1eX2<X08X57P3D6W0o"). Qed.

Lemma stdout_vprintf_L : forall ps, mspecL I (stdout_vprintf ps_so set_so_ps ps) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h02_Hh12psp;1p;3p;4p;;p;6g00;Sj10Tg01?Jj36Tg01HFj42Tg01I@j11Tg00b_l;5Tg01J@j44Tg007Cj63Tg00eT#0#0g00ERR0p,1BR1g00NdR2P2g00K;R3g00L1R4560P0P3P4f1R5C2V2p,1IR6P6P6V2R7g01E\%15X02M;5P0P1P2P6P0P3P4f0C4P7E3eW1o"). Qed.

Lemma stdout_exit_flush_L : mspecL I (stdout_exit_flush ps_so set_so_ps) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h02_Hh12soh22HHh32moh41sp;2p;1p;4p;3p;7p;:p;;p;6g00Rfj2>Tg003hj2=Tg00o2j12Tg000mj21Tg00jGj2<Tg00\Aj15Tg01;gj43Tg00P8j34Tg00=^j30Tg01B@j16Tg00Qij77Tg00acl:8Tg00b_l;9Tg01K>j3;Tg007Cj6:Tg00ERR0p,1BR1g00MiR2g00NdR3g00K;R4,>0g00g0R51=03g00hLg00eTR6f0R7#2'1'<R8P0P4g00L1R9%56R6C3R:g00gPR;9403R<n0100000020000X12p,1IR=P=P=V3R>g016HP0P1P3P8P:P<P=P>g00hj9058%66W0g00iJ9058P0P1P3P;P=P>g00FKP=f1P7O2P7W2W3X40F7W0M:8X12M;9P0P1P3P=A;049P>E:eo"). Qed.

Lemma stderr_pieces_L : forall ps buf, mspecL I (stderr_pieces (St:=PState) buf ps) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h02_Hh13bufh22psh32HHh42IHh52moh61ph71sp;1p;6p;7p;2p;4p;5p;3p;;p;:g00;Sj17Tg007Cj61Tg00Qij78Tg00\Aj13Tg000mj24Tg01@Hj2=Tg00jGj2<Tg00>kj1;Tg00\aj1:Tg00m>j45Tg012Tj59Tg01DBj32Tg00=^j36Tg013Ij3CTg00b_l;BTg00acl:ATg00kXj3@Tg01Gdj5>Tg01L?j3?Tg00ERR0f1R1f0R23?p=0g00eTR3#7R4#7R5P4P0p,1BR6P4p,1IR71021P7V4R8E1^14R9X25P0P6P4P2P7P8g00FKP7P1P2O2P2W3W5X70F8P0P6P4P7%34,02P8E1eX14P0P6P4g01M<1432'=f3R:,43'<R;P0g00NdR<P4P0g00JV#;#:R=P2P:C5%33R>/0:V<D9A232:f2R?'0P7P8g00g0R@g00hj76;P0P6P<P4P0P=P1f4RAC510>AV<P7P7P8AC=1AP:P>O1X0<M;BW0g00iJ96@;P?A231AO1W0M:AP0P6P4P7A@4:?,02P8E1eX14X49X25X64P2D>W2o"). Qed.

Lemma stderr_fprintf_L : forall ps, mspecL I (stderr_fprintf (St:=PState) ps) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h03bufh12psp;1p;3p;4p;2p;;p;6g00;Sj10Tg00\Aj1:Tg01L?j32Tg00>kj11Tg00\aj19Tg00m>j48Tg01N;j23Tg013Ij34Tg00b_l;5Tg01O>j26Tg007Cj67Tg00eTR0#0R1#0g00ERR2p,1BR3P1g00NdR4%:0R0f0R5522P2g00JV#1#9R6P5P0C8X01p,1IR7P7P7V4R81350A4650X01M;5P2P3P4P71625P8E7eW1o"). Qed.

Lemma stderr_fwrite_L : forall s, mspecL I (stderr_fwrite (St:=PState) s) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h02_Hh12HHh22moh31sh42s0p;1p;2p;4p;3p;7p;:p;6g00;Sj1=Tg000mj2<Tg00jGj22Tg00>kj11Tg00\aj1;Tg00\Aj15Tg00m>j43Tg00P8j34Tg00=^j30Tg013Ij36Tg00Qij77Tg00acl:8Tg01P<j29Tg007Cj6:Tg00eTR0#=g00ERR1p,1BR2g00NdR3g00hLf0R4,<0'2R5P1g00JV#1#;R6%50R0P4C3g00gPR79413p,1IR8P8V3R9g00g0R:g00hj705f1R;9660W0g00iJ90:5P1P2P3P7P8P9g00FKP8P;P4O2P4W1W2X41F7W0M:8P1P2P3P81914P9E:eW3o"). Qed.

(* [comment removed for export] *)
Lemma s_diag_L : forall d, mspecL I (s_diag d) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "p'0h04pathi004pathh15argv0i015argv0h21di021dp;1p;2p;6p10033p4p70R0p101Q9p4p710R1p8P0p101R3p4p710R2p8P0g01S2R0p4p710R3p8p1009:p4p70R4P1p8P4P2p8P4P3p8P1p1003hp4p710p8p101Sip4p710R1g007CR3p4p73110p8P1p100Qip4p73110p8P1p1008<R4p4p73110p8P1P4p4p741110p8P1p101Tep4p73110p8P1p101Ubp4p73110p8P1p100acp4p73110p8P1p101V`p4p73110p8P1p101W`p4p73110p8P1p101X^p4p73110p8P1p101YaR4p4p73110p8P1P4p4p741110p8P1p100b_p4p741110p8g00;Sj1<Tg01Z_j17Tg01[[j11Tg01\_j1;Tg01]Zj1:Tg01^\j18Tg01_Wj16Tg01`Xj15Tg00YMj22Tg01aSj13TP0j24TP3j69Tg00ERR3f4g00NdR0f3f2f1'4f0R1E9p=0g01bVR4P4p,1BR4p,1IR2P3P1P2V0R0D0P1g00eTR5#<R6%71#1P4P2P3%;1P0D0eW1P1O1%:1#1P4P2P3%81P0D0eX06P1O1%61#1P4P2P3%51P0D0eX06P1O1g01cQ,25#3P4P2P3g01dKP0D0eg01eF#1P4P2P3g01fDP0D0eg01g?,25#3P4P2P3g01h?P0D0eg01i:,25#3P4P2P3g01j<P0D0en01102000710101101001010000000000W2o"). Qed.

Lemma s_emit_L : forall v, mspecL I (s_emit ps_so set_so_ps v) (fun _ => I).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h01vp;1p;4p;6g01k7j13Tg01l3j12Tg01m7j40Tg007Cj61Tg00eTf0R0#3#2g00ERR1p,1Bg00NdR2p,1IR3P1g00K;g00L1P0C0P3V2E1eW0o"). Qed.

(* [comment removed for export] *)
Lemma new_handler_L : forall (Q : Empty_set -> assn PState), mspecL I new_handler Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["StdioL"] "h01Qp;1p;5p;6g006Oj12Tg00S[j51Tg007Cj60Tg01mnR0g00ERR1#2[P1p,1BR2P0p,1IR3f0R4D1P1P2P0P3g01nSP4E0eW0o"). Qed.

Lemma startup_L : mspecL I startup (fun _ => I).
Proof.
  unfold startup. eapply mspecL_seq; [|intros _; ret_I].
  apply mspecL_sys; [intros; exact Logic.I|]. intros s mo Ho rsp mo' evs Hst.
  destruct (I_minv _ _ Ho) as [Hmi Hh].
  pose proof (nstep_dec_set_tid mo rsp mo' evs Hmi Hst) as (_ & t & Hdec & _ & Hmo).
  assert (Hvm : m_vmmaps mo' = m_vmmaps mo). { destruct Hmo as [[_ ->]|[_ ->]]; [reflexivity| apply m_vmmaps_with_tid]. }
  destruct (I_after_node _ _ _ _ _ _ Ho Hst Hvm) as [Ho' LB]. split; [exact LB|]. intros; exact Ho'.
Qed.

Lemma exit_model_L : forall code, mspecL (fun s mo => exists X : Prop, I s mo) (exit_model io code) (fun _ _ _ => False).
Proof.
  intros code. unfold exit_model. eapply mspecL_seq with (R := I).
  - apply mspecL_exI. intros _. cbn [io io_exit io_S]. apply stdout_exit_flush_L.
  - intros _. apply mspecL_sys; [intros; exact Logic.I|]. intros s mo _ rsp mo' evs Hst. destruct (nstep_exit_none _ _ _ _ _ Hst).
Qed.
End StdioL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DriverL.
Context {ptr : Type}.
Variable B : Z.
Variable io : IOStyle PState.
Variable drv_malloc : Z -> Monad.M PState (option ptr).
Variable drv_free : ptr -> Monad.M PState unit.
Variable read_stage : Z.   (* [comment removed for export] *)
Variable alloc_init : Z -> Monad.M PState unit.
Variable run : Z -> list Z -> Monad.M PState Z.
Variable alloc_count : Monad.M PState Z.
(* [comment removed for export] *)
Variable own : list (ptr * Z) -> assn PState.
Variable own' : list (ptr * Z) -> assn PState.
Hypothesis Hoo' : forall X s mo, own X s mo -> own' X s mo.
(* [comment removed for export] *)
Variable mal_ok : list (ptr * Z) -> Z -> Prop.
Local Notation mspecL := (mspecL B).

Hypothesis Hdm : forall X n, 0 <= n ->
  mspecL (fun s mo => own X s mo /\ mal_ok X n) (drv_malloc n)
         (fun r s mo => match r with Some p => own ((p, n) :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p n, mspecL (own ((p, n) :: X)) (drv_free p) (fun _ => own X).
Hypothesis Hdf' : forall X p n, mspecL (own' ((p, n) :: X)) (drv_free p) (fun _ => own' X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hdiag : forall X d, mspecL (own X) (io_diag io d) (fun _ => own X).
Hypothesis Hexit : forall X, mspecL (own' X) (io_exit io) (fun _ => own' X).
Hypothesis Hinit : forall X bm, mspecL (own X) (alloc_init bm) (fun _ => own X).
Hypothesis Hcount : forall X, mspecL (own' X) alloc_count (fun _ => own' X).
(* [comment removed for export] *)
Hypothesis Hrun : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL (own [(b, cap)]) (run cfg payload) (fun _ => own' [(b, cap)]).
Hypothesis Hown_minv : forall X s mo, own X s mo -> minv mo /\ m_halted mo = None.
Hypothesis Hown_fds : forall X s mo mo', own X s mo ->
  m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> own X s mo'.
Hypothesis Hown_live : forall X s mo, own X s mo -> live mo <= B.
(* [comment removed for export] *)
Hypothesis OK_first : mal_ok [] 65536.
Hypothesis OK_grow : forall b k, (k <= 9)%nat -> mal_ok [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).

Lemma own_after_nodeL : forall X s mo n rsp mo' evs,
  own X s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> own X s mo' /\ live mo' <= B.
Proof.
  intros X s mo n rsp mo' evs Ho Hst Hvm. destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hst) as [Hh' Hmi'].
  assert (Ho' : own X s mo') by (eapply Hown_fds; eauto). split; [exact Ho'| exact (Hown_live _ _ _ Ho')].
Qed.

(* [comment removed for export] *)
Definition rd_invL (st : rd_st) : assn PState := fun s mo =>
  own [(rd_buf st, rd_cap st)] s mo
  /\ zlength (rd_content st) <= rd_cap st
  /\ (exists k, (k <= 10)%nat /\ rd_cap st = 65536 * 2 ^ (Z.of_nat k)).

Lemma zlength_app_rd {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["DriverL"] "h01xh11Ah24__x1h34__x2h42l1h52l2h67__arithh74__ffh88__varmaph95__with:4cstrh;5cstr0h<1nh=1yp;1p;2p;<p;4p;3p;7p;6p;Bp200R0g000mR1p4p710p8P0g02@]R2p4p710p8P0g00YhR3p4p710p8P0g01DBR4p4p710p8g00;Sj16TP3j21Tg02A<j2ATg00ZHR3j10Tg00ijR5j24Tg00=^j1Hj39Tg02ASj1@Tg00_jj23Tg02B1l<;Tg02BVj17Tg00C^j2:Tg00\Aj1TTg02C;j2STg02CYj1RTg02D7j4QTg02DUj1NTg02E3j1GTg02E^j28Tg00>kj1ETg02FAj3BTg02Fdj4CTg02GOj7DTg02H3j2?Tg02HUj2FTg02IAj3ITg02I`j4JTg02JRj4KTP4j3<TP2j3LTg002Uj6MTP1j25Tg02K=lBOTg02Kcl<PTg00eTR1f1R2f0R439p=2g00f2R6P6P6P1P1P1g02LHP3P3P3P5g02Lhf5R5f4R7f3R8f2R9P2P4MBOp=>P6P1P1P1P3P3P5P7P8P9P2P4M<Pp==%64R3%62R:P61192R;1194R<'AR=%04R>1189R?#0R@1182#0'4'2X<6%0=RA%0;RB%0<RC'4RD'212DDP1P1%H1REP4X01RFPE1224#@X=1X01PAPDPFPF131>X06P=PDP;PB131BP<PC131CE>E=PDPD131DM<;%7<g00hLR</:C%7?1:<@g02MKR@#T%6@P11S19P2%R1CQ%N1%G1R@g02N7g00NdR?P?g02NVR?P1g00JVRC,81%EC,815B1RCg02O6PCCCg00gPFD1?@?P4P9g00g0R?g00hjR@'31F49=9?@dAI1<2CJb7b8b9X21X311442R</2<^21^31P41158#01157#0O2b6b;b:CKA<924R7,19AL924EM159715921594'4'2eX5:X43X10P9P2P4O3W5W4X10o"). Qed.
Lemma zlength_u8s_rd : forall bs, zlength (u8s_of_bytes bs) = zlength bs.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["DriverL"] "h02bsh11np;1p;2p;3p;4p;6g00>kj12Tg00?Pj1=Tg00?nj1<Tg00;Sj15Tg00Yhj20Tg00ZHj11Tg00=^j33Tg00_jj2;Tg02O]j1:Tg00_4j46Tg02PGj47Tg002Uj68Tg02Pfj19Tg000mj24Tg00JV#2#2#2#=R0#<R1#5g00f2R2f0R3,01R4g00eTR5%13f1,01#133X12%14,;5P1P5%:0R0P3C6,05P1P5P0P3C7E8%93,451413535eW0o"). Qed.
Lemma pow2_le_1024_rd : forall k, (k <= 10)%nat -> 2 ^ Z.of_nat k <= 1024.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["DriverL"] "h03Hk0h17__arithh24__ffh38__varmaph45__with54__x1h64cstrh72Hkh81kp;2p;1p;4p;3p;8p;5p;<p;7g02QcR0j2:Tg00>kj17Tg00\aj19Tg00ZHR1j14Tg02R=j1LTg00C^R2j21Tg00_jj22Tg02Rbj4?Tg02BVj1>Tg00\Aj1<Tg00;Sj1;Tg02CYj1PTg02DUj1OTg02E3j1NTg02SIj23Tg02Fdj48Tg02H3j2KTg02HUj2JTg00=^j3CTg02IAj3BTg02I`j4ATg021Ij2DTg02C;j2ETg02E^j2FTg00Ajj1GTg02Slj8HTg02TPj5ITg00c\j16Tg02B1l<=Tg02GOj7MTf0R3#6#6p=0g00f2R4g00eTR5P0P1P2g02U7f5f4R2f3f2R1f1R0P3M<=p=@P0g02N7R6g00NdR7P7g02NVR8P3g00gPFMp=5g00fQ#0#0#0#0#0R9,:3g00JVR:#7R;#9R<%40R=%L;#7#9R;1:0911=;R>P0P=125=P9P;125;E@P3C?R9P>%>1R=g00hLR?%41'1R@g02MKRA#<RB%;ARA%P5%O5RC%N5RDP5135?g02UY135<C8'51KD8REP3P1g00g0RFg00hjRG'21J31=CFGdAB5?0CARGb2b3b41D?<P3b1b6b0P9P>P=P@PBPA1E50PCPDP6P7P7P8P51F5:g02V@135;C8,5DRD%G7PDGHPEPGb2b3b4X55113;110;[^55P3%42P1O2b1b6b0DIW7X84o"). Qed.

Lemma read_loop_body_L : forall fd path st, 0 <= fd ->
  mspecL (rd_invL st) (read_loop_body io drv_malloc drv_free read_stage fd path st)
        (fun r s mo => match r with
                       | inl st' => rd_invL st' s mo
                       | inr RdExit => exists X', own X' s mo
                       | inr (RdDone buf content) => (exists k, (k <= 10)%nat /\ own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)
                                                     /\ zlength content <= MAX_INPUT
                       end).
Proof.
  intros fd path st Hfd. unfold read_loop_body.
  eapply mspecL_bind with
    (Q1 := fun g s mo => match g with
                         | None => exists X', own X' s mo
                         | Some st1 => rd_invL st1 s mo /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
                         end).
  { apply mspecL_if_pre.
    - apply mspecL_if_pre.
      + eapply mspecL_seq; [eapply mspecL_pre; [apply Hdiag|]|].
        { intros s mo [[[Ho _] _] _]. exact Ho. }
        intros _. apply mspecL_ret. intros s mo Ho. exists [(rd_buf st, rd_cap st)]. exact Ho.
      + apply mspecL_pointwise. intros s0 mo0 [[(Ho0 & Hlen & k & Hk & Hcap) Heq] Hlt].
        apply Z.eqb_eq in Heq. apply Z.leb_gt in Hlt.
        pose proof (pow2_le_1024_rd k Hk) as Hp.
        assert (Hk9 : (k <= 9)%nat) by (unfold MAX_INPUT in Hlt; assert (k <> 10)%nat by (intros ->; cbn in Hcap; lia); lia).
        eapply mspecL_bind. { eapply mspecL_pre; [apply Hdm; lia|]. intros s mo [-> ->]. split; [exact Ho0|]. rewrite Hcap. apply OK_grow. exact Hk9. }
        intros [nb|]; cbn beta iota.
        * apply mspecL_pure. intros _. eapply mspecL_seq.
          { eapply mspecL_pre; [apply (Hdf [(nb, rd_cap st * 2)] (rd_buf st) (rd_cap st))|].
            intros s mo Ho. eapply Hperm; [apply perm_swap| exact Ho]. }
          intros _. apply mspecL_ret. intros s mo Ho. cbn. unfold rd_invL. cbn. splits; auto; try lia.
          exists (S k). split; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
        * eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists [(rd_buf st, rd_cap st)]. exact Ho.
    - apply mspecL_ret. intros s mo [[Ho [Hlen Hk]] Hne]. apply Z.eqb_neq in Hne. split; [|split; [reflexivity|lia]]. split; [exact Ho|]. auto. }
  intros [st1|]; cbn beta iota.
  2:{ apply mspecL_ret. intros s mo H. exact H. }
  apply mspecL_pointwise. intros s1 mo1 ((Ho & Hlen & k & Hk & Hcap) & Hct & Hlt).
  pose proof (pow2_le_1024_rd k Hk) as Hp.
  set (want0 := rd_cap st1 - zlength (rd_content st)).
  set (want := if 65536 <? want0 then 65536 else want0).
  assert (Hwant : 0 < want <= want0 /\ want <= 65536).
  { subst want want0. destruct (Z.ltb_spec 65536 (rd_cap st1 - zlength (rd_content st))); lia. }
  apply mspecL_bind with (Q1 := fun a s mo => s = s1 /\ own [(rd_buf st1, rd_cap st1)] s mo /\
                       match a with RdErr _ => True | RdData bs => zlength bs <= want end).
  { apply mspecL_sys; [intros; exact Logic.I|]. intros s mo [-> ->].
    intros rsp mo' evs Hst.
    pose proof (nstep_dec_read fd _ want mo1 rsp mo' evs ltac:(unfold MAX_INPUT, zlength in *; lia) Hst) as (_ & a & Hdec & Ha).
    assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
    { destruct a as [e|bs]; [destruct Ha as [-> _]; reflexivity|].
      destruct Ha as (p & off & data & _ & _ & _ & ->). apply m_vmmaps_with_fds. }
    destruct (own_after_nodeL _ _ _ _ _ _ _ Ho Hst Hvm) as [Ho' LB]. split; [exact LB|].
    intros a' Ha'. rewrite Hdec in Ha'. inversion Ha'. subst a'.
    cbn beta. split; [reflexivity|]. split; [exact Ho'|].
    destruct a as [e|bs]; [exact I|]. destruct Ha as (p & off & data & _ & _ & -> & _).
    unfold zlength. pose proof (length_file_read_le_count data off want ltac:(unfold zlength, MAX_INPUT in *; lia)). lia. }
  intros [e|bs]; cbn beta iota.
  - eapply mspecL_seq. { eapply mspecL_pre; [apply Hdiag|]. intros s mo (_ & Ho' & _). exact Ho'. }
    intros _. apply mspecL_ret. intros s mo Ho'. exists [(rd_buf st1, rd_cap st1)]. exact Ho'.
  - apply mspecL_if; intros C.
    + apply mspecL_ret. intros s mo (-> & Ho' & _). split; [| rewrite Hct; unfold MAX_INPUT in *; lia].
      exists k. split; [exact Hk|]. rewrite <- Hcap. split; [exact Ho'|]. rewrite Hct. lia.
    + apply mspecL_ret. intros s mo (-> & Ho' & Hbs). apply Nat.eqb_neq in C.
      assert (1 <= zlength bs) by (unfold zlength in *; destruct bs; cbn in *; [congruence|lia]).
      unfold rd_invL. cbn. split; [exact Ho'|]. rewrite zlength_app_rd, zlength_u8s_rd, Hct. split; [lia|]. exists k. auto.
Qed.

Lemma read_all_L : forall path,
  mspecL (own []) (read_all io drv_malloc drv_free read_stage path)
        (fun r s mo => match r with
                       | RdExit => exists X', own X' s mo
                       | RdDone buf content => (exists k, (k <= 10)%nat /\ own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)
                                               /\ zlength content <= MAX_INPUT
                       end).
Proof.
  intros path. unfold read_all.
  apply mspecL_bind with (Q1 := fun r s mo => own [] s mo /\ match r with SVal fd => 0 <= fd | SErr _ => True end).
  { apply mspecL_sys; [intros; exact Logic.I|]. intros s mo Ho. intros rsp mo' evs Hst.
    destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
    pose proof (nstep_dec_open _ mo rsp mo' evs Hmi Hst) as (_ & a & Hdec & Ha).
    assert (Hvm : m_vmmaps mo' = m_vmmaps mo).
    { destruct a as [e|fd]; [destruct Ha as [-> _]; reflexivity|]. destruct Ha as (_ & _ & _ & ent & _ & ->). apply m_vmmaps_with_fds. }
    destruct (own_after_nodeL _ _ _ _ _ _ _ Ho Hst Hvm) as [Ho' LB]. split; [exact LB|].
    intros a' Ha'. rewrite Hdec in Ha'. inversion Ha'. subst a'. cbn beta.
    split; [exact Ho'|]. destruct a as [e|fd]; [exact I|]. lia. }
  intros [e|fd]; cbn beta iota.
  - apply mspecL_pure. intros _. eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists []. exact Ho.
  - apply mspecL_pure. intros Hfd. eapply mspecL_bind; [eapply mspecL_pre; [apply Hdm; lia| intros s mo Ho; split; [exact Ho| exact OK_first]]|]. intros [buf|]; cbn beta iota.
    2:{ eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists []. exact Ho. }
    apply mspecL_pure. intros _.
    eapply mspecL_bind.
    + eapply mspecL_pre.
      * apply (mspecL_loop B (read_loop_body io drv_malloc drv_free read_stage fd path) rd_invL
                 (fun r s mo => match r with RdExit => exists X', own X' s mo
                                | RdDone buf content => (exists k, (k <= 10)%nat /\ own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)
                                                        /\ zlength content <= MAX_INPUT end)).
        intros st. eapply mspecL_post; [apply read_loop_body_L; exact Hfd|].
        intros [st'|[|b c]] s mo H; exact H.
      * intros s mo Ho. unfold rd_invL. cbn. split; [exact Ho|]. split; [unfold zlength; cbn; lia|]. exists 0%nat. split; [lia|reflexivity].
    + intros [|buf' content]; cbn beta iota; [apply mspecL_ret; intros s mo H; exact H|].
      apply mspecL_pointwise. intros s1 mo1 [(k & Hk & Ho1 & Hck) Hlen].
      eapply mspecL_bind with (Q1 := fun _ s mo => own [(buf', 65536 * 2 ^ Z.of_nat k)] s mo).
      * apply mspecL_sys; [intros; exact Logic.I|]. intros s mo [-> ->]. intros rsp mo' evs Hst.
        pose proof (nstep_dec_close fd mo1 rsp mo' evs Hst) as (_ & a & Hdec & Ha).
        assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
        { destruct a as [e|v]; [destruct Ha as (_ & -> & _); reflexivity|]. destruct Ha as (_ & _ & ->). apply m_vmmaps_with_fds. }
        destruct (own_after_nodeL _ _ _ _ _ _ _ Ho1 Hst Hvm) as [Ho' LB]. split; [exact LB|]. intros; exact Ho'.
      * intros _. apply mspecL_ret. intros s mo Ho. split; [| exact Hlen]. exists k. auto.
Qed.

Lemma main_model_L : forall argv,
  mspecL (own []) (main_model io drv_malloc drv_free read_stage alloc_init run alloc_count argv)
        (fun _ s mo => exists X', own' X' s mo).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PStdio ()) ["DriverL"] "p'0h02moh11sh22_Hh36statush47status'h51Hh62X'h72Hah86__sat2h94__x1h:1xi001xh;3Hk0h<7__arithh=4__ffh>8__varmaph?5__with@4__x2hA4cstrhB1nhC6__sat1hD1khE2HohF4__p1hG4__p2hH4__p3hI6__sat4hJ4__x3hK4__x4hL4__x5hM3mo'hN2s'hO2H0hP2H1hQ2H2hR4HcaphS3HckhT2HkhU4HlenhV3Ho0hW2HphX6__sat3hY1ahZ4argvh[1bi011bh\3bufi023bufh]7contenti037contenth^5cstr0h_1mh`3mo0ha1ri041rhb2rai052rahc2s0hd1yhe2z1hf2z2i06<count_allocsp%0p&0p;1p;2p;4p;3p;7p;5p;<p;6p;8p;9p;;p;:p;Bg00;Sj1jTg00Yhk20=Tg00ZHR0j11Tg00>kj1:Tg00\aj1HTg00X5k20^Tg03^[k10YTg00\Aj1tTg03_9j4hTg01\_k103Tg02Y5j3dTg01SiR1k10vTg00c\j1>Tg03\3k70:Tg003hk20]Tg02R=j1STg03_Uj2?Tg03`Jj1;Tg03a?j2<Tg00jGj2lTg012Tj5nTg02@=k20HTg00_PR2j2\Tg02_Oj4pTg02QcR3j2iTg00BLS00j27Tg00C^R4j22Tg03a`k10`Tg03b^j2ITg00=^j36Tg02Ymj2KTg02aFk20ZTg02_2j2=Tg02Rbk406Tg02BVj1yTg02bIj2xk40NTg02c1j3wTg02cUk20XTg00_jj2uTg02CYk10WTg02DUk10VTg02E3k10UTg02SIj2VTg02H3k20TTg02HUk20STg02IAk30RTg02I`k40PTg02C;j2_Tg02E^j2ZTg00Ajk10OTg02e5j2^Tg02hlk204Tg03F<k30MTg00ijj2NTg00^5R5j1oTg03c<k30KTg03d2k20ITg01@Hj2TTg02ASk10GTg02B1m<02Tg03dIk201Tg025Pj2gTg02d6k10CTg02dTk20BTg02e^k30JTg02oZk30ATg02FAk30@Tg02JRk40?Tg03dkk30>Tg002Uj6qTg03eLk80QTg01Tem900Tg01X^k70uTg03f;k80tTg0000k80sTg01W`k80rTg008<m;0qTg03g;m:0oTg00P8k30mTg000mk20lTg01Abj3zTg03h6k10gTg00Qik70fTg00b_m;09Tg03Cdk40eTg00kXk308Tg007Ck60dTg021Ik20cTg02Fdj4|Tg02GOk70<Tg02Slk80bTg03Dgk30aTg03EPk20hTg02D7k40iTg03Ggk70jTg03hkk20kTg02Kcm<0;Tg02K=mB0_Tg03F_k60nTg03iHk70\Tg00acm:0pTg00ERR6g00eTR7f0R840mp=]P6g00NdR9P7f1R:P8Dnp=020l78p=8g03ilR;,l8p=P%S8#Sp=`%;:/I8p=B1N;8,l:p=Gf2R;/N:#o=z78$0gp=Cg00hLR</l8p=@1N;:#o=z78p=DP6P7P7P:P8Dnp=3g00g0R=g00hjR>768p=fP6f4R?P7f3R@P;P:P8K0fp=aP6f7RAP9P7f6RBf5RCP?P@P;P:P8N;09p=Qg00iJ96=8p=v%:8#:p=~%:8#:#:#:p=k1=:8,K;p=mP@P7P;P:H0e>08?8p=412:8,7;p=MP6P@P7P;P:P8J0dp=Y%18,=:,K;p=F%18,=:p>0[1u78p=Xg00f2RDP7P3P0P4g02U7PCP?P@P;P:P8N<02p>0712<8p=520c<8p=9P7P:g02UYP8C|p=sP:g02N7R3P9P9g02NVREP8g00gPRFK0<p=RP;P3P9P9PEP7P:g02V@P8C|PFK0<p=JP@P3P9P9PEP;P:P8L0bp=AB0a7:8p=Lg03LO-0h8p=Ug02MKRF@08:8p=[P7P;P:P8H0ip=WP;P3P9P9PEP:P8K0jp=bAz7:8p>0L20=78p=O20k<8p=EP7PDP7P7P5P?P0P@g03jdP;P:P8N<0;p>0FPDPDPDP7P7P7g03kQP0P0P0PBg03l1PCP?P@P;P:P8NB0_p>0EPDP7P7P7P0P0PCP?P@P;P:P8N<0;p>0DA678<p=eP:P3P9P9PEP8J0np={P7P:g02O6P8C|p=cP;P3P9P9PEP:P8K0\p>05P6PAP7P7PBPCP?P@P;P:P8N;09p=rP6PAP7PBPCP?P@P;P:P8N:0pp=}%j7R3#jp,1BR020=38#1g00JVR5#:RG#HRH+0^$0YRIp,2ioRJP3g00fQRKP8%t7RLCh$035d6%]HRMV9RN'0P6p,3ptrRO$0vRPP7P6POPJp,:drv_mallocS01p,8drv_freeRQp,:read_stageS02P3%>KRRP8PLChK0:P1PO20]67RSP8PMP=PS%88RT#Pg01h?RU9d6JRVPQP;O1/0NV9RW'0P=PS%S5RX#SS03#SRY#S#`#`#`#`#`#HRZ,B8R[,GTg01j<R\9d6JR]/0Wp,:alloc_initRWACH[8O1p,3runR[P=P71B:ZR^#@1?:HP<n0100000020000%:XS04#HRX?D^:O2P=PS%;;R_%HYRY'<p,;alloc_countS05P=P7g03lXR`,l8P8P`n0100000020000S06#]XB7S07'3R`%]8Ran0110600020000PQP?O1Rb%]:V9Rc'0X47'3X37'3V9'0n0100000020000n0100000020001S08n10110500020021102103RdXbPReDnp,3ownRf20HO7Rg#tRhO1Rig00FKRj%jgRkp,4own'RlP8P;P:O3X6k'\W0X16V7Rm%fIP0P3PKP:PLCh$03Rn9d6JPNPiPiPmp,5HdiagRoPhPnO2P0PHPiPmPfPhP:P8O3PkPlP8P@P;O3X6kS09Php,4Hoo'RnPhP;P:P8O4CpWEX0jX16DaX29RpGQW2%vIP6P0PPP7P6POPJQ01PQQ02P3PRP:PLChRLK0:PePiP1POp-0ReP;PfP8P;P:O3X6k,\kRI%>RS0:#>S0;#>S0<#>S0=#>#>#>#>#>RR,i8RqPfPgPOP;%:GS0>#:S0?#:#~#kRr#~#kS0@#HRs%18Rt7mHRuPhD4P?P@O3%8:Rv;Mu'7XDD,\Dg03J7Rw,2TS0A'7n10110400020020102103X0jX16RTXaPPm&0`LP1POP0PTPdPmCYP8P0PHPIX0jX16RdPmP2PkPfP8P@P;O3X6kPlP8P?P@O3X6k,\kP8PfP8PCP?O3PkPlP8PAPBO3X6kP:PnP:PBPCP8O4CpW5X6kP:P8O2n2001000000120100000XOIX0jX16DaP0PdPMPmCYeP6P0P7PfPgPOP?PuPhD4P;P:O3%8@RM;Mu,7qXDD,\DS0BX0jX16Q0AQ08PmQ0AP6P0P7PD1i;RPfPgPOPCAFsH;RuPhD4P:P8O3%8?;MuRu'7X0jX16X:DP=PS%PvPQP@O1/0NV9Rd,0VP=PS1Gv^10]dPWACH^:O1P[P=P71I_ZR_#@1?;HP<n0100000020000ADX_;O2P=PS%;@R^/<YP`Pan0110600020000PQPCO1Rd/0cX47'3X37'3V9'0n0100000020000n0100000020001PmP6P0P7PuX0jX16PqP=PS%8;Ru#P10bNV9Rb,0VP=PS1Gu_10]bPWACH_;O1P[P=P71I^ZR^#@1?@HP<n0100000020000ADX^@O2P=PS%;?R_/<YP`Pan0110600020000PQPBO1/0cX47'3X37'3V9'0n0100000020000n0100000020001PmP6P0P7P=PS%PM10dNV9Rd,0VP=PS1GM^10]dPWACH^@O1P[P=P71I_ZR_#@1??HP<n0100000020000ADX_?O2P=PS%;C/<YP`Pan0110600020000PQPAO1/0cX47'3X37'3V9'0n0100000020000n0100000020001R_PfPgPOPBAFsH@R^PhD4P:P8O3%8C;M^R^X0jX16RdPdPmP6P0P7PdP_PmQ00PfPgPOPAAFsH?R_PhD4P;P:O3%8B/2_P0A66:CA6j8?'7XMjXN6P=PS%8AR_#PPQf9RdO1/0NV9RM,0VP=PS1BAZRb,G_10]MPWACHbAO1P[P=P7f8Rb/BZRM#@1?bHP<n0100000020000ADXMbO2P=PS%;d/<YP`Pan0110600020000PQf;RMO1/0cX47'3X37'3V9'0n0100000020000n0100000020001PmCYP8PfPgPOPdAFsHBPhD4P?P@O3%8dAFsHA'2P6P0P7P=PSf:R_#8Rv#PPQf<RIO1/0NV9Rn,0VP=PS1B_ZR2,Gv10]nPWACH2_O1P[P=P71BMZR2#@1?MHP<n0100000020000ADX2MO2P=PS%;IRn/<YP`Pan0110600020000PQf>RvO1RT/0cX47'3X37'3V9'0n0100000020000n0100000020001PfPgPOPM20[HbR1,KsPhD4O1A66:bA6j8A'7S0CXMjXN6Pm20ZbA%HrRr,21P0%8MR1#PRLPQf=RxO1/0NV9Ry,0VP=PS1G1210]yPWACH2MO1P[P=P71InZRn#@1?IHP<n0100000020000ADXnIO2P=PS%;xR2/<YP`Pan0110600020000PQf?RyO1R1/0cX47'3X37'3V9'0n0100000020000PfPgPOPIAFsHdPhD4O1Pm%fLP0PV10TNV9RVPfPgPOPxAFsH_PhD4RzO1R{P{PmPoPzPUO2P0PTPNPfPgPOPvAFsHMRTPhD4RUO1RzPiPmp,3HdfR|PhPvPTO3PpGQX29GQW2%vLP0%8I/GnRL10]VPWACHnIO1P[P=P71I2ZR2#@1?xHP<n0100000020000ADX2xO2P=PS%;vRn/<YP`Pan0110600020000PQf@RVO1/0cX47'3X37'3V9'0P{Pm%fLP0P]101NV9PzPzPmPoPUP\O2P0P1PNPfPgPOPy%1IRN,=HS0D,KsR1PhD4S0EO1PiPmP|PhPyP1O3PpGQX29GQW2%vLP0PWACH2xR2O1P[P=P71InZRn#@1?vHP<n0100000020000ADXnvO2P=PS%;yS0F/<YP`Pan0110600020000PQfARnO1/0cX47'3X37'3V9PzPzPmp,5HinitPUP2O2PHPN1iIR%SG#:#HR2,2NRUPIPN%XNPRP2%X2S0GJ07PMH06S0HPU%yxS0I%1xRN#5S0J%1vRz,xHS0K%9HRL%1yRp#5%1VR|,=HS0L#9[[S0M%5HR\g03O\Ro%1nR]=wH:UW7S0N1=H]R{#5\o^7\RTP:g03P820X<H'uPLeO1S0O%5|%9{[S0P%tFR|%jFS0Q&0W7RF&0V7S0R&0U7R}1V7<R~1V7H's'R20T}ES0SP8P;1u=>20S8;#fdB0R7<:H0PS0Tb=b>b?PLP8b<b8bCb8bAb;Q0HPUQ0IQ0JQ0KQ0MQ0NPTQ0OQ0PP|Q0Q1_7:Q0RP}1Z75RT9J}~RU&0O9R>PUCAQ0SQ0Tb=b>b?X97%58%5:S0N[^97P8fBRU#1REP?O2b<b8bCb8bAb;H0NQ0D#91ixR12N2S0DPxPN%XNPRP2Q0GJ07PIH06S0GQ0D%yvS0M%5zS0K1xHpQ0P\LAwHE:VoX7\1=HERE#5\o^7\Q0O%5]%9E[1^7KRKQ0<,^7R],LK#U+04Q0:,^7R2,LK#U-04K/[|'[Q0Q1_7;?W;F?W:FQ0RP}P}Q0>,Z79J}~RRP>1s~T,R}CAP>P}PRP>P}1V7r9J}TP>1V7sRRB0M7RTRR5J}Q0@#~#k#k#HRx,V79J}R5b}CACACAQ0SQ0Tb=b>b?X97X@7Q0N%9:[%5;12;r1Ks@Rr,2s?Mrx[[[^97^@7P8fCRr#1Rx1=HxP:P?P_O5b<b8bCb8bAb;AmsHNRN,2s?MNweb512s1?M1wP0P[P=P7Q0F/IZR1#@1?yHP<n0100000020000R_1NX1R1#oRx00LyRRO2P=PS%;V/<YS0FP`Pan0110600020000S0NPQPUO1S0@/0cX47S0>'3X37PfPgPOPVPNPhD4RaO1PlPaO1Pmp,4HrunPVPNP_PRP8P7P4g03mR:0K74%8RS0:%8yS0<PwPD%OyR_00IxRN%OV#1,2tXBD%1NS0P%1_RV'2%E1S0J,TV#ERa/2VP7P7P4P8X:7RYP412:8$0GXd7X:7Q0PPaPYPY%XtX:DPNPa1T:8#EX_7XB7P_PV%XVR_PxQ0JPY%E8X:7P1P1%X1I0FK0EJ0DPVPVP_N<02Q0GQ0DQ0MQ0K%OnR_#y%1_#51BUZ,NXR_-01<%9_%E_RV=67_'712_<%eV'7'g1BrZ,NX#EP7fDRV#O#1/T8R_-01<%9_%E_R1=67_'712_<%e1'7'gfER1#O#1/T:#EP7%1V,xH%11#5fF#1R_,=H#9[\LfG#1RL=wH:VoX7\1=HLRL#5\o^7\Q0O%5_%9L[1L2KR2,L]#UQ0=,^7RL/L2#U&0C5-0B7Q0;,^760J7/LK,L]R],LL#U%U]/[|'['['[Q0Q1_7C?WCF1_7@7W;1_7?9WFC7W:Q0RP}1{}A1Z7GRGQ0?,Z7RF60A7,cT,R}5b}1{}b1cT~,R}5b}605}P>P}1V7XQ03,Z760@7R|,s~,R}1cF|,R}5b}1{}d1cF~,R}5b}605}P>P}AJ}~GP>P}Q04,Z79J}~P>AJ}TGCACACACAQ0SQ0Tb=b>b?X97X@7XJ7XK7XL7XFeXGeXHe1T:?9678,7C%e8,7B'g1NX?RG#9A67CG'7%eC,7b'g%5@%5C12?C[[[[^97^@7^J7^K7^L7^Fe^Ge^HeP8fJRe/BZRZ,NX/2<%Oe#1Re/TBRX/2<%9XPBPZfH#1PeP?PCPAPbPdO<b<bIbXbIbfbQbebPb^bAb;H0?%ORB0>7xyEqQ0:Q0<'2ePvL0QO6P0Q0NQ0>PlPgPOPnAmsHzPhD4O1RzPzPmQ0FP=P=P0PlPgPOPrQ0L,KsPhD4RrO1RzP=PSP8P`%];n0110600020000PlPgPOPV1Ks{PhD4R{O1V7RVCYP8P0Q05Q07PlPgPOPUAmsHpRpPhD4RHO1R`P`PzV7RSp,6HcountPHO1P0Q06PzPVPlPgPOP11KsEPhD4P:P8O3P8W5X0jX16DaXB7GrP0P:P`PSPlP{P:P8O3P8W5X0jX16Dan0110100020100b[P0Q0@PcP`PlPhO1R`Pmp,4Hdf'PhPUPpO3P0P:P`PmPlPhP:P8O3PkQ09PhP8CpWEX0jX16DaX29GQX47GrX37GrbRX29GQW2G}W2G}bWQ0CQ00A66;dA6j:bPfQ0EP@P;O3P8A66?MP6PIA6jCIPfPrP:PBO3[X16A6j?MPjPIPfPrPvP8O3X0jPbPCP8EqW5PCP8EqW5P:P8O2n2001000000120000000W5X0jX16N900WSWVP:P8O2n2001000010121000000X5^X`jXc6K0uP8X5^X0jX16N900XTqL0tXDDL0sWUL0rP0Q0B?MuwX0jX16Q08PmCYeX]3X\OP:P8O2n10110401020021102103XYPN;0qW2G}P0PiP6POPJQ01PQQ02PWP[Q05P8N:0oPmCYeWZo"). Qed.

Lemma exit_model_L' : forall code,
  mspecL (fun s mo => exists X, own' X s mo) (exit_model io code) (fun _ _ _ => False).
Proof.
  intros code. unfold exit_model. eapply mspecL_seq with (R := fun s mo => exists X, own' X s mo).
  - apply mspecL_exI. intros X. eapply mspecL_post; [apply Hexit|]. intros a s mo Ho. exists X. exact Ho.
  - intros _. apply mspecL_sys; [intros; exact Logic.I|]. intros s mo _ rsp mo' evs Hst. destruct (nstep_exit_none _ _ _ _ _ Hst).
Qed.
End DriverL.
