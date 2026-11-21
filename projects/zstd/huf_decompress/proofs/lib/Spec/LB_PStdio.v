(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (18 recorded proofs replaced by written proofs (upd_so_L, stdio_write_L, stdout_stdio_write_L and 15 more); the frame hypotheses I_fds and Hown_fds also require the kernel build m_kernel unchanged, which I_after_node and own_after_nodeL supply from nstep_kernel). *)
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
Hypothesis I_fds : forall s mo mo', I s mo -> m_vmmaps mo' = m_vmmaps mo -> m_kernel mo' = m_kernel mo -> minv mo' -> m_halted mo' = None -> I s mo'.
Hypothesis I_live : forall s mo, I s mo -> live mo <= B.
Hypothesis I_so : forall s mo v, I s mo -> I (set_so_ps v s) mo.

Lemma I_after_node : forall s mo n rsp mo' evs,
  I s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> I s mo' /\ live mo' <= B.
Proof.
  intros s mo n rsp mo' evs Ho Hst Hvm. destruct (I_minv _ _ Ho) as [Hmi Hh].
  pose proof (nstep_kernel _ _ _ _ _ Hst) as Hkb.
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hst) as [Hh' Hmi'].
  assert (Ho' : I s mo') by (eapply I_fds; eauto). split; [exact Ho'| exact (I_live _ _ Ho')].
Qed.

Local Notation mspecL := (mspecL B).
Local Ltac ret_I := apply mspecL_ret; intros ? ? HH; exact HH.

Lemma upd_so_L : forall f, mspecL I (upd_so ps_so set_so_ps f) (fun _ => I).
Proof. intros f. unfold upd_so. apply mspecL_upd'. intros s mo Ho. apply I_so. exact Ho. Qed.

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
Proof. intros fd buf s. unfold stdio_write. apply mspecL_if; intros _; [apply mspecL_munr| apply stdio_write_loop_L]. Qed.

Lemma stdout_stdio_write_L : forall s, mspecL I (stdout_stdio_write ps_so set_so_ps s) (fun _ => I).
Proof.
  intros s. unfold stdout_stdio_write. eapply mspecL_seq; [apply rd_so_L|]. intros so.
  eapply mspecL_seq; [apply stdio_write_L|]. intros _. apply upd_so_L.
Qed.

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
Proof. unfold stdout_towrite. apply upd_so_L. Qed.

Lemma stdout_fwritex_L : forall s, mspecL I (stdout_fwritex ps_so set_so_ps s) (fun _ => I).
Proof.
  intros s. unfold stdout_fwritex. eapply mspecL_seq; [apply stdout_towrite_L|]. intros _.
  eapply mspecL_seq; [apply rd_so_L|]. intros so.
  apply mspecL_if; intros _; [apply stdout_writefn_L|].
  apply mspecL_if; intros _; [|apply upd_so_L].
  eapply mspecL_seq; [apply mspecL_if; intros _; [apply stdout_writefn_L| ret_I]|]. intros _. apply upd_so_L.
Qed.

Lemma out_pieces_L : forall ps, mspecL I (out_pieces ps_so set_so_ps ps) (fun _ => I).
Proof.
  induction ps as [|p ps IH]; cbn [out_pieces]; [ret_I|]. eapply mspecL_seq; [apply stdout_fwritex_L|]. intros _. apply IH.
Qed.

Lemma stdout_vprintf_L : forall ps, mspecL I (stdout_vprintf ps_so set_so_ps ps) (fun _ => I).
Proof. intros ps. unfold stdout_vprintf. eapply mspecL_seq; [apply stdout_towrite_L|]. intros _. apply out_pieces_L. Qed.

Lemma stdout_exit_flush_L : mspecL I (stdout_exit_flush ps_so set_so_ps) (fun _ => I).
Proof. unfold stdout_exit_flush. eapply mspecL_seq; [apply rd_so_L|]. intros so. apply mspecL_if; intros _; [apply stdout_writefn_L| ret_I]. Qed.

Lemma stderr_pieces_L : forall ps buf, mspecL I (stderr_pieces (St:=PState) buf ps) (fun _ => I).
Proof.
  induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [ret_I|].
  apply mspecL_if; intros _; [|apply IH]. eapply mspecL_seq; [apply stdio_write_L|]. intros _. apply IH.
Qed.

Lemma stderr_fprintf_L : forall ps, mspecL I (stderr_fprintf (St:=PState) ps) (fun _ => I).
Proof. intros ps. unfold stderr_fprintf. eapply mspecL_seq; [apply stderr_pieces_L|]. intros buf. apply stdio_write_L. Qed.

Lemma stderr_fwrite_L : forall s, mspecL I (stderr_fwrite (St:=PState) s) (fun _ => I).
Proof. intros s. unfold stderr_fwrite. apply mspecL_if; intros _; [apply stdio_write_L| ret_I]. Qed.

(* [comment removed for export] *)
Lemma s_diag_L : forall d, mspecL I (s_diag d) (fun _ => I).
Proof. intros d. destruct d; cbn [s_diag]; first [apply stderr_fprintf_L | apply stderr_fwrite_L]. Qed.

Lemma s_emit_L : forall v, mspecL I (s_emit ps_so set_so_ps v) (fun _ => I).
Proof. intros v. unfold s_emit. apply stdout_vprintf_L. Qed.

(* [comment removed for export] *)
Lemma new_handler_L : forall (Q : Empty_set -> assn PState), mspecL I new_handler Q.
Proof. intros Q. unfold new_handler. apply mspecL_munr. Qed.

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
  m_vmmaps mo' = m_vmmaps mo -> m_kernel mo' = m_kernel mo -> minv mo' -> m_halted mo' = None -> own X s mo'.
Hypothesis Hown_live : forall X s mo, own X s mo -> live mo <= B.
(* [comment removed for export] *)
Hypothesis OK_first : mal_ok [] 65536.
Hypothesis OK_grow : forall b k, (k <= 9)%nat -> mal_ok [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).

Lemma own_after_nodeL : forall X s mo n rsp mo' evs,
  own X s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> own X s mo' /\ live mo' <= B.
Proof.
  intros X s mo n rsp mo' evs Ho Hst Hvm. destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
  pose proof (nstep_kernel _ _ _ _ _ Hst) as Hkb.
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hst) as [Hh' Hmi'].
  assert (Ho' : own X s mo') by (eapply Hown_fds; eauto). split; [exact Ho'| exact (Hown_live _ _ _ Ho')].
Qed.

(* [comment removed for export] *)
Definition rd_invL (st : rd_st) : assn PState := fun s mo =>
  own [(rd_buf st, rd_cap st)] s mo
  /\ zlength (rd_content st) <= rd_cap st
  /\ (exists k, (k <= 10)%nat /\ rd_cap st = 65536 * 2 ^ (Z.of_nat k)).

Lemma zlength_app_rd {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_u8s_rd : forall bs, zlength (u8s_of_bytes bs) = zlength bs.
Proof. intros. unfold u8s_of_bytes, zlength. rewrite length_map. reflexivity. Qed.
Lemma pow2_le_1024_rd : forall k, (k <= 10)%nat -> 2 ^ Z.of_nat k <= 1024.
Proof. intros k Hk. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; lia. Qed.

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
  intros argv. unfold main_model.
  apply mspecL_if; intros _.
  { eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists []; apply Hoo'; exact Ho. }
  eapply mspecL_bind; [apply read_all_L|].
  intros [|buf content]; cbn beta iota; [apply mspecL_ret; intros s mo [X' H]; exists X'; apply Hoo'; exact H|].
  apply mspecL_pure. intros Hlen. apply mspecL_exI. intros k. apply mspecL_pure_l. intros Hk.
  apply (mspecL_pre B _ (fun s mo => own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)); [| intros s mo H; exact H].
  apply mspecL_pointwise. intros s0 mo0 [Ho0 Hck]. apply (mspecL_pre B _ (own [(buf, 65536 * 2 ^ Z.of_nat k)])); [| intros s mo [-> ->]; exact Ho0].
  pose proof (pow2_le_1024_rd k Hk) as Hp.
  apply mspecL_if; intros _.
  { eapply mspecL_seq; [apply Hdiag|]. intros _. eapply mspecL_seq; [apply Hdf|]. intros _. apply mspecL_ret. intros s mo Ho; exists []; apply Hoo'; exact Ho. }
  apply mspecL_if; intros _.
  { eapply mspecL_seq; [apply Hdiag|]. intros _. eapply mspecL_seq; [apply Hdf|]. intros _. apply mspecL_ret. intros s mo Ho; exists []; apply Hoo'; exact Ho. }
  eapply mspecL_seq; [apply Hinit|]. intros _.
  assert (Hcap : 65536 <= 65536 * 2 ^ Z.of_nat k <= MAX_INPUT) by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)); unfold MAX_INPUT; lia).
  eapply mspecL_seq; [apply Hrun; [exact Hcap| etransitivity; [| exact Hlen]; unfold zlength; rewrite length_skipn; lia]|]. intros status.
  eapply mspecL_seq with (R := own' [(buf, 65536 * 2 ^ Z.of_nat k)]).
  { destruct (Z.testbit _ 15); [|apply mspecL_ret; intros s mo H; exact H].
    eapply mspecL_seq; [apply Hcount|]. intros n. apply mspecL_ret. intros s mo H; exact H. }
  intros status'. eapply mspecL_seq; [apply Hdf'|]. intros _. apply mspecL_ret. intros s mo Ho. exists []. exact Ho.
Qed.

Lemma exit_model_L' : forall code,
  mspecL (fun s mo => exists X, own' X s mo) (exit_model io code) (fun _ _ _ => False).
Proof.
  intros code. unfold exit_model. eapply mspecL_seq with (R := fun s mo => exists X, own' X s mo).
  - apply mspecL_exI. intros X. eapply mspecL_post; [apply Hexit|]. intros a s mo Ho. exists X. exact Ho.
  - intros _. apply mspecL_sys; [intros; exact Logic.I|]. intros s mo _ rsp mo' evs Hst. destruct (nstep_exit_none _ _ _ _ _ Hst).
Qed.
End DriverL.
