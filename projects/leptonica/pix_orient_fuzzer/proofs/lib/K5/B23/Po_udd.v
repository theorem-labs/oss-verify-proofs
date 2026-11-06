(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface RT_fk RT_fk_iface Bi_fktw RT23_iface Po_rows Po_iface Po_casc_defs Po_count_defs Po_udd_defs Po_udd_c0 Po_udd_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_udd () := "C69OSSVerify5KrLib2K53B239Po_udd_c06udd_c0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Po_udd_c167udd_c16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;Po_udd_defsIpixUpDownDetect2_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section UDD.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis SM3 : stack_malloc_x_contractF RT 3%nat.
Hypothesis SCS : selCreateFromString_cps RT.
Hypothesis PMCS : udd_pmcs_cps RT.
Hypothesis HMT : udd_hmt_cps RT.
Hypothesis POR : pixOr_cps RT.
Hypothesis CASC : pixReduceRankBinaryCascade2_cps RT.
Hypothesis CNT : pixCountPixels2_cps RT.
Hypothesis DFD : pixDebugFlipDetect_cps RT.
Hypothesis DES : pixDestroy_cpsF RT.
Hypothesis DESN : pixDestroy_null_cpsF RT.
Hypothesis SDES : selDestroy_cps RT.

Theorem pixUpDownDetect_ok : pixUpDownDetect2_cps RT.
Proof using AF GP FKC SM3 SCS PMCS HMT POR CASC CNT DFD DES DESN SDES.
ltac2:(KReplay.run1 (kr_t_Po_udd ()) ["UDD"] "p;?p;3g0000l?2Tg000ll?1Tg001jj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,3SM3R4p,3SCSR5p,4PMCSR6p,3HMTR7p,3PORR8p,4CASCR9p,3CNTR:p,3DFDR;p,3DESR<p,4DESNR=p,4SDESR>M?2P0P1P2P3P4P5P6P7P8P9P:P;P<P=P>M?130o"). Qed.
End UDD.
