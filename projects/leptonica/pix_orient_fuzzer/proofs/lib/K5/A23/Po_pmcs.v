(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface RT_fk RT_fk_iface Pm_iface Pm_iface2 Po_rows Po_iface RT23_iface RT23b_iface Po_sakit Po_sacreate Po_sasplit_defs Po_msv_defs Po_sadestroy Po_pmcs_defs Po_pmcs_c0 Po_pmcs_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_pmcs () := "C69OSSVerify5KrLib2K53A23:Po_pmcs_c07pmcs_c0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_pmcs_c168pmcs_c16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_pmcs_defsMpixMorphCompSequence_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PMCS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis SM4 : stack_malloc_x_contractF RT 4%nat.
Hypothesis SCR0 : sarrayCreate02_cps RT.
Hypothesis SSQ : sarraySplitSeq2_cps RT.
Hypothesis SGC : sarrayGetCount_cps RT.
Hypothesis SGS : sarrayGetString_cps RT.
Hypothesis MSV2 : morphSequenceVerify2_cps RT.
Hypothesis SRC : stringRemoveWS_cps RT.
Hypothesis SS : sscanf_dd_icontractF RT.
Hypothesis PCPY : pixCopyNew1_sure_cps RT.
Hypothesis CSC : pixCloseSafeCompBrick3_cps RT.
Hypothesis SAD2 : sarrayDestroy2_cps RT.
Hypothesis ACCFMT : forall Σ m, ART RT Σ m -> acc asegs m SSCANF_FMT 6.

Theorem pixMorphCompSequence_ok : pixMorphCompSequence2_cps RT.
Proof using AF GP FKC SM4 SCR0 SSQ SGC SGS MSV2 SRC SS PCPY CSC SAD2 ACCFMT.
ltac2:(KReplay.run1 (kr_t_Po_pmcs ()) ["PMCS"] "p;@p;3g0000l@2Tg000nl@1Tg001nj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,3SM4R4p,4SCR0R5p,3SSQR6p,3SGCR7p,3SGSR8p,4MSV2R9p,3SRCR:p,2SSR;p,4PCPYR<p,3CSCR=p,4SAD2R>p,6ACCFMTR?M@2P0P1P2P3P4P5P6P7P8P9P:P;P<P=P>P?M@130o"). Qed.

End PMCS.
