(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface RT_fk RT_fk_iface Po_rows Po_iface Po_sakit Po_strnew Po_strtok Po_saadd Po_sasplit_defs Po_sasplit_c0 Po_sasplit_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_sasplit () := "C69OSSVerify5KrLib2K53A23=Po_sasplit_c0:sasplit_c0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>Po_sasplit_c16;sasplit_c16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23?Po_sasplit_defsHsarraySplitSeq2_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SASPLIT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis SN : stringNew2_cps RT.
Hypothesis ST1 : strtokSafe2_cps1 RT.
Hypothesis ST2 : strtokSafe2_cps2 RT.
Hypothesis ST3 : strtokSafe2_cps3 RT.
Hypothesis SAD : sarrayAddString2_cps RT.

Theorem sarraySplitSeq2_ok : sarraySplitSeq2_cps RT.
Proof using AF GP FKC SN ST1 ST2 ST3 SAD.
ltac2:(KReplay.run1 (kr_t_Po_sasplit ()) ["SASPLIT"] "p;9p;3g0000l92Tg0014l91Tg002:j30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,2SNR4p,3ST1R5p,3ST2R6p,3ST3R7p,3SADR8M92P0P1P2P3P4P5P6P7P8M9130o"). Qed.

End SASPLIT.
