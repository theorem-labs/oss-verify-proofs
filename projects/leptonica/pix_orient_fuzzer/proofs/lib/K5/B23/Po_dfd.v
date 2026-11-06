(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface RT_fk RT_fk_iface Po_rows Po_iface Po_dfd_defs Po_dfd_c0 Po_dfd_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_dfd () := "C69OSSVerify5KrLib2K53B239Po_dfd_c06dfd_c0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Po_dfd_c167dfd_c16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;Po_dfd_defsLpixDebugFlipDetect2_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DFD.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.

Theorem pixDebugFlipDetect_ok : pixDebugFlipDetect_cps RT.
Proof using AF GP FKC.
ltac2:(KReplay.run1 (kr_t_Po_dfd ()) ["DFD"] "p;4p;3g0000j42Tg000lj41Tg001jj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3C2P0P1P2P3C130o"). Qed.
End DFD.
