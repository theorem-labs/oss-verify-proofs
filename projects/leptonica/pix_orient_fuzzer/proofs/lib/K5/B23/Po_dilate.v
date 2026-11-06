(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_iface Pm_iface2 Cf_iface RT_fk RT_fk_iface Bi_iface Bi_iface2 Bi_fktw D_iface D_defs Po_rows Po_iface Po_dilate_defs Po_dilate0 Po_dilate16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_dilate () := "C69OSSVerify5KrLib2K53B23:Po_dilate0<pixDilate2_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;Po_dilate16=pixDilate2_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23>Po_dilate_defs@pixDilate2_of_alC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section DILATE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis PMA : processMorphArgs12_cps RT.
Hypothesis SGP : selGetParameters_cps RT.
Hypothesis PCLR : pixClearAll_cps RT.
Hypothesis PROP : pixRasterop_po_cps RT.
Hypothesis PDRC : pixDestroy_rc_cpsF RT.

Theorem pixDilate2_ok : pixDilate2_cps RT.
Proof using AF GP FKC PMA SGP PCLR PROP PDRC.
ltac2:(KReplay.run1 (kr_t_Po_dilate ()) ["DILATE"] "p;9p;3g0000l92Tg0013l91Tg0028j30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,3PMAR4p,3SGPR5p,4PCLRR6p,4PROPR7p,4PDRCR8M92P0P1P2P3P4P5P6P7P8M9130o"). Qed.
End DILATE.
