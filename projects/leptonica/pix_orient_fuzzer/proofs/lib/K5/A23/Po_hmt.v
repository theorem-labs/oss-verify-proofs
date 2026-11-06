(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_iface Pm_iface2 Cf_iface RT_fk RT_fk_iface Bi_iface Bi_iface2 Bi_fktw D_iface D_defs Po_rows Po_iface Po_dilate_defs Po_morph2_defs Po_hmt0 Po_hmt16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_hmt () := "C69OSSVerify5KrLib2K53A237Po_hmt09pixHMT2_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_hmt16:pixHMT2_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>Po_morph2_defs=pixHMT2_of_alC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section HMT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis PMA : processMorphArgs12_cps RT.
Hypothesis SGP : selGetParameters_cps RT.
Hypothesis PCLR : pixClearAll_cps RT.
Hypothesis PSET : pixSetAll_cps RT.
Hypothesis SFMT : selFindMaxTranslations_cps RT.
Hypothesis PROP : pixRasterop_po_cps RT.
Hypothesis PDRC : pixDestroy_rc_cpsF RT.

Theorem pixHMT2_ok : pixHMT2_cps RT.
Proof using AF GP FKC PMA SGP PCLR PSET SFMT PROP PDRC.
ltac2:(KReplay.run1 (kr_t_Po_hmt ()) ["HMT"] "p;;p;3g0000l;2Tg000ml;1Tg001lj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,3PMAR4p,3SGPR5p,4PCLRR6p,4PSETR7p,4SFMTR8p,4PROPR9p,4PDRCR:M;2P0P1P2P3P4P5P6P7P8P9P:M;130o"). Qed.
End HMT.
