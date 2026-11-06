(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env Pm_gaps_iface Pm_iface Pm_iface2 RT_fk RT_fk_iface D_iface D_defs Bi_fktw RT23_iface Po_rows Po_iface Po_kit Po_oc_defs Po_fz_defs Po_fzkit Po_fuzz_c0 Po_fuzz_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_fuzz () := "C69OSSVerify5KrLib2K53B23:Po_fuzz_c05fz_c0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;Po_fuzz_c166fz_c16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Po_fz_defs@po_fuzz_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FUZZTOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis DESER : pixDeserialize_res0_cps RT.
Hypothesis OC : pixOrientCorrect2_cps RT.
Hypothesis PXD : pixDestroy_cpsF RT.
Hypothesis PXDN : pixDestroy_null_cpsF RT.

Theorem po_fuzz_ok : po_fuzz_one2_cps RT.
Proof using AF GP FKC DESER OC PXD PXDN.
ltac2:(KReplay.run1 (kr_t_Po_fuzz ()) ["FUZZTOP"] "p;8p;3g0000j82Tg000lj81Tg001jj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,5DESERR4p,2OCR5p,3PXDR6p,4PXDNR7G2P0P1P2P3P4P5P6P7G130o"). Qed.
End FUZZTOP.
