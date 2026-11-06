(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read RT_liveprim L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_hkit L_harn_defs RT_globals.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt L2StmtS L2StmtD A0_sessK A0F_b2bd_K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require A0F_hbc_L2 A0F_dec_L2t A0F_bzd_L2t A0F_dinit_L2 A0F_dend_L2 A0F_b2bd_L2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).
Module HD := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.

Section Top.
Variable RT : rt_sig.
Hypothesis RC : rt_contracts RT.
Hypothesis AF_PRIM : af_live_primary RT.
Hypothesis ACL : forall Σ (m : mem), ART RT Σ m -> @alloc_ceiling (aceil_of_sp (rt_sp0 RT Σ)) = rt_sp0 RT Σ - STACK_WIN.
Hypothesis AF_DRV : forall Σ (m : mem), ART RT Σ m -> drv_consts m.
Hypothesis DEC10 : forall (AC : ACeil), @decompress10_contract AC RT.

Theorem b2bd_cps_A0 : HD.b2bd_cps RT L_libA.LIB_A dec_okL.
Proof.
  pose proof (rc_facts RT RC) as AF. pose proof (rc_asan_memset RT RC) as MSET.
  apply (A0F_b2bd_L2.b2bd_glue RT AF (rc_stack_malloc_2 RT RC) MSET).
  - intros AC. exact (@A0F_dinit_L2.bzDecompressInit_cps AC RT AF AF_PRIM (rc_malloc RT RC) MSET).
  - intros AC.
    pose proof (@A0F_hbc_L2.hbCreateDecodeTables_cps AC RT AF MSET AF_PRIM) as HBC.
    pose proof (@A0F_dec_L2t.decompress14_cps AC RT AF AF_DRV AF_PRIM (rc_stack_malloc_0 RT RC) MSET HBC) as D14.
    exact (@A0F_bzd_L2t.bzDecompress_cps AC RT AF AF_DRV (DEC10 AC) D14).
  - intros AC. exact (@A0F_dend_L2.bzDecompressEnd_cps AC RT AF AF_PRIM (rc_free RT RC)).
  - exact ACL.
Qed.
End Top.
