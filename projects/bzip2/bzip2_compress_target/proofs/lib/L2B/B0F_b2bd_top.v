(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim L_libA. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_hkit L_harn_defs RT_globals.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtS L2StmtD B0_sessK B0F_b2bd_K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require B0F_dec_L2t B0F_d10_L2t B0F_bzd_L2t B0F_dinit_L2 B0F_dend_L2 B0F_b2bd_L2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_bzd_skV B0F_bzd_srK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).
Module HD := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__.

Section Top.
Variable RT : rt_sig.
Hypothesis RC : rt_contracts RT.
Hypothesis AF_PRIM : af_live_primary RT.
Hypothesis ACL : forall Σ (m : mem), ART RT Σ m -> @alloc_ceiling (aceil_of_sp (rt_sp0 RT Σ)) = rt_sp0 RT Σ - STACK_WIN.
Hypothesis AF_DRV : forall Σ (m : mem), ART RT Σ m -> drv_consts m.

Theorem b2bd_cps_B0_K : HD.b2bd_cps RT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A dec_okL.
Proof.
  pose proof (rc_facts RT RC) as AF. pose proof (rc_asan_memset RT RC) as MSET.
  apply (B0F_b2bd_L2.b2bd_glue RT AF (rc_stack_malloc_2 RT RC) MSET).
  - intros AC. exact (@B0F_dinit_L2.bzDecompressInit_cps AC RT AF AF_PRIM (rc_malloc RT RC)).
  - intros AC.
    pose proof (@B0F_dec_L2t.decompress14_cps AC RT AF AF_DRV AF_PRIM (rc_stack_malloc_0 RT RC)) as D14.
    pose proof (@B0F_d10_L2t.decompress10_cps AC RT AF AF_DRV AF_PRIM (rc_stack_malloc_0 RT RC) (rc_malloc RT RC)) as D10.
    exact (@B0F_bzd_L2t.bzDecompress_cps AC RT AF AF_DRV D10 D14 AF_PRIM (@B0F_bzd_srK.B0_smallr_spec AC)).
  - intros AC. exact (@B0F_dend_L2.bzDecompressEnd_cps AC RT AF AF_PRIM (rc_free RT RC)).
  - exact ACL.
Qed.
End Top.
