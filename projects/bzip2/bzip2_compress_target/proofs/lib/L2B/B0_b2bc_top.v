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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtS B0_sessK B0_b2bc_K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require B0_hm_L2t B0_fs_L2t B0_bs_L2t B0_sm_L2t B0_cb_L2t B0_init_L2 B0_hc_L2t B0_bzc_L2 B0_end_L2 B0_b2bc_L2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpSess CmpSess2 CmpSessB CmpLaws CmpLawsB BzRT1 BzRT.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).
Module HD := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__.

Section Top.
Variable RT : rt_sig.
Hypothesis RC : rt_contracts RT.
Hypothesis AF_PRIM : af_live_primary RT.
Hypothesis AF_DRV : forall Σ (m : mem), ART RT Σ m -> drv_consts m.
Hypothesis ACL : forall Σ (m : mem), ART RT Σ m -> @alloc_ceiling (aceil_of_sp (rt_sp0 RT Σ)) = rt_sp0 RT Σ - STACK_WIN.

Theorem b2bc_cps_B0 : b2bc_cps_pos RT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A enc_okL.
Proof.
  pose proof (rc_facts RT RC) as AF. pose proof (rc_set_shadow RT RC) as SSH.
  apply (B0_b2bc_L2.b2bc_glue RT AF (rc_stack_malloc_2 RT RC) (rc_asan_memset RT RC)).
  - intros BZP AC. exact (@B0_init_L2.bzCompressInit_cps BZP AC RT AF AF_PRIM (rc_malloc RT RC)).
  - intros BZP AC.
    pose proof (@B0_hm_L2t.hbMakeCodeLengths_cps AC RT AF (rc_stack_malloc_7 RT RC) SSH (rc_stack_free_7 RT RC)) as HM.
    pose proof (@B0_sm_L2t.sendMTFValues_cps BZP AC RT AF (rc_stack_malloc_2 RT RC) HM AF_PRIM) as SM.
    pose proof (@B0_fs_L2t.fallbackSort_cps BZP AC RT AF (rc_stack_malloc_6 RT RC) SSH (rc_stack_free_6 RT RC) AF_DRV) as FS.
    pose proof (@B0_bs_L2t.blockSort_cps BZP AC RT AF (rc_stack_malloc_7 RT RC) SSH (rc_stack_free_7 RT RC) FS AF_PRIM) as BS.
    pose proof (@B0_cb_L2t.compressBlock_cps BZP AC RT AF (rc_stack_malloc_3 RT RC) SSH BS SM AF_PRIM) as CB.
    pose proof (@B0_hc_L2t.handle_compress_cps BZP AC RT AF (@HCXB BZP) cb_facts CB AF_DRV AF_PRIM (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_globals.TwinB__.af_acc_crc RT AF)) as HC.
    exact (@B0_bzc_L2.bzCompress_cps BZP AC RT AF AF_PRIM (@HCXB BZP) cb_facts HC).
  - intros BZP AC. exact (@B0_end_L2.bzCompressEnd_cps BZP AC RT AF (rc_free RT RC)).
  - exact ACL.
Qed.

(* [comment removed for export] *)
Theorem b2bc_cps_B0_K : HD.b2bc_cps RT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A enc_okL.
Proof. exact b2bc_cps_B0. Qed.
End Top.
