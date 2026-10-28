(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RF_fse_iface_m RF_fse_h_malloc.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_libc_iface RZ_frame_iface RZ_block_iface RZ_dframe_iface RZ_dctx_iface RZ_dctx_iface_m RZ_prod_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_frame_leaf RZ_getfh RZ_findfsi RZ_finddsize RZ_xxh_digest RZ_xxh_reset RZ_xxh_update
  RZ_dbegin RZ_dmf RZ_ddctx RZ_prod RZ_createdctx RZ_freedctx RZ_harness.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Startup_B F_memmove.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma zd_memsetZ_proof : zd_memsetZ_stmt.
Proof. exact Startup_B.rmemset_specZ. Qed.
Lemma zd_memcpyZ_proof : zd_memcpyZ_stmt.
Proof. exact Startup_B.rmemcpy_specZ. Qed.
Lemma zd_memmoveZ_proof : zd_memmoveZ_stmt.
Proof.
  unfold zd_memmoveZ_stmt. intros D S n ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ST RD N0 S0 D0 SN DN MI -> -> ->.
  eapply evt_mono.
  - eapply (F_memmove.memmove_reg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m D S n D (D + n) S (S + n));
      [exact ST | exact RD | repeat split; lia | exact MI | reflexivity | reflexivity | reflexivity].
  - intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & _).
    unfold zd_memmoveZ_post. do 14 eexists. exists m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'| exact ST'].
Qed.

Section CANSEC1. Context {rc : runConstT}.

Theorem zd_fuzz_one_closed : forall TBL : tbl_pred, tbl_laws TBL -> zd_dblock_stmt TBL ->
  zd_memsetZ_stmt -> zd_memcpyZ_stmt -> zd_memmoveZ_stmt ->
  rmalloc_stmt -> rfree_stmt ->
  fuzz_one_stmt.
Proof.
  intros TBL TBLL DBLOCK MEMSET MEMCPY MEMMOVE MALLOC FREE.
  pose proof zd_getfh_proof as GETFH.
  pose proof zd_getcblock_proof as GETCB.
  pose proof (zd_findfsi_proof GETFH GETCB) as FINDFSI.
  pose proof (zd_finddsize_proof GETFH FINDFSI) as FINDDSIZE.
  pose proof (zd_xxh_reset_proof MEMSET) as XXHRESET.
  pose proof (zd_xxh_update_proof MEMCPY) as XXHUPD.
  pose proof (zd_dmf_proof TBL TBLL DBLOCK zd_dbegin_proof zd_checkcont_proof GETFH XXHRESET GETCB zd_errcode_proof XXHUPD zd_xxh_digest_proof MEMMOVE MEMSET) as DMF.
  pose proof (zd_ddctx_proof DMF) as DDCTX.
  pose proof (fuzz_malloc_proof MALLOC) as FMALLOC.
  apply (fuzz_one_proof (prod_create_proof FMALLOC) (zd_reserve_proof zd_u32r_proof) (zd_createdctx_proof MALLOC) zd_u32r_proof FMALLOC DDCTX
           zd_iserror_proof FINDDSIZE FREE rfree_null_spec (prod_free_proof FREE) (zd_freedctx_proof FREE)).
Qed.


(* [comment removed for export] *)
Theorem zd_fuzz_one_client : forall TBL : tbl_pred, tbl_laws TBL -> zd_dblock_stmt TBL -> rmalloc_stmt -> rfree_stmt -> fuzz_one_stmt.
Proof.
  intros TBL TBLL DBLOCK MALLOC FREE.
  exact (zd_fuzz_one_closed TBL TBLL DBLOCK zd_memsetZ_proof zd_memcpyZ_proof zd_memmoveZ_proof MALLOC FREE).
Qed.

End CANSEC1.
