(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit
     AZ_libc_iface AZ_libc AZ_memmove
     AZ_fserd_iface AZ_hft_iface AZ_hft_rs_iface AZ_huf_iface AZ_huf_iface3 AZ_blk_iface AZ_blk_iface2 AZ_blk_iface3 AZ_blk_iface4 AZ_blk_iface5 AZ_blk_iface6
     AZ_block_iface AZ_seq_iface AZ_frame_iface AZ_xxh_iface AZ_dframe_iface AZ_dctx_iface AZ_dctx_iface_m AZ_prod_iface AZ_copy_iface AZ_dbs_iface
     AZ_tbl AZ_hufinv
     AZ_fse_bitinit AZ_huf_bitinit AZ_huf_fastargs
     AZ_huf_dx1e AZ_huf_dx2e AZ_huf_disp AZ_huf_1x AZ_huf_wksp
     AZ_bst AZ_seqhdr AZ_alloclit AZ_offinfo AZ_safecopy2 AZ_execend AZ_execsplit AZ_declit AZ_dblock
     AZ_frame_leaf AZ_prod AZ_prod_res AZ_getcblock AZ_checkcont AZ_xxh_reset AZ_xxh_digest AZ_decodefh
     AZ_getfh AZ_findfsi AZ_finddsize AZ_dbegin AZ_dmf AZ_ddctx AZ_createdctx AZ_freedctx AZ_xxh_update
     AZ_huf_wksp4 AZ_seq_s AZ_seq_d AZ_seq_l AZ_huf_4x2 AZ_fserd AZ_huf_dx41_z AZ_bfse AZ_hft_rstats AZ_huf_dx42_ffz AZ_huf_dx42_z AZ_huf_dx41_zz AZ_hft_x2 AZ_hft_x1 AZ_hft_fdec.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Section Lib.
  Variable AI : AMallocIface.
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  (* [comment removed for export] *)
  Hypothesis SM0K : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AI fflag rng_fs k.
  Hypothesis SM1K : forall k, Z.of_nat k < 8192 -> stack_malloc_1k_stmt AI fflag rng_fs k.
  Hypothesis SM2K : forall k, Z.of_nat k < 4096 -> stack_malloc_2k_stmt AI fflag rng_fs k.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FREL : fake_release_law AI fflag.
  Hypothesis FHL : fake_heap_law AI.
  (* [comment removed for export] *)

  Lemma SM2Kn : forall k, (k < 4096)%nat -> stack_malloc_2k_stmt AI fflag rng_fs k.
  Proof. intros k Hk. apply SM2K. lia. Qed.

  Lemma FSERD : fse_read_any_stmtA AI rng_fs.                   (* [comment removed for export] *)
  Proof. exact (fse_read_any_proofA AI fflag rng_fs FFLAG FREL SM0K FHL). Qed.
  Lemma FSEDEC : fse_dec_stmtA AI rng_fs.                     (* [comment removed for export] *)
  Proof. exact (fse_dec_proofA AI fflag rng_fs FFLAG FREL SM0K FHL FSERD). Qed.
  Lemma RSTATS : huf_rstats_stmtA AI rng_fs.                  (* [comment removed for export] *)
  Proof. exact (huf_rstats_proofA AI fflag rng_fs FHL FSEDEC). Qed.
  Lemma X1 : huf_rdx1_stmtA AI rng_fs.                        (* [comment removed for export] *)
  Proof. exact (huf_rdx1_proofA AI fflag rng_fs FFLAG FREL SM0K FHL RSTATS). Qed.
  Lemma X2 : huf_rdx2_stmtA AI rng_fs.                        (* [comment removed for export] *)
  Proof. exact (huf_rdx2_proofA AI fflag rng_fs FFLAG FREL SM0K FHL RSTATS). Qed.
  Lemma BFSE : zd_buildfse_stmtA.                               (* [comment removed for export] *)
  Proof. exact zd_buildfse_proofA. Qed.
  Lemma H4X1 : huf_4x1_stmtA.                                   (* [comment removed for export] *)
  Proof. exact huf_4x1_proofC. Qed.   (* [comment removed for export] *)
  Lemma H4X2 : huf_4x2_stmtA.                                   (* [comment removed for export] *)
  Proof. exact (huf_4x2_proofA x42b_proof (x42e_fast x42b_proof)). Qed.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma H4XW : huf_4x_wksp_stmtA AI rng_fs.
  Proof. exact (huf_4x_wksp_proofA AI rng_fs FHL X1 X2 H4X1 H4X2). Qed.
  Lemma SEQS : zd_seq_split_stmtA AI rng_fs.
  Proof.
    exact (zd_seq_split_proofA AI fflag rng_fs SM2Kn FFLAG FREL FHL (zd_execend_proofA zd_safecopy2_proofA) (zd_execend_split_proofA zd_safecopy2_proofA)
             zd_memmoveZ_proofA zd_memcpyZ_proofA).
  Qed.
  Lemma SEQD : zd_seq_default_stmtA AI rng_fs.
  Proof.
    exact (zd_seq_default_proofA AI fflag rng_fs SM2Kn FFLAG FREL FHL (zd_execend_proofA zd_safecopy2_proofA) zd_memmoveZ_proofA zd_memcpyZ_proofA).
  Qed.
  Lemma SEQL : zd_seq_long_stmtA AI rng_fs.                      (* [comment removed for export] *)
  Proof.
    exact (zd_seq_long_proofA AI fflag rng_fs SM2Kn FFLAG FREL FHL (zd_execend_proofA zd_safecopy2_proofA) (zd_execend_split_proofA zd_safecopy2_proofA)
             zd_memmoveZ_proofA).
  Qed.
  (* [comment removed for export] *)
  Lemma cl_1x : huf_1x_stmtA.
  Proof. exact huf_1x_closedA. Qed.
  Lemma cl_4x : huf_4x_stmtA.
  Proof. exact (huf_4x_proofA H4X1 H4X2). Qed.
  Lemma cl_1x1_wksp : huf_1x1_wksp_stmtA AI rng_fs.
  Proof. exact (huf_1x1_wksp_proofA AI rng_fs FHL X1 huf_1x1_proofA). Qed.
  (* [comment removed for export] *)
  Lemma cl_bst : zd_buildseq_stmtA AI rng_fs.
  Proof. exact (zd_buildseq_proofA AI fflag rng_fs SM2K FFLAG FREL FHL FSERD BFSE). Qed.
  Lemma cl_seqhdr : zd_seqhdr_stmtA AI rng_fs.
  Proof. exact (zd_seqhdr_proofA AI fflag rng_fs FHL cl_bst). Qed.
  Lemma cl_declit : zd_declit_stmtA AI rng_fs.
  Proof. exact (zd_declit_proofA AI rng_fs zd_alloclit_proofA zd_memcpyZ_proofA zd_memsetZ_proofA zd_memmoveZ_proofA FHL cl_1x cl_4x cl_1x1_wksp H4XW). Qed.
  Lemma cl_dblock : zd_dblock_stmtA AI rng_fs (atbl HUFINVw).
  Proof. exact (zd_dblock_proofA AI fflag rng_fs SM0K FFLAG FREL FHL cl_declit cl_seqhdr zd_offinfo_proofA SEQD SEQS SEQL). Qed.
  (* [comment removed for export] *)
  Lemma cl_getfh : zd_getfh_stmtA AI rng_fs.
  Proof. exact (zd_getfh_proofA AI fflag rng_fs SM0K FFLAG FREL FHL). Qed.
  Lemma cl_decodefh : zd_decodefh_stmtA AI rng_fs.
  Proof. exact (zd_decodefh_proofA AI fflag rng_fs SM0K FFLAG FREL FHL cl_getfh zd_xxh_reset_proofA). Qed.
  Lemma cl_findfsi : zd_findfsi_stmtA AI rng_fs.
  Proof. exact (zd_findfsi_proofA AI fflag rng_fs SM2K FFLAG FREL FHL cl_getfh zd_getcblock_proofA). Qed.
  Lemma cl_finddsize : zd_finddsize_stmtA AI rng_fs.
  Proof. exact (zd_finddsize_proofA AI fflag rng_fs SM1K FFLAG FREL FHL cl_getfh cl_findfsi). Qed.
  Lemma cl_dbegin : zd_dbegin_stmtA.
  Proof. exact (zd_dbegin_proofA zd_memcpyZ_proofA zd_memsetZ_proofA). Qed.
  Lemma cl_xxh_update : zd_xxh_update_stmtA2.
  Proof. exact (zd_xxh_update_proofA2 zd_memcpyZ_proofA). Qed.
  Lemma cl_dmf : zd_dmf_stmtA AI rng_fs.                        (* [comment removed for export] *)
  Proof.
    exact (zd_dmf_proofA AI fflag rng_fs (atbl HUFINVw) SM2K FFLAG FREL FHL atblw_laws zd_errcode_proofA cl_dbegin zd_checkcont_proofA
             cl_decodefh zd_getcblock_proofA cl_dblock cl_xxh_update zd_xxh_digest_proofA zd_memmoveZ_proofA zd_memsetZ_proofA).
  Qed.
  Lemma cl_ddctx : zd_ddctx_stmtA AI rng_fs.
  Proof. exact (zd_ddctx_proofA AI rng_fs cl_dmf). Qed.
  Lemma cl_reserve : zd_reserve_stmtA.
  Proof. exact (zd_reserve_proofA zd_u32r_proofA). Qed.

  Theorem lib_closedA :
    zd_reserve_stmtA /\ zd_u32r_stmtA /\ zd_createdctx_stmtA AI /\ zd_ddctx_stmtA AI rng_fs /\ zd_iserror_stmtA /\
    zd_finddsize_stmtA AI rng_fs /\ zd_freedctx_stmtA AI.
  Proof.
    refine (conj cl_reserve (conj zd_u32r_proofA (conj (zd_createdctx_proofA AI) (conj cl_ddctx (conj zd_iserror_proofA
             (conj cl_finddsize (zd_freedctx_proofA AI))))))).
  Qed.
End Lib.
End CANSEC1.
