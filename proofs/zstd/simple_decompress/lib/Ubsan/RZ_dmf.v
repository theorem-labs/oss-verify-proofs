(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_libc_iface RZ_frame_iface RZ_block_iface RZ_dframe_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require RZ_dmf_a RZ_dmf_b RZ_dmf_c RZ_dmf_d.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem zd_dmf_proof : forall TBL : tbl_pred, tbl_laws TBL -> zd_dblock_stmt TBL ->
  zd_dbegin_stmt -> zd_checkcont_stmt -> zd_getfh_stmt -> zd_xxh_reset_stmt -> zd_getcblock_stmt -> zd_errcode_stmt ->
  zd_xxh_update_stmt -> zd_xxh_digest_stmt -> zd_memmoveZ_stmt -> zd_memsetZ_stmt ->
  zd_dmf_stmt.
Proof.
  intros TBL TBLL DBLOCK DBEGIN CHECKCONT GETFH XXHRESET GETCB ERRCODE XXHUPD XXHDIG MEMMOVE MEMSET.
  unfold zd_dmf_stmt.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP lo DCTX DST CAP SRC src size
         DA RD0 RD1 RD8 GOT SB OK N0 NLEN N40 RS0 RS1 DSK RC0 RC40 DNULL DNN RDST ST RLO LO RSP SP16
         S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS MI -> -> -> -> -> -> -> ->.
  pose proof (RZ_dmf_a.L_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SP lo DCTX DST CAP SRC src size DNN LO) as HRET.
  pose proof (RZ_dmf_a.L_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SP lo DCTX DST CAP SRC src size
                RD0 RD1 N0 NLEN RS0 RS1 RC0 RC40 DNULL DNN RDST RLO LO RSP S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS) as HEXIT.
  pose proof (RZ_dmf_a.L_result ERRCODE ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SP lo DCTX DST CAP SRC src size
                RD0 N0 NLEN RS0 RC0 RC40 DNULL DNN RLO LO S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS) as HRES.
  pose proof (RZ_dmf_b.L_errx ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SP lo DCTX DST CAP SRC src size HRES) as HERRX.
  pose proof (RZ_dmf_b.L_errx2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SP lo DCTX DST CAP SRC src size HRES) as HERRX2.
  pose proof (RZ_dmf_b.L_fend TBL TBLL XXHDIG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SP lo DCTX DST CAP SRC src size
                RD0 RD1 RD8 OK N0 NLEN N40 RS0 RS1 RC0 RC40 DNULL DNN RDST RLO LO RSP S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS HRES) as HFEND.
  eapply RZ_dmf_d.dmf_body; try eassumption.
  eapply RZ_dmf_c.L_blocks; eassumption.
Qed.

