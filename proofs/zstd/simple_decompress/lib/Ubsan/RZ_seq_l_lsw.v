(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma seql_linv_switch : forall P OEND LLO LEND m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  seql_static P OEND LLO LEND 2 -> seql_linv P OEND LLO LEND 2 m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  forall m2 c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq,
  munch [(y_DCTX P + 30368, y_DCTX P + 30368 + 4); (y_SPV P - 688, y_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  rw_cells usegs m2 (y_SPV P + -688) (seql_frame P OEND c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq) ->
  rw_cells usegs m2 (y_DCTX P + 30096) (h5_vcells (y_ws P) (Z_to_bv 64 0)) ->
  seql_linv P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 m2 c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP'.
Proof.
  intros P OEND LLO LEND m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV m2 c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq MUL WML MI2 FR H5V2.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exists jpad, jseq; exact FR|]. clear FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_xinv y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  sd_static_open ST. unfold held in S18, S24, S25, S26, S27, S28, S29, S30, S32, S37, S38, S39, S40.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S37 LLL; lia| split; [clear - S28 S18 LLL; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S38 LOF; lia| split; [clear - S29 S18 LOF; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S39 LML; lia| split; [clear - S30 S18 LML; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S40; lia| split; [clear - S25 S18; lia| exact I]]]|].
  assert (XL2 : rdbl usegs m2 (DCTX + 30372) (DCTX + 95940)).
  { eapply rdbl_transport; [exact (XLIT eq_refl) | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - Hx; lia| split; [clear - S27 S18 Hx; lia| exact I]]]. }
  split; [replace (DCTX + 95908 + 32) with (DCTX + 95940) by lia; exact XL2|].
  split; [intros _; exact XL2|].
  split; [split; [exact H5V2 | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [lia| split; [clear - S27 S18; lia|exact I]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [lia| split; [clear - S27 S18; lia|exact I]]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S32; lia| split; [clear - S24 S18; lia|exact I]]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S27 S18; lia| split; [clear - S18; lia|exact I]]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.
