(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_ibase AZ_seq_s_iat.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac sqs_blob_seg H a b :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn a cs) in
    let mid := eval cbn [firstn skipn Nat.sub] in (firstn (b - a) (skipn a cs)) in
    let post := eval cbn [skipn] in (skipn b cs) in
    change (rw_cells sg mm A (pre ++ mid ++ post)) in H;
    apply (rw_cells_merge sg mm A pre mid post) in H;
    cbn [app cells_size csize Nat.add length] in H
  end.

Section CANSEC1. Context {rc : runConstT}.

Lemma sqs_iasan_now : forall P OEND LLO LEND LOCV m1 fr ff,
  sqs_static P OEND LLO LEND LOCV -> sqs_iinv P OEND LLO LEND LOCV m1 fr ff -> sqs_asan P m1.
Proof.
  intros P OEND LLO LEND LOCV m1 fr ff ST INV.
  destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XI).
  eapply (sqs_asan_transport P OEND LLO LEND LOCV m1 ST);
    destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1];
    cbn [sqs_xinv sqs_Wb v_m] in *; destruct XI as (_ & _ & _ & _ & _ & _ & _ & MU & WM & _); [exact MU | exact WM].
Qed.

(* [comment removed for export] *)
Lemma sqs_ibm_asan : forall P OEND LLO LEND LOCV m1 fr ff,
  sqs_static P OEND LLO LEND LOCV -> sqs_iinv P OEND LLO LEND LOCV m1 fr ff ->
  unpoisoned m1 0x22180 (0x22180 + 128) /\ rng (v_RNG P) 0x22180 128 /\ rng (v_RNG P) (shad 0x22180) (shspan 0x22180 128).
Proof.
  intros P OEND LLO LEND LOCV m1 fr ff ST INV.
  pose proof (sqs_iasan_now P OEND LLO LEND LOCV m1 fr ff ST INV) as AS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_asan v_RNG] in *. destruct AS as (_ & _ & _ & _ & ACL & _).
  assert (A : aro RNG m1 0x22180 128) by aro_cl ACL.
  destruct A as (U & R1 & R2). split; [exact U | split; [exact R1 | exact R2]].
Qed.

(* [comment removed for export] *)
Lemma sqs_itbl_asan : forall P OEND LLO LEND LOCV m1 fr ff,
  sqs_static P OEND LLO LEND LOCV -> sqs_iinv P OEND LLO LEND LOCV m1 fr ff ->
  aro (v_RNG P) m1 (v_LLT P) (8 * (1 + 2 ^ st_log (v_tLL P))) /\ aro (v_RNG P) m1 (v_OFT P) (8 * (1 + 2 ^ st_log (v_tOF P))) /\
  aro (v_RNG P) m1 (v_MLT P) (8 * (1 + 2 ^ st_log (v_tML P))).
Proof.
  intros P OEND LLO LEND LOCV m1 fr ff ST INV.
  pose proof (sqs_iasan_now P OEND LLO LEND LOCV m1 fr ff ST INV) as AS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_asan v_RNG v_LLT v_OFT v_MLT v_tLL v_tOF v_tML] in *. destruct AS as (_ & _ & _ & ATB & _).
  sd_static_open ST. apply ATB. clear - S16. lia.
Qed.

(* [comment removed for export] *)
Lemma sqs_itbl_logs : forall P OEND LLO LEND LOCV m1 fr ff,
  sqs_static P OEND LLO LEND LOCV -> sqs_iinv P OEND LLO LEND LOCV m1 fr ff ->
  rdn bsegs m1 (wa (v_LLT P + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (st_log (v_tLL P)))) /\
  rdn bsegs m1 (wa (v_OFT P + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (st_log (v_tOF P)))) /\
  rdn bsegs m1 (wa (v_MLT P + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (st_log (v_tML P)))) /\
  0 <= st_log (v_tLL P) <= 9 /\ 0 <= st_log (v_tOF P) <= 9 /\ 0 <= st_log (v_tML P) <= 9.
Proof.
  intros P OEND LLO LEND LOCV m1 fr ff ST INV.
  destruct INV as (_ & _ & _ & TLL & TOF & TML & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_LLT v_OFT v_MLT v_tLL v_tOF v_tML] in *. sd_static_open ST.
  split; [exact (seq_rdn_log bsegs m1 LLT K_LL tLL TLL OKLL)|]. split; [exact (seq_rdn_log bsegs m1 OFT K_OF tOF TOF OKOF)|].
  split; [exact (seq_rdn_log bsegs m1 MLT K_ML tML TML OKML)|].
  split; [exact (seq_tl_range K_LL tLL OKLL)|]. split; [exact (seq_tl_range K_OF tOF OKOF)| exact (seq_tl_range K_ML tML OKML)].
Qed.

(* [comment removed for export] *)
Lemma sqs_cb24_words : forall (m1 : amem) A pre j post,
  rw_cells bsegs m1 A (pre ++ CB 24 j :: post) -> exists w1 w2 w3, rw_cells bsegs m1 A (pre ++ C8 w1 :: C8 w2 :: C8 w3 :: post).
Proof.
  intros m1 A pre j post H.
  apply (rw_cells_split_CB bsegs m1 A pre 24 j post [8; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
destruct (cb8_as_c8 bsegs m1 A pre _ _ H) as [w1 H1].
change (rw_cells bsegs m1 A (pre ++ [C8 w1] ++ CB 8 (firstn 8 (skipn 8 j)) :: CB 8 (firstn 8 (skipn 8 (skipn 8 j))) :: post)) in H1.
rewrite app_assoc in H1.
destruct (cb8_as_c8 bsegs m1 A (pre ++ [C8 w1]) _ _ H1) as [w2 H2].
change (rw_cells bsegs m1 A ((pre ++ [C8 w1]) ++ [C8 w2] ++ CB 8 (firstn 8 (skipn 8 (skipn 8 j))) :: post)) in H2.
rewrite app_assoc in H2.
destruct (cb8_as_c8 bsegs m1 A ((pre ++ [C8 w1]) ++ [C8 w2]) _ _ H2) as [w3 H3].
exists w1, w2, w3. rewrite <- !app_assoc in H3. exact H3.
Qed.

(* [comment removed for export] *)
Lemma sqs_cb16_words : forall (m1 : amem) A pre j post,
  rw_cells bsegs m1 A (pre ++ CB 16 j :: post) -> exists w1 w2, rw_cells bsegs m1 A (pre ++ C8 w1 :: C8 w2 :: post).
Proof.
  intros m1 A pre j post H.
  apply (rw_cells_split_CB bsegs m1 A pre 16 j post [8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  destruct (cb8_as_c8 bsegs m1 A pre _ _ H) as [w1 H1].
  change (rw_cells bsegs m1 A (pre ++ [C8 w1] ++ CB 8 (firstn 8 (skipn 8 j)) :: post)) in H1. rewrite app_assoc in H1.
  destruct (cb8_as_c8 bsegs m1 A (pre ++ [C8 w1]) _ _ H1) as [w2 H2].
  exists w1, w2. rewrite <- !app_assoc in H2. exact H2.
Qed.

(* [comment removed for export] *)
Lemma sqs_cbst48 : forall (m1 : amem) A pre j post,
  rw_cells bsegs m1 A (pre ++ CB 48 j :: post) -> exists w1 w2 j', rw_cells bsegs m1 A (pre ++ C8 w1 :: C8 w2 :: CB 32 j' :: post).
Proof.
  intros m1 A pre j post H.
  apply (rw_cells_split_CB bsegs m1 A pre 48 j post [8; 8; 32]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  destruct (cb8_as_c8 bsegs m1 A pre _ _ H) as [w1 H1].
  change (rw_cells bsegs m1 A (pre ++ [C8 w1] ++ CB 8 (firstn 8 (skipn 8 j)) :: CB 32 (firstn 32 (skipn 8 (skipn 8 j))) :: post)) in H1. rewrite app_assoc in H1.
  destruct (cb8_as_c8 bsegs m1 A (pre ++ [C8 w1]) _ _ H1) as [w2 H2].
  exists w1, w2, (firstn 32 (skipn 8 (skipn 8 j))). rewrite <- !app_assoc in H2. exact H2.
Qed.
Lemma sqs_cbst32 : forall (m1 : amem) A pre j post,
  rw_cells bsegs m1 A (pre ++ CB 32 j :: post) -> exists w1 w2 j', rw_cells bsegs m1 A (pre ++ C8 w1 :: C8 w2 :: CB 16 j' :: post).
Proof.
  intros m1 A pre j post H.
  apply (rw_cells_split_CB bsegs m1 A pre 32 j post [8; 8; 16]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  destruct (cb8_as_c8 bsegs m1 A pre _ _ H) as [w1 H1].
  change (rw_cells bsegs m1 A (pre ++ [C8 w1] ++ CB 8 (firstn 8 (skipn 8 j)) :: CB 16 (firstn 16 (skipn 8 (skipn 8 j))) :: post)) in H1. rewrite app_assoc in H1.
  destruct (cb8_as_c8 bsegs m1 A (pre ++ [C8 w1]) _ _ H1) as [w2 H2].
  exists w1, w2, (firstn 16 (skipn 8 (skipn 8 j))). rewrite <- !app_assoc in H2. exact H2.
Qed.

(* [comment removed for export] *)
Lemma sqs_iff_ahull : forall P OEND LLO LEND LOCV m1 fr ff,
  sqs_static P OEND LLO LEND LOCV -> sqs_iinv P OEND LLO LEND LOCV m1 fr ff -> ahull (v_RNG P) m1 (v_FF P + 32) 40.
Proof.
  intros P OEND LLO LEND LOCV m1 fr ff ST INV.
  destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_xinv v_RNG v_FF] in *. sd_static_open ST. unfold held in *.
  destruct XI as (_ & _ & _ & _ & _ & _ & SHS & _).
  destruct S61 as (_ & _ & _ & _ & _ & _ & _ & FFa & FFb & FFc & ESHF & RFF & RSHF & _).
  exists FF, (FF + 256).
  split; [clear; lia|]. split; [clear; lia|]. split; [clear - FFc; Z.div_mod_to_equations; lia|]. split; [clear - FFc; Z.div_mod_to_equations; lia|].
  split; [clear - S49; lia|]. split; [unfold KEND; clear - S50 S18 S17; lia|].
  replace (shad (FF + 256) - shad FF) with 32 by (rewrite !shad_div; clear - FFc; Z.div_mod_to_equations; lia). rewrite <- ESHF.
  split; [eapply (rw_cells_wr_at bsegs m1 SHF _ 32 SHS); cbn [cells_size csize Nat.add length]; clear; lia | exact RSHF].
Qed.

End CANSEC1.
