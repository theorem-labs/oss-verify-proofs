(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_huf_iface RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition seqd_iinv (P : sdp) (LEND : Z) (m1 : fmem) (fr : list cell) : Prop :=
  rw_cells usegs m1 (q_SPV P + -352) fr /\
  dctx_ptrs usegs m1 (q_DCTX P) (Z_to_bv 64 (q_LLT P)) (Z_to_bv 64 (q_MLT P)) (Z_to_bv 64 (q_OFT P)) (q_huf P) /\
  bytes_at usegs m1 (q_LLT P) (map (Z_to_bv 8) (seq_table_bytes (q_tLL P))) /\
  bytes_at usegs m1 (q_OFT P) (map (Z_to_bv 8) (seq_table_bytes (q_tOF P))) /\
  bytes_at usegs m1 (q_MLT P) (map (Z_to_bv 8) (seq_table_bytes (q_tML P))) /\
  bytes_at usegs m1 (q_SEQ P) (map (Z_to_bv 8) (q_sq P)) /\
  rdbl usegs m1 (q_LITP P) (LEND + 32) /\
  seqd_xinv P m1 (seqd_fe P).

Lemma seqd_iinv_mi : forall P LEND m1 fr, seqd_iinv P LEND m1 fr -> mem_inv usegs m1.
Proof.
  intros P LEND m1 fr (_ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_xinv] in XI. destruct XI as (_ & _ & _ & _ & _ & _ & MI). exact MI.
Qed.

(* [comment removed for export] *)
Lemma seqd_iinv_frame : forall P OEND LEND m1 fr,
  seqd_static P OEND LEND -> seqd_iinv P LEND m1 fr ->
  forall m2 fr2,
  munch [(q_SPV P - 352, q_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  rw_cells usegs m2 (q_SPV P + -352) fr2 -> seqd_iinv P LEND m2 fr2.
Proof.
  intros P OEND LEND m1 fr ST INV m2 fr2 MUL WML MI2 FR.
  destruct INV as (_ & PT & TLL & TOF & TML & SQB & LIT & XI).
  split; [exact FR|]. clear FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_xinv q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_ptrs, dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy in *.
  split; [eapply rw_cells_transport; [exact PT | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S28 S18 LLL; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S29 S18 LOF; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S30 S18 LML; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S25 S18; lia|exact I]]|].
  split; [eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S26 S18 Hx; lia|exact I]]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S24 S18; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S18; lia|exact I]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

(* [comment removed for export] *)
Lemma seqd_iinv_linv : forall P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq,
  seqd_iinv P LEND m1 (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq) -> seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP.
Proof.
  intros P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq (FR & _ & TLL & TOF & TML & SQB & LIT & XI).
  split; [exists j0, jpad, jseq; exact FR|]. repeat (split; [assumption|]). exact XI.
Qed.

(* [comment removed for export] *)
Lemma iframe_bc_blob : forall (m : fmem) A cs v, nth_error cs 8 = Some (C4 v) ->
  rw_cells usegs m A cs -> rw_cells usegs m A (firstn 8 cs ++ CB 4 (le4 v) :: skipn 9 cs).
Proof.
  intros m A cs v HN RW.
  assert (E : cs = firstn 8 cs ++ C4 v :: skipn 9 cs).
  { rewrite <- (firstn_skipn 8 cs) at 1. f_equal.
    do 8 (destruct cs as [|? cs]; [discriminate HN|]). destruct cs as [|c9 cs]; [discriminate HN|]. cbn in HN. injection HN as ->. reflexivity. }
  remember (firstn 8 cs) as pre eqn:Epre. remember (skipn 9 cs) as post eqn:Epost. clear Epre Epost HN. subst cs.
  pose proof RW as [[WF _] _]. apply cells_wf_app in WF. destruct WF as (W1 & _ & W2).
  eapply rw_cells_recell; [exact RW | |].
  - apply cells_wf_app. split; [exact W1|]. split; [apply length_le4| exact W2].
  - rewrite !cells_bytes_app. reflexivity.
Qed.

(* [comment removed for export] *)
Definition seqd_ibits (P : sdp) (B bc ptr : Z) : Prop := 0 <= bc <= B /\ bit_ok (q_SEQ P) (zlen (q_sq P)) bc ptr.

Definition seqd_ifr_hd (P : sdp) (OEND LEND : Z) (c0 c8 c16 c48 c72 c80 c88 : word) : list cell :=
  [C8 c0; C8 c8; C8 c16; C8 (Z_to_bv 64 OEND); C8 (Z_to_bv 64 (q_DST P)); C8 (Z_to_bv 64 (q_DCTX P + 26684)); C8 c48; C8 (q_dend P); C8 (Z_to_bv 64 (q_PFX P)); C8 c72; C8 c80; C8 c88; C8 (Z_to_bv 64 LEND)].

Definition seqd_ifr_tl (P : sdp) (p0 p1 p2 : word) (jseq : list byte) : list cell :=
  [C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (q_LITP P)); CB 24 jseq; CB 104 (le8 (q_s11 P) ++ le8 (q_s10 P) ++ le8 (q_s9 P) ++ le8 (q_s8 P) ++ le8 (q_s7 P) ++ le8 (q_s6 P) ++ le8 (q_s5 P) ++ le8 (q_s4 P) ++ le8 (q_s3 P) ++ le8 (q_s2 P) ++ le8 (q_s1 P) ++ le8 (q_s0 P) ++ le8 (q_ra P))].

Definition seqd_ifr (P : sdp) (OEND LEND : Z) (c0 c8 c16 c48 c72 c80 c88 : word) (bd st : list cell) (p0 p1 p2 : word) (jseq : list byte) : list cell :=
  seqd_ifr_hd P OEND LEND c0 c8 c16 c48 c72 c80 c88 ++ bd ++ st ++ seqd_ifr_tl P p0 p1 p2 jseq.

Lemma seqd_ifr_join : forall (m m' : fmem) P OEND LEND c0 c8 c16 c48 c72 c80 c88 bd st bd' st' p0 p1 p2 jseq,
  rw_cells usegs m (q_SPV P + -352) (seqd_ifr P OEND LEND c0 c8 c16 c48 c72 c80 c88 bd st p0 p1 p2 jseq) ->
  cells_size bd = 40%nat -> cells_size st = 48%nat ->
  munch [(q_SPV P - 248, q_SPV P - 160)] m m' -> wmono usegs m m' ->
  rw_cells usegs m' (q_SPV P + -248) bd' -> rw_cells usegs m' (q_SPV P + -208) st' -> cells_size bd' = 40%nat -> cells_size st' = 48%nat ->
  rw_cells usegs m' (q_SPV P + -352) (seqd_ifr P OEND LEND c0 c8 c16 c48 c72 c80 c88 bd' st' p0 p1 p2 jseq).
Proof.
  intros m m' P OEND LEND c0 c8 c16 c48 c72 c80 c88 bd st bd' st' p0 p1 p2 jseq FR SB SS MU WM BD ST SB' SS'.
  unfold seqd_ifr in *.
  assert (EH : Z.of_nat (cells_size (seqd_ifr_hd P OEND LEND c0 c8 c16 c48 c72 c80 c88)) = 104) by reflexivity.
  assert (ET : Z.of_nat (cells_size (seqd_ifr_tl P p0 p1 p2 jseq)) = 160) by reflexivity.
  apply rw_cells_app in FR as (F1 & FR). apply rw_cells_app in FR as (F2 & FR). apply rw_cells_app in FR as (F3 & F4).
  rewrite EH, SB, SS in F4. change (Z.of_nat 40) with 40 in F4. change (Z.of_nat 48) with 48 in F4.
  replace (q_SPV P + -352 + 104 + 40 + 48) with (q_SPV P + -160) in F4 by lia.
  apply rw_cells_app. split.
  - eapply rw_cells_transport; [exact F1 | exact MU | exact WM |]. rewrite EH. cbn [disjoint_from]. split; [lia | exact I].
  - rewrite EH. replace (q_SPV P + -352 + 104) with (q_SPV P + -248) by lia.
    apply rw_cells_app. split; [exact BD|]. rewrite SB'. change (Z.of_nat 40) with 40.
    replace (q_SPV P + -248 + 40) with (q_SPV P + -208) by lia.
    apply rw_cells_app. split; [exact ST|].
    rewrite SS'. change (Z.of_nat 48) with 48. replace (q_SPV P + -208 + 48) with (q_SPV P + -160) by lia.
    eapply rw_cells_transport; [exact F4 | exact MU | exact WM |]. rewrite ET. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma seqd_ifr_saved : forall P OEND LEND c0 c8 c16 c48 c72 c80 c88 bd st p0 p1 p2 jseq,
  seqd_ifr P OEND LEND c0 c8 c16 c48 c72 c80 c88 bd st p0 p1 p2 jseq =
  (seqd_ifr_hd P OEND LEND c0 c8 c16 c48 c72 c80 c88 ++ bd ++ st ++ [C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (q_LITP P)); CB 24 jseq]) ++
  [CB 104 (le8 (q_s11 P) ++ le8 (q_s10 P) ++ le8 (q_s9 P) ++ le8 (q_s8 P) ++ le8 (q_s7 P) ++ le8 (q_s6 P) ++ le8 (q_s5 P) ++ le8 (q_s4 P) ++ le8 (q_s3 P) ++ le8 (q_s2 P) ++ le8 (q_s1 P) ++ le8 (q_s0 P) ++ le8 (q_ra P))].
Proof. intros. unfold seqd_ifr, seqd_ifr_tl. rewrite <- !app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Definition ai_408 (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c48 c72 c80 c88 cw u144 u152 u160 u168 u176 u184 p0 p1 p2 : word) (jpad jseq : list byte) (bc ptr : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 (seqd_ifr P OEND LEND c0 c8 c16 c48 c72 c80 c88 (bitd_cells cw (Z_to_bv 64 bc) jpad ptr (q_SEQ P)) [C8 u144; C8 u152; C8 u160; C8 u168; C8 u176; C8 u184] p0 p1 p2 jseq) ->
  seqd_ibits P 64 bc ptr ->
  evt usegs (seqd_post P) (MS (mkR (Z_to_bv 64 0x1cbac) (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_SPV P + -160)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 (q_SPV P + -208)) (Z_to_bv 64 (q_SPV P + -248)) (Z_to_bv 64 (q_LLT P)) x13 x14 x15 x16 x17 (Z_to_bv 64 (q_nbSeq P)) x19 (Z_to_bv 64 (q_DCTX P)) x21 x22 (Z_to_bv 64 (q_PFX P)) x24 x25 x26 x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1db98) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_43c (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c48 c72 c80 c88 cw u160 u168 u176 u184 p0 p1 p2 : word) (jpad jseq : list byte) (bc ptr sLL : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 (seqd_ifr P OEND LEND c0 c8 c16 c48 c72 c80 c88 (bitd_cells cw (Z_to_bv 64 bc) jpad ptr (q_SEQ P)) [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (q_LLT P + 8)); C8 u160; C8 u168; C8 u176; C8 u184] p0 p1 p2 jseq) ->
  seqd_ibits P 73 bc ptr ->
  0 <= sLL < 2^(st_log (q_tLL P)) ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_SPV P + -160)) (Z_to_bv 64 (2^60)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (q_nbSeq P)) x19 (Z_to_bv 64 (q_DCTX P)) x21 x22 (Z_to_bv 64 (q_PFX P)) x24 x25 x26 x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1cbac) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_538 (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c48 c72 c80 c88 cw u160 u168 u176 u184 p0 p1 p2 : word) (jpad jseq : list byte) (bc ptr sLL : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 (seqd_ifr P OEND LEND c0 c8 c16 c48 c72 c80 c88 (bitd_cells cw (Z_to_bv 64 bc) jpad ptr (q_SEQ P)) [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (q_LLT P + 8)); C8 u160; C8 u168; C8 u176; C8 u184] p0 p1 p2 jseq) ->
  seqd_ibits P 73 bc ptr ->
  0 <= sLL < 2^(st_log (q_tLL P)) ->
  evt usegs (seqd_post P) (MS (mkR (Z_to_bv 64 0x1cbbc) (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_SPV P + -160)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 (q_SPV P + -192)) (Z_to_bv 64 (q_SPV P + -248)) (Z_to_bv 64 (q_OFT P)) x13 x14 x15 x16 x17 (Z_to_bv 64 (q_nbSeq P)) x19 (Z_to_bv 64 (q_DCTX P)) x21 x22 (Z_to_bv 64 (q_PFX P)) x24 x25 x26 x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1db98) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_56c (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c48 c72 c80 c88 cw u176 u184 p0 p1 p2 : word) (jpad jseq : list byte) (bc ptr sLL sOF : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 (seqd_ifr P OEND LEND c0 c8 c16 c48 c72 c80 c88 (bitd_cells cw (Z_to_bv 64 bc) jpad ptr (q_SEQ P)) [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (q_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (q_OFT P + 8)); C8 u176; C8 u184] p0 p1 p2 jseq) ->
  seqd_ibits P 82 bc ptr ->
  0 <= sLL < 2^(st_log (q_tLL P)) -> 0 <= sOF < 2^(st_log (q_tOF P)) ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_SPV P + -160)) (Z_to_bv 64 (2^60)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (q_nbSeq P)) x19 (Z_to_bv 64 (q_DCTX P)) x21 x22 (Z_to_bv 64 (q_PFX P)) x24 x25 x26 x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1cbbc) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_66c (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c48 c72 c80 c88 cw u176 u184 p0 p1 p2 : word) (jpad jseq : list byte) (bc ptr sLL sOF : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 (seqd_ifr P OEND LEND c0 c8 c16 c48 c72 c80 c88 (bitd_cells cw (Z_to_bv 64 bc) jpad ptr (q_SEQ P)) [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (q_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (q_OFT P + 8)); C8 u176; C8 u184] p0 p1 p2 jseq) ->
  seqd_ibits P 82 bc ptr ->
  0 <= sLL < 2^(st_log (q_tLL P)) -> 0 <= sOF < 2^(st_log (q_tOF P)) ->
  evt usegs (seqd_post P) (MS (mkR (Z_to_bv 64 0x1cbcc) (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_SPV P + -160)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 (q_SPV P + -176)) (Z_to_bv 64 (q_SPV P + -248)) (Z_to_bv 64 (q_MLT P)) x13 x14 x15 x16 x17 (Z_to_bv 64 (q_nbSeq P)) x19 (Z_to_bv 64 (q_DCTX P)) x21 x22 (Z_to_bv 64 (q_PFX P)) x24 x25 x26 x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1db98) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_6a8 (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c48 c72 c80 c88 cw p0 p1 p2 : word) (jpad jseq : list byte) (bc ptr sLL sOF sML : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 (seqd_ifr P OEND LEND c0 c8 c16 c48 c72 c80 c88 (bitd_cells cw (Z_to_bv 64 bc) jpad ptr (q_SEQ P)) [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (q_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (q_OFT P + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (q_MLT P + 8))] p0 p1 p2 jseq) ->
  seqd_ibits P 91 bc ptr ->
  0 <= sLL < 2^(st_log (q_tLL P)) -> 0 <= sOF < 2^(st_log (q_tOF P)) -> 0 <= sML < 2^(st_log (q_tML P)) ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_SPV P + -160)) (Z_to_bv 64 (2^60)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (q_nbSeq P)) x19 (Z_to_bv 64 (q_DCTX P)) x21 x22 (Z_to_bv 64 (q_PFX P)) x24 x25 x26 x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1cbcc) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_7ac (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (j0 jpad jseq : list byte) (x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 (q_LITP P) j0 jpad jseq) ->
  seqd_ibits P 91 bc ptr ->
  0 <= sLL < 2^(st_log (q_tLL P)) -> 0 <= sOF < 2^(st_log (q_tOF P)) -> 0 <= sML < 2^(st_log (q_tML P)) ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 (Z_to_bv 64 (q_SPV P + -160)) (Z_to_bv 64 1152921504606846976) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (q_nbSeq P)) (Z_to_bv 64 18446744073709551599) x20 x21 x22 x23 (Z_to_bv 64 (q_DST P)) x25 x26 x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1cc14) (q_fc P) None m1 (seg_rom usegs)).

