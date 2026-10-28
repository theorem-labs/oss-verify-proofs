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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_lbase2 RZ_seq_d_lkit2 RZ_seq_d_lbase3 seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Definition seqd_frame4 (P : sdp) (OEND LEND : Z) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (j0 jpad : list byte) (llv mlv ofs : Z) : list cell := let '(mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  [CB 8 j0; C8 (Z_to_bv 64 (PFX + 8)); C8 (Z_to_bv 64 (- (SPV - 160) - 1)); C8 (Z_to_bv 64 OEND); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DCTX + 26684)); C8 (Z_to_bv 64 0); C8 dend; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (OEND - 32)); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 1152921504606846976); C8 (Z_to_bv 64 LEND); C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (MLT + 8)); C8 p0; C8 p1; C8 p2] ++ [C8 (Z_to_bv 64 LP)] ++ [C8 (Z_to_bv 64 llv); C8 (Z_to_bv 64 mlv); C8 (Z_to_bv 64 ofs)] ++ [CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)].

Lemma seqd_frame4_merge : forall P OEND LEND (m1 : fmem) cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad llv mlv ofs,
  rw_cells usegs m1 (q_SPV P + -352) (seqd_frame4 P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad llv mlv ofs) ->
  exists jseq, rw_cells usegs m1 (q_SPV P + -352) (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq).
Proof.
  intros P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad llv mlv ofs FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_frame4 seqd_frame q_SPV] in *.
  eexists.
  rewrite (app_assoc _ [C8 (Z_to_bv 64 LP)]) in FR.
  apply rw_cells_merge in FR. cbn [cells_size csize Nat.add] in FR. exact FR.
Qed.

Lemma seqd_frame4_cells : forall P OEND LEND (m : fmem) cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad llv mlv ofs,
  rw_cells usegs m (q_SPV P + -352) (seqd_frame4 P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad llv mlv ofs) ->
  rw_cells usegs m (q_SPV P + -136) [C8 (Z_to_bv 64 LP)] /\ rw_cells usegs m (q_SPV P + -128) [C8 (Z_to_bv 64 llv); C8 (Z_to_bv 64 mlv); C8 (Z_to_bv 64 ofs)].
Proof.
  intros P OEND LEND m cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad llv mlv ofs FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_frame4 q_SPV] in FR.
  apply rw_cells_app in FR. destruct FR as (_ & REST). apply rw_cells_app in REST. destruct REST as (LPC & REST).
  apply rw_cells_app in REST. destruct REST as (SQC & _).
  cbn [cells_size csize Nat.add app] in LPC, SQC.
  match type of LPC with rw_cells _ _ ?a _ => replace a with (SPV + -136) in LPC by lia end.
  match type of SQC with rw_cells _ _ ?a _ => replace a with (SPV + -128) in SQC by lia end.
  split; [exact LPC | exact SQC].
Qed.

(* [comment removed for export] *)
Lemma seqd_linv_slow : forall P OEND LEND m0 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqd_static P OEND LEND -> seqd_linv P OEND LEND m0 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall j0 jpad llv mlv ofs OP m2 lp',
  rw_cells usegs m0 (q_SPV P + -352) (seqd_frame4 P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad llv mlv ofs) ->
  q_DST P <= OP <= OEND ->
  munch [(OP, OEND); (q_SPV P + -136, q_SPV P + -136 + 8); (q_SPV P + -352 - 192, q_SPV P + -352)] m0 m2 ->
  wmono usegs m0 m2 -> mem_inv usegs m2 ->
  stk usegs m2 (q_lo P) (q_SPV P + -352) -> stk usegs m2 (q_B0 P) (q_B1 P) ->
  rw_cells usegs m2 (q_SPV P + -128) [C8 (Z_to_bv 64 llv); C8 (Z_to_bv 64 mlv); C8 (Z_to_bv 64 ofs)] ->
  rw_cells usegs m2 (q_SPV P + -136) [C8 (Z_to_bv 64 lp')] ->
  seqd_linv P OEND LEND m2 cw bc ptr sLL sOF sML p0 p1 p2 lp'.
Proof.
  intros P OEND LEND m0 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV j0 jpad llv mlv ofs OP m2 lp' FR HOP MUL WML MI2 STK2 BUF2 SQC LPC.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XI).
  assert (FR2 : rw_cells usegs m2 (q_SPV P + -352) (seqd_frame4 P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 lp' j0 jpad llv mlv ofs)).
  { clear TLL TOF TML SQB LIT XI.
    destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_static seqd_frame4 q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *. sd_static_open ST. unfold held in *.
    apply rw_cells_app in FR. destruct FR as (PRE & REST). apply rw_cells_app in REST. destruct REST as (_ & REST).
    apply rw_cells_app in REST. destruct REST as (_ & SAV).
    cbn [cells_size csize Nat.add app] in PRE, SAV.
    apply rw_cells_app. split.
    - eapply rw_cells_transport; [exact PRE | exact MUL | exact WML |].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear - S24 S18 S1 S2 S3 S4 S5 S6 HOP; lia|]. split; [lia|]. split; [lia| exact I].
    - apply rw_cells_app. split; [cbn [cells_size csize Nat.add]; replace (SPV + -352 + Z.of_nat 216) with (SPV + -136) by lia; exact LPC|].
      apply rw_cells_app. split; [cbn [cells_size csize Nat.add]; replace (SPV + -352 + Z.of_nat 216 + Z.of_nat 8) with (SPV + -128) by lia; exact SQC|].
      eapply rw_cells_transport; [exact SAV | exact MUL | exact WML |].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear - S24 S18 S1 S2 S3 S4 S5 S6 HOP; lia|]. split; [lia|]. split; [lia| exact I]. }
  destruct (seqd_frame4_merge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR2) as (jseq & FR3). clear FR FR2 SQC LPC.
  split; [exists j0, jpad, jseq; exact FR3|]. clear FR3.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_xinv q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy in *.
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S33 S1 S2 S3 S4 S5 S6 HOP LLL; lia| split; [clear - S28 S18 LLL; lia| split; [clear - S28 S18 LLL; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S34 S1 S2 S3 S4 S5 S6 HOP LOF; lia| split; [clear - S29 S18 LOF; lia| split; [clear - S29 S18 LOF; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S35 S1 S2 S3 S4 S5 S6 HOP LML; lia| split; [clear - S30 S18 LML; lia| split; [clear - S30 S18 LML; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S31 S1 S2 S3 S4 S5 S6 HOP; lia| split; [clear - S25 S18; lia| split; [clear - S25 S18; lia|exact I]]]]|].
  split; [eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S12 S1 S2 S3 S4 S5 S6 S8 HOP Hx; lia| split; [clear - S26 S18 Hx; lia| split; [clear - S26 S18 Hx; lia|exact I]]]]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HOP; lia| split; [clear - S27 S18; lia| split; [clear - S27 S18; lia|exact I]]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HOP; lia| split; [clear - S27 S18; lia| split; [clear - S27 S18; lia|exact I]]]]|].
  split; [exact BUF2|]. split; [exact STK2|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx HOP S5; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

Lemma seqd_slow : zd_execend_stmt -> forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bb64 P OEND LEND K -> at_bb80 P OEND LEND K.
Proof.
  intros EXE P OEND LEND K ST HK CONT1. unfold at_bb80.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x25 x27 x28 x29 x30 x31 INV LF HO HL HM.
  pose proof (seqd_linv_frame P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS.
  pose proof (seqd_frame4_merge P OEND LEND) as MERGE. pose proof (seqd_frame4_cells P OEND LEND) as F4C.
  pose proof (fun m0 INV0 => seqd_linv_slow P OEND LEND m0 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV0) as SLOW.
  pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold at_bb64 in CONT1. unfold zd_execend_stmt in EXE.
  pose proof INV as ((j0 & jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_frame seqd_frame4 seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, FR, L1, L2, CONT1, TRANS, MERGE, F4C, SLOW |- *.
  sd_static_open ST.
  assert (MUL : munch [(SPV - 352, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= PFX < 2^47 /\ 4096 <= OEND < 2^47)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S9 S11; lia).
  ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold TRANS; try hold EXE; try hold MERGE; try hold F4C; try hold SLOW; try hold L2; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1dfe4] 40%nat
    [KZRange SPV 544 (2^47); KZRange OP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange PFX 4096 (2^47); KZRange OEND 4096 (2^47);
     KZWr (SPV - 352) 352]
    [(SPV - 352, 352)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in EXE; try unfold held in MERGE; try unfold held in F4C; try unfold held in SLOW; try unfold held in L2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1dfe4) _ _ _ _) => (edestruct MERGE as (jseq2 & FRM); [exact FR|];
      pose proof (TRANS _ _ _ _ _ _ _ _ _ _ _ _ _ _ MUL WMl KXMI FRM) as INV0;
      pose proof INV0 as (_ & _ & _ & _ & _ & LIT0 & XI0); cbn [seqd_xinv q_B0 q_B1 q_lo q_SPV q_LITP] in XI0, LIT0; destruct XI0 as (_ & _ & BUF0 & STK0 & _);
      edestruct F4C as (LPC & SQC); [exact FR|];
      unfold held in S12, S24, S26;
      eapply evt_cut;
      [ eapply (EXE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 (SPV + -352) lo OP OEND (SPV + -128) (SPV + -136) LP LEND llv mlv ofs PFX (bv_unsigned dend) B0 B1);
        [ exact BUF0 | lia | lia | lia | lia | exact SQC | exact LPC | lia | lia | lia | lia | unfold WILDCOPY_OVERLENGTH; lia
        | eapply rdbl_sub; [exact LIT0 | lia | unfold WILDCOPY_OVERLENGTH; lia]
        | unfold apart, WILDCOPY_OVERLENGTH; destruct S12 as [A|[A|A]]; [right; lia | left; lia | left; lia]
        | lia | lia | lia | lia
        | unfold apart; lia | unfold apart; lia | unfold apart; lia | unfold apart, WILDCOPY_OVERLENGTH; lia
        | exact STK0 | lia | lia
        | unfold off_stack; lia | unfold off_stack; lia | unfold off_stack; lia | unfold off_stack, WILDCOPY_OVERLENGTH; lia
        | clear - ALSP; destruct ALSP as [A]; lia | clear - ALSP; destruct ALSP as [A]; lia
        | exact KXMI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | symmetry; apply Z_to_bv_bv_unsigned ]
      | ];
      intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & r & lp2 & -> & MUc & WMc & MIc & STKc & BUFc & SQCc & LPCc & HR2 & RES);
      replace (ret_pc (Z_to_bv 64 0x1d440)) with (Z_to_bv 64 0x1d440) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]);
      pose proof (SLOW m0 INV0 j0 jpad llv mlv ofs OP m2 lp2 FR ltac:(lia) MUc WMc MIc STKc BUFc SQCc LPCc) as INV2;
      clear MUc WMc STKc BUFc SQCc LPCc LPC SQC LIT0 BUF0 STK0 FRM INV0 KXMI MUL WMl FR F4C;
      pose proof INV2 as ((j0' & jpad' & jseq' & FR) & _); cbn [seqd_frame q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in FR;
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold TRANS; try hold EXE; try hold MERGE; try hold SLOW; try hold L2; try hold INV2; try hold RES; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1d124] 20%nat
    [KZRange SPV 544 (2^47); KZRange r 0 18446744073709551615; KZWr (SPV - 352) 352]
    [(SPV - 352, 352)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in EXE; try unfold held in MERGE; try unfold held in SLOW; try unfold held in L2; try unfold held in INV2; try unfold held in RES; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d124) _ _ _ _) => (eapply CONT1; [exact INV2 | lia | destruct RES as [RE|(RE1 & RE2 & RE3 & RE4)]; [left; exact RE | right; split; [destruct LF0 as (_ & _ & LFR); split; [cbn [q_DST]; exact L1|]; split; [cbn [q_LITP]; lia| exact LFR] | lia]]])
      end))
      end).
Qed.
