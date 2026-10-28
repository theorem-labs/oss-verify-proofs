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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_rkit RZ_seq_l_xat RZ_seq_l_la_at RZ_seq_l_la_at2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac la_ring_split FR :=
  lazymatch type of FR with rw_cells ?s ?mm ?A ?L =>
    let pre := eval cbv [firstn] in (firstn 46%nat L) in
    let post := eval cbv [skipn] in (skipn 47%nat L) in
    lazymatch eval cbv [skipn] in (skipn 46%nat L) with
    | CB 192 ?r :: _ => change (rw_cells s mm A (pre ++ CB 192 r :: post)) in FR
    end
  end.

Ltac la_ring_join FR k :=
  lazymatch type of FR with rw_cells ?s ?mm ?A ?L =>
    let n := eval cbv in (46 + k)%nat in
    let pre := eval cbv [firstn] in (firstn 46%nat L) in
    let mid := eval cbv [firstn skipn] in (firstn k (skipn 46%nat L)) in
    let post := eval cbv [skipn] in (skipn n L) in
    change (rw_cells s mm A (pre ++ mid ++ post)) in FR
  end.

Lemma la_store_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  (forall K', 1 <= K' < K -> la_head P OEND LLO LEND LOCV K') -> la_done P OEND LLO LEND LOCV -> la_exec P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT2 CONT3. unfold la_exec.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c176 c184 c216 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv cnt sn raddr rend x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x25 x27 x29.
  rewrite <- (Z_to_bv_bv_unsigned p0). pose proof (kx_u64_range p0) as HO. remember (bv_unsigned p0) as ofz eqn:Eofz. clear Eofz p0.
  intros INV LF HLV HMV HCNT HSN HSR HRA HRE HRING HOPD.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold la_done in CONT3.
  assert (CONT2' : forall K', 1 <= K' < K -> forall Ks, Ks = K' -> la_head P OEND LLO LEND LOCV Ks) by (intros K' HK' Ks ->; apply CONT2; exact HK').
  clear CONT2. rename CONT2' into CONT2. unfold la_head in CONT2.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, HK, HSN, HSR, HRA, HRE, HOPD, L1, L2, L6, CONT2, CONT3, TRANS |- *.
  sd_static_open ST.
  subst raddr. subst rend.
  assert (RG : 1 <= nbSeq <= 98047 /\ 1 <= Z.min nbSeq 8 <= 8 /\ 0 <= cnt <= 98046 /\ 0 <= llv <= 262143 /\ 0 <= mlv <= 262143) by (clear - S16 HK HCNT HLV HMV; lia).
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (CASES : sn = 0 \/ sn = 1 \/ sn = 2 \/ sn = 3 \/ sn = 4 \/ sn = 5 \/ sn = 6 \/ sn = 7) by (clear - HSR; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; rewrite C in *; clear C.
  all: la_ring_split FR.
  all: lazymatch type of HRING with seql_ring_ok ?k _ _ _ => lazymatch k with
    | 0 => apply (seql_ring_open_0 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
    | 1 => apply (seql_ring_open_1 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
    | 2 => apply (seql_ring_open_2 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
    | 3 => apply (seql_ring_open_3 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
    | 4 => apply (seql_ring_open_4 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
    | 5 => apply (seql_ring_open_5 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
    | 6 => apply (seql_ring_open_6 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
    | 7 => apply (seql_ring_open_7 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
    end end; cbn [app] in FR.
  all: (try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold TRANS; try hold HRING; try hold LF0; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML).
  all: kx_autoLx [0x17d38; 0x183a8] 30%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange nbSeq 1 98047; KZRange (Z.min nbSeq 8) 1 8; KZRange cnt 0 98046; KZRange llv 0 262143; KZRange mlv 0 262143; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
  all: kx_mem.
  all: (try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: lazymatch type of HRING with seql_ring_ok ?k _ _ _ =>
    pose proof (seql_ring_ok_grow k rl rm ro llv mlv ofz HRING HLV HMV HO) as HRING2;
    lazymatch k with
    | 0 => la_ring_join FR 4%nat; apply seql_ring_close_0 in FR
    | 1 => la_ring_join FR 5%nat; apply seql_ring_close_1 in FR
    | 2 => la_ring_join FR 5%nat; apply seql_ring_close_2 in FR
    | 3 => la_ring_join FR 5%nat; apply seql_ring_close_3 in FR
    | 4 => la_ring_join FR 5%nat; apply seql_ring_close_4 in FR
    | 5 => la_ring_join FR 5%nat; apply seql_ring_close_5 in FR
    | 6 => la_ring_join FR 5%nat; apply seql_ring_close_6 in FR
    | 7 => la_ring_join FR 4%nat; apply seql_ring_close_7 in FR
    end; cbn [app] in FR;
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x17d38) _ _ _ _) =>
      eapply (CONT2 (K - 1) ltac:(lia) (K - 1) eq_refl) with (sn := k + 1) (OP := OP);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seql_lfacts; cbn [y_DST y_tLL y_tOF y_tML y_SEQ y_sq y_nbSeq]; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia| exact L7]
      | lia | lia | lia | lia | reflexivity | exact HRING2 | exact HOPD ]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x183a8) _ _ _ _) =>
      eapply CONT3 with (OP := OP);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seql_lfacts; cbn [y_DST y_tLL y_tOF y_tML y_SEQ y_sq y_nbSeq]; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia| exact L7]
      | exact HOPD
      | replace (Z.min nbSeq 8) with (k + 1) by lia; exact HRING2 ]
    end end.
Qed.
