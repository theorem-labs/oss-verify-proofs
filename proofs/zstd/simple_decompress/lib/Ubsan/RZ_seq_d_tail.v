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
Lemma seqd_frame_exit : forall P OEND LEND (m1 : fmem) cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq,
  rw_cells usegs m1 (q_SPV P + -352) (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq) ->
  exists jpre, rw_cells usegs m1 (q_SPV P + -352) (CB 248 jpre :: seqd_saved P).
Proof.
  intros P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_frame seqd_saved q_SPV] in *.
  apply (rw_cells_forget _ _ _ 30%nat 248%nat) in FR; [|reflexivity].
  cbn [skipn] in FR. set (X := cells_bytes _) in FR. clearbody X.
  pose proof FR as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (WX & _).
  exists X. eapply rw_cells_recell; [exact FR | | ].
  - cbn [cells_wf cell_wf]. split; [exact WX|]. repeat split.
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma seqd_bfa4 : forall P OEND LEND K, seqd_static P OEND LEND -> seqd_ranges P -> at_bfa4 P OEND LEND K.
Proof.
  intros P OEND LEND K ST RG. unfold at_bfa4.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 INV HR RES.
  destruct INV as ((j0 & jpad & jseq & FR) & _ & _ & _ & _ & _ & XI).
  destruct (seqd_frame_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as (jpre & FRX).
  eapply (p_exit P m1 jpre r); [exact RG | exact XI | exact FRX | exact HR | exact RES].
Qed.

Lemma seqd_tail : forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bfa4 P OEND LEND K -> (forall K', 1 <= K' < K -> at_head P OEND LEND K') -> at_exit P OEND LEND K -> at_bb64 P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT1 CONT2 CONT3. unfold at_bb64.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP r x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x26 x27 x28 x29 x30 x31 INV HR RES.
  pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold at_bfa4 in CONT1. unfold at_exit in CONT3.
  assert (CONT2' : forall K', 1 <= K' < K -> forall Ks, Ks = K' -> at_head P OEND LEND Ks) by (intros K' HK' Ks ->; apply CONT2; exact HK').
  clear CONT2. rename CONT2' into CONT2. unfold at_head in CONT2.
  pose proof INV as ((j0 & jpad & jseq & FR) & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_frame seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, FR, RES, HK, CONT1, CONT2, CONT3 |- *.
  sd_static_open ST.
  destruct RES as [RE|(LF & NE)].
  - apply zd_is_error_true_iff in RE.
    assert (RG : 1 <= K <= 98047 /\ 18446744073709551497 <= r <= 18446744073709551615) by (clear - S16 HK HR RE; lia).
    ((try hold CONT1; try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold RE; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
      kx_autoLx [0x1d6e4; 0x1d724] 40%nat
      [KZRange SPV 544 (2^47); KZRange K 1 98047; KZRange r 18446744073709551497 18446744073709551615; KZWr (SPV - 352) 352]
      [(SPV - 352, 352)];
      try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end);
      kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in RE; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
      lazymatch goal with
        | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d6e4) _ _ _ _) => (eapply CONT1 with (OP := 0); [exact INV | lia | left; apply zd_is_error_true_iff; lia])
        end).
  - destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7). cbn [q_DST q_LITP q_nbSeq] in L1, L2, L6.
    assert (RG : 1 <= K <= 98047 /\ 0 <= r <= 2^47 /\ 4096 <= OP <= 2^47 /\ 4096 <= OP + r <= 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S16 HK HR L1 NE; lia).
    ((try hold CONT1; try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold NE; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
      kx_autoLx [0x1cc14; 0x1d65c; 0x1d724] 40%nat
      [KZRange SPV 544 (2^47); KZRange K 1 98047; KZRange r 0 (2^47); KZRange OP 4096 (2^47); KZRange (OP + r) 4096 (2^47); KZWr (SPV - 352) 352]
      [(SPV - 352, 352)];
      try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end);
      kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in NE; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
      lazymatch goal with
        | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1cc14) _ _ _ _) => (eapply (CONT2 (K - 1)); [lia | lia | exact INV | unfold seqd_lfacts; cbn [q_DST q_LITP q_tLL q_tOF q_tML q_SEQ q_sq q_nbSeq]; split; [lia|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia| exact L7]])
        | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d65c) _ _ _ _) => (eapply CONT3; [exact INV | cbn [q_DST]; lia | exact L2 | lia])
        end).
Qed.
