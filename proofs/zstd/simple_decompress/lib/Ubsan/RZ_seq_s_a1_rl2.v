(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_a1_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma a1_reload2 : forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 LEND ->
  a1_exec P OEND LLO LEND LOCV K -> a1_brk P OEND LLO LEND LOCV K -> a1_upd P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK HLBE CONT CONTK. unfold a1_upd.
  intros m1 c0 c8 c40 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x29 x30 x31 INV LF HO HLV HMV.
  pose proof (seqs_linv_frame P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold a1_exec in CONT. unfold a1_brk in CONTK.
  pose proof (seqs_linv_lbe P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP LEND INV HLBE) as LBK.
  destruct INV as ((jpad & jseq & FR) & _ & _ & _ & SQB & _).
  destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_frame seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En.
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  assert (MUL : munch [(SPV - 384, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RS : 0 <= bc <= 9900000) by (clear - L6 HK S16; lia).
  assert (DJ : SPV - 384 + 384 <= SEQ \/ SEQ + n <= SPV - 384) by (unfold held in S25; clear - S25 S18; lia).
  assert (RGL : 4096 <= DCTX < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 0 <= llv <= 262143 /\ 1 <= K <= 98047) by (clear - L2 S8 S9 S11 S16 S19 S20 HLV HK; lia). assert (DJD : SPV - 384 + 384 <= DCTX + 30360 \/ DCTX + 30360 + 8 <= SPV - 384) by (unfold held in S27; clear - S27 S18; lia).
  assert (CASES : 65 <= bc \/ (bc <= 64 /\ ptr = SEQ) \/ (bc <= 64 /\ 8 <= n /\ SEQ + 8 <= ptr <= SEQ + n - 8) \/
                  (bc <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8)).
  { unfold bit_ok in L7. clear - L7. destruct (Z_le_gt_dec bc 64) as [B|B]; [|left; lia]. destruct (L7 B) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec (SEQ + 8) ptr); [right; right; left; lia|]. destruct (Z.eq_dec ptr SEQ); [right; left; lia| right; right; right; lia]. }
  clear L7.
  destruct CASES as [C|[C|[C|C]]].
  - (* [comment removed for export] *)
    try hold TRANS. try hold CONT. try hold CONTK. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold HO. try hold HLV. try hold HMV. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b23c; 0x1ba28; 0x1ca64] 120%nat
    [KZRange SPV 592 (2^47); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
     KZRange K 1 98047; KZRange DCTX 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange llv 0 262143; KZWord (DCTX + 30360) 8 LEND; KZDisj (SPV - 384) 384 (DCTX + 30360) 8; KZRange n 1 (2^47); KZRange bc 65 9900000;
     KZWr (SPV - 384) 384; KZDisj (SPV - 384) 384 SEQ n]
    [(SEQ, n); (SPV - 384, 384)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end).
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in CONTK; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in HO; try unfold held in HLV; try unfold held in HMV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1b23c) _ _ _ _) => (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia | lia ])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ba28) _ _ _ _) => (eapply CONTK;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2). subst ptr.
    try hold TRANS. try hold CONT. try hold CONTK. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold HO. try hold HLV. try hold HMV. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b23c; 0x1ba28; 0x1ca64] 120%nat
    [KZRange SPV 592 (2^47); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
     KZRange K 1 98047; KZRange DCTX 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange llv 0 262143; KZWord (DCTX + 30360) 8 LEND; KZDisj (SPV - 384) 384 (DCTX + 30360) 8; KZRange n 1 (2^47); KZRange bc 0 64;
     KZWr (SPV - 384) 384; KZDisj (SPV - 384) 384 SEQ n]
    [(SEQ, n); (SPV - 384, 384)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end).
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in CONTK; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in HO; try unfold held in HLV; try unfold held in HMV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1b23c) _ _ _ _) => (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia | lia ])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ba28) _ _ _ _) => (eapply CONTK;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2 & C3).
    assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
      by (exists (bc / 8), (bc mod 8), (ptr - SEQ); clear - C1 C3 RS; lia).
    destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
    try hold TRANS. try hold CONT. try hold CONTK. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold HO. try hold HLV. try hold HMV. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b23c; 0x1ba28; 0x1ca64] 120%nat
    [KZRange SPV 592 (2^47); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
     KZRange K 1 98047; KZRange DCTX 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange llv 0 262143; KZWord (DCTX + 30360) 8 LEND; KZDisj (SPV - 384) 384 (DCTX + 30360) 8; KZRange n 16 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 384) 384; KZDisj (SPV - 384) 384 SEQ n]
    [(SEQ, n); (SPV - 384, 384)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end).
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in CONTK; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in HO; try unfold held in HLV; try unfold held in HMV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1b23c) _ _ _ _) => (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia | lia ])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ba28) _ _ _ _) => (eapply CONTK;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2 & C3 & C4).
    assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n)
      by (exists (bc / 8), (bc mod 8), (ptr - SEQ); clear - C1 C3 C4 RS; lia).
    destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
    destruct (Z_le_gt_dec q d) as [QD|QD].
    + try hold TRANS. try hold CONT. try hold CONTK. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold HO. try hold HLV. try hold HMV. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoLx [0x1b23c; 0x1ba28; 0x1ca64] 120%nat
    [KZRange SPV 592 (2^47); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
     KZRange K 1 98047; KZRange DCTX 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange llv 0 262143; KZWord (DCTX + 30360) 8 LEND; KZDisj (SPV - 384) 384 (DCTX + 30360) 8; KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 384) 384; KZDisj (SPV - 384) 384 SEQ n]
    [(SEQ, n); (SPV - 384, 384)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end).
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in CONTK; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in HO; try unfold held in HLV; try unfold held in HMV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1b23c) _ _ _ _) => (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia | lia ])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ba28) _ _ _ _) => (eapply CONTK;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia ])
      end.

    + try hold TRANS. try hold CONT. try hold CONTK. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold HO. try hold HLV. try hold HMV. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoLx [0x1b23c; 0x1ba28; 0x1ca64] 120%nat
    [KZRange SPV 592 (2^47); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
     KZRange K 1 98047; KZRange DCTX 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange llv 0 262143; KZWord (DCTX + 30360) 8 LEND; KZDisj (SPV - 384) 384 (DCTX + 30360) 8; KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
     KZWr (SPV - 384) 384; KZDisj (SPV - 384) 384 SEQ n]
    [(SEQ, n); (SPV - 384, 384)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end).
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in CONTK; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in HO; try unfold held in HLV; try unfold held in HMV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1b23c) _ _ _ _) => (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia | lia ])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ba28) _ _ _ _) => (eapply CONTK;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia ])
      end.

Qed.
