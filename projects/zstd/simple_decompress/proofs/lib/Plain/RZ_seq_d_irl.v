(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Lemma seqd_irl_LL : forall P OEND LEND, seqd_static P OEND LEND -> ai_538 P OEND LEND -> ai_43c P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_43c.
  intros m1 p0 p1 p2 j0 jpad jseq j_c16 j_c48 j_cbc j_c104 j_c112 j_c120 j_c128 j_c136 cw bc ptr d sLL x1 x6 x7 x14 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 INV IB HPD HF0.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold ai_538 in CONT.
  destruct INV as (FR & _ & _ & _ & _ & SQB & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En.
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  subst ptr.
  assert (MUL : munch [(SPV - 304, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 304 + 304 <= SEQ \/ SEQ + n <= SPV - 304) by (unfold held in S25; clear - S25 S18; lia).
  assert (CASES : 65 <= bc \/ (bc <= 64 /\ d = 0) \/ (bc <= 64 /\ 8 <= d /\ d + 8 <= n) \/ (bc <= 64 /\ 1 <= d <= 7 /\ d + 8 <= n)).
  { unfold bit_ok in IB2. clear - IB2. destruct (Z_le_gt_dec bc 64) as [B|B]; [|left; lia]. destruct (IB2 B) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec 8 d); [right; right; left; lia|]. destruct (Z.eq_dec d 0); [right; left; lia| right; right; right; lia]. }
  clear IB2.
  destruct CASES as [C|[C|[C|C]]].
  - try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b604] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange bc 65 100;
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 ]).

  - destruct C as (C1 & C2). subst d. replace (SEQ + 0) with SEQ in * by lia.
    try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b604] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange bc 0 64;
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 ]).

  - destruct C as (C1 & C2 & C3).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - C1 IB1; lia).
    destruct QR as (q & r & -> & Q1 & Q2).
    try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b604] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 ]).

  - destruct C as (C1 & C2 & C3).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - C1 IB1; lia).
    destruct QR as (q & r & -> & Q1 & Q2).
    destruct (Z_le_gt_dec q d) as [QD|QD].
    + try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoLx [0x1b604] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 ]).

    + try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoLx [0x1b604] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 ]).

Qed.

(* [comment removed for export] *)
Lemma seqd_irl_OF : forall P OEND LEND, seqd_static P OEND LEND -> ai_66c P OEND LEND -> ai_56c P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_56c.
  intros m1 p0 p1 p2 j0 jpad jseq j_c16 j_c48 j_cbc j_c120 j_c128 j_c136 cw bc ptr sLL sOF x1 x6 x7 x17 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 INV IB  HF0 HF1.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold ai_66c in CONT.
  destruct INV as (FR & _ & _ & _ & _ & SQB & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En.
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  assert (ED : exists d, ptr = SEQ + d) by (exists (ptr - SEQ); lia). destruct ED as (d & ->).
  assert (MUL : munch [(SPV - 304, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 304 + 304 <= SEQ \/ SEQ + n <= SPV - 304) by (unfold held in S25; clear - S25 S18; lia).
  assert (CASES : 65 <= bc \/ (bc <= 64 /\ d = 0) \/ (bc <= 64 /\ 8 <= d /\ d + 8 <= n) \/ (bc <= 64 /\ 1 <= d <= 7 /\ d + 8 <= n)).
  { unfold bit_ok in IB2. clear - IB2. destruct (Z_le_gt_dec bc 64) as [B|B]; [|left; lia]. destruct (IB2 B) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec 8 d); [right; right; left; lia|]. destruct (Z.eq_dec d 0); [right; left; lia| right; right; right; lia]. }
  clear IB2.
  destruct CASES as [C|[C|[C|C]]].
  - try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b738] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange bc 65 100;
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 ]).

  - destruct C as (C1 & C2). subst d. replace (SEQ + 0) with SEQ in * by lia.
    try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b738] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange bc 0 64;
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 ]).

  - destruct C as (C1 & C2 & C3).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - C1 IB1; lia).
    destruct QR as (q & r & -> & Q1 & Q2).
    try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b738] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 ]).

  - destruct C as (C1 & C2 & C3).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - C1 IB1; lia).
    destruct QR as (q & r & -> & Q1 & Q2).
    destruct (Z_le_gt_dec q d) as [QD|QD].
    + try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoLx [0x1b738] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 ]).

    + try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoLx [0x1b738] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 ]).

Qed.

(* [comment removed for export] *)
Lemma seqd_irl_ML : forall P OEND LEND, seqd_static P OEND LEND -> ai_7ac P OEND LEND -> ai_6a8 P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_6a8.
  intros m1 p0 p1 p2 j0 jpad jseq j_c48 j_c136 cw bc ptr sLL sOF sML x1 x5 x6 x7 x12 x15 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 INV IB  HF0 HF1 HF2.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold ai_7ac in CONT.
  destruct INV as (FR & _ & _ & _ & _ & SQB & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En.
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  assert (ED : exists d, ptr = SEQ + d) by (exists (ptr - SEQ); lia). destruct ED as (d & ->).
  assert (MUL : munch [(SPV - 304, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 304 + 304 <= SEQ \/ SEQ + n <= SPV - 304) by (unfold held in S25; clear - S25 S18; lia).
  assert (CASES : 65 <= bc \/ (bc <= 64 /\ d = 0) \/ (bc <= 64 /\ 8 <= d /\ d + 8 <= n) \/ (bc <= 64 /\ 1 <= d <= 7 /\ d + 8 <= n)).
  { unfold bit_ok in IB2. clear - IB2. destruct (Z_le_gt_dec bc 64) as [B|B]; [|left; lia]. destruct (IB2 B) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec 8 d); [right; right; left; lia|]. destruct (Z.eq_dec d 0); [right; left; lia| right; right; right; lia]. }
  clear IB2.
  destruct CASES as [C|[C|[C|C]]].
  - try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold HF2. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b878] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange bc 65 100;
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 | exact HF2 ]).

  - destruct C as (C1 & C2). subst d. replace (SEQ + 0) with SEQ in * by lia.
    try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold HF2. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b878] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange bc 0 64;
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 | exact HF2 ]).

  - destruct C as (C1 & C2 & C3).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - C1 IB1; lia).
    destruct QR as (q & r & -> & Q1 & Q2).
    try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold HF2. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b878] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 | exact HF2 ]).

  - destruct C as (C1 & C2 & C3).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - C1 IB1; lia).
    destruct QR as (q & r & -> & Q1 & Q2).
    destruct (Z_le_gt_dec q d) as [QD|QD].
    + try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold HF2. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoLx [0x1b878] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 | exact HF2 ]).

    + try hold TRANS. try hold CONT. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold HF2. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoLx [0x1b878] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; kx_rd SQB).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | first [exact FR | (lazymatch type of FR with rw_cells _ ?mm ?AA ?cs => lazymatch cs with (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?v :: _) => apply (iframe_bc_blob mm AA cs v eq_refl) in FR end end; exact FR)]] | (split; [lia | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 | exact HF2 ]).

Qed.
