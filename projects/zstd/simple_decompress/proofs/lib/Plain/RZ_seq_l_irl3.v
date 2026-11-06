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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Lemma seql_irl_ML : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> ai_i7 P OEND LLO LEND LOCV -> ai_i6 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i6.
  intros m1 p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c240 w_c248 jpad jseq rl rm ro cw bc ptr sLL sOF sML x1 x7 x12 x16 x21 x22 x23 x25 x26 x27 x30 x31 INV IB  HF0 HF1 HF2.
  pose proof (seql_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seql_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i7 in CONT. pose proof INV as INV0.
  destruct INV as (FR & _ & _ & _ & _ & SQB & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  sd_static_open ST.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En.
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  assert (ED : exists d, ptr = SEQ + d) by (exists (ptr - SEQ); lia). destruct ED as (d & ->).
  assert (MUL : munch [(SPV - 608, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 608 + 608 <= SEQ \/ SEQ + n <= SPV - 608) by (unfold held in S25; clear - S25 S18; lia).
  assert (CASES : 65 <= bc \/ (bc <= 64 /\ d = 0) \/ (bc <= 64 /\ 8 <= d /\ d + 8 <= n) \/ (bc <= 64 /\ 1 <= d <= 7 /\ d + 8 <= n)).
  { unfold bit_ok in IB2. clear - IB2. destruct (Z_le_gt_dec bc 64) as [B|B]; [|left; lia]. destruct (IB2 B) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec 8 d); [right; right; left; lia|]. destruct (Z.eq_dec d 0); [right; left; lia| right; right; right; lia]. }
  clear IB2.
  destruct CASES as [C|[C|[C|C]]].
  - try hold TRANS. try hold CONT. try hold INV0. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold HF2. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x178f8] 120%nat
    [KZRange SPV 816 (2^47); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange n 1 (2^47); KZRange bc 65 100;
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 SEQ n]
    [(SEQ, n); (SPV - 608, 608)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in INV0; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | exact INV0 ] | (split; [lia | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 | exact HF2 ]).

  - destruct C as (C1 & C2). subst d. replace (SEQ + 0) with SEQ in * by lia.
    try hold TRANS. try hold CONT. try hold INV0. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold HF2. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x178f8] 120%nat
    [KZRange SPV 816 (2^47); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange n 1 (2^47); KZRange bc 0 64;
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 SEQ n]
    [(SEQ, n); (SPV - 608, 608)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in INV0; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | exact INV0 ] | (split; [lia | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 | exact HF2 ]).

  - destruct C as (C1 & C2 & C3).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - C1 IB1; lia).
    destruct QR as (q & r & -> & Q1 & Q2).
    try hold TRANS. try hold CONT. try hold INV0. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold HF2. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x178f8] 120%nat
    [KZRange SPV 816 (2^47); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange n 16 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 SEQ n]
    [(SEQ, n); (SPV - 608, 608)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in INV0; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | exact INV0 ] | (split; [lia | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 | exact HF2 ]).

  - destruct C as (C1 & C2 & C3).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - C1 IB1; lia).
    destruct QR as (q & r & -> & Q1 & Q2).
    destruct (Z_le_gt_dec q d) as [QD|QD].
    + try hold TRANS. try hold CONT. try hold INV0. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold HF2. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoLx [0x178f8] 120%nat
    [KZRange SPV 816 (2^47); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 SEQ n]
    [(SEQ, n); (SPV - 608, 608)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in INV0; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | exact INV0 ] | (split; [lia | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 | exact HF2 ]).

    + try hold TRANS. try hold CONT. try hold INV0. try hold En. try hold Esqb. try hold HF0. try hold HF1. try hold HF2. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoLx [0x178f8] 120%nat
    [KZRange SPV 816 (2^47); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 SEQ n]
    [(SEQ, n); (SPV - 608, 608)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in INV0; try unfold held in En; try unfold held in Esqb; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | exact INV0 ] | (split; [lia | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]) | exact HF0 | exact HF1 | exact HF2 ]).

Qed.
