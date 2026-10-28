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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_ibase RZ_seq_s_a1_at seqS_kit_ifse.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Lemma seqs_ifse_LL : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> ai_i2 P OEND LLO LEND LOCV -> ai_i1 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i1.
  intros m1 c0 c8 c16 c24 c40 c72 c104 c128 cw u176 u184 u192 u200 u208 u216 p0 p1 p2 jpad jseq bc ptr x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV IB.
  unfold ai_i2 in CONT.
  eapply (seqs_ifse_call P OEND LLO LEND LOCV _ m1 c0 c8 c16 c24 c40 c72 c104 c128 cw jpad jseq bc ptr [] [C8 u192; C8 u200; C8 u208; C8 u216] u176 u184 p0 p1 p2 (v_SPV P + -208) (v_LLT P) 64 _ K_LL (v_tLL P));
    [ exact ST | exact INV | cbn [cells_size csize Nat.add]; lia | left; reflexivity | reflexivity | left; split; [reflexivity | split; reflexivity]
    | exact IB | lia | apply ret_pc_even; [lia | reflexivity] | ].
  intros m2 cw2 jpad2 bc2 ptr2 st z5 z11 z12 z13 z14 z15 z16 z17 INV2 IB2 HST.
  cbn [app] in INV2.
  eapply CONT; [exact INV2 | exact IB2 | exact HST].
Qed.

(* [comment removed for export] *)
Lemma seqs_ifse_OF : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> ai_i4 P OEND LLO LEND LOCV -> ai_i3 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i3.
  intros m1 c0 c8 c16 c24 c40 c72 c104 c128 cw u192 u200 u208 u216 p0 p1 p2 jpad jseq bc ptr sLL x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV IB HF0.
  unfold ai_i4 in CONT.
  eapply (seqs_ifse_call P OEND LLO LEND LOCV _ m1 c0 c8 c16 c24 c40 c72 c104 c128 cw jpad jseq bc ptr [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (v_LLT P + 8))] [C8 u208; C8 u216] u192 u200 p0 p1 p2 (v_SPV P + -192) (v_OFT P) 73 _ K_OF (v_tOF P));
    [ exact ST | exact INV | cbn [cells_size csize Nat.add]; lia | right; left; reflexivity | reflexivity | right; left; split; [reflexivity | split; reflexivity]
    | exact IB | lia | apply ret_pc_even; [lia | reflexivity] | ].
  intros m2 cw2 jpad2 bc2 ptr2 st z5 z11 z12 z13 z14 z15 z16 z17 INV2 IB2 HST.
  cbn [app] in INV2.
  eapply CONT; [exact INV2 | exact IB2 | exact HF0 | exact HST].
Qed.

(* [comment removed for export] *)
Lemma seqs_ifse_ML : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> ai_i6 P OEND LLO LEND LOCV -> ai_i5 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i5.
  intros m1 c0 c8 c16 c24 c40 c72 c104 c128 cw u208 u216 p0 p1 p2 jpad jseq bc ptr sLL sOF x5 x6 x7 x8 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV IB HF0 HF1.
  unfold ai_i6 in CONT.
  eapply (seqs_ifse_call P OEND LLO LEND LOCV _ m1 c0 c8 c16 c24 c40 c72 c104 c128 cw jpad jseq bc ptr [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (v_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (v_OFT P + 8))] [] u208 u216 p0 p1 p2 (v_SPV P + -176) (v_MLT P) 82 _ K_ML (v_tML P));
    [ exact ST | exact INV | cbn [cells_size csize Nat.add]; lia | right; right; reflexivity | reflexivity | right; right; split; [reflexivity | split; reflexivity]
    | exact IB | lia | apply ret_pc_even; [lia | reflexivity] | ].
  intros m2 cw2 jpad2 bc2 ptr2 st z5 z11 z12 z13 z14 z15 z16 z17 INV2 IB2 HST.
  cbn [app] in INV2.
  eapply CONT; [exact INV2 | exact IB2 | exact HF0 | exact HF1 | exact HST].
Qed.

(* [comment removed for export] *)
Lemma seqs_ihead : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> LLO <= v_LITP P <= LEND ->
  a1_head P OEND LLO LEND LOCV (v_nbSeq P) -> ai_i7 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST HLP CONT. unfold ai_i7.
  intros m1 c0 c8 c40 c104 c128 cw p0 p1 p2 jpad jseq bc ptr sLL sOF sML x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 INV IB HF0 HF1 HF2.
  pose proof (seqs_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seqs_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold a1_head in CONT.
  destruct INV as (FR & _). destruct IB as (IB1 & IB2).
  unfold seqs_ifr in FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  cbn [app] in FR.
  sd_static_open ST. clear AL1 AL2 AL3 AL4.
  assert (MUL : munch [(SPV - 384, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OEND < 2^47 /\ 4096 <= MLT < 2^47 /\ 4096 <= DCTX < 2^47 /\ 4096 <= DST < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S19 S20 S23; lia).
  try hold TRANS. try hold CONT. try hold IB2. try hold HF0. try hold HF1. try hold HF2. try hold HLP. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x1ada8] 20%nat
    [KZRange SPV 592 (2^47); KZRange OEND 4096 (2^47); KZRange MLT 4096 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZWr (SPV - 384) 384]
    [(SPV - 384, 384)].
  kx_mem. (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in HLP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  eapply CONT with (LP := LITP);
    [ eapply seqs_iinv_linv; eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | cbn [seqs_frame]; repeat f_equal; lia]
    | unfold seqs_lfacts; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq v_nbSeq];
      split; [lia|]; split; [exact HLP|]; split; [exact HF0|]; split; [exact HF1|]; split; [exact HF2|]; split; [lia| exact IB2] ].
Qed.
