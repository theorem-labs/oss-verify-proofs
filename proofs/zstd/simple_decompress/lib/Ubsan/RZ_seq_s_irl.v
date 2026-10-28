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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Lemma seqs_irl_LL : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> ai_i3 P OEND LLO LEND LOCV -> ai_i2 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i2.
  intros m1 c0 c8 c16 c24 c40 c72 c104 c128 cw u192 u200 u208 u216 p0 p1 p2 jpad jseq bc ptr sLL x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV IB HF0.
  pose proof (seqs_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i3 in CONT. pose proof INV as INV0.
  destruct INV as (_ & PT & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  hold CONT. hold INV0. hold IB. hold HF0.
  try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold AL1. try hold AL2. try hold AL3. try hold AL4. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x1db98] 20%nat
    [KZRange SPV 592 (2^47); KZRange DCTX 4096 (2^47)]
    [].
  all: try kx_mem.
  all: unfold held in CONT, INV0, IB, HF0.
  all: (eapply CONT; [ exact INV0 | exact IB | exact HF0 ]).
Qed.

(* [comment removed for export] *)
Lemma seqs_irl_OF : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> ai_i5 P OEND LLO LEND LOCV -> ai_i4 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i4.
  intros m1 c0 c8 c16 c24 c40 c72 c104 c128 cw u208 u216 p0 p1 p2 jpad jseq bc ptr sLL sOF x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV IB HF0 HF1.
  pose proof (seqs_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i5 in CONT. pose proof INV as INV0.
  destruct INV as (_ & PT & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  hold CONT. hold INV0. hold IB. hold HF0. hold HF1.
  try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold AL1. try hold AL2. try hold AL3. try hold AL4. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x1db98] 20%nat
    [KZRange SPV 592 (2^47); KZRange DCTX 4096 (2^47)]
    [].
  all: try kx_mem.
  all: unfold held in CONT, INV0, IB, HF0, HF1.
  all: (eapply CONT; [ exact INV0 | exact IB | exact HF0 | exact HF1 ]).
Qed.

(* [comment removed for export] *)
Lemma seqs_irl_ML : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> ai_i7 P OEND LLO LEND LOCV -> ai_i6 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i6.
  intros m1 c0 c8 c16 c24 c40 c72 c104 c128 cw p0 p1 p2 jpad jseq bc ptr sLL sOF sML x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV IB HF0 HF1 HF2.
  pose proof (seqs_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seqs_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i7 in CONT.
  destruct INV as (FR & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST.
  unfold seqs_ifr in FR. cbn [app v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in FR.
  assert (RP : 4096 <= PFX < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7; lia).
  assert (MUL : munch [(SPV - 384, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  hold CONT. hold TRANS. hold IB. hold HF0. hold HF1. hold HF2.
  try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold AL1. try hold AL2. try hold AL3. try hold AL4. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x1ada0] 40%nat
    [KZRange SPV 592 (2^47); KZRange PFX 4096 (2^47); KZWr (SPV - 384) 384]
    [(SPV - 384, 384)].
  all: kx_mem.
  all: unfold held in CONT, TRANS, IB, HF0, HF1, HF2.
  all: lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ (Z_to_bv 64 ?a7) _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?a18) _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    replace (Z_to_bv 64 a7) with (Z_to_bv 64 (2^60)) by (apply Z_to_bv_eqm; reflexivity);
    replace (Z_to_bv 64 a18) with (Z_to_bv 64 (-17)) by (apply Z_to_bv_eqm; reflexivity) end.
  all: eapply (CONT _ c0 c8 c40 c104 c128 cw p0 p1 p2 jpad jseq bc ptr sLL sOF sML);
    [ eapply seqs_iinv_eq; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | ] | exact IB | exact HF0 | exact HF1 | exact HF2 ].
  all: unfold seqs_ifr; cbn [app v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws].
  all: repeat match goal with
    | |- ?x = ?x => reflexivity
    | |- cons _ _ = cons _ _ => apply f_equal2
    | |- C8 _ = C8 _ => apply f_equal
    end.
  all: try reflexivity.
  all: lazymatch goal with |- Z_to_bv 64 ?a = Z_to_bv 64 ?b => rewrite <- (Z_to_bv_mod64 a), <- (Z_to_bv_mod64 b); f_equal end.
  all: try unfold two64.
  all: repeat match goal with
    | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
    | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
    end.
  all: try (simpl Z.land); try (simpl Z.lxor).
  all: lia.
Qed.
