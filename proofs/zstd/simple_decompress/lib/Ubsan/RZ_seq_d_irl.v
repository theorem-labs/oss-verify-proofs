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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_huf_iface RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Lemma seqd_irl_LL : forall P OEND LEND, seqd_static P OEND LEND -> ai_538 P OEND LEND -> ai_43c P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_43c.
  intros m1 c0 c8 c16 c48 c72 c80 c88 cw u160 u168 u176 u184 p0 p1 p2 jpad jseq bc ptr sLL x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 INV IB HL.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold ai_538 in CONT. pose proof INV as INV0.
  destruct INV as (_ & PT & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  assert (RG : 544 <= SPV < 2^47 /\ 4096 <= DCTX < 2^47) by (clear - S17 S19 S20; lia).
  assert (MUL : munch [(SPV - 352, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  hold TRANS. hold CONT. hold INV0. hold IB. hold HL.
  try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S17. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML. try hold ALSP. try hold ALLL. try hold ALOF. try hold ALML.
  kx_autoLx [0x1db98] 20%nat
    [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47)]
    [].
  all: try kx_mem.
  all: unfold held in TRANS, CONT, INV0, IB, HL.
  all: (eapply CONT; [ first [ exact INV0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | assumption] ] | exact IB | exact HL ]).
Qed.

(* [comment removed for export] *)
Lemma seqd_irl_OF : forall P OEND LEND, seqd_static P OEND LEND -> ai_66c P OEND LEND -> ai_56c P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_56c.
  intros m1 c0 c8 c16 c48 c72 c80 c88 cw u176 u184 p0 p1 p2 jpad jseq bc ptr sLL sOF x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 INV IB HL HO.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold ai_66c in CONT. pose proof INV as INV0.
  destruct INV as (_ & PT & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  assert (RG : 544 <= SPV < 2^47 /\ 4096 <= DCTX < 2^47) by (clear - S17 S19 S20; lia).
  assert (MUL : munch [(SPV - 352, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  hold TRANS. hold CONT. hold INV0. hold IB. hold HL. hold HO.
  try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S17. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML. try hold ALSP. try hold ALLL. try hold ALOF. try hold ALML.
  kx_autoLx [0x1db98] 20%nat
    [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47)]
    [].
  all: try kx_mem.
  all: unfold held in TRANS, CONT, INV0, IB, HL, HO.
  all: (eapply CONT; [ first [ exact INV0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | assumption] ] | exact IB | exact HL | exact HO ]).
Qed.

Lemma seqd_irl_eq : forall P LEND m1 fr fr', seqd_iinv P LEND m1 fr -> fr = fr' -> seqd_iinv P LEND m1 fr'.
Proof. intros P LEND m1 fr fr' H E. subst fr'. exact H. Qed.

(* [comment removed for export] *)
Lemma seqd_irl_ML : forall P OEND LEND, seqd_static P OEND LEND -> ai_7ac P OEND LEND -> ai_6a8 P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_6a8.
  intros m1 c0 c8 c16 c48 c72 c80 c88 cw p0 p1 p2 jpad jseq bc ptr sLL sOF sML x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 INV IB HL HO HM.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold ai_7ac in CONT.
  destruct INV as (FR & _).
  unfold seqd_ifr, seqd_ifr_hd, seqd_ifr_tl, bitd_cells in FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post app q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST.
  assert (RG : 544 <= SPV < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= DST < 2^47 /\ 4096 <= PFX < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S17; lia).
  assert (MUL : munch [(SPV - 352, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  hold TRANS. hold CONT. hold IB. hold HL. hold HO. hold HM.
  try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S17. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML. try hold ALSP. try hold ALLL. try hold ALOF. try hold ALML.
  kx_autoLx [0x1cc14] 40%nat
    [KZRange SPV 544 (2^47); KZRange OEND 4096 (2^47); KZRange DST 4096 (2^47); KZRange PFX 4096 (2^47); KZWr (SPV - 352) 352]
    [(SPV - 352, 352)].
  all: try kx_mem.
  all: unfold held in TRANS, CONT, IB, HL, HO, HM.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with FR : rw_cells ?sg mm ?AA (C8 ?w :: ?L) |- _ =>
      assert (FR2 : rw_cells sg mm AA (CB 8 (le8 w) :: L))
        by (eapply rw_cells_recell; [exact FR | pose proof FR as [[WF _] _]; split; [apply length_le8 | exact (proj2 WF)] | reflexivity])
    end end.
  all: (eapply CONT;
      [ eapply seqd_irl_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR2] | cbn [seqd_frame]; repeat f_equal; lia]
      | exact IB | exact HL | exact HO | exact HM ]).
Qed.
