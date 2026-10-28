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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase RZ_seq_l_ient RZ_seq_l_la_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_ihead : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> LLO <= y_LITP P <= LEND ->
  la_head P OEND LLO LEND LOCV (y_nbSeq P) -> ai_i7 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST HLP CONT. unfold ai_i7.
  intros m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw p0 p1 p2 jpad jring jseq bc ptr sLL sOF sML x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 INV IB HZ HF0 HF1 HF2.
  pose proof (seql_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seql_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold la_head in CONT.
  destruct INV as (FR & _). destruct IB as (IB1 & IB2).
  assert (JL : length jring = 192%nat).
  { pose proof FR as [[WF _] _]. unfold seql_ifr in WF. cbn [app] in WF.
    repeat (let W := fresh "W" in destruct WF as [W WF]; try exact W). }
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  cbv beta iota zeta delta [seql_ifr seql_saved y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in FR. cbn [app] in FR.
  sd_static_open ST.
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OEND < 2^47 /\ 4096 <= MLT < 2^47 /\ 4096 <= DCTX < 2^47 /\ 4096 <= DST < 2^47 /\ 4096 <= PFX < 2^47 /\ 1 <= nbSeq <= 98047 /\ 1 <= Z.min nbSeq 8 <= 8)
    by (clear - S1 S2 S3 S4 S5 S6 S7 S16 S19 S20 S23; lia).
  try hold TRANS. try hold CONT. try hold IB2. try hold HF0. try hold HF1. try hold HF2. try hold HLP. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
  try hold JL.
  kx_autoLx [0x17d38; 0x19c80; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange OEND 4096 (2^47); KZRange MLT 4096 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange PFX 4096 (2^47);
     KZRange nbSeq 1 98047; KZRange (Z.min nbSeq 8) 1 8; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end).
  kx_mem. (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in HLP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  try unfold held in JL. destruct (seql_ring_any jring JL) as (rl & rm & ro & RB). subst jring.
  lazymatch type of FR with rw_cells ?sg ?mm ?AA ?L =>
    pose proof (rw_cells_merge sg mm AA (firstn 49 L) (skipn 49 L) [] ltac:(rewrite app_nil_r, firstn_skipn; exact FR)) as FR2 end.
  cbn [firstn skipn cells_size csize Nat.add cells_bytes cbytes app] in FR2. rewrite app_nil_r in FR2.
  lazymatch goal with |- context [mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?r21 _ _ _ _ _ _ _ _ _ _] =>
    replace r21 with (Z_to_bv 64 (Z.min nbSeq 8 - 0)) by (f_equal; lia) end.
  eapply CONT with (LP := LITP) (sn := 0) (OP := DST) (rl := rl) (rm := rm) (ro := ro);
    [ eapply seql_iinv_linv; eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR2] | cbn [seql_frame]; repeat f_equal; lia]
    | unfold seql_lfacts; cbn [y_DST y_tLL y_tOF y_tML y_SEQ y_sq y_nbSeq];
      split; [lia|]; split; [exact HLP|]; split; [exact HF0|]; split; [exact HF1|]; split; [exact HF2|]; split; [lia| exact IB2]
    | lia | lia | lia | lia | reflexivity | (intros j Hj; exfalso; lia) | reflexivity ].
Qed.
