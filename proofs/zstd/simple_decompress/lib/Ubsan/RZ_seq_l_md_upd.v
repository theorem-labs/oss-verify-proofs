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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_md_at seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma md_update : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  md_upd P OEND LLO LEND LOCV K -> md_exec P OEND LLO LEND LOCV K -> md_rl1 P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK  CONT1 CONT2 . unfold md_rl1.
  intros m1 c0 c128 c176 c232 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP nLL aLL bLL vLL nOF bOF nML bML mlv ofs sn x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x24 x28 x29 INV LF NX HA1 HV HM HSN HRING.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold md_upd in CONT1. unfold md_exec in CONT2. 
  
  destruct INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  pose proof NX as (NX1 & NX2 & NX3 & NX4 & NX5 & NX6 & NX7 & NX8 & NX9).
  pose proof (Z_to_bv_bv_unsigned ofs) as Eofs. pose proof (kx_u64_range ofs) as HO. remember (bv_unsigned ofs) as ofz eqn:Eofz. clear Eofz. subst ofs.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  sd_static_open ST.
  pose proof (seq_pow_le _ _ OKLL) as PLL. pose proof (seq_pow_le _ _ OKOF) as POF. pose proof (seq_pow_le _ _ OKML) as PML.
  assert (RS : 0 <= bc <= 9900000 /\ 1 <= K <= 98047) by (clear - L6 HK S16; lia).
  assert (RP : 1 <= 2^bLL <= 512 /\ 1 <= 2^bOF <= 512 /\ 1 <= 2^bML <= 512 /\ nLL <= 511 /\ nOF <= 511 /\ nML <= 511).
  { clear - NX1 NX2 NX3 NX4 NX5 NX6 NX7 NX8 NX9 PLL POF PML.
    pose proof (Z.pow_pos_nonneg 2 bLL). pose proof (Z.pow_pos_nonneg 2 bOF). pose proof (Z.pow_pos_nonneg 2 bML). lia. }
  pose proof (bitmask_know m1 bLL MI ltac:(clear - NX1; lia)) as BK1.
  pose proof (bitmask_know m1 bOF MI ltac:(clear - NX4; lia)) as BK2.
  pose proof (bitmask_know m1 bML MI ltac:(clear - NX7; lia)) as BK3.
  unfold BITMASK in BK1, BK2, BK3.
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (PA : 0 < 2^aLL <= 65536) by (clear - HA1; split; [apply Z.pow_pos_nonneg; lia | change 65536 with (2^16); apply Z.pow_le_mono_r; lia]).
  assert (HV' : 0 <= vLL <= 131071) by (clear - HV; lia). assert (HM' : 0 <= mlv <= 262143) by (clear - HM; lia).
  
  try hold TRANS. try hold CONT1. try hold CONT2. try hold LF0. try hold NX. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold L7. try hold NX3. try hold NX6. try hold NX9. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x186f0; 0x188c8; 0x1ac04] 200%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange bc 0 9900000; KZRange K 1 98047;
     KZRange nLL 0 511; KZRange nOF 0 511; KZRange nML 0 511; KZRange aLL 0 16; KZRange bLL 0 9; KZRange bOF 0 9; KZRange bML 0 9;
     KZRange vLL 0 131071; KZRange mlv 0 262143;
     KZRange (2^bLL) 1 512; KZRange (2^bOF) 1 512; KZRange (2^bML) 1 512;
     KZWord (BITMASK + 4 * bLL) 4 (2^bLL - 1); KZWord (BITMASK + 4 * bOF) 4 (2^bOF - 1); KZWord (BITMASK + 4 * bML) 4 (2^bML - 1);
     KZWr (SPV - 688) 688; KZImg 0x10000 0x14000]
    [(SPV - 688, 688)].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end).
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: kx_mem.
  all: sd_rbf2.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT1; try unfold held in CONT2; try unfold held in LF0; try unfold held in NX; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in NX3; try unfold held in NX6; try unfold held in NX9; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: first
    [ eapply CONT1;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seql_lfacts; cbn [y_DST y_tLL y_tOF y_tML y_SEQ y_sq]; sd_land;
        split; [exact L1|]; split; [exact L2|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|];
        eapply bit_ok_mono; [exact L7 | lia]
      | exact HO | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. ]
    | eapply CONT2;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | eapply seql_lfacts_bc; [exact LF0 | lia]
      | exact HO | lia | lia  | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..] ].
Qed.
