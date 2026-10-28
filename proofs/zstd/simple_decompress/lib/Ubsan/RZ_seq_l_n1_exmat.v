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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_lkit2 RZ_seq_l_xat RZ_seq_l_n1_at seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma n1_exec3 : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  seql_at_err P OEND LLO LEND LOCV -> n1_tail P OEND LLO LEND LOCV K -> n1_matloop P OEND LLO LEND LOCV K -> n1_close P OEND LLO LEND LOCV K -> n1_match P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2 CONT3 CONT4. unfold n1_match.
  intros m1 c0 c128 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs ile sl ole sn cidx dll dml dof x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 INV LF HO FAST E1 E2 E3  HSN HCI HDL HDM HDO HRING.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold seql_at_err in CONT1. unfold n1_tail in CONT2. unfold n1_matloop in CONT3. unfold n1_close in CONT4.
  pose proof INV as INV0. destruct INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & _). pose proof FAST as FAST0. destruct FAST as (F1 & F2 & F3 & F4).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, L1, L2, CONT1, CONT2, CONT3, CONT4, TRANS, HSN |- *.
  sd_static_open ST.
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= ole < 2^47 /\ 4096 <= PFX < 2^47 /\ 4096 <= ile < 2^47 /\ 0 <= mlv <= 262143 /\ 0 <= sl < 2^19)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 F1 F2 F3 F4 E1 E2 E3; lia).
  destruct (Z_le_gt_dec ofs (ole - PFX)) as [CA|CB].
  - (* [comment removed for export] *)
    assert (RA : 0 <= ole - PFX - ofs <= 2^47 /\ 4096 <= ole - ofs <= 2^47 /\ 0 <= ofs <= 2^47) by (clear - CA HO RG; lia).
    try hold CONT1. try hold CONT2. try hold CONT3. try hold CONT4. try hold TRANS. try hold INV0. try hold HK. try hold LF0. try hold ST0. try hold FAST0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1abb4; 0x19038; 0x18fa4; 0x1925c; 0x35670; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange ole 4096 (2^47); KZRange PFX 4096 (2^47); KZRange ile 4096 (2^47); KZRange mlv 0 262143;
     KZRange ofs 0 (2^47); KZRange (ole - PFX) 0 (2^47); KZRange (ole - PFX - ofs) 0 (2^47); KZRange (ole - ofs) 4096 (2^47); KZRange sl 0 (2^19); KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end).
    all: kx_mem.
    all: (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in CONT4; try unfold held in TRANS; try unfold held in INV0; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1925c) _ _ _ _) =>
          eapply CONT4; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_lfacts_lp; [exact LF0 | lia] | unfold seql_mfast; cbn [y_DST]; lia | lia | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) =>
          eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | cbn [y_DST]; lia | lia | lia | right; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV2
      end.
    clear TRANS FR MUL WMl INV0. try clear MI. try clear KXMI. try clear jpad jseq.
    pose proof (seql_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST0 INV2) as TRANS.
    pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV2) as MI.
    pose proof INV2 as INV0. destruct INV2 as ((jpad & jseq & FR) & _).
    cbn [seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in TRANS, FR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUL : munch [(SPV - 688, SPV)] mm mm) by apply munch_refl; assert (WMl : wmono usegs mm mm) by apply wmono_refl end.
    try hold CONT1. try hold CONT2. try hold CONT3. try hold CONT4. try hold TRANS. try hold INV0. try hold HK. try hold LF0. try hold ST0. try hold FAST0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1abb4; 0x19038; 0x18fa4; 0x1925c; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange ole 4096 (2^47); KZRange mlv 0 262143; KZRange ofs 16 (2^47); KZRange (ole - ofs) 4096 (2^47); KZRange sl 0 (2^19); KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end).
    all: kx_mem.
    all: (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in CONT4; try unfold held in TRANS; try unfold held in INV0; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x19038) _ _ _ _) =>
          eapply CONT2; [first [exact INV0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]] | lia | split; [ eapply seql_lfacts_lp; [exact LF0 | lia] | lia] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fa4) _ _ _ _) =>
          eapply CONT3 with (ole := ole) (mlv := mlv) (ofs := ofs); [first [exact INV0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]] | eapply seql_lfacts_lp; [exact LF0 | lia] | unfold seql_mfast; cbn [y_DST]; lia | cbn [y_PFX]; lia | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => exfalso; lia
      end.
  - (* [comment removed for export] *)
    assert (RB : 1 <= ofs - ole + PFX <= 18446744073709551615 /\ 1 <= ofs <= 18446744073709551615 /\ 0 <= ole - PFX <= 2^47) by (clear - CB HO RG S3 L1 E3 F1; lia).
    try hold CONT1. try hold CONT2. try hold CONT3. try hold CONT4. try hold TRANS. try hold INV0. try hold HK. try hold LF0. try hold ST0. try hold FAST0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1abb4; 0x19038; 0x18fa4; 0x1925c; 0x35670; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange ole 4096 (2^47); KZRange PFX 4096 (2^47); KZRange ile 4096 (2^47); KZRange mlv 0 262143;
     KZRange ofs 1 18446744073709551615; KZRange (ole - PFX) 0 (2^47); KZRange (ofs - ole + PFX) 1 18446744073709551615; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end).
    all: kx_mem.
    all: (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in CONT4; try unfold held in TRANS; try unfold held in INV0; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => (eapply CONT1; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | lia | left; reflexivity])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => (exfalso; lia)
      end.
Qed.

Lemma n1_matloop_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  n1_tail P OEND LLO LEND LOCV K -> n1_matloop P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1. unfold n1_matloop.
  intros m1 c0 c128 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ole mlv sl ofs cur src ome sn cidx dll dml dof x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 INV LF MF HOF EM HC ES HSN HCI HDL HDM HDO HRING.
  remember (Z.to_nat (ome - cur)) as k eqn:EK.
  assert (HM : ome - cur <= 32 * (Z.of_nat k + 1)) by (subst k; rewrite Z2Nat.id by lia; lia).
  clear EK. unfold n1_tail in CONT1.
  revert m1 cur src x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 INV HC ES HM.
  induction k as [|k IHk]; intros m1 cur src x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 INV HC ES HM.
  all: pose proof LF as LF0; destruct LF as (L1 & L2 & _); pose proof MF as MF0; destruct MF as (M1 & M2 & M3 & M4).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, L1, L2, M1, HOF, CONT1 |- *.
  all: sd_static_open ST.
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= src < 2^47 /\ 4096 <= ome < 2^47 /\ 0 <= sl < 2^47) by (clear - L1 S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 M4 HOF EM HC ES; lia).
  all: (try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HOF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML).
  all: kx_autoLx [0x18fa4; 0x19038; 0x1abb4; 0x35670; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47)]
    [].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end).
  all: kx_mem.
  all: (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HOF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) =>
        eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV | cbn [y_DST]; lia | lia | lia | right; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV1
    end.
  all: (try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HOF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML).
  all: kx_autoLx [0x18fa4; 0x19038; 0x1abb4; 0x35670; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47)]
    [].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end).
  all: kx_mem.
  all: (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HOF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) =>
        eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV1 | cbn [y_DST]; lia | lia | lia | right; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV2
    end.
  all: pose proof (seql_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST0 INV2) as TRANS.
  all: pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV2) as MI.
  all: pose proof INV2 as INV0; destruct INV2 as ((jpad & jseq & FR) & _).
  all: cbn [seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in TRANS, FR.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUL : munch [(SPV - 688, SPV)] mm mm) by apply munch_refl; assert (WMl : wmono usegs mm mm) by apply wmono_refl end.
  all: (try hold CONT1; try hold IHk; try hold TRANS; try hold INV0; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HOF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML).
  all: kx_autoLx [0x18fa4; 0x19038; 0x1abb4; 0x35670; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47); KZRange sl 0 (2^47); KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end).
  all: kx_mem.
  all: (try unfold held in CONT1; try unfold held in IHk; try unfold held in TRANS; try unfold held in INV0; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HOF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fa4) _ _ _ _) =>
        first [exfalso; lia | eapply IHk; [first [exact INV0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]] | lia | lia | lia]]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x19038) _ _ _ _) =>
        eapply CONT1; [first [exact INV0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]] | lia | split; [exact LF0 | lia] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => exfalso; lia
    end.
Qed.
