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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_lkit2 RZ_seq_l_xat RZ_seq_l_e2_at seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac e2m_hold t := lazymatch t with (?a, ?b) => e2m_hold a; e2m_hold b | ?h => try hold h end.
Ltac e2m_unhold t := lazymatch t with (?a, ?b) => e2m_unhold a; e2m_unhold b | ?h => try unfold held in h end.

Lemma e2_exec3 : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  seql_at_err P OEND LLO LEND LOCV -> e2_tail P OEND LLO LEND LOCV K -> e2_matloop P OEND LLO LEND LOCV K -> e2_close P OEND LLO LEND LOCV K -> e2_match P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2 CONT3 CONT4. unfold e2_match.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs ile sl ole idx x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x26 x28 x29 x30 x31 INV LF HO FAST E1 E2 E3 ELP HIDX HRING.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold seql_at_err in CONT1. unfold e2_tail in CONT2. unfold e2_matloop in CONT3. unfold e2_close in CONT4.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & _). pose proof FAST as FAST0. destruct FAST as (F1 & F2 & F3 & F4).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, L1, L2, CONT1, CONT2, CONT3, CONT4, TRANS |- *.
  sd_static_open ST.
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= ole < 2^47 /\ 4096 <= PFX < 2^47 /\ 4096 <= ile < 2^47 /\ 0 <= mlv <= 262143)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 F1 F2 F3 F4 E1 E3; lia).
  destruct (Z_le_gt_dec ofs (ole - PFX)) as [CA|CB].
  - (* [comment removed for export] *)
    assert (RA : 0 <= ole - PFX - ofs <= 2^47 /\ 4096 <= ole - ofs <= 2^47 /\ 0 <= ofs <= 2^47) by (clear - CA HO RG; lia).
    ((try hold CONT1; try hold CONT2; try hold CONT3; try hold CONT4; try hold TRANS; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold INV; try hold L2; try hold F3; e2m_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1a6f4; 0x1a0cc; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange ole 4096 (2^47); KZRange PFX 4096 (2^47); KZRange ile 4096 (2^47); KZRange mlv 0 262143;
     KZRange ofs 0 (2^47); KZRange (ole - PFX) 0 (2^47); KZRange (ole - PFX - ofs) 0 (2^47); KZRange (ole - ofs) 4096 (2^47); KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in CONT4; try unfold held in TRANS; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in INV; try unfold held in L2; try unfold held in F3; e2m_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a6f4) _ _ _ _) => (eapply CONT4; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_lfacts_lp; [exact LF0 | lia] | unfold seql_mfast; cbn [y_DST]; lia | lia | cbn [y_PFX]; lia | lia | first [eassumption | lia | (cbn [y_PFX]; lia) | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a0cc) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | cbn [y_DST]; lia | lia | lia | right; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV2;
    pose proof INV2 as ((?jpf & ?jsf & FR2) & _); cbn [seql_frame y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in FR2;
    ((try hold CONT1; try hold CONT2; try hold CONT3; try hold CONT4; try hold TRANS; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold INV; try hold INV2; try hold L2; try hold F3; try hold MUL; try hold WMl; try hold KXMI; try hold FR; e2m_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1a1d8; 0x1a150; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange ole 4096 (2^47); KZRange mlv 0 262143; KZRange ofs 16 (2^47); KZRange (ole - ofs) 4096 (2^47)]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in CONT4; try unfold held in TRANS; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in INV; try unfold held in INV2; try unfold held in L2; try unfold held in F3; try unfold held in MUL; try unfold held in WMl; try unfold held in KXMI; try unfold held in FR; e2m_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a1d8) _ _ _ _) => (eapply CONT2; [exact INV2 | lia | right; split; [ eapply seql_lfacts_lp; [exact LF0 | lia] | lia] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a150) _ _ _ _) => (eapply CONT3 with (ole := ole) (mlv := mlv) (ofs := ofs); [exact INV2 | eapply seql_lfacts_lp; [exact LF0 | lia] | unfold seql_mfast; cbn [y_DST]; lia | cbn [y_PFX]; lia | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end))
      end).
  - (* [comment removed for export] *)
    assert (RB : 1 <= ofs - ole + PFX <= 18446744073709551615 /\ 1 <= ofs <= 18446744073709551615 /\ 0 <= ole - PFX <= 2^47) by (clear - CB HO RG S3 L1 E3 F1; lia).
    ((try hold CONT1; try hold CONT2; try hold CONT3; try hold CONT4; try hold TRANS; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold INV; try hold L2; try hold F3; e2m_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1a104; 0x1a0d8; 0x1abb4; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange ole 4096 (2^47); KZRange PFX 4096 (2^47); KZRange ile 4096 (2^47); KZRange mlv 0 262143;
     KZRange ofs 1 18446744073709551615; KZRange (ole - PFX) 0 (2^47); KZRange (ofs - ole + PFX) 1 18446744073709551615; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in CONT4; try unfold held in TRANS; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in INV; try unfold held in L2; try unfold held in F3; e2m_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => (eapply CONT1; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | lia | left; reflexivity])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a104) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a0d8) _ _ _ _) => (exfalso; lia)
      end).
Qed.

Lemma e2_matloop_aux : forall (k : nat) P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  e2_tail P OEND LLO LEND LOCV K ->
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c240 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (idx : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x26 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seql_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - y_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  ome - cur <= 32 * (Z.of_nat k + 1) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 idx) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sl) (Z_to_bv 64 (-17)) (Z_to_bv 64 src) x21 (Z_to_bv 64 ome) (Z_to_bv 64 LLO) (Z_to_bv 64 OP) x25 x26 (Z_to_bv 64 cur) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1a150) (y_fc P) None m1 (seg_rom usegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LLO LEND LOCV K ST HK CONT1 m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ole mlv sl ofs cur src ome idx x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x26 x28 x29 x30 x31 INV LF MF HOF EM HC ES HIDX HRING HM.
  all: pose proof CONT1 as CONT0; unfold e2_tail in CONT1.
  all: pose proof LF as LF0; destruct LF as (L1 & L2 & _); pose proof MF as MF0; destruct MF as (M1 & M2 & M3 & M4).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, L1, L2, M1, HOF, CONT1 |- *.
  all: sd_static_open ST.
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= src < 2^47 /\ 4096 <= ome < 2^47) by (clear - L1 S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 HOF EM HC ES; lia).
  - pose proof I as IHk.
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HM; try hold HOF; e2m_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1a1d8; 0x1a150; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HM; try unfold held in HOF; e2m_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV | cbn [y_DST]; lia | lia | lia | right; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV1;
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HM; try hold HOF; e2m_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1a1d8; 0x1a150; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HM; try unfold held in HOF; e2m_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV1 | cbn [y_DST]; lia | lia | lia | right; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV2;
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HM; try hold HOF; e2m_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1a1d8; 0x1a150; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HM; try unfold held in HOF; e2m_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a150) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a1d8) _ _ _ _) => (eapply CONT1; [exact INV2 | lia | right; split; [exact LF0 | lia] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end))
      end))
      end).
  - ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HM; try hold HOF; e2m_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1a1d8; 0x1a150; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HM; try unfold held in HOF; e2m_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV | cbn [y_DST]; lia | lia | lia | right; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV1;
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HM; try hold HOF; e2m_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1a1d8; 0x1a150; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HM; try unfold held in HOF; e2m_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV1 | cbn [y_DST]; lia | lia | lia | right; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV2;
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HM; try hold HOF; e2m_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1a1d8; 0x1a150; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HM; try unfold held in HOF; e2m_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a150) _ _ _ _) => (eapply (IHk _ OEND LLO LEND LOCV K ST0 HK CONT0) with (ole := ole) (mlv := mlv) (ofs := ofs); [exact INV2 | exact LF0 | exact MF0 | cbn [y_PFX]; lia | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. | lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a1d8) _ _ _ _) => (eapply CONT1; [exact INV2 | lia | right; split; [exact LF0 | lia] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end))
      end))
      end).
Qed.

Lemma e2_matloop_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  e2_tail P OEND LLO LEND LOCV K -> e2_matloop P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1. unfold e2_matloop.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ole mlv sl ofs cur src ome idx x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x26 x28 x29 x30 x31 INV LF MF HOF EM HC ES HIDX HRING.
  eapply (e2_matloop_aux (Z.to_nat (ome - cur)) P OEND LLO LEND LOCV K ST HK CONT1); try eassumption. lia.
Qed.
