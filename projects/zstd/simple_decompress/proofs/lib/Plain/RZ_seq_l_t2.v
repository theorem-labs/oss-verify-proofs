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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_lkit2 RZ_seq_l_xat RZ_seq_l_t2_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma t2_lfacts_op : forall P OEND LLO LEND B OP OP' LP bc ptr sLL sOF sML,
  seql_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> y_DST P <= OP' <= OEND ->
  seql_lfacts P OEND LLO LEND B OP' LP bc ptr sLL sOF sML.
Proof. intros P OEND LLO LEND B OP OP' LP bc ptr sLL sOF sML (L1 & L) H. split; [exact H| exact L]. Qed.

Lemma t2_brk_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  seql_at_err P OEND LLO LEND LOCV -> t2_sw0 P OEND LLO LEND LOCV K -> t2_cpA P OEND LLO LEND LOCV K -> t2_cpB P OEND LLO LEND LOCV K -> t2_w1 P OEND LLO LEND LOCV K -> t2_brk P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2 CONT3 CONT4 CONT5. unfold t2_brk.
  intros m1 w0 c8 c16 c48 c56 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs idx cidx raddr x1 x5 x6 x7 x8 x11 x12 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 INV LF HO HL HM HB HIDX HRING HCI HRA HRL HRM HRO.
  unfold seql_at_err in CONT1. unfold t2_sw0 in CONT2. unfold t2_cpA in CONT3. unfold t2_cpB in CONT4. unfold t2_w1 in CONT5.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, L1, L2, CONT1, CONT2, CONT3, CONT4, CONT5 |- *.
  sd_static_open ST.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= OEND < 2^47 /\ 0 <= LEND - LP <= 2^47 /\ 0 <= OEND - OP <= 2^47)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11; lia).
  assert (MUL : munch [(SPV - 608, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  ((try hold CONT1; try hold CONT2; try hold CONT3; try hold CONT4; try hold CONT5; try hold HK; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold LF0; try hold ST0; try hold INV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18c10; 0x18ff4; 0x18d9c; 0x18fc8] 60%nat
    [KZRange SPV 816 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange (LEND - LP) 0 (2^47); KZRange (OEND - OP) 0 (2^47); KZRange llv 0 262143; KZRange mlv 0 262143; KZWr (SPV - 608) 608]
    [(SPV - 608, 608)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in CONT4; try unfold held in CONT5; try unfold held in HK; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18c10) _ _ _ _) => (eapply CONT1; [exact INV | lia | left; reflexivity])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18ff4) _ _ _ _) => (sd_diffs; eapply CONT2 with (llv := llv); [exact INV | exact LF0 | exact HO | lia | exact HM | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18d9c) _ _ _ _) => (sd_diffs; eapply CONT3 with (OP := OP) (cur := OP); [exact INV | exact LF0 | exact HO | exact HL | exact HM | lia | lia | lia | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fc8) _ _ _ _) => (sd_diffs; eapply CONT4 with (OP := OP) (cur := OP); [exact INV | exact LF0 | exact HO | exact HL | exact HM | lia | lia | lia | lia | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2f530) _ _ _ _) => (sd_diffs; eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV | cbn [y_DST]; lia | lia | lia | left; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV'; eapply CONT5 with (OP := OP); [exact INV' | exact LF0 | exact HO | exact HL | exact HM | lia | lia | lia | lia | reflexivity | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
Qed.

Lemma t2_w1_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  t2_wl P OEND LLO LEND LOCV K -> t2_cpB P OEND LLO LEND LOCV K -> t2_w1 P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2. unfold t2_w1.
  intros m1 w0 c8 c16 c48 c56 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs lft en wend wlen idx cidx raddr x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 INV LF HO HL HM ELF HLF EEN HEN EW HW EWL HD HIDX HRING HCI HRA HRL HRM HRO.
  unfold t2_wl in CONT1. unfold t2_cpB in CONT2.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  subst wlen.
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, L1, L2, CONT1, CONT2 |- *.
  sd_static_open ST.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= en < 2^47 /\ 4096 <= wend < 2^47 /\ 1 <= lft <= 262143 /\ 0 <= wend - OP <= 2^47 /\ 0 <= llv <= 262143)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 HL ELF HLF EEN HEN EW HW; lia).
  ((try hold CONT1; try hold CONT2; try hold HK; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold LF0; try hold ST0; try hold INV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18d60; 0x18fc8] 40%nat
    [KZRange SPV 816 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange en 4096 (2^47); KZRange wend 4096 (2^47);
     KZRange lft 1 262143; KZRange (wend - OP) 0 (2^47); KZRange llv 0 262143]
    [(SPV - 608, 608)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18d60) _ _ _ _) => (eapply CONT1 with (OP := OP) (wend := wend); [ exact INV | exact LF0 | exact HO | exact HL | exact HM | exact ELF | exact HLF | exact EEN | exact HEN | exact EW | reflexivity | lia | lia | lia | exact HD | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fc8) _ _ _ _) => (eapply CONT2 with (OP := OP) (cur := wend); [ exact INV | exact LF0 | exact HO | exact HL | exact HM | exact ELF | exact HLF | exact EEN | exact HEN | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
Qed.

Lemma t2_wl_aux : forall (k : nat) P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  t2_cpB P OEND LLO LEND LOCV K ->
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs lft en wend wlen cur srcp : Z) (idx cidx raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP -> seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML -> 0 <= ofs < 2^64 -> 0 <= llv < 2^18 -> 0 <= mlv < 2^18 ->
  lft = LEND - LP -> 0 < lft < llv -> en = OP + lft -> en <= OEND ->
  wend = en - 32 -> wlen = wend - OP -> 17 <= wend - OP -> OP + 16 <= cur < wend -> srcp = LP + (cur - OP) + 16 -> 17 <= LP - OP ->
  idx = y_nbSeq P - K -> seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro -> 0 <= cidx <= 7 -> raddr = y_SPV P - 328 + 24 * cidx -> llv = rl cidx -> mlv = rm cidx -> ofs = ro cidx -> wend - cur <= 32 * (Z.of_nat k + 1) ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 cur) (Z_to_bv 64 LP) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 idx) (Z_to_bv 64 srcp) (Z_to_bv 64 wlen) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 lft) (Z_to_bv 64 wend) (Z_to_bv 64 en) (Z_to_bv 64 OP) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18d60) (y_fc P) None m1 (seg_rom psegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LLO LEND LOCV K ST HK CONT1 m1 w0 c8 c16 c48 c56 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs lft en wend wlen cur srcp idx cidx raddr x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV LF HO HL HM ELF HLF EEN HEN EW EWL HW HC ES HD HIDX HRING HCI HRA HRL HRM HRO HMk.
  all: unfold t2_cpB in CONT1.
  all: pose proof LF as LF0; destruct LF as (L1 & L2 & _).
  all: pose proof ST as ST0. all: subst wlen.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, L1, L2, CONT1 |- *.
  all: sd_static_open ST.
  all: assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= en < 2^47 /\ 4096 <= wend < 2^47 /\ 4096 <= cur < 2^47 /\ 4096 <= srcp < 2^47 /\ 1 <= lft <= 262143 /\ 0 <= llv <= 262143)
         by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 HL ELF HLF EEN HEN EW HW HC ES; lia).
  - pose proof I as IHk.
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold HM; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18d60; 0x18fc8] 40%nat
    [KZRange SPV 816 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange en 4096 (2^47); KZRange wend 4096 (2^47);
     KZRange cur 4096 (2^47); KZRange srcp 4096 (2^47); KZRange lft 1 262143; KZRange (wend - OP) 17 (2^47); KZRange llv 0 262143]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in HM; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2f530) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV | cbn [y_DST]; lia | lia | lia | left; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV1;
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold HM; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18d60; 0x18fc8] 40%nat
    [KZRange SPV 816 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange en 4096 (2^47); KZRange wend 4096 (2^47);
     KZRange cur 4096 (2^47); KZRange srcp 4096 (2^47); KZRange lft 1 262143; KZRange (wend - OP) 17 (2^47); KZRange llv 0 262143]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in HM; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2f530) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV1 | cbn [y_DST]; lia | lia | lia | left; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV2;
    pose proof INV2 as ((jpad2 & jseq2 & FR) & _); cbn [seql_frame y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in FR;
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold HM; try hold HMk; try hold INV2; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18d60; 0x18fc8] 40%nat
    [KZRange SPV 816 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange en 4096 (2^47); KZRange wend 4096 (2^47);
     KZRange cur 4096 (2^47); KZRange srcp 4096 (2^47); KZRange lft 1 262143; KZRange (wend - OP) 17 (2^47); KZRange llv 0 262143]
    [(SPV - 608, 608)];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in HM; try unfold held in HMk; try unfold held in INV2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18d60) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fc8) _ _ _ _) => (eapply CONT1 with (OP := OP) (cur := wend); [ exact INV2 | exact LF0 | exact HO | exact HL | exact HM | exact ELF | exact HLF | exact EEN | exact HEN | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end))
      end))
      end).
  - ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold HM; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18d60; 0x18fc8] 40%nat
    [KZRange SPV 816 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange en 4096 (2^47); KZRange wend 4096 (2^47);
     KZRange cur 4096 (2^47); KZRange srcp 4096 (2^47); KZRange lft 1 262143; KZRange (wend - OP) 17 (2^47); KZRange llv 0 262143]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in HM; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2f530) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV | cbn [y_DST]; lia | lia | lia | left; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV1;
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold HM; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18d60; 0x18fc8] 40%nat
    [KZRange SPV 816 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange en 4096 (2^47); KZRange wend 4096 (2^47);
     KZRange cur 4096 (2^47); KZRange srcp 4096 (2^47); KZRange lft 1 262143; KZRange (wend - OP) 17 (2^47); KZRange llv 0 262143]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in HM; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2f530) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV1 | cbn [y_DST]; lia | lia | lia | left; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV2;
    pose proof INV2 as ((jpad2 & jseq2 & FR) & _); cbn [seql_frame y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in FR;
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold HM; try hold HMk; try hold INV2; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18d60; 0x18fc8] 40%nat
    [KZRange SPV 816 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange en 4096 (2^47); KZRange wend 4096 (2^47);
     KZRange cur 4096 (2^47); KZRange srcp 4096 (2^47); KZRange lft 1 262143; KZRange (wend - OP) 17 (2^47); KZRange llv 0 262143]
    [(SPV - 608, 608)];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in HM; try unfold held in HMk; try unfold held in INV2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18d60) _ _ _ _) => (eapply (IHk _ OEND LLO LEND LOCV K ST0 HK) with (OP := OP) (wend := wend); [unfold t2_cpB; exact CONT1 | exact INV2 | exact LF0 | exact HO | exact HL | exact HM | exact ELF | exact HLF | exact EEN | exact HEN | exact EW | reflexivity | exact HW | lia | lia | exact HD | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. | lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fc8) _ _ _ _) => (eapply CONT1 with (OP := OP) (cur := wend); [ exact INV2 | exact LF0 | exact HO | exact HL | exact HM | exact ELF | exact HLF | exact EEN | exact HEN | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end))
      end))
      end).
Qed.

Lemma t2_wl_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  t2_cpB P OEND LLO LEND LOCV K -> t2_wl P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1. unfold t2_wl.
  intros m1 w0 c8 c16 c48 c56 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs lft en wend wlen cur srcp idx cidx raddr x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV LF HO HL HM ELF HLF EEN HEN EW EWL HW HC ES HD HIDX HRING HCI HRA HRL HRM HRO.
  eapply (t2_wl_aux (Z.to_nat (wend - cur)) P OEND LLO LEND LOCV K ST HK CONT1) with (llv := llv) (mlv := mlv) (ofs := ofs) (lft := lft) (wlen := wlen); first [eassumption | lia].
Qed.

Lemma t2_cpA_aux : forall (k : nat) P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P -> LOCV = 2 ->
  t2_sw P OEND LLO LEND LOCV K ->
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs lft en cur src : Z) (idx cidx raddr : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP -> seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML -> 0 <= ofs < 2^64 -> 0 <= llv < 2^18 -> 0 <= mlv < 2^18 ->
  lft = LEND - LP -> 0 < lft < llv -> en = OP + lft -> en <= OEND ->
  OP <= cur < en -> src = LP + (cur - OP) -> idx = y_nbSeq P - K -> seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro -> 0 <= cidx <= 7 -> raddr = y_SPV P - 328 + 24 * cidx -> llv = rl cidx -> mlv = rm cidx -> ofs = ro cidx -> en - cur <= Z.of_nat k + 1 ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 src) x10 x11 x12 (Z_to_bv 64 (y_DCTX P + 29896)) x14 x15 x16 x17 (Z_to_bv 64 idx) x19 (Z_to_bv 64 OEND) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 lft) x25 (Z_to_bv 64 en) (Z_to_bv 64 cur) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18d9c) (y_fc P) None m1 (seg_rom psegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LLO LEND LOCV K ST HK HLOC CONT1 m1 w0 c8 c16 c48 c56 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs lft en cur src idx cidx raddr x1 x5 x6 x7 x8 x10 x11 x12 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31 INV LF HO HL HM ELF HLF EEN HEN HC ES HIDX HRING HCI HRA HRL HRM HRO HMk.
  all: pose proof CONT1 as CONT0; unfold t2_sw in CONT1.
  all: pose proof (seql_linv_buf P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as STEP.
  all: pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  all: pose proof (seql_copy_facts P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as (BUF & _).
  all: pose proof LF as LF0; destruct LF as (L1 & L2 & _).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, L1, L2, BUF, CONT1, STEP |- *.
  all: sd_static_open ST.
  all: assert (LE32 : B0 <= LLO /\ LEND + 32 <= OEND) by (unfold held in S42; clear - S42 HLOC; lia).
  all: assert (MUL : munch [(cur, cur + 1)] m1 m1) by apply munch_refl; assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= src < 2^47 /\ 4096 <= en < 2^47 /\ 1 <= lft <= 262143 /\ 0 <= llv <= 262143 /\
                   B0 <= src /\ src + 1 <= B1 /\ B0 <= cur /\ cur + 1 <= B1 /\ DST <= cur /\ cur + 1 <= OEND)
         by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 LE32 HL ELF HLF EEN HEN HC ES; lia).
  - pose proof I as IHk.
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold STEP; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18d9c; 0x18fe4] 40%nat
    [KZRange SPV 816 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange en 4096 (2^47); KZRange lft 1 262143; KZRange llv 0 262143;
     KZWr cur 1]
    [(src, 1)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in STEP; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18d9c) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fe4) _ _ _ _) => (eapply CONT1 with (OP := en); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | eapply t2_lfacts_op; [exact LF0 | cbn [y_DST]; lia] | exact HO | exact HL | exact HM | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold STEP; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18d9c; 0x18fe4] 40%nat
    [KZRange SPV 816 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange en 4096 (2^47); KZRange lft 1 262143; KZRange llv 0 262143;
     KZWr cur 1]
    [(src, 1)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in STEP; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18d9c) _ _ _ _) => (eapply (IHk _ OEND LLO LEND LOCV K ST0 HK HLOC CONT0) with (OP := OP); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact HO | exact HL | exact HM | exact ELF | exact HLF | exact EEN | exact HEN | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. | lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fe4) _ _ _ _) => (eapply CONT1 with (OP := en); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | eapply t2_lfacts_op; [exact LF0 | cbn [y_DST]; lia] | exact HO | exact HL | exact HM | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
Qed.

Lemma t2_cpA_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P -> LOCV = 2 ->
  t2_sw P OEND LLO LEND LOCV K -> t2_cpA P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK HLOC CONT1. unfold t2_cpA.
  intros m1 w0 c8 c16 c48 c56 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs lft en cur src idx cidx raddr x1 x5 x6 x7 x8 x10 x11 x12 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31 INV LF HO HL HM ELF HLF EEN HEN HC ES HIDX HRING HCI HRA HRL HRM HRO.
  eapply (t2_cpA_aux (Z.to_nat (en - cur)) P OEND LLO LEND LOCV K ST HK HLOC CONT1) with (llv := llv) (mlv := mlv) (ofs := ofs) (lft := lft); first [eassumption | lia].
Qed.

Lemma t2_cpB_aux : forall (k : nat) P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P -> LOCV = 2 ->
  t2_sw P OEND LLO LEND LOCV K ->
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs lft en cur src rem : Z) (idx cidx raddr : Z) (x1 x5 x6 x7 x8 x11 x12 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP -> seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML -> 0 <= ofs < 2^64 -> 0 <= llv < 2^18 -> 0 <= mlv < 2^18 ->
  lft = LEND - LP -> 0 < lft < llv -> en = OP + lft -> en <= OEND ->
  OP <= cur < en -> src = LP + (cur - OP) -> rem = en - cur -> idx = y_nbSeq P - K -> seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro -> 0 <= cidx <= 7 -> raddr = y_SPV P - 328 + 24 * cidx -> llv = rl cidx -> mlv = rm cidx -> ofs = ro cidx -> en - cur <= Z.of_nat k + 1 ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 src) (Z_to_bv 64 rem) x11 x12 (Z_to_bv 64 (y_DCTX P + 29896)) x14 x15 x16 x17 (Z_to_bv 64 idx) x19 (Z_to_bv 64 OEND) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 lft) (Z_to_bv 64 cur) (Z_to_bv 64 en) x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18fc8) (y_fc P) None m1 (seg_rom psegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LLO LEND LOCV K ST HK HLOC CONT1 m1 w0 c8 c16 c48 c56 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs lft en cur src rem idx cidx raddr x1 x5 x6 x7 x8 x11 x12 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 INV LF HO HL HM ELF HLF EEN HEN HC ES ER HIDX HRING HCI HRA HRL HRM HRO HMk.
  all: pose proof CONT1 as CONT0; unfold t2_sw in CONT1.
  all: pose proof (seql_linv_buf P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as STEP.
  all: pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  all: pose proof (seql_copy_facts P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as (BUF & _).
  all: pose proof LF as LF0; destruct LF as (L1 & L2 & _).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, L1, L2, BUF, CONT1, STEP |- *.
  all: sd_static_open ST.
  all: assert (LE32 : B0 <= LLO /\ LEND + 32 <= OEND) by (unfold held in S42; clear - S42 HLOC; lia).
  all: assert (MUL : munch [(cur, cur + 1)] m1 m1) by apply munch_refl; assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= src < 2^47 /\ 4096 <= en < 2^47 /\ 1 <= lft <= 262143 /\ 0 <= llv <= 262143 /\
                   B0 <= src /\ src + 1 <= B1 /\ B0 <= cur /\ cur + 1 <= B1 /\ DST <= cur /\ cur + 1 <= OEND)
         by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 LE32 HL ELF HLF EEN HEN HC ES ER; lia).
  - pose proof I as IHk.
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold STEP; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18fc8; 0x18fe4] 40%nat
    [KZRange SPV 816 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange en 4096 (2^47); KZRange lft 1 262143; KZRange llv 0 262143;
     KZRange rem 1 (2^47); KZWr cur 1]
    [(src, 1)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in STEP; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fc8) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fe4) _ _ _ _) => (eapply CONT1 with (OP := en); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | eapply t2_lfacts_op; [exact LF0 | cbn [y_DST]; lia] | exact HO | exact HL | exact HM | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold STEP; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18fc8; 0x18fe4] 40%nat
    [KZRange SPV 816 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange en 4096 (2^47); KZRange lft 1 262143; KZRange llv 0 262143;
     KZRange rem 1 (2^47); KZWr cur 1]
    [(src, 1)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in STEP; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fc8) _ _ _ _) => (eapply (IHk _ OEND LLO LEND LOCV K ST0 HK HLOC CONT0) with (OP := OP); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact HO | exact HL | exact HM | exact ELF | exact HLF | exact EEN | exact HEN | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. | lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18fe4) _ _ _ _) => (eapply CONT1 with (OP := en); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | eapply t2_lfacts_op; [exact LF0 | cbn [y_DST]; lia] | exact HO | exact HL | exact HM | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
Qed.

Lemma t2_cpB_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P -> LOCV = 2 ->
  t2_sw P OEND LLO LEND LOCV K -> t2_cpB P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK HLOC CONT1. unfold t2_cpB.
  intros m1 w0 c8 c16 c48 c56 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs lft en cur src rem idx cidx raddr x1 x5 x6 x7 x8 x11 x12 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 INV LF HO HL HM ELF HLF EEN HEN HC ES ER HIDX HRING HCI HRA HRL HRM HRO.
  eapply (t2_cpB_aux (Z.to_nat (en - cur)) P OEND LLO LEND LOCV K ST HK HLOC CONT1) with (llv := llv) (mlv := mlv) (ofs := ofs) (lft := lft); first [eassumption | lia].
Qed.
