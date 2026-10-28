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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_end seqS_kit_al.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqs_none : forall (P : ssp) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
  seqs_mem P -> seqs_ranges P -> seqs_side P -> seqs_sep P -> v_nbSeq P = 0 -> v_LOC P = 2 ->
  evt usegs (seqs_post P)
    (MS (mkR (v_ra P) (Z_to_bv 64 (v_SPV P)) (v_gp P) (v_tp P) t0 t1 t2 (v_s0 P) (v_s1 P) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 (v_DST P))
             (Z_to_bv 64 (v_CAP P)) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (zlen (v_sq P))) (Z_to_bv 64 (v_nbSeq P)) a6 a7
             (v_s2 P) (v_s3 P) (v_s4 P) (v_s5 P) (v_s6 P) (v_s7 P) (v_s8 P) (v_s9 P) (v_s10 P) (v_s11 P) t3 t4 t5 t6)
        (v_F P) (Z_to_bv 64 0x1ac08) (v_fc P) None (v_m P) (seg_rom usegs)).
Proof.
  intros P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP NB0 LV.
  pose proof (seqs_p_last1 P) as PL1. pose proof RG as RG0. pose proof SEP as SEP0.
  assert (FE0 : seqs_fe P = v_fe P) by (unfold seqs_fe; rewrite NB0; reflexivity). rewrite FE0 in PL1.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_mem seqs_ranges seqs_side seqs_sep seqs_post seqs_saved v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in MEM, RG, SIDE, SEP, NB0, LV |- *.
  cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in PL1.
  destruct MEM as ((PT & REP & HH1 & HH3 & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & STK & MI).
  destruct (h5_view2 m DCTX ws HH5) as (H5O & H5L). pose proof H5O as H5V. unfold h5_vcells in H5V, H5O. rewrite L1, L2, L3, L4, LV in H5V. clear HH5 L1 L2 L3 L4 SQB PT HH1.
  unfold dctx_h3 in *. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  assert (PL : DST <= LITP /\ LBE + 32 <= DST + CAP /\ rdbl usegs m (DCTX + 30372) (DCTX + 95940)).
  { destruct SIDE as (_ & _ & _ & _ & D5). unfold seq_lit_placed, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz in D5.
    destruct D5 as [(E & _)|[(E & _)|(_ & A & B & C)]]; [lia | lia |]. split; [exact A|]. split; [exact B|]. replace (DCTX + 95940) with (DCTX + 30372 + 65568) by lia. exact C. }
  destruct PL as (PL1' & PL2 & XLIT). subst nbSeq.
  assert (RA : 592 <= SPV < 2^47 /\ 0 <= lo <= SPV - 592 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= DST < 2^47 /\ 32 <= CAP < 2^47 /\ 4096 <= DST + CAP < 2^47 /\
               4096 <= LITP < 2^47 /\ 4096 <= LBE < 2^47 /\ B0 <= DST /\ DST + CAP <= B1 /\ LITP <= LBE)
    by (unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH in RG; lia).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer in P1, P2, P5.
  assert (X1 : SPV <= DCTX \/ DCTX + 95992 <= SPV - 384) by (clear - P1 RA; lia).
  assert (X2 : SPV <= B0 \/ B1 <= SPV - 384) by (clear - P2 RA; lia).
  pose proof (proj1 SIDE) as D8.
  clear RG SIDE P1 P2 P3 P4 P5 P6 P7 P8.
  assert (MU : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - 592, SPV)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (MUL : munch [(SPV - 384, SPV)] m m) by apply munch_refl.
  assert (R0 : 592 <= SPV < 2^47 /\ 0 <= lo <= SPV - 592) by (clear - RA; lia).
  carve_frame 384%nat STK.
  hold RG0. hold SEP0. hold PL1. hold XLIT. hold LRD. hold PL1'. hold PL2. hold H5O.
  kx_autoLx [0x1b99c] 60%nat
    [KZRange SPV 592 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange CAP 32 (2^47); KZRange (DST + CAP) 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47);
     KZWr (SPV - 384) 384; KZDisj (SPV - 384) 384 DCTX 95992]
    [].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => first [kx_trap_fast | seqs_land_close] end).
  kx_mem. unfold held in *.
  lazymatch type of MUL with munch _ ?ma ?mb =>
    assert (XLIT2 : rdbl usegs mb (DCTX + 30372) (DCTX + 95940)) by (eapply (rdbl_transport usegs _ ma mb); [exact XLIT | exact MUL | intros x Hx; left; cbn [outside]; split; [lia|exact I]]);
    assert (H5O2 : rw_cells usegs mb (DCTX + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (wnth ws H5_litBufferLocation)])
      by (eapply rw_cells_transport; [exact H5O | exact MUL | lazymatch goal with W : wmono usegs ma mb |- _ => exact W end | cbn [disjoint_from cells_size csize Nat.add]; split; [lia|exact I]]) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply (PL1 mm _ _ _ _ _ (DST + CAP) DST LITP LBE (Z_to_bv 64 LITP) (wnth ws H5_litBufferLocation)); [exact RG0 | exact SEP0 | | split; [unfold h5_vcells; exact H5O2 | exact H5L] | exact FR | lia | lia | lia | lia | lia | lia | lia | exact XLIT2] end.
  cbn [seqs_xinv]. unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation.
  split; [do 3 eexists; exact REP|]. split; [exact HH3|]. split; [exact BUF|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact KXMI].
Qed.
