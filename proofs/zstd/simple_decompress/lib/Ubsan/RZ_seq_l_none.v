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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_end.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_eframe_merge : forall (P : slp) (m1 : fmem) ja jb jc a b c x y z,
  rw_cells usegs m1 (y_SPV P + -688) ([CB 96 ja; C8 a; CB 56 jb; C8 b; CB 72 jc; C8 c; CB 304 x; C8 y; CB 24 z] ++ seql_saved P) ->
  exists jd, rw_cells usegs m1 (y_SPV P + -688) ([CB 96 ja; C8 a; CB 56 jb; C8 b; CB 72 jc; C8 c; CB 336 jd] ++ seql_saved P).
Proof.
  intros P m1 ja jb jc a b c x y z FR. exists (x ++ le8 y ++ z).
  pose proof FR as [[WF _] _]. cbn [cells_wf cell_wf app] in WF. destruct WF as (W1 & _ & W2 & _ & W3 & _ & W4 & _ & W5 & WS).
  eapply rw_cells_recell; [exact FR | |].
  - cbn [cells_wf cell_wf app]. rewrite !length_app, length_le8, W4, W5. repeat split; try assumption.
  - cbn [cells_bytes cbytes app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma seql_none : forall (P : slp) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
  seql_mem P -> seql_ranges P -> seql_side P -> seql_sep P -> y_nbSeq P = 0 ->
  evt usegs (seql_post P)
    (MS (mkR (y_ra P) (Z_to_bv 64 (y_SPV P)) (y_gp P) (y_tp P) t0 t1 t2 (y_s0 P) (y_s1 P) (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (y_DST P))
             (Z_to_bv 64 (y_CAP P)) (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 (zlen (y_sq P))) (Z_to_bv 64 (y_nbSeq P)) a6 a7
             (y_s2 P) (y_s3 P) (y_s4 P) (y_s5 P) (y_s6 P) (y_s7 P) (y_s8 P) (y_s9 P) (y_s10 P) (y_s11 P) t3 t4 t5 t6)
        (y_F P) (Z_to_bv 64 0x17a94) (y_fc P) None (y_m P) (seg_rom usegs)).
Proof.
  intros P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP NB0.
  pose proof (seql_p_last1 P) as PL1. pose proof (seql_p_last2 P) as PL2. pose proof (seql_eframe_merge P) as EFM. pose proof RG as RG0. pose proof SEP as SEP0.
  assert (FE0 : seql_fe P = y_fe P) by (unfold seql_fe; rewrite NB0; reflexivity). rewrite FE0 in PL1, PL2.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_mem seql_ranges seql_side seql_sep seql_post seql_saved y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in MEM, RG, SIDE, SEP, NB0 |- *.
  cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in PL1, PL2, EFM.
  destruct MEM as ((PT & REP & HH1 & HH3 & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & STK & MI).
  destruct (h5_view2 m DCTX ws HH5) as (H5O & H5L). pose proof H5O as H5V. unfold h5_vcells in H5V, H5O. rewrite L1, L2, L3, L4 in H5V. clear HH5 L1 L2 L3 L4 SQB PT HH1.
  unfold dctx_h3 in *. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  subst nbSeq.
  assert (RA : 896 <= SPV < 2^47 /\ 0 <= lo <= SPV - 896 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= DST < 2^47 /\ 0 <= CAP < 2^47 /\ 4096 <= DST + CAP < 2^47 /\
               4096 <= LITP < 2^47 /\ 4096 <= LBE < 2^47 /\ B0 <= DST /\ DST + CAP <= B1 /\ LITP <= LBE)
    by (unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH in RG; lia).
  assert (PLS : LOC = 2 -> B0 <= LITP /\ LBE <= B1 /\ 32 <= CAP /\ rdbl usegs m (DCTX + 30372) (DCTX + 95940)).
  { intros E2. destruct SIDE as (_ & _ & _ & _ & D5). unfold seq_lit_placed, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz in D5.
    destruct D5 as [(E & _)|[(E & _)|(_ & A & B & C)]]; [exfalso; lia | exfalso; lia |]. split; [clear - A RA; lia|]. split; [clear - B RA; lia|]. split; [clear - A B RA; lia|]. replace (DCTX + 95940) with (DCTX + 30372 + 65568) by lia. exact C. }
  assert (PLB : LOC = 1 -> 4096 <= LITB < 2^47 /\ DST <= LITB <= DST + CAP) by (intros E1; destruct SIDE as (_ & _ & _ & _ & D5); unfold seq_lit_placed, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split in D5; destruct D5 as [(E & _)|[(_ & A & _)|(E & _)]]; [exfalso; lia | clear - A RA; lia | exfalso; lia]).
  assert (LOCK : (LOC = 0 /\ CAP <= 0) \/ (LOC = 0 /\ 1 <= CAP) \/ LOC = 1 \/ LOC = 2)
    by (destruct SIDE as (_ & _ & _ & D4 & _); unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split in D4; clear - D4; lia).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer in P1, P2, P4, P5.
  assert (X1 : SPV <= DCTX \/ DCTX + 95992 <= SPV - 688) by (clear - P1 RA; lia).
  assert (X2 : SPV <= B0 \/ B1 <= SPV - 688) by (clear - P2 RA; lia).
  assert (X3 : SPV <= LITP \/ LBE + 32 <= SPV - 688) by (clear - P4 RA; lia).
  assert (AL8 : Z.land DCTX 7 = 0) by (destruct SIDE as (A & _); change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact A).
  clear RG SIDE P1 P2 P3 P4 P5 P6 P7 P8.
  assert (MU : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - 896, SPV)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (MUL : munch [(SPV - 688, SPV)] m m) by apply munch_refl.
  assert (R0 : 896 <= SPV < 2^47 /\ 0 <= lo <= SPV - 896) by (clear - RA; lia).
  carve_frame 688%nat STK.
  destruct LOCK as [(LV & CZ)|[(LV & CZ)|[LV|LV]]].
  - subst LOC. assert (C0 : CAP = 0) by (clear - CZ RA; lia). subst CAP. assert (XLITC : 0 = 2 -> rdbl usegs m (DCTX + 30372) (DCTX + 95940)) by (intros HL2; exfalso; clear - HL2; lia). clear PLS PLB CZ.
    hold RG0. hold SEP0. hold PL1. hold PL2. hold EFM. hold XLITC. hold LRD. hold H5O.
    kx_autoLx [0x18330; 0x1ab6c; 0x1ac04] 80%nat
    [KZRange SPV 896 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47);
     KZWr (SPV - 688) 688; KZDisj (SPV - 688) 688 DCTX 95992]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; unfold held in *;
    lazymatch type of MUL with munch _ ?ma ?mb =>
      assert (LRD2 : rdbl usegs mb LITP (LBE + 32)) by (eapply (rdbl_transport usegs _ ma mb); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; split; [lia|exact I]]);
      assert (XLIT2 : 0 = 2 -> rdbl usegs mb (DCTX + 30372) (DCTX + 95940)) by (intros HL2; eapply (rdbl_transport usegs _ ma mb); [exact (XLITC HL2) | exact MUL | intros x Hx; left; cbn [outside]; split; [lia|exact I]]);
      assert (H5O2 : rw_cells usegs mb (DCTX + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (wnth ws H5_litBufferLocation)])
        by (eapply rw_cells_transport; [exact H5O | exact MUL | lazymatch goal with W : wmono usegs ma mb |- _ => exact W end | cbn [disjoint_from cells_size csize Nat.add]; split; [lia|exact I]]) end;
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18330) _ _ ?mm _) =>
      destruct (EFM mm _ _ _ _ _ _ _ _ _ FR) as (jd & FRE);
      eapply (PL1 mm _ _ _ jd _ DST LITP LBE (wnth ws H5_litBufferLocation)); [exact RG0 | exact SEP0 | | split; [unfold h5_vcells; exact H5O2 | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | lia | apply XLIT2; exfalso; lia]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ab6c) _ _ ?mm _) =>
      destruct (EFM mm _ _ _ _ _ _ _ _ _ FR) as (jd & FRE);
      eapply (PL2 mm _ _ _ jd _ DST LITP LBE (wnth ws H5_litBufferLocation)); [exact RG0 | exact SEP0 | | split; [unfold h5_vcells; exact H5O2 | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | eapply rdbl_sub; [exact LRD2 | lia | lia]]
    end;
    (cbn [seql_xinv]; unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation;
     split; [do 3 eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| exact KXMI]).
  - subst LOC. assert (XLITC : 0 = 2 -> rdbl usegs m (DCTX + 30372) (DCTX + 95940)) by (intros HL2; exfalso; clear - HL2; lia). clear PLS PLB.
    hold RG0. hold SEP0. hold PL1. hold PL2. hold EFM. hold XLITC. hold LRD. hold H5O.
    kx_autoLx [0x18330; 0x1ab6c; 0x1ac04] 80%nat
    [KZRange SPV 896 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange CAP 1 (2^47); KZRange (DST + CAP) 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47);
     KZWr (SPV - 688) 688; KZDisj (SPV - 688) 688 DCTX 95992]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; unfold held in *;
    lazymatch type of MUL with munch _ ?ma ?mb =>
      assert (LRD2 : rdbl usegs mb LITP (LBE + 32)) by (eapply (rdbl_transport usegs _ ma mb); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; split; [lia|exact I]]);
      assert (XLIT2 : 0 = 2 -> rdbl usegs mb (DCTX + 30372) (DCTX + 95940)) by (intros HL2; eapply (rdbl_transport usegs _ ma mb); [exact (XLITC HL2) | exact MUL | intros x Hx; left; cbn [outside]; split; [lia|exact I]]);
      assert (H5O2 : rw_cells usegs mb (DCTX + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (wnth ws H5_litBufferLocation)])
        by (eapply rw_cells_transport; [exact H5O | exact MUL | lazymatch goal with W : wmono usegs ma mb |- _ => exact W end | cbn [disjoint_from cells_size csize Nat.add]; split; [lia|exact I]]) end;
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18330) _ _ ?mm _) =>
      destruct (EFM mm _ _ _ _ _ _ _ _ _ FR) as (jd & FRE);
      eapply (PL1 mm _ _ _ jd _ DST LITP LBE (wnth ws H5_litBufferLocation)); [exact RG0 | exact SEP0 | | split; [unfold h5_vcells; exact H5O2 | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | lia | apply XLIT2; exfalso; lia]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ab6c) _ _ ?mm _) =>
      destruct (EFM mm _ _ _ _ _ _ _ _ _ FR) as (jd & FRE);
      eapply (PL2 mm _ _ _ jd _ DST LITP LBE (wnth ws H5_litBufferLocation)); [exact RG0 | exact SEP0 | | split; [unfold h5_vcells; exact H5O2 | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | eapply rdbl_sub; [exact LRD2 | lia | lia]]
    end;
    (cbn [seql_xinv]; unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation;
     split; [do 3 eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| exact KXMI]).
  - subst LOC. assert (XLITC : 1 = 2 -> rdbl usegs m (DCTX + 30372) (DCTX + 95940)) by (intros HL2; exfalso; clear - HL2; lia). pose proof (PLB eq_refl) as RLB. clear PLS PLB.
    hold RG0. hold SEP0. hold PL1. hold PL2. hold EFM. hold XLITC. hold LRD. hold H5O.
    kx_autoLx [0x18330; 0x1ab6c; 0x1ac04] 80%nat
    [KZRange SPV 896 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange LITB 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47);
     KZWr (SPV - 688) 688; KZDisj (SPV - 688) 688 DCTX 95992]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; unfold held in *;
    lazymatch type of MUL with munch _ ?ma ?mb =>
      assert (LRD2 : rdbl usegs mb LITP (LBE + 32)) by (eapply (rdbl_transport usegs _ ma mb); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; split; [lia|exact I]]);
      assert (XLIT2 : 1 = 2 -> rdbl usegs mb (DCTX + 30372) (DCTX + 95940)) by (intros HL2; eapply (rdbl_transport usegs _ ma mb); [exact (XLITC HL2) | exact MUL | intros x Hx; left; cbn [outside]; split; [lia|exact I]]);
      assert (H5O2 : rw_cells usegs mb (DCTX + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (wnth ws H5_litBufferLocation)])
        by (eapply rw_cells_transport; [exact H5O | exact MUL | lazymatch goal with W : wmono usegs ma mb |- _ => exact W end | cbn [disjoint_from cells_size csize Nat.add]; split; [lia|exact I]]) end;
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18330) _ _ ?mm _) =>
      destruct (EFM mm _ _ _ _ _ _ _ _ _ FR) as (jd & FRE);
      eapply (PL1 mm _ _ _ jd _ DST LITP LBE (wnth ws H5_litBufferLocation)); [exact RG0 | exact SEP0 | | split; [unfold h5_vcells; exact H5O2 | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | lia | apply XLIT2; exfalso; lia]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ab6c) _ _ ?mm _) =>
      destruct (EFM mm _ _ _ _ _ _ _ _ _ FR) as (jd & FRE);
      eapply (PL2 mm _ _ _ jd _ DST LITP LBE (wnth ws H5_litBufferLocation)); [exact RG0 | exact SEP0 | | split; [unfold h5_vcells; exact H5O2 | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | eapply rdbl_sub; [exact LRD2 | lia | lia]]
    end;
    (cbn [seql_xinv]; unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation;
     split; [do 3 eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| exact KXMI]).
  - subst LOC. destruct (PLS eq_refl) as (PD1 & PD2 & C32 & XLIT2S). assert (XLITC : 2 = 2 -> rdbl usegs m (DCTX + 30372) (DCTX + 95940)) by (intros _; exact XLIT2S). clear PLS PLB XLIT2S.
    hold RG0. hold SEP0. hold PL1. hold PL2. hold EFM. hold XLITC. hold LRD. hold H5O.
    kx_autoLx [0x18330; 0x1ab6c; 0x1ac04] 80%nat
    [KZRange SPV 896 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange CAP 32 (2^47); KZRange (DST + CAP) 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47);
     KZWr (SPV - 688) 688; KZDisj (SPV - 688) 688 DCTX 95992]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; unfold held in *;
    lazymatch type of MUL with munch _ ?ma ?mb =>
      assert (LRD2 : rdbl usegs mb LITP (LBE + 32)) by (eapply (rdbl_transport usegs _ ma mb); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; split; [lia|exact I]]);
      assert (XLIT2 : 2 = 2 -> rdbl usegs mb (DCTX + 30372) (DCTX + 95940)) by (intros HL2; eapply (rdbl_transport usegs _ ma mb); [exact (XLITC HL2) | exact MUL | intros x Hx; left; cbn [outside]; split; [lia|exact I]]);
      assert (H5O2 : rw_cells usegs mb (DCTX + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (wnth ws H5_litBufferLocation)])
        by (eapply rw_cells_transport; [exact H5O | exact MUL | lazymatch goal with W : wmono usegs ma mb |- _ => exact W end | cbn [disjoint_from cells_size csize Nat.add]; split; [lia|exact I]]) end;
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18330) _ _ ?mm _) =>
      destruct (EFM mm _ _ _ _ _ _ _ _ _ FR) as (jd & FRE);
      eapply (PL1 mm _ _ _ jd _ DST LITP LBE (wnth ws H5_litBufferLocation)); [exact RG0 | exact SEP0 | | split; [unfold h5_vcells; exact H5O2 | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | lia | apply XLIT2; reflexivity]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ab6c) _ _ ?mm _) =>
      destruct (EFM mm _ _ _ _ _ _ _ _ _ FR) as (jd & FRE);
      eapply (PL2 mm _ _ _ jd _ DST LITP LBE (wnth ws H5_litBufferLocation)); [exact RG0 | exact SEP0 | | split; [unfold h5_vcells; exact H5O2 | exact H5L] | exact FRE | lia | lia | lia | lia | lia | lia | eapply rdbl_sub; [exact LRD2 | lia | lia]]
    end;
    (cbn [seql_xinv]; unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation;
     split; [do 3 eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| exact KXMI]).
Qed.
