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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma seql_p_exit0 : forall (P : slp) m1 jpre r loc (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  y_lo P <= y_SPV P - 896 -> 0 <= y_SPV P < 2^47 -> 4096 <= y_lo P ->
  seql_xinv P m1 (seql_fe P) -> h5_viewed m1 (y_DCTX P) (y_ws P) loc ->
  rw_cells usegs m1 (y_SPV P + -688) (CB 584 jpre :: seql_saved P) ->
  0 <= r < 2^64 -> (zd_is_error r = true \/ r <= y_CAP P) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 r) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1abb4) (y_fc P) None m1 (seg_rom usegs)).
Proof.
  intros [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws] m1 jpre r loc x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 G14 G15 G16 XI H5V FR RR RES.
  unfold seql_fe in *. cbn [seql_xinv seql_post seql_saved y_SPV y_lo y_gp y_tp y_F y_fc y_CAP y_nbSeq y_fe y_DCTX y_ws] in *.
  destruct XI as ((r0' & r1' & r2' & REP) & H3 & BUF & STK & MU & WM & MI1).
  apply h5_close in H5V.
  unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  hold REP. hold H3. hold BUF. hold H5V.
  kx_run [] 20%nat [KZRange SPV 896 (2^47)] [].
  unfold held in *.
  release_frame FR STK SPV.
  zstep.
  apply evt_done. unfold zd_seq_split_post.
  do 15 eexists. exists r, r0', r1', r2', (wupd ws H5_litBufferLocation loc).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact STK|]. split; [exact BUF|].
  split; [exact REP|]. split; [exact H3|]. split; [exact H5V|].
  split; [intros i Hi; apply wnth_wupd_other; exact Hi|]. split; [exact RR| exact RES].
Qed.

Lemma seql_null : forall (P : slp) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
  seql_mem P -> seql_side P -> seql_sep P -> y_nbSeq P = 0 -> y_DST P = 0 -> y_CAP P = 0 ->
  4096 <= y_DCTX P -> y_DCTX P + DCTX_SIZEOF < 2^47 -> 4096 <= y_LITP P -> y_LITP P <= y_LBE P -> y_LBE P + WILDCOPY_OVERLENGTH < 2^47 ->
  y_lo P <= y_SPV P - 896 -> 0 <= y_SPV P < 2^47 -> 4096 <= y_lo P ->
  evt usegs (seql_post P)
    (MS (mkR (y_ra P) (Z_to_bv 64 (y_SPV P)) (y_gp P) (y_tp P) t0 t1 t2 (y_s0 P) (y_s1 P) (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (y_DST P))
             (Z_to_bv 64 (y_CAP P)) (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 (zlen (y_sq P))) (Z_to_bv 64 (y_nbSeq P)) a6 a7
             (y_s2 P) (y_s3 P) (y_s4 P) (y_s5 P) (y_s6 P) (y_s7 P) (y_s8 P) (y_s9 P) (y_s10 P) (y_s11 P) t3 t4 t5 t6)
        (y_F P) (Z_to_bv 64 0x17a94) (y_fc P) None (y_m P) (seg_rom usegs)).
Proof.
  intros P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM SIDE SEP NB0 D0 C0 G1 G2 G11 G12 G13 G14 G15 G16.
  pose proof (seql_p_exit0 P) as PEXIT.
  assert (FE0 : seql_fe P = y_fe P) by (unfold seql_fe; rewrite NB0; reflexivity). rewrite FE0 in PEXIT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_mem seql_side seql_sep seql_post seql_saved y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in MEM, SIDE, SEP, NB0, D0, C0, G1, G2, G11, G12, G13, G14, G15, G16 |- *.
  cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in PEXIT.
  destruct MEM as ((PT & REP & HH1 & HH3 & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & STK & MI).
  destruct (h5_view2 m DCTX ws HH5) as (H5O & H5L). pose proof H5O as H5V. unfold h5_vcells in H5V, H5O. rewrite L1, L2, L3, L4 in H5V. clear HH5 L1 L2 L3 L4 SQB PT HH1 LRD.
  unfold dctx_h3 in *. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  subst nbSeq. subst DST. subst CAP.
  assert (RA : 896 <= SPV < 2^47 /\ 0 <= lo <= SPV - 896 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= LITP < 2^47 /\ 4096 <= LBE < 2^47 /\ 0 <= LBE - LITP < 2^47)
    by (unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH in *; lia).
  assert (AL8 : Z.land DCTX 7 = 0) by (destruct SIDE as (A & _); change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact A).
  assert (LOCK : LOC = 0 \/ (LOC = 1 /\ LITB = 0)).
  { destruct SIDE as (_ & _ & _ & _ & D5). unfold seq_lit_placed, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, WILDCOPY_OVERLENGTH in D5.
    destruct D5 as [(E & _)|[(E & A & _)|(_ & A & B & _)]]; [left; exact E | right; split; [exact E | clear - A; lia] | exfalso; clear - A B G11 G12; lia]. }
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer in P1, P2.
  assert (X1 : SPV <= DCTX \/ DCTX + 95992 <= SPV - 688) by (clear - P1 RA; lia).
  assert (X2 : SPV <= B0 \/ B1 <= SPV - 688) by (clear - P2 RA; lia).
  clear SIDE P1 P2 P3 P4 P5 P6 P7 P8.
  assert (MU : munch [(0, 0 + 0); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - 896, SPV)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (MUL : munch [(SPV - 688, SPV)] m m) by apply munch_refl.
  assert (R0 : 896 <= SPV < 2^47 /\ 0 <= lo <= SPV - 896) by (clear - RA; lia).
  carve_frame 688%nat STK.
  destruct LOCK as [LV|(LV & PLB)].
  - subst LOC.
    hold PEXIT. hold H5O.
    kx_autoLx [0x1abb4; 0x1ac04] 160%nat
    [KZRange SPV 896 (2^47); KZRange DCTX 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47); KZRange (LBE - LITP) 0 (2^47);
     KZWr (SPV - 688) 688; KZDisj (SPV - 688) 688 DCTX 95992]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; unfold held in *;
    lazymatch type of MUL with munch _ ?ma ?mb =>
      assert (H5O2 : rw_cells usegs mb (DCTX + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (wnth ws H5_litBufferLocation)])
        by (eapply rw_cells_transport; [exact H5O | exact MUL | lazymatch goal with W : wmono usegs ma mb |- _ => exact W end | cbn [disjoint_from cells_size csize Nat.add]; split; [lia|exact I]]) end;
    (apply (rw_cells_forget _ _ _ 9%nat 584%nat) in FR; [|reflexivity]); cbn [skipn app] in FR;
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?rr) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _) =>
      eapply (PEXIT mm _ rr (wnth ws H5_litBufferLocation)); [lia | lia | lia | | split; [unfold h5_vcells; exact H5O2 | exact H5L] | exact FR | lia | first [left; reflexivity | right; lia]] end;
    (cbn [seql_xinv]; unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation;
     split; [do 3 eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| exact KXMI]).
  - subst LOC. assert (LB0 : LITB = 0) by (clear - PLB; lia). subst LITB.
    hold PEXIT. hold H5O.
    kx_autoLx [0x1abb4; 0x1ac04] 160%nat
    [KZRange SPV 896 (2^47); KZRange DCTX 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47); KZRange (LBE - LITP) 0 (2^47);
     KZWr (SPV - 688) 688; KZDisj (SPV - 688) 688 DCTX 95992]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; unfold held in *;
    lazymatch type of MUL with munch _ ?ma ?mb =>
      assert (H5O2 : rw_cells usegs mb (DCTX + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (wnth ws H5_litBufferLocation)])
        by (eapply rw_cells_transport; [exact H5O | exact MUL | lazymatch goal with W : wmono usegs ma mb |- _ => exact W end | cbn [disjoint_from cells_size csize Nat.add]; split; [lia|exact I]]) end;
    (apply (rw_cells_forget _ _ _ 9%nat 584%nat) in FR; [|reflexivity]); cbn [skipn app] in FR;
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?rr) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _) =>
      eapply (PEXIT mm _ rr (wnth ws H5_litBufferLocation)); [lia | lia | lia | | split; [unfold h5_vcells; exact H5O2 | exact H5L] | exact FR | lia | first [left; reflexivity | right; lia]] end;
    (cbn [seql_xinv]; unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation;
     split; [do 3 eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| exact KXMI]).
Qed.
