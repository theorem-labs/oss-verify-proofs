(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit ABytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_z4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s3_iface AF_huf_z4s2_iface AF_huf_z4d_iface AF_huf_z4sb AF_huf_z4s0.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.

Lemma z4f_cons : forall m A c cs, rw_cells bsegs m A (c :: cs) <->
  rw_cells bsegs m A [c] /\ rw_cells bsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs. change (c :: cs) with ([c] ++ cs). rewrite ABytes.rw_cells_app.
  cbn [cells_size]. rewrite ?Nat.add_0_r. reflexivity.
Qed.

Ltac z4f_split :=
  repeat match goal with H : rw_cells _ _ _ (_ :: _ :: _) |- _ => apply z4f_cons in H; destruct H as [?Ha ?Hb] end.
Ltac z4f_gsplit :=
  repeat match goal with |- rw_cells _ _ _ (_ :: _ :: _) => apply z4f_cons; split end.
Lemma z4f_at : forall m A B cs, rw_cells bsegs m A cs -> B = A -> rw_cells bsegs m B cs.
Proof. intros m A B cs H ->. exact H. Qed.
Ltac z4f_close :=
  match goal with H : rw_cells _ ?mm _ [?c] |- rw_cells _ ?mm _ [_] =>
    eapply z4f_at; [exact H | cbn [csize]; lia] end.

Lemma z4f_spd : forall m (A : Z) (ja jb jc j2 : list byte) (x y z u v : word),
  rw_cells bsegs m A [CB 48 ja; C8 x; CB 16 jb; C8 y; C8 z; CB 16 jc; C8 u; C8 v; CB 160 j2] ->
  exists (w0 w1 w2 w3 w4 w5 w7 w8 w11 w12 : word) (j4 j3 j2' j1 : list byte),
    rw_cells bsegs m A (SPD w0 w1 w2 w3 w4 w5 x w7 w8 y z w11 w12 u v)
    /\ rw_cells bsegs m (A + 120) [CB 40 j4] /\ rw_cells bsegs m (A + 160) [CB 40 j3]
    /\ rw_cells bsegs m (A + 200) [CB 40 j2'] /\ rw_cells bsegs m (A + 240) [CB 40 j1].
Proof.
  intros m A ja jb jc j2 x y z u v H.
  z4f_split.
  repeat match goal with
  | H : rw_cells _ _ _ [CB 48 _] |- _ => apply (rw_cells_split_CB _ _ _ [] _ _ [] [8;8;8;8;8;8]%nat) in H; [| reflexivity]
  | H : rw_cells _ _ _ [CB 16 _] |- _ => apply (rw_cells_split_CB _ _ _ [] _ _ [] [8;8]%nat) in H; [| reflexivity]
  | H : rw_cells _ _ _ [CB 160 _] |- _ => apply (rw_cells_split_CB _ _ _ [] _ _ [] [40;40;40;40]%nat) in H; [| reflexivity]
  end.
  cbn [app mk_CB_cells] in *.
  z4f_split.
  repeat match goal with H : rw_cells _ _ _ [CB 8 _] |- _ =>
    let w := fresh "w" in let HW := fresh "HW" in destruct (c8_of_CB _ _ _ H) as (w & HW & _); clear H end.
  do 14 eexists. unfold SPD.
  repeat match goal with |- _ /\ _ => split end.
  all: z4f_gsplit.
  all: cbn [csize] in *.
  all: z4f_close.
Qed.

Lemma z4f_blk_unp : forall (AI : AMallocIface) L RNG st LB m0 p A k m (S : Z),
  AHEAP AI L RNG st LB m0 -> In (HB p A k) LB -> KHIGH <= S - 384 ->
  munch [(S - 384, S)] m0 m -> unpoisoned m A (A + k).
Proof.
  intros AI L RNG st LB m0 p A k m S AH IN KH MU.
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH IN) as (_ & AR & _ & _ & SD & _).
  pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
  unfold ablock_range in AR. destruct AR as (_ & K0 & _ & AM).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI in B1.
  assert (U0 : unpoisoned m0 A (A + k))
    by (apply ablock_unpoisoned; [exact SD | exact (z4_mod16_8 _ AM) | lia | lia | lia]).
  eapply unpoisoned_munch; [exact U0 | exact MU |].
  rewrite z4_shad_span.
  apply appW_shadow_disjoint; [apply appW_cons; [lia | exact appW_nil] | lia | unfold KEND; lia].
Qed.

Ltac z4f_pick :=
  match goal with H : rw_cells _ ?mm _ _ |- rw_cells _ ?mm _ _ =>
    eapply z4f_at; [exact H | cbn [csize] in *; lia] end.

Lemma z4f_epi_exit : forall (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word)
    (fc : bv 32) (m0 mm : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs je : list byte)
    (z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
  lo <= bv_unsigned sp - 384 -> 2^46 <= bv_unsigned sp <= 2^47 -> rng RNG (bv_unsigned sp - 384) 384 -> rng_aimg RNG ->
  (exists buf, u8arr bsegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap) ->
  bytes_at bsegs mm SS (map (Z_to_bv 8) src) -> bytes_at bsegs mm (DT + 4) cbs ->
  bytes_at bsegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
  stk bsegs mm lo (bv_unsigned sp + -384) -> rw_cells bsegs mm (bv_unsigned sp + -384) [CB 280 je] ->
  rw_cells bsegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs mm -> munch [(lo, bv_unsigned sp); (DST, DST + dcap)] m0 mm -> wmono bsegs m0 mm ->
  evtF bsegs RNG (z4d_postA RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc DST dcap lo m0)
    (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16
             z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31)
        FR (Z_to_bv 64 AZ4_DEPI) fc None mm (seg_rom bsegs)).
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 mm DST dcap SS DT mtl tl lo src cbs je
    z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 LOS SPB RS RI HB HS HC HD ST CBH FRB MI MU WM.
  apply (rw_cells_split_CB _ _ _ [] _ _ [] [120;40;40;40;40]%nat) in CBH; [| reflexivity].
  cbn [app mk_CB_cells] in CBH.
  repeat match goal with H : rw_cells _ _ _ (CB _ _ :: _ :: _) |- _ => apply z4f_cons in H; destruct H as [?Ha ?Hb] end.
  pose proof (z4d_epi RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs
                LOS SPB RS RI) as E.
  unfold z4epi_hyp in E. eapply E.
  unfold AF_huf_z4s3_iface.Z4SF.
  refine (conj HB (conj HS (conj HC (conj HD (conj ST _))))).
  do 10 (split; [first [z4f_pick | reflexivity] |]).
  exact (conj FRB (conj MI (conj MU WM))).
Qed.

Theorem z4d_proofA : z4i1_stmtA ->
  (forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
          (rng_fs : alayout -> footprint -> Prop)
          (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
          (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
          (SBL SBH : Z) (rstk : region),
    z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
    z4s2_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q) ->
  z4d_stmtA.
Proof.
  intros I1 Z2 AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0
    DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk
    AH NFK ABL MTL TLM HDT TOK ECB LCB DSTF DC BYS NSM S16 SRCB DJ1 DJ2 DJ3 LOA LOS SPT SP16 TPA HINV
    RCL RLO RHI RRL RRS WSK WIM WIS WFS.
  unfold z4d_goal. intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 OUT SRC CBS HDR STK MI.
  unfold Z4D_STACK in LOS.
  assert (CTX : z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk).
  { unfold z4ctx. repeat match goal with |- _ /\ _ => split end. all: first [assumption | lia]. }
  destruct TOK as (TLB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & GOT & _ & _ & SHB & _).
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (_ & DAR & DRA & DRS & _).
  pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HDT) as (DB1 & DB2 & DB3). cbn [ab_addr ab_size] in DB1, DB2, DB3.
  unfold ablock_range in DAR. destruct DAR as (_ & _ & _ & DAM).
  pose proof (Z.pow_le_mono_r 2 1 mtl ltac:(lia) ltac:(lia)) as PM. rewrite Z.pow_1_r in PM.
  assert (PT : 2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia).
  unfold DTABLE_BYTES, HufHarness.DT_BYTES in *. unfold AIMG_HI in DB1.
  assert (SPB : 2^46 <= bv_unsigned sp <= 2^47) by lia.
  assert (LOS' : lo <= bv_unsigned sp - 384) by lia.
  assert (RS : rng RNG (bv_unsigned sp - 384) 384) by (eapply rng_sub; [exact WSK | lia | lia]).
  assert (KH : KHIGH <= bv_unsigned sp - 384) by (unfold KHIGH; lia).
  assert (DSB : 0 <= DST /\ (0 < dcap -> 4096 <= DST) /\ DST + dcap <= 2^47).
  { destruct DSTF as [[-> ->] | (pb & IN)]; [lia|].
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    unfold AIMG_HI in B1. lia. }
  destruct DSB as (DS0 & DS1 & DS2).
  assert (RD4 : rng RNG DT 4) by (eapply rng_sub; [exact DRA | lia | lia]).
  assert (RSD : rng RNG (shad DT) 1).
  { eapply rng_sub; [exact DRS | lia |]. rewrite shlenE.
    pose proof (Z.div_le_lower_bound (4 * (1 + 2 ^ mtl) + 7) 8 1 ltac:(lia) ltac:(lia)). lia. }
  assert (UD : forall mm, munch [(bv_unsigned sp - 384, bv_unsigned sp)] m0 mm -> unpoisoned mm DT (DT + 8)).
  { intros mm MU. eapply unpoisoned_sub; [exact (z4f_blk_unp AI L RNG st LB m0 pdt DT _ mm (bv_unsigned sp) AH HDT KH MU)
                                         | lia | lia]. }
  assert (SBK : 10 <= zlen src -> 4096 <= SBL /\ SBL mod 8 = 0 /\ SBL <= SS /\ SS + zlen src <= SBH /\ SBH <= 2^47
                 /\ SBH <= lo /\ rng RNG SS (zlen src) /\ rng RNG (shad SBL) (shlen (SBH - SBL + 7))
                 /\ forall mm, munch [(bv_unsigned sp - 384, bv_unsigned sp)] m0 mm -> unpoisoned mm SBL SBH).
  { intros N10. destruct (SRCB ltac:(lia)) as (p & IN & S1 & S2).
    pose proof (AI_block AI _ _ _ _ _ _ _ _ AH IN) as (_ & SAR & SRA & SRS & _).
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (SB1 & SB2 & SB3). cbn [ab_addr ab_size] in SB1, SB2, SB3.
    unfold ablock_range in SAR. destruct SAR as (_ & _ & _ & SAM). unfold AIMG_HI in SB1.
    split; [lia|]. split; [exact (z4_mod16_8 _ SAM)|]. do 4 (split; [lia|]).
    split; [eapply rng_sub; [exact SRA | lia | lia]|]. split; [exact SRS|].
    intros mm MU. eapply unpoisoned_sub; [exact (z4f_blk_unp AI L RNG st LB m0 p SBL _ mm (bv_unsigned sp) AH IN KH MU)
                                         | lia | lia]. }
  assert (TRF : forall mm, munch [(bv_unsigned sp - 384, bv_unsigned sp)] m0 mm -> wmono bsegs m0 mm ->
     (exists buf, u8arr bsegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
     /\ bytes_at bsegs mm SS (map (Z_to_bv 8) src) /\ bytes_at bsegs mm (DT + 4) cbs
     /\ bytes_at bsegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]
     /\ munch [(lo, bv_unsigned sp); (DST, DST + dcap)] m0 mm).
  { intros mm MU WM. split; [|split; [|split; [|split]]].
    - destruct DSTF as [[-> ->] | (pb & IN)].
      + exists (@nil Z). cbn [map length]. split; [|reflexivity]. unfold u8arr. split; [apply bytes_at_nil; lia|].
        unfold wr_at. cbn [length]. split; [lia | split; [lia | intros i Hi; exfalso; lia]].
      + pose proof (AI_block AI _ _ _ _ _ _ _ _ AH IN) as (_ & _ & _ & _ & _ & WA & _).
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (B1 & B2 & _). cbn [ab_addr ab_size] in B1, B2.
        apply (z4_wr_u8arr mm DST dcap); [exact (wr_at_transport _ _ _ _ _ WA WM) | lia | exact B1].
    - destruct (Z.eq_dec (zlen src) 0) as [Z0 | NZ].
      + pose proof (bytes_at_bound _ _ _ _ SRC) as BB. rewrite length_map in BB.
        assert (E : src = []) by (apply length_zero_iff_nil; lia). rewrite E. cbn [map]. apply bytes_at_nil. lia.
      + eapply bytes_at_transport; [exact SRC | exact MU |]. rewrite length_map.
        destruct (SRCB ltac:(lia)) as (p & IN & S1 & S2).
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
        cbn [disjoint_from]. split; [lia | exact I].
    - eapply bytes_at_transport; [exact CBS | exact MU |]. cbn [disjoint_from]. split; [lia | exact I].
    - eapply bytes_at_transport; [exact HDR | exact MU |]. cbn [disjoint_from length]. split; [lia | exact I].
    - eapply munch_weaken; [| exact MU]. intros x X. cbn [outside] in X. destruct X as (X1 & X2 & _).
      cbn [outside]. split; [lia | exact I]. }
  apply (z4s0_entry _ RNG m0 FR fc ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           DST dcap SS DT lo mtl tl SBL SBH src STK MI GOT SHB LOS' RS WIM SPB SP16 DS0 DS1 DS2 DC NSM
           ltac:(lia) ltac:(lia) (z4_mod16_8 _ DAM) MTL ltac:(lia) SRC HDR RD4 RSD UD SBK).
  - intros mm je z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31
      ST' CB' FRB MI' MU' WM'.
    destruct (TRF mm MU' WM') as (OUT' & SRC' & CBS' & HDR' & MUD).
    exact (z4f_epi_exit RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 mm DST dcap SS DT mtl tl lo src cbs je
             z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31
             LOS' SPB RS WIM OUT' SRC' CBS' HDR' ST' CB' FRB MI' MUD WM').
  - intros mm ja jb jc j2 l1 l2 l3 z1 z5 z6 z7 z10 z12 z13 z14 z16 z17 z24 z27 z28 z29 z30 z31
      L1 L2 L3 LS D6 N10 ST' RW FRB MI' MU' WM'.
    destruct (TRF mm MU' WM') as (OUT' & SRC' & CBS' & HDR' & MUD).
    destruct (z4f_spd _ _ _ _ _ _ _ _ _ _ _ RW)
      as (w0 & w1 & w2 & w3 & w4 & w5 & w7 & w8 & w11 & w12 & j4 & j3 & j2' & j1 & SPDH & H4 & H3 & H2 & H1).
    pose proof (Z2 (z4d_postA RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc DST dcap lo m0)
                  AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0
                  DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk CTX) as G2.
    pose proof (z4d_epi RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs
                  LOS' SPB RS WIM) as E.
    apply (I1 _ AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0
             DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk CTX G2 E mm l1 l2 l3
             w0 w1 w2 w3 w4 w5 w7 w8 w11 w12 j4 j3 j2' j1); [| exact L1 | exact L2 | exact L3 | exact LS | exact D6 | exact N10].
    unfold AF_huf_z4s3_iface.Z4SF.
    refine (conj OUT' (conj SRC' (conj CBS' (conj HDR' (conj ST' _))))).
    do 10 (split; [first [z4f_pick | reflexivity] |]).
    exact (conj FRB (conj MI' (conj MUD WM'))).
Qed.

End CANSEC1.
