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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s2_iface AF_huf_z4d_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From Stdlib Require Import Wf_nat.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Frame MState.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s1_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_z4s1a.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.

Lemma lc_blk : forall AI L RNG st LB m p A k, AHEAP AI L RNG st LB m -> In (HB p A k) LB ->
  1 <= k /\ ablk A (A + k) /\ A + k <= ATOP /\ A mod 16 = 0 /\ AIMG_HI <= A /\ A + k + 8 <= 2^47 /\
  rng RNG A k /\ rng RNG (shad A) (shlen (k + 7)).
Proof.
  intros AI L RNG st LB m p A k AH Hb.
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (HN & (R1 & R2 & R3 & R4) & W1 & W2 & _).
  pose proof (ablk_lin _ _ R1) as (A1 & A2 & A3 & A4).
  split; [lia|]. split; [exact R1|]. split; [lia|]. split; [exact R4|]. split; [lia|]. split; [lia|].
  split; [exact W1|exact W2].
Qed.

Lemma lc_ablk_ap : forall a k, ablk a (a + k) -> 0 <= k -> KXGoM.apart a k ASHOFF (ATOP / 8 + 1).
Proof.
  intros a k H HL. pose proof (@ATOP_lo rc). pose proof (@ATOP_hi rc).
  unfold KXGoM.apart, ablk, AIMG_HI, KLS, ASHOFF in *. lia.
Qed.

Lemma lc_stk_ap : forall a, ATOP + 4096 <= a -> KXGoM.apart a 384 ASHOFF (ATOP / 8 + 1).
Proof.
  intros a H. pose proof (@ATOP_lo rc). pose proof (@ATOP_hi rc).
  unfold KXGoM.apart, ASHOFF in *. lia.
Qed.

Lemma lc_pow : forall t u, 1 <= t -> t <= u -> u <= 12 -> (2 <= 2^t <= 4096) /\ 2^t <= 2^u.
Proof.
  intros t u H1 H2 H3.
  pose proof (Z.pow_le_mono_r 2 1 t ltac:(lia) H1) as A. rewrite Z.pow_1_r in A.
  pose proof (Z.pow_le_mono_r 2 t 12 ltac:(lia) ltac:(lia)) as B.
  pose proof (Z.pow_le_mono_r 2 t u ltac:(lia) H2) as C.
  lia.
Qed.

Lemma lc_m16 : forall a, a mod 16 = 0 -> a mod 8 = 0 /\ (a + 4) mod 4 = 0.
Proof. intros a H. Z.div_mod_to_equations. lia. Qed.

Lemma lc_seg : forall d, 0 <= d < 2^32 -> 0 <= (d + 3) / 4 <= 2^32.
Proof. intros d H. Z.div_mod_to_equations. lia. Qed.


Lemma z4bk_spd_merge : forall (mm : amem) (SP : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : word),
  rw_cells bsegs mm (SP + -384) [C8 w0] /\ rw_cells bsegs mm (SP + -376) [C8 w1] /\
    rw_cells bsegs mm (SP + -368) [C8 w2] /\ rw_cells bsegs mm (SP + -360) [C8 w3] /\
    rw_cells bsegs mm (SP + -352) [C8 w4; C8 w5; C8 w6; C8 w7] /\ rw_cells bsegs mm (SP + -320) [C8 w8] /\
    rw_cells bsegs mm (SP + -312) [C8 w9; C8 w10] /\ rw_cells bsegs mm (SP + -296) [C8 w11] /\
    rw_cells bsegs mm (SP + -288) [C8 w12] /\ rw_cells bsegs mm (SP + -280) [C8 w13; C8 w14] ->
  rw_cells bsegs mm (SP + -384) (SPD w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14).
Proof.
  intros mm SP w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). unfold SPD.
  change (rw_cells bsegs mm (SP + -384) ([C8 w0] ++ [C8 w1] ++ [C8 w2] ++ [C8 w3] ++ [C8 w4; C8 w5; C8 w6; C8 w7] ++ [C8 w8] ++ [C8 w9; C8 w10] ++ [C8 w11] ++ [C8 w12] ++ [C8 w13; C8 w14])).
  rewrite !rw_cells_app. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
  repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with
    | |- rw_cells _ _ ?B ?c =>
        match goal with Hx : rw_cells _ _ ?A c |- _ => replace B with A by lia; exact Hx end
    end.
Qed.

Lemma z4bk_bmap : forall (l : list byte), map (Z_to_bv 8) (map bv_unsigned l) = l.
Proof.
  induction l as [|b l IH]; cbn [map]; [reflexivity|].
  rewrite IH, stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma z4bk_bnil : forall (mm mm' : amem) A (bs : list byte),
  bytes_at bsegs mm A bs -> length bs = 0%nat -> bytes_at bsegs mm' A bs.
Proof.
  intros mm mm' A bs (H1 & H2 & _) HL. destruct bs; [|discriminate].
  split; [lia|]. split; [exact H2|]. intros i Hi. cbn [length] in Hi. lia.
Qed.

Ltac z4bk_bd :=
  lazymatch goal with
  | |- rw_cells _ _ ?A (BD4A ?c ?b ?jp (Z_to_bv _ ?p) ?s ?e) =>
      match goal with H : rw_cells _ _ A (BD4A c b jp (Z_to_bv _ ?p') s e) |- _ =>
        replace p with p' by lia; exact H end
  end.

Lemma z4_spd_split : forall (mm : amem) (SP : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : word),
  rw_cells bsegs mm (SP + -384) (SPD w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14) ->
  rw_cells bsegs mm (SP + -384) [C8 w0] /\ rw_cells bsegs mm (SP + -376) [C8 w1] /\
    rw_cells bsegs mm (SP + -368) [C8 w2] /\ rw_cells bsegs mm (SP + -360) [C8 w3] /\
    rw_cells bsegs mm (SP + -352) [C8 w4; C8 w5; C8 w6; C8 w7] /\ rw_cells bsegs mm (SP + -320) [C8 w8] /\
    rw_cells bsegs mm (SP + -312) [C8 w9; C8 w10] /\ rw_cells bsegs mm (SP + -296) [C8 w11] /\
    rw_cells bsegs mm (SP + -288) [C8 w12] /\ rw_cells bsegs mm (SP + -280) [C8 w13; C8 w14].
Proof.
  intros mm SP w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 H. unfold SPD in H.
  change (rw_cells bsegs mm (SP + -384) ([C8 w0] ++ [C8 w1] ++ [C8 w2] ++ [C8 w3] ++ [C8 w4; C8 w5; C8 w6; C8 w7] ++ [C8 w8] ++ [C8 w9; C8 w10] ++ [C8 w11] ++ [C8 w12] ++ [C8 w13; C8 w14])) in H.
  rewrite !rw_cells_app in H. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  destruct H as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with
    | |- rw_cells _ _ ?B ?c =>
        match goal with Hx : rw_cells _ _ ?A c |- _ => replace B with A by lia; exact Hx end
    end.
Qed.

(* [comment removed for export] *)
Section BR.
  Variable RNG : footprint.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop).
  Variables (AI : AMallocIface) (L : alayout) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
            (cells : list deltX2) (pdt : aptr) (SBL SBH : Z) (rstk : region).
  Hypothesis HC : z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk.
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DL := (tl + 256 * mtl).
  Notation DTH := (DT + DTABLE_BYTES mtl).
  Notation Zw z := (Z_to_bv 64 z) (only parsing).
  Notation Z4SF' := (Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).
  Notation BDS k b jp O o := (BD4A k (Zw b) jp (Zw (SS + O + o)) (Zw (SS + O)) (Zw (SS + O + 8))) (only parsing).
  Notation SPL w0 w4 w5 w7 k2 k4 k3 :=
    (SPD w0 (Zw (DST + 3 * seg)) (Zw (tl + 256 * mtl)) (Zw (DST + dcap - 7)) w4 w5 (Zw (DST + dcap)) w7 k2
         (Zw (DST + seg)) (Zw (DST + 2 * seg)) k4 k3 (Zw (DT + 4)) (Zw dcap)) (only parsing).
  Notation WM := [(SP + -384, SP + -104); (DST, DST + dcap)].
  Notation SF mm w0 w4 w5 w7 k1 k2 k3 k4 b1 b2 b3 b4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4 :=
    (Z4SF' mm (SPL w0 w4 w5 w7 k2 k4 k3) (BDS k4 b4 jp4 (6 + l1 + l2 + l3) o4) (BDS k3 b3 jp3 (6 + l1 + l2) o3)
       (BDS k2 b2 jp2 (6 + l1) o2) (BDS k1 b1 jp1 6 o1)) (only parsing).
  Notation MEM mm w0 w4 w5 w7 k1 k2 k3 k4 b1 b2 b3 b4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4 :=
    (z4L_mem SP DST dcap seg DT tl DL DT DTH cbs mm w0 w4 w5 w7
       (bv_unsigned k1) (bv_unsigned k2) (bv_unsigned k3) (bv_unsigned k4) b1 b2 b3 b4
       (SS + 6 + o1) (SS + 6 + l1 + o2) (SS + 6 + l1 + l2 + o3) (SS + 6 + l1 + l2 + l3 + o4) jp1 jp2 jp3 jp4
       (Zw (SS + 6)) (Zw (SS + (6 + l1))) (Zw (SS + (6 + l1 + l2))) (Zw (SS + (6 + l1 + l2 + l3)))
       (Zw (SS + 6 + 8)) (Zw (SS + (6 + l1) + 8)) (Zw (SS + (6 + l1 + l2) + 8)) (Zw (SS + (6 + l1 + l2 + l3) + 8)))
    (only parsing).


(* [comment removed for export] *)
  Lemma z4b_ctx : 6 <= dcap -> z4L_ctx RNG SP DST dcap seg DT tl mtl DL DT DTH cbs.
  Proof using HC.
    intros D6. pose proof HC as C.
    destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
                   & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
    destruct DSTF as [(E1 & E2)|(pb & HDB)]; [lia|].
    pose proof (lc_blk _ _ _ _ _ _ _ _ _ AH HDT) as (T1 & TB & T2 & T3 & T4 & T5 & WDT & WDTS).
    pose proof (lc_blk _ _ _ _ _ _ _ _ _ AH HDB) as (B1 & BB & B2 & B3 & B4 & B5 & WDB & WDBS).
    pose proof (AI_layout AI L RNG st LB m0 AH) as (Y1 & Y2 & Y3 & _).
    pose proof (@ATOP_lo rc) as HA1. pose proof (@ATOP_hi rc) as HA2.
    destruct TOK as (TK & _).
    assert (TL12 : 1 <= tl <= 12) by exact TK.
    pose proof (lc_pow tl mtl ltac:(lia) TLM ltac:(lia)) as (PW & PT).
    assert (DTE : DTABLE_BYTES mtl = 4 * (1 + 2^mtl)) by reflexivity.
    assert (AHI : 4096 <= AIMG_HI) by (unfold AIMG_HI; lia).
    assert (ALH : AIMG_LO <= AIMG_HI) by (unfold AIMG_LO, AIMG_HI; lia).
    pose proof (lc_m16 _ T3) as (T6 & T7). pose proof (lc_m16 _ B3) as (B6 & _).
    clear NFK ABL ECB BYS NSM SRCB DJ1 DJ2 TPA HINV RCL RLO RHI RRL RRS WIS WFS HDT HDB TK.
    unfold z4L_ctx.
    split; [eapply rng_sub; [exact WSK| lia| lia]|].
    split; [exact LCB|].
    split; [lia|].
    split; [lia|].
    split; [replace (DT + DTABLE_BYTES mtl - DT + 7) with (DTABLE_BYTES mtl + 7) by lia; exact WDTS|].
    split; [exact T6|].
    split; [lia|].
    split; [lia|].
    split; [exact WDBS|].
    split; [exact B6|].
    split; [eapply rng_sub; [exact WDT| lia| lia]|].
    split; [exact WDB|].
    split; [exact WIM|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [unfold KXGoM.apart; lia|].
    split; [unfold KXGoM.apart; lia|].
    split; [unfold KXGoM.apart; lia|].
    split; [unfold KXGoM.apart; lia|].
    split; [exact T7|].
    split; [lia|].
    split; [apply lc_seg; lia|].
    split; [reflexivity|].
    split; [exact TL12|].
    split; [exact MTL|].
    split; [exact PW|].
    split; [lia|].
    split; [lia|].
    split; [apply lc_stk_ap; lia|].
    split; [apply lc_ablk_ap; [exact BB| lia]|].
    split; [apply lc_ablk_ap; [eapply ablk_sub; [exact TB| lia| lia]| lia]|].
    lia.
  Qed.
  Lemma z4b_ssb : 0 < n -> 16 <= SS /\ SS + n + 8 <= 2^47.
  Proof using HC.
    intros N. pose proof HC as C.
    destruct C as (AH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16 & SRCB & _).
    destruct (SRCB N) as (p & HS & L1 & L2).
    pose proof (lc_blk _ _ _ _ _ _ _ _ _ AH HS) as (_ & _ & _ & _ & _ & A5 & _).
    lia.
  Qed.
(* [comment removed for export] *)
  Lemma z4b_mem : forall mm w0 w4 w5 w7 k1 k2 k3 k4 b1 b2 b3 b4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4,
    SF mm w0 w4 w5 w7 k1 k2 k3 k4 b1 b2 b3 b4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4 ->
    MEM mm w0 w4 w5 w7 k1 k2 k3 k4 b1 b2 b3 b4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4.
  Proof using HC.
    intros mm w0 w4 w5 w7 k1 k2 k3 k4 b1 b2 b3 b4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4 H.
    destruct H as ((buf & BU & BL) & SB & CB & DB & STK & RSP & SZ0 & R4 & S4 & R3 & S3 & R2 & S2 & R1 & S1 & RFR
                   & MI & MU & WMO).
    apply z4_spd_split in RSP. destruct RSP as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    pose proof HC as C.
    destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
                   & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
    assert (AHm : AHEAP AI L RNG st LB mm).
    { pose proof (AI_layout AI L RNG st LB m0 AH) as LY. pose proof (@ATOP_lo rc) as HA.
      destruct DSTF as [[E1 E2] | [pb HBo]].
      - eapply (AI_frame AI _ _ _ _ m0 mm [(lo, SP)]); [exact AH | eapply munch_weaken; [|exact MU] | exact WMO |].
        + intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [exact Hx | split; [lia | exact I]].
        + apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
          left. left. lia.
      - eapply (AI_frame AI); [exact AH | exact MU | exact WMO |].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
        + left. left. lia.
        + right. left. exists (HB pb DST dcap). split; [exact HBo|]. cbn. lia. }
    unfold z4L_mem.
    rewrite !Z_to_bv_bv_unsigned.
    replace (SS + 6 + l1 + o2) with (SS + (6 + l1) + o2) by lia.
    replace (SS + 6 + l1 + l2 + o3) with (SS + (6 + l1 + l2) + o3) by lia.
    replace (SS + 6 + l1 + l2 + l3 + o4) with (SS + (6 + l1 + l2 + l3) + o4) by lia.
    split; [exact P0|]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
    split; [exact R4|]. split; [exact R3|]. split; [exact R2|]. split; [exact R1|].
    split; [exact MI|].
    split.
    { apply (AF_huf_z4s1a.z4_x2tab_fact_tl mm (DT + 4) cells tl TOK). rewrite <- ECB. exact CB. }
    split; [exact CB|].
    split.
    { exists (map (Z_to_bv 8) buf). split; [exact BU|]. rewrite length_map. exact BL. }
    split.
    { destruct (hb_unpoisoned AI L RNG st LB mm pdt DT (DTABLE_BYTES mtl) AHm HDT) as (U & _). exact U. }
    destruct DSTF as [[E1 E2] | [pb HBo]].
    - rewrite E1, E2, Z.add_0_r. apply unpoisoned_nil. lia.
    - destruct (hb_unpoisoned AI L RNG st LB mm pb DST dcap AHm HBo) as (U & _). exact U.
  Qed.
(* [comment removed for export] *)
  Lemma z4b_back : forall mm mm' w0 w4 w5 w7 v0 v4 v5 v7 k1 k2 k3 k4 b1 b2 b3 b4 h1 h2 h3 h4 l1 l2 l3 o1 o2 o3 o4
                         jp1 jp2 jp3 jp4,
    SF mm w0 w4 w5 w7 k1 k2 k3 k4 b1 b2 b3 b4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4 ->
    munch WM mm mm' -> wmono bsegs mm mm' ->
    MEM mm' v0 v4 v5 v7 k1 k2 k3 k4 h1 h2 h3 h4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4 ->
    SF mm' v0 v4 v5 v7 k1 k2 k3 k4 h1 h2 h3 h4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4.
  Proof using HC.
    intros mm mm' w0 w4 w5 w7 v0 v4 v5 v7 k1 k2 k3 k4 b1 b2 b3 b4 h1 h2 h3 h4 l1 l2 l3 o1 o2 o3 o4
           jp1 jp2 jp3 jp4 HS HM HW HN.
    pose proof HC as C.
    destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
                   & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
    pose proof (ablk_lin _ _ (ABL _ HDT)) as BT. cbn [ab_addr ab_size] in BT.
    assert (DTE : DTABLE_BYTES mtl = 4 * (1 + 2^mtl)) by reflexivity.
    pose proof (Z.pow_nonneg 2 mtl ltac:(lia)) as PM.
    pose proof (@ATOP_lo rc) as HA1.
    assert (DB : DST + dcap <= ATOP).
    { destruct DSTF as [(E1 & E2)|(pb & HDB)]; [lia|].
      pose proof (ablk_lin _ _ (ABL _ HDB)) as A. cbn [ab_addr ab_size] in A. lia. }
    unfold Z4SF in HS. unfold z4L_mem in HN.
    destruct HS as (HBUF & HSRC & HCB & HHD & HSTK & HSPL & _ & HB4 & _ & HB3 & _ & HB2 & _ & HB1 & _ & HFRS & HMI
                    & HMU & HWM).
    destruct HN as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & NB4 & NB3 & NB2 & NB1 & NMI & NZT & NCB
                    & (obuf & NBUF & NBL) & NU1 & NU2).
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in N5, N7, N8, NB1, NB2, NB3, NB4.
    clear NFK TOK ECB LCB BYS NSM TPA HINV RCL RLO RHI RRL RRS WSK WIM WIS WFS.
    unfold Z4SF.
    split.
    { exists (map bv_unsigned obuf). rewrite z4bk_bmap. split; [exact NBUF|]. rewrite length_map. exact NBL. }
    split.
    { destruct (Z.eq_dec (zlen src) 0) as [E0|E0].
      - eapply z4bk_bnil; [exact HSRC|]. rewrite length_map. lia.
      - destruct (SRCB ltac:(lia)) as (p & HSB & L1 & L2).
        pose proof (ablk_lin _ _ (ABL _ HSB)) as A. cbn [ab_addr ab_size] in A.
        eapply bytes_at_transport; [exact HSRC | exact HM |]. rewrite length_map. cbn [disjoint_from]. lia. }
    split; [exact NCB|].
    split.
    { eapply bytes_at_transport; [exact HHD | exact HM |].
      cbn [disjoint_from length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    split.
    { eapply stk_transport_disjoint; [exact HSTK | exact HM | exact HW |]. cbn [disjoint_from]. lia. }
    split.
    { apply z4bk_spd_merge. exact (conj N0 (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj N7 (conj N8 N9))))))))). }
    split; [reflexivity|].
    split; [z4bk_bd|]. split; [reflexivity|].
    split; [z4bk_bd|]. split; [reflexivity|].
    split; [z4bk_bd|]. split; [reflexivity|].
    split; [z4bk_bd|]. split; [reflexivity|].
    split.
    { eapply rw_cells_transport; [exact HFRS | exact HM | exact HW |].
      cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    split; [exact NMI|].
    split.
    { eapply munch_trans; [exact HMU|]. eapply munch_weaken; [|exact HM].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (X1 & X2 & _).
      split; [lia|]. split; [exact X2|exact I]. }
    eapply wmono_trans; [exact HWM | exact HW].
  Qed.
End BR.
End CANSEC1.
