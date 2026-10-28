(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM Startup_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_w4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4m AF_huf_w4m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4e AF_huf_fdw_kit AF_huf_w4s1k AF_huf_w4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree KXCell HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s12_iface AF_huf_w4s3b AF_huf_w4s31z AF_huf_w4p AF_huf_w4s31k AF_huf_w4s31k2 AF_huf_w4s31k3 AF_huf_w4s31k4 AF_huf_w4s31c.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).




Section CANSEC1. Context {rc : runConstT}.
Section W4S31.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte) (pdt : aptr)
            (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -496).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis NFK : forall F k, ~ In (mkABlock (ABFake 0) F k) LB.
  Hypothesis ABL : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis DSTF : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis NSM : n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SRCB : 0 < n -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + n <= SBH.
  Hypothesis DJ1 : DT + DTL <= SS \/ SS + n <= DT.
  Hypothesis DJ2 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis DJ3 : DT + DTL <= DST \/ DST + dcap <= DT.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TPA : tp = Z_to_bv 64 ATP.
  Hypothesis HINV : harness_invA m0.
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WIS : rng_aimg_sh RNG.
  Hypothesis WFS : rng_fs L RNG.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation WB l := (l AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src
                      cells cbs pdt SBL SBH rstk AH NFK ABL MTL TLM HDT TOK ECB LCB DSTF DC BYS NSM S16 SRCB DJ1 DJ2 DJ3
                      LOA LOS SPT SP16 TPA HINV RCL RLO RHI RRL RRS WSK WIM WIS WFS).

  Notation W4F' mm fr mid l256 l296 l336 :=
    (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm fr mid l256 l296 l336).

  Hypothesis CONT2 : w4s32_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl
                        tl lo src cbs.

  Lemma w4s31_bvu : forall (b : word), b = Z_to_bv 64 (bv_unsigned b).
  Proof. intros b. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Lemma w4s31_bvr : forall (b : word), 0 <= bv_unsigned b < 2^64.
  Proof. intros b. pose proof (bv_unsigned_in_range 64 b) as H. unfold bv_modulus in H. exact H. Qed.

  Lemma w4s31_rel : forall m A B cs sz, stk bsegs m lo A -> rw_cells bsegs m A cs -> cells_size cs = sz -> lo <= A ->
    B = A + Z.of_nat sz -> stk bsegs m lo B.
  Proof. intros m A B cs sz ST RW HS HL ->. subst sz. exact (stk_release bsegs m lo A cs ST RW HL). Qed.

  Lemma w4s31_bytes_sub : forall m A (src : list Z) O Lk,
    bytes_at bsegs m A (map (Z_to_bv 8) src) -> 0 <= O -> 0 <= Lk -> O + Lk <= zlen src ->
    bytes_at bsegs m (A + O) (map (Z_to_bv 8) (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))).
  Proof.
    intros m A src0 O Lk H O0 L0 OL.
    rewrite <- (firstn_skipn (Z.to_nat O) src0), map_app in H.
    apply bytes_at_app in H as [_ H].
    rewrite <- (firstn_skipn (Z.to_nat Lk) (skipn (Z.to_nat O) src0)), map_app in H.
    apply bytes_at_app in H as [H _].
    rewrite length_map, length_firstn in H.
    replace (A + O) with (A + Z.of_nat (Nat.min (Z.to_nat O) (length src0))) by lia.
    exact H.
  Qed.

  Lemma w4s31_len_sub : forall (src : list Z) O Lk, 0 <= O -> 0 <= Lk -> O + Lk <= zlen src ->
    zlen (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src)) = Lk.
  Proof. intros src0 O Lk O0 L0 OL. rewrite length_firstn, length_skipn. lia. Qed.


  Lemma w4s31_mid : forall mm mm' fr l256 l296 l336 cs rest (c bw p a e : word) pad1 ob,
    W4F' mm fr (cs ++ [CB 112 rest]) l256 l296 l336 -> cells_size cs = 40%nat -> 6 <= dcap ->
    munch [(DST, DST + dcap); (SP + -376, SP + -336); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' ->
    mem_inv bsegs mm' -> stk bsegs mm' lo (SP + -480) ->
    u8arr bsegs mm' DST ob -> zlen ob = dcap ->
    rw_cells bsegs mm' (SP + -376) [C8 c; C4 bw; CB 4 pad1; C8 p; C8 a; C8 e] ->
    W4F' mm' fr (W4DX c bw p a e pad1 ++ [CB 112 rest]) l256 l296 l336.
  Proof using All.
    intros mm mm' fr l256 l296 l336 cs rest c bw p a e pad1 ob HW HCS D6 MU' WM' MI' ST' OB OBL DS.
    unfold W4F in HW |- *.
    destruct HW as ((buf & BU & BL) & SRC & CBS & DTH & ST & F0 & FS & M1 & MS & L1 & LS1 & L2 & LS2 & L3 & LS3 & FRA & MI & MU & WM).
    pose proof (w4e_sp AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (SP1 & SP2 & SP3 & SP4).
    pose proof (w4e_blocks AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs pdt SBL SBH AH MTL TLM HDT LCB DSTF DC SRCB DJ2 (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL))
      as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (w4e_d0 AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs AH DSTF DC DJ2 (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (D1 & D2 & D3).
    pose proof (@ATOP_hi rc) as AT1. pose proof (@ATOP_lo rc) as AT2.
    unfold AIMG_HI in *. unfold KXGoM.apart in *.
    pose proof (magree_of_munch bsegs _ _ _ MU' WM') as AG.
    apply kx_rw_cells_app in M1 as [_ MR]. rewrite HCS in MR.
    replace (SP + -480 + 104 + Z.of_nat 40) with (SP + -336) in MR by lia.
    replace (SP + -480 + 104) with (SP + -376) in * by lia. replace (SP + -480 + 256) with (SP + -224) in * by lia.
    replace (SP + -480 + 296) with (SP + -184) in * by lia. replace (SP + -480 + 336) with (SP + -144) in * by lia.
    split.
    { exists (map bv_unsigned ob). split; [|rewrite length_map; exact OBL].
      assert (E : map (Z_to_bv 8) (map bv_unsigned ob) = ob).
      { clear. induction ob as [|x ob' IH]; [reflexivity|]. cbn. rewrite IH. f_equal. apply byte_of_unsigned. }
      rewrite E. exact OB. }
    split.
    { apply (bytes_at_magree bsegs _ mm mm' SS _ AG SRC). intros x Hx. rewrite length_map in Hx.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split.
    { apply (bytes_at_magree bsegs _ mm mm' (DT + 4) _ AG CBS). intros x Hx.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split.
    { apply (bytes_at_magree bsegs _ mm mm' DT _ AG DTH). intros x Hx. cbn [length] in Hx.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [exact ST'|].
    split.
    { apply (rw_cells_magree bsegs _ mm mm' (SP + -480) fr AG F0). intros x Hx. rewrite FS in Hx.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [exact FS|].
    split.
    { apply kx_rw_cells_app. split; [unfold W4DX; exact DS|].
      change (Z.of_nat (cells_size (W4DX c bw p a e pad1))) with 40.
      replace (SP + -376 + 40) with (SP + -336) by lia.
      apply (rw_cells_magree bsegs _ mm mm' (SP + -336) _ AG MR). intros x Hx. cbn in Hx.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [reflexivity|].
    split.
    { apply (rw_cells_magree bsegs _ mm mm' (SP + -224) l256 AG L1). intros x Hx. rewrite LS1 in Hx.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [exact LS1|].
    split.
    { apply (rw_cells_magree bsegs _ mm mm' (SP + -184) l296 AG L2). intros x Hx. rewrite LS2 in Hx.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [exact LS2|].
    split.
    { apply (rw_cells_magree bsegs _ mm mm' (SP + -144) l336 AG L3). intros x Hx. rewrite LS3 in Hx.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [exact LS3|].
    split.
    { apply (rw_cells_magree bsegs _ mm mm' (SP + -104) _ AG FRA). intros x Hx. change (Z.of_nat (cells_size _)) with 104 in Hx.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [exact MI'|].
    split.
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU'].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & Hx2 & _).
      split; [exact Hx2|]. split; [lia|]. split; [lia|exact I]. }
    eapply wmono_trans; eassumption.
  Qed.


  Lemma w4s31_proof : w4s2_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                        src cbs.
  Proof using All.
    intros l1 l2 l3 q pt1 pt2 pt3 pt4 b1 b2 b3 b4 c1 c2 c3 c4 pad1 pad2 pad3 pad4 rest w0 w8 w16 w40 w48 w56 mm
      x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31 HW HL1 HL2 HL3 HN HD6 HS3 ST1 ST2 ST3 ST4 HQ HQ3.
    pose (dl := tl + 256 * mtl).
    pose proof ST1 as ST1'. unfold W4STRMt in ST1'.
    assert (HSEG : 0 <= seg <= dcap) by lia.
    assert (HQS : q <= seg) by lia.
    pose proof (w4e_sp AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (SPA & SPB & SPC & SPD).
    pose proof (WB w4p_ctx mm _ _ _ _ _ (SS + 6) l1 HW HD6 ltac:(lia) ltac:(lia) ltac:(lia)) as CTX.
    destruct CTX as ((bs & BS & BL) & HCB & CL & TL & (ob & OB & OL) & U1 & U2 & U3 & R1 & R2 & R3 &
                     (A1 & L1 & A2 & L2 & A3 & L3 & M1 & M2 & M3 & N1 & N2 & N3 & B1 & B2 & B3 & B4 & B5 & B6 & H1 & H2 & H3) &
                     P1 & P2 & P3 & P4 & P5 & P6 & P7 & MI & RF & HDST & E1 & HDC & HSP & HS1 & HS2 & HLEN & HDTB & E2 & HTL & HMT & ZT).
    pose proof HW as HW0. unfold W4F in HW0.
    destruct HW0 as (_ & SRC0 & _ & _ & ST & FR0 & FS0 & MD0 & MS0 & F2 & S2 & F3 & S3 & F4 & S4 & FRC & _ & MU0 & WM0).
    pose proof MD0 as MD1. apply kx_rw_cells_app in MD1 as [DS0 _].
    replace (SP + -480 + 104) with (SP + -376) in DS0 by lia. unfold W4BD in DS0.
    rewrite (w4s31_bvu c1) in DS0.
    pose proof DSTF as DSTF'. destruct DSTF' as [[D0 _]|[pb HDB]]; [lia|].
    pose proof (WB w4p_hb mm pb DST dcap DST dcap MU0 WM0 HDB ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & _ & _ & _ & HB4 & HB5).
    assert (DLO : DST + dcap <= lo) by lia.
    assert (HSTK : forall m1 m2, stk bsegs m1 lo (SP + -480) -> munch [(DST, DST + dcap); (SP + -376, SP + -336)] m1 m2 ->
                   wmono bsegs m1 m2 -> stk bsegs m2 lo (SP + -480)).
    { intros m1 m2 S1 MU WM. apply (stk_magree bsegs _ m1 m2 lo (SP + -480) (magree_of_munch bsegs _ _ _ MU WM) S1).
      intros x Hx. unfold KXGoM.apart in P2. cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    assert (HU8 : forall m1 m2 o, u8arr bsegs m1 DST o -> zlen o = dcap ->
                  munch [(SP + -376, SP + -336); (SP + -496, SP + -480)] m1 m2 ->
                  wmono bsegs m1 m2 -> u8arr bsegs m2 DST o).
    { intros m1 m2 o [OB1 OW1] OL1 MU WM. pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
      split.
      - apply (bytes_at_magree bsegs _ m1 m2 DST _ AG OB1). intros x Hx. cbn [outside]. split; [lia|]. split; [lia|exact I].
      - apply (wr_at_magree bsegs _ m1 m2 DST _ AG OW1). intros x Hx. cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    assert (HD2 : forall (mm' : amem) (cw bw pw aw ew : word)
                    (y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31 : word),
        munch [(DST, DST + dcap); (SP + -376, SP + -336); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' ->
        mem_inv bsegs mm' -> stk bsegs mm' lo (SP + -480) ->
        (exists ob', u8arr bsegs mm' DST ob' /\ zlen ob' = dcap) ->
        rw_cells bsegs mm' (SP + -376) [C8 cw; C4 bw; CB 4 pad1; C8 pw; C8 aw; C8 ew] ->
        evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 (Z_to_bv 64 (DST + seg + q)) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
                (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
           FR (Z_to_bv 64 570176) fc None mm' (seg_rom bsegs))).
    { intros mm' cw bw pw aw ew y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31
        MU WM MI' ST' (ob' & OB' & OL') DS'.
      pose proof (w4s31_mid mm mm' _ _ _ _ (W4BD c1 b1 pad1 (SS + 6) pt1) rest cw bw pw aw ew pad1 ob' HW eq_refl HD6
                    MU WM MI' ST' OB' OL' DS') as HW'.
      exact (CONT2 l1 l2 l3 q pt2 pt3 pt4 b2 b3 b4 cw bw pw aw ew c2 c3 c4 pad1 pad2 pad3 pad4 rest w0 w8 w16 w40 w48 w56 mm'
               y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31
               HW' HL1 HL2 HL3 HN HD6 HS3 ST2 ST3 ST4 HQ HQ3). }
    assert (HTS : forall (mm' : amem) (j c b : Z) (pw : word)
                    (y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y25 y28 y29 y30 y31 : word),
        munch [(DST, DST + dcap); (SP + -376, SP + -336); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' ->
        mem_inv bsegs mm' -> stk bsegs mm' lo (SP + -480) ->
        (exists ob', u8arr bsegs mm' DST ob' /\ zlen ob' = dcap) ->
        rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 pw; C8 (Z_to_bv 64 (SS + 6));
                                        C8 (Z_to_bv 64 (SS + 6 + 8))] ->
        0 <= j -> q + j < seg -> 0 <= b < 2^31 -> 0 <= c < 2^64 ->
        evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 (Z_to_bv 64 (DST + seg + q)) y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + q + j)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
                (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) y28 y29 y30 y31)
           FR (Z_to_bv 64 569912) fc None mm' (seg_rom bsegs))).
    { intros mm' j c b pw y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y25 y28 y29 y30 y31
        MU WM MI' ST' (ob' & OB' & OL') DS' HJ HQJ HB HC.
      pose proof (w4s31_mid mm mm' _ _ _ _ (W4BD c1 b1 pad1 (SS + 6) pt1) rest (Z_to_bv 64 c) (Z_to_bv 64 b) pw
                    (Z_to_bv 64 (SS + 6)) (Z_to_bv 64 (SS + 6 + 8)) pad1 ob' HW eq_refl HD6 MU WM MI' ST' OB' OL' DS') as HW'.
      pose proof (WB w4p_ctx mm' _ _ _ _ _ (SS + 6) l1 HW' HD6 ltac:(lia) ltac:(lia) ltac:(lia)) as CTX'.
      destruct CTX' as ((bs' & BS' & BL') & HCB' & CL' & TL' & (ob2 & OB2 & OL2) & U1' & U2' & U3' & _ & _ & _ & _ &
                        _ & _ & _ & _ & _ & _ & _ & MI2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZT').
      pose proof HW' as HW1. unfold W4F in HW1.
      destruct HW1 as (_ & _ & _ & _ & _ & FR1 & _).
      apply (w4s31_tail POST RNG mm' FR fc gp tp y25 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
               w0 w8 w16 w40 w48 w56 pw pad1 bs' cbs ob2 SP DST dcap seg q DT dl (SS + 6) b c tl mtl j l1
               FR1 DS' BS' BL' HCB' CL' TL' OB2 OL2 U1' U2' U3' R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6
               H1 H2 H3 P1 P2 P3 P4 P5 P6 P7 E1 E2 MI' RF ltac:(lia) HDC HSEG HQ HQJ HJ HQ3 HSP HS1 HS2 HLEN HB ltac:(lia)
               HTL ltac:(lia) eq_refl HC ZT').
      intros mm2 cw bw pw2 aw ew z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z23 z27 z28 z29 z30 z31
        MU2 WM2 MI3 OB3 FR3 DS3.
      apply (HD2 mm2 cw bw pw2 aw ew z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z23 y25 z27 z28 z29 z30 z31).
      - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
        intros x Hx. cbn [outside] in Hx |- *. lia.
      - eapply wmono_trans; eassumption.
      - exact MI3.
      - apply (HSTK mm' mm2 ST'); [eapply munch_weaken; [|exact MU2]; apply w4s31_sub2; lia | exact WM2].
      - exact OB3.
      - exact DS3. }
    assert (HLH : forall (x9 x10 x12 x13 x28 x29 x30 x31 : word), b1 <= 64 -> 4 <= seg - q ->
        evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (DST + seg + q)) x9 x10 (Z_to_bv 64 b1) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 0) (Z_to_bv 64 (DST + seg - 3)) (Z_to_bv 64 (- DT - 5))
               (Z_to_bv 64 (DST + q)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 seg) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8acdc) fc None mm (seg_rom bsegs))).
    { intros x9' x10' x12' x13' x28' x29' x30' x31' HB HR.
      apply (w4s31_loop (Z.to_nat seg) POST RNG mm FR fc gp tp x9' x10' x12' x13' x25 x28' x29' x30' x31'
               w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl (SS + 6) pt1 b1 (bv_unsigned c1)
               tl mtl 0 l1
               FR0 DS0 BS BL HCB CL TL OB OL U1 U2 U3 R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6
               H1 H2 H3 P1 P2 P3 P4 P5 P6 P7 E1 E2 MI RF ltac:(lia) HDC HSEG HQ ltac:(lia) ltac:(lia) ltac:(lia) HQ3 HSP HS1
               HS2 ltac:(lia) HLEN ltac:(lia) ltac:(lia) HTL ltac:(lia) eq_refl (w4s31_bvr c1) ZT).
      intros mm2 cw bw pw2 aw ew z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z23 z27 z28 z29 z30 z31
        MU2 WM2 MI3 OB3 FR3 DS3.
      apply (HD2 mm2 cw bw pw2 aw ew z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z23 x25 z27 z28 z29 z30 z31).
      - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx |- *. lia.
      - exact WM2.
      - exact MI3.
      - apply (HSTK mm mm2 ST); [eapply munch_weaken; [|exact MU2]; apply w4s31_sub2; lia | exact WM2].
      - exact OB3.
      - exact DS3. }
    eapply w4c0_walk; try eassumption; try lia.
    - 
      intros HQS'.
      eapply w4s31_d1; try eassumption; try lia.
      + 
        intros HA.
        destruct (Z_lt_le_dec 64 b1) as [HB|HB].
        * eapply w4s31_e1a; try eassumption; try lia.
          -- intros HQE mm' pw' y10 MU WM MI' FR' DS'.
             eapply HD2; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia
                         | exact WM | exact MI' | apply (HSTK mm mm' ST); [eapply munch_weaken; [|exact MU]; apply w4s31_sub1 | exact WM]
                         | exists ob; split; [apply (HU8 mm mm' ob OB OL); [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia | exact WM] | exact OL] | exact DS'].
          -- intros HQL mm' pw' y10 MU WM MI' FR' DS'.
             replace (Z_to_bv 64 (DST + q)) with (Z_to_bv 64 (DST + q + 0)) by (f_equal; lia).
        eapply HTS; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia
                         | exact WM | exact MI' | apply (HSTK mm mm' ST); [eapply munch_weaken; [|exact MU]; apply w4s31_sub1 | exact WM]
                         | exists ob; split; [apply (HU8 mm mm' ob OB OL); [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia | exact WM] | exact OL] | exact DS' | lia | lia | lia
                         | apply w4s31_bvr ].
        * destruct (Z.eq_dec pt1 0) as [P0|P0].
          -- eapply w4s31_e1z; try eassumption; try lia.
             ++ intros HQE y10 y11 y12 y14.
                eapply HD2; [apply munch_refl | apply wmono_refl | exact MI | exact ST
                            | exists ob; split; [exact OB | exact OL] | exact DS0].
             ++ intros HQL y10 y11 y12 y14.
                replace (Z_to_bv 64 (DST + q)) with (Z_to_bv 64 (DST + q + 0)) by (f_equal; lia).
                eapply HTS; [apply munch_refl | apply wmono_refl | exact MI | exact ST
                            | exists ob; split; [exact OB | exact OL] | exact DS0 | lia | lia | lia | apply w4s31_bvr].
          -- destruct (Z_le_gt_dec 8 pt1) as [P8|P8].
             ++ 
                pose proof (w4s31_len_sub src 6 l1 ltac:(lia) ltac:(lia) ltac:(lia)) as LBS.
                set (bs1 := firstn (Z.to_nat l1) (skipn (Z.to_nat 6) src)) in *.
                assert (NZ : 0 < n) by lia.
                destruct (SRCB NZ) as (psb & HSB & SB1 & SB2).
                destruct (hb_unpoisoned AI L RNG st LB m0 psb SBL (SBH - SBL) AH HSB) as (SU & SA16 & SN1 & SAB & SAT & SRG & SSH & SWR).
                pose proof (ablk_lin _ _ (ABL _ HDB)) as HDL. cbn [ab_addr ab_size] in HDL.
                pose proof (ablk_lin _ _ (ABL _ HDT)) as HTLB. cbn [ab_addr ab_size] in HTLB.
                pose proof RCL as RCL'. destruct RCL' as (SHC & RLT).
                pose proof (shclean_hull _ _ _ _ _ SHC) as (HH1 & HH2 & HH3 & HH4 & HH5 & HH6).
                pose proof (ablk_disj_band _ _ (ABL _ HDB)) as HDB2. cbn [ab_addr ab_size] in HDB2.
                assert (SPK : SP <= KEND) by lia.
                assert (ART : artcells mm).
                { pose proof (AI_rtcells AI L RNG st LB m0 AH) as A0. unfold artcells in *.
                  repeat match type of A0 with _ /\ _ => let H := fresh "A" in destruct A0 as [H A0] end.
                  repeat (split; [eapply rw_cells_transport; [eassumption | exact MU0 | exact WM0 |];
                                  cbn [disjoint_from cells_size csize]; unfold AIMG_HI in *; atop_facts; lia |]).
                  eapply rw_cells_transport; [eassumption | exact MU0 | exact WM0 |];
                    cbn [disjoint_from cells_size csize]; unfold AIMG_HI in *; atop_facts; lia. }
                assert (UBD : unpoisoned mm (SP + -376) (SP + -336)).
                { eapply unpoisoned_munch; [| exact MU0 |].
                  - eapply unpoisoned_sub; [eapply shclean_unpoisoned; exact SHC | lia | lia].
                  - cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, AIMG_HI, KEND, KLS in *. atop_facts.
                    Z.div_mod_to_equations; lia. }
                eapply w4s31_e1r with (bs := bs1) (lo := lo); try eassumption; try lia.
                all: lazymatch goal with
                     | |- bytes_at _ _ _ (map _ _) => apply w4s31_bytes_sub; [exact SRC0 | lia | lia | lia]
                     | |- Forall _ _ =>
                         pose proof BYS as BY2; rewrite <- (firstn_skipn (Z.to_nat 6) src) in BY2;
                         apply Forall_app in BY2 as [_ BY2];
                         rewrite <- (firstn_skipn (Z.to_nat l1) (skipn (Z.to_nat 6) src)) in BY2;
                         apply Forall_app in BY2 as [BY2 _]; exact BY2
                     | |- ablk _ _ => rewrite LBS; eapply ablk_sub; [exact SAB | lia | lia]
                     | |- unpoisoned _ (SS + 6) _ => rewrite LBS; exact U1
                     | |- rng _ (shad (SP + -376)) _ =>
                         unfold rrng in RRS; eapply rng_sub; [exact RRS | |]; rewrite !shad_div; Z.div_mod_to_equations; lia
                     | |- rng _ (shad (SS + 6)) _ =>
                         rewrite LBS; eapply rng_sub; [exact SSH | |]; unfold nshad, shlen; rewrite !shad_div, ?Z.shiftr_div_pow2 by lia;
                         Z.div_mod_to_equations; lia
                     | |- rng _ (SS + 6) _ => rewrite LBS; exact R1
                     | |- rng _ (SP + -496) _ => eapply rng_sub; [exact WSK | lia | lia]
                     | |- _ + 8 <= zlen _ => rewrite LBS; lia
                     | |- _ => idtac
                     end.
                ** intros HQE mm' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 MU WM MI' ST' FR' DS'.
                   eapply HD2; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia
                               | exact WM | exact MI' | exact ST'
                               | exists ob; split; [apply (HU8 mm mm' ob OB OL MU WM) | exact OL] | exact DS'].
                ** intros HQL mm' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 MU WM MI' ST' FR' DS'.
                   rewrite (w4s31_bvu (Z_to_bv 64 (le64v bs1 (pt1 - b1 / 8)))) in DS'.
                   replace (Z_to_bv 64 (DST + q)) with (Z_to_bv 64 (DST + q + 0)) by (f_equal; lia).
                   eapply HTS; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia
                               | exact WM | exact MI' | exact ST'
                               | exists ob; split; [apply (HU8 mm mm' ob OB OL MU WM) | exact OL] | exact DS' | lia | lia | lia
                               | apply w4s31_bvr ].
             ++ eapply w4s31_e1s with (A1 := A1) (L1 := L1); try eassumption; try lia.
                ** intros HQE mm' c' b' pw' y10 y11 y12 y13 y14 y15 MU WM MI' FR' DS' HC' HB'.
                   eapply HD2; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia
                               | exact WM | exact MI' | apply (HSTK mm mm' ST); [eapply munch_weaken; [|exact MU]; apply w4s31_sub1 | exact WM]
                               | exists ob; split; [apply (HU8 mm mm' ob OB OL); [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia | exact WM] | exact OL] | exact DS'].
                ** intros HQL mm' c' b' pw' y10 y11 y12 y13 y14 y15 MU WM MI' FR' DS' HC' HB'.
                   replace (Z_to_bv 64 (DST + q)) with (Z_to_bv 64 (DST + q + 0)) by (f_equal; lia).
        eapply HTS; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia
                               | exact WM | exact MI' | apply (HSTK mm mm' ST); [eapply munch_weaken; [|exact MU]; apply w4s31_sub1 | exact WM]
                               | exists ob; split; [apply (HU8 mm mm' ob OB OL); [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia | exact WM] | exact OL] | exact DS' | lia | lia | lia | lia ].
      + 
        intros HA HB.
        eapply w4s31_o1; try eassumption; try lia.
        intros mm' pw' y10 MU WM MI' FR' DS'.
        replace (Z_to_bv 64 (DST + q)) with (Z_to_bv 64 (DST + q + 0)) by (f_equal; lia).
        eapply HTS; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia
                    | exact WM | exact MI' | apply (HSTK mm mm' ST); [eapply munch_weaken; [|exact MU]; apply w4s31_sub1 | exact WM]
                    | exists ob; split; [apply (HU8 mm mm' ob OB OL); [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia | exact WM] | exact OL] | exact DS' | lia | lia | lia
                    | apply w4s31_bvr ].
      + 
        intros HA HB y10. apply HLH; lia.
    - 
      intros y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31.
      assert (STK : stk bsegs mm lo (SP + -104)).
      { pose proof (w4s31_rel mm _ (SP + -480 + 104) _ _ ST FR0 FS0 ltac:(lia) ltac:(lia)) as T1.
        pose proof (w4s31_rel mm _ (SP + -480 + 256) _ _ T1 MD0 MS0 ltac:(lia) ltac:(lia)) as T2.
        pose proof (w4s31_rel mm _ (SP + -480 + 296) _ _ T2 F2 S2 ltac:(lia) ltac:(lia)) as T3.
        pose proof (w4s31_rel mm _ (SP + -480 + 336) _ _ T3 F3 S3 ltac:(lia) ltac:(lia)) as T4.
        exact (w4s31_rel mm _ (SP + -104) _ _ T4 F4 S4 ltac:(lia) ltac:(lia)). }
      eapply w4_err; eassumption.
  Qed.

End W4S31.
End CANSEC1.
