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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseWalkMem HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_w4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4m AF_huf_w4m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s1k AF_huf_w4s1kb AF_huf_w4s1x AF_huf_w4s1c AF_huf_w4s1r2 AF_huf_w4e AF_huf_w4p.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_tbl_iface2 AF_huf_bitd AF_huf_w4s12_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section W4S1.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte) (pdt : aptr)
            (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -480).
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

  Hypothesis S2G : w4s2_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                      src cbs.

  Notation W4F' mm fr mid l256 l296 l336 :=
    (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm fr mid l256 l296 l336).
  Lemma w4s1_ff : 0x10007fff8000 <= SPF /\ SP <= 2^47 /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP.
  Proof using AH LOA LOS SPT.
    pose proof (AI_layout AI L RNG st LB m0 AH) as HL. pose proof (@ATOP_lo rc) as HA.
    unfold HUF_DEC_STACK_A in LOS. clear - HL HA LOS LOA SPT. lia.
  Qed.

  Lemma w4s1_hinv_core : forall o l b, W4HINV o l b -> 0 <= o /\ 0 <= b <= 64 /\ ((o = 0 /\ 0 <= b <= 64) \/ (o + 8 <= l /\ 0 <= b <= 8)).
  Proof. unfold W4HINV. lia. Qed.

  Lemma w4s1_hinv_le : forall o l b, W4HINV o l b -> 1 <= l -> 0 <= o < l.
  Proof. unfold W4HINV. lia. Qed.

  Lemma w4s1_hinv_step : forall o l b B o' b', W4HINV o l b -> 8 <= o -> b <= B <= b + 48 ->
    o' = o - B / 8 -> b' = B mod 8 -> W4HINV o' l b'.
  Proof. unfold W4HINV. intros o l b B o' b' H H8 HB -> ->. Z.div_mod_to_equations. lia. Qed.

  Lemma w4s1_hinv_fin : forall o l b B o' b', W4HINV o l b -> b <= B <= b + 48 ->
    (o < 8 /\ o' = o /\ b' = B) \/ (8 <= o /\ o' = o - B / 8 /\ b' = B mod 8) -> W4STRMt l o' b'.
  Proof.
    unfold W4HINV, W4STRMt. intros o l b B o' b' H HB [(H8 & -> & ->)|(H8 & -> & ->)]; Z.div_mod_to_equations; lia.
  Qed.

  Lemma w4s1_apart_sym : forall a n b m, KXGoM.apart a n b m -> KXGoM.apart b m a n.
  Proof. unfold KXGoM.apart. lia. Qed.

  Lemma w4s1_k10 : Z_to_bv 64 (-20) = Z_to_bv 64 AW4_K10.
  Proof.
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, AW4_K10.
    vm_compute. reflexivity.
  Qed.

  Ltac w4zl := repeat match goal with H : _ \/ _ |- _ => clear H end; lia.

  (* [comment removed for export] *)
  Lemma w4s1_dctx_of : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> 6 <= dcap ->
    w4s1_dctx RNG mm SPF (DT + 4) DT (DT + DTL) DST dcap tl.
  Proof using All.
    intros mm MU WM D6.
    pose proof w4s1_ff as (F1 & F2 & F3 & F4).
    pose proof (w4e_sp AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (SP1 & SP2 & SP3 & SP4).
    pose proof (w4e_blocks AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs pdt SBL SBH AH MTL TLM HDT LCB DSTF DC SRCB DJ2 (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL))
      as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (w4e_d0 AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs AH DSTF DC DJ2 (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (D1 & D2 & D3).
    pose proof (@ATOP_hi rc) as AT1. pose proof (@ATOP_lo rc) as AT2.
    pose proof (WB AF_huf_w4p.w4p_hb mm pdt DT DTL DT DTL MU WM HDT ltac:(lia) ltac:(lia) ltac:(lia))
      as (UT & RT & TA1 & TA2 & RTS & TA3 & TA4).
    destruct DSTF as [[D0a D0b]|(pb & HBD)]; [lia|].
    pose proof (WB AF_huf_w4p.w4p_hb mm pb DST dcap DST dcap MU WM HBD ltac:(lia) ltac:(lia) ltac:(lia))
      as (UO & RO & OA1 & OA2 & ROS & OA3 & OA4).
    assert (TLB : DT + 4 + 2 * 2^tl <= DT + DTL).
    { unfold DTABLE_BYTES, HufHarness.DT_BYTES.
      assert (P1 : 2^tl <= 2^(mtl + 1)) by (apply Z.pow_le_mono_r; lia).
      rewrite Z.pow_add_r in P1 by lia. lia. }
    pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia)) as TP.
    unfold w4s1_dctx.
    repeat match goal with |- _ /\ _ => split end.
    all: try exact UT.
    all: try exact UO.
    all: try exact WIM.
    all: try exact RO.
    all: try exact ROS.
    all: try (replace (DT + DTL - DT + 7) with (DTL + 7) by lia; exact RTS).
    all: try (eapply rng_sub; [exact RT | lia | lia]).
    all: try (eapply rng_sub; [exact WSK | lia | lia]).
    all: try lia.
    all: try (unfold AIMG_HI in *; unfold KXGoM.apart in *; lia).
  Qed.

  Lemma w4s1_srcctx : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    bytes_at bsegs mm SS (map (Z_to_bv 8) src) -> 10 <= n -> w4s_src_ctx RNG mm SS n SBL SBH.
  Proof using All.
    intros mm MU WM MI SB N10.
    pose proof w4s1_ff as (F1 & F2 & F3 & F4).
    pose proof (@ATOP_lo rc) as HA. pose proof (@ATOP_hi rc) as HA2.
    destruct (SRCB ltac:(lia)) as (p & HS & L1 & L2).
    pose proof (WB AF_huf_w4p.w4p_hb mm p SBL (SBH - SBL) SBL (SBH - SBL) MU WM HS ltac:(lia) ltac:(lia) ltac:(lia))
      as (US & RS & SA1 & SA2 & RSS & SA3 & SA4).
    replace (SBL + (SBH - SBL)) with SBH in US by lia.
    pose proof (ablk_lin _ _ (ABL _ HS)) as ASB. cbn [ab_addr ab_size] in ASB.
    unfold w4s_src_ctx.
    split; [exact MI|].
    split; [exists (map (Z_to_bv 8) src); split; [exact SB | rewrite length_map; lia]|].
    repeat match goal with |- _ /\ _ => split end.
    all: try exact US.
    all: try exact WIM.
    all: try exact RSS.
    all: try (eapply rng_sub; [exact RS | lia | lia]).
    all: try lia.
    all: try (unfold AIMG_HI in *; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma w4s1_round : forall mm mm' fr mid l256 l296 l336 fr' d1' l256' l296' l336' rest ob,
    W4F' mm fr mid l256 l296 l336 -> rw_cells bsegs mm (SP + -336) [CB 112 rest] ->
    munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
    mem_inv bsegs mm' -> u8arr bsegs mm' DST ob -> zlen ob = dcap ->
    rw_cells bsegs mm' (SP + -480) fr' -> cells_size fr' = 104%nat ->
    rw_cells bsegs mm' (SP + -376) d1' -> cells_size d1' = 40%nat ->
    rw_cells bsegs mm' (SP + -224) l256' -> cells_size l256' = 40%nat ->
    rw_cells bsegs mm' (SP + -184) l296' -> cells_size l296' = 40%nat ->
    rw_cells bsegs mm' (SP + -144) l336' -> cells_size l336' = 40%nat ->
    W4F' mm' fr' (d1' ++ [CB 112 rest]) l256' l296' l336'.
  Proof using All.
    intros mm mm' fr mid l256 l296 l336 fr' d1' l256' l296' l336' rest ob HW RST MU' WM' MI' OB OBL F0' FS' D1' DS'
      N4 N4S N3 N3S N2 N2S.
    unfold W4F in HW |- *.
    destruct HW as ((buf & BU & BL) & SRC & CBS & DTH & ST & F0 & FS & M1 & MS & L1 & LS1 & L2 & LS2 & L3 & LS3 & FRA & MI & MU & WM).
    pose proof (w4e_sp AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (SP1 & SP2 & SP3 & SP4).
    pose proof (w4e_blocks AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs pdt SBL SBH AH MTL TLM HDT LCB DSTF DC SRCB DJ2 (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL))
      as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (w4e_d0 AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs AH DSTF DC DJ2 (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (D1 & D2 & D3).
    pose proof (@ATOP_hi rc) as AT1. pose proof (@ATOP_lo rc) as AT2.
    unfold AIMG_HI in *. unfold KXGoM.apart in *.
    pose proof (magree_of_munch bsegs _ _ _ MU' WM') as AG.
    replace (SP + -480 + 104) with (SP + -376) in * by lia. replace (SP + -480 + 256) with (SP + -224) in * by lia.
    replace (SP + -480 + 296) with (SP + -184) in * by lia. replace (SP + -480 + 336) with (SP + -144) in * by lia.
    split.
    { exists (map bv_unsigned ob). split; [|rewrite length_map; exact OBL].
      assert (E : map (Z_to_bv 8) (map bv_unsigned ob) = ob).
      { clear. induction ob as [|x ob' IH]; [reflexivity|]. cbn. rewrite IH. f_equal. apply byte_of_unsigned. }
      rewrite E. exact OB. }
    split.
    { apply (bytes_at_magree bsegs _ mm mm' SS _ AG SRC). intros a Ha. rewrite length_map in Ha.
      cbn [outside]. repeat (split; [lia|]); exact I. }
    split.
    { apply (bytes_at_magree bsegs _ mm mm' (DT + 4) _ AG CBS). intros a Ha.
      cbn [outside]. repeat (split; [lia|]); exact I. }
    split.
    { apply (bytes_at_magree bsegs _ mm mm' DT _ AG DTH). intros a Ha. cbn [length] in Ha.
      cbn [outside]. repeat (split; [lia|]); exact I. }
    split.
    { apply (stk_magree bsegs _ mm mm' lo (SP + -480) AG ST). intros a Ha.
      cbn [outside]. repeat (split; [lia|]); exact I. }
    split; [exact F0'|]. split; [exact FS'|].
    split.
    { apply rw_cells_app. split; [exact D1'|]. rewrite DS'.
      replace (SP + -376 + Z.of_nat 40) with (SP + -336) by lia.
      apply (rw_cells_magree bsegs _ mm mm' (SP + -336) _ AG RST). intros a Ha. cbn [cells_size csize] in Ha.
      cbn [outside]. repeat (split; [lia|]); exact I. }
    split; [rewrite cells_size_app, DS'; reflexivity|].
    split; [exact N4|]. split; [exact N4S|]. split; [exact N3|]. split; [exact N3S|]. split; [exact N2|]. split; [exact N2S|].
    split.
    { apply (rw_cells_magree bsegs _ mm mm' (SP + -104) _ AG FRA). intros a Ha. change (Z.of_nat (cells_size _)) with 104 in Ha.
      cbn [outside]. repeat (split; [lia|]); exact I. }
    split; [exact MI'|].
    split.
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU'].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & Hx2 & _).
      split; [exact Hx2|]. repeat (split; [lia|]); exact I. }
    eapply wmono_trans; eassumption.
  Qed.

  Lemma w4s1_loopf : forall (fuel : nat) (l1 l2 l3 q pt1 pt2 pt3 pt4 b1 b2 b3 b4 c1 c2 c3 c4 : Z)
           (pad1 pad2 pad3 pad4 rest : list byte) (w0 : word) (mm : amem)
           (x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 : word),
    dcap - q <= 4 * Z.of_nat fuel ->
    W4F' mm [C8 w0; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + 3 * seg)); C8 (Z_to_bv 64 (DST + dcap - 3));
             C8 (Z_to_bv 64 seg); C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DST + seg));
             C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg)); C8 (Z_to_bv 64 (DST + dcap))]
            (W4BD (Z_to_bv 64 c1) b1 pad1 (SS + 6) pt1 ++ [CB 112 rest])
            (W4BD (Z_to_bv 64 c4) b4 pad4 (SS + 6 + l1 + l2 + l3) pt4)
            (W4BD (Z_to_bv 64 c3) b3 pad3 (SS + 6 + l1 + l2) pt3)
            (W4BD (Z_to_bv 64 c2) b2 pad2 (SS + 6 + l1) pt2) ->
    1 <= l1 < 65536 -> 1 <= l2 < 65536 -> 1 <= l3 < 65536 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    W4HINV pt1 l1 b1 -> W4HINV pt2 l2 b2 -> W4HINV pt3 l3 b3 -> W4HINV pt4 (n - (6 + l1 + l2 + l3)) b4 ->
    8 <= dcap - 3 * seg -> 0 <= q -> 3 * seg + q + 4 <= dcap ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + pt4)) (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 b2) (Z_to_bv 64 b3) (Z_to_bv 64 b4)
               x8 x9 (Z_to_bv 64 (-20)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 b1) (Z_to_bv 64 (SS + 6 + l1 + pt2))
               (Z_to_bv 64 (SS + 6 + l1 + l2 + pt3)) (Z_to_bv 64 q) (Z_to_bv 64 DST) x22 x23 (Z_to_bv 64 0x7fff8000)
               (Z_to_bv 64 (SS + 6 + pt1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 c4) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 (-1 * DT + -5)) x31)
          FR (Z_to_bv 64 0x89de4) fc None mm (seg_rom bsegs)).
  Proof using All.
    pose proof (AF_huf_w4s1c.w4s1_core w4s1_decA w4s1_decB w4s1_rall) as CORE.
    induction fuel as [|fuel IH];
      intros l1 l2 l3 q pt1 pt2 pt3 pt4 b1 b2 b3 b4 c1 c2 c3 c4 pad1 pad2 pad3 pad4 rest w0 mm
        x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 HF HW HL1 HL2 HL3 HN HD6 HDS HI1 HI2 HI3 HI4 HD8 HQ HQD HC1 HC2 HC3 HC4.
    { exfalso. cbn [Z.of_nat] in HF. pose proof (Z.div_pos (dcap + 3) 4 ltac:(lia) ltac:(lia)). lia. }
    pose proof w4s1_ff as (F1 & F2 & F3 & F4).
    pose proof HW as HW0.
    destruct HW0 as ((buf & BU & BL) & SRC & CBS & DTH & ST & F0 & FS & M1 & MS & L1' & LS1 & L2' & LS2 & L3' & LS3 & FRA & MI & MU & WM).
    assert (HN0 : 0 < n) by lia.
    pose proof (WB AF_huf_w4p.w4p_ctx mm _ _ _ _ _ SS n HW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as WP.
    decompose [and] WP. clear WP.
    pose proof (w4s1_dctx_of mm MU WM HD6) as DCX.
    pose proof (w4s1_srcctx mm MU WM MI SRC ltac:(lia)) as SC.
    apply rw_cells_app in M1 as (M1 & MR).
    cbn [W4BD cells_size csize] in M1, MR, L1', L2', L3'.
    match type of MR with rw_cells _ _ ?a _ => replace a with (SP + -336) in MR by (cbn; lia) end.
    replace (SP + -480 + 104) with (SP + -376) in M1 by lia.
    replace (SP + -480 + 256) with (SP + -224) in L1' by lia.
    replace (SP + -480 + 296) with (SP + -184) in L2' by lia.
    replace (SP + -480 + 336) with (SP + -144) in L3' by lia.
    pose proof (w4s1_hinv_core _ _ _ HI1) as (P1a & P1b & P1c).
    pose proof (w4s1_hinv_core _ _ _ HI2) as (P2a & P2b & P2c).
    pose proof (w4s1_hinv_core _ _ _ HI3) as (P3a & P3b & P3c).
    pose proof (w4s1_hinv_core _ _ _ HI4) as (P4a & P4b & P4c).
    pose proof (w4s1_hinv_le _ _ _ HI1 ltac:(lia)) as P1d.
    pose proof (w4s1_hinv_le _ _ _ HI2 ltac:(lia)) as P2d.
    pose proof (w4s1_hinv_le _ _ _ HI3 ltac:(lia)) as P3d.
    pose proof (w4s1_hinv_le _ _ _ HI4 ltac:(lia)) as P4d.
    assert (APD : KXGoM.apart SS n DST dcap) by (apply w4s1_apart_sym; assumption).
    eapply CORE with (L1 := l1) (L2 := l2) (L3 := l3) (L4 := n - (6 + l1 + l2 + l3)).
    all: try exact DCX.
    all: try exact MI.
    all: try exact CBS.
    all: try exact BU.
    all: try exact SC.
    all: try exact F0.
    all: try exact M1.
    all: try exact L1'.
    all: try exact L2'.
    all: try exact L3'.
    all: try eassumption.
    all: try (lazymatch goal with |- forall _, _ => fail | |- _ => w4zl end).
    - intros mm' obuf' B1 B2 B3 B4 o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' y8 y9 y11 y12 y13 y14 y15 y16 y22 y23 y31
        MU' WM' MI' OB' OBL' FR' D1' D2' D3' D4' H81 E1o E1b H82 E2o E2b H83 E3o E3b H84 E4o E4b HB1 HB2 HB3 HB4
        HC1' HC2' HC3' HC4' HQ'.
      apply (IH l1 l2 l3 (q + 4) o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' pad1 pad2 pad3 pad4 rest w0 mm'
               y8 y9 y11 y12 y13 y14 y15 y16 y22 y23 y31).
      + rewrite Nat2Z.inj_succ in HF. w4zl.
      + eapply w4s1_round; [exact HW | exact MR | exact MU' | exact WM' | exact MI' | exact OB' |
          rewrite length_map; exact OBL' | exact FR' | reflexivity | exact D1' | reflexivity | exact D4' | reflexivity |
          exact D3' | reflexivity | exact D2' | reflexivity].
      + exact HL1.
      + exact HL2.
      + exact HL3.
      + exact HN.
      + exact HD6.
      + exact HDS.
      + eapply w4s1_hinv_step; [exact HI1 | exact H81 | exact HB1 | exact E1o | exact E1b].
      + eapply w4s1_hinv_step; [exact HI2 | exact H82 | exact HB2 | exact E2o | exact E2b].
      + eapply w4s1_hinv_step; [exact HI3 | exact H83 | exact HB3 | exact E3o | exact E3b].
      + eapply w4s1_hinv_step; [exact HI4 | exact H84 | exact HB4 | exact E4o | exact E4b].
      + exact HD8.
      + w4zl.
      + exact HQ'.
      + exact HC1'.
      + exact HC2'.
      + exact HC3'.
      + exact HC4'.
    - intros mm' obuf' B1 B2 B3 B4 o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' w40 w48 w56
        y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y21 y25 y28 y29 y30 y31
        MU' WM' MI' OB' OBL' FR' D1' D2' D3' D4' R1 R2 R3 R4 HB1 HB2 HB3 HB4 HC1' HC2' HC3' HC4'.
      rewrite w4s1_k10.
      apply (S2G l1 l2 l3 (q + 4) o1' o2' o3' o4' b1' b2' b3' b4' (Z_to_bv 64 c1') (Z_to_bv 64 c2') (Z_to_bv 64 c3')
               (Z_to_bv 64 c4') pad1 pad2 pad3 pad4 rest w0 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + 3 * seg))
               w40 w48 w56 mm' y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y21 y25 y28 y29 y30 y31).
      + eapply w4s1_round; [exact HW | exact MR | exact MU' | exact WM' | exact MI' | exact OB' |
          rewrite length_map; exact OBL' | exact FR' | reflexivity | exact D1' | reflexivity | exact D4' | reflexivity |
          exact D3' | reflexivity | exact D2' | reflexivity].
      + exact HL1.
      + exact HL2.
      + exact HL3.
      + exact HN.
      + exact HD6.
      + exact HDS.
      + eapply w4s1_hinv_fin; [exact HI1 | exact HB1 | exact R1].
      + eapply w4s1_hinv_fin; [exact HI2 | exact HB2 | exact R2].
      + eapply w4s1_hinv_fin; [exact HI3 | exact HB3 | exact R3].
      + eapply w4s1_hinv_fin; [exact HI4 | exact HB4 | exact R4].
      + w4zl.
      + w4zl.
  Qed.

  (* [comment removed for export] *)
  Lemma w4s1_proof : w4s1_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT
                       mtl tl lo src cbs.
  Proof using All.
    unfold w4s1_goal.
    intros l1 l2 l3 q pt1 pt2 pt3 pt4 b1 b2 b3 b4 c1 c2 c3 c4 pad1 pad2 pad3 pad4 rest w0 mm
      x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 HW HL1 HL2 HL3 HN HD6 HDS HI1 HI2 HI3 HI4 HD8 HQ HQD.
    rewrite <- w4s1_k10.
    rewrite <- (Z_to_bv_bv_unsigned c1), <- (Z_to_bv_bv_unsigned c2), <- (Z_to_bv_bv_unsigned c3) in HW.
    rewrite <- (Z_to_bv_bv_unsigned c4) in HW |- *.
    pose proof (bv_unsigned_in_range _ c1) as R1. pose proof (bv_unsigned_in_range _ c2) as R2.
    pose proof (bv_unsigned_in_range _ c3) as R3. pose proof (bv_unsigned_in_range _ c4) as R4.
    unfold bv_modulus in R1, R2, R3, R4. change (2 ^ Z.of_N 64) with (2^64) in R1, R2, R3, R4.
    eapply (w4s1_loopf (Z.to_nat (dcap - q))).
    1: (rewrite Z2Nat.id by w4zl; w4zl).
    1: exact HW.
    all: try eassumption.
  Qed.

End W4S1.
End CANSEC1.
