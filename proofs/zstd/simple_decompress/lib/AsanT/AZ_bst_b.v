(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseWalkMem FseRdKit FseRdKit2 ZdWalkKit MemRange SepHide ZdSeqBuildW.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_bfse_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_libc_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AZ_kx AZ_blk_iface AZ_blk_iface2 AZ_bst_env AZ_bst_a.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac kxa_norm ::= unfold shspan in *.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_hide segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_hide segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_hide segs m m' MU WM.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Notation zlen l := (Z.of_nat (length l)).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation SHB := 2147450880.
Notation BF5 := (Z_to_bv 8 18446744073709551605).

Section CANSEC1. Context {rc : runConstT}.

Lemma ffr_pres_mono : forall Wa Wb LBx (m m' : amem), (forall a, outside Wb a -> outside Wa a) -> ffr_pres Wa LBx m m' -> ffr_pres Wb LBx m m'.
Proof.
  intros Wa Wb LBx m m' HW H a Ha HP. apply (H a Ha). destruct HP as [[HF HO]|HS]; [left; split; [exact HF| exact (HW a HO)]| right; exact HS].
Qed.

(* [comment removed for export] *)
Lemma bs_sh_rd0 : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n -> 0 <= X -> X + n <= 2^47 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr p 3 + SHB)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m X n p U H1 H2 H3 H4.
  pose proof (fk_unp_shadow_zero m X n p U H1 H2) as B.
  assert (C : rw_cells bsegs m (shad p) [C1 (Z_to_bv 8 0)]).
  { apply rw_cells_C1_of_byte; [| | exact B]; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia. }
  pose proof (rw_cells_read bsegs m (shad p) [C1 (Z_to_bv 8 0)] 0 (C1 (Z_to_bv 8 0)) C eq_refl) as RD.
  rewrite Z.add_0_r in RD. unfold shad, ASHOFF in RD. rewrite Z.add_comm in RD. exact RD.
Qed.

(* [comment removed for export] *)
Lemma unp_keep : forall (m1 m2 : amem) Wl X n, unpoisoned m1 X (X + n) -> munch Wl m1 m2 ->
  disjoint_from Wl (shad X) (shad (X + n - 1) + 1 - shad X) -> unpoisoned m2 X (X + n).
Proof. intros m1 m2 Wl X n U MU D. eapply unpoisoned_munch; [exact U| exact MU| exact D]. Qed.

Section BS.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA lo FF SHF FLG : Z)
            (DTS DTP SRC W DFLT BASE BITS ty : Z) (k : seq_kind) (dt0 wb0 : list byte) (srcb : list Z) (frw oldp nbw coldw : word).
  (* [comment removed for export] *)
  Hypothesis LD0 : zlen dt0 = 8 + 8 * 2^(kind_maxLog k).
  Hypothesis LW0 : 626 <= zlen wb0.
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) srcb.
  Hypothesis SLEN : zlen srcb <= 1048576.
  Hypothesis TYR : 0 <= ty <= 3.
  Hypothesis DTP8 : DTP mod 8 = 0.
  Hypothesis DTS4 : DTS mod 4 = 0.      (* [comment removed for export] *)
  Hypothesis BASE4 : BASE mod 4 = 0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPV - 5136 /\ SPV - 208 <= SPA <= SPV - 192 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis G_dts : ablk DTS (DTS + zlen dt0) /\ (DTS + zlen dt0 <= lo \/ SPV + 16 <= DTS) /\ (FF + 256 <= DTS \/ DTS + zlen dt0 <= FF) /\ 4096 <= DTS /\ DTS + zlen dt0 < 2^47.
  Hypothesis G_dtp : ablk DTP (DTP + 8) /\ (DTP + 8 <= lo \/ SPV + 16 <= DTP) /\ (FF + 256 <= DTP \/ DTP + 8 <= FF) /\ 4096 <= DTP /\ DTP + 8 < 2^47.
  Hypothesis G_w : ablk W (W + zlen wb0) /\ (W + zlen wb0 <= lo \/ SPV + 16 <= W) /\ (FF + 256 <= W \/ W + zlen wb0 <= FF) /\ 4096 <= W /\ W + zlen wb0 < 2^47.
  Hypothesis G_src : ablk SRC (SRC + zlen srcb) /\ (SRC + zlen srcb <= lo \/ SPV <= SRC) /\ (FF + 256 <= SRC \/ SRC + zlen srcb <= FF)
                     /\ 4096 <= SRC /\ SRC + zlen srcb < 2^47.
  Hypothesis G_img : 4096 <= BASE /\ BASE + 212 <= AIMG_HI /\ 4096 <= BITS /\ BITS + 53 <= AIMG_HI.
  Hypothesis G_sep : (DTS + zlen dt0 <= DTP \/ DTP + 8 <= DTS) /\ (DTS + zlen dt0 <= W \/ W + zlen wb0 <= DTS) /\ (DTS + zlen dt0 <= SRC \/ SRC + zlen srcb <= DTS)
                     /\ (DTP + 8 <= W \/ W + zlen wb0 <= DTP) /\ (DTP + 8 <= SRC \/ SRC + zlen srcb <= DTP) /\ (W + zlen wb0 <= SRC \/ SRC + zlen srcb <= W).
  Hypothesis G_ff : ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ.
  Hypothesis G_flg : FLG = fflag L 2 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB2 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG)
                     /\ (DTS + zlen dt0 <= FLG \/ FLG + 1 <= DTS) /\ (DTP + 8 <= FLG \/ FLG + 1 <= DTP) /\ (W + zlen wb0 <= FLG \/ FLG + 1 <= W).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV + 16 - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_dts : rng RNG DTS (zlen dt0) /\ rng RNG (shad DTS) (shspan DTS (zlen dt0)).
  Hypothesis R_dtp : rng RNG DTP 8 /\ rng RNG (shad DTP) (shspan DTP 8).
  Hypothesis R_w : rng RNG W (zlen wb0) /\ rng RNG (shad W) (shspan W (zlen wb0)).
  Hypothesis R_src : rng RNG SRC (zlen srcb) /\ rng RNG (shad SRC) (shspan SRC (zlen srcb)).
  Hypothesis HSRC : ahull RNG m0 SRC (zlen srcb).
  Hypothesis R_img : aro RNG m0 BASE (4 * zlen (kind_base k)) /\ aro RNG m0 BITS (zlen (kind_bits k)).
  Hypothesis R_ff : rng RNG FF 256 /\ rng RNG SHF 32 /\ rng RNG FLG 1.
  Hypothesis LBH : ablkLB LB.
  Hypothesis G_in : ainblk LB DTS (zlen dt0) /\ ainblk LB DTP 8 /\ ainblk LB W (zlen wb0) /\ (0 < zlen srcb -> ainimg LB SRC (zlen srcb)).
  (* [comment removed for export] *)
  Hypothesis G_af : ashort LB 3 /\ rng_fs L RNG /\ SPV + 16 < al_top L /\ rng RNG lo (al_top L - lo) /\ KHIGH <= lo.
  Hypothesis TP : tp = Z_to_bv 64 ATP.

  Notation WR := [(DTS, DTS + zlen dt0); (DTP, DTP + 8); (W, W + zlen wb0)].
  Notation POST := (zd_buildseq_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DTS DTP W DFLT k ty (zlen srcb) frw oldp dt0 (length wb0) lo m0).
  Notation BS_EXIT := (AZ_bst_a.bs_exitA AI fflag FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo FF SHF FLG
                        DTS DTP SRC W DFLT BASE BITS ty k dt0 wb0 srcb frw oldp G_lo G_dts G_dtp G_w G_img G_sep G_ff G_flg RSTK RI R_img R_ff LBH).
  Notation BINV := (AZ_bst_a.BINV AI L RNG st LB m0 SPV FF DTS DTP W dt0 wb0).
  Notation MAGIC := (Z_to_bv 64 0x41b58ab3).
  Notation RETIRED := (Z_to_bv 64 0x45e0360e).

  (* [comment removed for export] *)
  Notation STb pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 FF) x21 x22 (Z_to_bv 64 SHF) x24 x25 (Z_to_bv 64 SHB) x27 x28 x29 x30 x31)   (* [comment removed for export] *)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition BE (m1 : amem) : Prop :=
    BINV m1
    /\ rw_cells bsegs m1 (SPV + -104) (BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ (exists jA jB, rw_cells bsegs m1 SPA [CB 16 jA; C8 (Z_to_bv 64 BASE); C8 (Z_to_bv 64 BITS); C8 (Z_to_bv 64 DTS); C8 coldw;
                                           C8 (Z_to_bv 64 (kind_maxLog k)); C8 (Z_to_bv 64 DTP); CB 16 jB; C8 (Z_to_bv 64 FF)])   (* [comment removed for export] *)
    /\ stk bsegs m1 lo SPA /\ stk bsegs m1 (SPA + 88) (SPV + -104)
    /\ (exists j3 j4, rw_cells bsegs m1 FF [C8 MAGIC; C8 (Z_to_bv 64 0x1a046); C8 (Z_to_bv 64 0x88cd8); CB 8 j3;
                                          C4 (Z_to_bv 64 (kind_max k)); CB 212 j4; C8 (Z_to_bv 64 FLG)])
    /\ rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m1 SHF BSH0
    /\ u8arr bsegs m1 DTS dt0 /\ rw_cells bsegs m1 DTP [C8 oldp] /\ u8arr bsegs m1 W wb0
    /\ bytes_at bsegs m1 SRC (map (Z_to_bv 8) srcb)
    /\ bytes_at bsegs m1 BASE (u32s (map (Z_to_bv 64) (kind_base k))) /\ bytes_at bsegs m1 BITS (map (Z_to_bv 8) (kind_bits k))
    /\ rw_cells bsegs m1 SPV [C8 nbw; C8 (Z_to_bv 64 W)]
    /\ unpoisoned m1 DTS (DTS + zlen dt0) /\ unpoisoned m1 DTP (DTP + 8) /\ unpoisoned m1 W (W + zlen wb0)
    /\ unpoisoned m1 SRC (SRC + zlen srcb)
    /\ unpoisoned m1 BASE (BASE + 4 * zlen (kind_base k)) /\ unpoisoned m1 BITS (BITS + zlen (kind_bits k)).
  Ltac open_be I := destruct I as (BI & SAV & (jA & jB & FRA) & STL & STG & (j3 & j4 & XF) & XL & XS & DTA & DTPC & WA & SB & BASEB & BITSB
                                      & ARGS & UD & UP & UW & US & UBASE & UBITS).

  Ltac be_geom :=
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6); pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6);
    pose proof G_flg as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7); pose proof R_ff as (RF1 & RF2 & RF3);
    pose proof G_dts as (D1 & D2 & D3 & D4 & D5); pose proof G_dtp as (P1 & P2 & P3 & P4 & P5); pose proof G_w as (W1 & W2 & W3 & W4 & W5);
    pose proof R_dts as (RD1 & RD2); pose proof R_dtp as (RP1 & RP2); pose proof R_w as (RW1 & RW2);
    pose proof G_src as (S1 & S2 & S3 & S4 & S5); pose proof G_sep as (DSP1 & DSP2 & DSP3 & DSP4 & DSP5 & DSP6); pose proof G_img as (IB1 & IB2 & IB3 & IB4);
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR;
    hide G_lo; hide G_ff; hide G_flg; hide R_ff; hide G_dts; hide G_dtp; hide G_w; hide R_dts; hide R_dtp; hide R_w; hide G_src; hide G_sep; hide G_img; hide G_in; hide R_img.
  (* [comment removed for export] *)
  Ltac be_lits :=
    lazymatch goal with
    | G2 : lo <= SPV - 5136, G3 : SPV - 208 <= SPA <= SPV - 192, F1 : ablk FF (FF + 256), F3 : FF + 256 <= ATOP, F4 : SHF = shad FF, L1 : ablk FLG (FLG + 1), L2 : FLG + 1 <= ATOP,
      D1 : ablk DTS (DTS + zlen dt0), P1 : ablk DTP (DTP + 8), W1 : ablk W (W + zlen wb0),
      D2 : DTS + zlen dt0 <= lo \/ SPV + 16 <= DTS, P2 : DTP + 8 <= lo \/ SPV + 16 <= DTP, W2 : W + zlen wb0 <= lo \/ SPV + 16 <= W,
      S2 : SRC + zlen srcb <= lo \/ SPV <= SRC, L4 : forall b, In b (FB2 FF :: LB) -> _ |- _ =>
      let FL := fresh "FL" in pose proof (fk_ablk_lits _ _ F1) as FL;
      let LL := fresh "LL" in pose proof (fk_ablk_lits _ _ L1) as LL;
      let DL := fresh "DL" in pose proof (fk_ablk_lits _ _ D1) as DL;
      let PL := fresh "PL" in pose proof (fk_ablk_lits _ _ P1) as PL;
      let WL := fresh "WL" in pose proof (fk_ablk_lits _ _ W1) as WL;
      let ATR := fresh "ATR'" in pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR;
      assert (F0' : 6443008 <= FF /\ FF + 256 <= ATOP) by (clear - FL F3 ATR; lia);
      assert (L0' : 6443008 <= FLG /\ FLG + 1 <= ATOP) by (clear - LL L2 ATR; lia);
      assert (D0' : 6443008 <= DTS /\ 0 <= zlen dt0) by (clear - DL; lia);
      assert (P0' : 6443008 <= DTP) by (clear - PL; lia);
      assert (W0' : 6443008 <= W /\ 0 <= zlen wb0) by (clear - WL; lia);
      assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity);
      assert (GS : SHB + 788992 <= SHF /\ SHF + 32 <= 17594333495296) by (rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia);
      assert (FFSH : FF + 256 <= SHF \/ SHF + 32 <= FF) by (clear - FL GS ATR; lia);
      assert (FLSH : FLG + 1 <= SHF \/ SHF + 32 <= FLG) by (clear - LL GS ATR; lia);
      assert (DSH : DTS + zlen dt0 <= SHF \/ SHF + 32 <= DTS) by (clear - DL GS ATR; lia);
      assert (PSH : DTP + 8 <= SHF \/ SHF + 32 <= DTP) by (clear - PL GS ATR; lia);
      assert (WSH : W + zlen wb0 <= SHF \/ SHF + 32 <= W) by (clear - WL GS ATR; lia);
      assert (D2' : DTS + zlen dt0 <= SPA \/ SPV + 16 <= DTS) by (clear - D2 G2 G3; lia);
      assert (P2' : DTP + 8 <= SPA \/ SPV + 16 <= DTP) by (clear - P2 G2 G3; lia);
      assert (W2' : W + zlen wb0 <= SPA \/ SPV + 16 <= W) by (clear - W2 G2 G3; lia);
      assert (S2' : SRC + zlen srcb <= SPA \/ SPV <= SRC) by (clear - S2 G2 G3; lia);
      let LFF := fresh "LFF" in pose proof (L4 _ ltac:(left; reflexivity)) as LFF; cbn [ab_addr ab_size] in LFF;
      clear FL LL DL PL WL ATR
    end.


  (* [comment removed for export] *)
  Lemma binv_step : forall m1 m2 Wl,
    BINV m1 -> munch Wl m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
    sub_fp Wl (WR ++ [(FF, FF + 248); (SPV - 5136, SPV); (SHF, SHF + 32)]) ->
    BINV m2.
  Proof.
    intros m1 m2 Wl (AH1 & FFR1 & MU1 & WM1 & MI1) MU WM MI2 SUB. be_geom. unfold hidden in G_in.
    pose proof G_in as (ID & IP & IW & _).
    pose proof (munch_weaken _ _ m1 m2 SUB MU) as MUW. clear MU SUB.
    assert (FL := fk_ablk_lits _ _ F1).
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (INB : forall X n, ainblk LB X n -> ainblk (FB2 FF :: LB) X n) by (intros X n (b & Hb & H); exists b; split; [right; exact Hb| exact H]).
    split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WM)| exact MI2]]]].
    - eapply (AI_frame AI); [exact AH1 | exact MUW | exact WM |]. cbn [app].
      constructor; [cbn [fst snd]; replace (DTS + zlen dt0 - DTS) with (zlen dt0) by (clear; lia); apply fk_acr_inblk; apply INB; exact ID|].
      constructor; [cbn [fst snd]; replace (DTP + 8 - DTP) with 8 by (clear; lia); apply fk_acr_inblk; apply INB; exact IP|].
      constructor; [cbn [fst snd]; replace (W + zlen wb0 - W) with (zlen wb0) by (clear; lia); apply fk_acr_inblk; apply INB; exact IW|].
      constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia]|].
      constructor; [cbn [fst snd]; left; left; cbn; clear - G1 G2 G3 G5; lia|].
      constructor; [cbn [fst snd]| constructor].
      rewrite F4. replace (shad FF + 32 - shad FF) with 32 by (clear; lia).
      eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - FL; lia].
    - eapply ffr_pres_trans; [exact FFR1|].
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 m2 2 FF 256 SHF 32 WR [(FF, FF + 248); (SPV - 5136, SPV)]);
        [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH1 b Hb) as HB; cbn [ab_addr ab_size] in HB; clear - HB; lia
                                                            | exists FF, (FF + 256); split; [exact F1 | clear; lia]]] |];
          constructor; [cbn [fst snd]; split; [clear; lia | left; clear - G1 G2 G3 G5; lia] | constructor]
        | constructor; [cbn [fst snd]; split; [exists DTS, (DTS + zlen dt0); split; [exact D1| clear; lia]| clear; lia]|];
          constructor; [cbn [fst snd]; split; [exists DTP, (DTP + 8); split; [exact P1| clear; lia]| clear; lia]|];
          constructor; [cbn [fst snd]; split; [exists W, (W + zlen wb0); split; [exact W1| clear; lia]| clear; lia]| constructor]
        | apply ffr_pres_refl
        | cbn [app]; eapply munch_weaken; [| exact MUW]; unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia
        | exact WM ].
    - eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUW]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx F5 F6 FA8 F2. Z.div_mod_to_equations. lia.
  Qed.



  (* [comment removed for export] *)
  Lemma bs_basicA : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x28 x29 x30 x31 : word),
    BE m1 -> ty = 0 ->
    evtF bsegs RNG POST (STb 0x88e70 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x21 x22 x24 x25 (Z_to_bv 64 DFLT) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I TY0. open_be I. be_geom. be_lits. unfold BSAVED in SAV. unfold BSH0 in XS.
    pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    (* [comment removed for export] *)
    pose proof (bs_sh_rd0 m1 DTP 8 DTP UP ltac:(clear; lia) ltac:(clear - DTP8; Z.div_mod_to_equations; lia) ltac:(clear - P4; lia) ltac:(clear - P5; lia)) as RDz.
    assert (RTz : rng RNG (Z.shiftr DTP 3 + SHB) 1).
    { eapply rng_sub'; [exact RP2|]. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. unfold shspan. rewrite shad_div. unfold ASHOFF.
      clear - DTP8; Z.div_mod_to_equations; lia. }
    hide_all_disj.
    fk_hold UD. fk_hold UP. fk_hold UW. fk_hold US. fk_hold UBASE. fk_hold UBITS. fk_hold BI. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold AH1. clear BASEB BITSB.
    pose proof (munch_refl [(DTP, DTP + 8); (FF, FF + 8)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    zstep.                                                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep. if_false.                                       (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep. bcase KF; [| exfalso; rewrite ?unsigned_lit in KF by (clear - F0'; lia); clear - KF F0'; lia].   (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    unfold fk_held in *. unhide.
    assert (BI2 : BINV m2).
    { eapply binv_step; [exact BI| exact MUL| exact WML| assumption|]. unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia. }
    (* [comment removed for export] *)
    lazymatch type of XF with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: rest) with ([c1] ++ [c2; c3; c4; c5; c6] ++ rest) in XF end.
    apply rw_cells_app in XF. destruct XF as [XM XF]. apply rw_cells_app in XF. destruct XF as [_ XP]. cbn [cells_size csize Nat.add length app] in XM, XP.
    replace (FF + Z.of_nat 8 + Z.of_nat 240) with (FF + 248) in XP by (clear; lia).
    destruct (rw_cells_forget _ _ _ _ FRA) as [jfr FRA']. destruct (rw_cells_forget _ _ _ _ XS) as [shb XS']. fold (BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) in SAV.
    cbn [cells_size csize Nat.add length] in FRA', XS'.
    (* [comment removed for export] *)
    eapply (BS_EXIT m2 jfr _ shb dt0 wb0 (Z_to_bv 64 DFLT) 0).
    all: [> exact BI2| exact SAV| exact FRA'| exact STL| exact STG| exact XM| exact XP| exact XL| exact XS'| exact DTA| reflexivity| exact WA| reflexivity| exact DTPC
         | clear; lia| right; split; [clear; pose proof (Nat2Z.is_nonneg (length srcb)); lia| left; split; [exact TY0| split; reflexivity]]].
  Qed.

  (* [comment removed for export] *)
  Ltac bs_close r :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      unfold fk_held in *; unhide;
      let BI2 := fresh "BI2" in
      assert (BI2 : BINV mx);
      [ lazymatch goal with MUL : munch _ _ mx, WML : wmono _ _ mx, BI : BINV _ |- _ =>
          eapply binv_step; [exact BI| exact MUL| exact WML| assumption| unfold sub_fp; cbn [outside app]; intros x Hx; first [match goal with HL : 16 <= zlen dt0 |- _ => clear - Hx HL end| clear - Hx]; lia] end
      | lazymatch goal with XF : rw_cells _ mx FF (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) |- _ =>
          change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: rest) with ([c1] ++ [c2; c3; c4; c5; c6] ++ rest) in XF;
          apply rw_cells_app in XF; destruct XF as [XM XF]; apply rw_cells_app in XF; destruct XF as [_ XP]; cbn [cells_size csize Nat.add length app] in XM, XP;
          replace (FF + Z.of_nat 8 + Z.of_nat 240) with (FF + 248) in XP by (clear; lia);
          lazymatch goal with FRA : rw_cells _ mx SPA _, XS : rw_cells _ mx SHF _, SAV : rw_cells _ mx (SPV + -104) _ |- _ =>
            destruct (rw_cells_forget _ _ _ _ FRA) as [jfr FRA']; destruct (rw_cells_forget _ _ _ _ XS) as [shb XS'];
            fold (BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) in SAV; cbn [cells_size csize Nat.add length] in FRA', XS';
            eapply (BS_EXIT mx jfr _ shb _ _ _ r);
            [exact BI2| exact SAV| exact FRA'| eassumption| eassumption| exact XM| exact XP| eassumption| exact XS'| eassumption| | eassumption| | eassumption| | ]
          end
        end ]
    end.

  (* [comment removed for export] *)
  Lemma bs_pfA : forall (n : nat) i lim m1 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x27 x28 x29 x30 x31 : word),
    0 <= i -> 64 * i < lim -> lim <= 64 * (i + Z.of_nat n) -> lim <= 8192 ->
    evtF bsegs RNG (fun ms' => exists (j : Z),
                      ms' = STb 0x89040 m1 x1 x5 x6 x7 (Z_to_bv 64 (64 * j)) (Z_to_bv 64 lim) x12 x13 x14 x15 x16 x17
                                x18 x19 x21 x22 x24 x25 x27 x28 x29 x30 x31)
      (STb 0x89038 m1 x1 x5 x6 x7 (Z_to_bv 64 (64 * i)) (Z_to_bv 64 lim) x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x27 x28 x29 x30 x31).
  Proof.
    induction n as [|n IH]; intros until x31; intros HI HLT HN HLIM; [exfalso; lia|].
    clear - IH HI HLT HN HLIM.                             (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. bcase K.                                 (* [comment removed for export] *)
    - replace (64 * i + 64) with (64 * (i + 1)) by (clear; lia).
      eapply (IH (i + 1) lim m1); [clear - HI; lia| clear - K; lia| clear - HN; lia| exact HLIM].
    - apply evtF_done. replace (64 * i + 64) with (64 * (i + 1)) by (clear; lia). eexists _. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma bs_repeatA : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x24 x25 x27 x28 x29 x30 x31 : word),
    BE m1 -> ty = 3 -> (frw <> Z_to_bv 64 0 -> 4096 <= bv_unsigned oldp < 2^47) ->   (* [comment removed for export] *)
    evtF bsegs RNG POST (STb 0x88ff4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x21 frw x24 x25 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I TY3 OLDP. open_be I. be_geom. be_lits. unfold BSAVED in SAV. unfold BSH0 in XS.
    pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    assert (KM : kind_maxLog k = 8 \/ kind_maxLog k = 9) by (destruct k; cbn; auto).
    pose proof (bs_sh_rd0 m1 DTP 8 DTP UP ltac:(clear; lia) ltac:(clear - DTP8; Z.div_mod_to_equations; lia) ltac:(clear - P4; lia) ltac:(clear - P5; lia)) as RDz.
    assert (RTz : rng RNG (Z.shiftr DTP 3 + SHB) 1).
    { eapply rng_sub'; [exact RP2|]. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. unfold shspan. rewrite shad_div. unfold ASHOFF.
      clear - DTP8; Z.div_mod_to_equations; lia. }
    hide_all_disj.
    fk_hold UD. fk_hold UP. fk_hold UW. fk_hold US. fk_hold UBASE. fk_hold UBITS. fk_hold BI. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold AH1. clear BASEB BITSB.
    pose proof (munch_refl [(FF, FF + 8)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    zstep. bcase K0.                                       (* [comment removed for export] *)
    - (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply Z_to_bv_eqm; reflexivity).
      zstep. zstep. zstep.                                 (* [comment removed for export] *)
      zstep. bcase KF; [exfalso; rewrite ?unsigned_lit in KF by (clear - F0'; lia); clear - KF F0'; lia|].   (* [comment removed for export] *)
      bs_close (2^64 - 20); [reflexivity| reflexivity| clear; lia| left; reflexivity].
    - assert (FRNZ : frw <> Z_to_bv 64 0) by (intros E; apply K0; rewrite E; reflexivity).
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep. bcase K1.                                     (* [comment removed for export] *)
      + zstep. zstep. zstep.                               (* [comment removed for export] *)
        zstep. bcase KF; [exfalso; rewrite ?unsigned_lit in KF by (clear - F0'; lia); clear - KF F0'; lia|].
        bs_close 0; [reflexivity| reflexivity| clear; lia| right; split; [clear; pose proof (Nat2Z.is_nonneg (length srcb)); lia| right; left; split; [exact TY3| split; [exact FRNZ| split; reflexivity]]]].
      + zstep.                                             (* [comment removed for export] *)
        zstep.                                             (* [comment removed for export] *)
        zstep. bcase K2.                                   (* [comment removed for export] *)
        * zstep. zstep. zstep.                             (* [comment removed for export] *)
          zstep. bcase KF; [exfalso; rewrite ?unsigned_lit in KF by (clear - F0'; lia); clear - KF F0'; lia|].
          bs_close 0; [reflexivity| reflexivity| clear; lia| right; split; [clear; pose proof (Nat2Z.is_nonneg (length srcb)); lia| right; left; split; [exact TY3| split; [exact FRNZ| split; reflexivity]]]].
        * zstep.                                           (* [comment removed for export] *)
          (* [comment removed for export] *)
          (* [comment removed for export] *)
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. if_false.            (* [comment removed for export] *)
          zstep.                                           (* [comment removed for export] *)
          (* [comment removed for export] *)
          zstep. zstep.                                    (* [comment removed for export] *)
          clear RDz.
          destruct KM as [ML|ML]; rewrite ML.
          all: zstep; zstep.                               (* [comment removed for export] *)
          all: try lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?e 8)] => let v := eval vm_compute in (Z.lor e 8) in change (Z.lor e 8) with v end.
          (* [comment removed for export] *)
          (* [comment removed for export] *)
          all: eapply evtF_cut;
            [ first [ eapply (bs_pfA 33 0 2056 m1); [clear; lia| clear; lia| clear; lia| clear; lia]
                    | eapply (bs_pfA 65 0 4104 m1); [clear; lia| clear; lia| clear; lia| clear; lia] ]
            | cbv beta; intros ms' (jj & ->) ].
          all: zstep; zstep; zstep; zstep.                 (* [comment removed for export] *)
          all: zstep; bcase KF; [| exfalso; rewrite ?unsigned_lit in KF by (clear - F0'; lia); clear - KF F0'; lia].
          all: bs_close 0; [reflexivity| reflexivity| clear; lia| right; split; [clear; pose proof (Nat2Z.is_nonneg (length srcb)); lia| right; left; split; [exact TY3| split; [exact FRNZ| split; reflexivity]]]].
  Qed.

  (* [comment removed for export] *)
  Lemma bs_rleA : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x27 x28 x29 x30 x31 : word),
    BE m1 -> ty = 1 ->
    evtF bsegs RNG POST (STb 0x88fc0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 (Z_to_bv 64 (kind_max k)) x22
                              (Z_to_bv 64 SRC) (Z_to_bv 64 (zlen srcb)) x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I TY1. open_be I. be_geom. be_lits. unfold BSAVED in SAV. unfold BSH0 in XS.
    pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    assert (KM : 0 <= kind_max k <= 52 /\ 8 <= kind_maxLog k <= 9) by (destruct k; cbn; lia).
    assert (L16 : 16 <= zlen dt0) by (pose proof (Z.pow_le_mono_r 2 8 (kind_maxLog k) ltac:(clear; lia) ltac:(clear - KM; lia)) as P8; change (2^8) with 256 in P8; clear - P8 LD0; lia).
    assert (LKB : zlen (kind_bits k) = kind_max k + 1 /\ zlen (kind_base k) = kind_max k + 1) by (destruct k; split; reflexivity).
    destruct LKB as [LKB1 LKB2].
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    unfold hidden in R_img. destruct R_img as ((_ & RB1 & RB2) & (_ & RI1 & RI2)).
    hide_all_disj.
    fk_hold UD. fk_hold UP. fk_hold UW. fk_hold US. fk_hold UBASE. fk_hold UBITS. fk_hold BI. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold AH1.
    pose proof (munch_refl [(DTS, DTS + 16); (DTP, DTP + 8); (FF, FF + 8)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    zstep. bcase K1.                                       (* [comment removed for export] *)
    - (* [comment removed for export] *)
      zstep. replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (2^64 - 72)) by (apply Z_to_bv_eqm; reflexivity).
      zstep. zstep. zstep.
      zstep. bcase KF; [| exfalso; rewrite ?unsigned_lit in KF by (clear - F0'; lia); clear - KF F0'; lia].
      bs_close (2^64 - 72); [reflexivity| reflexivity| clear; lia| left; reflexivity].
    - assert (NZ : 0 < zlen srcb) by (rewrite ?unsigned_lit in K1 by (clear - DB S4 S5; lia); clear - K1 DB; pose proof (Nat2Z.is_nonneg (length srcb)); lia).
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      unfold fk_held in US. pose proof R_src as [RS1 RS2]. pose proof S1 as SBK. pose proof (fk_ablk_lits _ _ SBK) as SL.
      assert (S0' : 6443008 <= SRC) by (clear - SL; lia).
      (* [comment removed for export] *)
      fk_hold SAV. fk_hold FRA. fk_hold STL. fk_hold STG. fk_hold XF. fk_hold XL. fk_hold XS. fk_hold DTA. fk_hold DTPC. fk_hold WA. fk_hold ARGS.
      kx_autoFLAx [KAUnp SRC 1; KAApp SRC 1] [0x88fd4] 40%nat [KZRange SRC 6443008 (2^47 - 1)] [] []; [ .. | kx_mem ].
      kx_abs. unfold fk_held in SB.
      (* [comment removed for export] *)
      remember (Znth 0 srcb) as sym eqn:ESYM.
      pose proof (Forall_Znth _ _ 0 FBY ltac:(clear - NZ; lia)) as SYMR. cbv beta in SYMR. rewrite <- ESYM in SYMR.
      pose proof (u8ro_read bsegs _ SRC _ 0 _ (wa SRC) SB (nth_error_map_Znth (Z_to_bv 8) srcb 0 ltac:(clear - NZ; lia)) ltac:(clear - NZ; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD0.
      rewrite <- ESYM in RD0.
      zstep. cbv beta. rewrite (byte_lit sym) by (clear - SYMR; lia).
      zstep. bcase K2.                                     (* [comment removed for export] *)
      (* [comment removed for export] *)
      2: zstep; replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply Z_to_bv_eqm; reflexivity).
      2: unfold fk_held in XF, XS, SAV, FRA, STL, STG, XL, DTA, DTPC, WA, ARGS.
      2: zstep; zstep; zstep.
      2: zstep; bcase KF; [| exfalso; rewrite ?unsigned_lit in KF by (clear - F0'; lia); clear - KF F0'; lia].
      2: bs_close (2^64 - 20); [reflexivity| reflexivity| clear; lia| left; reflexivity].
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      unfold fk_held in SAV, FRA, STL, STG, XF, XL, XS, DTA, DTPC, WA, ARGS, UD, UP, UBASE, UBITS.
      rewrite <- (firstn_skipn 16 dt0) in DTA. apply u8arr_app in DTA. destruct DTA as [HDU RESTU].
      assert (LH : length (firstn 16 dt0) = 16%nat) by (rewrite firstn_length; clear - L16; lia).
      rewrite LH in RESTU. change (Z.of_nat 16) with 16 in RESTU.
      apply rw_cells_of_u8arr in HDU. rewrite LH in HDU.
      assert (LBT : zlen (u32s (map (Z_to_bv 64) (kind_base k))) = 4 * (kind_max k + 1)) by (rewrite u32s_length, length_map; clear - LKB2; lia).
      assert (LBI : zlen (map (Z_to_bv 8) (kind_bits k)) = kind_max k + 1) by (rewrite length_map; exact LKB1).
      assert (SYM : 0 <= sym <= kind_max k) by (rewrite ?unsigned_lit in K2 by (clear - SYMR KM; lia); clear - K2 SYMR; lia).
      clear RD0 K2 SB US RS1 RS2 SBK SL.
      unfold AIMG_HI in IB2, IB4. rewrite LKB2 in RB1, RB2, UBASE. rewrite LKB1 in RI1, RI2, UBITS.
      assert (LR : zlen (skipn 16 dt0) = zlen dt0 - 16) by (rewrite skipn_length; clear - L16; lia).
      pose proof (fk_ablk_lits _ _ D1) as DL. pose proof (fk_ablk_lits _ _ P1) as PL. hide DL. hide PL.
      fk_hold WA. fk_hold RESTU.   (* [comment removed for export] *)
      pose proof BASEB as BASEB1. pose proof BITSB as BITSB1. fk_hold BASEB1. fk_hold BITSB1.   (* [comment removed for export] *)
      kx_autoFLAx [KAUnp (BASE + 4 * sym) 4; KAUnp (BITS + sym) 1; KAUnp DTS 16; KAApp DTS 16; KAUnp DTP 8; KAApp DTP 8] [0x891f8] 150%nat
        [KZRange SPA 4096 (2^47 - 208); KZAlign SPA 32; KZRange BASE 4096 6459180; KZRange BITS 4096 6459339; KZRange sym 0 52; KZRange (kind_max k) 0 52;
         KZRange DTS 6443008 (2^47 - 16); KZRange DTP 6443008 (2^47 - 8); KZAlign DTP 8; KZAlign DTS 4; KZAlign BASE 4;   (* [comment removed for export] *)
         KZWr DTS 16; KZWr DTP 8; KZDisj DTS 16 DTP 8; KZDisj DTS 16 SPA 88; KZDisj DTP 8 SPA 88;
         KZDisj DTS 16 FF 256; KZDisj DTP 8 FF 256; KZDisj DTS 16 FLG 1; KZDisj DTP 8 FLG 1; KZDisj DTS 16 SHF 32; KZDisj DTP 8 SHF 32;
         KZDisj DTS 16 W (zlen wb0); KZDisj DTP 8 W (zlen wb0); KZDisj DTS 16 (SPV + -104) 120; KZDisj DTP 8 (SPV + -104) 120]
        [(SPA, 88); (BASE, 4 * (kind_max k + 1)); (BITS, kind_max k + 1)]
        [(SPA, 88); (BASE, 4 * (kind_max k + 1)); (BITS, kind_max k + 1); (DTS, 16); (DTP, 8)].
      (* [comment removed for export] *)
      all: lazymatch goal with
           | |- evtF _ _ _ _ => idtac
           | |- 4096 <= BASE <= _ => clear - IB1 IB2; lia
           | |- 4096 <= BITS <= _ => clear - IB3 IB4; lia
           | |- _ /\ rd_at _ _ _ _ => split; [clear - IB1 IB2 IB3 IB4 KM; lia| kx_rd_at]
           | |- _ /\ rng _ _ _ => split; [clear - IB1 IB2 IB3 IB4 KM; lia| first [exact RB1| exact RI1]]
           | |- _ /\ unpZ _ _ _ /\ _ => split; [clear - IB1 IB2 IB3 IB4 KM SYM; lia | split; [kxa_unpZ | intros _; kxa_rng]]
           | |- _ /\ _ <= KXKEND /\ _ => unfold KXKEND, KXSHLO, KXSHHI; unfold hidden in DL, PL; first [clear - DL L16 D0' D5 ATR; lia | clear - PL P0' P5 ATR; lia]
           | |- _ /\ _ /\ (?A + _ <= ?B \/ _) =>
               let X := base_of A in let Y := base_of B in unhide_related X Y;
               repeat match goal with H : hidden _ |- _ => clear H end; clear KXRD KXK KXA; lia
           | |- sc_resid _ _ _ _ => first [kx_rd BITSB | kx_rd BASEB]
           | |- accP _ _ _ => first [kx_acc RI1 | kx_acc RB1]
           end.
      kx_mem.
      unfold fk_held in WA, RESTU.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (WA' : u8arr bsegs mx W wb0)
          by (eapply u8arr_transport; [exact WA| exact MUL| exact WML| cbn [disjoint_from fst snd]; unfold hidden in DSP2, DSP4, W3; clear - DSP2 DSP4 W3 L16 W0'; lia]);
        assert (RESTU' : u8arr bsegs mx (DTS + 16) (skipn 16 dt0))
          by (eapply u8arr_transport; [exact RESTU| exact MUL| exact WML| rewrite LR; cbn [disjoint_from fst snd]; unfold hidden in DSP1, D3; clear - DSP1 D3 L16 D0'; lia])
      end.
      clear WA RESTU. unfold fk_held in BASEB1, BITSB1.
      (* [comment removed for export] *)
      lazymatch type of HDU with context [C4 (ev KXE0 ?j)] => kx_read_eq j RDB end.
      lazymatch type of HDU with context [le1 (ev KXE0 ?j)] => kx_read_eq j RDI end.
      rewrite (rdval_u32s bsegs m1 BASE (kind_base k) sym (4 * sym + BASE + 0) true BASEB1 ltac:(clear; lia) ltac:(clear - SYM LKB2; lia)
                 (Forall_Znth _ _ sym (kind_base_small k) ltac:(clear - SYM LKB2; lia))) in RDB.
      rewrite (rdval_u8s bsegs m1 BITS (kind_bits k) sym (sym + BITS + 0) BITSB1 ltac:(clear; lia) ltac:(clear - SYM LKB1; lia) (kind_bits_bytes k)) in RDI.
      clear BASEB1 BITSB1.
      rewrite RDB, RDI in HDU. rewrite !le1_lit in HDU.
      (* [comment removed for export] *)
      lazymatch type of HDU with rw_cells _ ?mx _ ?cs =>
        pose proof (rw_cells_merge bsegs mx DTS [] cs []) as HDM; rewrite app_nil_r in HDM; specialize (HDM HDU) end.
      cbn [app cells_size csize Nat.add] in HDM. apply u8arr_of_rw_cells in HDM.
      lazymatch type of HDM with u8arr _ _ _ ?bs => set (img := bs) in * end.
      assert (LIMG : length img = 16%nat) by reflexivity.
      pose proof (Forall_Znth _ _ sym (kind_base_small k) ltac:(clear - SYM LKB2; lia)) as RBASE. cbv beta in RBASE.
      pose proof (Forall_Znth _ _ sym (kind_bits_bytes k) ltac:(clear - SYM LKB1; lia)) as RBITS. cbv beta in RBITS.
      assert (EIMG : img = map (Z_to_bv 8) (seq_table_bytes (rle_table k sym))).
      { subst img. unfold rle_table, seq_table_bytes. cbn [st_fast st_log st_cells flat_map seqsym_bytes ss_next ss_nbAdd ss_nbBits ss_base cells_bytes cbytes].
        rewrite !map_app. rewrite (le4_Z 0 0 eq_refl), (le2_Z 0 0 eq_refl), (le4_Z _ _ eq_refl). rewrite !app_nil_r. reflexivity. }
      lazymatch type of HDM with u8arr _ ?mx _ _ =>
        assert (DTA' : u8arr bsegs mx DTS (img ++ skipn 16 dt0)) by (apply u8arr_app; split; [exact HDM| rewrite LIMG; exact RESTU']) end.
      clear HDM RESTU' HDU.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      zstep. bcase KF; [| exfalso; rewrite ?unsigned_lit in KF by (clear - F0'; lia); clear - KF F0'; lia].
      bs_close 1; [rewrite length_app, skipn_length, LIMG; clear - L16; lia| reflexivity| clear; lia|].
      right. split; [clear - NZ; lia|]. right. right. split; [left; exact TY1|]. split; [reflexivity|].
      exists (rle_table k sym). split; [apply rle_table_ok; exact SYM|].
      replace (length (seq_table_bytes (rle_table k sym))) with (length img) by (rewrite EIMG, length_map; reflexivity).
      rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. exact EIMG.
  Qed.
End BS.
End CANSEC1.
