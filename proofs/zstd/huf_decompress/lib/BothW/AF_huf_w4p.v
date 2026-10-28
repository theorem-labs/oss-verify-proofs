(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_w4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw Stdio_pure.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Set Ltac Backtrace. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation amem := (word -> option byte).

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
Import ListNotations.
Open Scope Z_scope.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC2. Context {rc : runConstT}.


Lemma w4p_rng_sub : forall R A N a k, rng R A N -> A <= a -> a + k <= A + N -> 0 <= k -> rng R a k.
Proof.
  unfold rng. intros R A N a k (H1 & H2 & H3) Ha Hk Hk0.
  split; [lia|]. split; [lia|]. intros b j Hb Hj. apply H3; lia.
Qed.

Lemma w4p_bytes_sub : forall m A bs i k, bytes_at bsegs m A bs -> 0 <= i -> 0 <= k -> i + k <= zlen bs ->
  exists bs', bytes_at bsegs m (A + i) bs' /\ zlen bs' = k.
Proof.
  intros m A bs i k H Hi Hk Hik.
  rewrite <- (firstn_skipn (Z.to_nat i) bs) in H.
  apply bytes_at_app in H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) bs)) in H.
  apply bytes_at_app in H as [H _].
  exists (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)). split.
  - replace (A + i) with (A + Z.of_nat (Z.to_nat i)) by lia. exact H.
  - rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia.
Qed.

Section W4P.
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
  Notation W4F' mm fr mid l256 l296 l336 :=
    (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm fr mid l256 l296 l336).

  Lemma w4p_hb : forall mm p A N a k, munch DW m0 mm -> wmono bsegs m0 mm -> In (HB p A N) LB ->
    A <= a -> a + k <= A + N -> 0 <= k ->
    unpoisoned mm a (a + k) /\ rng RNG a k /\ A mod 8 = 0 /\ 0 <= A /\ rng RNG (shad A) (shlen (N + 7)) /\ 4096 <= A /\ A + N <= ATOP.
  Proof using All.
    intros mm p A N a k MU WM HB Ha Hk Hk0.
    pose proof (w4e_aheap AI L RNG st LB sp m0 DST dcap tl lo src cbs AH DSTF DC LOA LOS SPT mm MU WM) as AHm.
    pose proof (hb_unpoisoned AI L RNG st LB mm p A N AHm HB) as (U & A16 & N1 & AB & AT & R1 & R2 & _).
    unfold ablk, AIMG_HI, KLS in AB.
    split; [apply (unpoisoned_sub mm A (A + N)); [exact U|lia|lia]|].
    split; [apply (w4p_rng_sub RNG A N); [exact R1|lia|lia|lia]|].
    split; [lia|]. split; [lia|]. split; [exact R2|]. split; lia.
  Qed.

  Lemma w4p_ctx : forall mm fr mid l256 l296 l336 S len,
    W4F' mm fr mid l256 l296 l336 -> 6 <= dcap -> SS <= S -> 1 <= len -> S + len <= SS + n ->
    (exists bs, bytes_at bsegs mm S bs /\ zlen bs = len) /\
    bytes_at bsegs mm (DT + 4) cbs /\ zlen cbs = 2 * 2^tl /\ 2 <= 2^tl <= 4096 /\
    (exists ob, u8arr bsegs mm DST ob /\ zlen ob = dcap) /\
    unpoisoned mm S (S + len) /\ unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) /\ unpoisoned mm DST (DST + dcap) /\
    rng RNG S len /\ rng RNG (DT + 4) (2 * 2^tl) /\ rng RNG DST dcap /\
    (exists A1 L1 A2 L2 A3 L3, A1 mod 8 = 0 /\ A2 mod 8 = 0 /\ A3 mod 8 = 0 /\ 0 <= A1 /\ 0 <= A2 /\ 0 <= A3 /\
       A1 <= S /\ S + len <= A1 + L1 /\ A2 <= DT + 4 /\ DT + 4 + 2 * 2^tl <= A2 + L2 /\ A3 <= DST /\ DST + dcap <= A3 + L3 /\
       rng RNG (shad A1) (shlen (L1 + 7)) /\ rng RNG (shad A2) (shlen (L2 + 7)) /\ rng RNG (shad A3) (shlen (L3 + 7))) /\
    KXGoM.apart S len (SP + -480) 480 /\ KXGoM.apart DST dcap (SP + -480) 480 /\ KXGoM.apart DST dcap S len /\
    KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 /\ KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) /\
    KXGoM.apart DST dcap 0x7fff8000 (2^44) /\ KXGoM.apart DST dcap 2147450880 (2^44) /\
    mem_inv bsegs mm /\ rng RNG (SP + -480) 480 /\
    4096 <= DST /\ DST + dcap <= 2^47 /\ 1 <= dcap <= 2^32 /\ 0x10007fff8000 + 2720 <= SP <= 2^47 /\ 4096 <= S /\ S + len <= 2^47 /\
    len <= 2^32 /\ 4096 <= DT /\ DT + 4 + 2 * 2^tl <= 2^47 /\ 1 <= tl <= 12 /\ 0 <= mtl <= 255 /\
    ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)].
  Proof using All.
    intros mm fr mid l256 l296 l336 S len HW D6 HS1 HL HS2.
    unfold W4F in HW.
    destruct HW as ((buf & BU & BL) & SRC & CBS & DTH & ST & F0 & FS & M1 & MS & L1 & LS1 & L2 & LS2 & L3 & LS3 & FRA & MI & MU & WM).
    pose proof (w4e_sp AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (SP1 & SP2 & SP3 & SP4).
    pose proof (w4e_blocks AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs pdt SBL SBH AH MTL TLM HDT LCB DSTF DC SRCB DJ2 (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL))
      as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (w4e_d0 AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs AH DSTF DC DJ2 (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (D1 & D2 & D3).
    pose proof (@ATOP_hi rc) as AT1. pose proof (@ATOP_lo rc) as AT2.
    pose proof TOK as (T1 & T2 & _). unfold HUF_TABLELOG_MAX in T1.
    assert (P2 : 2 <= 2^tl <= 4096).
    { pose proof (Z.pow_le_mono_r 2 1 tl ltac:(lia) ltac:(lia)) as Q1.
      pose proof (Z.pow_le_mono_r 2 tl 12 ltac:(lia) ltac:(lia)) as Q2.
      change (2^1) with 2 in Q1. change (2^12) with 4096 in Q2. lia. }
    assert (ZT : ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]).
    { apply (w4s1_x1tab_fact mm (DT + 4) cells tl TOK). rewrite <- ECB. exact CBS. }
    destruct DSTF as [[D0a D0b]|(pb & HBD)]; [lia|].
    destruct (SRCB ltac:(lia)) as (ps & HBS & SB1 & SB2).
    destruct B5 as [B5|B5]; [lia|]. destruct B6 as [B6|B6]; [lia|].
    unfold AIMG_HI in *. unfold KXGoM.apart in *.
    pose proof (w4p_hb mm ps SBL (SBH - SBL) S len MU WM HBS ltac:(lia) ltac:(lia) ltac:(lia))
      as (US & RS & AS1 & AS2 & RSS & AS3 & AS4).
    pose proof (w4p_hb mm pdt DT DTL (DT + 4) (2 * 2^tl) MU WM HDT ltac:(lia) ltac:(lia) ltac:(lia))
      as (UD & RD & AD1 & AD2 & RDS & AD3 & AD4).
    pose proof (w4p_hb mm pb DST dcap DST dcap MU WM HBD ltac:(lia) ltac:(lia) ltac:(lia))
      as (UO & RO & AO1 & AO2 & ROS & AO3 & AO4).
    destruct (w4p_bytes_sub mm SS (map (Z_to_bv 8) src) (S - SS) len SRC ltac:(lia) ltac:(lia)
                ltac:(rewrite length_map; lia)) as (bs & BS & BSL).
    replace (SS + (S - SS)) with S in BS by lia.
    split; [exists bs; split; [exact BS|exact BSL]|].
    split; [exact CBS|]. split; [exact LCB|]. split; [exact P2|].
    split; [exists (map (Z_to_bv 8) buf); split; [exact BU|rewrite length_map; exact BL]|].
    split; [exact US|]. split; [exact UD|]. split; [exact UO|].
    split; [exact RS|]. split; [exact RD|]. split; [exact RO|].
    split.
    { exists SBL, (SBH - SBL), DT, DTL, DST, dcap.
      repeat match goal with |- _ /\ _ => split end.
      all: first [assumption | lia]. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact MI|].
    split; [apply (w4p_rng_sub RNG lo (al_top L - lo)); [exact WSK|lia|lia|lia]|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    exact ZT.
  Qed.

  
  Lemma w4p_rl : forall mm fr mid l256 l296 l336 S len D,
    W4F' mm fr mid l256 l296 l336 -> 6 <= dcap -> SS <= S -> 1 <= len -> S + len <= SS + n ->
    SP + -376 <= D -> D + 40 <= SP + -104 -> D mod 8 = 0 ->
    (exists bz : list Z, bytes_at bsegs mm S (map (Z_to_bv 8) bz) /\ Forall (fun c => 0 <= c < 256) bz /\ zlen bz = len /\
       bz = firstn (Z.to_nat len) (skipn (Z.to_nat (S - SS)) src)) /\
    ablk S (S + len) /\ stk bsegs mm lo (SP + -480) /\ ATOP + 4096 <= lo /\ lo <= SP + -496 /\ artcells mm /\
    SP mod 8 = 0 /\ unpoisoned mm D (D + 40) /\ rng RNG D 40 /\ rng RNG (shad D) 5 /\ rng RNG (SP + -496) 16 /\
    rng RNG (shad S) (nshad (len + S mod 8)) /\ rng_aimg RNG /\ rng_aimg_sh RNG.
  Proof using All.
    intros mm fr mid l256 l296 l336 S len D HW D6 HS1 HL HS2 HD1 HD2 HD3.
    unfold W4F in HW.
    destruct HW as ((buf & BU & BL) & SRC & CBS & DTH & ST & F0 & FS & M1 & MS & L1 & LS1 & L2 & LS2 & L3 & LS3 & FRA & MI & MU & WM).
    pose proof (w4e_sp AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (SPa & SPb & SPc & SPd).
    pose proof (w4e_d0 AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs AH DSTF DC DJ2 (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST
      dcap DT DTL)) as (D1 & D2 & D3).
    pose proof (@ATOP_hi rc) as AT1. pose proof (@ATOP_lo rc) as AT2.
    destruct (SRCB ltac:(lia)) as (ps & HBS & SB1 & SB2).
    pose proof (w4p_hb mm ps SBL (SBH - SBL) S len MU WM HBS ltac:(lia) ltac:(lia) ltac:(lia))
      as (US & RS & AS1 & AS2 & RSS & AS3 & AS4).
    
    assert (BZ : exists bz : list Z, bytes_at bsegs mm S (map (Z_to_bv 8) bz) /\ Forall (fun c => 0 <= c < 256) bz /\ zlen bz = len /\
       bz = firstn (Z.to_nat len) (skipn (Z.to_nat (S - SS)) src)).
    { pose proof SRC as H.
      rewrite <- (firstn_skipn (Z.to_nat (S - SS)) src) in H. rewrite map_app in H.
      apply bytes_at_app in H as [_ H].
      rewrite length_map, firstn_length_le in H by lia.
      rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat (S - SS)) src)) in H. rewrite map_app in H.
      apply bytes_at_app in H as [H _].
      exists (firstn (Z.to_nat len) (skipn (Z.to_nat (S - SS)) src)).
      split; [replace (SS + Z.of_nat (Z.to_nat (S - SS))) with S in H by lia; exact H|].
      split; [apply Forall_take, Forall_drop, BYS|].
      split; [|reflexivity].
      rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia. }
    assert (HABS : ablk S (S + len)).
    { pose proof (hb_unpoisoned AI L RNG st LB m0 ps SBL (SBH - SBL) AH HBS) as (_ & _ & _ & K & _).
      unfold ablk in K |- *. lia. }
    assert (ART : artcells mm)
      by exact (AI_rtcells AI _ _ _ _ _ (w4e_aheap AI L RNG st LB sp m0 DST dcap tl lo src cbs AH DSTF DC LOA LOS SPT mm MU WM)).
    assert (SP8 : SP mod 8 = 0).
    { pose proof (Z.div_mod SP 16 ltac:(lia)) as E16. rewrite SP16 in E16. rewrite E16.
      replace (16 * (SP / 16) + 0) with ((2 * (SP / 16)) * 8) by lia. apply Z_mod_mult. }
    assert (RCm : rclean mm rstk).
    { apply (rclean_transport _ m0 mm rstk RCL MU WM).
      unfold appW, KLOW, KHIGH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; lia. }
    pose proof (rclean_shclean _ _ RCm) as SHm.
    pose proof (shclean_hull _ _ _ _ _ SHm) as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6).
    assert (UD : unpoisoned mm D (D + 40)).
    { apply (shclean_unpoisoned mm _ _ (r_rlo rstk) (r_rhi rstk)). eapply shclean_sub; [exact SHm | lia | lia | lia]. }
    assert (RD : rng RNG D 40).
    { apply (w4p_rng_sub RNG lo (al_top L - lo)); [exact WSK | lia | lia | lia]. }
    assert (RSD : rng RNG (shad D) 5).
    { unfold rrng in RRS. apply (w4p_rng_sub RNG _ _ _ _ RRS); rewrite ?shad_div;
        [clear - HU1 HU2 RLO RHI SPd HD1 HD2 HD3; Z.div_mod_to_equations; lia
        |clear - HU1 HU2 RLO RHI SPd HD1 HD2 HD3; Z.div_mod_to_equations; lia
        |lia]. }
    assert (R496 : rng RNG (SP + -496) 16).
    { apply (w4p_rng_sub RNG lo (al_top L - lo)); [exact WSK | lia | lia | lia]. }
    assert (RSS' : rng RNG (shad S) (nshad (len + S mod 8))).
    { apply (w4p_rng_sub RNG _ _ _ _ RSS); unfold shad, shlen, nshad; rewrite ?Z.shiftr_div_pow2 by lia; try change (2^3) with 8;
        clear - AS1 AS2 SB1 SB2 HS1 HS2 HL; Z.div_mod_to_equations; lia. }
    split; [exact BZ|]. split; [exact HABS|]. split; [exact ST|]. split; [exact LOA|]. split; [lia|]. split; [exact ART|].
    split; [exact SP8|]. split; [exact UD|]. split; [exact RD|]. split; [exact RSD|]. split; [exact R496|].
    split; [exact RSS'|]. split; [exact WIM|exact WIS].
  Qed.

  Lemma w4p_W4F_upd : forall mm mm' fr mid l256 l296 l336 mid' l256' l296' l336' A ob,
    W4F' mm fr mid l256 l296 l336 ->
    munch [(DST, DST + dcap); (A, A + 40)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    u8arr bsegs mm' DST ob -> zlen ob = dcap ->
    SP + -376 <= A -> A + 40 <= SP + -104 ->
    (mid' = mid /\ (A + 40 <= SP + -376 \/ SP + -224 <= A) \/ rw_cells bsegs mm' (SP + -376) mid' /\ cells_size mid' = 152%nat) ->
    (l256' = l256 /\ (A + 40 <= SP + -224 \/ SP + -184 <= A) \/ rw_cells bsegs mm' (SP + -224) l256' /\ cells_size l256' = 40%nat) ->
    (l296' = l296 /\ (A + 40 <= SP + -184 \/ SP + -144 <= A) \/ rw_cells bsegs mm' (SP + -184) l296' /\ cells_size l296' = 40%nat) ->
    (l336' = l336 /\ (A + 40 <= SP + -144 \/ SP + -104 <= A) \/ rw_cells bsegs mm' (SP + -144) l336' /\ cells_size l336' = 40%nat) ->
    W4F' mm' fr mid' l256' l296' l336'.
  Proof using All.
    intros mm mm' fr mid l256 l296 l336 mid' l256' l296' l336' A ob HW MU' WM' MI' OB OBL HA1 HA2 KM K1 K2 K3.
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
      cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    split.
    { apply (bytes_at_magree bsegs _ mm mm' (DT + 4) _ AG CBS). intros a Ha.
      cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    split.
    { apply (bytes_at_magree bsegs _ mm mm' DT _ AG DTH). intros a Ha. cbn [length] in Ha.
      cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    split.
    { apply (stk_magree bsegs _ mm mm' lo (SP + -480) AG ST). intros a Ha.
      cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    split.
    { apply (rw_cells_magree bsegs _ mm mm' (SP + -480) fr AG F0). intros a Ha. rewrite FS in Ha.
      cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    split; [exact FS|].
    split.
    { destruct KM as [(-> & KM)|(KM & _)]; [|exact KM].
      apply (rw_cells_magree bsegs _ mm mm' (SP + -376) mid AG M1). intros a Ha. rewrite MS in Ha.
      cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    split; [destruct KM as [(-> & _)|(_ & KM)]; [exact MS|exact KM]|].
    split.
    { destruct K1 as [(-> & K1)|(K1 & _)]; [|exact K1].
      apply (rw_cells_magree bsegs _ mm mm' (SP + -224) l256 AG L1). intros a Ha. rewrite LS1 in Ha.
      cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    split; [destruct K1 as [(-> & _)|(_ & K1)]; [exact LS1|exact K1]|].
    split.
    { destruct K2 as [(-> & K2)|(K2 & _)]; [|exact K2].
      apply (rw_cells_magree bsegs _ mm mm' (SP + -184) l296 AG L2). intros a Ha. rewrite LS2 in Ha.
      cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    split; [destruct K2 as [(-> & _)|(_ & K2)]; [exact LS2|exact K2]|].
    split.
    { destruct K3 as [(-> & K3)|(K3 & _)]; [|exact K3].
      apply (rw_cells_magree bsegs _ mm mm' (SP + -144) l336 AG L3). intros a Ha. rewrite LS3 in Ha.
      cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    split; [destruct K3 as [(-> & _)|(_ & K3)]; [exact LS3|exact K3]|].
    split.
    { apply (rw_cells_magree bsegs _ mm mm' (SP + -104) _ AG FRA). intros a Ha. change (Z.of_nat (cells_size _)) with 104 in Ha.
      cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    split; [exact MI'|].
    split.
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU'].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & Hx2 & _).
      split; [exact Hx2|]. split; [lia|exact I]. }
    eapply wmono_trans; eassumption.
  Qed.

  
  Lemma w4p_W4F_upd3 : forall mm mm' fr mid l256 l296 l336 mid' l256' l296' l336' A ob,
    W4F' mm fr mid l256 l296 l336 ->
    munch [(DST, DST + dcap); (A, A + 40); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    stk bsegs mm' lo (SP + -480) ->
    u8arr bsegs mm' DST ob -> zlen ob = dcap ->
    SP + -376 <= A -> A + 40 <= SP + -104 ->
    (mid' = mid /\ (A + 40 <= SP + -376 \/ SP + -224 <= A) \/ rw_cells bsegs mm' (SP + -376) mid' /\ cells_size mid' = 152%nat) ->
    (l256' = l256 /\ (A + 40 <= SP + -224 \/ SP + -184 <= A) \/ rw_cells bsegs mm' (SP + -224) l256' /\ cells_size l256' = 40%nat) ->
    (l296' = l296 /\ (A + 40 <= SP + -184 \/ SP + -144 <= A) \/ rw_cells bsegs mm' (SP + -184) l296' /\ cells_size l296' = 40%nat) ->
    (l336' = l336 /\ (A + 40 <= SP + -144 \/ SP + -104 <= A) \/ rw_cells bsegs mm' (SP + -144) l336' /\ cells_size l336' = 40%nat) ->
    W4F' mm' fr mid' l256' l296' l336'.
  Proof using All.
    intros mm mm' fr mid l256 l296 l336 mid' l256' l296' l336' A ob HW MU' WM' MI' ST' OB OBL HA1 HA2 KM K1 K2 K3.
    unfold W4F in HW |- *.
    destruct HW as ((buf & BU & BL) & SRC & CBS & DTH & ST & F0 & FS & M1 & MS & L1 & LS1 & L2 & LS2 & L3 & LS3 & FRA & MI & MU & WM).
    pose proof (w4e_sp AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (SP1 & SP2 & SP3 & SP4).
    pose proof (w4e_blocks AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs pdt SBL SBH AH MTL TLM HDT LCB DSTF DC SRCB DJ2
      (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (w4e_d0 AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs AH DSTF DC DJ2
      (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (D1 & D2 & D3).
    pose proof (@ATOP_hi rc) as AT1. pose proof (@ATOP_lo rc) as AT2.
    unfold AIMG_HI in *. unfold KXGoM.apart in *.
    clear DJ1 B5 D3.
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
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split.
    { apply (bytes_at_magree bsegs _ mm mm' (DT + 4) _ AG CBS). intros a Ha.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split.
    { apply (bytes_at_magree bsegs _ mm mm' DT _ AG DTH). intros a Ha. cbn [length] in Ha.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [exact ST'|].
    split.
    { apply (rw_cells_magree bsegs _ mm mm' (SP + -480) fr AG F0). intros a Ha. rewrite FS in Ha.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [exact FS|].
    split.
    { destruct KM as [(-> & KM)|(KM & _)]; [|exact KM].
      apply (rw_cells_magree bsegs _ mm mm' (SP + -376) mid AG M1). intros a Ha. rewrite MS in Ha.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [destruct KM as [(-> & _)|(_ & KM)]; [exact MS|exact KM]|].
    split.
    { destruct K1 as [(-> & K1)|(K1 & _)]; [|exact K1].
      apply (rw_cells_magree bsegs _ mm mm' (SP + -224) l256 AG L1). intros a Ha. rewrite LS1 in Ha.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [destruct K1 as [(-> & _)|(_ & K1)]; [exact LS1|exact K1]|].
    split.
    { destruct K2 as [(-> & K2)|(K2 & _)]; [|exact K2].
      apply (rw_cells_magree bsegs _ mm mm' (SP + -184) l296 AG L2). intros a Ha. rewrite LS2 in Ha.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [destruct K2 as [(-> & _)|(_ & K2)]; [exact LS2|exact K2]|].
    split.
    { destruct K3 as [(-> & K3)|(K3 & _)]; [|exact K3].
      apply (rw_cells_magree bsegs _ mm mm' (SP + -144) l336 AG L3). intros a Ha. rewrite LS3 in Ha.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [destruct K3 as [(-> & _)|(_ & K3)]; [exact LS3|exact K3]|].
    split.
    { apply (rw_cells_magree bsegs _ mm mm' (SP + -104) _ AG FRA). intros a Ha. change (Z.of_nat (cells_size _)) with 104 in Ha.
      cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
    split; [exact MI'|].
    split.
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU'].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & Hx2 & _).
      split; [exact Hx2|]. split; [lia|]. split; [lia|exact I]. }
    eapply wmono_trans; eassumption.
  Qed.
End W4P.

End CANSEC2.
