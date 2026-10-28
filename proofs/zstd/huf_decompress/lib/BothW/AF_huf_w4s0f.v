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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_w4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4m AF_huf_w4m AF_huf_tbl_iface2 AF_huf_bitd AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s0 AF_huf_w4s12_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface RF_huf_x4s04.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section W4S0F.
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
  Notation W4F' mm fr mid l256 l296 l336 :=
    (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm fr mid l256 l296 l336).
  Ltac hc := idtac.

  Lemma w4c_sp : 0x10007fff8000 <= SP + -496 /\ SP <= 2^47 /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP.
Proof using AH LOA LOS SPT.
  pose proof (AI_layout AI L RNG st LB m0 AH) as HL. pose proof (@ATOP_lo rc) as HA.
  unfold HUF_DEC_STACK_A in LOS. clear - HL HA LOS LOA SPT. lia.
Qed.
  Lemma w4c_d0 : 0 <= DST /\ DST + dcap <= ATOP /\ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST).
Proof using All.
  pose proof (@ATOP_lo rc) as HA.
  destruct DSTF as [[-> ->]|(pb & HB)]; [lia|].
  pose proof (AI_block AI L RNG st LB m0 pb DST dcap AH HB) as (D1 & (C2 & C3 & C4 & C5) & _).
  unfold ablk, AIMG_HI, KLS in C2. lia.
Qed.
  Lemma w4c_appW : appW DW.
Proof using All.
  pose proof w4c_d0 as (D1 & D2 & D3). pose proof (@ATOP_lo rc) as HA.
  unfold appW, KLOW, KHIGH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; lia.
Qed.
  Lemma w4c_aheap : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
Proof using All.
  intros mm MU WM. pose proof w4c_sp as SPB.
  destruct DSTF as [[E1 E2] | [pb HBo]].
  - eapply (AI_frame AI _ _ _ _ m0 mm [(lo, SP)]); [exact AH | eapply munch_weaken; [|exact MU] | exact WM |].
    + intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [exact Hx | split; [lia | exact I]].
    + apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
      left. left. lia.
  - eapply (AI_frame AI); [exact AH | exact MU | exact WM |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
    + left. left. lia.
    + right. left. exists (HB pb DST dcap). split; [exact HBo|]. cbn. lia.
Qed.
  Lemma w4c_magree : forall mm, munch DW m0 mm -> wmono bsegs m0 mm ->
    magree bsegs (fun a => aclient_addr CI LB SP a /\ ~ (DST <= a < DST + dcap)) m0 mm.
Proof using All.
  intros mm MU WM. apply (munch_magreeA DW m0 mm); [exact MU | exact WM |].
  intros a [CA ND]. cbn [outside]. split; [| split; [exact ND | exact I]].
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  destruct CA as [S | [R | [B | (a' & A' & E)]]].
  - lia.
  - destruct R as (iv & IN & R1 & R2). pose proof (AI_aci_img AI iv IN) as HI. unfold ABase.AIMG_HI in HI. lia.
  - destruct B as (b & IN & B1 & B2). pose proof (AI_block_bounds AI _ _ _ _ _ b AH IN) as (BB1 & BB2 & BB3).
    unfold ABase.AIMG_HI in BB1. lia.
  - subst a. unfold shad, ASHOFF. rewrite ?Z.shiftr_div_pow2 by lia.
    assert (A'B : 0 <= a' < 2^47).
    { destruct A' as [A1 | [(iv & IN & R1 & R2) | (cls & A & k & IN & F1 & F2)]].
      - lia.
      - pose proof (AI_aci_img AI iv IN). pose proof (AI_aci_lo AI iv IN). unfold ABase.AIMG_HI in *. lia.
      - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (BB1 & BB2 & BB3). cbn [ab_addr ab_size] in BB1, BB2, BB3.
        unfold ABase.AIMG_HI in *. lia. }
    Z.div_mod_to_equations. lia.
Qed.
  Lemma w4c_epi : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    stk bsegs mm lo (SP + -104) -> rw_cells bsegs mm (SP + -104) FRS ->
    mem_inv bsegs mm -> munch DW m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) FR (Z_to_bv 64 AW4_EPI) fc None mm (seg_rom bsegs)).
Proof using All.
  intros mm t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra ST FRC MI MU WM.
  pose proof w4c_sp as SPB.
  unfold AW4_EPI.
  do 15 zstep.
  release_frame FRC ST (bv_unsigned sp).
  apply evtF_done. unfold huf_dec_postA.
  do 15 eexists. exists mm.
  split; [reflexivity|].
  exact (conj MI (conj ST (conj (w4c_magree mm MU WM) (w4c_aheap mm MU WM)))).
Qed.

  Lemma w4c_lay : al_top L <= 2^47 /\ ATOP + 4096 <= lo /\ lo <= SP - 4096 /\ SP + 16 < al_top L.
  Proof using AH LOA LOS SPT. pose proof (AI_layout AI _ _ _ _ _ AH) as LY. unfold HUF_DEC_STACK_A in LOS.
    clear - LY LOS LOA SPT. lia. Qed.

  Lemma w4c_rcl : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> rclean mm rstk.
  Proof. intros mm MU WM. hc. eapply rclean_transport; [exact RCL|exact MU|exact WM|exact w4c_appW]. Qed.
  Lemma w4c_art : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> artcells mm.
  Proof using All. intros mm MU WM. exact (AI_rtcells AI _ _ _ _ _ (w4c_aheap mm MU WM)). Qed.

  Lemma w4c_unpS : forall mm, munch DW m0 mm -> 0 < n -> unpoisoned mm SS (SS + n).
  Proof.
    intros mm MU NP. hc. destruct (SRCB NP) as (p & HS & L1 & L2).
    pose proof (fun p A n H => hb_unpoisoned AI L RNG st LB m0 p A n AH H) as HU.
    destruct (HU _ _ _ HS) as (U & _ & N1 & AB & _).
    apply (unpoisoned_sub mm SBL (SBL + (SBH - SBL))); [|exact L1|lia].
    eapply unpoisoned_appW; [exact U|exact MU|exact w4c_appW|lia|].
    pose proof (ablk_lin _ _ AB) as A. lia.
  Qed.

  Lemma w4c_shar : forall a l b h, b mod 16 = 0 -> b <= a -> 0 <= l -> a + l <= h ->
    shad a + nshad (l + a mod 8) <= shad b + shlen (h - b + 7).
  Proof.
    intros a l b h B16 BA L0 AHh. rewrite !shad_div, nshad_div. unfold shlen. rewrite Z.shiftr_div_pow2 by lia.
    change (2^3) with 8. Z.div_mod_to_equations. lia.
  Qed.

  Lemma w4c_sh5 : forall A, A mod 8 = 0 -> shad (A + 40 - 1) + 1 - shad A = 5.
  Proof. intros A HA. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.

  Lemma w4c_m64 : forall x, x mod 64 = 0 -> x mod 8 = 0.
  Proof. intros x HX. Z.div_mod_to_equations. lia. Qed.

  Lemma w4c_rng : forall o len, 0 <= o -> 0 <= len -> o + len <= n -> 0 < n ->
    ablk (SS + o) (SS + o + len) /\ SS + o + 8 <= 2^47 /\ rng RNG (SS + o) len /\
    rng RNG (shad (SS + o)) (nshad (len + (SS + o) mod 8)).
  Proof.
    intros o len O1 O2 O3 NP. hc. destruct (SRCB NP) as (p & HS & L1 & L2).
    pose proof (fun p A n H => hb_unpoisoned AI L RNG st LB m0 p A n AH H) as HU.
    destruct (HU _ _ _ HS) as (_ & A16 & N1 & AB & AT & R1 & R2 & _).
    pose proof (ablk_lin _ _ AB) as A.
    split; [eapply ablk_sub; [exact AB|lia|lia]|]. split; [lia|]. split; [eapply rng_sub; [exact R1|lia|lia]|].
    eapply rng_sub; [exact R2| |].
    - unfold shad. rewrite !Z.shiftr_div_pow2 by lia. apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
    - apply w4c_shar; lia.
  Qed.
  Lemma w4c_call : forall (Q : machine_state -> Prop) mm (A o len : Z) (j : list byte)
      (xra t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    6 <= dcap -> 0 < n -> munch DW m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm lo (SP + -480) -> rw_cells bsegs mm A [CB 40 j] ->
    SP + -480 <= A -> A + 40 <= SP + -104 -> A mod 8 = 0 ->
    bytes_at bsegs mm SS (map (Z_to_bv 8) src) -> 0 <= o -> 0 <= len -> o + len <= n ->
    x10 = Z_to_bv 64 A -> x11 = Z_to_bv 64 (SS + o) -> x12 = Z_to_bv 64 len ->
    (forall m' (ret : Z) (u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word),
       munch [(SP + -480 - ABIT_INIT_STACK, SP + -480); (A, A + 40)] mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' ->
       stk bsegs m' lo (SP + -480) ->
       match init_dstream (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) with
       | Ok d => ret = len /\ bd_zero d = false /\ exists jp, rw_cells bsegs m' A (bitdz_cellsA (SS + o) d jp)
       | Err e => ret = - e /\ exists j', rw_cells bsegs m' A [CB 40 j']
       | Ub | NoFuel => False
       end ->
       evtF bsegs RNG Q (MS (mkR xra (Z_to_bv 64 (SP + -480)) gp tp u5 u6 u7 x8 x9 (Z_to_bv 64 ret) u11 u12 u13 u14 u15 u16
                                 u17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u28 u29 u30 u31)
                            FR (ret_pc xra) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR xra (Z_to_bv 64 (SP + -480)) gp tp t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16
                              x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                         FR (Z_to_bv 64 ABIT_INIT_D) fc None mm (seg_rom bsegs)).
  Proof.
    intros Q mm A o len j xra t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
      t3 t4 t5 t6 D6 NP MU WM MI STK RWA A1 A2 A3 BYT O1 O2 O3 E10 E11 E12 K.
    pose proof w4c_lay as LY. pose proof (w4c_rcl mm MU WM) as RC. pose proof (w4c_art mm MU WM) as ART.
    pose proof (w4c_unpS mm MU NP) as UNP. destruct (w4c_rng o len O1 O2 O3 NP) as (ABS & S8 & RS & RSS).
    pose proof bit_init_proofAD as BI. unfold bit_init_stmtA in BI.
    assert (LENB : zlen (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = len).
    { rewrite firstn_length, skipn_length. lia. }
    hc. pose proof (rclean_shclean _ _ RC) as SHC. pose proof (shclean_hull _ _ _ _ _ SHC) as HU.
    eapply evtF_cut.
    - eapply (BI RNG xra (Z_to_bv 64 (SP + -480))) with (D := A) (S := SS + o)
        (bs := firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) (j := j) (lo := lo) (RLO := r_rlo rstk) (RHI := r_rhi rstk).
      + exact RWA.
      + exact A3.
      + rewrite <- (firstn_skipn (Z.to_nat o) src), map_app in BYT. apply bytes_at_app in BYT. destruct BYT as [_ BYT].
        rewrite map_length, firstn_length_le, Z2Nat.id in BYT by lia.
        rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat o) src)), map_app in BYT.
        apply bytes_at_app in BYT. exact (proj1 BYT).
      + apply Forall_take, Forall_drop, BYS.
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; lia.
      + lia.
      + intros _. rewrite LENB. exact (conj ABS S8).
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; exact STK.
      + exact LOA.
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; unfold ABIT_INIT_STACK; lia.
      + exact MI.
      + exact ART.
      + eapply shclean_sub; [exact SHC|lia|lia|lia].
      + rewrite LENB. eapply unpoisoned_sub; [exact UNP|lia|lia].
      + eapply rng_sub; [exact WSK|lia|lia].
      + destruct HU as (U1 & U2 & U3 & U4 & U5 & _). rewrite <- (w4c_sh5 A A3).
        apply (rng_shad_sub RNG (r_rlo rstk) (r_rhi rstk)); [exact RRS|lia|lia|lia|exact U5|apply w4c_m64, U4].
      + intros _. rewrite LENB. exact (conj RS RSS).
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia. eapply rng_sub; [exact WSK|lia|lia].
      + exact RRS.
      + exact WIM.
      + exact E10.
      + exact E11.
      + rewrite LENB. exact E12.
    - intros ms' (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & ret & m' & EQ & MU' & WM' & MI' & STK' & BY' & RES).
      subst ms'. rewrite Z_to_bv_unsigned in MU', STK'. unfold bv_wrap, bv_modulus in MU', STK'.
      rewrite Z.mod_small in MU', STK' by lia.
      rewrite LENB in RES. apply K; [exact MU'|exact WM'|exact MI'|exact STK'|exact RES].
  Qed.

  Notation BIW A := [(SP + -480 - ABIT_INIT_STACK, SP + -480); (A, A + 40)].
  Lemma w4c_keep : forall mm m' A B bd, rw_cells bsegs mm B bd ->
      munch (BIW A) mm m' -> wmono bsegs mm m' -> SP + -480 <= B -> (B + Z.of_nat (cells_size bd) <= A \/ A + 40 <= B) ->
      rw_cells bsegs m' B bd.
  Proof.
    intros mm m' A B bd RW MU WM B1 B2.
    eapply rw_cells_transport; [exact RW|exact MU|exact WM|]. cbn [disjoint_from]. unfold ABIT_INIT_STACK. lia.
  Qed.

  Lemma w4c_rebuild : forall mm m' A fr mid l256 l296 l336 mid' l256' l296' l336',
      0 < n -> SP + -376 <= A -> A + 40 <= SP + -104 ->
      W4F' mm fr mid l256 l296 l336 ->
      munch (BIW A) mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' -> stk bsegs m' lo (SP + -480) ->
      rw_cells bsegs m' (SP + -376) mid' -> cells_size mid' = 152%nat ->
      rw_cells bsegs m' (SP + -224) l256' -> cells_size l256' = 40%nat ->
      rw_cells bsegs m' (SP + -184) l296' -> cells_size l296' = 40%nat ->
      rw_cells bsegs m' (SP + -144) l336' -> cells_size l336' = 40%nat ->
      W4F' m' fr mid' l256' l296' l336'.
  Proof using All.
    intros mm m' A fr mid l256 l296 l336 mid' l256' l296' l336' NZ0 A1 A2 WF MU' WM' MI' STK' N1 N1S N4 N4S N3 N3S N2 N2S.
    pose proof w4c_lay as LY. unfold ABIT_INIT_STACK in *.
    destruct WF as (BUF & BSS & BDT4 & BDT & STK & FRC & FRCS & MID & MIDS & B4 & B4S & B3 & B3S & B2 & B2S & FRM & MI & MU & WM).
    assert (NZ : SS + n <= ATOP).
    { destruct (SRCB NZ0) as (psb & HSB & SB1 & SB2).
      pose proof (ablk_lin _ _ (ABL _ HSB)) as AA. cbn [ab_addr ab_size] in AA. lia. }
    assert (DLO : DST + dcap <= ATOP).
    { destruct DSTF as [(E1 & E2)|(pb & HDB)]; [lia|].
      pose proof (ablk_lin _ _ (ABL _ HDB)) as HDL. cbn [ab_addr ab_size] in HDL. lia. }
    pose proof (ablk_lin _ _ (ABL _ HDT)) as HTL. cbn [ab_addr ab_size] in HTL.
    assert (DTB : DT + 4 + zlen cbs <= ATOP).
    { rewrite LCB. cbv [DTABLE_BYTES HufHarness.DT_BYTES] in HTL.
      assert (P2 : 2 ^ tl <= 2 * 2 ^ mtl).
      { destruct (Z_lt_le_dec tl 0) as [Hn|Hn].
        - rewrite (Z.pow_neg_r 2 tl Hn). pose proof (Z.pow_pos_nonneg 2 mtl ltac:(lia) ltac:(lia)). lia.
        - replace (2 * 2 ^ mtl) with (2 ^ (mtl + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
      lia. }
    unfold W4F.
    replace (SP + -480 + 104) with (SP + -376) by lia. replace (SP + -480 + 256) with (SP + -224) by lia.
    replace (SP + -480 + 296) with (SP + -184) by lia. replace (SP + -480 + 336) with (SP + -144) by lia.
    destruct BUF as (buf & BU & BL).
    split; [exists buf; split; [eapply u8arr_transport; [exact BU | exact MU' | exact WM' |] | exact BL] |].
    { rewrite length_map, BL. cbn [disjoint_from]. lia. }
    split; [eapply bytes_at_transport; [exact BSS | exact MU' |]; rewrite length_map; cbn [disjoint_from]; lia |].
    split; [eapply bytes_at_transport; [exact BDT4 | exact MU' |]; cbn [disjoint_from]; lia |].
    split; [eapply bytes_at_transport; [exact BDT | exact MU' |]; cbn [disjoint_from length]; lia |].
    split; [exact STK' |].
    split; [eapply rw_cells_transport; [exact FRC | exact MU' | exact WM' |]; rewrite FRCS; cbn [disjoint_from]; lia |].
    split; [exact FRCS |].
    split; [exact N1 |]. split; [exact N1S |]. split; [exact N4 |]. split; [exact N4S |].
    split; [exact N3 |]. split; [exact N3S |]. split; [exact N2 |]. split; [exact N2S |].
    split; [eapply rw_cells_transport; [exact FRM | exact MU' | exact WM' |]; cbn [disjoint_from cells_size csize]; lia |].
    split; [exact MI' |].
    split.
    - eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']].
      intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia.
    - eapply wmono_trans; [exact WM | exact WM'].
  Qed.

  Notation ZS pc m r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 :=
    (MS (mkR r1 (Z_to_bv 64 (SP + -480)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
             r26 r27 r28 r29 r30 r31) FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

  Lemma w4c_neg : forall e, Z_to_bv 64 (- e) = Z_to_bv 64 (2^64 - e).
  Proof.
    intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    replace (2^64 - e) with (- e + 1 * 2 ^ Z.of_N 64) by (cbn; lia). rewrite Z.mod_add by (cbn; lia). reflexivity.
  Qed.

  Lemma w4c_cl : forall (Q : machine_state -> Prop) mm (A o len R : Z) j fr mid l256 l296 l336
      (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word),
    6 <= dcap -> 0 < n -> W4F' mm fr mid l256 l296 l336 -> rw_cells bsegs mm A [CB 40 j] ->
    SP + -376 <= A -> A + 40 <= SP + -104 -> A mod 8 = 0 -> 0 <= o -> 0 <= len -> o + len <= n ->
    r1 = Z_to_bv 64 R -> 0 <= R < 2^64 -> R mod 2 = 0 ->
    r10 = Z_to_bv 64 A -> r11 = Z_to_bv 64 (SS + o) -> r12 = Z_to_bv 64 len ->
    (forall m' d jp (u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word),
       init_dstream (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = Ok d -> bd_zero d = false ->
       munch (BIW A) mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' -> stk bsegs m' lo (SP + -480) ->
       rw_cells bsegs m' A (bitdz_cellsA (SS + o) d jp) ->
       evtF bsegs RNG Q (ZS R m' r1 u5 u6 u7 r8 r9 (Z_to_bv 64 len) u11 u12 u13 u14 u15 u16 u17 r18 r19 r20 r21 r22 r23
                           r24 r25 r26 r27 u28 u29 u30 u31)) ->
    (forall m' e j' (u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word),
       init_dstream (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = Err e ->
       munch (BIW A) mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' -> stk bsegs m' lo (SP + -480) ->
       rw_cells bsegs m' A [CB 40 j'] ->
       evtF bsegs RNG Q (ZS R m' r1 u5 u6 u7 r8 r9 (Z_to_bv 64 (2^64 - e)) u11 u12 u13 u14 u15 u16 u17 r18 r19 r20 r21
                           r22 r23 r24 r25 r26 r27 u28 u29 u30 u31)) ->
    evtF bsegs RNG Q (ZS ABIT_INIT_D mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
                         r27 r28 r29 r30 r31).
  Proof using All.
    intros Q mm A o len R j fr mid l256 l296 l336 r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
      r24 r25 r26 r27 r28 r29 r30 r31 D6 NP WF RWA A1 A2 A3 O1 O2 O3 E1 R1 R2 E10 E11 E12 KO KE.
    destruct WF as (BUF & BSS & BDT4 & BDT & STK & FRC & FRCS & MID & MIDS & B4 & B4S & B3 & B3S & B2 & B2S & FRM & MI & MU & WM).
    eapply (w4c_call Q mm A o len j); try eassumption; try lia.
    intros m' ret u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 MU' WM' MI' STK' RES.
    subst r1. rewrite (ret_pc_even R R1 R2).
    destruct (init_dstream _) as [d|e| |] eqn:EQ; try contradiction.
    - destruct RES as (-> & BZ & jp & RW). eapply KO; [reflexivity|exact BZ|exact MU'|exact WM'|exact MI'|exact STK'|exact RW].
    - destruct RES as (-> & j' & RW). rewrite w4c_neg. eapply KE; [reflexivity|exact MU'|exact WM'|exact MI'|exact STK'|exact RW].
  Qed.

  Lemma w4c_err : forall mm fr mid l256 l296 l336
      (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word),
    W4F' mm fr mid l256 l296 l336 ->
    evtF bsegs RNG POST (ZS AW4_EPI mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
                           r27 r28 r29 r30 r31).
  Proof using All.
    intros mm fr mid l256 l296 l336 r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
      r27 r28 r29 r30 r31 WF.
    pose proof w4c_sp as SPB.
    destruct WF as (BUF & BSS & BDT4 & BDT & STK & FRC & FRCS & MID & MIDS & B4 & B4S & B3 & B3S & B2 & B2S & FRM & MI & MU & WM).
    assert (T1 : stk bsegs mm lo (SP + -480 + 104)).
    { replace (SP + -480 + 104) with (SP + -480 + Z.of_nat (cells_size fr)) by (rewrite FRCS; lia).
      apply stk_release; [exact STK|exact FRC|lia]. }
    assert (T2 : stk bsegs mm lo (SP + -480 + 256)).
    { replace (SP + -480 + 256) with (SP + -480 + 104 + Z.of_nat (cells_size mid)) by (rewrite MIDS; lia).
      apply stk_release; [exact T1|exact MID|lia]. }
    assert (T3 : stk bsegs mm lo (SP + -480 + 296)).
    { replace (SP + -480 + 296) with (SP + -480 + 256 + Z.of_nat (cells_size l256)) by (rewrite B4S; lia).
      apply stk_release; [exact T2|exact B4|lia]. }
    assert (T4 : stk bsegs mm lo (SP + -480 + 336)).
    { replace (SP + -480 + 336) with (SP + -480 + 296 + Z.of_nat (cells_size l296)) by (rewrite B3S; lia).
      apply stk_release; [exact T3|exact B3|lia]. }
    assert (T5 : stk bsegs mm lo (SP + -104)).
    { replace (SP + -104) with (SP + -480 + 336 + Z.of_nat (cells_size l336)) by (rewrite B2S; lia).
      apply stk_release; [exact T4|exact B2|lia]. }
    eapply w4c_epi; eassumption.
  Qed.

  Hypothesis LOOP : w4s1_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                      src cbs.
  Hypothesis S2G : w4s2_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                      src cbs.

  Ltac atstop := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
    let b := eval vm_compute in (orb (orb (p =? ABIT_INIT_D) (p =? AW4_EPI)) (orb (p =? 0x89de4) (p =? 0x8ac7c))) in
    lazymatch b with true => idtac end end.
  Lemma w4c_bslen : forall o len, 0 <= o -> 0 <= len -> o + len <= n ->
    zlen (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = len.
  Proof. intros o len O1 O2 O3. rewrite firstn_length, skipn_length. lia. Qed.

  Lemma w4c_bsbytes : forall o len, Forall (fun c => 0 <= c < 256) (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)).
  Proof using All. intros o len. apply Forall_take, Forall_drop, BYS. Qed.

  Lemma w4c_hinv : forall o len d, 0 <= o -> 0 <= len -> o + len <= n ->
    init_dstream (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = Ok d ->
    W4HINV (bd_ptr d) len (bd_bits d) /\ 1 <= len /\ 0 <= bd_bits d <= 64.
  Proof using All.
    intros o len d O1 O2 O3 ID.
    pose proof (init_dstream_shape _ _ (w4c_bsbytes o len) ID) as SH. rewrite (w4c_bslen o len O1 O2 O3) in SH.
    unfold W4HINV. lia.
  Qed.

  Lemma w4c_eerr : forall o len e, init_dstream (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = Err e -> 1 <= e <= 119.
  Proof using All. intros o len e ID. exact (init_dstream_err_range _ _ (w4c_bsbytes o len) ID). Qed.

  Lemma w4c_mid : forall m c1 c2, rw_cells bsegs m (SP + -376) c1 -> cells_size c1 = 40%nat ->
    rw_cells bsegs m (SP + -336) c2 -> rw_cells bsegs m (SP + -376) (c1 ++ c2).
  Proof.
    intros m c1 c2 R1 S1 R2. apply (proj2 (rw_cells_app _ _ _ c1 c2)). split; [exact R1|].
    rewrite S1. replace (SP + -376 + Z.of_nat 40) with (SP + -336) by lia. exact R2.
  Qed.

  Lemma w4c_bd : forall S d jp, bd_zero d = false ->
    bitdz_cellsA S d jp = W4BD (Z_to_bv 64 (bd_cont d)) (bd_bits d) jp S (bd_ptr d).
  Proof. intros S d jp BZ. unfold bitdz_cellsA, W4BD. rewrite BZ. reflexivity. Qed.

  Lemma w4c_far : 0 < n -> SS + n <= ATOP /\ DT + 4 + zlen cbs <= ATOP /\ DST + dcap <= ATOP /\ 0 <= SS /\ 0 <= DT.
  Proof using All.
    intros NZ0.
    destruct (SRCB NZ0) as (psb & HSB & SB1 & SB2).
    pose proof (ablk_lin _ _ (ABL _ HSB)) as AA. cbn [ab_addr ab_size] in AA.
    pose proof (ablk_lin _ _ (ABL _ HDT)) as HTL. cbn [ab_addr ab_size] in HTL.
    assert (DLO : DST + dcap <= ATOP).
    { destruct DSTF as [(E1 & E2)|(pb & HDB)]; [pose proof ATOP_lo; lia|].
      pose proof (ablk_lin _ _ (ABL _ HDB)) as HDL. cbn [ab_addr ab_size] in HDL. lia. }
    rewrite LCB. cbv [DTABLE_BYTES HufHarness.DT_BYTES] in HTL.
    assert (P2 : 2 ^ tl <= 2 * 2 ^ mtl).
    { destruct (Z_lt_le_dec tl 0) as [Hn|Hn].
      - rewrite (Z.pow_neg_r 2 tl Hn). pose proof (Z.pow_pos_nonneg 2 mtl ltac:(lia) ltac:(lia)). lia.
      - replace (2 * 2 ^ mtl) with (2 ^ (mtl + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
    lia.
  Qed.

  Lemma w4c_landm : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
  Proof. intros. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small; lia. Qed.

  Lemma w4c_sx32 : forall e, 0 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
  Proof.
    intros e He. unfold sx32. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with 18446744073709551616. rewrite Z.mod_small by lia.
    unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
    rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma w4c_x30 : forall d, 0 <= d + 4 < 2^64 ->
    Z_to_bv 64 (Z.lxor (d + 4) 18446744073709551615) = Z_to_bv 64 (-1 * d + -5).
  Proof.
    intros d Hd. rewrite zb_lxor_ones by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with 18446744073709551616.
    replace (-1 * d + -5) with (18446744073709551615 - (d + 4) + (-1) * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Lemma w4c_x29 : forall t m, 1 <= t <= 12 -> 0 <= m <= 255 ->
    Z.land (Z.land (bv_swrap 32 (0 - (t + 256 * m))) 18446744073709551615) 63 = 64 - t.
  Proof.
    intros t m T M.
    pose proof (neg_desc_shift2 t m T M) as N.
    change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
    change (2 ^ 64) with 18446744073709551616.
    rewrite (Z.mod_small (t + 256 * m) 18446744073709551616) in N by lia. exact N.
  Qed.

  Lemma w4c_strm : forall o len b, W4HINV o len b -> W4STRMt len o b.
  Proof. intros o len b H. unfold W4HINV, W4STRMt in *. clear - H. lia. Qed.

  Ltac w4eq := first [ reflexivity | f_equal; lia | f_equal; rewrite ?w4c_landm by lia; lia
                     | apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity | rewrite w4c_sx32 by lia; reflexivity
                     | apply w4c_x30; lia | f_equal; rewrite ?w4c_landm by lia; apply w4c_x29; lia
                     | Z.div_mod_to_equations; lia ].
  Ltac w4no K := exfalso; zify_cond K; Z.div_mod_to_equations; lia.
  Ltac w4br := lazymatch goal with |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
    let K := fresh "K" in if_cases K; [ try w4no K | try w4no K ] end.
  Ltac w4kp H MU WM N := pose proof (w4c_keep _ _ _ _ _ H MU WM) as N;
    specialize (N ltac:(lia) ltac:(cbv [bitdz_cellsA cells_size csize Nat.add app Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
  Ltac w4keep H MU WM := eapply (w4c_keep _ _ _ _ _ H MU WM); [lia | cbn [cells_size csize Nat.add]; lia].

  Ltac w4run := repeat (tryif atstop then fail else
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail | _ => zstep end).
  Ltac w4m8 := clear - SP16; Z.div_mod_to_equations; lia.

  Lemma w4c_loop : forall mm (l1 l2 l3 pt1 pt2 pt3 pt4 b1 b2 b3 b4 : Z) (c1 c2 c3 c4 : word) (pad1 pad2 pad3 pad4 rest : list byte)
      (w0 r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word),
    W4F' mm [C8 w0; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + 3 * seg)); C8 (Z_to_bv 64 (DST + dcap - 3));
             C8 (Z_to_bv 64 seg); C8 c3; C8 c2; C8 c1; C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap);
             C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg)); C8 (Z_to_bv 64 (DST + dcap))]
            (W4BD c1 b1 pad1 (SS + 6) pt1 ++ [CB 112 rest]) (W4BD c4 b4 pad4 (SS + 6 + l1 + l2 + l3) pt4)
            (W4BD c3 b3 pad3 (SS + 6 + l1 + l2) pt3) (W4BD c2 b2 pad2 (SS + 6 + l1) pt2) ->
    1 <= l1 < 65536 -> 1 <= l2 < 65536 -> 1 <= l3 < 65536 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap ->
    W4HINV pt1 l1 b1 -> W4HINV pt2 l2 b2 -> W4HINV pt3 l3 b3 -> W4HINV pt4 (n - (6 + l1 + l2 + l3)) b4 ->
    8 <= dcap - 3 * seg ->
    r1 = Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + pt4) -> r5 = Z_to_bv 64 b2 -> r6 = Z_to_bv 64 b3 -> r7 = Z_to_bv 64 b4 ->
    r10 = Z_to_bv 64 AW4_K10 -> r17 = Z_to_bv 64 b1 -> r18 = Z_to_bv 64 (SS + 6 + l1 + pt2) ->
    r19 = Z_to_bv 64 (SS + 6 + l1 + l2 + pt3) -> r20 = Z_to_bv 64 0 -> r21 = Z_to_bv 64 DST ->
    r24 = Z_to_bv 64 AW4_KSB -> r25 = Z_to_bv 64 (SS + 6 + pt1) -> r26 = Z_to_bv 64 (DT + 4) -> r27 = c4 ->
    r28 = Z_to_bv 64 (2^62) -> r29 = Z_to_bv 64 (64 - tl) -> r30 = Z_to_bv 64 (-1 * DT + -5) ->
    evtF bsegs RNG POST (ZS (AW4_S0C + 276) mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
                           r24 r25 r26 r27 r28 r29 r30 r31).
  Proof using All.
    intros. subst r1 r5 r6 r7 r10 r17 r18 r19 r20 r21 r24 r25 r26 r27 r28 r29 r30.
    exact (LOOP l1 l2 l3 0 pt1 pt2 pt3 pt4 b1 b2 b3 b4 c1 c2 c3 c4 pad1 pad2 pad3 pad4 rest w0 mm r8 r9 r11 r12 r13 r14 r15 r16
                r22 r23 r31 ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia)).
  Qed.

  Lemma w4c_s2 : forall mm (l1 l2 l3 pt1 pt2 pt3 pt4 b1 b2 b3 b4 : Z) (c1 c2 c3 c4 : word) (pad1 pad2 pad3 pad4 rest : list byte)
      (w0 w8 w16 w40 w48 w56 r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
       r30 r31 : word),
    W4F' mm [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
             C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
             C8 (Z_to_bv 64 (DST + dcap))]
            (W4BD c1 b1 pad1 (SS + 6) pt1 ++ [CB 112 rest]) (W4BD c4 b4 pad4 (SS + 6 + l1 + l2 + l3) pt4)
            (W4BD c3 b3 pad3 (SS + 6 + l1 + l2) pt3) (W4BD c2 b2 pad2 (SS + 6 + l1) pt2) ->
    1 <= l1 < 65536 -> 1 <= l2 < 65536 -> 1 <= l3 < 65536 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap ->
    W4HINV pt1 l1 b1 -> W4HINV pt2 l2 b2 -> W4HINV pt3 l3 b3 -> W4HINV pt4 (n - (6 + l1 + l2 + l3)) b4 ->
    r1 = Z_to_bv 64 (DST + 3 * seg) -> r8 = Z_to_bv 64 (DST + seg) -> r10 = Z_to_bv 64 AW4_K10 ->
    r18 = Z_to_bv 64 DST -> r19 = Z_to_bv 64 (tl + 256 * mtl) -> r20 = Z_to_bv 64 (DST + 3 * seg) ->
    r22 = Z_to_bv 64 (DST + 2 * seg) -> r23 = Z_to_bv 64 (DST + seg) -> r24 = Z_to_bv 64 AW4_KSB ->
    r26 = Z_to_bv 64 (DT + 4) -> r27 = Z_to_bv 64 seg ->
    evtF bsegs RNG POST (ZS (AW4_S0C + 4012) mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
                           r24 r25 r26 r27 r28 r29 r30 r31).
  Proof using All.
    intros. subst r1 r8 r10 r18 r19 r20 r22 r23 r24 r26 r27.
    pose proof (S2G l1 l2 l3 0 pt1 pt2 pt3 pt4 b1 b2 b3 b4 c1 c2 c3 c4 pad1 pad2 pad3 pad4 rest w0 w8 w16 w40 w48 w56 mm
                  r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r21 r25 r28 r29 r30 r31) as S2H.
    rewrite !Z.add_0_r in S2H.
    exact (S2H ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             (w4c_strm pt1 l1 b1 ltac:(assumption)) (w4c_strm pt2 l2 b2 ltac:(assumption))
             (w4c_strm pt3 l3 b3 ltac:(assumption)) (w4c_strm pt4 (n - (6 + l1 + l2 + l3)) b4 ltac:(assumption))
             ltac:(lia) ltac:(lia)).
  Qed.

  Ltac w4pack := unfold W4F, W4BD; cbn [app];
    replace (SP + -480 + 104) with (SP + -376) by lia; replace (SP + -480 + 256) with (SP + -224) by lia;
    replace (SP + -480 + 296) with (SP + -184) by lia; replace (SP + -480 + 336) with (SP + -144) by lia;
    split; [eexists; split; eassumption|];
    do 17 (split; [first [eassumption | reflexivity]|]); eassumption.
  Ltac w4fact K := zify_cond K.

  Lemma w4s0c : w4s0c_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                  src cbs.
  Proof using All.
    unfold w4s0c_goal.
    intros l1 l2 l3 w0 w1 w2 w3 w5 w6 w7 j1 j2 j3 j4 rest mm x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31
      WF L1 L2 L3 LN D6.
    pose proof w4c_sp as SPB. pose proof w4c_lay as LY.
    pose proof WF as WF0.
    destruct WF0 as (_ & _ & _ & _ & _ & _ & _ & MID & _ & B4 & _ & B3 & _ & B2 & _ & _ & _ & _ & _).
    apply (proj1 (rw_cells_app _ _ _ [CB 40 j1] [CB 112 rest])) in MID. destruct MID as (M1 & M2).
    cbn [cells_size csize Nat.add] in M2.
    replace (SP + -480 + 104) with (SP + -376) in M1 by lia.
    replace (SP + -480 + 104 + Z.of_nat 40) with (SP + -336) in M2 by lia.
    replace (SP + -480 + 256) with (SP + -224) in B4 by lia.
    replace (SP + -480 + 296) with (SP + -184) in B3 by lia.
    replace (SP + -480 + 336) with (SP + -144) in B2 by lia.
    w4run.
    eapply (w4c_cl _ mm (SP + -376) 6 l1 _ j1);
      [ lia | lia | exact WF | exact M1 | lia | lia | w4m8 | lia | lia | lia
      | reflexivity | unfold AW4_S0C; lia | unfold AW4_S0C; reflexivity | w4eq | w4eq | w4eq | | ].
    2: { intros m1 e1 c1' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID1 MU1 WM1 MI1 STK1 RW1.
         pose proof (w4c_eerr _ _ _ ID1) as E1.
         assert (M21 : rw_cells bsegs m1 (SP + -336) [CB 112 rest]) by w4keep M2 MU1 WM1.
         assert (B41 : rw_cells bsegs m1 (SP + -224) [CB 40 j4]) by w4keep B4 MU1 WM1.
         assert (B31 : rw_cells bsegs m1 (SP + -184) [CB 40 j3]) by w4keep B3 MU1 WM1.
         assert (B21 : rw_cells bsegs m1 (SP + -144) [CB 40 j2]) by w4keep B2 MU1 WM1.
         pose proof (w4c_mid _ _ _ RW1 eq_refl M21) as MD1.
         pose proof (w4c_rebuild mm m1 (SP + -376) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF MU1 WM1 MI1 STK1
                       MD1 eq_refl B41 eq_refl B31 eq_refl B21 eq_refl) as WF1.
         w4run. w4br. w4run. eapply w4c_err; exact WF1. }
    intros m1 d1 jp1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID1 BZ1 MU1 WM1 MI1 STK1 RW1.
    destruct (w4c_hinv 6 l1 d1 ltac:(lia) ltac:(lia) ltac:(lia) ID1) as (HV1 & LL1 & BB1).
    assert (M21 : rw_cells bsegs m1 (SP + -336) [CB 112 rest]) by w4keep M2 MU1 WM1.
    assert (B41 : rw_cells bsegs m1 (SP + -224) [CB 40 j4]) by w4keep B4 MU1 WM1.
    assert (B31 : rw_cells bsegs m1 (SP + -184) [CB 40 j3]) by w4keep B3 MU1 WM1.
    assert (B21 : rw_cells bsegs m1 (SP + -144) [CB 40 j2]) by w4keep B2 MU1 WM1.
    pose proof (w4c_mid _ _ _ RW1 eq_refl M21) as MD1.
    pose proof (w4c_rebuild mm m1 (SP + -376) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF MU1 WM1 MI1 STK1
                  MD1 eq_refl B41 eq_refl B31 eq_refl B21 eq_refl) as WF1.
    clear M1 B4 B3 B2 MU1 WM1 MI1 STK1 WF.
    w4run. w4br. w4run.
    eapply (w4c_cl _ m1 (SP + -144) (6 + l1) l2 _ j2);
      [ lia | lia | exact WF1 | exact B21 | lia | lia | w4m8 | lia | lia | lia
      | reflexivity | unfold AW4_S0C; lia | unfold AW4_S0C; reflexivity | w4eq | w4eq | w4eq | | ].
    2: { intros m2 e2 c2' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID2 MU2 WM2 MI2 STK2 RW2.
         pose proof (w4c_eerr _ _ _ ID2) as E2.
         w4kp MD1 MU2 WM2 MD2. w4kp B41 MU2 WM2 B42. w4kp B31 MU2 WM2 B32.
         pose proof (w4c_rebuild m1 m2 (SP + -144) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF1 MU2 WM2 MI2 STK2
                       MD2 eq_refl B42 eq_refl B32 eq_refl RW2 eq_refl) as WF2.
         w4run. w4br. w4run. eapply w4c_err; exact WF2. }
    intros m2 d2 jp2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID2 BZ2 MU2 WM2 MI2 STK2 RW2.
    destruct (w4c_hinv (6 + l1) l2 d2 ltac:(lia) ltac:(lia) ltac:(lia) ID2) as (HV2 & LL2 & BB2).
    w4kp MD1 MU2 WM2 MD2. w4kp B41 MU2 WM2 B42. w4kp B31 MU2 WM2 B32.
    pose proof (w4c_rebuild m1 m2 (SP + -144) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF1 MU2 WM2 MI2 STK2
                  MD2 eq_refl B42 eq_refl B32 eq_refl RW2 eq_refl) as WF2.
    clear MD1 B41 B31 B21 MU2 WM2 MI2 STK2 WF1 M21 RW1.
    w4run. w4br. w4run.
    eapply (w4c_cl _ m2 (SP + -184) (6 + l1 + l2) l3 _ j3);
      [ lia | lia | exact WF2 | exact B32 | lia | lia | w4m8 | lia | lia | lia
      | reflexivity | unfold AW4_S0C; lia | unfold AW4_S0C; reflexivity | w4eq | w4eq | w4eq | | ].
    2: { intros m3 e3 c3' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID3 MU3 WM3 MI3 STK3 RW3.
         pose proof (w4c_eerr _ _ _ ID3) as E3.
         w4kp MD2 MU3 WM3 MD3. w4kp B42 MU3 WM3 B43. w4kp RW2 MU3 WM3 C23.
         pose proof (w4c_rebuild m2 m3 (SP + -184) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF2 MU3 WM3 MI3 STK3
                       MD3 eq_refl B43 eq_refl RW3 eq_refl C23 eq_refl) as WF3.
         w4run. w4br. w4run. eapply w4c_err; exact WF3. }
    intros m3 d3 jp3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID3 BZ3 MU3 WM3 MI3 STK3 RW3.
    destruct (w4c_hinv (6 + l1 + l2) l3 d3 ltac:(lia) ltac:(lia) ltac:(lia) ID3) as (HV3 & LL3 & BB3).
    w4kp MD2 MU3 WM3 MD3. w4kp B42 MU3 WM3 B43. w4kp RW2 MU3 WM3 C23.
    pose proof (w4c_rebuild m2 m3 (SP + -184) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF2 MU3 WM3 MI3 STK3
                  MD3 eq_refl B43 eq_refl RW3 eq_refl C23 eq_refl) as WF3.
    clear MD2 B42 B32 MU3 WM3 MI3 STK3 WF2 RW2.
    w4run. w4br. w4run.
    eapply (w4c_cl _ m3 (SP + -224) (6 + l1 + l2 + l3) (n - (6 + l1 + l2 + l3)) _ j4);
      [ lia | lia | exact WF3 | exact B43 | lia | lia | w4m8 | lia | lia | lia
      | reflexivity | unfold AW4_S0C; lia | unfold AW4_S0C; reflexivity | w4eq | w4eq | w4eq | | ].
    2: { intros m4 e4 c4' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID4 MU4 WM4 MI4 STK4 RW4.
         pose proof (w4c_eerr _ _ _ ID4) as E4.
         w4kp MD3 MU4 WM4 MD4. w4kp RW3 MU4 WM4 C34. w4kp C23 MU4 WM4 C24.
         pose proof (w4c_rebuild m3 m4 (SP + -224) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF3 MU4 WM4 MI4 STK4
                       MD4 eq_refl RW4 eq_refl C34 eq_refl C24 eq_refl) as WF4.
         w4run. w4br. w4run. eapply w4c_err; exact WF4. }
    intros m4 d4 jp4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID4 BZ4 MU4 WM4 MI4 STK4 RW4.
    destruct (w4c_hinv (6 + l1 + l2 + l3) (n - (6 + l1 + l2 + l3)) d4 ltac:(lia) ltac:(lia) ltac:(lia) ID4)
      as (HV4 & LL4 & BB4).
    w4kp MD3 MU4 WM4 MD4. w4kp RW3 MU4 WM4 C34. w4kp C23 MU4 WM4 C24.
    pose proof (w4c_rebuild m3 m4 (SP + -224) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF3 MU4 WM4 MI4 STK4
                  MD4 eq_refl RW4 eq_refl C34 eq_refl C24 eq_refl) as WF4.
    clear MD3 B43 C23 RW3 MU4 WM4 MI4 STK4 WF3 MD4 C24 C34 RW4.
    rewrite (w4c_bd _ d1 jp1 BZ1), (w4c_bd _ d2 jp2 BZ2), (w4c_bd _ d3 jp3 BZ3), (w4c_bd _ d4 jp4 BZ4) in WF4.
    replace (SS + (6 + l1)) with (SS + 6 + l1) in WF4 by lia.
    replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in WF4 by lia.
    replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in WF4 by lia.
    destruct WF4 as (BUF & BSS & BDT4 & BDT & STK & FRC & FRCS & MID & MIDS & L256 & L256S & L296 & L296S & L336 & L336S
                     & FRM & MI & MU & WM).
    replace (SP + -480 + 104) with (SP + -376) in MID by lia. replace (SP + -480 + 256) with (SP + -224) in L256 by lia.
    replace (SP + -480 + 296) with (SP + -184) in L296 by lia. replace (SP + -480 + 336) with (SP + -144) in L336 by lia.
    unfold W4BD in MID, L256, L296, L336. cbn [app] in MID.
    destruct (w4c_far ltac:(lia)) as (FA1 & FA2 & FA3 & FA4 & FA5).
    destruct BUF as (buf & BU & BL). pose proof TOK as (TL1 & _). unfold HUF_TABLELOG_MAX in TL1.
    w4run. w4br. w4run.
    if_cases KA.
    { w4run. replace (DST + dcap + -3) with (DST + dcap - 3) in FRC by lia;
      eapply (w4c_s2 _ l1 l2 l3 (bd_ptr d1) (bd_ptr d2) (bd_ptr d3) (bd_ptr d4) (bd_bits d1) (bd_bits d2) (bd_bits d3)
              (bd_bits d4) (Z_to_bv 64 (bd_cont d1)) (Z_to_bv 64 (bd_cont d2)) (Z_to_bv 64 (bd_cont d3))
              (Z_to_bv 64 (bd_cont d4)) jp1 jp2 jp3 jp4 rest);
      [ w4pack | .. ]; first [assumption | lia | w4eq]. }
    w4fact KA. w4run.
    if_cases KB.
    { w4run. replace (DST + dcap + -3) with (DST + dcap - 3) in FRC by lia;
      eapply (w4c_s2 _ l1 l2 l3 (bd_ptr d1) (bd_ptr d2) (bd_ptr d3) (bd_ptr d4) (bd_bits d1) (bd_bits d2) (bd_bits d3)
              (bd_bits d4) (Z_to_bv 64 (bd_cont d1)) (Z_to_bv 64 (bd_cont d2)) (Z_to_bv 64 (bd_cont d3))
              (Z_to_bv 64 (bd_cont d4)) jp1 jp2 jp3 jp4 rest);
      [ w4pack | .. ]; first [assumption | lia | w4eq]. }
    w4fact KB.
    assert (D8 : 8 <= dcap - 3 * seg).
    { pose proof w4c_d0 as (DA & DB & _). pose proof (@ATOP_hi rc) as AH2. clear - KA DA DB AH2 D6 DC.
      change 18446744073709551615 with (Z.ones 64) in KA. rewrite !Z.land_ones in KA by lia.
      Z.div_mod_to_equations. lia. }
    w4run. replace (DST + dcap + -3) with (DST + dcap - 3) in FRC by lia;
      eapply (w4c_loop _ l1 l2 l3 (bd_ptr d1) (bd_ptr d2) (bd_ptr d3) (bd_ptr d4) (bd_bits d1) (bd_bits d2) (bd_bits d3)
              (bd_bits d4) (Z_to_bv 64 (bd_cont d1)) (Z_to_bv 64 (bd_cont d2)) (Z_to_bv 64 (bd_cont d3))
              (Z_to_bv 64 (bd_cont d4)) jp1 jp2 jp3 jp4 rest);
      [ w4pack | .. ]; first [assumption | lia | w4eq].
  Qed.

  Hypothesis W4S0 : w4s0c_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                      src cbs ->
                    w4_slow_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT
                      mtl tl lo src cbs.

  Lemma w4s0_slow : w4_slow_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT
                      mtl tl lo src cbs.
  Proof using All. exact (W4S0 w4s0c). Qed.
End W4S0F.
End CANSEC1.
