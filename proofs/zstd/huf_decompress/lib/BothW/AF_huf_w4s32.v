(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_HufX1.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image PropExec Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4m AF_huf_w4e.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3_iface AF_huf_w4s3_iface2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3b AF_huf_w4p AFrameD.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s32z AF_huf_w4s32k AF_huf_w4s32k2 AF_huf_w4s32k3 AF_huf_w4s32c.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section W4S32.
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

  Hypothesis CONT3 : w4s33_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl
                        tl lo src cbs.

  Lemma w4s32_proof : w4s32_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl
                        tl lo src cbs.
Proof using All.
    unfold w4s32_goal.
    intros l1 l2 l3 q pt2 pt3 pt4 b2 b3 b4 c1 bw1 p1 a1 e1 c2 c3 c4 pad1 pad2 pad3 pad4 rest w0 w8 w16 w40 w48 w56 mm
           x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31
           HW HL1 HL2 HL3 HN D6 H3S TS2 TS3 TS4 HQ HQ2.
    pose proof (WB w4p_ctx mm _ _ _ _ _ (SS + 6 + l1) l2 HW D6 ltac:(lia) ltac:(lia) ltac:(lia))
      as ((bs0 & BS0 & BSL0) & HCB & HCBL & P2 & (ob & OB & OBL) & U1 & U2 & U3 & R1 & R2 & R3 &
          (A1 & L1 & A2 & L2 & A3 & L3 & M1 & M2 & M3 & Z1 & Z2 & Z3 & I1 & I2 & I3 & I4 & I5 & I6 & RS1 & RS2 & RS3) &
          AP1 & AP2 & AP3 & AP4 & AP5 & AP6 & AP7 & MI & RSP & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & ZT).
    assert (S8 : (SP + -144) mod 8 = 0).
    { pose proof (Z.div_mod SP 16 ltac:(lia)) as E16. rewrite SP16 in E16. rewrite E16.
      replace (16 * (SP / 16) + 0 + -144) with ((2 * (SP / 16) - 18) * 8) by lia. apply Z_mod_mult. }
    pose proof (WB w4p_rl mm _ _ _ _ _ (SS + 6 + l1) l2 (SP + -144) HW D6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S8)
      as ((bz & BZ & BZR & BZL & _) & HABS & STK & LO1 & LO2 & ART & SP8 & UST & RD40 & RSH & R496 & RSS & WIM' & WIS').
    pose proof HW as HW'. unfold W4F in HW'.
    destruct HW' as (_ & _ & _ & _ & ST & F0 & _ & _ & _ & _ & _ & _ & _ & K2 & _ & _ & _ & MU & WM).
    replace (SP + -480 + 336) with (SP + -144) in K2 by lia.
    unfold W4FRW in F0. cbv zeta in F0. unfold W4DS in K2.
    pose proof (w4e_sp AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (SPa & SPb & SPc & SPd).
    pose proof (w4e_blocks AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs pdt SBL SBH AH MTL TLM HDT LCB DSTF DC SRCB DJ2
      (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (w4e_d0 AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs AH DSTF DC DJ2
      (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (D1 & D2 & D3).
    pose proof (@ATOP_hi rc) as AT1. pose proof (@ATOP_lo rc) as AT2.
    pose proof TS2 as (TP0 & TPC & TB).
    assert (SG : 4 * seg <= dcap + 3 < 4 * seg + 4).
    { pose proof (Z.div_mod (dcap + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (dcap + 3) 4 ltac:(lia)). lia. }
    assert (EC : Z_to_bv 64 (bv_unsigned c2) = c2) by apply Z_to_bv_bv_unsigned.
    assert (CR : 0 <= bv_unsigned c2 < 2^64) by (pose proof (bv_unsigned_in_range _ c2) as CR0; unfold bv_modulus in CR0; exact CR0).
    assert (AP8 : KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16) by (unfold KXGoM.apart; lia).
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bz)) = l2) by (rewrite length_map; exact BZL).
    assert (KD :
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -144, SP + -104); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' -> stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -144) [C8 cw'; C4 bw'; CB 4 pad2; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          FR (Z_to_bv 64 0x8b994) fc None mm' (seg_rom bsegs)))).
    { intros mm' ob' cw' bw' pw' aw' ew' y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31
             MU' WM' MI' ST' OB' OBL' K2'.
      apply (CONT3 l1 l2 l3 q pt3 pt4 b3 b4 c1 bw1 p1 a1 e1 cw' bw' pw' aw' ew' c3 c4 pad1 pad2 pad3 pad4 rest
               w0 w8 w16 w40 w48 w56 mm' y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + 2 * seg))
               y23 y25 y27 y28 y29 y30 y31);
        [|exact HL1|exact HL2|exact HL3|exact HN|exact D6|exact H3S|exact TS3|exact TS4|exact HQ|exact HQ2].
      eapply (WB w4p_W4F_upd3 mm mm' _ _ _ _ _ _ _ _ (W4DX cw' bw' pw' aw' ew' pad2) (SP + -144) ob' HW
          ltac:(replace (SP + -144 + 40) with (SP + -104) by lia; exact MU') WM' MI' ST' OB' OBL');
        try lia.
      - left. split; [reflexivity | right; lia].
      - left. split; [reflexivity | right; lia].
      - left. split; [reflexivity | right; lia].
      - right. split; [exact K2' | reflexivity]. }
    refine (w4s32_d2 POST RNG mm FR fc gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31
              w0 w8 w16 w40 w48 w56 c2 pad2 SP DST dcap seg q DT (tl + 256 * mtl) tl mtl b2 (SS + 6 + l1) pt2
              F0 K2 MI RSP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HQ2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl _ _ _).
    - 
      intros HA.
      eapply w4s32_e2 with (bz := bz) (cbs := cbs) (ob := ob) (S := SS + 6 + l1) (pt := pt2) (b := b2) (tl := tl) (rsv := mtl)
        (len := l2) (lo := lo) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3);
        try exact KD; try eassumption; try lia.
      all: replace (SP + -104) with (SP + -144 + 40) by lia; exact UST.
    - 
      intros HA HB64.
      eapply w4s32_o2 with (x10 := gp) (x11 := gp) (x14 := gp) (x18 := gp) (S := SS + 6 + l1) (pt := pt2) (b := b2) (tl := tl) (rsv := mtl);
        try eassumption; try lia.
      intros;
      first [ eapply KD
            | eapply w4s32_tsw with (mm := mm) (lo := lo) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) (cbs := cbs) (ob := ob)
                (tl := tl) (rsv := mtl); [exact KD | ..] ];
      try (lazymatch goal with |- munch _ ?m ?m => apply munch_refl end);
      try (lazymatch goal with |- wmono _ ?m ?m => apply wmono_refl end);
      try (lazymatch goal with |- munch _ _ _ =>
          eapply munch_weaken; [ | eassumption]; unfold sub_fp; intros; cbn [outside] in *; tauto end);
      try eassumption;
      try (lazymatch goal with |- stk _ _ _ _ => eapply stk_transportD; [eassumption | eassumption | cbn [disjoint_from]; lia] end);
      try (lazymatch goal with |- u8arr _ _ _ _ =>
          eapply u8arr_transportD; [eassumption | eassumption | cbn [disjoint_from]; unfold KXGoM.apart in *; lia] end);
      try lia.
      all: eapply stk_transportD with (m := mm); [exact STK | eassumption | cbn [disjoint_from]; lia].
    - 
      intros HA HB64 y10.
      eapply (w4s32_lp (Z.to_nat seg)) with (mm0 := mm) (mm := mm) (i := 0) (off := pt2) (S := SS + 6 + l1) (b := b2)
        (c := bv_unsigned c2) (bs := map (Z_to_bv 8) bz) (len := l2) (cbs := cbs) (ob := ob) (tl := tl) (rsv := mtl)
        (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3);
        try eassumption; try lia.
      all: try (rewrite EC; eassumption).
      all: try (rewrite Z2Nat.id by lia; lia).
      all: try (lazymatch goal with |- munch _ ?m ?m => apply munch_refl end).
      all: try (lazymatch goal with |- wmono _ ?m ?m => apply wmono_refl end).
      all: try (eapply w4s32_e2k; [exact KD | apply munch_refl | apply wmono_refl | exact STK | lia]).
  Qed.

End W4S32.
End CANSEC1.
