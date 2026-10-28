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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3_iface AF_huf_w4s3_iface2 AF_huf_w4s3_iface3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3b AF_huf_w4p AF_huf_w4s34z AF_huf_w4s34k AF_huf_w4s34c AF_huf_w4s34k2 AF_huf_w4s34k3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require InitMem.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC0. Context {rc : runConstT}.
Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
Import KXS.
  

Ltac w4l4_exit lem A1 L1 A2 L2 A3 L3 KD :=
  eapply lem with (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3);
  try eassumption; try lia; try (Z.div_mod_to_equations; lia);
  let mm1 := fresh "mm1" in let ob1 := fresh "ob1" in let c1 := fresh "c1" in let b1 := fresh "b1" in
  let wp1 := fresh "wp1" in let ws1 := fresh "ws1" in let we1 := fresh "we1" in
  intros mm1 ob1 c1 b1 wp1 ws1 we1; intros;
  eapply (KD mm1 ob1 c1 b1 wp1 ws1 we1); try eassumption; try lia;
  first [ (eapply munch_trans; eassumption) | (eapply wmono_trans; eassumption) | idtac ].

Lemma w4s34_l4 : forall (n : nat) (Q : machine_state -> Prop) (RNG : footprint) (mm0 mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
 dcap - 3 * seg - q - i <= 4 * Z.of_nat n ->
 munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm0 mm -> wmono bsegs mm0 mm ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> 1 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word) (j : Z)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
    0 <= j -> 3 * seg + q + j <= dcap ->
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm0 mm' -> wmono bsegs mm0 mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + j)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  induction n as [|n IH]; intros until len; intros HN MU0 WM0; intros;
    (match goal with H : forall (_ : amem) (_ : list byte) (_ _ : Z) (_ _ _ : word), _ |- _ => rename H into KD end);
    pose proof w4s34_hcb as HCB; unfold w4s34_hcb_case in HCB.
  all: destruct (Z.eq_dec off 0) as [HOZ|HOZ];
    [ w4l4_exit w4s34_hz A1 L1 A2 L2 A3 L3 KD
    | destruct (Z_le_gt_dec 8 off) as [HO8|HO8];
      [ destruct (Z_lt_le_dec dcap (3 * seg + q + i + 4)) as [HXE|HXE];
        [ w4l4_exit w4s34_hfx A1 L1 A2 L2 A3 L3 KD | ]
      | destruct (Z_le_gt_dec b (8 * off + 7)) as [HB8|HB8];
        [ destruct (Z_lt_le_dec dcap (3 * seg + q + i + 4)) as [HXE|HXE];
          [ w4l4_exit w4s34_hcx A1 L1 A2 L2 A3 L3 KD | ]
        | w4l4_exit HCB A1 L1 A2 L2 A3 L3 KD ] ] ].
  - lia.
  - lia.
  - eapply w4s34_l4f with (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
    intros mm1 ob1 c1 b1 y1 y7 y8 y9 y10 y12 y13 y18 y22 y23 y25 y27 y28 y29 y30 y31 MU1 WM1 MI1 U1 UL1 CF1 CD1. intros.
    replace (S + off - b / 8) with (S + (off - b / 8)) in CD1 by lia.
    assert (MU2 : munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm0 mm1).
    { eapply munch_trans; [exact MU0 | eapply munch_weaken; [ | exact MU1]; apply w4s34_sub2; lia]. }
    pose proof (wmono_trans _ _ _ _ WM0 WM1) as WM2.
    eapply IH with (off := off - b / 8) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia; try (Z.div_mod_to_equations; lia).
  - eapply w4s34_hca with (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
    intros mm1 ob1 c1 b1 y1 y7 y8 y9 y10 y12 y13 y18 y22 y23 y25 y27 y28 y29 y30 y31 MU1 WM1 MI1 U1 UL1 CF1 CD1. intros.
    replace (S + off - b / 8) with (S + (off - b / 8)) in CD1 by lia.
    assert (MU2 : munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm0 mm1).
    { eapply munch_trans; [exact MU0 | eapply munch_weaken; [ | exact MU1]; apply w4s34_sub2; lia]. }
    pose proof (wmono_trans _ _ _ _ WM0 WM1) as WM2.
    eapply IH with (off := off - b / 8) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia; try (Z.div_mod_to_equations; lia).
Time Qed.


End CANSEC0.

Section CANSEC1. Context {rc : runConstT}.
Lemma w4s34_wr_stk : forall m A n, wr_at bsegs m A n -> AIMG_HI <= A -> 0 <= n -> stk bsegs m A (A + n).
Proof.
  intros m A n WR HA HN.
  destruct (Shadow.rw_cells_of_wr_at bsegs m A n WR ltac:(apply no_image_asan; unfold AIMG_HI in *; lia) HN) as (bs & BL & BC).
  pose proof (stk_of_rw_cells _ _ _ _ BC) as S. cbn [cells_size csize] in S. rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S.
Qed.

Section W4S34.
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

  Hypothesis CONT : w4s34_ck_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl
                        tl lo src cbs.

  Notation W4F' mm fr mid l256 l296 l336 :=
    (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm fr mid l256 l296 l336).

  Lemma w4s34_proof : w4s34_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl
                        tl lo src cbs.
  Proof using All.
    unfold w4s34_goal.
    intros l1 l2 l3 q pt4 b4 c1 bw1 p1 a1 e1 c2 bw2 p2 a2 e2 c3 bw3 p3 a3 e3 c4 pad1 pad2 pad3 pad4 rest w0 w8 w16 w40 w48 w56 mm
           x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31
           HW HL1 HL2 HL3 HN D6 H3S TS4 HQ HQ2.
    pose proof (WB w4p_ctx mm _ _ _ _ _ (SS + 6 + l1 + l2 + l3) (n - (6 + l1 + l2 + l3)) HW D6 ltac:(lia) ltac:(lia) ltac:(lia))
      as ((bs & BS & BSL) & HCB & HCBL & P2 & (ob & OB & OBL) & U1 & U2 & U3 & R1 & R2 & R3 &
          (A1 & L1 & A2 & L2 & A3 & L3 & M1 & M2 & M3 & Z1 & Z2 & Z3 & I1 & I2 & I3 & I4 & I5 & I6 & RS1 & RS2 & RS3) &
          AP1 & AP2 & AP3 & AP4 & AP5 & AP6 & AP7 & MI & RSP & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & ZT).
    pose proof (WB w4p_rl mm _ _ _ _ _ (SS + 6 + l1 + l2 + l3) (n - (6 + l1 + l2 + l3)) (SP + -224) HW D6 ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia))
      as (_ & HABS & ST & LOA' & LOS' & ART & SP8 & UD & RD & RSD & R496 & RSS & WIM' & WIS').
    pose proof HW as HW0. unfold W4F in HW0.
    destruct HW0 as (_ & _ & _ & _ & _ & F0 & _ & _ & _ & K4 & _ & _ & _ & _ & _ & _ & _ & MU & WM).
    replace (SP + -480 + 256) with (SP + -224) in K4 by lia.
    unfold W4FRW in F0. cbv zeta in F0. unfold W4DS in K4.
    pose proof (w4e_sp AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (SPa & SPb & SPc & SPd).
    pose proof (w4e_blocks AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs pdt SBL SBH AH MTL TLM HDT LCB DSTF DC SRCB DJ2
      (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (w4e_d0 AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs AH DSTF DC DJ2
      (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (D1 & D2 & D3).
    pose proof (@ATOP_hi rc) as AT1. pose proof (@ATOP_lo rc) as AT2.
    pose proof TS4 as (TP0 & TPC & TB).
    assert (SG : 4 * seg <= dcap + 3 < 4 * seg + 4).
    { pose proof (Z.div_mod (dcap + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (dcap + 3) 4 ltac:(lia)). lia. }
    assert (EC : Z_to_bv 64 (bv_unsigned c4) = c4) by apply Z_to_bv_bv_unsigned.
    assert (CR : 0 <= bv_unsigned c4 < 2^64) by (pose proof (bv_unsigned_in_range _ c4) as CR0; unfold bv_modulus in CR0; exact CR0).
    pose proof K4 as K4c. rewrite <- EC in K4c.
    assert (TBK : w4_tbok cbs tl).
    { unfold w4_tbok. intros i lo0 hi0 Hi HF.
      destruct (ZT (DT + 4 + i) ltac:(lia) lo0 hi0 ltac:(replace (DT + 4 + i - (DT + 4)) with i by lia; exact HF))
        as (b0 & RB & BB).
      exists b0. split; [|exact BB].
      pose proof HCB as (_ & _ & HB).
      pose proof (HB (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
      destruct (nth_error cbs (Z.to_nat i)) as [x|] eqn:EX.
      - try rewrite EX in E.
        pose proof (KXTac.rdn1_mrd bsegs mm _ _ E) as E2. unfold wa in E2. rewrite E2 in RB. injection RB as RB.
        subst x. reflexivity.
      - apply nth_error_None in EX. lia. }
    pose proof ART as (_ & _ & _ & _ & GC & _).
    assert (RCm : rclean mm rstk).
    { apply (rclean_transport _ m0 mm rstk RCL MU WM).
      unfold appW, KLOW, KHIGH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; lia. }
    pose proof (rclean_shclean _ _ RCm) as SHm.
    pose proof (shclean_hull _ _ _ _ _ SHm) as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6).
    assert (UST : unpoisoned mm (SP + -480) SP).
    { apply (shclean_unpoisoned mm _ _ (r_rlo rstk) (r_rhi rstk)). eapply shclean_sub; [exact SHm | lia | lia | lia]. }
    assert (RSH : rng RNG (shad (SP + -480)) (shlen (480 + 7))).
    { unfold rrng in RRS. apply (w4p_rng_sub RNG _ _ _ _ RRS); rewrite ?shad_div, ?shlen_div;
        clear - HU1 HU2 RLO RHI SPd SP16; Z.div_mod_to_equations; lia. }
    assert (GOT : rw_cells bsegs mm GOT_SHBASE [C8 (Z_to_bv 64 ASHBASE)]).
    { pose proof (AI_relro AI L RNG st LB mm (w4e_aheap AI L RNG st LB sp m0 DST dcap tl lo src cbs AH DSTF DC LOA LOS SPT mm MU WM))
        as RR.
      unfold ARELRO_LO, ARELRO_HI in RR.
      eapply InitMem.rw_cells_recast; [apply (InitMem.rw_cells_image0 bsegs mm GOT_SHBASE (le8 (Z_to_bv 64 ASHBASE)));
          [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply RR; rewrite length_le8 in Ha; unfold GOT_SHBASE in *; lia
          | vm_compute; reflexivity | unfold GOT_SHBASE; lia | rewrite length_le8; unfold GOT_SHBASE; lia ]
        | cbn; split; exact I | reflexivity | reflexivity]. }
    assert (RGT : rng RNG GOT_SHBASE 8) by (apply (w4p_rng_sub RNG _ _ _ _ WIM); unfold GOT_SHBASE; lia).
    assert (RAS : rng RNG ASHBASE 8) by (apply (w4p_rng_sub RNG _ _ _ _ WIM); unfold ASHBASE; lia).
    assert (WR496 : wr_at bsegs mm (SP + -496) 16).
    { pose proof ST as (S0 & S1 & S2). unfold wr_at. split; [lia|]. split; [lia|].
      intros i Hi. destruct (S2 (SP + -496 + i) ltac:(lia)) as (S3 & _). exact S3. }
    assert (APS : KXGoM.apart (SS + 6 + l1 + l2 + l3) (n - (6 + l1 + l2 + l3)) (SP + -496) 16).
    { pose proof HABS as HA0. unfold ablk, AIMG_HI, KLS in HA0. unfold KXGoM.apart. lia. }
    assert (KC : forall (mA mm' : amem) (lA : list cell) (ob' : list byte) (cw bw pw aw ew : word)
                   (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
        W4F' mA (W4FRW DST dcap w0 w8 w16 w40 w48 w56) (W4DX c1 bw1 p1 a1 e1 pad1 ++ [CB 112 rest]) lA
             (W4DX c3 bw3 p3 a3 e3 pad3) (W4DX c2 bw2 p2 a2 e2 pad2) ->
        munch [(DST, DST + dcap); (SP + -224, SP + -184)] mA mm' -> wmono bsegs mA mm' -> mem_inv bsegs mm' ->
        u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
        rw_cells bsegs mm' (SP + -224) [C8 cw; C4 bw; CB 4 pad4; C8 pw; C8 aw; C8 ew] ->
        evtF bsegs RNG POST (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
                 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
            FR (Z_to_bv 64 AW4_CK) fc None mm' (seg_rom bsegs))).
    { intros mA mm' lA ob' cw bw pw aw ew y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26
             y27 y28 y29 y30 y31 HWA MU' WM' MI' OB' OBL' K4'.
      apply (CONT c1 bw1 p1 a1 e1 c2 bw2 p2 a2 e2 c3 bw3 p3 a3 e3 cw bw pw aw ew pad1 pad2 pad3 pad4 rest
               w0 w8 w16 w40 w48 w56 mm' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26
               y27 y28 y29 y30 y31).
      replace (SP + -184) with (SP + -224 + 40) in MU' by lia.
      apply (WB w4p_W4F_upd mA mm' _ _ _ _ _ _ (W4DX cw bw pw aw ew pad4) _ _ (SP + -224) ob' HWA MU' WM' MI' OB' OBL');
        [lia | lia | left; split; [reflexivity | lia] | right; split; [exact K4' | reflexivity]
        | left; split; [reflexivity | lia] | left; split; [reflexivity | lia]]. }
    assert (KM : forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word) (j : Z)
        (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
        0 <= j -> 3 * seg + q + j <= dcap ->
        W4F' mm' (W4FRW DST dcap w0 w8 w16 w40 w48 w56) (W4DX c1 bw1 p1 a1 e1 pad1 ++ [CB 112 rest]) (W4DX (Z_to_bv 64 c') (Z_to_bv 64 b') wp ws we pad4) (W4DX c3 bw3 p3 a3 e3 pad3) (W4DX c2 bw2 p2 a2 e2 pad2) -> mem_inv bsegs mm' ->
        u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
        rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad4; C8 wp; C8 ws; C8 we] ->
        0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
        evtF bsegs RNG POST
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
        y14 y15 y16 y17 y18
        (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + 3 * seg + q + j)) (Z_to_bv 64 4611686018427387904) y22 y23
        (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
        FR (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))).
    { intros mm' ob' c' b' wp ws we j y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31
             HJ0 HJ1 HWA MIA OBA OBLA K4A HCA HBA.
      pose proof (WB w4p_ctx mm' _ _ _ _ _ (SS + 6 + l1 + l2 + l3) (n - (6 + l1 + l2 + l3)) HWA D6 ltac:(lia) ltac:(lia) ltac:(lia))
        as ((bs' & BS' & BSL') & HCB' & HCBL' & P2' & (obx & OBx & OBLx) & U1' & U2' & U3' & R1' & R2' & R3' &
            (A1' & L1' & A2' & L2' & A3' & L3' & M1' & M2' & M3' & Z1' & Z2' & Z3' & I1' & I2' & I3' & I4' & I5' & I6' & RS1' & RS2' & RS3') &
            AP1' & AP2' & AP3' & AP4' & AP5' & AP6' & AP7' & MI' & RSP' & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & G9' & G10' &
            G11' & ZT').
      pose proof HWA as HW1. unfold W4F in HW1.
      destruct HW1 as (_ & _ & _ & _ & _ & F1 & _).
      unfold W4FRW in F1. cbv zeta in F1.
      pose proof w4s34_g4 as G4L. unfold w4s34_g4_case in G4L.
      eapply G4L with (mm := mm') (dcap := dcap) (tl := tl) (rsv := mtl) (j := j).
      all: try first [ eassumption | lia ].
      - intros HLT.
        pose proof w4s34_t4 as T4L. unfold w4s34_t4_case in T4L.
        eapply (T4L (Z.to_nat (dcap - 3 * seg - q - j))) with (mm0 := mm') (mm := mm') (pw := wp) (aw := ws) (ew := we)
          (pad1 := pad4) (cbs := cbs) (ob := ob') (dcap := dcap) (b := b') (c := c') (tl := tl) (rsv := mtl) (j := j)
          (A2 := A2') (L2 := L2') (A3 := A3') (L3 := L3').
        all: try first [ eassumption | lia | (rewrite Z2Nat.id by lia; lia) | apply munch_refl | apply wmono_refl ].
        intros mm2 ob2 cw bw pw aw ew z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z20 z22 z23 z25 z27 z28 z29 z30 z31
               MU2 WM2 MI2 OB2 OBL2 K42.
        eapply KC; [exact HWA | exact MU2 | exact WM2 | exact MI2 | exact OB2 | exact OBL2 | exact K42].
      - intros HEQ y10'.
        eapply KC; [exact HWA | apply munch_refl | apply wmono_refl | exact MIA | exact OBA | exact OBLA | exact K4A]. }
    assert (KG : forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word) (j : Z)
        (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
        0 <= j -> 3 * seg + q + j <= dcap ->
        munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
        u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
        rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad4; C8 wp; C8 ws; C8 we] ->
        0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
        evtF bsegs RNG POST
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
        y14 y15 y16 y17 y18
        (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + 3 * seg + q + j)) (Z_to_bv 64 4611686018427387904) y22 y23
        (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
        FR (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))).
    { intros mm' ob' c' b' wp ws we j y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31
             HJ0 HJ1 MU' WM' MI' OB' OBL' K4' HC' HB'.
      replace (SP + -184) with (SP + -224 + 40) in MU' by lia.
      eapply KM; [exact HJ0 | exact HJ1 | | exact MI' | exact OB' | exact OBL' | exact K4' | exact HC' | exact HB'].
      apply (WB w4p_W4F_upd mm mm' _ _ _ _ _ _ (W4DX (Z_to_bv 64 c') (Z_to_bv 64 b') wp ws we pad4) _ _ (SP + -224) ob' HW
               MU' WM' MI' OB' OBL');
        [lia | lia | left; split; [reflexivity | lia] | right; split; [exact K4' | reflexivity]
        | left; split; [reflexivity | lia] | left; split; [reflexivity | lia]]. }
    assert (KG3 : forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word) (j : Z)
        (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
        0 <= j -> 3 * seg + q + j <= dcap ->
        munch [(DST, DST + dcap); (SP + -224, SP + -184); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
        u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
        rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad4; C8 wp; C8 ws; C8 we] ->
        0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
        evtF bsegs RNG POST
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
        y14 y15 y16 y17 y18
        (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + 3 * seg + q + j)) (Z_to_bv 64 4611686018427387904) y22 y23
        (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
        FR (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))).
    { intros mm' ob' c' b' wp ws we j y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31
             HJ0 HJ1 MU' WM' MI' OB' OBL' K4' HC' HB'.
      assert (ST' : stk bsegs mm' lo (SP + -480)).
      { apply (stk_merge bsegs mm' lo (SP + -496) (SP + -480)); [ | | lia].
        - apply (stk_transport_disjoint bsegs [(DST, DST + dcap); (SP + -224, SP + -184); (SP + -496, SP + -480)] mm mm' lo
                   (SP + -496));
            [exact (proj1 (stk_split bsegs mm lo (SP + -496) (SP + -480) ST ltac:(lia))) | exact MU' | exact WM' | ].
          cbn [disjoint_from]. repeat split; try exact I; lia.
        - replace (SP + -480) with (SP + -496 + 16) by lia. apply w4s34_wr_stk; [ | unfold AIMG_HI in *; lia | lia].
          apply (wr_at_transport bsegs mm mm'); [exact WR496 | exact WM']. }
      replace (SP + -184) with (SP + -224 + 40) in MU' by lia.
      eapply KM; [exact HJ0 | exact HJ1 | | exact MI' | exact OB' | exact OBL' | exact K4' | exact HC' | exact HB'].
      apply (WB w4p_W4F_upd3 mm mm' _ _ _ _ _ _ (W4DX (Z_to_bv 64 c') (Z_to_bv 64 b') wp ws we pad4) _ _ (SP + -224) ob' HW
               MU' WM' MI' ST' OB' OBL');
        [lia | lia | left; split; [reflexivity | lia] | right; split; [exact K4' | reflexivity]
        | left; split; [reflexivity | lia] | left; split; [reflexivity | lia]]. }
    destruct (Z_le_gt_dec b4 64) as [HB64|HB64].
    - destruct (Z_le_gt_dec (3 * seg + q + 4) dcap) as [HDL|HDE].
      + pose proof w4s34_d4L as D4L. unfold w4s34_d4L_case in D4L.
        eapply D4L with (S := SS + 6 + l1 + l2 + l3) (len := n - (6 + l1 + l2 + l3)) (off := pt4) (b := b4) (c := bv_unsigned c4)
          (pad1 := pad4) (bs := bs) (cbs := cbs) (ob := ob) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3)
          (dcap := dcap) (tl := tl) (rsv := mtl).
        all: try first [ eassumption | lia ].
        intros y1 y7 y8 y9 y10 y12 y13 y18 y22 y23 y25 y27 y28 y29 y30 y31.
        eapply (w4s34_l4 (Z.to_nat (dcap - 3 * seg - q))) with (mm0 := mm) (S := SS + 6 + l1 + l2 + l3)
          (len := n - (6 + l1 + l2 + l3)) (off := pt4) (b := b4) (c := bv_unsigned c4) (pad1 := pad4) (bs := bs) (cbs := cbs)
          (ob := ob) (i := 0) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) (dcap := dcap) (tl := tl)
          (rsv := mtl).
        all: try first [ eassumption | lia | (rewrite Z2Nat.id by lia; lia) | apply munch_refl | apply wmono_refl ].
      + pose proof w4s34_d4E as D4E. unfold w4s34_d4E_case in D4E.
        eapply D4E with (S := SS + 6 + l1 + l2 + l3) (len := n - (6 + l1 + l2 + l3)) (off := pt4) (b := b4) (c := bv_unsigned c4)
          (pad1 := pad4) (bs := bs) (cbs := cbs) (ob := ob) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3)
          (dcap := dcap) (tl := tl) (rsv := mtl).
        all: try first [ eassumption | lia ].
        intros y1 y5 y6 y7 y8 y9 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31.
        destruct (Z.eq_dec pt4 0) as [HP0|HP0].
        * pose proof w4s34_ez as EZ. unfold w4s34_ez_case2 in EZ.
          eapply EZ with (S := SS + 6 + l1 + l2 + l3) (len := n - (6 + l1 + l2 + l3)) (off := pt4) (b := b4) (c := bv_unsigned c4) (pad1 := pad4) (bs := bs) (cbs := cbs) (ob := ob) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) (dcap := dcap) (tl := tl) (rsv := mtl).
          all: try first [ eassumption | lia | (Z.div_mod_to_equations; lia) ].
          intros mm1 ob1 c1x b1x wp1 ws1 we1 v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v22 v23 v25 v27 v28 v29 v30 v31
                 MU1 WM1 MI1 OB1 OBL1 K41 HC1 HB1.
          replace (DST + 3 * seg + q) with (DST + 3 * seg + q + 0) by lia.
          eapply KG; first [ eassumption | lia ].
        * assert (HP1 : 1 <= pt4 /\ pt4 + 8 <= n - (6 + l1 + l2 + l3)) by (destruct TPC as [HT|(HT1 & HT2 & _)]; lia).
          destruct (Z_le_gt_dec 8 pt4) as [HP8|HP8].
          -- pose proof w4s34_ef as EF. unfold w4s34_ef_case2 in EF.
             eapply EF with (S := SS + 6 + l1 + l2 + l3) (len := n - (6 + l1 + l2 + l3)) (off := pt4) (b := b4) (c := bv_unsigned c4) (pad1 := pad4) (bs := bs) (cbs := cbs) (ob := ob) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) (dcap := dcap) (tl := tl) (rsv := mtl).
             all: try first [ eassumption | lia | (Z.div_mod_to_equations; lia) ].
          intros mm1 ob1 c1x b1x wp1 ws1 we1 v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v22 v23 v25 v27 v28 v29 v30 v31
                 MU1 WM1 MI1 OB1 OBL1 K41 HC1 HB1.
          replace (DST + 3 * seg + q) with (DST + 3 * seg + q + 0) by lia.
          eapply KG3; first [ eassumption | lia ].
          -- destruct (Z_le_gt_dec (b4 / 8) pt4) as [HBO|HBO].
             ++ pose proof w4s34_eca as ECA. unfold w4s34_eca_case2 in ECA.
                eapply ECA with (S := SS + 6 + l1 + l2 + l3) (len := n - (6 + l1 + l2 + l3)) (off := pt4) (b := b4) (c := bv_unsigned c4) (pad1 := pad4) (bs := bs) (cbs := cbs) (ob := ob) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) (dcap := dcap) (tl := tl) (rsv := mtl).
                all: try first [ eassumption | lia | (Z.div_mod_to_equations; lia) ].
          intros mm1 ob1 c1x b1x wp1 ws1 we1 v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v22 v23 v25 v27 v28 v29 v30 v31
                 MU1 WM1 MI1 OB1 OBL1 K41 HC1 HB1.
          replace (DST + 3 * seg + q) with (DST + 3 * seg + q + 0) by lia.
          eapply KG; first [ eassumption | lia ].
             ++ pose proof w4s34_ecb as ECBL. unfold w4s34_ecb_case2 in ECBL.
                eapply ECBL with (S := SS + 6 + l1 + l2 + l3) (len := n - (6 + l1 + l2 + l3)) (off := pt4) (b := b4) (c := bv_unsigned c4) (pad1 := pad4) (bs := bs) (cbs := cbs) (ob := ob) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) (dcap := dcap) (tl := tl) (rsv := mtl).
                all: try first [ eassumption | lia | (Z.div_mod_to_equations; lia) ].
          intros mm1 ob1 c1x b1x wp1 ws1 we1 v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v22 v23 v25 v27 v28 v29 v30 v31
                 MU1 WM1 MI1 OB1 OBL1 K41 HC1 HB1.
          replace (DST + 3 * seg + q) with (DST + 3 * seg + q + 0) by lia.
          eapply KG; first [ eassumption | lia ].
    - assert (HP0 : pt4 = 0) by (destruct TPC as [HT|(_ & _ & HT)]; lia).
      destruct (Z_le_gt_dec (3 * seg + q + 4) dcap) as [HDL|HDE].
      + pose proof w4s34_d4XL as DXL. unfold w4s34_d4XL_case2 in DXL.
        eapply DXL with (S := SS + 6 + l1 + l2 + l3) (len := n - (6 + l1 + l2 + l3)) (off := pt4) (b := b4) (c := bv_unsigned c4) (pad1 := pad4) (bs := bs) (cbs := cbs) (ob := ob) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) (dcap := dcap) (tl := tl) (rsv := mtl).
        all: try first [ eassumption | lia ].
          intros mm1 ob1 c1x b1x wp1 ws1 we1 v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v22 v23 v25 v27 v28 v29 v30 v31
                 MU1 WM1 MI1 OB1 OBL1 K41 HC1 HB1.
          replace (DST + 3 * seg + q) with (DST + 3 * seg + q + 0) by lia.
          eapply KG; first [ eassumption | lia ].
      + pose proof w4s34_d4XE as DXE. unfold w4s34_d4XE_case2 in DXE.
        eapply DXE with (S := SS + 6 + l1 + l2 + l3) (len := n - (6 + l1 + l2 + l3)) (off := pt4) (b := b4) (c := bv_unsigned c4) (pad1 := pad4) (bs := bs) (cbs := cbs) (ob := ob) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) (dcap := dcap) (tl := tl) (rsv := mtl).
        all: try first [ eassumption | lia ].
          intros mm1 ob1 c1x b1x wp1 ws1 we1 v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v22 v23 v25 v27 v28 v29 v30 v31
                 MU1 WM1 MI1 OB1 OBL1 K41 HC1 HB1.
          replace (DST + 3 * seg + q) with (DST + 3 * seg + q + 0) by lia.
          eapply KG; first [ eassumption | lia ].
  Time Qed.

End W4S34.
End CANSEC1.
