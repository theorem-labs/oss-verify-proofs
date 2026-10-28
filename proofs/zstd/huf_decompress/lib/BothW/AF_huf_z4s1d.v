(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
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
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Lemma z4_dm8 : forall h, 8 * (h / 8) + h mod 8 = h.
Proof. intros h. pose proof (Z.div_mod h 8 ltac:(lia)). lia. Qed.
Lemma z4_ads : forall a b, a + (b - a) = b.
Proof. intros. lia. Qed.

Lemma z4_pre_ok : forall L o b h, z4H L o b -> b <= h <= b + 48 -> z4R_pre L o (h / 8) (h mod 8) (8 <=? o).
Proof.
  intros L o b h H B. pose proof (Z.div_mod h 8 ltac:(lia)). pose proof (Z.mod_pos_bound h 8 ltac:(lia)).
  unfold z4R_pre, z4H in *. destruct (Z.leb_spec 8 o); lia.
Qed.
Lemma z4_post_h : forall L o b, z4R_post L o b -> z4H L o b.
Proof. intros L o b H. unfold z4R_post, z4H in *. lia. Qed.
Lemma z4_ops_q : forall dcap q1 q2 q3 q4, z1ops ((dcap + 3) / 4) q1 q2 q3 q4 -> q4 + 8 <= dcap -> 6 <= dcap ->
  q1 + 8 <= dcap /\ q2 + 8 <= dcap /\ q3 + 8 <= dcap /\
  0 <= q1 /\ (dcap + 3) / 4 <= q2 /\ 2 * ((dcap + 3) / 4) <= q3 /\ 3 * ((dcap + 3) / 4) <= q4.
Proof.
  intros dcap q1 q2 q3 q4 O Q D. pose proof (Z.div_mod (dcap + 3) 4 ltac:(lia)).
  pose proof (Z.mod_pos_bound (dcap + 3) 4 ltac:(lia)). unfold z1ops in O. lia.
Qed.
Lemma z4_ops_step : forall s q1 q2 q3 q4 e1 e2 e3 e4 q1' q2' q3' q4', z1ops s q1 q2 q3 q4 ->
  q1 + 3 <= e1 <= q1 + 6 -> q2 + 3 <= e2 <= q2 + 6 -> q3 + 3 <= e3 <= q3 + 6 -> q4 + 3 <= e4 <= q4 + 6 ->
  e1 + 1 <= q1' <= e1 + 2 -> e2 + 1 <= q2' <= e2 + 2 -> e3 + 1 <= q3' <= e3 + 2 -> e4 + 1 <= q4' <= e4 + 2 ->
  z1ops s q1' q2' q3' q4'.
Proof. intros. unfold z1ops in *. lia. Qed.
Lemma z4_meas : forall dcap q4 e4 q4', q4 + 8 <= dcap -> q4 + 3 <= e4 -> e4 + 1 <= q4' ->
  (Z.to_nat (dcap - q4') < Z.to_nat (dcap - q4))%nat.
Proof. intros. lia. Qed.
Lemma z4_eb : forall D q R, D + q + 3 <= R <= D + q + 6 -> q + 3 <= R - D <= q + 6.
Proof. intros. lia. Qed.


Section CANSEC1. Context {rc : runConstT}.
Section IT.
  Variable RNG : footprint.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop).
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

  Hypothesis CTXL : 6 <= dcap -> z4L_ctx RNG SP DST dcap seg DT tl mtl DL DT DTH cbs.
  Hypothesis SSB : 0 < n -> 16 <= SS /\ SS + n + 8 <= 2^47.
  Hypothesis MD1 : z4L_md1_goal RNG Q gp tp FR fc SP DST dcap seg DT tl mtl DL DT DTH cbs.
  Hypothesis MD2 : z4L_md2_goal RNG Q gp tp FR fc SP DST dcap seg DT tl mtl DL DT DTH cbs.
  Hypothesis MD3 : z4L_md3_goal RNG Q gp tp FR fc SP DST dcap seg DT tl mtl DL DT DTH cbs.
  Hypothesis MD4 : z4L_md4_goal RNG Q gp tp FR fc SP DST dcap seg DT tl mtl DL DT DTH cbs.
  Hypothesis RL : forall r1 r2 r3 r4,
    z4R_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r3 r4.
  Hypothesis B1 : forall mm w0 w4 w5 w7 k1 k2 k3 k4 b1 b2 b3 b4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4,
    SF mm w0 w4 w5 w7 k1 k2 k3 k4 b1 b2 b3 b4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4 ->
    MEM mm w0 w4 w5 w7 k1 k2 k3 k4 b1 b2 b3 b4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4.
  Hypothesis B2 : forall mm mm' w0 w4 w5 w7 v0 v4 v5 v7 k1 k2 k3 k4 b1 b2 b3 b4 h1 h2 h3 h4 l1 l2 l3 o1 o2 o3 o4
                         jp1 jp2 jp3 jp4,
    SF mm w0 w4 w5 w7 k1 k2 k3 k4 b1 b2 b3 b4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4 ->
    munch WM mm mm' -> wmono bsegs mm mm' ->
    MEM mm' v0 v4 v5 v7 k1 k2 k3 k4 h1 h2 h3 h4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4 ->
    SF mm' v0 v4 v5 v7 k1 k2 k3 k4 h1 h2 h3 h4 l1 l2 l3 o1 o2 o3 o4 jp1 jp2 jp3 jp4.

  Lemma z4s1_bnd : forall (l1 l2 l3 q1 q2 q3 q4 o1 o2 o3 o4 b1 b2 b3 b4 : Z) (k1 k2 k3 k4 : word),
    1 <= l1 -> 1 <= l2 -> 1 <= l3 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    z4H l1 o1 b1 -> z4H l2 o2 b2 -> z4H l3 o3 b3 -> z4H (n - (6 + l1 + l2 + l3)) o4 b4 ->
    z1ops seg q1 q2 q3 q4 -> q4 + 8 <= dcap ->
    z4L_bnd DST dcap (bv_unsigned k1) (bv_unsigned k2) (bv_unsigned k3) (bv_unsigned k4)
      (SS + 6 + o1) (SS + 6 + l1 + o2) (SS + 6 + l1 + l2 + o3) (SS + 6 + l1 + l2 + l3 + o4) b1 b2 b3 b4
      (DST + q1) (DST + q2) (DST + q3) (DST + q4).
  Proof using SSB.
    intros l1 l2 l3 q1 q2 q3 q4 o1 o2 o3 o4 b1 b2 b3 b4 k1 k2 k3 k4 L1 L2 L3 LN D6 D3 H1 H2 H3 H4 OPS Q4.
    destruct (SSB ltac:(lia)) as [S16 SB].
    pose proof (bv_unsigned_in_range _ k1) as K1. pose proof (bv_unsigned_in_range _ k2) as K2.
    pose proof (bv_unsigned_in_range _ k3) as K3. pose proof (bv_unsigned_in_range _ k4) as K4.
    unfold bv_modulus in K1, K2, K3, K4.
    pose proof (Z.div_mod (dcap + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (dcap + 3) 4 ltac:(lia)).
    unfold z4L_bnd, z4H, z1ops in *. lia.
  Qed.

  Lemma z4s1_it : z4I_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  Proof using CTXL SSB MD1 MD2 MD3 MD4 RL B1 B2.
    intros Z2 EPI mm l1 l2 l3 q1 q2 q3 q4. revert mm l1 l2 l3 q1 q2 q3.
    induction q4 as [q4 IH] using (well_founded_ind (well_founded_ltof _ (fun q => Z.to_nat (dcap - q)))).
    intros mm l1 l2 l3 q1 q2 q3 o1 o2 o3 o4 b1 b2 b3 b4 k1 k2 k3 k4 jp1 jp2 jp3 jp4 w0 w4 w5 w7
      x8 x10 x11 x13 x17 x22 x25 x27 x28 x29 SF0 L1 L2 L3 LN D6 D3 H1 H2 H3 H4 OPS Q4.
    pose proof (CTXL D6) as CX.
    pose proof (B1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF0) as M0.
    pose proof (z4s1_bnd l1 l2 l3 q1 q2 q3 q4 o1 o2 o3 o4 b1 b2 b3 b4 k1 k2 k3 k4 L1 L2 L3 LN D6 D3 H1 H2 H3 H4 OPS Q4)
      as BND.
    rewrite <- (Z_to_bv_bv_unsigned k1).
    eapply (MD1 CX). 1: exact M0. 1: exact BND.
    intros mm1 v0 v4 v5 v7 d1 d2 d3 d4 la lb lc ld y11 y13 y20 y27 y29 MU1 WM1 M1 La Lb Lc Ld E1 E2 E3 E4.
    eapply (MD2 CX). 1: exact M1. 1: exact BND. all: try assumption.
    intros mm2 u0 u4 u5 u7 U1 U2 U3 U4 f1 f2 f3 f4 l5 l6 l7 l8 z1 z11 z13 z28 z29 MU2 WM2 M2 L5 L6 L7 L8
      UU1 UU2 UU3 UU4 F1 F2 F3 F4.
    eapply (MD3 CX). 1: exact M2. 1: exact BND. all: try assumption.
    intros mm3 t0 t4 t5 t7 V1 V2 V3 V4 g1 g2 g3 g4 l9 l10 l11 l12 r11 r13 r26 r27 r29 MU3 WM3 M3 L9 L10 L11 L12
      VV1 VV2 VV3 VV4 G1 G2 G3 G4.
    eapply (MD4 CX). 1: exact M3. 1: exact BND. all: try assumption.
    intros mm4 p0 p4 p7 R1 R2 R3 R4 h1 h2 h3 h4 l13 l14 l15 l16 e13 e22 e23 e27 e28 e29 MU4 WM4 M4 L13 L14 L15 L16
      RR1 RR2 RR3 RR4 HH1 HH2 HH3 HH4.
    pose proof (munch_trans _ _ _ _ (munch_trans _ _ _ _ (munch_trans _ _ _ _ MU1 MU2) MU3) MU4) as MU.
    pose proof (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3) WM4) as WMO.
    pose proof (B2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF0 MU WMO M4) as SF4.
    (destruct (z4_ops_q dcap q1 q2 q3 q4 OPS Q4 D6) as (QA1 & QA2 & QA3 & QB1 & QB2 & QB3 & QB4)).
    (pose proof (z4_pre_ok _ _ _ _ H1 HH1) as P1; pose proof (z4_pre_ok _ _ _ _ H2 HH2) as P2;
          pose proof (z4_pre_ok _ _ _ _ H3 HH3) as P3; pose proof (z4_pre_ok _ _ _ _ H4 HH4) as P4).
    (pose proof (z4_eb _ _ _ RR1) as EB1; pose proof (z4_eb _ _ _ RR2) as EB2;
          pose proof (z4_eb _ _ _ RR3) as EB3; pose proof (z4_eb _ _ _ RR4) as EB4).
    pose proof (RL (8 <=? o1) (8 <=? o2) (8 <=? o3) (8 <=? o4) Z2 EPI mm4 l1 l2 l3 q1 q2 q3 q4
                   (R1 - DST) (R2 - DST) (R3 - DST) (R4 - DST) o1 o2 o3 o4
                   (h1 / 8) (h1 mod 8) (h2 / 8) (h2 mod 8) (h3 / 8) (h3 mod 8) (h4 / 8) (h4 mod 8)
                   k1 k2 k3 k4 jp1 jp2 jp3 jp4 p0 p4 p7 l13 l14 l15 l16 e13 e22 e23 e27 e28 e29) as G.
    (rewrite !z4_dm8, !z4_ads in G).
    (specialize (G SF4 L1 L2 L3 LN D6 D3 P1 P2 P3 P4 L13 L14 L15 L16 EB1 EB2 EB3 EB4 QA1 QA2 QA3 Q4 QB1 QB2 QB3 QB4)).
    (rewrite !Z_to_bv_bv_unsigned).
    (apply G; clear G).
    intros mm' q1' q2' q3' q4' o1' o2' o3' o4' b1' b2' b3' b4' k1' k2' k3' k4' w0' w4' w5' w7'
      y8 y10' y11' y13' y17 y22 y25 y27' y28 y29' SF' PP1 PP2 PP3 PP4 QQ1 QQ2 QQ3 QQ4 Q4'.
    (apply (IH q4' (z4_meas _ _ _ _ Q4 (proj1 EB4) (proj1 QQ4)) mm' l1 l2 l3 q1' q2' q3' o1' o2' o3' o4'
             b1' b2' b3' b4' k1' k2' k3' k4'
             jp1 jp2 jp3 jp4 w0' w4' w5' w7' y8 y10' y11' y13' y17 y22 y25 y27' y28 y29' SF' L1 L2 L3 LN D6 D3
             (z4_post_h _ _ _ PP1) (z4_post_h _ _ _ PP2) (z4_post_h _ _ _ PP3) (z4_post_h _ _ _ PP4)
             (z4_ops_step _ _ _ _ _ _ _ _ _ _ _ _ _ OPS EB1 EB2 EB3 EB4 QQ1 QQ2 QQ3 QQ4) Q4')).
  Qed.
End IT.
End CANSEC1.
