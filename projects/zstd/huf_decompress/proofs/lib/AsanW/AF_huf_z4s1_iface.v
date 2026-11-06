(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Definition z1hd (L pt b : Z) : Prop := 0 <= pt /\ (pt = 0 \/ pt + 8 <= L) /\ 0 <= b <= 64 /\ (8 <= pt -> b <= 8).

(* [comment removed for export] *)
Definition z1ops (SEG q1 q2 q3 q4 : Z) : Prop :=
  0 <= q1 /\ q1 <= 2 * (q4 - 3 * SEG) /\ SEG <= q2 /\ q2 - SEG <= 2 * (q4 - 3 * SEG) /\
  2 * SEG <= q3 /\ q3 - 2 * SEG <= 2 * (q4 - 3 * SEG) /\ 3 * SEG <= q4.

Section CANSEC1. Context {rc : runConstT}.
Section Z4S1I.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).

  Definition z4s1_goal : Prop :=
    forall (l1 l2 l3 : Z) (q1 q2 q3 q4 pt1 pt2 pt3 pt4 b1 b2 b3 b4 : Z) (c1 c2 c3 c4 b4o : word)
           (w40 w272 w280 : word) (j0 j1 jp : list byte) (mm : amem)
           (x5 x6 x7 x8 x11 x14 x16 x17 x21 x23 x25 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
         (SPA w40 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (SS + 6 + l1))
              (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SS + 6)) (Z_to_bv 64 (DST + 2 * seg)) (Z_to_bv 64 (SS + 6 + l1 + l2))
              (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + 8)) (Z_to_bv 64 (DST + dcap - 7)) (Z_to_bv 64 (SS + 6 + 8))
              (Z_to_bv 64 (SS + 6 + l1 + 8)) (Z_to_bv 64 (SS + 6 + l1 + l2 + 8)) w272 w280
              (Z_to_bv 64 (SS + 6 + l1 + l2 + pt3)) c4 c1 (Z_to_bv 64 (DT + 4)) j0 j1)
         (BD4A c4 b4o jp (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + pt4)) (Z_to_bv 64 (SS + 6 + l1 + l2 + l3))
               (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + 8))) ->
    1 <= l1 -> 1 <= l2 -> 1 <= l3 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    z1hd l1 pt1 b1 -> z1hd l2 pt2 b2 -> z1hd l3 pt3 b3 -> z1hd (n - (6 + l1 + l2 + l3)) pt4 b4 ->
    z1ops seg q1 q2 q3 q4 -> q4 + 8 <= dcap ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -576)) gp tp x5 x6 x7 x8 (Z_to_bv 64 b1) (Z_to_bv 64 (DST + q4)) x11
               (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + pt4)) (Z_to_bv 64 (DST + q3)) x14 (Z_to_bv 64 (DST + q2)) x16 x17
               (Z_to_bv 64 b3) c3 (Z_to_bv 64 (DT + 4)) x21 (Z_to_bv 64 (SS + 6 + l1 + pt2)) x23 (Z_to_bv 64 (DST + q1)) x25
               (Z_to_bv 64 (SS + 6 + pt1)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (64 - tl)) c2 (Z_to_bv 64 b4) x31)
          FR (Z_to_bv 64 0x88820) fc None mm (seg_rom asegs)).
End Z4S1I.
End CANSEC1.
