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
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4s_iface AF_huf_w4sb AF_huf_w4s12_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section W4S3I.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -496).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation W4SF' mm sa sb bd4 := (W4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm sa sb bd4).

  (* [comment removed for export] *)
  Definition w4s32_goal : Prop :=
    forall (l1 l2 l3 q pt2 pt3 pt4 b2 b3 b4 : Z) (c1 c2 c3 c4 : word)
           (w0 w8 w16 w40 w48 w56 w64 w72 w80 w88 w120 w128 w144 w152 w160 w168 : word) (jp : list byte) (mm : amem)
           (x5 x6 x10 x11 x12 x13 x14 x17 x20 x26 x27 x28 x29 x30 x31 : word),
    W4SF' mm [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 dcap); C8 w40; C8 w48; C8 w56; C8 w64;
              C8 w72; C8 w80; C8 w88; C8 (Z_to_bv 64 seg); C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (SS + 6 + l1 + l2));
              C8 w120; C8 w128]
             [C8 w144; C8 w152; C8 w160; C8 w168; C8 (Z_to_bv 64 (SS + 14)); C8 (Z_to_bv 64 (SS + 6 + l1 + 8));
              C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + 8)); C8 (Z_to_bv 64 (DST + 2 * seg)); C8 (Z_to_bv 64 (DST + seg));
              C8 c3; C8 c2; C8 c1]
             [C8 c4; C4 (Z_to_bv 64 b4); CB 4 jp; C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + pt4));
              C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + l3)); C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + 8))] ->
    1 <= l1 < 65536 -> 1 <= l2 < 65536 -> 1 <= l3 < 65536 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    W4STRM l2 pt2 b2 -> W4STRM l3 pt3 b3 -> W4STRM (n - (6 + l1 + l2 + l3)) pt4 b4 ->
    0 <= q -> 3 * seg + q <= dcap ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (DST + dcap + -3)) (Z_to_bv 64 SPF) gp tp x5 x6 (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (SS + 6 + l1 + l2))
               (Z_to_bv 64 (DST + dcap)) x10 x11 x12 x13 x14
               (Z_to_bv 64 (DST + seg + q)) (Z_to_bv 64 (DST + 3 * seg + q)) x17 (Z_to_bv 64 (SS + 6 + l1)) (Z_to_bv 64 b3)
               x20 (Z_to_bv 64 b2) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + 3 * seg))
               (Z_to_bv 64 (SS + 6 + l1 + l2 + pt3)) (Z_to_bv 64 (SS + 6 + l1 + pt2)) x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x91e48) fc None mm (seg_rom asegs)).
End W4S3I.
End CANSEC1.
