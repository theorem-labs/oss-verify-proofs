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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4m AF_huf_w4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section W4S3I2.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -480).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation W4F' mm fr mid l256 l296 l336 :=
    (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm fr mid l256 l296 l336).

  (* [comment removed for export] *)
  Definition w4s33_goal : Prop :=
    forall (l1 l2 l3 q pt3 pt4 b3 b4 : Z) (c1 bw1 p1 a1 e1 c2 bw2 p2 a2 e2 c3 c4 : word) (pad1 pad2 pad3 pad4 rest : list byte)
           (w0 w8 w16 w40 w48 w56 : word) (mm : amem)
           (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 : word),
    W4F' mm (W4FRW DST dcap w0 w8 w16 w40 w48 w56)
         (W4DX c1 bw1 p1 a1 e1 pad1 ++ [CB 112 rest])
         (W4DS c4 b4 pad4 (SS + 6 + l1 + l2 + l3) pt4)
         (W4DS c3 b3 pad3 (SS + 6 + l1 + l2) pt3)
         (W4DX c2 bw2 p2 a2 e2 pad2) ->
    1 <= l1 < 65536 -> 1 <= l2 < 65536 -> 1 <= l3 < 65536 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    W4TS l3 pt3 b3 -> W4TS (n - (6 + l1 + l2 + l3)) pt4 b4 ->
    0 <= q -> 3 * seg + q <= dcap ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9
               x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (tl + 256 * mtl))
               (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) x23
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 AW4_D3) fc None mm (seg_rom bsegs)).
End W4S3I2.
End CANSEC1.
