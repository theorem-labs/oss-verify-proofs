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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition W4TS (L pt b : Z) : Prop := 0 <= pt /\ (pt = 0 \/ (1 <= pt /\ pt + 8 <= L /\ b <= 64)) /\ 0 <= b < 2^31.
Definition W4DS (c : word) (b : Z) (pad : list byte) (S pt : Z) : list cell :=
  [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))].
Definition W4DX (c bw p a e : word) (pad : list byte) : list cell := [C8 c; C4 bw; CB 4 pad; C8 p; C8 a; C8 e].
Definition W4FRW (DST dcap : Z) (w0 w8 w16 w40 w48 w56 : word) : list cell :=
  let seg := (dcap + 3) / 4 in
  [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
   C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
   C8 (Z_to_bv 64 (DST + dcap))].
Definition AW4_D2 : Z := 0x8b340.
Definition AW4_D3 : Z := 0x8b994.
Definition AW4_D4 : Z := 0x8bff0.

Section CANSEC1. Context {rc : runConstT}.
Section W4S3I.
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
  Definition w4s32_goal : Prop :=
    forall (l1 l2 l3 q pt2 pt3 pt4 b2 b3 b4 : Z) (c1 bw1 p1 a1 e1 c2 c3 c4 : word) (pad1 pad2 pad3 pad4 rest : list byte)
           (w0 w8 w16 w40 w48 w56 : word) (mm : amem)
           (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 : word),
    W4F' mm (W4FRW DST dcap w0 w8 w16 w40 w48 w56)
         (W4DX c1 bw1 p1 a1 e1 pad1 ++ [CB 112 rest])
         (W4DS c4 b4 pad4 (SS + 6 + l1 + l2 + l3) pt4)
         (W4DS c3 b3 pad3 (SS + 6 + l1 + l2) pt3)
         (W4DS c2 b2 pad2 (SS + 6 + l1) pt2) ->
    1 <= l1 < 65536 -> 1 <= l2 < 65536 -> 1 <= l3 < 65536 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    W4TS l2 pt2 b2 -> W4TS l3 pt3 b3 -> W4TS (n - (6 + l1 + l2 + l3)) pt4 b4 ->
    0 <= q -> 3 * seg + q <= dcap ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q)) x9
               x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (tl + 256 * mtl))
               (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) x23
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 AW4_D2) fc None mm (seg_rom bsegs)).
End W4S3I.
End CANSEC1.
