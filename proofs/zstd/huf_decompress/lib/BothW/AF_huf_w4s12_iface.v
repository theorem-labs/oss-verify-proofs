(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4m AF_huf_w4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_w4s12_iface () := "C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_w4sb3HDIK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00c5ARocqVerifyHarness?AgentSubmission5BothWBAF_huf_w4s12_iface6W4STRMK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).


Definition W4STRM (L pt b : Z) : Prop := 0 <= pt /\ (pt = 0 \/ pt + 8 <= L) /\ 0 <= b < 2^31.

Lemma HDI_W4STRM : forall L pt b, HDI L pt b -> W4STRM L pt b.
Proof. unfold HDI, W4STRM. lia. Qed.

Definition W4BD (c : word) (b : Z) (pad : list byte) (S pt : Z) : list cell :=
  [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))].
Definition W4HINV (o len b : Z) : Prop := 0 <= o /\ ((o + 8 <= len /\ 0 <= b <= 8) \/ (o = 0 /\ 0 <= b <= 64)).
Definition W4STRMt (L pt b : Z) : Prop := 0 <= pt /\ (pt = 0 \/ (1 <= pt /\ pt + 8 <= L /\ b <= 64)) /\ 0 <= b < 2^31.
Definition AW4_K10 : Z := 18446744073709551596.

Definition w4s_src_ctx (RNG : footprint) (mm : amem) (SS n SBL SBH : Z) : Prop :=
  mem_inv bsegs mm
  /\ (exists sbuf, bytes_at bsegs mm SS sbuf /\ Z.of_nat (length sbuf) = n)
  /\ unpoisoned mm SBL SBH /\ SBL <= SS /\ SS + n <= SBH /\ SBL mod 8 = 0
  /\ rng RNG SS n /\ rng RNG (shad SBL) (shlen (SBH - SBL + 7)) /\ rng_aimg RNG
  /\ 0x60d000 <= SS /\ SS + n <= 2^47 /\ 0x60d000 <= SBL /\ SBH <= 2^47.

Ltac w4s_src_intro C :=
  let MI := fresh "MI" in let sbuf := fresh "sbuf" in let SB := fresh "SB" in let SL := fresh "SL" in
  destruct C as (MI & (sbuf & SB & SL) & ?US & ?US1 & ?US2 & ?A8 & ?WS & ?WSS & ?WI & ?R1 & ?R2 & ?R3 & ?R4).

Section CANSEC1. Context {rc : runConstT}.
Section W4S12I.
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

  
  Definition w4s1_goal : Prop :=
    forall (l1 l2 l3 q pt1 pt2 pt3 pt4 b1 b2 b3 b4 : Z) (c1 c2 c3 c4 : word) (pad1 pad2 pad3 pad4 rest : list byte)
           (w0 : word) (mm : amem) (x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 : word),
    W4F' mm [C8 w0; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + 3 * seg)); C8 (Z_to_bv 64 (DST + dcap - 3));
             C8 (Z_to_bv 64 seg); C8 c3; C8 c2; C8 c1; C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap);
             C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg)); C8 (Z_to_bv 64 (DST + dcap))]
            (W4BD c1 b1 pad1 (SS + 6) pt1 ++ [CB 112 rest])
            (W4BD c4 b4 pad4 (SS + 6 + l1 + l2 + l3) pt4)
            (W4BD c3 b3 pad3 (SS + 6 + l1 + l2) pt3)
            (W4BD c2 b2 pad2 (SS + 6 + l1) pt2) ->
    1 <= l1 < 65536 -> 1 <= l2 < 65536 -> 1 <= l3 < 65536 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    W4HINV pt1 l1 b1 -> W4HINV pt2 l2 b2 -> W4HINV pt3 l3 b3 -> W4HINV pt4 (n - (6 + l1 + l2 + l3)) b4 ->
    8 <= dcap - 3 * seg -> 0 <= q -> 3 * seg + q + 4 <= dcap ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + pt4)) (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 b2) (Z_to_bv 64 b3) (Z_to_bv 64 b4)
               x8 x9 (Z_to_bv 64 AW4_K10) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 b1) (Z_to_bv 64 (SS + 6 + l1 + pt2))
               (Z_to_bv 64 (SS + 6 + l1 + l2 + pt3)) (Z_to_bv 64 q) (Z_to_bv 64 DST) x22 x23 (Z_to_bv 64 AW4_KSB)
               (Z_to_bv 64 (SS + 6 + pt1)) (Z_to_bv 64 (DT + 4)) c4 (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 (-1 * DT + -5)) x31)
          FR (Z_to_bv 64 0x89de4) fc None mm (seg_rom bsegs)).

  
  Definition w4s2_goal : Prop :=
    forall (l1 l2 l3 q pt1 pt2 pt3 pt4 b1 b2 b3 b4 : Z) (c1 c2 c3 c4 : word) (pad1 pad2 pad3 pad4 rest : list byte)
           (w0 w8 w16 w40 w48 w56 : word) (mm : amem)
           (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31 : word),
    W4F' mm [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
             C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
             C8 (Z_to_bv 64 (DST + dcap))]
            (W4BD c1 b1 pad1 (SS + 6) pt1 ++ [CB 112 rest])
            (W4BD c4 b4 pad4 (SS + 6 + l1 + l2 + l3) pt4)
            (W4BD c3 b3 pad3 (SS + 6 + l1 + l2) pt3)
            (W4BD c2 b2 pad2 (SS + 6 + l1) pt2) ->
    1 <= l1 < 65536 -> 1 <= l2 < 65536 -> 1 <= l3 < 65536 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    W4STRMt l1 pt1 b1 -> W4STRMt l2 pt2 b2 -> W4STRMt l3 pt3 b3 -> W4STRMt (n - (6 + l1 + l2 + l3)) pt4 b4 ->
    0 <= q -> 3 * seg + q <= dcap ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q)) x9
               (Z_to_bv 64 AW4_K10) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (tl + 256 * mtl))
               (Z_to_bv 64 (DST + 3 * seg + q)) x21 (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg))
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8ac7c) fc None mm (seg_rom bsegs)).
End W4S12I.
End CANSEC1.
