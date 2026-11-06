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
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4s_iface AF_huf_w4sb.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_w4s12_iface () := "C59OSSVerify5KrLib5AsanW;AF_huf_w4sb3HDIC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00c59OSSVerify5KrLib5AsanWBAF_huf_w4s12_iface6W4STRMC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Definition W4STRM (L pt b : Z) : Prop := 0 <= pt /\ (pt = 0 \/ pt + 8 <= L) /\ 0 <= b < 2^31.

Lemma HDI_W4STRM : forall L pt b, HDI L pt b -> W4STRM L pt b.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4s12_iface ()) [] "h01Hh14__x1h22H1h32H2h42H3h51Lh62_Hh77__arithh84__ffh98__varmaph:5__with;1bh<2ptp;3p;1p;2p;4p;8p;7g0000j3STg000jj13Tg001Oj18Tg001mj25Tg002Jj20Tg002fj24Tg003@R0j21Tg003[j39Tg004_j17Tg005Dj2ATg005aj2=Tg006=j1RTg006]j1QTg007=j2PTg007[j1MTg0089j1LTg008dj2:Tg009Gj2KTg009jj4<Tg00:Uj1GTg00;7j1FTg00;Uj3ETg00<8j8HTg00<\j2ITg00=>j2DTg00=Xj2JTg00>Dj3?Tg00>^j3CTg00?=j4BTg00?oj4@Tg00@Jj7NTg00@nj7OTg00ARR1f0R2'0p=2g00B0R3??21p=6f1R4g00BNR5g00BmR6P6g00CMR7P2g00CmFNp=;f2R8P5P6P6P7P4P2FOp=>AS842P0%28%68g00DMR9#3R:#3#3R;#8R<,58f3R='0'4%24R>%3;#3#3#8R;,04'110<8108<['1'1f4R??9=8P2%2?R=f5R@#615@<f6RA'0'410?;,1=10<@10@<['1'1P0%6A15A<f7R='0'4%2@10@;'110<A10A<['1f8R??9=AP2%6?15?<f9R='0'4%2?10?;'110<=10=<['1P0%2=10=;'1f:R0,0<100<[f<f;R?;90P2%2?10?;'1f=R?,0<10?<[f>R0#2%60150<f?'0'4R<%2?%8:R:%79#7#7#7RA#8'ARB,=?'1R?'1P=P<P?P@g00E2R@#R%Q@1P34%M3%L3R@P5P6P6P7P31:31g00E^R51K39R9C<,;@R?P3P9P51:3;C<,;@5>@%G6P3P9g00FE1:3:%FA5E3C<,;@9>@?GH1I@7P2P8g00FlR@g00GLR7'D1J28=?@7dAC314CBb8b9b:X13%22102;'11=4B,1>[^13P2P0P8O2b7C@C@W6W4P4P2O2n2001000000121000000W0W3P4P2O2n2001000000121000000W0W2P4P2O2n2001000000121000000W0X;3X<3X53o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section W4S12I.
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
  Definition w4s1_goal : Prop :=
    forall (l1 l2 l3 q pt1 pt2 pt3 pt4 b1 b2 b3 b4 : Z) (c1 c2 c3 c4 c4o b4o p4o : word)
           (w8 w16 w40 w48 w56 w64 : word) (jp : list byte) (mm : amem)
           (x1 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x29 x31 : word),
    W4SF' mm [C8 (Z_to_bv 64 DT); C8 w8; C8 w16; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 dcap); C8 w40; C8 w48; C8 w56; C8 w64;
              C8 (Z_to_bv 64 (SS + 6)); C8 (Z_to_bv 64 (SS + 6 + l1)); C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 seg);
              C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (SS + 6 + l1 + l2)); C8 (Z_to_bv 64 (DST + 2 * seg));
              C8 (Z_to_bv 64 (DST + 3 * seg))]
             [C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + 8)); C8 (Z_to_bv 64 (DST + dcap + -3));
              C8 (Z_to_bv 64 (DST + 3 * seg)); C8 (Z_to_bv 64 (SS + 14)); C8 (Z_to_bv 64 (SS + 6 + l1 + 8));
              C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + 8)); C8 (Z_to_bv 64 (DST + 2 * seg)); C8 (Z_to_bv 64 (DST + seg));
              C8 c3; C8 c2; C8 c1]
             [C8 c4o; C4 b4o; CB 4 jp; C8 p4o; C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + l3));
              C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + 8))] ->
    1 <= l1 < 65536 -> 1 <= l2 < 65536 -> 1 <= l3 < 65536 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    HDI l1 pt1 b1 -> HDI l2 pt2 b2 -> HDI l3 pt3 b3 -> HDI (n - (6 + l1 + l2 + l3)) pt4 b4 ->
    8 <= dcap - 3 * seg -> 0 <= q -> DST + 3 * seg + q < DST + dcap - 3 ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 b4) x6 x7 c4 x9 (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + pt4)) x11 x12 x13
               x14 x15 x16 x17 x18 (Z_to_bv 64 b3) (Z_to_bv 64 2147450880) (Z_to_bv 64 b2) (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SS + 6 + l1 + l2 + pt3)) (Z_to_bv 64 (SS + 6 + l1 + pt2))
               (Z_to_bv 64 (SS + 6 + pt1)) (Z_to_bv 64 b1) (Z_to_bv 64 q) x29 (Z_to_bv 64 (64 - tl)) x31)
          FR (Z_to_bv 64 0x90cc0) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition w4s2_goal : Prop :=
    forall (l1 l2 l3 q pt1 pt2 pt3 pt4 b1 b2 b3 b4 : Z) (c1 c2 c3 c4 : word)
           (w0 w8 w16 w40 w48 w56 w64 w72 w80 w88 w120 w128 w144 w152 w160 w168 : word) (jp : list byte) (mm : amem)
           (x5 x6 x11 x12 x13 x17 x28 x29 x30 x31 : word),
    W4SF' mm [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 dcap); C8 w40; C8 w48; C8 w56; C8 w64;
              C8 w72; C8 w80; C8 w88; C8 (Z_to_bv 64 seg); C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (SS + 6 + l1 + l2));
              C8 w120; C8 w128]
             [C8 w144; C8 w152; C8 w160; C8 w168; C8 (Z_to_bv 64 (SS + 14)); C8 (Z_to_bv 64 (SS + 6 + l1 + 8));
              C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + 8)); C8 (Z_to_bv 64 (DST + 2 * seg)); C8 (Z_to_bv 64 (DST + seg));
              C8 c3; C8 c2; C8 c1]
             [C8 c4; C4 (Z_to_bv 64 b4); CB 4 jp; C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + pt4));
              C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + l3)); C8 (Z_to_bv 64 (SS + 6 + l1 + l2 + l3 + 8))] ->
    1 <= l1 < 65536 -> 1 <= l2 < 65536 -> 1 <= l3 < 65536 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    W4STRM l1 pt1 b1 -> W4STRM l2 pt2 b2 -> W4STRM l3 pt3 b3 -> W4STRM (n - (6 + l1 + l2 + l3)) pt4 b4 ->
    0 <= q -> 3 * seg + q <= dcap ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (DST + dcap + -3)) (Z_to_bv 64 SPF) gp tp x5 x6 (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (SS + 6 + l1 + l2))
               (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + seg)) x11 x12 x13 (Z_to_bv 64 (DST + q))
               (Z_to_bv 64 (DST + seg + q)) (Z_to_bv 64 (DST + 3 * seg + q)) x17 (Z_to_bv 64 (SS + 6 + l1)) (Z_to_bv 64 b3)
               (Z_to_bv 64 (SS + 6)) (Z_to_bv 64 b2) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + 3 * seg))
               (Z_to_bv 64 (SS + 6 + l1 + l2 + pt3)) (Z_to_bv 64 (SS + 6 + l1 + pt2)) (Z_to_bv 64 (SS + 6 + pt1))
               (Z_to_bv 64 b1) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x91870) fc None mm (seg_rom asegs)).
End W4S12I.
End CANSEC1.
