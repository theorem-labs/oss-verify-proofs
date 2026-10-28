(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_x4s RF_huf_x4s31 RF_huf_x4s31b RF_huf_x4s32 RF_huf_x4s32b RF_huf_x4s33 RF_huf_x4s33b RF_huf_x4s34 RF_huf_x4s34b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4s3 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s4SPL3C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4s34b9x34_entryC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4s33b9x33_entryC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4s32b9x32_entryC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4s31b9x31_entryK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegs".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section X4S3.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 2 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 2 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation XB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).
  Notation X4F' mm spl b1 b2 b3 b4 := (X4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b1 b2 b3 b4).

  (* [comment removed for export] *)
  Variables (L1 L2 L3 L4 SEG Q2 Q3 : Z).
  Notation O2 := (6 + L1). Notation O3 := (6 + L1 + L2). Notation O4 := (6 + L1 + L2 + L3).
  Hypothesis HL : 1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n.
  Hypothesis HQ : 0 < SEG <= Q2 /\ Q2 <= Q3 /\ Q3 <= dcap /\ 4 <= dcap.

  Ltac x4s3_sec := first [ eassumption | lia ].

  (* [comment removed for export] *)
  Lemma x4s3_all : forall q1 q2 q3 q4 pt1 pt2 pt3 pt4 c1 b1 c2 b2 c3 b3 c4 b4 v8 v16 v24 v32 v40 v48 v56 v128 mm j0 j96 j120
                          jp1 jp2 jp3 jp4 (xra t0 t1 x8 x9 a0 a1 a2 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word),
    X4F' mm (SPL3 v8 v16 v24 v32 v40 v48 v56 (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + Q2) dcap DST v128 j0 j96 j120)
            (BD4 c1 b1 (SS + 6 + pt1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + pt2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + pt3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + pt4) (SS + O4) jp4) ->
    0 <= q1 <= SEG -> 0 <= q2 <= Q2 -> 0 <= q3 <= Q3 -> 0 <= q4 <= dcap ->
    0 <= pt1 -> (pt1 = 0 \/ pt1 + 8 <= L1) -> 0 <= pt2 -> (pt2 = 0 \/ pt2 + 8 <= L2) ->
    0 <= pt3 -> (pt3 = 0 \/ pt3 + 8 <= L3) -> 0 <= pt4 -> (pt4 = 0 \/ pt4 + 8 <= L4) ->
    0 <= b1 < 2^31 -> 0 <= b2 < 2^31 -> 0 <= b3 < 2^31 -> 0 <= b4 < 2^31 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 (Z_to_bv 64 DST) x8 x9 a0 a1 a2 (Z_to_bv 64 (DST + SEG))
                           a4 a5 a6 a7 (Z_to_bv 64 (DST + q1)) (Z_to_bv 64 (tl + 256 * mtl)) x20 (Z_to_bv 64 (DST + q4))
                           (Z_to_bv 64 (DST + q3)) (Z_to_bv 64 (DST + q2)) (Z_to_bv 64 (DST + Q3)) (Z_to_bv 64 (DT + 4))
                           (Z_to_bv 64 SEG) (Z_to_bv 64 (DST + dcap)) t3 t4 t5 t6)
                       F (Z_to_bv 64 101644) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros XF Q1R Q2R Q3R Q4R P1 P1' P2 P2' P3 P3' P4 P4' B1 B2 B3 B4.
    eapply x31_entry with (L1 := L1) (SEG := SEG) (Q2 := Q2) (v80 := DST + dcap - 3) (v104 := dcap)
      (bd2 := BD4 c2 b2 (SS + O2 + pt2) (SS + O2) jp2) (bd3 := BD4 c3 b3 (SS + O3 + pt3) (SS + O3) jp3)
      (bd4 := BD4 c4 b4 (SS + O4 + pt4) (SS + O4) jp4)
      (y5 := Z_to_bv 64 (DST + q4)) (y6 := Z_to_bv 64 (DST + q3)) (y7 := Z_to_bv 64 (DST + q2)) (y8 := Z_to_bv 64 (DST + Q3)).
    all: try (exact XF).
    all: try x4s3_sec.
    intros mm1 c1' b1' p1' jp1' xra1 t01 t11 x81 x91 a01 a11 a21 a31 a41 a51 a61 a71 x181 x261 t31 t41 t51 t61 XF1.
    eapply x32_entry with (O2 := O2) (L2 := L2) (Q2 := Q2) (SEG := SEG) (v80 := DST + dcap - 3) (v104 := dcap)
      (bd1 := BD4 c1' b1' p1' (SS + 6) jp1') (bd3 := BD4 c3 b3 (SS + O3 + pt3) (SS + O3) jp3)
      (bd4 := BD4 c4 b4 (SS + O4 + pt4) (SS + O4) jp4)
      (y5 := Z_to_bv 64 (DST + q4)) (y6 := Z_to_bv 64 (DST + q3)) (y8 := Z_to_bv 64 (DST + Q3)).
    all: try (exact XF1).
    all: try x4s3_sec.
    intros mm2 c2' b2' p2' jp2' xra2 t02 t12 t22 x82 x92 a02 a12 a22 a32 a42 a52 a62 a72 x182 x232 x262 t32 t42 t52 t62 XF2.
    eapply x33_entry with (O3 := O3) (L3 := L3) (Q3 := Q3) (q4 := q4) (SEG := SEG) (Q2 := Q2) (v80 := DST + dcap - 3) (v104 := dcap)
      (bd1 := BD4 c1' b1' p1' (SS + 6) jp1') (bd2 := BD4 c2' b2' p2' (SS + O2) jp2')
      (bd4 := BD4 c4 b4 (SS + O4 + pt4) (SS + O4) jp4).
    all: try (exact XF2).
    all: try x4s3_sec.
    intros mm3 c3' b3' p3' jp3' xra3 t03 t13 t23 x83 x93 a03 a13 a23 a33 a43 a53 a63 a73 x183 x223 x233 x243 x263 t33 t43 t53 t63 XF3.
    eapply x34_entry with (O4 := O4) (L4 := L4) (SEG := SEG) (Q2 := Q2) (v104 := dcap)
      (bd1 := BD4 c1' b1' p1' (SS + 6) jp1') (bd2 := BD4 c2' b2' p2' (SS + O2) jp2') (bd3 := BD4 c3' b3' p3' (SS + O3) jp3').
    all: try (exact XF3).
    all: try x4s3_sec.
    intros mm4 c4' b4' p4' jp4' xra4 t04 t14 t24 x84 x94 a04 a14 a24 a34 a44 a54 a64 a74 x184 x214 x224 x234 x244 x264 t34 t44 t54 t64 XF4.
    eapply x4s_end.
    all: try (exact XF4).
    all: try x4s3_sec.
  Qed.

End X4S3.
End CANSEC1.
