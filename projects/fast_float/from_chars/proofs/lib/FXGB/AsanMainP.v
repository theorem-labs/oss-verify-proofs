(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF.

Module AsanMainG1F.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcFam2.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint jplanG (k : nat) : plan := match k with
  | O => PRun F30000 [0x639d4; 0x73c38; 0xd51d0; 0x615bc; 0x401d8; 0x82908; 0x81f7c] []
  | Datatypes.S k' => let p := jplanG k' in PJoin F30000 [0x639d4; 0x73c38; 0xd51d0; 0x615bc; 0x401d8; 0x82908; 0x81f7c; 0x7344c; 0x73480] 0x632d0 p
       [(0x7344c, PLoopW 200 [0x73458] [(0x73458, p)]); (0x73480, PLoopW 200 [0x73490] [(0x73490, p)])] end.
Fixpoint jplanR (k : nat) : plan := match k with
  | O => PRun F30000 [0x73c38; 0xd51d0; 0x82908; 0x81f7c] []
  | Datatypes.S k' => let p := jplanR k' in PJoin F30000 [0x73c38; 0xd51d0; 0x82908; 0x81f7c; 0x7344c; 0x73480; 0xd49dc] 0x632d0 p
       [(0x7344c, PLoopW 200 [0x73458] [(0x73458, p)]); (0x73480, PLoopW 200 [0x73490] [(0x73490, p)]);
        (0xd49dc, PLoopW 200 [0xd49f8] [(0xd49f8, p)])] end.
(* [comment removed for export] *)
Definition CLO2 : Z := 0x7fff7000 - 0x22000.
Definition SEGS2 : MCF := MSegK 20 P2AW (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x614a4 0 (MAlt MVoid MEnd) KNil)).
Definition RPS2 : MCF := MSplitG 0 CLO2 (MCall (inr PRP) SEGS2) (MCall (inr PRP) SEGS2).
Definition SEGS1 : MCF := MSegK 20 P2AW (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x639d4 0 RPS2 (KCons 0x614a4 0 (MAlt MVoid MEnd) KNil))).
Definition RPS1 : MCF := MSplitG 1 (0x7fff7000 - 0x12000) (MCall (inr PRP) SEGS1) (MCall (inr PRP) SEGS1).
(* [comment removed for export] *)
Definition P2L : plan := PRun F3000 [0xd462c; 0x614a4; 0x639d4; 0xd51d0] [].
Definition P_BACKG : plan := PJoin F8000 [] 0xd51d0 PFin [].
Definition KRD3 : MCF := MSegK 20 P_BACKG (KCons 0xd51d0 63 (MReadB 0x608cc0 0x10 (MSegK 20 P_TOCL (KCons 0xd51d0 57 MEnd KNil)) MEnd)
                                          (KCons 0xd51d0 57 MEnd KNil)).
Definition SEG3L : MCF := MSegK 20 P2L (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x614a4 0 (MAlt MVoid MEnd) (KCons 0xd51d0 57 MEnd KNil))).
Definition RP3L : MCF := MSplitG 0 CLO2 (MCall (inr PRP) SEG3L) (MCall (inr PRP) SEG3L).
Definition SEG2L : MCF := MSegK 20 P2L (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x639d4 0 RP3L (KCons 0x614a4 0 (MAlt MVoid MEnd) (KCons 0xd51d0 57 MEnd KNil)))).
Definition RP2L : MCF := MSplitG 0 CLO2 (MCall (inr PRP) SEG2L) (MCall (inr PRP) SEG2L).
Definition SEG1L : MCF := MSegK 20 P2L (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x639d4 0 RP2L (KCons 0x614a4 0 (MAlt MVoid MEnd) (KCons 0xd51d0 57 MEnd KNil)))).
Definition RP1L : MCF := MSplitG 0 CLO2 (MCall (inr PRP) SEG1L) (MCall (inr PRP) SEG1L).
Definition K2AL (k : MCF) : MCF := MJoin (MSegK 20 P2L (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x639d4 0 RP1L (KCons 0x614a4 0 (MAlt MVoid MEnd) (KCons 0xd51d0 57 MEnd KNil))))) 0xd462c k.
Definition KMC2 : MCF := MJoin (K2AL (K2BP (LOOPP KTP) KTP)) 0x614a4 KRD3.
(* [comment removed for export] *)
Definition KRD2 (k : MCF) : MCF := MJoin (MReadB 0x608cc0 0x10 (MSplit (hvar 16) 65551 KMC2 KMC2) MEnd) 0xd51d0 KCLOSEB.
Definition KFREE1 (k : MCF) : MCF :=
  MSegK 40 (jplanR 10) (KCons 0x82908 0 (NUNW (MSegK 40 (jplanR 10) (KCons 0x81f7c 0 (NPUT
     (MSegK 40 (jplanR 10) (KCons 0x73c38 222 (MCall (inl (A1 (NFixA 0x40000 13)))
        (MSegK 40 (jplanR 8) (KCons 0x73c38 222 (MCall (inl (A1 (NFixA 0x40000 13))) (MSegK 40 (jplanR 8) (KCons 0xd51d0 63 (KRD2 k) KNil))) KNil))) KNil))) KNil))) KNil).
Definition KGCPY (k : MCF) : MCF :=
  MJoin (MSegK 40 (jplanG 6) (KCons 0x639d4 0 MEnd (KCons 0x401d8 0 MVoid KNil))) 0x639d4 (MJoin (MJoin RPS1 0xd462c (K2BP (LOOPP KTP) KTP)) 0x614a4 (KFREE1 k)).
Definition KGMAL (k : MCF) : MCF :=
  MSegK 20 P_TO_MMAP1 (KCons 0x73c38 222 (MCall (inl (A1 (NNullA 0x22000 GE true true false)))
     (MSep (TSepW 0 13) (MSep (TSepW 0 1) (MSep (TSepR 0 0x10000 0x63c000)
       (MSegK 40 (jplanG 6) (KCons 0x81f7c 0 (NPUT (KGCPY k)) (KCons 0x401d8 0 MVoid KNil))))))) KNil).
Definition P_TO_UNW : plan := PJoin F8000 [0x8fd24] 0x82908 PFin [].
Definition KGROW (k : MCF) : MCF := MSegK 20 P_TO_UNW (KCons 0x82908 0 (NUNW (KGMAL k)) (KCons 0x8fd24 0 MVoid KNil)).
(* [comment removed for export] *)
Definition P_TOG0 : plan := PJoin F8000 [] 0x8fb50 PFin [].
Definition STAGE1F (k : MCF) : MCF := MJoin (K2AW (K2BP (LOOPP KTP) KTP)) 0x614a4 (MSegK 20 P_TOG0 (KCons 0x8fb50 0 (KGROW k) KNil)).
Definition KM5G (k : MCF) : MCF := MSegK 20 P_TO_READ (KCons 0xd51d0 63 (MReadHB 0x608cc0 0x10 6 (MConcR (STAGE1F k)) (STAGE1F k)) (KCons 0x401d8 0 MVoid KNil)).
Definition KM4G (k : MCF) : MCF := MSegK 20 P_TO_PUT (KCons 0x81f7c 0 (NPUT (KM5G k)) (KCons 0x401d8 0 MVoid KNil)).
Definition KM3G (k : MCF) : MCF := MSegK 20 P_TO_MMAP (KCons 0x73c38 222 (MCall (inl (A1 (NFixA 0x20000 11))) (KM4G k)) (KCons 0x4467c 0 MVoid KNil)).
Definition KM2G (k : MCF) : MCF := MSegK 20 P_TO_MMAP1 (KCons 0x73c38 222 (MCall (inl (A1 (NNullA 0x12000 GE true true false))) (MSep (TSepW 0 12) (MSep (TSepR 0 0x10000 0x63c000) (KM3G k)))) KNil).
Definition KOKOG (k : MCF) : MCF := MSegK 20 P_MAL_U (KCons 0x82908 0 (NUNW (KM2G k)) (KCons 0x8fd4c 0 MVoid KNil)).
Definition KFILEG (k : MCF) : MCF := MSegK 20 P_OPEN (KCons 0xd51d0 56 (MOpen MEnd (KOKOG k)) (KCons 0x8fc54 0 MVoid KNil)).
Definition MAING (k : MCF) : MCF := TOPK (KFILEG k).
Definition S1GF : sst := S1c 65536 131071.
(* [comment removed for export] *)
End AsanMainG1F.


Module AsanPhases.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP.AsanMainG1F.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcFam2.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition capj (j : nat) : Z := 2 ^ (16 + Z.of_nat j).
Definition mapj (j : nat) : Z := capj j + 8192.     (* [comment removed for export] *)
Definition clo (j : nat) : Z := 0x7fff7000 - mapj j.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KCLFL : MCF := MRegEq (hvar 16) (MSel MEnd MVoid).

(* [comment removed for export] *)
Fixpoint jplanL (k : nat) : plan := match k with
  | O => PRun F30000 [0x73c38; 0xd51d0; 0x82908; 0x81f7c; 0x8fb8c] []
  | Datatypes.S k' => let p := jplanL k' in PJoin F30000 [0x73c38; 0xd51d0; 0x82908; 0x81f7c; 0x8fb8c; 0x7344c; 0x73480; 0xd49dc] 0x632d0 p
       [(0x7344c, PLoopW 200 [0x73458] [(0x73458, p)]); (0x73480, PLoopW 200 [0x73490] [(0x73490, p)]);
        (0xd49dc, PLoopW 200 [0xd49f8] [(0xd49f8, p)])] end.
Definition P_TOR : plan := PJoin F8000 [] 0xd51d0 PFin [].

(* [comment removed for export] *)
Definition P_BACKJ : plan := PRun F3000 [0x8fb8c; 0x8fb50; 0xd51d0] [].
Definition KBACKJ : MCF := MSegK 20 P_BACKJ (KCons 0x8fb8c 0 MEnd (KCons 0x8fb50 0 MEnd (KCons 0xd51d0 57 KCLFL KNil))).
Definition SEG3J (c : Z) : MCF := MSegK 20 P2L (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x614a4 0 (MAlt MVoid MEnd) (KCons 0xd51d0 57 KCLFL KNil))).
Definition RP3J (c : Z) : MCF := MSplitG 0 c (MCall (inr PRP) (SEG3J c)) (MCall (inr PRP) (SEG3J c)).
Definition SEG2J (c : Z) : MCF := MSegK 20 P2L (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x639d4 0 (RP3J c) (KCons 0x614a4 0 (MAlt MVoid MEnd) (KCons 0xd51d0 57 KCLFL KNil)))).
Definition RP2J (c : Z) : MCF := MSplitG 0 c (MCall (inr PRP) (SEG2J c)) (MCall (inr PRP) (SEG2J c)).
Definition SEG1J (c : Z) : MCF := MSegK 20 P2L (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x639d4 0 (RP2J c) (KCons 0x614a4 0 (MAlt MVoid MEnd) (KCons 0xd51d0 57 KCLFL KNil)))).
Definition RP1J (c : Z) : MCF := MSplitG 0 c (MCall (inr PRP) (SEG1J c)) (MCall (inr PRP) (SEG1J c)).
Definition K2AJ (c : Z) (k : MCF) : MCF := MJoin (MSegK 20 P2L (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x639d4 0 (RP1J c) (KCons 0x614a4 0 (MAlt MVoid MEnd) (KCons 0xd51d0 57 KCLFL KNil))))) 0xd462c k.
Definition KMCJ (j : nat) : MCF := MJoin (K2AJ (clo j) (K2BP (LOOPP KTP) KTP)) 0x614a4 KBACKJ.
(* [comment removed for export] *)
Definition KEOFJ : MCF := MSegK 20 P_TOR (KCons 0xd51d0 63 (MReadB 0x608cc0 0x10 (MSegK 20 P_TOCL (KCons 0xd51d0 57 KCLFL KNil)) MVoid) KNil).
(* [comment removed for export] *)
Definition KBACKJG (kgr : MCF) : MCF := MSegK 20 P_BACKJ (KCons 0x8fb8c 0 MEnd (KCons 0x8fb50 0 kgr (KCons 0xd51d0 57 KCLFL KNil))).
Definition KBACKJAG (kgr : MCF) : MCF := MSegK 20 P_BACKJ (KCons 0x8fb8c 0 KEOFJ (KCons 0x8fb50 0 kgr (KCons 0xd51d0 57 KCLFL KNil))).
Definition KMCJG (j : nat) (kgr : MCF) : MCF := MJoin (K2AJ (clo j) (K2BP (LOOPP KTP) KTP)) 0x614a4 (KBACKJG kgr).
Definition KMCJAG (j : nat) (kgr : MCF) : MCF := MJoin (K2AJ (clo j) (K2BP (LOOPP KTP) KTP)) 0x614a4 (KBACKJAG kgr).
Definition BODYJG (j : nat) (kgr : MCF) : MCF :=
  MSegK 20 P_TOR (KCons 0xd51d0 63 (MReadB 0x608cc0 0x10 (MSplitR 10 15 (KMCJAG j kgr) (KMCJAG j kgr)) (MSplitR 10 15 (KMCJG j kgr) (KMCJG j kgr))) KNil).
Definition BODYJ (j : nat) : MCF := BODYJG j MEnd.
(* [comment removed for export] *)
Definition KGREX : MCF := MConcR (MConcF MEnd).
(* [comment removed for export] *)
Definition LOOPJ (j : nat) : MCF :=
  if Nat.eqb j 1 then BODYJG 1 KGREX else MLoopW 12 (BODYJ j) (KCons 0x8fb50 0 KGREX (KCons 0xd51d0 57 KCLFL KNil)).

(* [comment removed for export] *)
Fixpoint seps (i : nat) (n : nat) (k : MCF) : MCF := match n with O => k | Datatypes.S n' => MSep (TSepW 0 i) (seps (Datatypes.S i) n' k) end.
Definition shres (j : nat) (k : MCF) : MCF :=      (* [comment removed for export] *)
  MSplitG 0 (clo (Datatypes.S j)) (MCall (inl (A1 (NFixKA (capj (Datatypes.S j) / 8 - 4096) false (18 + j) GL))) k)
                                 (MCall (inl (A1 (NFixKA (capj (Datatypes.S j) / 8 - 4096) false (16 + j) GL))) k).
Definition SEGS2J (j : nat) : MCF := MSegK 20 P2AW (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x614a4 0 (MAlt MVoid MEnd) KNil)).
Definition RPS2J (j : nat) : MCF := MSplitG 0 (clo (Datatypes.S j)) (MCall (inr PRP) (SEGS2J j)) (MCall (inr PRP) (SEGS2J j)).
Definition SEGS1J (j : nat) : MCF := MSegK 20 P2AW (KCons 0xd462c 0 (MAlt MVoid MEnd) (KCons 0x639d4 0 (RPS2J j) (KCons 0x614a4 0 (MAlt MVoid MEnd) KNil))).
Definition RPS1J (j : nat) : MCF := MSplitG 1 (clo j) (MCall (inr PRP) (SEGS1J j)) (MCall (inr PRP) (SEGS1J j)).
Definition KFREEJ (k : MCF) : MCF :=
  MSegK 40 (jplanL 10) (KCons 0x82908 0 (NUNW (MSegK 40 (jplanL 10) (KCons 0x81f7c 0 (NPUT (MSegK 40 (jplanL 10) (KCons 0x8fb8c 0 k KNil))) KNil))) KNil).
Definition KGCPYJ (j : nat) (k : MCF) : MCF :=
  MJoin (MSegK 40 (jplanG 6) (KCons 0x639d4 0 MEnd (KCons 0x401d8 0 MVoid KNil))) 0x639d4 (MJoin (MJoin (RPS1J j) 0xd462c (K2BP (LOOPP KTP) KTP)) 0x614a4 (KFREEJ k)).
Definition KPUTJ (j : nat) (k : MCF) : MCF := MSegK 40 (jplanG 6) (KCons 0x81f7c 0 (NPUT (KGCPYJ j k)) (KCons 0x401d8 0 MVoid KNil)).
Definition KGMALJ (j : nat) (k : MCF) : MCF :=
  MSegK 20 P_TO_MMAP1 (KCons 0x73c38 222 (MCall (inl (A1 (NNullA (mapj (Datatypes.S j)) GE true true false)))
     (MSep (TSepW 0 (13 + j)) (seps 1 (Datatypes.S j) (MSep (TSepR 0 0x10000 0x63c000)
       (if Nat.leb 2 j then MSegK 40 (jplanG 6) (KCons 0x73c38 222 (shres j (KPUTJ j k)) (KCons 0x401d8 0 MVoid KNil)) else KPUTJ j k))))) KNil).
Definition P_TO_UNWJ : plan := PJoin F8000 [0x8fd24; 0x8fd04] 0x82908 PFin [].
Definition KGROWJ (j : nat) (k : MCF) : MCF := MSegK 20 P_TO_UNWJ (KCons 0x82908 0 (NUNW (KGMALJ j k)) (KCons 0x8fd24 0 MVoid (KCons 0x8fd04 0 MEnd KNil))).

(* [comment removed for export] *)
Fixpoint KPHK (kh kp : nat -> MCF) (n : nat) (j : nat) : MCF :=
  match n with
  | O => MEnd
  | Datatypes.S n' =>
      MJoin (MJoin (LOOPJ j) 0x8fb50 (KGROWJ j (KPHK kh kp n' (Datatypes.S j)))) 0xd51d0 (KCLOSEBK kh kp)
  end.
Definition KPH (n : nat) (j : nat) : MCF := KPHK KNONE KNONE n j.
(* [comment removed for export] *)
End AsanPhases.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP.AsanMainG1F OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP.AsanPhases.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcFam2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition KFREE1P (k : MCF) : MCF :=
  MSegK 40 (jplanL 10) (KCons 0x82908 0 (NUNW (MSegK 40 (jplanL 10) (KCons 0x81f7c 0 (NPUT
     (MSegK 40 (jplanL 10) (KCons 0x73c38 222 (MCall (inl (A1 (NFixA 0x40000 13)))
        (MSegK 40 (jplanL 8) (KCons 0x73c38 222 (MCall (inl (A1 (NFixA 0x40000 13))) (MSegK 40 (jplanL 8) (KCons 0x8fb8c 0 k KNil))) KNil))) KNil))) KNil))) KNil).
Definition KGCPYP (k : MCF) : MCF :=
  MJoin (MSegK 40 (jplanG 6) (KCons 0x639d4 0 MEnd (KCons 0x401d8 0 MVoid KNil))) 0x639d4 (MJoin (MJoin RPS1 0xd462c (K2BP (LOOPP KTP) KTP)) 0x614a4 (KFREE1P k)).
Definition KGMALP (k : MCF) : MCF :=
  MSegK 20 P_TO_MMAP1 (KCons 0x73c38 222 (MCall (inl (A1 (NNullA 0x22000 GE true true false)))
     (MSep (TSepW 0 13) (MSep (TSepW 0 1) (MSep (TSepR 0 0x10000 0x63c000)
       (MSegK 40 (jplanG 6) (KCons 0x81f7c 0 (NPUT (KGCPYP k)) (KCons 0x401d8 0 MVoid KNil))))))) KNil).
Definition KGROWP (k : MCF) : MCF := MSegK 20 P_TO_UNW (KCons 0x82908 0 (NUNW (KGMALP k)) (KCons 0x8fd24 0 MVoid KNil)).
(* [comment removed for export] *)
Definition STAGE1E : MCF := MJoin (K2AW (K2BP (LOOPP KTP) KTP)) 0x614a4 (MSegK 20 P_TOG0 (KCons 0x8fb50 0 (MConcR (MConcF MEnd)) KNil)).
Definition KM5P (k : MCF) : MCF :=
  MJoin (MSegK 20 P_TO_READ (KCons 0xd51d0 63 (MReadHB 0x608cc0 0x10 6 (MConcR STAGE1E) STAGE1E) (KCons 0x401d8 0 MVoid KNil))) 0x8fb50 (KGROWP k).
Definition KM4P (k : MCF) : MCF := MSegK 20 P_TO_PUT (KCons 0x81f7c 0 (NPUT (KM5P k)) (KCons 0x401d8 0 MVoid KNil)).
Definition KM3P (k : MCF) : MCF := MSegK 20 P_TO_MMAP (KCons 0x73c38 222 (MCall (inl (A1 (NFixA 0x20000 11))) (KM4P k)) (KCons 0x4467c 0 MVoid KNil)).
Definition KM2P (k : MCF) : MCF := MSegK 20 P_TO_MMAP1 (KCons 0x73c38 222 (MCall (inl (A1 (NNullA 0x12000 GE true true false))) (MSep (TSepW 0 12) (MSep (TSepR 0 0x10000 0x63c000) (KM3P k)))) KNil).
Definition KOKOP (k : MCF) : MCF := MSegK 20 P_MAL_U (KCons 0x82908 0 (NUNW (KM2P k)) (KCons 0x8fd4c 0 MVoid KNil)).
Definition KFILEP (k : MCF) : MCF := MSegK 20 P_OPEN (KCons 0xd51d0 56 (MOpen MEnd (KOKOP k)) (KCons 0x8fc54 0 MVoid KNil)).
Definition MAINP (k : MCF) : MCF := TOPK (KFILEP k).
Definition PHI : Z := 67108863.
(* [comment removed for export] *)
Definition GHI : Z := 4611686018427387903.
(* [comment removed for export] *)
Definition MSG_REFUSED : list Z :=
  [99;108;105;58;32;105;110;112;117;116;32;62;61;32;54;55;49;48;56;56;54;52;32;98;121;116;101;115;44;32;114;101;102;117;115;101;100;10].
Definition SH_REFUSED : shp := ShEmit [PD 2 (SLit MSG_REFUSED) (lconst 0)] 2.
Definition FILE_G : shp := ShIf (hvar 16) 0 PHI FILE_W SH_REFUSED.
Definition SHG : shp := SH_TOP FILE_G.
(* [comment removed for export] *)
Lemma flen_of_le : forall n, flen_of n <= Z.of_nat n. Proof. intros n. unfold flen_of. lia. Qed.
Lemma flen_of_range : forall n, 0 <= flen_of n <= GHI. Proof. intros n. unfold flen_of, FLT, GHI. lia. Qed.
Lemma flen_of_exact : forall n, flen_of n < GHI -> flen_of n = Z.of_nat n. Proof. intros n. unfold flen_of, FLT, GHI. lia. Qed.
Lemma flen_of_small : forall n, Z.of_nat n <= GHI -> flen_of n = Z.of_nat n. Proof. intros n. unfold flen_of, FLT, GHI. lia. Qed.
Lemma flen_of_big : forall n b, b <= GHI -> b <= Z.of_nat n -> b <= flen_of n. Proof. intros n b. unfold flen_of, FLT, GHI. lia. Qed.
(* [comment removed for export] *)
Definition MAINPK (kh kp : nat -> MCF) (n : nat) : MCF := MAINP (KPHK kh kp n 1).
Definition S1P : sst := S1c 65536 GHI.
(* [comment removed for export] *)
