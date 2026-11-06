(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.FxChMap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.

Module AsanPhases2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.AsanMainG1F OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.AsanPhases OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcFam2.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition GCK : positive := H0.
Definition GC (k : MCF) : MCF := MGc GCK [] k.
(* [comment removed for export] *)
Definition KFULLJ (j : nat) : MCF := GC (MJoin (K2AJ (clo j) (K2BP (LOOPP KTP) KTP)) 0x614b0 (KBACKJG MEnd)).
Definition BODYF (j : nat) : MCF :=
  MSegK 20 P_TOR (KCons 0xd3954 63 (MReadB 0x607400 0x10 MEnd (KFULLJ j)) KNil).
(* [comment removed for export] *)
Definition TAILA (j : nat) : MCF := GC (MSplitR 10 15 (KMCJAG j KGREX) (KMCJAG j KGREX)).
(* [comment removed for export] *)
Definition LOOPJ2 (j : nat) : MCF :=
  if Nat.eqb j 1 then GC (MSegK 20 P_TOR (KCons 0xd3954 63 (MReadB 0x607400 0x10 (TAILA 1) (KFULLJ 1)) KNil))
  else GC (MLoopW0 12 (BODYF j) (KCons 0x8fb5c 0 KGREX (KCons 0xd3958 63 (TAILA j) KNil))).
Fixpoint KPHK2 (kh kp : nat -> MCF) (n : nat) (j : nat) : MCF :=
  match n with
  | O => MEnd
  | Datatypes.S n' =>
      MJoin (MJoin (LOOPJ2 j) 0x8fb5c (GC (KGROWJ j (KPHK2 kh kp n' (Datatypes.S j))))) 0xd3954 (GC (KCLOSEBK kh kp))
  end.

(* [comment removed for export] *)
Fixpoint jplanGS (k : nat) : plan := match k with
  | O => PRun F30000 [0x639e0; 0x73c44; 0xd3954; 0x615c8; 0x3febc; 0x82914; 0x81f88; 0xd3088] []
  | Datatypes.S k' => let p := jplanGS k' in PJoin F30000 [0x639e0; 0x73c44; 0xd3954; 0x615c8; 0x3febc; 0x82914; 0x81f88; 0x73458; 0x7348c; 0xd3088] 0x632dc p
       [(0x73458, PLoopW 200 [0x73464] [(0x73464, p)]); (0x7348c, PLoopW 200 [0x7349c] [(0x7349c, p)])] end.
Definition PLAN_MSW : plan := PRun F30000 [0xd317c] [(0xd3160, PLoopW 200 [0xd317c] [(0xd317c, PFin)])].
Definition KMS (nxt : MCF) : MCF :=
  MSplitR 11 0 (MCall (inl (A1 NMset)) nxt)
    (MSplitR 11 0xbe (MSegK 20 PLAN_MSW (KCons 0xd317c 0 nxt KNil)) (MCall (inl (A1 (NMsetK [512]))) nxt)).
Fixpoint MSG (n : nat) (ks : mks) : MCF :=
  match n with
  | O => MSegK 40 (jplanG 6) ks
  | Datatypes.S n' => MSegK 40 (jplanGS 6) (KCons 0xd3088 0 (KMS (MSG n' ks)) ks)
  end.
Definition KGCPYJ2 (j : nat) (k : MCF) : MCF :=
  MJoin (MSG 3 (KCons 0x639e0 0 MEnd (KCons 0x3febc 0 MVoid KNil))) 0x639e0 (MJoin (MJoin (RPS1J j) 0xd2db0 (K2BP (LOOPP KTP) KTP)) 0x614b0 (KFREEJ k)).
Definition KPUTJ2 (j : nat) (k : MCF) : MCF := MSG 3 (KCons 0x81f88 0 (NPUT (KGCPYJ2 j k)) (KCons 0x3febc 0 MVoid KNil)).
Definition KGMALJ2 (j : nat) (k : MCF) : MCF :=
  MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (A1 (NNullA (mapj (Datatypes.S j)) GE true true false)))
     (MSep (TSepW 0 (13 + j)) (seps 1 (Datatypes.S j) (MSep (TSepR 0 0x10000 0x63a000)
       (if Nat.leb 2 j then MSG 3 (KCons 0x73c44 222 (shres j (KPUTJ2 j k)) (KCons 0x3febc 0 MVoid KNil)) else KPUTJ2 j k))))) KNil).
Definition KGROWJ2 (j : nat) (k : MCF) : MCF := MSegK 20 P_TO_UNWJ (KCons 0x82914 0 (NUNW (KGMALJ2 j k)) (KCons 0x8fd30 0 MVoid (KCons 0x8fd10 0 MEnd KNil))).
(* [comment removed for export] *)
Definition KGCPYP2 (k : MCF) : MCF :=
  MJoin (MSG 3 (KCons 0x639e0 0 MEnd (KCons 0x3febc 0 MVoid KNil))) 0x639e0 (MJoin (MJoin RPS1 0xd2db0 (K2BP (LOOPP KTP) KTP)) 0x614b0 (KFREE1P k)).
Definition KGMALP2 (k : MCF) : MCF :=
  MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (A1 (NNullA 0x22000 GE true true false)))
     (MSep (TSepW 0 13) (MSep (TSepW 0 1) (MSep (TSepR 0 0x10000 0x63a000)
       (MSG 3 (KCons 0x81f88 0 (NPUT (KGCPYP2 k)) (KCons 0x3febc 0 MVoid KNil))))))) KNil).
Definition KGROWP2 (k : MCF) : MCF := MSegK 20 P_TO_UNW (KCons 0x82914 0 (NUNW (KGMALP2 k)) (KCons 0x8fd30 0 MVoid KNil)).
Definition KM5P2 (k : MCF) : MCF :=
  MJoin (MSegK 20 P_TO_READ (KCons 0xd3954 63 (MReadHB 0x607400 0x10 6 (MConcR STAGE1E) STAGE1E) (KCons 0x3febc 0 MVoid KNil))) 0x8fb5c (KGROWP2 k).
Definition KM4P2 (k : MCF) : MCF := MSegK 20 P_TO_PUT (KCons 0x81f88 0 (NPUT (KM5P2 k)) (KCons 0x3febc 0 MVoid KNil)).
Definition KM3P2 (k : MCF) : MCF := MSegK 20 P_TO_MMAP (KCons 0x73c44 222 (MCall (inl (A1 (NFixA 0x20000 11))) (KM4P2 k)) (KCons 0x44360 0 MVoid KNil)).
Definition KM2P2 (k : MCF) : MCF := MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (A1 (NNullA 0x12000 GE true true false))) (MSep (TSepW 0 12) (MSep (TSepR 0 0x10000 0x63a000) (KM3P2 k)))) KNil).
Definition KOKOP2 (k : MCF) : MCF := MSegK 20 P_MAL_U (KCons 0x82914 0 (NUNW (KM2P2 k)) (KCons 0x8fd58 0 MVoid KNil)).
Definition KFILEP2 (k : MCF) : MCF := MSegK 20 P_OPEN (KCons 0xd3954 56 (MOpen MEnd (KOKOP2 k)) (KCons 0x8fc60 0 MVoid KNil)).
Definition MAINP2 (k : MCF) : MCF := TOPK (KFILEP2 k).
(* [comment removed for export] *)
Fixpoint KPHK3 (kh kp : nat -> MCF) (n : nat) (j : nat) : MCF :=
  match n with
  | O => MEnd
  | Datatypes.S n' =>
      MJoin (MJoin (LOOPJ2 j) 0x8fb5c (GC (KGROWJ2 j (KPHK3 kh kp n' (Datatypes.S j))))) 0xd3954 (GC (KCLOSEBK kh kp))
  end.
End AsanPhases2.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanCpSW.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.AsanMainG1F OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.AsanPhases OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhases3.AsanPhases2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanCpSW.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcFam2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition PLAN_MS0 : plan := PRun F300 [0xd317c] [].
Definition KMS2 (nxt : MCF) : MCF :=
  MSplitR 12 0 (MSegK 20 PLAN_MS0 (KCons 0xd317c 0 nxt KNil))
    (MSplitR 11 0 (MCall (inl (A1 NMset)) nxt)
       (MSplitR 11 0xbe (MSegK 20 PLAN_MSW (KCons 0xd317c 0 nxt KNil)) (MCall (inl (A1 (NMsetK []))) nxt))).
Fixpoint MSG2 (n : nat) (ks : mks) : MCF :=
  match n with
  | O => MSegK 40 (jplanG 6) ks
  | Datatypes.S n' => MSegK 40 (jplanGS 6) (KCons 0xd3088 0 (KMS2 (MSG2 n' ks)) ks)
  end.
(* [comment removed for export] *)
Definition NCONVA : MCF -> MCF := MCall (inl NConvA).
Definition NENQ : MCF -> MCF := MCall (inl NEnq).
Fixpoint jplanLQ (k : nat) : plan := match k with
  | O => PRun F30000 [0x73c44; 0xd3954; 0x82914; 0x81f88; 0x8fb98; 0xd3088; 0x43b04] []
  | Datatypes.S k' => let p := jplanLQ k' in PJoin F30000 [0x73c44; 0xd3954; 0x82914; 0x81f88; 0x8fb98; 0xd3088; 0x43b04; 0x73458; 0x7348c] 0x632dc p
       [(0x73458, PLoopW 200 [0x73464] [(0x73464, p)]); (0x7348c, PLoopW 200 [0x7349c] [(0x7349c, p)])] end.
(* [comment removed for export] *)
Definition KENQ (k : MCF) : MCF := MSegK 40 (jplanLQ 10) (KCons 0x43b04 0 (NENQ (MSegK 40 (jplanLQ 4) (KCons 0x8fb98 0 k KNil))) KNil).
Definition KFREEQ (k : MCF) : MCF :=
  MSegK 40 (jplanLQ 10) (KCons 0x82914 0 (NUNW (MSegK 40 (jplanLQ 10) (KCons 0x81f88 0 (NPUT
    (MSegK 40 (jplanLQ 10) (KCons 0xd3088 0 (KMS2 (KENQ k)) (KCons 0x43b04 0 (NENQ (MSegK 40 (jplanLQ 4) (KCons 0x8fb98 0 k KNil))) KNil)))) KNil))) KNil).
(* [comment removed for export] *)
Fixpoint jplanLS (k : nat) : plan := match k with
  | O => PRun F30000 [0x73c44; 0xd3954; 0x82914; 0x81f88; 0x8fb98; 0xd3088] []
  | Datatypes.S k' => let p := jplanLS k' in PJoin F30000 [0x73c44; 0xd3954; 0x82914; 0x81f88; 0x8fb98; 0xd3088; 0x73458; 0x7348c] 0x632dc p
       [(0x73458, PLoopW 200 [0x73464] [(0x73464, p)]); (0x7348c, PLoopW 200 [0x7349c] [(0x7349c, p)])] end.
Definition KFREEJ3 (k : MCF) : MCF :=
  MSegK 40 (jplanLS 10) (KCons 0x82914 0 (NUNW (MSegK 40 (jplanLS 10) (KCons 0x81f88 0 (NPUT
    (MSegK 40 (jplanLS 10) (KCons 0xd3088 0 (KMS2 (MSegK 40 (jplanLS 10) (KCons 0x8fb98 0 k KNil))) (KCons 0x8fb98 0 k KNil)))) KNil))) KNil).
(* [comment removed for export] *)
Definition KGCPYJ3 (j : nat) (k : MCF) : MCF :=
  MJoin (MSG2 5 (KCons 0x639e0 0 MEnd (KCons 0x3febc 0 MVoid KNil))) 0x639e0 (MJoin (MJoin (RPS1J j) 0xd2db0 (K2BP (LOOPP KTP) KTP)) 0x614b0 (KFREEQ (MBlobAdd 1 k))).   (* [comment removed for export] *)
Definition KPUTJ3 (j : nat) (k : MCF) : MCF := MSG2 3 (KCons 0x81f88 0 (NPUT (KGCPYJ3 j k)) (KCons 0x3febc 0 MVoid KNil)).
Definition KGMALJ3 (j : nat) (k : MCF) : MCF :=
  MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (A1 (NNullA (mapj (Datatypes.S j)) GE true true false)))
     (MSep (TSepW 0 14) (MSep (TSepW 0 1) (MSep (TSepR 0 0x10000 0x63a000)     (* [comment removed for export] *)
       (KPUTJ3 j k))))) KNil).   (* [comment removed for export] *)
Definition KGROWJ3 (j : nat) (k : MCF) : MCF := MSegK 20 P_TO_UNWJ (KCons 0x82914 0 (NUNW (KGMALJ3 j k)) (KCons 0x8fd30 0 MVoid (KCons 0x8fd10 0 MEnd KNil))).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NORM1 (k : MCF) : MCF := k.
Definition KGCPYP3 (k : MCF) : MCF :=
  MJoin (MSG2 5 (KCons 0x639e0 0 MEnd (KCons 0x3febc 0 MVoid KNil))) 0x639e0 (MJoin (MJoin RPS1 0xd2db0 (K2BP (LOOPP KTP) KTP)) 0x614b0 (KFREEQ (MBlobNil 2 (MBlobAdd 1 (NORM1 k))))).   (* [comment removed for export] *)
Definition KGMALP3 (k : MCF) : MCF :=
  MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (A1 (NNullA 0x22000 GE true true false)))
     (MSep (TSepW 0 13) (MSep (TSepW 0 1) (MSep (TSepR 0 0x10000 0x63a000)
       (MSG2 3 (KCons 0x81f88 0 (NPUT (KGCPYP3 k)) (KCons 0x3febc 0 MVoid KNil))))))) KNil).
Definition KGROWP3 (k : MCF) : MCF := MSegK 20 P_TO_UNW (KCons 0x82914 0 (NUNW (KGMALP3 k)) (KCons 0x8fd30 0 MVoid KNil)).
Definition KM5P3 (k : MCF) : MCF :=
  MJoin (MSegK 20 P_TO_READ (KCons 0xd3954 63 (MReadHB 0x607400 0x10 6 (MConcR STAGE1E) STAGE1E) (KCons 0x3febc 0 MVoid KNil))) 0x8fb5c (KGROWP3 k).
Definition KM4P3 (k : MCF) : MCF := MSegK 20 P_TO_PUT (KCons 0x81f88 0 (NPUT (KM5P3 k)) (KCons 0x3febc 0 MVoid KNil)).
Definition KM3P3 (k : MCF) : MCF := MSegK 20 P_TO_MMAP (KCons 0x73c44 222 (MCall (inl (A1 (NFixA 0x20000 11))) (NCONVA (KM4P3 k))) (KCons 0x44360 0 MVoid KNil)).
Definition KM2P3 (k : MCF) : MCF := MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (A1 (NNullA 0x12000 GE true true false))) (MSep (TSepW 0 12) (MSep (TSepR 0 0x10000 0x63a000) (KM3P3 k)))) KNil).
Definition KOKOP3 (k : MCF) : MCF := MSegK 20 P_MAL_U (KCons 0x82914 0 (NUNW (KM2P3 k)) (KCons 0x8fd58 0 MVoid KNil)).
Definition KFILEP3 (k : MCF) : MCF := MSegK 20 P_OPEN (KCons 0xd3954 56 (MOpen MEnd (KOKOP3 k)) (KCons 0x8fc60 0 MVoid KNil)).
(* [comment removed for export] *)
Definition MAINP3 (k : MCF) : MCF := TOPK (KFILEP3 k).

(* [comment removed for export] *)
Definition NPW : Type := (NPF + wnode)%type.
Definition MCW : Type := @mchain NPW.
Definition apostW : NPW -> sst -> smodel -> ast -> option (sst * smodel * ast) := apostP apostF (ppostW IMGMd).
Definition LW (c : MCF) : MCW := mmap (fun n : NPF => (inl n : NPW)) c.
Definition GCW (k : MCW) : MCW := MGc GCK [] k.
Definition PRPW (k : MCW) : MCW := MCall (inl (inr PRP)) k.
Definition WCPS (k : MCW) : MCW := MCall (inr WCps) k.

(* [comment removed for export] *)
Definition P_TW : plan := PRun F8000 [0x639e0; 0xd2c84; 0x615c8; 0x3febc; 0xd3954] [].
Definition GC1 (k : MCW) : MCW := MGc 1 [] k.      (* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint TWn (k : nat) : MCW :=
  match k with
  | O => MEnd
  | Datatypes.S k' =>
      MSegK 20 P_TW (KCons 0x639e0 0 (MAlt MVoid (PRPW (TWn k')))
                    (KCons 0xd2c84 0 (MAlt MVoid (WCPS MEnd))
                    (KCons 0x615c8 0 MVoid
                    (KCons 0x3febc 0 MVoid
                    (KCons 0xd3954 57 (MAlt MVoid (MRegEq (hvar 16) (MSel MEnd MVoid))) KNil)))))     (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Definition TWS : MCW := MSplitR 10 48 (TWn 6) (MSplitR 10 64 (TWn 6) (TWn 6)).
(* [comment removed for export] *)
Definition P_TWK : plan := PRun F8000 [0x8fb98; 0x8fb5c] [].
(* [comment removed for export] *)
Definition TAILW (j : nat) : MCW :=
  GCW (MJoin (MSplitG 0 (clo j) TWS TWS) 0x614b0
         (MSegK 20 P_TWK (KCons 0x8fb98 0 (LW KEOFJ) (KCons 0x8fb5c 0 (LW KGREX) KNil)))).

(* [comment removed for export] *)
Definition LOOPJW (j : nat) : MCW :=
  if Nat.eqb j 1 then GCW (MSegK 20 P_TOR (KCons 0xd3954 63 (MReadB 0x607400 0x10 (TAILW 1) (LW (KFULLJ 1))) KNil))
  else GCW (MLoopW 12 (LW (BODYF j)) (KCons 0x8fb5c 0 (LW KGREX) (KCons 0xd3958 63 (TAILW j) KNil))).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition capj (j : nat) : Z := 65536 * 2 ^ Z.of_nat j.
Definition PHW (kh kp : nat -> MCF) (j : nat) (knext : MCF) : MCW :=
  MJoin (MJoin (LOOPJW j) 0x8fb5c (LW (MSplit (hvar 16) (capj j - 1) MVoid (GC (KGROWJ3 j knext))))) 0xd3954 (LW (GC (KCLOSEBK kh kp))).
(* [comment removed for export] *)
Definition ZMAXA : Z := 8389632.     (* [comment removed for export] *)
Definition PHWC (j : nat) (knext : MCF) (kclose : MCW) : MCW :=
  MJoin (MJoin (LOOPJW j) 0x8fb5c (LW (MSplit (hvar 16) (capj j - 1) MVoid (GC (KGROWJ3 j knext))))) 0xd3954 kclose.
(* [comment removed for export] *)
Definition LOOPJWL (j : nat) (P : sst) (n0 : positive) (FP : fstate) (shP : shp) (meas : lin) : MCW :=
  GCW (MLoop P n0 FP shP meas (LW (BODYF j)) (KCons 0x8fb5c 0 (LW KGREX) (KCons 0xd3958 63 (TAILW j) KNil))).
Definition PHWCL (j : nat) (P : sst) (n0 : positive) (FP : fstate) (shP : shp) (meas : lin) (knext : MCF) (kclose : MCW) : MCW :=
  MJoin (MJoin (LOOPJWL j P n0 FP shP meas) 0x8fb5c (LW (MSplit (hvar 16) (capj j - 1) MVoid (GC (KGROWJ3 j knext))))) 0xd3954 kclose.
(* [comment removed for export] *)
Definition KCLOSEW (kh kp : nat -> MCF) : MCW := LW (GC (KCLOSEBK kh kp)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WOPS (l : list wop) (k : MCW) : MCW := MCall (inr (WNorm l)) k.     (* [comment removed for export] *)
Definition KCT2 (iA iB : nat) (nbA nbB : positive) (zA zB : list wop) : MCW :=
  MAllowW 0 ZMAXA (MSplit (hvar 1) 127 (WOPS zA (MCont iA nbA)) (WOPS zB (MCont iB nbB))).     (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KTKg (kh kp : nat -> MCF) (g : nat) : MCF :=
  MJoin (MSegK 20 P_FLAG (KCons 0x8fde0 0 MEnd KNil)) 0x8fde0 (MSegK 20 P_TR (KCons 0x8fe60 0 (kh g) (KCons 0x61d38 0 (kp g) KNil))).
Definition KSELKg (kh kp : nat -> MCF) : MCF := MSelB (MSelB (KTKg kh kp 4) (KTKg kh kp 3)) (MSelB (KTKg kh kp 2) (KTKg kh kp 1)).
Definition KBITSKg (kh kp : nat -> MCF) : MCF := MSplitB (hvar 2) 0 0 (MSplitB (hvar 2) 1 0 (KSELKg kh kp) (KSELKg kh kp)) (MSplitB (hvar 2) 1 1 (KSELKg kh kp) (KSELKg kh kp)).
Definition KBODYKg (kh kp : nat -> MCF) (cl : lin) : MCF := MSplit cl 0 (MSel (KTKg kh kp 0) MEnd) (MSel MEnd (KBITSKg kh kp)).
Definition KHDRCT (kh kp : nat -> MCF) (cl : lin) : MCF :=
  MSegK 20 P_HDR (KCons 0x8fc9c 0 MVoid (KCons 0x8fd98 0 (MSel MVoid (KBODYKg kh kp cl)) (KCons 0x8fc80 0 MVoid KNil))).
Definition KCLOSECT (kh kp : nat -> MCF) : MCW :=
  LW (GC (MClose (MSplit (hvar 1) 127 (MSel (KHDRCT kh kp CLA) MVoid) (MSel MVoid (KHDRCT kh kp CLB))))).

(* [comment removed for export] *)
Definition KFILEP4 (kerr k : MCF) : MCF := MSegK 20 P_OPEN (KCons 0xd3954 56 (MOpen kerr (KOKOP3 k)) (KCons 0x8fc60 0 MVoid KNil)).
Definition MAINP4 (kerr k : MCF) : MCF := TOPK (KFILEP4 kerr k).
