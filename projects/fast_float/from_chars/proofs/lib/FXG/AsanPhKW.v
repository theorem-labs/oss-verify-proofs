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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanTblML AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhases3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanLit AsanCpSW AsanPhases3.

Module AsanPhases0.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhases3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanCpSW AsanPhases3 AsanErrT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.AsanMainG1F OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.AsanPhases OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhases3.AsanPhases2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanCpSW OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhases3 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanErrT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcFam2.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition KTOR2W0 : MCF := MSegK 20 P_TOR2 (KCons 0xd3954 63 (MReadB 0x607400 0x10 KTOCLW MVoid) (KCons 0x639e0 0 MEnd KNil)).
(* [comment removed for export] *)
Definition P2AQ : plan := PRun F3000 [0xd2db0; 0x614b0; 0x639e0; 0x61474; 0x61814; 0x61714] [].
Definition P2AV : plan := PRun F3000 [0xd2db0; 0x614b0; 0x639e0; 0x61814; 0x61714] [].
Definition KV (r : @mks NPF) : @mks NPF := KCons 0x61814 0 MVoid (KCons 0x61714 0 MVoid r).
Definition CLOW : Z := 0x7fff7000 - 0x12000.
Definition SEGQ : MCF := MSegK 20 P2AV (KCons 0xd2db0 0 (MAlt MVoid MEnd) (KCons 0x614b0 0 (MAlt MVoid MEnd) (KV KNil))).
Definition SEG3W0 : MCF := MSegK 20 P2AV (KCons 0xd2db0 0 (MAlt MVoid MEnd) (KCons 0x614b0 0 (MAlt MVoid MEnd) (KV KNil))).
Definition RP3W0 : MCF := MSplitG 0 CLOW (MCall (inr PRP) SEG3W0) (MCall (inr PRP) SEG3W0).
Definition SEG2W0 : MCF := MSegK 20 P2AV (KCons 0xd2db0 0 (MAlt MVoid MEnd) (KCons 0x639e0 0 RP3W0 (KCons 0x614b0 0 (MAlt MVoid MEnd) (KV KNil)))).
Definition RP2W0 : MCF := MSplitG 0 CLOW (MCall (inr PRP) SEG2W0) (MCall (inr PRP) SEG2W0).
Definition SEG1W0 : MCF := MSegK 20 P2AV (KCons 0xd2db0 0 (MAlt MVoid MEnd) (KCons 0x639e0 0 RP2W0 (KCons 0x614b0 0 (MAlt MVoid MEnd) (KV KNil)))).
Definition RP1W0 : MCF := MSplitG 0 CLOW (MCall (inr PRP) SEG1W0) (MCall (inr PRP) SEG1W0).
Definition K2AW0 (k : MCF) : MCF :=
  MJoin (MSegK 20 P2AQ (KCons 0xd2db0 0 (MAlt MVoid MEnd) (KCons 0x639e0 0 RP1W0 (KCons 0x614b0 0 (MAlt MVoid MEnd) (KCons 0x61474 0 (MCall (inr (PQR 4)) SEGQ) (KV KNil)))))) 0xd2db0 k.
Definition KRDW0 : MCF := MJoin (K2AW0 (K2BP (LOOPP KTPS) KTPS)) 0x614b0 KTOR2W0.
(* [comment removed for export] *)
Definition KRDJ0 (kclose : MCF) : MCF := MJoin (MSplit (hvar 16) 15 KRDW0 KRDW0) 0xd3954 kclose.
(* [comment removed for export] *)
Definition KM5W0 (krd : MCF) : MCF := MSG2 4 (KCons 0xd3954 63 (MReadHB 0x607400 0x10 6 krd MVoid) (KCons 0x3febc 0 MVoid KNil)).     (* [comment removed for export] *)
Definition KM4W0 (krd : MCF) : MCF := MSegK 20 P_TO_PUT (KCons 0x81f88 0 (NPUT (KM5W0 krd)) (KCons 0x3febc 0 MVoid KNil)).
(* [comment removed for export] *)
Definition KM3W0 (krd : MCF) : MCF :=
  MSegK 20 P_TO_MMAP (KCons 0x73c44 222 (MCall (inl (A1 (NFixA 0x20000 11))) (NCONVA (KM4W0 krd))) (KCons 0x44360 0 MVoid KNil)).
Definition KM2W0 (krd : MCF) : MCF :=
  MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (A1 (NNullA 0x12000 GE true true false))) (MSep (TSepW 0 12) (MSep (TSepR 0 0x10000 0x63a000) (KM3W0 krd)))) KNil).
Definition KOKOW0 (krd : MCF) : MCF := MSegK 20 P_MAL_U (KCons 0x82914 0 (NUNW (KM2W0 krd)) (KCons 0x8fd58 0 MVoid KNil)).
Definition KFILEW0 (kerr krd : MCF) : MCF := MSegK 20 P_OPEN (KCons 0xd3954 56 (MOpen kerr (KOKOW0 krd)) (KCons 0x8fc60 0 MVoid KNil)).
(* [comment removed for export] *)
Definition MAINW0 (kerr kclose : MCF) : MCF := TOPK (KFILEW0 kerr (KRDJ0 kclose)).     (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NORMW (k : MCF) : MCF := MRgFront 6 (MRgFront 3 (MRgFront 4 (MRgFront 4 (MRgFront 4 k)))).
Definition KCT0 (k : MCF) : MCF :=
  GC (MBlobNil 1 (MAllowFront 2 (MAllowW 0 ZMAXA (NORMW k)))).

(* [comment removed for export] *)
Definition KENQX : MCF := NENQ KF5.
Definition KF3X : MCF := MSegK 40 (jplanLQ 10) (KCons 0xd3088 0 (KMS2 (MSegK 40 (jplanLQ 10) (KCons 0x43b04 0 KENQX KNil))) (KCons 0x43b04 0 KENQX KNil)).
Definition KF2X : MCF := MSegK 40 (jplanLQ 10) (KCons 0x81f88 0 (NPUT KF3X) KNil).
Definition KAFTERX : MCF := MSegK 40 (jplanLQ 10) (KCons 0x82914 0 (NUNW KF2X) KNil).
Definition KWVX : MCF :=
  MJoin (MWritev 0x15f87 (MSegK 20 P_RETRYO (KCons 0xca418 66 (MLoopW 22 WBOP (KCons 0xca39c 0 (MPop MEnd) KNil)) (KCons 0xca39c 0 (MPop MEnd) KNil)))) 0xca39c KAFTERX.
Definition KHDROVR : MCF :=
  MSegK 20 P_HDR (KCons 0x8fc9c 0 (MSel (MSegK 20 P_WVO (KCons 0xca390 66 MEnd KNil)) MVoid) (KCons 0x8fd98 0 MVoid (KCons 0x8fc80 0 MVoid KNil))).
Definition KOVRA : MCF := MClose (MJoin (MSel KHDROVR MVoid) 0xca390 KWVX).
Definition KOVRB : MCF := MClose (MJoin (MSel MVoid KHDROVR) 0xca390 KWVX).
Definition KCLS0 (kovA kA kovB kB : MCF) : MCF := MSplit (hvar 1) 127 (MSplit LA T63 kovA kA) (MSplit LB T63 kovB kB).
(* [comment removed for export] *)
Definition MAINW2 (kerr kA kB : MCF) : MCF := MAINW0 kerr (KCT0 (KCLS0 KOVRA kA KOVRB kB)).


(* [comment removed for export] *)
Definition KRD0 : MCF := MSplit (hvar 16) 15 KRDW0 KRDW0.
Definition NORMWw (k : MCW) : MCW := MRgFront 6 (MRgFront 3 (MRgFront 4 (MRgFront 4 (MRgFront 4 k)))).
Definition KCT0W (k : MCW) : MCW := GCW (MBlobNil 1 (MAllowFront 2 (MAllowW 0 ZMAXA (NORMWw k)))).
Definition KCLS0W (kA kB : MCW) : MCW := MSplit (hvar 1) 127 (MSplit LA T63 (LW KOVRA) kA) (MSplit LB T63 (LW KOVRB) kB).
Definition MAINWW (kerr : MCF) (kA kB : MCW) : MCW := MJoin (LW (TOPK (KFILEW0 kerr KRD0))) 0xd3954 (KCT0W (KCLS0W kA kB)).
End AsanPhases0.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanErrT AsanPhCTA AsanPhCTANB AsanPhCTB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTANB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTZA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTZA.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblML OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.AsanMainG1F OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.AsanPhases OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhases3.AsanPhases2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanLit OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanCpSW OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhases3 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhKW.AsanPhases0 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanErrT OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTA OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTANB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTANB.AsanPhCTBNB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTZA OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTZA.AsanPhCTZB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcSubst AcMALlib.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition CONTSW : list (sst * smodel * fstate * shp * ast) := [CTA_C; CTB_C; TERR_C].
Definition CHAINW : MCW := MAINWW (KERR 2) (WOPS (CTZA 0) (MCont 0 CTA_NB)) (WOPS (CTZB 0) (MCont 1 CTB_NB)).     (* [comment removed for export] *)
Definition S1W2 : sst := S1c2 6 65535.
Definition phw_res : option (list (sst * smodel * fstate * shp * ast)) :=
  mcheck ASEGS LIM TBLM IMGMd PV 6 65535 false (Some H0) apostW anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a [] CONTSW CHAINW S1W2 M1c FSClosed SHWF A1c.
Definition phw_chk : bool := is_some phw_res.
