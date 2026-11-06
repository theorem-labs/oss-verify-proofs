(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.FxChMap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanTblML AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanEntry.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF AsanMainP AsanLit AsanCpSW AsanPhases3.

Module AsanPhasesR.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.FxChMap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhases3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanCpSW AsanPhases3 AsanErrT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP.AsanMainG1F OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP.AsanPhases OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhases3.AsanPhases2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanCpSW OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhases3 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanErrT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcFam2.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Definition STOPS_R : list Z := [0x61420; 0x61468; 0xcbc0c].
Definition PQW (j : nat) (k : MCW) : MCW := MCall (inl (inr (PQC j))) k.
Fixpoint KSEQ (ds : list bool) (kend : MCW) : MCW :=
  match ds with
  | [] => MSegK 20 (PRun F30000 [0xcbc0c] []) (KCons 0xcbc0c 66 kend KNil)
  | d :: ds' =>
      let r := KSEQ ds' kend in      (* [comment removed for export] *)
      MSegK 20 (PRun F30000 STOPS_R []) (KCons 0x61420 0 (if d then PQW 3 r else r) (KCons 0x61468 0 (if d then PQW 4 r else r) KNil))
  end.
Definition DS_R : list bool := [false; true; true; true; false; true].
(* [comment removed for export] *)
Definition B0L : lin := {| l_c := 18446744073709551024; l_t := [(1%positive, 32768); (2%positive, 4096); (3%positive, 64); (4%positive, 16)] |}.
Definition P_RETRYL : plan := PRun F3000 [0xcbc94; 0xcbc18] [].
Definition WB2L : MCW := MWritev2 B0L (MSegK 20 P_RETRYL (KCons 0xcbc94 66 MEnd (KCons 0xcbc18 0 MEnd KNil))).
Definition KWVL : MCW :=
  MJoin (MWritev2 B0L (MSegK 20 P_RETRYL (KCons 0xcbc94 66 (MLoopW 22 WB2L (KCons 0xcbc18 0 (MPop MEnd) KNil)) (KCons 0xcbc18 0 (MPop MEnd) KNil)))) 0xcbc18 (LW KF5).
Definition KREFUSE (ds : list bool) (kend : MCW) : MCW := MSegK 20 P_TO_UNWJ (KCons 0x82908 0 MVoid (KCons 0x8fd24 0 MVoid (KCons 0x8fd04 0 (KSEQ ds kend) KNil))).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHWRL (P : sst) (n0 : positive) (FP : fstate) (shP : shp) (meas : lin) (kclose : MCW) : MCW :=
  MJoin (MJoin (LOOPJWL 10 P n0 FP shP meas) 0x8fb50 (MSplit (hvar 16) (capj 10 - 1) MVoid (MSel MVoid (GCW (KREFUSE DS_R KWVL))))) 0xd51d0 kclose.
Definition PHWR (kclose : MCW) : MCW :=
  MJoin (MJoin (LOOPJW 10) 0x8fb50 (MSplit (hvar 16) (capj 10 - 1) MVoid (MSel MVoid (GCW (KREFUSE DS_R KWVL))))) 0xd51d0 kclose.
(* [comment removed for export] *)
End AsanPhasesR.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTblL AsanTblLd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTBNB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTB AsanPhCTBNB.

Module AsanPhK10.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.FxChMap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanTblML AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhases3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanLit AsanCpSW AsanPhases3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhL10NB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTblL AsanTblLd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTBNB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTB AsanPhCTBNB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTZB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTZB.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblML OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP.AsanMainG1F OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP.AsanPhases OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhases3.AsanPhases2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanLit OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanCpSW OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhases3 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhL10 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhL10NB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK10Thm.AsanPhasesR OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblL OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblLd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhT10 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTBNB.AsanPhCTANB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTBNB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTZB.AsanPhCTZA OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTZB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcSubst AcMALlib.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition CONTS10 : list (sst * smodel * fstate * shp * ast) := [CTA_C; CTB_C].
Definition CHAIN10 : MCW := PHWRL PHL10_S PHL10_N0 PHL10_FS PHL10_SH PHL10_MEAS (KCT2 0 1 CTA_NB CTB_NB (CTZA 10) (CTZB 10)).
Definition ph10_res : option (list (sst * smodel * fstate * shp * ast)) :=
  mcheck ASEGS LIM TBLLd IMGLd PV 65536 GHI false (Some H0) apostW anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a [] CONTS10 CHAIN10 PHT10_S PHT10_M PHT10_FS PHT10_SH PHT10_A.
Definition ph10_chk : bool := is_some ph10_res.
End AsanPhK10.


Module AsanPhK10Cert.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK10Thm.AsanPhK10.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma ph10_ok : ph10_res = Some nil.
Proof. vm_cast_no_check (eq_refl (Some (@nil (sst * smodel * fstate * shp * ast)))). Qed.
Lemma ph10_chk_true : ph10_chk = true.
Proof. unfold ph10_chk. rewrite ph10_ok. reflexivity. Qed.
End AsanPhK10Cert.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblML OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry.AsanSegs OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanLit OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanCpSW OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhases3 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK10Thm.AsanPhasesR OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblL OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblLd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhT10 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTBNB.AsanPhCTANB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTBNB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK10Thm.AsanPhK10 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK10Thm.AsanPhK10Cert.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam AcSubst AcMALlib AcFam2 AcFam2Ok.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Strategy opaque [TBLM TBLMd IMGMd TBLLd IMGLd mcheck].

Section Ph.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.
(* [comment removed for export] *)
Let Hanode2 : forall nk, anode_ok ASEGS cfg LIM (apost_alloc2 LIM) awf HA nk := alloc2_anode_ok cfg LIM A_wx A_segb Hoff A_respos A_reswf.
Variables (path0 : path) (data0 : list byte) (fs0 : Fs.Fs) (argv0 : list byte).
Hypothesis Hp1 : path_eqb path0 [] = false.
Hypothesis Hp2 : path_has_slash path0 = false.
Hypothesis Hp3 : path_is_dirref path0 = false.
Hypothesis Hp4 : (length path0 < path_max)%nat.
Hypothesis Hp5 : Forall (fun b => b <> Z_to_bv 8 0) path0.
Hypothesis HFL : 65536 <= Z.of_nat (length data0).

#[using="Hoff Hanode2"] Lemma anodeW_ok : forall nk, anode_ok ASEGS cfg LIM apostW awf HA nk.
Proof. LiaFast.lf_pins (fun (Hoff Hanode2 : LiaFast.U) => LiaFast.u0).
  exact (anodeP_ok ASEGS cfg LIM apostF awf HA (ppostW IMGMd) alloc_HA_agree
           (anodeP_ok ASEGS cfg LIM (apost_alloc2 LIM) awf HA (ppostA IMGMd QSITES_P MCSITES_P) alloc_HA_agree
              Hanode2
              (pnodeA_ok cfg LIM IMGMd QSITES_P MCSITES_P A_wx IMGMd_ok QSITES_P_ok MCSITES_P_ok))
           (pnodeW_ok cfg LIM IMGMd A_wx)).
Qed.
Definition cont_okA := cont_ok ASEGS cfg LIM PV path0 data0 fs0 argv0 false (Some H0) awf HA.

#[using="Hoff Hfs Hanode2 Hp1 Hp2 Hp3 Hp4 Hp5 HFL"] Theorem ph10_realizes : forall finals, ph10_res = Some finals -> cont_okA CTA_C -> cont_okA CTB_C ->
  forall model0 mem0 E ms model, DEN ASEGS LIM model0 mem0 E PHT10_S PHT10_M ms model ->
  INV PV path0 data0 fs0 false (Some H0) mem0 E PHT10_S PHT10_M PHT10_FS model0 -> HAX awf HA E PHT10_S PHT10_M PHT10_A mem0 -> shp_wf (s_next PHT10_S) PHT10_SH = true ->
  (forall S' M' FS' sh' (a' : ast) model0' mem0' E' ms' model', In (S', M', FS', sh', a') finals ->
     DEN ASEGS LIM model0' mem0' E' S' M' ms' model' -> INV PV path0 data0 fs0 false (Some H0) mem0' E' S' M' FS' model0' ->
     HAX awf HA E' S' M' a' mem0' -> shp_wf (s_next S') sh' = true -> agree (s_next PHT10_S) E E' ->
     realizes_cfg ASEGS cfg (mkCfg ms' model') (shp_den path0 fs0 argv0 E' sh')) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (shp_den path0 fs0 argv0 E PHT10_SH).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hanode2 Hp1 Hp2 Hp3 Hp4 Hp5 HFL : LiaFast.U) => LiaFast.u0).
  intros finals Hres HcA HcB model0 mem0 E ms model Hd Hi HX Hw Hk.
  change (mcheck ASEGS LIM TBLLd IMGLd PV 65536 GHI false (Some H0) apostW anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a [] CONTS10 CHAIN10 PHT10_S PHT10_M PHT10_FS PHT10_SH PHT10_A = Some finals) in Hres.
  assert (Hcp : forall E M (a : ast) m0, HA E M a m0 -> Forall (sbytes_ok (sarg path0 argv0) E m0) (acopy_alloc a)) by (intros; constructor).
  assert (HC : forall j c, nth_error CONTS10 j = Some c -> cont_okA c).
  { intros j c Hj. destruct j as [|[|j]]; [injection Hj as <-; exact HcA | injection Hj as <-; exact HcB | destruct j; discriminate Hj]. }
  exact (mchain_sound ASEGS cfg LIM TBLLd IMGLd A_wx A_segb Hoff Hfs A_respos A_reswf TBLLd_ok IMGLd_ok TBLLd_ecall PV path0 data0 fs0 65536 GHI argv0 false (Some H0)
            Hp1 Hp2 (fun _ => Hp3) Hp4 Hp5 (HFL_lb _ _ HFL) ltac:(unfold GHI; lia) Hseg_asan apostW anil aeqb awf HA acopy_alloc asubst ag_ok alins_a aset_a amod_a [] CONTS10 alloc_awf_mono alloc_aeqb_eq alloc_HA_nil alloc_HA_agree anodeW_ok Hcp HA_subst alloc_HA_mod (subs_nil_ok _) (subs_nil_use _) HC
            CHAIN10 PHT10_S PHT10_M PHT10_FS PHT10_SH PHT10_A finals Hres model0 mem0 E ms model Hd Hi HX Hw Hk).
Qed.

(* [comment removed for export] *)
#[using="Hoff Hfs Hanode2 Hp1 Hp2 Hp3 Hp4 Hp5 HFL"] Corollary ph10_cont : cont_okA CTA_C -> cont_okA CTB_C -> cont_okA PHT10_C.
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hanode2 Hp1 Hp2 Hp3 Hp4 Hp5 HFL : LiaFast.U) => LiaFast.u0).
  intros HcA HcB. unfold cont_okA, cont_ok, PHT10_C. cbn [fst snd]. intros model0 mem0 E ms model Hd Hi HX Hw.
  exact (ph10_realizes nil ph10_ok HcA HcB model0 mem0 E ms model Hd Hi HX Hw
           (fun S' M' FS' sh' a' model0' mem0' E' ms' model' Hin => False_ind _ Hin)).
Qed.
End Ph.
