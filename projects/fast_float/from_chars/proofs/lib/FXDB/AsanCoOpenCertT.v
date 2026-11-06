(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxCertLib.

Module AsanCoOpenT.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChAdd FxChNull FxChEnt FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDir FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC.FxChDirDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDir OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanOpenFinF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanOpenFinF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTblU.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMchr FxMNode AsanQSites FxSNodes AsanSNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanPNodes FxSFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanSFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanSFam3 FxDirConv AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxChFamI AsanUsageT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblU OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSFam3.AsanCpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSFam3 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.FxKeep OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxChFamI OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition T0T : sst := ret_gen S_OPEN_T ERRLO ERRHI.
Definition LPATH : lin := hvar 17.
(* [comment removed for export] *)
Definition FV8C : fact := FRange PV 140735332483072 140737488355326.
Definition FV8SPC : fact := FRange (lsub PV (sm_sp MMAIN)) 0 4194304.
Definition FENDP0 : fact := FRange (ladd PV LPATH) 0x7fff7f800000 (0x800000000000 - 17).
Definition FENDP2 : fact := FRange (lsub (ladd PV LPATH) (sm_sp MMAIN)) 0 4194304.
Definition FRZP : fact := FRange (lsub (laddc RANDP16 (-16)) (ladd PV LPATH)) 1 4194304.
Definition FPV0 : fact := FRange (lsub PV P0) 1 4194304.
Definition FSC : list fact := [FV8C; FV8SPC; FENDP0; FENDP2; FRZP; FPV0].
Definition TCT : sst := add_facts T0T FSC.
Definition AC0T : ast * sfam := (AMAIN, ([(PV, LPATH, 1%nat)], [])).
(* [comment removed for export] *)
Definition SH_CANNOT2 : shp := ShEmit [PD 2 (SArgs CANNOT_PRE 1 LPATH []) (lconst 0); PD 2 (SLit [10]) (lconst 0)] 2.

(* [comment removed for export] *)
Definition KSTCT (n : nat) (ends : MKUT) : MCUT := Nat.iter n (fun k =>
      MSegK 20 (PRun F30000 STOPS_U []) (KCons 0x5329c 0 (NODEUT (inr (PQC 0)) k) (KCons 0x51c2c 0 (NODEUT (inr (PQC 1)) k) (KCons 0x5077c 0 (NODEUT (inr (PQC 2)) k)
                   (KCons 0x61420 0 (NODEUT (inr (PQC 3)) k) (KCons 0x61468 0 (NODEUT (inr (PQC 4)) k) (KCons 0xd4478 0 (NODEUT (inr (PMC 0)) k)
                   (KCons 0x73588 0 (NODEUT (inl (HSL3 0)) k) (KCons 0xd4404 0 (NODEUT (inl (HMCH3 0)) k) (KCons 0xcd1e0 0 (NODEUT (inl (HNUL3 0 0)) k)
                   (KCons 0x639d4 0 (NODEUT (inr PRP) k) (KCons 0xd4500 0 (NODEUT (inl (HCP3 0 64)) k) ends)))))))))))) MEnd.
Definition KTOWVCT (k : MCUT) : MCUT := MJoin (KSTCT F24 (KCons 0xcbc0c 66 MEnd KNil)) 0xcbc0c k.
Definition KCAT : MCUT := KTOWVCT (KW1T (WBuf B0R BFull 1) WEmpty UAFTERT).
Definition KCBT : MCUT := KTOWVCT (KW2T (WBuf B0R BPreArg 1) (WLit 0x1eb5b) UKB2T).
Definition KCCT : MCUT := KTOWVCT (KW2T (WBuf B0R BPre 0) (WArg 0) (KSTCT F12 (KCons 0xcbc0c 66 UKWLT KNil))).
Definition CCH_ABT : MCUT := MSplit LPATH 62 KCAT KCBT.
Definition TC_ABT : sst := add_fact TCT (FRange LPATH 0 63).
Definition TC_CT : sst := add_fact TCT (FRange LPATH 64 M64).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FLHI : Z := -1.

(* [comment removed for export] *)
Definition c_res_abT : option (list (sst * smodel * fstate * shp * (ast * sfam))) :=
  mcheck ASEGS LIM TBLR IMGR PV 0 FLHI false (Some H0) apostUT anilUT aeqbUT awfUT acopyUT asubUT agokUT alins_nil aset_id amod_f [] [] CCH_ABT TC_ABT MMAIN FSClosed SH_CANNOT AC0T.
Definition c_res_cT : option (list (sst * smodel * fstate * shp * (ast * sfam))) :=
  mcheck ASEGS LIM TBLR IMGR PV 0 FLHI false (Some H0) apostUT anilUT aeqbUT awfUT acopyUT asubUT agokUT alins_nil aset_id amod_f [] [] KCCT TC_CT MMAIN FSClosed SH_CANNOT2 AC0T.
(* [comment removed for export] *)
End AsanCoOpenT.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxCertLib OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCoOpenCertT.AsanCoOpenT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma c_res_ab_nilT : c_res_abT = Some []. Proof. apply res_nil_eq. vm_cast_no_check (eq_refl true). Qed.
Lemma c_res_c_nilT : c_res_cT = Some []. Proof. apply res_nil_eq. vm_cast_no_check (eq_refl true). Qed.
(* [comment removed for export] *)
