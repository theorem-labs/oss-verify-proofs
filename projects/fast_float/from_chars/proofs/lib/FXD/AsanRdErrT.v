(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChAdd FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDir FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC.FxChDirDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDir OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC AsanTMain2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTblU.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMchr FxMNode AsanQSites FxSNodes AsanSNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanPNodes FxSFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanSFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanSFam3 FxDirConv AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxChFamI AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxDirConvOwn.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblU OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3.AsanCpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3 OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep.FxKeep OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxChFamI OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt.FxDropOwn OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxDirConvOwn.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition FV8SPT : fact := FRange (lsub PV (sm_sp MMAIN)) 0 4194304.
Definition FSRT : list fact := [FARGC; FV8; FV8SPT; FRND].
Definition SRT : sst := conv_post TMAIN drop_rand FSRT PV SZR [46; 0].
Definition MRT : smodel := frz_clear MMAIN.
Definition ART : ast * sfam := (AMAIN, ([], [])).

(* [comment removed for export] *)
Definition NODET (nk : pnode) (k : MCUT) : MCUT := MAlt (MCall (inr (inr nk)) k) k.
Definition KSTGT (n : nat) (stops : list Z) (ends : MKUT) : MCUT := Nat.iter n (fun k =>
      MSegK 20 (PRun F30000 stops []) (KCons 0x52e0c 0 (NODET (PQC 0) k) (KCons 0x5179c 0 (NODET (PQC 1) k) (KCons 0x502ec 0 (NODET (PQC 2) k)
                   (KCons 0x6142c 0 (NODET (PQC 3) k) (KCons 0x61474 0 (NODET (PQC 4) k) (KCons 0xd2bfc 0 (NODET (PMC 0) k) ends))))))) MEnd.
Definition KSTAT (n : nat) : MCUT := Nat.iter n (fun k =>
      MSegK 20 (PRun F30000 STOPS_A []) (KCons 0x52e0c 0 (NODET (PQC 0) k) (KCons 0x6142c 0 (NODET (PQC 3) k) (KCons 0x61474 0 (NODET (PQC 4) k)
                   (KCons 0xd2bfc 0 (MCall (inr (inr (PMC 0))) MEnd) (KCons 0x5176c 0 MEnd KNil)))))) MEnd.
Definition KAFTERT : MCUT := MSegK 40 P_EXIT (KCons 0xc4798 94 MExit KNil).
Definition WB2T : MCUT := MWritev2 B0R (MSegK 20 P_RETRY (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))).
Definition KWLT : MCUT := MJoin (MWritev2 B0R (MSegK 20 P_RETRY (KCons 0xca418 66 (MLoopW 22 WB2T (KCons 0xca39c 0 (MPop MEnd) KNil))
                                                               (KCons 0xca39c 0 (MPop MEnd) KNil)))) 0xca39c KAFTERT.
Definition KJOINT (kc : MCUT) : MCUT := MJoin (KSTAT F8) 0x5176c (MJoin (KSTGT F6 STOPS_B (KCons 0xcbeac 0 MEnd KNil)) 0xcbeac kc).
Definition KTAILT : MCUT := KJOINT (KSTGT F6 STOPS (KCons 0xca390 66 KWLT KNil)).
(* [comment removed for export] *)
Definition P_MAL_U : plan := PJoin F5000 [0x8fd58] 0x82914 PFin [].
Definition P_TO_MMAP1 : plan := PJoin F5000 [] 0x73c44 PFin [].
Definition P_TO_PUT : plan := PJoin F8000 [0x3febc] 0x81f88 PFin [].
Definition KM5T : MCUT := MSegK 20 P_TO_READ (KCons 0xd3954 63 (MReadDir KTAILT) (KCons 0x3febc 0 MVoid KNil)).
Definition KM4T : MCUT := MSegK 20 P_TO_PUT (KCons 0x81f88 0 (MCall (inl NPut) KM5T) (KCons 0x3febc 0 MVoid KNil)).
Definition KM3T : MCUT := MSegK 20 P_TO_MMAP (KCons 0x73c44 222 (MCall (inl (NFixA 0x20000 11)) KM4T) (KCons 0x44360 0 MVoid KNil)).
Definition KM2T : MCUT := MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (NNullA 0x12000 GE true true false)) (MSep (TSepW 0 12) KM3T)) KNil).
Definition KOKT : MCUT := MSegK 20 P_MAL_U (KCons 0x82914 0 (MCall (inl NUnw) KM2T) (KCons 0x8fd58 0 MVoid KNil)).
Definition RDCHT : MCUT := MSegK 20 P_OPEN (KCons 0xd3954 56 (MOpenDir KTAILT KOKT) (KCons 0x8fc60 0 MVoid KNil)).

(* [comment removed for export] *)
Definition rd_resT : option (list (sst * smodel * fstate * shp * (ast * sfam))) :=
  mcheck ASEGS LIM TBLR IMGR PV 0 0 true None apostUT anilUT aeqbUT awfUT acopyUT asubUT agokUT alins_nil aset_id amod_f [] [] RDCHT SRT MRT FSClosed SHD ART.
