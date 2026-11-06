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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChAdd FxChNull FxChEnt FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDir FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC.FxChDirDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDir OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
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

Module AsanCoNFDefs.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChAdd FxChNull FxChEnt FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDir FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC.FxChDirDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDir OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTblU.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMchr FxMNode AsanQSites FxSNodes AsanSNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanPNodes FxSFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanSFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanSFam3 FxDirConv AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanUsageT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblU OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3.AsanCpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3 OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT.AsanUsage.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition NNF : positive := Eval vm_compute in s_next S1.
Definition LPNF : lin := lvar NNF.
Definition FARGC2N : fact := FRange (lvar 5) 2 2.
Definition FV8N : fact := FRange PV 140735332483072 140737488355326.
Definition FV8SPN : fact := FRange (lsub PV (sm_sp M1)) 0 4194304.
Definition FLPN : fact := FRange LPNF 0 131071.
Definition FENDN0 : fact := FRange (ladd PV LPNF) 0x7fff7f800000 (0x800000000000 - 17).
Definition FENDN2 : fact := FRange (lsub (ladd PV LPNF) (sm_sp M1)) 0 4194304.
Definition FRZN : fact := FRange (lsub (laddc RANDP16 (-16)) (ladd PV LPNF)) 1 4194304.
Definition FPV0N : fact := FRange (lsub PV P0) 1 4194304.
Definition FSNF : list fact := [FARGC2N; FV8N; FV8SPN; FLPN; FENDN0; FENDN2; FRZN; FPV0N].
Definition SNF : sst := add_facts (bump (drop_post S1 (drop_f DROPB)) (Pos.succ NNF)) FSNF.
(* [comment removed for export] *)
Definition ANF : sfam := ([(PV, LPNF, 0%nat)], []).
Definition CO_PRE_N : list Z := [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32].
Definition SH_NF : shp := ShEmit [PD 2 (SArgs CO_PRE_N 0 LPNF [10]) (lconst 0)] 2.
Definition SH_NF2 : shp := ShEmit [PD 2 (SArgs CO_PRE_N 0 LPNF []) (lconst 0); PD 2 (SLit [10]) (lconst 0)] 2.

(* [comment removed for export] *)
Definition NF1 : MCU := MSegK 20 P_OPEN (KCons 0xd3954 56 MEnd KNil).
(* [comment removed for export] *)
Definition KSTN (n : nat) (ends : MKU) : MCU := Nat.iter n (fun k =>
      MSegK 20 (PRun F30000 STOPS_U []) (KCons 0x52e0c 0 (NODEU (inr (PQC 0)) k) (KCons 0x5179c 0 (NODEU (inr (PQC 1)) k) (KCons 0x502ec 0 (NODEU (inr (PQC 2)) k)
                   (KCons 0x6142c 0 (NODEU (inr (PQC 3)) k) (KCons 0x61474 0 (NODEU (inr (PQC 4)) k) (KCons 0xd2bfc 0 (NODEU (inr (PMC 0)) k)
                   (KCons 0x73594 0 (NODEU (inl (HSL3 0)) k) (KCons 0xd2b88 0 (NODEU (inl (HMCH3 0)) k) (KCons 0xcb964 0 (NODEU (inl (HNUL3 0 0)) k)
                   (KCons 0x639e0 0 (NODEU (inr PRP) k) (KCons 0xd2c84 0 (NODEU (inl (HCP3 0 64)) k) ends)))))))))))) MEnd.
Definition KTOWVN (k : MCU) : MCU := MJoin (KSTN F24 (KCons 0xca390 66 MEnd KNil)) 0xca390 k.
Definition KNA : MCU := KTOWVN (KW1 (WBuf B0R BFull 1) WEmpty UAFTER).
Definition KNB : MCU := KTOWVN (KW2 (WBuf B0R BPreArg 1) (WLit 0x1eb1c) UKB2).
Definition KNC : MCU := KTOWVN (KW2 (WBuf B0R BPre 0) (WArg 0) (KSTN F12 (KCons 0xca390 66 UKWL KNil))).
Definition NF2_AB : MCU := MSplit LPNF 62 KNA KNB.
End AsanCoNFDefs.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxChFamI AsanUsageT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblU OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3.AsanCpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3 OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCoNFT.AsanCoNFDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep.FxKeep OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxChFamI OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition NNFT : positive := Eval vm_compute in s_next TMAIN.
Definition LPNFT : lin := lvar NNFT.
Definition FV8SPNT : fact := FRange (lsub PV (sm_sp MMAIN)) 0 4194304.
Definition FLPNT : fact := FRange LPNFT 0 131071.
Definition FENDN0T : fact := FRange (ladd PV LPNFT) 0x7fff7f800000 (0x800000000000 - 17).
Definition FENDN2T : fact := FRange (lsub (ladd PV LPNFT) (sm_sp MMAIN)) 0 4194304.
Definition FRZNT : fact := FRange (lsub (laddc RANDP16 (-16)) (ladd PV LPNFT)) 1 4194304.
Definition FSNFT : list fact := [FARGC2N; FV8N; FV8SPNT; FLPNT; FENDN0T; FENDN2T; FRZNT; FPV0N].
Definition SNFT : sst := add_facts (bump TMAIN (Pos.succ NNFT)) FSNFT.
(* [comment removed for export] *)
Definition ANFT : ast * sfam := (AMAIN, ([(PV, LPNFT, 0%nat)], [])).
Definition SH_NFT : shp := ShEmit [PD 2 (SArgs CO_PRE_N 0 LPNFT [10]) (lconst 0)] 2.
Definition SH_NF2T : shp := ShEmit [PD 2 (SArgs CO_PRE_N 0 LPNFT []) (lconst 0); PD 2 (SLit [10]) (lconst 0)] 2.

(* [comment removed for export] *)
Definition NF1T : MCUT := MSegK 20 P_OPEN (KCons 0xd3954 56 MEnd KNil).
Definition nf1_resT : option (list (sst * smodel * fstate * shp * (ast * sfam))) :=
  mcheck ASEGS LIM TBLR IMGR PV 0 0 true None apostUT anilUT aeqbUT awfUT acopyUT asubUT agokUT alins_nil aset_id amod_f [] [] NF1T SNFT MMAIN FSClosed SH_NFT ANFT.
Definition S_OPT : sst := Eval vm_compute in match nf1_resT with Some ((St, _, _, _, _) :: _) => St | _ => TMAIN end.

(* [comment removed for export] *)
Definition TNFT : sst := ret_gen S_OPT ERRLO ERRHI.
Definition KSTNT (n : nat) (ends : MKUT) : MCUT := Nat.iter n (fun k =>
      MSegK 20 (PRun F30000 STOPS_U []) (KCons 0x52e0c 0 (NODEUT (inr (PQC 0)) k) (KCons 0x5179c 0 (NODEUT (inr (PQC 1)) k) (KCons 0x502ec 0 (NODEUT (inr (PQC 2)) k)
                   (KCons 0x6142c 0 (NODEUT (inr (PQC 3)) k) (KCons 0x61474 0 (NODEUT (inr (PQC 4)) k) (KCons 0xd2bfc 0 (NODEUT (inr (PMC 0)) k)
                   (KCons 0x73594 0 (NODEUT (inl (HSL3 0)) k) (KCons 0xd2b88 0 (NODEUT (inl (HMCH3 0)) k) (KCons 0xcb964 0 (NODEUT (inl (HNUL3 0 0)) k)
                   (KCons 0x639e0 0 (NODEUT (inr PRP) k) (KCons 0xd2c84 0 (NODEUT (inl (HCP3 0 64)) k) ends)))))))))))) MEnd.
Definition KTOWVNT (k : MCUT) : MCUT := MJoin (KSTNT F24 (KCons 0xca390 66 MEnd KNil)) 0xca390 k.
Definition KNAT : MCUT := KTOWVNT (KW1T (WBuf B0R BFull 1) WEmpty UAFTERT).
Definition KNBT : MCUT := KTOWVNT (KW2T (WBuf B0R BPreArg 1) (WLit 0x1eb1c) UKB2T).
Definition KNCT : MCUT := KTOWVNT (KW2T (WBuf B0R BPre 0) (WArg 0) (KSTNT F12 (KCons 0xca390 66 UKWLT KNil))).
Definition NF2_ABT : MCUT := MSplit LPNFT 62 KNAT KNBT.
Definition TNF_ABT : sst := add_fact TNFT (FRange LPNFT 0 63).
Definition TNF_CT : sst := add_fact TNFT (FRange LPNFT 64 M64).
Definition nf2_res_abT : option (list (sst * smodel * fstate * shp * (ast * sfam))) :=
  mcheck ASEGS LIM TBLR IMGR PV 0 0 true None apostUT anilUT aeqbUT awfUT acopyUT asubUT agokUT alins_nil aset_id amod_f [] [] NF2_ABT TNF_ABT MMAIN FSClosed SH_NFT ANFT.
Definition nf2_res_cT : option (list (sst * smodel * fstate * shp * (ast * sfam))) :=
  mcheck ASEGS LIM TBLR IMGR PV 0 0 true None apostUT anilUT aeqbUT awfUT acopyUT asubUT agokUT alins_nil aset_id amod_f [] [] KNCT TNF_CT MMAIN FSClosed SH_NF2T ANFT.
