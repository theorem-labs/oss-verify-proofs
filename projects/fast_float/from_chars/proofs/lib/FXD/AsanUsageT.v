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

Module AsanUsage.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTblU.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMchr FxMNode AsanQSites FxSNodes AsanSNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanPNodes FxSFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanSFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanSFam3 FxDirConv AsanRdErr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblU OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3.AsanCpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3 OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErr.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ISLX : Z := 0x73594.
Definition NSITES : list nsite := [NS_PCORE].
Definition apostU (nk : snode + pnode) (S : sst) (M : smodel) (a : sfam) : option (sst * smodel * sfam) :=
  apostP (hpost3 ISLX NSITES) (ppostA IMGR QSITES MCSITES) nk S M a.
Definition MCU : Type := @mchain (snode + pnode).
Definition MKU : Type := @mks (snode + pnode).

(* [comment removed for export] *)
Definition A0 : sfam := ([(P0, lvar 11, 0%nat)], []).

(* [comment removed for export] *)
Definition USG_PRE : list Z := [117; 115; 97; 103; 101; 58; 32].
Definition USG_SUF : list Z := [32; 73; 78; 80; 85; 84; 10].
Definition SHU : shp := ShEmit [PD 2 (SArgs USG_PRE 0 (lvar 11) USG_SUF) (lconst 0)] 2.
Definition SHU2 : shp := ShEmit [PD 2 (SArgs USG_PRE 0 (lvar 11) []) (lconst 0); PD 2 (SLit USG_SUF) (lconst 0)] 2.

(* [comment removed for export] *)
Definition RG_DUMMY : region := RG (lconst 0) (lconst 0) RW TEmpty.
Definition DROPB : list lin := Eval vm_compute in List.map (fun k => rg_base (List.nth k (s_rgs S1) RG_DUMMY)) [0;2;4;6;9;11;13;15;17;19;21;23;42;43]%nat.
(* [comment removed for export] *)
Definition FARGC_U : fact := FCond BC_NE (lvar 5) (lconst 2) true.
Definition FEND0 : fact := FRange (ladd P0 (lvar 11)) 0x7fff7f800000 (0x800000000000 - 17).
Definition FEND1 : fact := FRange (lsub P0 (sm_sp M1)) 0 4194304.
Definition FEND2 : fact := FRange (lsub (ladd P0 (lvar 11)) (sm_sp M1)) 0 4194304.
Definition FRZU : fact := FRange (lsub (laddc RANDP16 (-16)) (ladd P0 (lvar 11))) 1 4194304.
Definition FSU : list fact := [FARGC_U; FEND0; FEND1; FEND2; FRZU].
Definition SUC : sst := add_facts (drop_post S1 (drop_f DROPB)) FSU.

(* [comment removed for export] *)
Definition F12 : nat := 12.
Definition F24 : nat := 24.
(* [comment removed for export] *)
Definition STOPS_U : list Z := [0x52e0c; 0x5179c; 0x502ec; 0x6142c; 0x61474; 0xd2bfc; 0x73594; 0xd2b88; 0x639e0; 0xcb964; 0xd2c84; 0xca390; 0xca418].
Definition NODEU (nk : snode + pnode) (k : MCU) : MCU := MAlt (MCall nk k) k.
Definition KSTU (n : nat) (ends : MKU) : MCU := Nat.iter n (fun k =>
      MSegK 20 (PRun F30000 STOPS_U []) (KCons 0x52e0c 0 (NODEU (inr (PQC 0)) k) (KCons 0x5179c 0 (NODEU (inr (PQC 1)) k) (KCons 0x502ec 0 (NODEU (inr (PQC 2)) k)
                   (KCons 0x6142c 0 (NODEU (inr (PQC 3)) k) (KCons 0x61474 0 (NODEU (inr (PQC 4)) k) (KCons 0xd2bfc 0 (NODEU (inr (PMC 0)) k)
                   (KCons 0x73594 0 (NODEU (inl (HSL3 0)) k) (KCons 0xd2b88 0 (NODEU (inl (HMCH3 0)) k) (KCons 0xcb964 0 (NODEU (inl (HNUL3 0 0)) k)
                   (KCons 0x639e0 0 (NODEU (inr PRP) k) (KCons 0xd2c84 0 (NODEU (inl (HCP3 0 74)) k) ends)))))))))))) MEnd.
(* [comment removed for export] *)
Definition U_RETRY : plan := PRun F3000 [0xca418; 0xca39c] [].
Definition U_RETRY2 : plan := PRun F3000 [0xca418; 0xca39c; 0xca458] [].
Definition U_EXIT : plan := PRun F30000 [0xca390; 0xca418; 0xc4798; 0xd3954] [].
Definition UAFTER : MCU := MSegK 40 U_EXIT (KCons 0xc4798 94 MExit KNil).
(* [comment removed for export] *)
Definition KW1 (F0 F1 : wsrc) (k : MCU) : MCU :=
  let body := MWritevC F0 F1 (MSegK 20 U_RETRY (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))) in
  MJoin (MWritevC F0 F1 (MSegK 20 U_RETRY (KCons 0xca418 66 (MLoopW 22 body (KCons 0xca39c 0 (MPop MEnd) KNil)) (KCons 0xca39c 0 (MPop MEnd) KNil)))) 0xca39c k.
(* [comment removed for export] *)
Definition KW2 (F0 F1 : wsrc) (k : MCU) : MCU :=
  let body2 := MWritevC F1 WEmpty (MSegK 20 U_RETRY (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))) in
  let ph2 := MSegK 20 U_RETRY (KCons 0xca418 66 (MWritevC F1 WEmpty (MSegK 20 U_RETRY (KCons 0xca418 66 (MLoopW 15 body2 (KCons 0xca39c 0 (MPop MEnd) KNil)) (KCons 0xca39c 0 (MPop MEnd) KNil)))) KNil) in
  let body1 := MWritevC F0 F1 (MSegK 20 U_RETRY2 (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd (KCons 0xca458 0 MEnd KNil)))) in
  MJoin (MWritevC F0 F1 (MSegK 20 U_RETRY2 (KCons 0xca418 66 (MLoopW 15 body1 (KCons 0xca39c 0 (MPop MEnd) (KCons 0xca458 0 ph2 KNil)))
                                            (KCons 0xca39c 0 (MPop MEnd) (KCons 0xca458 0 ph2 KNil))))) 0xca39c k.
(* [comment removed for export] *)
Definition UWB2 : MCU := MWritev2 B0R (MSegK 20 U_RETRY (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))).
Definition UKWL : MCU := MJoin (MWritev2 B0R (MSegK 20 U_RETRY (KCons 0xca418 66 (MLoopW 22 UWB2 (KCons 0xca39c 0 (MPop MEnd) KNil))
                                                                 (KCons 0xca39c 0 (MPop MEnd) KNil)))) 0xca39c UAFTER.
(* [comment removed for export] *)
Definition UKB2 : MCU := MSegK 20 (PRun F30000 [0xca390; 0xca418] []) (KCons 0xca390 66 (MWritev0 (MSegK 20 U_RETRY (KCons 0xca39c 0 UAFTER KNil))) KNil).
(* [comment removed for export] *)
Definition KTOWV (k : MCU) : MCU := MJoin (KSTU F24 (KCons 0xca390 66 MEnd KNil)) 0xca390 k.
Definition KRA : MCU := KTOWV (KW1 (WBuf B0R BFull 1) WEmpty UAFTER).
Definition KRB : MCU := KTOWV (KW2 (WBuf B0R BPreArg 1) (WLit 0x15f7f) UKB2).
Definition KRC : MCU := KTOWV (KW2 (WBuf B0R BPre 0) (WArg 0) (KSTU F12 (KCons 0xca390 66 UKWL KNil))).
(* [comment removed for export] *)
Definition UCH_AB : MCU := MSegK 20 P_OPEN (KCons 0x8fc60 0 (MSplit (lvar 11) 66 KRA KRB) KNil).
Definition UCH_C : MCU := MSegK 20 P_OPEN (KCons 0x8fc60 0 KRC KNil).
Definition SUC_AB : sst := add_fact SUC (FRange (lvar 11) 0 73).
Definition SUC_C : sst := add_fact SUC (FRange (lvar 11) 74 M64).

(* [comment removed for export] *)
Definition u_res_ab : option (list (sst * smodel * fstate * shp * sfam)) :=
  mcheck ASEGS LIM TBLR IMGR PV 0 0 true None apostU anil3 aeqb3 awf3 acopy3 (fun _ a => a) (fun _ _ => false) alins_nil aset_id amod_t [] [] UCH_AB SUC_AB M1 FSClosed SHU A0.
Definition u_res_c : option (list (sst * smodel * fstate * shp * sfam)) :=
  mcheck ASEGS LIM TBLR IMGR PV 0 0 true None apostU anil3 aeqb3 awf3 acopy3 (fun _ a => a) (fun _ _ => false) alins_nil aset_id amod_t [] [] UCH_C SUC_C M1 FSClosed SHU2 A0.
End AsanUsage.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxChFamI.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblU OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3.AsanCpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3 OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep.FxKeep OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxChFamI.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition NUT : Type := anode + (snode + pnode).
Definition apostUT : NUT -> sst -> smodel -> ast * sfam -> option (sst * smodel * (ast * sfam)) := apostI (apost_alloc LIM) anil3 apostU.
Definition anilUT : ast * sfam -> bool := anilX anil anil3.
Definition aeqbUT : ast * sfam -> ast * sfam -> bool := aeqbX aeqb aeqb3.
Definition awfUT : positive -> ast * sfam -> bool := awfX awf awf3.
Definition acopyUT (a : ast * sfam) : list srec := acopy3 (snd a).
(* [comment removed for export] *)
Definition asubUT (_ : tree lin) (a : ast * sfam) : ast * sfam := a.
Definition agokUT (_ : smodel) (_ : ast * sfam) : bool := false.
Definition MCUT : Type := @mchain NUT.
Definition MKUT : Type := @mks NUT.
Definition A0T : ast * sfam := (AMAIN, A0).

(* [comment removed for export] *)
Definition SUT : sst := add_facts TMAIN FSU.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NODEUT (nk : snode + pnode) (k : MCUT) : MCUT := MAlt (MCall (inr nk) k) k.
Definition KSTUT (n : nat) (ends : MKUT) : MCUT := Nat.iter n (fun k =>
      MSegK 20 (PRun F30000 STOPS_U []) (KCons 0x52e0c 0 (NODEUT (inr (PQC 0)) k) (KCons 0x5179c 0 (NODEUT (inr (PQC 1)) k) (KCons 0x502ec 0 (NODEUT (inr (PQC 2)) k)
                   (KCons 0x6142c 0 (NODEUT (inr (PQC 3)) k) (KCons 0x61474 0 (NODEUT (inr (PQC 4)) k) (KCons 0xd2bfc 0 (NODEUT (inr (PMC 0)) k)
                   (KCons 0x73594 0 (NODEUT (inl (HSL3 0)) k) (KCons 0xd2b88 0 (NODEUT (inl (HMCH3 0)) k) (KCons 0xcb964 0 (NODEUT (inl (HNUL3 0 0)) k)
                   (KCons 0x639e0 0 (NODEUT (inr PRP) k) (KCons 0xd2c84 0 (NODEUT (inl (HCP3 0 74)) k) ends)))))))))))) MEnd.
(* [comment removed for export] *)
Definition UAFTERT : MCUT := MSegK 40 U_EXIT (KCons 0xc4798 94 MExit KNil).
(* [comment removed for export] *)
Definition KW1T (F0 F1 : wsrc) (k : MCUT) : MCUT :=
  let body := MWritevC F0 F1 (MSegK 20 U_RETRY (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))) in
  MJoin (MWritevC F0 F1 (MSegK 20 U_RETRY (KCons 0xca418 66 (MLoopW 22 body (KCons 0xca39c 0 (MPop MEnd) KNil)) (KCons 0xca39c 0 (MPop MEnd) KNil)))) 0xca39c k.
(* [comment removed for export] *)
Definition KW2T (F0 F1 : wsrc) (k : MCUT) : MCUT :=
  let body2 := MWritevC F1 WEmpty (MSegK 20 U_RETRY (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))) in
  let ph2 := MSegK 20 U_RETRY (KCons 0xca418 66 (MWritevC F1 WEmpty (MSegK 20 U_RETRY (KCons 0xca418 66 (MLoopW 15 body2 (KCons 0xca39c 0 (MPop MEnd) KNil)) (KCons 0xca39c 0 (MPop MEnd) KNil)))) KNil) in
  let body1 := MWritevC F0 F1 (MSegK 20 U_RETRY2 (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd (KCons 0xca458 0 MEnd KNil)))) in
  MJoin (MWritevC F0 F1 (MSegK 20 U_RETRY2 (KCons 0xca418 66 (MLoopW 15 body1 (KCons 0xca39c 0 (MPop MEnd) (KCons 0xca458 0 ph2 KNil)))
                                            (KCons 0xca39c 0 (MPop MEnd) (KCons 0xca458 0 ph2 KNil))))) 0xca39c k.
(* [comment removed for export] *)
Definition UWB2T : MCUT := MWritev2 B0R (MSegK 20 U_RETRY (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))).
Definition UKWLT : MCUT := MJoin (MWritev2 B0R (MSegK 20 U_RETRY (KCons 0xca418 66 (MLoopW 22 UWB2T (KCons 0xca39c 0 (MPop MEnd) KNil))
                                                                 (KCons 0xca39c 0 (MPop MEnd) KNil)))) 0xca39c UAFTERT.
(* [comment removed for export] *)
Definition UKB2T : MCUT := MSegK 20 (PRun F30000 [0xca390; 0xca418] []) (KCons 0xca390 66 (MWritev0 (MSegK 20 U_RETRY (KCons 0xca39c 0 UAFTERT KNil))) KNil).
(* [comment removed for export] *)
Definition KTOWVT (k : MCUT) : MCUT := MJoin (KSTUT F24 (KCons 0xca390 66 MEnd KNil)) 0xca390 k.
Definition KRAT : MCUT := KTOWVT (KW1T (WBuf B0R BFull 1) WEmpty UAFTERT).
Definition KRBT : MCUT := KTOWVT (KW2T (WBuf B0R BPreArg 1) (WLit 0x15f7f) UKB2T).
Definition KRCT : MCUT := KTOWVT (KW2T (WBuf B0R BPre 0) (WArg 0) (KSTUT F12 (KCons 0xca390 66 UKWLT KNil))).
(* [comment removed for export] *)
Definition UCH_ABT : MCUT := MSegK 20 P_OPEN (KCons 0x8fc60 0 (MSplit (lvar 11) 66 KRAT KRBT) KNil).
Definition UCH_CT : MCUT := MSegK 20 P_OPEN (KCons 0x8fc60 0 KRCT KNil).
Definition SUC_ABT : sst := add_fact SUT (FRange (lvar 11) 0 73).
Definition SUC_CT : sst := add_fact SUT (FRange (lvar 11) 74 M64).


(* [comment removed for export] *)
Definition ut_res_ab : option (list (sst * smodel * fstate * shp * (ast * sfam))) :=
  mcheck ASEGS LIM TBLR IMGR PV 0 0 true None apostUT anilUT aeqbUT awfUT acopyUT asubUT agokUT alins_nil aset_id amod_f [] [] UCH_ABT SUC_ABT MMAIN FSClosed SHU A0T.
Definition ut_res_c : option (list (sst * smodel * fstate * shp * (ast * sfam))) :=
  mcheck ASEGS LIM TBLR IMGR PV 0 0 true None apostUT anilUT aeqbUT awfUT acopyUT asubUT agokUT alins_nil aset_id amod_f [] [] UCH_CT SUC_CT MMAIN FSClosed SHU2 A0T.
