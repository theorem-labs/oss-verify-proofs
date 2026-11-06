(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxDrv FxCall FxGenA.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam FxChEnt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF AsanLit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcSubst AcSteps AcPri AcConvA AcNPop AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes FxPNodesX AsanBNodes AsanQcsX AsanTblH2 AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChSplitS.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxPay HxBaseH HxRebyte HxRecell.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTblH2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblH2.HarnTblX.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Export HarnEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require AcFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require HarnTblL.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require M4Pure HxSurg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require HarnFam HarnLoop HarnSite HarnFk HarnChain HarnFcdT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4H.M4Pure OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HxSurg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.HxDerive OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt.HxLow OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnFam OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnLoop OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnSite OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnFk OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnChain OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnFcdT.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4X Require FcfAD.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition hinfo (St : sst) := (s_pc St, List.length (s_rgs St), List.length (s_facts St), s_next St).
(* [comment removed for export] *)
Definition G0 : pgeo := PGeo (lvar VP) (lvar VN) (lvar VPS) (lvar VQ) (lvar VR).     (* [comment removed for export] *)
Definition G1 : pgeo :=
  let U := nth 1 (s_rgs ENT_S) (RG (lconst 0) (lconst 0) RW TEmpty) in
  let QU := lvar V_QU in let TU := lvar V_TU in
  PGeoU (rg_base U) (laddc (ladd (lscale 8 QU) TU) 1) (oshadow (rg_base U)) QU TU (lvar V_SBU) (rg_size U).
Definition NL : lin := pg_N G1.
Definition genCRLS := genCRLSg G1.
Definition genCRLS0 := genCRLS0g G1.
Definition FCDC : m4con := M4Con FP0 FCD_Q (CKFn [0x91e30]).
(* [comment removed for export] *)
Definition FCFC : m4con := M4Con FcfAD.FP0 FcfAD.FCF_Q (CKFn FcfAD.FRETS).
Definition FCIC : m4con := M4Con OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_fci.P0 OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_fci.Q (CKFn OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_fci.RETS).
Definition CONS : list m4con := [FCDC; FCFC; FCIC].
Definition ppostAll (p : pnode + (hnode + bnode)) (S : sst) (M : smodel) : option sst :=
  match p with
  | inl q => ppostA IMGMd QSITES_P MCSITES_P q S M
  | inr (inl h) => ppostH G1 CONS IMGMd h S M
  | inr (inr b) => ppostB IMGH b S M
  end.
Definition apostH : NPH -> sst -> smodel -> ast -> option (sst * smodel * ast) := apostP (AsanQcsX.apostS (AcFam3.apost_alloc3 LIM) (AsanQcsX.apost_x IMGMd)) ppostAll.
(* [comment removed for export] *)
Definition AGOK_DEV (M : smodel) (a : ast) : bool := true.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TBLHX : tree xi := HarnTblL.TBLHXL.
Definition IMGHX : tree Z := HarnTblL.IMGHXL.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rgtab (S : sst) := List.map (fun R => (rg_base R, rg_size R, rg_kind R, List.length (FxCall.telems (rg_cont R)))) (s_rgs S).

(* [comment removed for export] *)
Definition SEPS0 (k : MCH) : MCH :=
  MSep (TSepS IX_FS) (MSep (TSepS IX_CTX) (MSep (TSepS IX_THR) (MSep (TSepS IX_BLK)
  (MSep (TSepR IX_FS 0x10000 0x63a000) (MSep (TSepR IX_CTX 0x10000 0x63a000)
  (MSep (TSepW IX_CTX IX_FS) (MSep (TSepW IX_THR IX_FS) (MSep (TSepW IX_BLK IX_FS) k)))))))).

(* [comment removed for export] *)
Definition STOPS_HH : list Z := STOPS_H ++ [0x900a0; 0x900a4; 0x8ffc0; 0x90688; 0x906a4; 0x906d8; 0x906f0; 0x90204; 0x9025c; 0x902b8; 0x90604; 0x90740].
Definition P_HH : plan := PRun F60000 STOPS_HH [].
Definition STOPS_H2 : list Z := STOPS_H ++ [0x8ffc0; 0x8fff8; 0x90688; 0x906a4; 0x906d8; 0x906f0; 0x90204; 0x9025c; 0x902b8; 0x90740; 0x908dc; 0xb9c88].
Definition P_H2 : plan := PRun F60000 STOPS_H2 [].
Definition STOPS_B : list Z := [0x90688; 0x906a4; 0x906d8; 0x906f0; 0x90740; 0xd84a4; 0xb84f4].
Definition P_B : plan := PRun F60000 STOPS_B [].
Definition STOPS_B2 : list Z := [0x906a4; 0x906d8; 0x906f0; 0x90740; 0xd84a4; 0xb84f4].
Definition P_B2 : plan := PRun F60000 STOPS_B2 [].
Definition STOPS_L : list Z := [0x901e4; 0x9024c; 0x902a0; 0x90688; 0x906a4; 0x90740; 0xd84a4; 0xb84f4; 0x908dc; 0x90c04; 0x97d00; 0x9c180; 0x90444; 0x90480; 0x8fe64].
Definition P_L : plan := PRun F60000 STOPS_L [].
Definition STOPS_E : list Z := [0x90c04; 0x97d00; 0x9c180; 0x4ad74].
Definition P_E : plan := PRun F60000 STOPS_E [].
Definition STOPS_N : list Z := [0x90208; 0x90260; 0x902bc; 0x4ad74; 0x92454; 0x92138; 0x681cc; 0x683ac].
Definition P_N : plan := PRun F60000 STOPS_N [].
Definition KEND : @mks NPH := KCons 0x906a4 0 MEnd (KCons 0x90740 0 MEnd KNil).
Definition BODY : MCH := MSplitR 18 106 MVoid (
  NODE HPC1 (MSegK 20 P_B2
    (KCons 0x906d8 0 (NODE HPC2 (MSegK 20 P_B2 (KCons 0x906f0 0 (NODE HPLD (MSegK 20 P_B2 KEND)) KEND))) KEND))).
(* [comment removed for export] *)
Definition LOOP (k : MCH) : MCH := NODE (HREB 8 1) (MSegK 20 P_B2
       (KCons 0x906a4 0 (MLoopG genCRLS BODY (KCons 0x90740 0 k KNil)) (KCons 0x90740 0 k KNil))).
(* [comment removed for export] *)
Definition STOPS_B0 : list Z := [0x90688; 0x906a4; 0x906d8; 0x906f0; 0x90740; 0xd84a4; 0xb84f4].
Definition P_B0 : plan := PRun F60000 STOPS_B0 [].
Definition KEND0 : @mks NPH := KCons 0x90688 0 MEnd (KCons 0x90740 0 MEnd KNil).
Definition BODY0 : MCH := MSplitR 18 105 MVoid (MSegK 20 P_B0 (KCons 0x906a4 0
  (NODE HPC1 (MSegK 20 P_B0
    (KCons 0x906d8 0 (NODE HPC2 (MSegK 20 P_B0 (KCons 0x906f0 0 (NODE HPLD (MSegK 20 P_B0 KEND0)) KEND0))) KEND0))) KEND0)).
Definition LOOP0 (k : MCH) : MCH := NODE (HREB 8 1) (MLoopG genCRLS0 BODY0 (KCons 0x90740 0 k KNil)).
(* [comment removed for export] *)
Definition Y2 (S : sst) : lin := HINTof S 2.
Definition CARVE2 (k : MCH) : MCH := SURG (SSplit (fk_carve_fl 2 Y2)) (SURG (SSplit (fk_carve_ar 2 Y2)) (SURG (SSplit (fk_carve_sh 2 Y2)) k)).
(* [comment removed for export] *)
Definition PROMZ2 (k : MCH) : MCH := NODE (HPROMZ (fun S => idx_at S (oshadow (rgk S 10)))) k.
(* [comment removed for export] *)
Definition CUTFSH (k : MCH) : MCH := SURG (SSteps (fk_cut_fsh (fun S => oshadow (rgk S 10)))) k.
Definition ENTRY (k : MCH) : MCH := MSegK 20 P_HH (KCons 0x900a0 0 (CARVE2 (MSegK 20 P_HH (KCons 0x900a4 0 (PROMZ2 (CUTFSH k)) KNil))) KNil).
(* [comment removed for export] *)
Definition fsh_drop (S : sst) : option (list rstep) :=
  match idx_at S (rgk S 24) with
  | Some i => Some [RDrop i; RDrop (Datatypes.S i); RDrop (Datatypes.S (Datatypes.S i)); RDrop (Datatypes.S (Datatypes.S (Datatypes.S i)))]
  | None => None
  end.
(* [comment removed for export] *)
Definition EXIT2 (k : MCH) : MCH :=
  FSH_RW 3 (SURG (SSteps fsh_drop) (SURG (SMerge (fun S => merge_at S (rgk S 24) 3)) (SURG (SMerge (fun S => merge_at S (rgk S 24) 2))
  (SURG (SMerge (fk_mrg3 (fun S => rgk S 24)))
  (SURG (SSteps (fk_drop (fun S => rgk S 25))) (NODE (HIXF (fun S => Some (rgk S 25))) (SURG (SMerge (fk_mrg3 (fun S => rgk S 25)))
  (TRY (HUNZ (fk_unz (fun S => rgk S 10))) (TRY (HPROMZ (fk_unz (fun S => rgk S 10))) (NODE (HIXF (fun S => Some (rgk S 10)))
  (SURG (SMerge (fk_mrg3 (fun S => rgk S 10))) k))))))))))).
(* [comment removed for export] *)
Fixpoint RTPREP_from (n j : nat) (k : MCH) : MCH :=
  match n with O => k | Datatypes.S n' => SURG (SSteps (rt_win j)) (RTPREP_from n' (Datatypes.S j) k) end.
(* [comment removed for export] *)
Definition RTREP (k : MCH) : MCH :=
  TRY (HZBK cs_zbk_lsan) (TRY (HZBK cs_zbk_tsd0) (TRY (HZBK cs_zbk_fsh) (TRY (HZBK cs_zbk_tsd) (TRY (HZBK cs_zbk_hme) (TRY (HRB1 cs_rb1_fb) (TRY (HRBK cs_rbk_tlsb)
  (TRY (HRBK cs_rbk_tlse) (TRY (HRBK cs_rbk_beg) k)))))))).
Definition RTPREP (k : MCH) : MCH := RTREP (RTPREP_from RT_NWINS 0 k).
