(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxDrv FxCall FxGenA.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam FxChEnt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF AsanLit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcSubst AcSteps AcPri AcConvA AcNPop AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes FxPNodesX AsanBNodes AsanQcsX AsanTblH2 AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChSplitS.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH HxRebyte HxRecell.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXHB Require Import HxPay.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTblH2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2.HarnTblX.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require Export HarnEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require AcFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require HarnTblL.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import M4Pure HxSurg HxDerive HxLow HarnFam HarnFcdT.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require Import HarnLoop HarnSite HarnFk HarnChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4Y Require FcfBD.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
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
Definition FCDC : m4con := M4Con FP0 FCD_Q (CKFn FcdBD.FRETS).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition FCFC : m4con := M4Con FcfBD.FP0 FcfBD.FCF_Q (CKFn FcfBD.FRETS).
Definition FCIC : m4con := M4Con OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_fci.P0 OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_fci.Q (CKFn OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_fci.RETS).
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
  (MSep (TSepR IX_FS 0x10000 0x63c000) (MSep (TSepR IX_CTX 0x10000 0x63c000)
  (MSep (TSepW IX_CTX IX_FS) (MSep (TSepW IX_THR IX_FS) (MSep (TSepW IX_BLK IX_FS) k)))))))).

(* [comment removed for export] *)
Definition STOPS_HH : list Z := STOPS_H ++ [0x900e4; 0x900e8; 0x90010; 0x90898; 0x908bc; 0x908fc; 0x90914; 0x902a0; 0x9030c; 0x9037c; 0x90710; 0x90968].
Definition P_HH : plan := PRun F60000 STOPS_HH [].
Definition STOPS_H2 : list Z := STOPS_H ++ [0x90010; 0x9021c; 0x90898; 0x908bc; 0x908fc; 0x90914; 0x902a0; 0x9030c; 0x9037c; 0x90968; 0x90c14; 0xbb504].
Definition P_H2 : plan := PRun F60000 STOPS_H2 [].
Definition STOPS_B : list Z := [0x90898; 0x908bc; 0x908d4; 0x908fc; 0x90914; 0x90968; 0xd9d20; 0xb9d70].
Definition P_B : plan := PRun F60000 STOPS_B [].
Definition STOPS_B2 : list Z := [0x908bc; 0x908d4; 0x908fc; 0x90914; 0x90968; 0xd9d20; 0xb9d70].
Definition P_B2 : plan := PRun F60000 STOPS_B2 [].
Definition STOPS_L : list Z := [0x9026c; 0x902e4; 0x90350; 0x90898; 0x908bc; 0x90968; 0xd9d20; 0xb9d70; 0x90c14; 0x90f3c; 0x98cb8; 0x9d970; 0x90528; 0x90564; 0x8fe58].
Definition P_L : plan := PRun F60000 STOPS_L [].
Definition STOPS_E : list Z := [0x90f3c; 0x98cb8; 0x9d970; 0x4b204].
Definition P_E : plan := PRun F60000 STOPS_E [].
Definition STOPS_N : list Z := [0x902a4; 0x90310; 0x90380; 0x4b204; 0x9244c; 0x92788; 0x681c0; 0x683a0].
Definition P_N : plan := PRun F60000 STOPS_N [].
Definition KEND : @mks NPH := KCons 0x908bc 0 MEnd (KCons 0x90968 0 MEnd KNil).
(* [comment removed for export] *)
Definition HPC1L (P : plan) (k : MCH) : MCH := NODE HPC1 (MSegK 20 P (KCons 0x908d4 0 (NODE HPL1 k) KNil)).
Definition BODY : MCH := MSplitR 22 21 (
  HPC1L P_B2 (MSegK 20 P_B2
    (KCons 0x908fc 0 (NODE HPC2 (MSegK 20 P_B2 (KCons 0x90914 0 (NODE HPLD (MSegK 20 P_B2 KEND)) KEND))) KEND))) MVoid.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition LOOP (k : MCH) : MCH := NODE (HREB 24 1) (MSegK 20 P_B2
       (KCons 0x908bc 0 (MLoopG genCRLS BODY (KCons 0x90968 0 k KNil)) (KCons 0x90968 0 k KNil))).
(* [comment removed for export] *)
Definition STOPS_B0 : list Z := [0x90898; 0x908bc; 0x908d4; 0x908fc; 0x90914; 0x90968; 0xd9d20; 0xb9d70].
Definition P_B0 : plan := PRun F60000 STOPS_B0 [].
Definition KEND0 : @mks NPH := KCons 0x90898 0 MEnd (KCons 0x90968 0 MEnd KNil).
Definition BODY0 : MCH := MSplitR 22 22 (MSegK 20 P_B0 (KCons 0x908bc 0
  (HPC1L P_B0 (MSegK 20 P_B0
    (KCons 0x908fc 0 (NODE HPC2 (MSegK 20 P_B0 (KCons 0x90914 0 (NODE HPLD (MSegK 20 P_B0 KEND0)) KEND0))) KEND0))) KEND0)) MVoid.      (* [comment removed for export] *)
Definition LOOP0 (k : MCH) : MCH := NODE (HREB 24 1) (MLoopG genCRLS0 BODY0 (KCons 0x90968 0 k KNil)).
(* [comment removed for export] *)
Definition Y2 (S : sst) : lin := HINTof S 2.
Definition CARVE2 (k : MCH) : MCH := SURG (SSplit (fk_carve_fl 2 Y2)) (SURG (SSplit (fk_carve_ar 2 Y2)) (SURG (SSplit (fk_carve_sh 2 Y2)) k)).
(* [comment removed for export] *)
Definition PROMZ2 (k : MCH) : MCH := NODE (HPROMZ (fun S => idx_at S (oshadow (rgk S 10)))) k.
(* [comment removed for export] *)
Definition CUTFSH (k : MCH) : MCH := SURG (SSteps (fk_cut_fsh (fun S => oshadow (rgk S 10)))) k.
Definition ENTRY (k : MCH) : MCH := MSegK 20 P_HH (KCons 0x900e4 0 (CARVE2 (MSegK 20 P_HH (KCons 0x900e8 0 (PROMZ2 (CUTFSH k)) KNil))) KNil).
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
(* [comment removed for export] *)
