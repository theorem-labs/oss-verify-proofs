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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanEntry.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF AsanLit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry.AsanSegs OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcHA AcFam AcSubst AcSubstR AcPri AcFam2 AcFam3 AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxMchr AsanQcsX AsanPNodes FxPNodesX AsanTblH2 AsanBodyE AsanBNodes AsanBodyFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxBDec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxBDec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTblH2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanBodyG.

Module AsanTailCertL.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF AsanLit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst AcFam AcSubst AcPri AcConvA AcNPop AcNPopG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2 AcFam3 AcMALlib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSubst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPopG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxMchr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMNode AsanQcsX AsanPNodes FxPNodesX AsanTblH2 AsanBodyE AsanBNodes AsanBodyFam AsanTailCh AsanBodyCh AsanBodyCh2 AsanBodyCh2w.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxBDec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTblH2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanBodyCertBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTblH2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanBodyG.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsX OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxPNodesX OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblH2 OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyE OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyFam OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTailCh OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyCh OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyCh2 OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyCh2w OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxBDec.FxPChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblH2.AsanTailDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyCertBase OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblH2.AsanTailDefsL OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyG.AsanTailTL OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyG.AsanTailFL.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition FTL_N0 : positive := Eval vm_compute in s_next FTL_S.
Definition FTL_FINS : list (sst * smodel * ast) := [(FTL_S, FTL_M, FTL_A)].
(* [comment removed for export] *)
Definition OFF_TL : nat := off_pri TTL_S TTL_M TTL_A.
Definition IBT_L : nat := rg_idx_w (s_rgs TTL_S) 0.
(* [comment removed for export] *)
Definition GEN_FTL (L : list (sst * smodel)) (As : list (list lin)) : option (sst * smodel * list lin) := Some (FTL_S, FTL_M, alins_a FTL_A).
Definition KTAILL_CERT : MCB := MJoinG GEN_FTL (TAILF_LW A1B A2B A3B BB (via_of TTL_S) VCT OFF_TL (mp_idx (LIN 0 [(UBT_L, 4096)]) (sm_maps TTL_M) 0) QUT_L MPT_L (mp_idx_w (sm_maps TTL_M)) IBT_L MEnd) 0x8fcc4 (MWeaken FTL_S FTL_N0 PFS PSH MEnd).
Definition taill_res : option (list (sst * smodel * ast)) :=
  pchecku ASEGS TBLH IMGH apostB aeqb awf asubst ag_ok alins_a (aset_a) [] amod_a LIM KTAILL_CERT TTL_S TTL_M TTL_A.
Lemma taill_cert : taill_res = Some FTL_FINS.
Proof. vm_cast_no_check (eq_refl (Some FTL_FINS)). Qed.
End AsanTailCertL.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsX OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxPNodesX OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblH2 OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyE OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyFam OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxBDec.FxPChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxBDec.FxPChkSound OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblH2.AsanTailDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyG.AsanTailTL OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyG.AsanTailFL OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTailSubL.AsanTailCertL.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Strategy opaque [TBLH IMGH pchecku].

Section TailSubL.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hanode3 : forall nk, anode_ok ASEGS cfg LIM (apost_alloc3 LIM) awf HA nk.
Hypothesis Hshm : forall model0 mem0 E S M ms model a, DEN ASEGS LIM model0 mem0 E S M ms model -> HA_on E M a mem0 -> a_pri a <> [] ->
  forall c, In c CLS -> 1 <= z_j (pden E a) c ->
  forall x, z_sh (pden E a) + 536870912 * c <= x < z_sh (pden E a) + 536870912 * c + 32768 ->
  rd1 ASEGS (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 x) <> None.

#[using="Hanode3 Hshm"] Theorem taill_sub_ok : sub_ok ASEGS cfg LIM awf HA TTL_S TTL_M TTL_A FTL_FINS.
Proof. LiaFast.lf_pins (fun (Hanode3 Hshm : LiaFast.U) => LiaFast.u0).
  refine (sub_ok_of_pchecku ASEGS cfg LIM TBLH IMGH A_wx TBLH_ok IMGH_ok apostB aeqb awf HA asubst ag_ok alins_a aset_a
           alloc_awf_mono alloc_aeqb_eq alloc_HA_agree (anodeB_ok cfg Hanode3 Hshm) HA_subst [] _ _ amod_a alloc_HA_mod LIM (or_introl eq_refl) KTAILL_CERT TTL_S TTL_M TTL_A FTL_FINS taill_cert).
  - intros j T MT aT fins H. destruct j; discriminate H.
  - intros H. exfalso. apply H. reflexivity.
Qed.
End TailSubL.
