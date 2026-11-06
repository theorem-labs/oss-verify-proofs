(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanEntry.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF AsanLit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry.AsanSegs OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam AcSubst AcSubstR AcPri AcFam2 AcFam3 AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxMchr AsanQcsX AsanPNodes FxPNodesX AsanTblH2 AsanBodyE AsanBNodes AsanBodyFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTblH2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.

Module AsanTailCertE.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF AsanLit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcFam AcSubst AcPri AcConvA AcNPop AcNPopG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2 AcFam3 AcMALlib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSubst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam3 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxMchr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMNode AsanQcsX AsanPNodes FxPNodesX AsanTblH2 AsanBodyE AsanBNodes AsanBodyFam AsanTailCh AsanBodyCh AsanBodyCh2 AsanBodyCh2w.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTblH2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyCertBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxPNodesX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTailCh OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCh OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCh2 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCh2w OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.FxPChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2.AsanTailDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCertBase OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailTE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailFE.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition FTE_N0 : positive := Eval vm_compute in s_next FTE_S.
Definition FTE_FINS : list (sst * smodel * ast) := [(FTE_S, FTE_M, FTE_A)].
Definition IBT_E : nat := rg_idx_w (s_rgs TTE_S) 0.
(* [comment removed for export] *)
Definition GEN_FTE (L : list (sst * smodel)) (As : list (list lin)) : option (sst * smodel * list lin) := Some (FTE_S, FTE_M, alins_a FTE_A).
Definition KTAILE_CERT : MCB := MJoinG GEN_FTE (TAILF_EW A1B A2B A3B BB (via_of TTE_S) VCT (mp_idx_w (sm_maps TTE_M)) IBT_E MEnd) 0x8fcb8 (MWeaken FTE_S FTE_N0 PFS PSH MEnd).
Definition taile_res : option (list (sst * smodel * ast)) :=
  pchecku ASEGS TBLH IMGH apostB aeqb awf asubst ag_ok alins_a (aset_a) [] amod_a LIM KTAILE_CERT TTE_S TTE_M TTE_A.
Lemma taile_cert : taile_res = Some FTE_FINS.
Proof. vm_cast_no_check (eq_refl (Some FTE_FINS)). Qed.
(* [comment removed for export] *)
End AsanTailCertE.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxPNodesX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyFam OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.FxPChk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.FxPChkSound OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2.AsanTailDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailTE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailFE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTailSubE.AsanTailCertE.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Strategy opaque [TBLH IMGH pchecku].

Section TailSubE.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hanode3 : forall nk, anode_ok ASEGS cfg LIM (apost_alloc3 LIM) awf HA nk.
Hypothesis Hshm : forall model0 mem0 E S M ms model a, DEN ASEGS LIM model0 mem0 E S M ms model -> HA_on E M a mem0 -> a_pri a <> [] ->
  forall c, In c CLS -> 1 <= z_j (pden E a) c ->
  forall x, z_sh (pden E a) + 536870912 * c <= x < z_sh (pden E a) + 536870912 * c + 32768 ->
  rd1 ASEGS (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 x) <> None.

#[using="Hanode3 Hshm"] Theorem taile_sub_ok : sub_ok ASEGS cfg LIM awf HA TTE_S TTE_M TTE_A FTE_FINS.
Proof. LiaFast.lf_pins (fun (Hanode3 Hshm : LiaFast.U) => LiaFast.u0).
  refine (sub_ok_of_pchecku ASEGS cfg LIM TBLH IMGH A_wx TBLH_ok IMGH_ok apostB aeqb awf HA asubst ag_ok alins_a aset_a
           alloc_awf_mono alloc_aeqb_eq alloc_HA_agree (anodeB_ok cfg Hanode3 Hshm) HA_subst [] _ _ amod_a alloc_HA_mod LIM (or_introl eq_refl) KTAILE_CERT TTE_S TTE_M TTE_A FTE_FINS taile_cert).
  - intros j T MT aT fins H. destruct j; discriminate H.
  - intros H. exfalso. apply H. reflexivity.
Qed.
End TailSubE.
(* [comment removed for export] *)
