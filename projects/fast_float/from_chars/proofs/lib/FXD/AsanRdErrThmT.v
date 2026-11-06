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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDir FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDir OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC AsanTMain2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcHA AcFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTblU.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMchr FxMNode AsanQSites FxSNodes AsanSNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanPNodes FxSFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanSFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanSFam3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblU OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3.AsanCpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxDirConv AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanRdConvT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanUsageThmT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxChFamI AsanFamU AsanUsageT AsanUsageThmT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxDirConvOwn AsanRdErrT AsanRdErrCertT AsanRdConvT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdConvT.AsanRdConv OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageThmT.AsanLeafLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep.FxKeep OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxChFamI OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanFamU OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageThmT OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt.FxDropOwn OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxDirConvOwn OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErrT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErrCertT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdConvT.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Strategy opaque [TBLR IMGR mcheck].

Section RdT.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.
Variables (path0 : path) (fs0 : Fs.Fs) (argv0 : list byte).
Hypothesis Hp1 : path_eqb path0 [] = false.
Hypothesis Hp2 : path_has_slash path0 = false.
Hypothesis Hp4 : (length path0 < path_max)%nat.
Hypothesis Hp5 : Forall (fun b => b <> Z_to_bv 8 0) path0.

#[using="Type"] Lemma SHD_wfT : shp_wf (s_next SRT) SHD = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma ART_wf : awfUT (s_next SRT) ART = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Hoff Hfs Hp1 Hp2 Hp4 Hp5"] Theorem rd_handoffT : forall model0 mem0 E ms model,
  DEN ASEGS LIM model0 mem0 E TMAIN MMAIN ms model ->
  INV PV path0 [] fs0 true None mem0 E TMAIN MMAIN FSClosed model0 ->
  HA E MMAIN AMAIN mem0 ->
  Forall (fact_ok E) FSRT -> uE E (fst FRZT) <= uE E PV ->
  (forall w, uE E PV <= w < uE E PV + uE E SZR - 16 -> mem0 (Z_to_bv 64 w) <> None) ->
  mem0 (Z_to_bv 64 (uE E PV)) = Some (Z_to_bv 8 46) /\ mem0 (Z_to_bv 64 (uE E PV + 1)) = Some (Z_to_bv 8 0) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (shp_den path0 fs0 argv0 E SHD).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hp1 Hp2 Hp4 Hp5 : LiaFast.U) => LiaFast.u0).
  intros model0 mem0 E ms model Hd Hi HAa HF HP0 HM HB.
  pose proof (den_conv_rdT model0 mem0 E ms model Hd HF HP0 HM HB) as Hd1.
  apply (ut_realizesM cfg Hoff Hfs path0 fs0 argv0 Hp1 Hp2 Hp4 Hp5 RDCHT SRT MRT SHD ART [] rd_res_nilT model0 mem0 E ms model).
  - exact Hd1.
  - exact (INV_conv_rd path0 fs0 mem0 E TMAIN SRT MMAIN MRT FSClosed model0 SRT_next Hi).
  - split; [exact ART_wf|]. split.
    + apply (HA_ext E MMAIN MRT AMAIN mem0 mem0); [apply incl_refl | apply incl_refl | intros x Hx; exact Hx | intros x _ _; reflexivity | intros _ x _; reflexivity | exact HAa].
    + apply HA3_nil. reflexivity.
  - exact SHD_wfT.
  - intros S' M' FS' sh' a' model0' mem0' E' ms' model' Hin. destruct Hin.
Qed.
End RdT.
