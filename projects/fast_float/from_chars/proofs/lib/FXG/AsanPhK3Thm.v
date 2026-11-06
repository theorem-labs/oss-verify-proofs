(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.FxChMap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanTblML AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanEntry.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF AsanMainP AsanLit AsanCpSW AsanPhases3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTA AsanPhCTANB AsanPhCTB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTANB.

Module AsanPhK3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.FxChMap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanTblML AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhases3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanLit AsanCpSW AsanPhases3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhL3NB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTA AsanPhCTANB AsanPhCTB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTANB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTZA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhCTZA.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblML OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.AsanMainG1F OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.AsanPhases OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhases3.AsanPhases2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanLit OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanCpSW OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhases3 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTA.AsanPhL3 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhL3NB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTA.AsanPhT3 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTA.AsanPhT4 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTA OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTANB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTANB.AsanPhCTBNB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTZA OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTZA.AsanPhCTZB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcSubst AcMALlib.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition CONTS3 : list (sst * smodel * fstate * shp * ast) := [PHT4_C; CTA_C; CTB_C].
Definition NB4 : positive := Eval vm_compute in s_next PHT4_S.
Definition CHAIN3 : MCW := PHWCL 3 PHL3_S PHL3_N0 PHL3_FS PHL3_SH PHL3_MEAS (GC (MCont 0 NB4)) (KCT2 1 2 CTA_NB CTB_NB (CTZA 3) (CTZB 3)).
Definition ph3_res : option (list (sst * smodel * fstate * shp * ast)) :=
  mcheck ASEGS LIM TBLM IMGMd PV 65536 GHI false (Some H0) apostW anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a [] CONTS3 CHAIN3 PHT3_S PHT3_M PHT3_FS PHT3_SH PHT3_A.
Definition ph3_chk : bool := is_some ph3_res.
End AsanPhK3.


Module AsanPhK3Cert.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhK3Thm.AsanPhK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma ph3_ok : ph3_res = Some nil.
Proof. vm_cast_no_check (eq_refl (Some (@nil (sst * smodel * fstate * shp * ast)))). Qed.
Lemma ph3_chk_true : ph3_chk = true.
Proof. unfold ph3_chk. rewrite ph3_ok. reflexivity. Qed.
End AsanPhK3Cert.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblML OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry.AsanSegs OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanLit OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanCpSW OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhases3 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTA.AsanPhT3 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTA.AsanPhT4 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTA OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTANB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhCTANB.AsanPhCTBNB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhK3Thm.AsanPhK3 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhK3Thm.AsanPhK3Cert.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcHA AcFam AcSubst AcMALlib AcFam2 AcFam2Ok.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Strategy opaque [TBLM TBLMd IMGMd mcheck].

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

#[using="Hoff Hfs Hanode2 Hp1 Hp2 Hp3 Hp4 Hp5 HFL"] Theorem ph3_realizes : forall finals, ph3_res = Some finals -> cont_okA PHT4_C -> cont_okA CTA_C -> cont_okA CTB_C ->
  forall model0 mem0 E ms model, DEN ASEGS LIM model0 mem0 E PHT3_S PHT3_M ms model ->
  INV PV path0 data0 fs0 false (Some H0) mem0 E PHT3_S PHT3_M PHT3_FS model0 -> HAX awf HA E PHT3_S PHT3_M PHT3_A mem0 -> shp_wf (s_next PHT3_S) PHT3_SH = true ->
  (forall S' M' FS' sh' (a' : ast) model0' mem0' E' ms' model', In (S', M', FS', sh', a') finals ->
     DEN ASEGS LIM model0' mem0' E' S' M' ms' model' -> INV PV path0 data0 fs0 false (Some H0) mem0' E' S' M' FS' model0' ->
     HAX awf HA E' S' M' a' mem0' -> shp_wf (s_next S') sh' = true -> agree (s_next PHT3_S) E E' ->
     realizes_cfg ASEGS cfg (mkCfg ms' model') (shp_den path0 fs0 argv0 E' sh')) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (shp_den path0 fs0 argv0 E PHT3_SH).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hanode2 Hp1 Hp2 Hp3 Hp4 Hp5 HFL : LiaFast.U) => LiaFast.u0).
  intros finals Hres Hc2 HcA HcB model0 mem0 E ms model Hd Hi HX Hw Hk.
  change (mcheck ASEGS LIM TBLM IMGMd PV 65536 GHI false (Some H0) apostW anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a [] CONTS3 CHAIN3 PHT3_S PHT3_M PHT3_FS PHT3_SH PHT3_A = Some finals) in Hres.
  assert (Hcp : forall E M (a : ast) m0, HA E M a m0 -> Forall (sbytes_ok (sarg path0 argv0) E m0) (acopy_alloc a)) by (intros; constructor).
  assert (HC : forall j c, nth_error CONTS3 j = Some c -> cont_okA c).
  { intros j c Hj. destruct j as [|[|[|j]]]; [injection Hj as <-; exact Hc2 | injection Hj as <-; exact HcA | injection Hj as <-; exact HcB | destruct j; discriminate Hj]. }
  exact (mchain_sound ASEGS cfg LIM TBLM IMGMd A_wx A_segb Hoff Hfs A_respos A_reswf TBLM_ok IMGMd_ok TBLM_ecall PV path0 data0 fs0 65536 GHI argv0 false (Some H0)
            Hp1 Hp2 (fun _ => Hp3) Hp4 Hp5 (HFL_lb _ _ HFL) ltac:(unfold GHI; lia) Hseg_asan apostW anil aeqb awf HA acopy_alloc asubst ag_ok alins_a aset_a amod_a [] CONTS3 alloc_awf_mono alloc_aeqb_eq alloc_HA_nil alloc_HA_agree anodeW_ok Hcp HA_subst alloc_HA_mod (subs_nil_ok _) (subs_nil_use _) HC
            CHAIN3 PHT3_S PHT3_M PHT3_FS PHT3_SH PHT3_A finals Hres model0 mem0 E ms model Hd Hi HX Hw Hk).
Qed.

(* [comment removed for export] *)
#[using="Hoff Hfs Hanode2 Hp1 Hp2 Hp3 Hp4 Hp5 HFL"] Corollary ph3_cont : cont_okA PHT4_C -> cont_okA CTA_C -> cont_okA CTB_C -> cont_okA PHT3_C.
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hanode2 Hp1 Hp2 Hp3 Hp4 Hp5 HFL : LiaFast.U) => LiaFast.u0).
  intros Hc2 HcA HcB. unfold cont_okA, cont_ok, PHT3_C. cbn [fst snd]. intros model0 mem0 E ms model Hd Hi HX Hw.
  exact (ph3_realizes nil ph3_ok Hc2 HcA HcB model0 mem0 E ms model Hd Hi HX Hw
           (fun S' M' FS' sh' a' model0' mem0' E' ms' model' Hin => False_ind _ Hin)).
Qed.
End Ph.
