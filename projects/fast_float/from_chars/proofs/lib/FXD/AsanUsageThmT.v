(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChAdd FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanUsageT.

Module AsanLeafLib.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec RefLayout ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxMem.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC AsanTblAll.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblAll.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanEntry.
Export OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry.AsanSegs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTblU.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMchr FxMNode AsanQSites FxHNodes FxSNodes AsanSNodes FxDirConv AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanUsageT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblU OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxHNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT.AsanUsage.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma TBLR_ok : tbl_ok ASEGS TBLR. Proof. exact AsanTblAll.TBLA_ok. Qed.
Lemma TBLR_ecall : ecall_ok ASEGS TBLR. Proof. exact AsanTblAll.TBLA_ecall. Qed.
Lemma IMGR_ok : img_ok ASEGS IMGR.
Proof.
  apply mk_img_runs_ok; [|intros p w Hp; rewrite tget_empty in Hp; discriminate].
  assert (H : forallb (fun p => Z.leb 0 (fst p)) U_WR = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. rewrite Forall_forall. intros p Hp. apply Z.leb_le. exact (H p Hp).
Qed.
Lemma QSITES_ok : Forall (qsite_ok ASEGS) QSITES.
Proof.
  unfold QSITES. apply Forall_cons; [exact QS_PRINTF_ok|]. apply Forall_cons; [exact QS_MEMCHR_ok|]. apply Forall_cons; [exact QS_STRNLEN_ok|].
  apply Forall_cons; [exact QS_MEMCPY_S_ok|]. apply Forall_cons; [exact QS_MEMCPY_D_ok|]. apply Forall_nil.
Qed.
Lemma MCSITES_ok : Forall (msite_ok ASEGS) MCSITES.
Proof. unfold MCSITES. apply Forall_cons; [exact MC_SITE_ok | apply Forall_nil]. Qed.

(* [comment removed for export] *)
Lemma ISL_ok : isl_ok ASEGSN ISLX.
Proof. unfold isl_ok, ISLX. split; [lia|]. repeat split; qins_tac. Qed.
Lemma NSITES_ok : Forall (nsite_ok ASEGSN) NSITES.
Proof. unfold NSITES. apply Forall_cons; [exact NS_PCORE_ok | apply Forall_nil]. Qed.

Section Sh.
Variables (path0 : path) (fs0 : Fs.Fs) (argv0 : list byte).
(* [comment removed for export] *)
#[using="Type"] Lemma SHU2_den : forall E, shp_den path0 fs0 argv0 E SHU2 = shp_den path0 fs0 argv0 E SHU.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E. unfold SHU, SHU2. cbn [shp_den List.map concat pend_evs pd_ch pd_off pd_src src_bytes].
  unfold pend_evs. cbn [pd_ch pd_off pd_src src_bytes].
  assert (H0 : Z.to_nat (uE E (lconst 0)) = O) by (unfold uE; rewrite lden_lconst; reflexivity).
  rewrite !H0. f_equal. rewrite !app_nil_r, <- !map_app. rewrite !skipn_O. rewrite <- !app_assoc. reflexivity.
Qed.

End Sh.

Definition PDUM : path := [Z_to_bv 8 120].
Lemma PD1 : path_eqb PDUM [] = false. Proof. reflexivity. Qed.
Lemma PD2 : path_has_slash PDUM = false. Proof. vm_compute. reflexivity. Qed.
Lemma PD4 : (length PDUM < path_max)%nat. Proof. cbn. unfold path_max. lia. Qed.
Lemma PD5 : Forall (fun b => b <> Z_to_bv 8 0) PDUM. Proof. constructor; [intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate | constructor]. Qed.

(* [comment removed for export] *)
Lemma INV_entry : forall sp brk0 mb lim inp path0 mem0 E S M,
  lwf (s_next S) PV = true -> uE E PV + Z.of_nat (length path0) < 0x800000000000 ->
  INV PV path0 [] (in_fs inp) true None mem0 E S M FSClosed (model0 sp brk0 mb lim inp).
Proof.
  intros sp brk0 mb lim inp path0 mem0 E S M Hw Hb. unfold INV.
  refine (conj Hw (conj eq_refl (conj _ (conj _ (conj _ (conj _ (conj eq_refl (conj _ (conj eq_refl (conj eq_refl I)))))))))).
  - intros Hc; discriminate Hc.
  - split; intros Hc; discriminate Hc.      (* [comment removed for export] *)
  - exact Hb.
  - intros Hc; discriminate Hc.
  - split; reflexivity.
Qed.

End AsanLeafLib.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxChFamI AsanFamU AsanUsageT.

Module AsanUsageCertT.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import FxCertLib AsanUsageT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma ut_res_ab_nil : ut_res_ab = Some []. Proof. apply res_nil_eq. vm_cast_no_check (eq_refl true). Qed.
Lemma ut_res_c_nil : ut_res_c = Some []. Proof. apply res_nil_eq. vm_cast_no_check (eq_refl true). Qed.
End AsanUsageCertT.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageThmT.AsanLeafLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep.FxKeep OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxChFamI OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanFamU OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageThmT.AsanUsageCertT.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Strategy opaque [TBLR IMGR mcheck].

Section U.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.
Variables (path0 : path) (fs0 : Fs.Fs) (argv0 : list byte).
Hypothesis Hp1 : path_eqb path0 [] = false.
Hypothesis Hp2 : path_has_slash path0 = false.
Hypothesis Hp4 : (length path0 < path_max)%nat.
Hypothesis Hp5 : Forall (fun b => b <> Z_to_bv 8 0) path0.

(* [comment removed for export] *)
Definition HAUT : valu -> smodel -> ast * sfam -> (word -> option byte) -> Prop := HAsum HA (HA3 (sarg path0 argv0)).

#[using="Hoff"] Lemma anode_okUT : forall nk, anode_ok ASEGS cfg LIM apostUT awfUT HAUT nk.
Proof. LiaFast.lf_pins (fun (Hoff : LiaFast.U) => LiaFast.u0).
  exact (anodeU_ok cfg LIM A_wx A_segb Hoff A_respos A_reswf (sarg path0 argv0) ISLX NSITES ISL_ok NSITES_ok IMGR QSITES MCSITES
           IMGR_ok QSITES_ok MCSITES_ok).
Qed.
#[using="Type"] Lemma HAUT_copy : forall E M a m0, HAUT E M a m0 -> Forall (sbytes_ok (sarg path0 argv0) E m0) (acopyUT a).
Proof. LiaFast.lf_pins LiaFast.u0. intros E M [a1 a2] m0 [_ H]. apply Forall_forall. exact (HA3_copy (sarg path0 argv0) E M a2 m0 H). Qed.
#[using="Type"] Lemma awfUT_mono : forall n n' a, (n <= n')%positive -> awfUT n a = true -> awfUT n' a = true.
Proof. LiaFast.lf_pins LiaFast.u0. exact (awfX_mono awf awf3 alloc_awf_mono awf3_mono). Qed.
#[using="Type"] Lemma aeqbUT_eq : forall x y, aeqbUT x y = true -> x = y.
Proof. LiaFast.lf_pins LiaFast.u0. exact (aeqbX_eq aeqb aeqb3 alloc_aeqb_eq aeqb3_eq). Qed.
#[using="Type"] Lemma HAUT_nil : forall E M a m0, anilUT a = true -> HAUT E M a m0.
Proof. LiaFast.lf_pins LiaFast.u0. exact (HAsum_nil anil HA anil3 (HA3 (sarg path0 argv0)) alloc_HA_nil (HA3_nil (sarg path0 argv0))). Qed.
#[using="Type"] Lemma HAUT_agree : forall n E E' M a m0, sm_wf n M = true -> awfUT n a = true -> agree n E E' -> HAUT E M a m0 -> HAUT E' M a m0.
Proof. LiaFast.lf_pins LiaFast.u0. exact (HAsum_agree awf HA awf3 (HA3 (sarg path0 argv0)) alloc_HA_agree (HA3_agree (sarg path0 argv0))). Qed.

#[using="Hoff Hfs Hp1 Hp2 Hp4 Hp5"] Theorem ut_realizesM : forall ch S0 M0 sh0 (a0 : ast * sfam) finals,
  mcheck ASEGS LIM TBLR IMGR PV 0 0 true None apostUT anilUT aeqbUT awfUT acopyUT asubUT agokUT alins_nil aset_id amod_f [] [] ch S0 M0 FSClosed sh0 a0 = Some finals ->
  forall model0 mem0 E ms model, DEN ASEGS LIM model0 mem0 E S0 M0 ms model ->
  INV PV path0 [] fs0 true None mem0 E S0 M0 FSClosed model0 -> HAX awfUT HAUT E S0 M0 a0 mem0 -> shp_wf (s_next S0) sh0 = true ->
  (forall S' M' FS' sh' (a' : ast * sfam) model0' mem0' E' ms' model', In (S', M', FS', sh', a') finals ->
     DEN ASEGS LIM model0' mem0' E' S' M' ms' model' -> INV PV path0 [] fs0 true None mem0' E' S' M' FS' model0' ->
     HAX awfUT HAUT E' S' M' a' mem0' -> shp_wf (s_next S') sh' = true -> agree (s_next S0) E E' ->
     realizes_cfg ASEGS cfg (mkCfg ms' model') (shp_den path0 fs0 argv0 E' sh')) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (shp_den path0 fs0 argv0 E sh0).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hp1 Hp2 Hp4 Hp5 : LiaFast.U) => LiaFast.u0).
  intros ch S0 M0 sh0 a0 finals Hres model0 mem0 E ms model Hd Hi HX Hw Hk.
  assert (HFL : 0 <= Z.of_nat (length ([] : list byte)) <= 0) by (cbn; lia).
  exact (mchain_sound ASEGS cfg LIM TBLR IMGR A_wx A_segb Hoff Hfs A_respos A_reswf TBLR_ok IMGR_ok TBLR_ecall PV path0 [] fs0 0 0 argv0 true None
           Hp1 Hp2 (fun H => ltac:(discriminate H)) Hp4 Hp5 (HFL_of _ _ _ HFL) ltac:(lia) Hseg_asan apostUT anilUT aeqbUT awfUT HAUT acopyUT asubUT agokUT alins_nil aset_id amod_f [] [] awfUT_mono aeqbUT_eq
           HAUT_nil HAUT_agree anode_okUT HAUT_copy (fun _ _ _ _ _ H _ => ltac:(discriminate H)) (fun _ _ _ _ _ H _ => ltac:(discriminate H)) (subs_nil_ok _) (subs_nil_use _) (conts_nil_ok _)
           ch S0 M0 FSClosed sh0 a0 finals Hres model0 mem0 E ms model Hd Hi HX Hw Hk).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma FSU_wfT : Forall (fun g => fwf (s_next TMAIN) g = true) FSU.
Proof. LiaFast.lf_pins LiaFast.u0. apply Forall_forall. intros g Hg. assert (H : forallb (fwf (s_next TMAIN)) FSU = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. exact (H g Hg). Qed.
#[using="Type"] Theorem den_conv_ut : forall model0 mem0 E ms model, DEN ASEGS LIM model0 mem0 E TMAIN MMAIN ms model -> Forall (fact_ok E) FSU ->
  DEN ASEGS LIM model0 mem0 E SUT MMAIN ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 mem0 E ms model Hd HF. unfold SUT.
  apply den_add_facts; [exact Hd|].
  pose proof FSU_wfT as W. rewrite Forall_forall in W, HF |- *. intros g Hg. exact (conj (W g Hg) (HF g Hg)).
Qed.

#[using="Type"] Lemma SUT_next : s_next SUT = s_next TMAIN. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma A0T_wf : awfUT (s_next SUT) A0T = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma SHU_wfT : shp_wf (s_next SUT) SHU = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma SHU2_wfT : shp_wf (s_next SUT) SHU2 = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma lv11_wfT : lwf (s_next SUT) (lvar 11) = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Hoff Hfs Hp1 Hp2 Hp4 Hp5"] Theorem ut_handoff : forall model0 mem0 E ms model,
  DEN ASEGS LIM model0 mem0 E TMAIN MMAIN ms model ->
  INV PV path0 [] fs0 true None mem0 E TMAIN MMAIN FSClosed model0 ->
  Forall (fact_ok E) FSU ->
  HA E MMAIN AMAIN mem0 ->
  HA3 (sarg path0 argv0) E MMAIN A0 mem0 ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (shp_den path0 fs0 argv0 E SHU).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hp1 Hp2 Hp4 Hp5 : LiaFast.U) => LiaFast.u0).
  intros model0 mem0 E ms model Hd Hi HF HAa HA.
  pose proof (den_conv_ut model0 mem0 E ms model Hd HF) as Hd1.
  assert (Hi1 : INV PV path0 [] fs0 true None mem0 E SUT MMAIN FSClosed model0)
    by exact (INV_same PV path0 [] fs0 true None mem0 E TMAIN SUT MMAIN FSClosed model0 Hi SUT_next).
  assert (Hn : forall f, s_next (add_fact SUT f) = s_next SUT) by reflexivity.
  pose proof (u_range E (lvar 11)) as R11.
  destruct (Z_le_gt_dec (bv_unsigned (lden E (lvar 11))) 73) as [Hle|Hgt].
  - apply (ut_realizesM UCH_ABT SUC_ABT MMAIN SHU A0T [] ut_res_ab_nil model0 mem0 E ms model).
    + unfold SUC_ABT. apply den_addfact; [exact Hd1|]. intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next SUT) E E' (lvar 11) lv11_wfT Ha'). lia.
    + exact (INV_same PV path0 [] fs0 true None mem0 E SUT SUC_ABT MMAIN FSClosed model0 Hi1 (Hn _)).
    + split; [unfold SUC_ABT; rewrite Hn; exact A0T_wf | exact (conj HAa HA)].
    + unfold SUC_ABT. rewrite Hn. exact SHU_wfT.
    + intros S' M' FS' sh' a' model0' mem0' E' ms' model' Hin. destruct Hin.
  - rewrite <- SHU2_den.
    apply (ut_realizesM UCH_CT SUC_CT MMAIN SHU2 A0T [] ut_res_c_nil model0 mem0 E ms model).
    + unfold SUC_CT. apply den_addfact; [exact Hd1|]. intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next SUT) E E' (lvar 11) lv11_wfT Ha').
      unfold M64, two64 in *. lia.
    + exact (INV_same PV path0 [] fs0 true None mem0 E SUT SUC_CT MMAIN FSClosed model0 Hi1 (Hn _)).
    + split; [unfold SUC_CT; rewrite Hn; exact A0T_wf | exact (conj HAa HA)].
    + unfold SUC_CT. rewrite Hn. exact SHU2_wfT.
    + intros S' M' FS' sh' a' model0' mem0' E' ms' model' Hin. destruct Hin.
Qed.
End U.
