(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChain FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanEntry AsanPlan AsanStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF AsanMainP AsanErrT AsanPhT1.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhCTA AsanPhCTB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhKCAThm.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhKCBThm.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhKS AsanPhKW AsanPhK0 AsanPhKCAThm AsanPhKCBThm AsanPhKSThm AsanPhKWThm AsanPhK0Thm AsanPhK1Thm AsanPhK2Thm AsanPhK3Thm AsanPhK4Thm AsanPhK5Thm AsanPhK6Thm AsanPhK7Thm AsanPhK8Thm AsanPhK9Thm AsanPhK10Thm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanErrT OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhT1 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhT2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhT3 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhT4 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhT5 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhT6 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhT7 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhT8 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhT9 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA.AsanPhT10 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTA OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhCTB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhKCAThm.AsanPhKCA OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhKCBThm.AsanPhKCB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhKS OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhKW OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK0 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhKCAThm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhKCBThm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhKSThm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhKWThm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK0Thm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK1Thm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK2Thm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK3Thm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK4Thm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK5Thm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK6Thm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK7Thm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK8Thm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK9Thm OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhK10Thm.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition FLLO : Z := 67108864.
Definition SHL : shp := SH_TOP SH_REFUSED.
Definition S1L2 : sst := S1P2.

Section All.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.
Variables (path0 : path) (data0 : list byte) (fs0 : Fs.Fs) (argv0 : list byte).
Hypothesis Hp1 : path_eqb path0 [] = false.
Hypothesis Hp2 : path_has_slash path0 = false.
Hypothesis Hp3 : path_is_dirref path0 = false.
Hypothesis Hp4 : (length path0 < path_max)%nat.
Hypothesis Hp5 : Forall (fun b => b <> Z_to_bv 8 0) path0.
Definition cont_okR := cont_ok ASEGS cfg LIM PV path0 data0 fs0 argv0 false (Some H0) awf HA.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma inv_len1 : forall mem0 E S M FS model0, INV PV path0 data0 fs0 false (Some H0) mem0 E S M FS model0 ->
  bv_unsigned (E (dvar H0 16)) = flen data0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E S M FS model0 Hi. destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdv).
  unfold hv_inv in Hdv. destruct Hdv as (_ & _ & HL & _). exact HL.
Qed.
#[using="Type"] Lemma flen_min : flen data0 = Z.min (Z.of_nat (length data0)) GHI.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma ue_hvar16 : forall E, uE E (hvar 16) = bv_unsigned (E (dvar H0 16)).
Proof. LiaFast.lf_pins LiaFast.u0. intros E. unfold uE, hvar. rewrite lden_lvar. reflexivity. Qed.
#[using="Type"] Lemma inv_len : forall mem0 E S M FS model0, INV PV path0 data0 fs0 false (Some H0) mem0 E S M FS model0 ->
  uE E (hvar 16) = Z.min (Z.of_nat (length data0)) GHI.
Proof. LiaFast.lf_pins LiaFast.u0. intros mem0 E S M FS model0 Hi. rewrite ue_hvar16, (inv_len1 _ _ _ _ _ _ Hi). exact flen_min. Qed.
#[using="Type"] Lemma shp_den_if : forall E l lo hi a b, shp_den path0 fs0 argv0 E (ShIf l lo hi a b) =
  if (Z.leb lo (uE E l) && Z.leb (uE E l) hi)%bool then shp_den path0 fs0 argv0 E a else shp_den path0 fs0 argv0 E b.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma shp_den_alt2 : forall E a b, shp_den path0 fs0 argv0 E (ShAlt2 a b) = t_alt2 (shp_den path0 fs0 argv0 E a) (shp_den path0 fs0 argv0 E b).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Hp4"] Lemma shg_bounded : forall E, uE E (hvar 16) <= PHI -> shp_den path0 fs0 argv0 E SHG = shp_den path0 fs0 argv0 E SHWF.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros E H. pose proof (bv_unsigned_in_range _ (lden E (hvar 16))) as R. fold (uE E (hvar 16)) in R.
  unfold SHG, SHWF, SH_TOP. rewrite !shp_den_if, !shp_den_alt2. unfold FILE_G. rewrite shp_den_if.
  replace (Z.leb 0 (uE E (hvar 16)) && Z.leb (uE E (hvar 16)) PHI)%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
#[using="Type"] Lemma shg_refused : forall E, PHI < uE E (hvar 16) -> shp_den path0 fs0 argv0 E SHG = shp_den path0 fs0 argv0 E SHL.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E H. unfold SHG, SHL, SH_TOP. rewrite !shp_den_if, !shp_den_alt2. unfold FILE_G. rewrite shp_den_if.
  replace (Z.leb 0 (uE E (hvar 16)) && Z.leb (uE E (hvar 16)) PHI)%bool with false; [reflexivity|].
  symmetry. apply andb_false_intro2. apply Z.leb_gt. exact H.
Qed.
#[using="Type"] Lemma shg_wf : shp_wf (s_next S1P2) SHG = true.
Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Hp4"] Lemma cont_vac : forall c : sst * smodel * fstate * shp * ast,
  existsb (fact_eqb (FRange (hvar 16) 6 PHI)) (s_facts (fst (fst (fst (fst c))))) = true -> PHI < Z.of_nat (length data0) -> cont_okR c.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros c Hex Hbig. unfold cont_okR, cont_ok. intros model0 mem0 E ms model Hd Hi HX Hw. exfalso.
  apply existsb_exists in Hex. destruct Hex as (f & Hin & Hf). apply fact_eqb_eq in Hf. subst f.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  rewrite Forall_forall in HF0. specialize (HF0 _ Hin). cbn [fact_ok] in HF0.
  pose proof (inv_len _ _ _ _ _ _ Hi) as HL. unfold uE in HL. rewrite HL in HF0. unfold PHI, GHI in *. lia.
Qed.

(* [comment removed for export] *)
Hypothesis HleafA : Forall cont_okR CONTSCA.
Hypothesis HleafB : Forall cont_okR CONTSCB.
Hypothesis Herr : cont_okR TERR_C.
(* [comment removed for export] *)
#[using="Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 HleafA"] Lemma ctA_ok : 6 <= Z.of_nat (length data0) <= PHI -> cont_okR CTA_C.
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 HleafA : LiaFast.U) => LiaFast.u0). intros HFL. exact (phca_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL HleafA). Qed.
#[using="Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 HleafB"] Lemma ctB_ok : 6 <= Z.of_nat (length data0) <= PHI -> cont_okR CTB_C.
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 HleafB : LiaFast.U) => LiaFast.u0). intros HFL. exact (phcb_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL HleafB). Qed.
#[using="Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 Herr"] Theorem short_realizes : 0 <= Z.of_nat (length data0) <= 5 ->
  forall model0 mem0 E ms model, DEN ASEGS LIM model0 mem0 E S1S2 M1c ms model ->
  INV PV path0 data0 fs0 false (Some H0) mem0 E S1S2 M1c FSClosed model0 -> HAX awf HA E S1S2 M1c A1c mem0 -> shp_wf (s_next S1S2) SHSF = true ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (shp_den path0 fs0 argv0 E SHSF).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 Herr : LiaFast.U) => LiaFast.u0). intros HFL. exact (phs_realizes cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL Herr). Qed.
#[using="Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 HleafA HleafB Herr"] Theorem wide_realizes : 6 <= Z.of_nat (length data0) <= 65535 ->
  forall model0 mem0 E ms model, DEN ASEGS LIM model0 mem0 E S1W2 M1c ms model ->
  INV PV path0 data0 fs0 false (Some H0) mem0 E S1W2 M1c FSClosed model0 -> HAX awf HA E S1W2 M1c A1c mem0 -> shp_wf (s_next S1W2) SHWF = true ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (shp_den path0 fs0 argv0 E SHWF).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 HleafA HleafB Herr : LiaFast.U) => LiaFast.u0).
  intros HFL. assert (H6 : 6 <= Z.of_nat (length data0) <= PHI) by (unfold PHI; lia).
  exact (phw_realizes cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL (ctA_ok H6) (ctB_ok H6) Herr).
Qed.
(* [comment removed for export] *)
#[using="Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 Herr"] Lemma grow_all_realizes : 65536 <= Z.of_nat (length data0) -> cont_okR CTA_C -> cont_okR CTB_C ->
  forall model0 mem0 E ms model, DEN ASEGS LIM model0 mem0 E S1P2 M1c ms model ->
  INV PV path0 data0 fs0 false (Some H0) mem0 E S1P2 M1c FSClosed model0 -> HAX awf HA E S1P2 M1c A1c mem0 ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (shp_den path0 fs0 argv0 E SHG).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 Herr : LiaFast.U) => LiaFast.u0).
  intros HFL HA0 HB0.
  pose proof (ph10_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL HA0 HB0) as H10.
  pose proof (ph9_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL H10 HA0 HB0) as H9.
  pose proof (ph8_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL H9 HA0 HB0) as H8.
  pose proof (ph7_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL H8 HA0 HB0) as H7.
  pose proof (ph6_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL H7 HA0 HB0) as H6'.
  pose proof (ph5_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL H6' HA0 HB0) as H5.
  pose proof (ph4_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL H5 HA0 HB0) as H4.
  pose proof (ph3_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL H4 HA0 HB0) as H3.
  pose proof (ph2_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL H3 HA0 HB0) as H2.
  pose proof (ph1_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL H2 HA0 HB0) as H1.
  intros model0 mem0 E ms model Hd Hi HX.
  exact (ph0_realizes cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL H1 Herr model0 mem0 E ms model Hd Hi HX shg_wf).
Qed.
(* [comment removed for export] *)
#[using="Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 HleafA HleafB Herr"] Theorem grow_realizes : 65536 <= Z.of_nat (length data0) <= PHI ->
  forall model0 mem0 E ms model, DEN ASEGS LIM model0 mem0 E S1P2 M1c ms model ->
  INV PV path0 data0 fs0 false (Some H0) mem0 E S1P2 M1c FSClosed model0 -> HAX awf HA E S1P2 M1c A1c mem0 -> shp_wf (s_next S1P2) SHWF = true ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (shp_den path0 fs0 argv0 E SHWF).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 HleafA HleafB Herr : LiaFast.U) => LiaFast.u0).
  intros HFL model0 mem0 E ms model Hd Hi HX _.
  assert (H6 : 6 <= Z.of_nat (length data0) <= PHI) by lia.
  rewrite <- (shg_bounded E) by (rewrite (inv_len _ _ _ _ _ _ Hi); unfold PHI, GHI in *; lia).
  exact (grow_all_realizes (proj1 HFL) (ctA_ok H6) (ctB_ok H6) model0 mem0 E ms model Hd Hi HX).
Qed.
(* [comment removed for export] *)
#[using="Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 Herr"] Theorem refused_realizes_R : FLLO <= Z.of_nat (length data0) ->
  forall model0 mem0 E ms model, DEN ASEGS LIM model0 mem0 E S1L2 M1c ms model ->
  INV PV path0 data0 fs0 false (Some H0) mem0 E S1L2 M1c FSClosed model0 -> HAX awf HA E S1L2 M1c A1c mem0 -> shp_wf (s_next S1L2) SHL = true ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (shp_den path0 fs0 argv0 E SHL).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 Herr : LiaFast.U) => LiaFast.u0).
  unfold S1L2. intros HFL model0 mem0 E ms model Hd Hi HX _.
  assert (Hbig : PHI < Z.of_nat (length data0)) by (unfold FLLO, PHI in *; lia).
  rewrite <- (shg_refused E) by (rewrite (inv_len _ _ _ _ _ _ Hi); unfold PHI, GHI in *; lia).
  exact (grow_all_realizes ltac:(unfold FLLO in HFL; lia) (cont_vac CTA_C ltac:(vm_compute; reflexivity) Hbig) (cont_vac CTB_C ltac:(vm_compute; reflexivity) Hbig)
           model0 mem0 E ms model Hd Hi HX).
Qed.
End All.
(* [comment removed for export] *)
