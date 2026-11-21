(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YA0n.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK0n YK0i YK15 YK0j.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK0k.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YA0i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Section d.
Open Scope bv_scope.
Section e.
Variable segs : list Segment.
Record world := mkW {
w_H : word -> bool ;
w_A : list (Z * Z) ;
w_Hoff : H_off_segments segs w_H ;
w_Awf : A_wf w_A }.
Definition wle (W W' : world) : Prop := hsub (w_H W') (w_H W).
Lemma wle_refl : forall W, wle W W.
Proof. intros W. apply hsub_refl. Qed.
Lemma wle_trans : forall W1 W2 W3, wle W1 W2 -> wle W2 W3 -> wle W1 W3.
Proof. intros W1 W2 W3 Ha Hc. eapply hsub_trans; [exact Hc | exact Ha]. Qed.
Local Notation AIw W md := (AI segs (w_H W) (w_A W) md).
Definition SRr (W : world) (c : config) (Q : world -> config -> Prop) : Prop :=
AIw W (cfg_model c) ->
forall T, (forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizes segs c' T) ->
srealizes segs c T.
Lemma SRr_ret : forall W c (Q : world -> config -> Prop), Q W c -> SRr W c Q.
Proof. intros W c Q HQ HI T HK. exact (HK W c (wle_refl W) HI HQ). Qed.
Lemma SRr_bind : forall W c (R Q : world -> config -> Prop),
SRr W c R -> (forall W' c', wle W W' -> R W' c' -> SRr W' c' Q) -> SRr W c Q.
Proof.
intros W c R Q H1 H2 HI T HK. apply (H1 HI T). intros W' c' Hle HI' HR.
apply (H2 W' c' Hle HR HI' T). intros W'' c'' Hle' HI'' HQ.
exact (HK W'' c'' (wle_trans _ _ _ Hle Hle') HI'' HQ).
Qed.
Lemma SRr_mono : forall W c (Q Q' : world -> config -> Prop),
SRr W c Q -> (forall W' c', wle W W' -> Q W' c' -> Q' W' c') -> SRr W c Q'.
Proof.
intros W c Q Q' H HQQ HI T HK. apply (H HI T). intros W' c' Hle HI' HQ.
exact (HK W' c' Hle HI' (HQQ W' c' Hle HQ)).
Qed.
Lemma SRr_srealizes : forall W c Q T,
SRr W c Q -> AIw W (cfg_model c) ->
(forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizes segs c' T) ->
srealizes segs c T.
Proof. intros W c Q T H HI HK. exact (H HI T HK). Qed.
Hypothesis Hwx : wx_segs_nowrap segs.
Let KP (W : world) (Q : world -> config -> Prop) (T : TSet) : config -> Prop :=
fun c => AIw W (cfg_model c) -> srealizes segs c T.
Lemma SRr_step : forall W ms msr' model Q,
ms_svc_pending ms = None ->
RiscvSemantics.step segs (restrict (w_H W) ms) = MachineOk msr' ->
(forall model', same_but_materialized model model' ->
SRr W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRr W (mkCfg ms model) Q.
Proof.
intros W ms msr' model Q Hsvc Hs Hk HI T HK.
destruct HI as (HH & Hwf & Hcov & Hinv & Hh).
destruct (node_instr_restricted segs (w_H W) HH Hwx (w_A W) ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
as (model' & Hinv' & Hsame & _ & _ & Hnode).
apply (srz_silent1 segs _ _ T Hnode (bnode_none segs ms model Hsvc)).
apply (Hk model' Hsame).
- apply (AI_same segs (w_H W) (w_A W) model model'); [split; auto | exact Hsame | exact Hinv'].
- exact HK.
Qed.
Lemma SRr_msteps : forall W ms msr' model Q,
msteps segs (restrict (w_H W) ms) msr' ->
(forall model', same_but_materialized model model' ->
hclean (w_H W) msr' ->
SRr W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRr W (mkCfg ms model) Q.
Proof.
intros W ms msr' model Q Hms Hk HI T HK.
destruct HI as (HH & Hwf & Hcov & Hinv & Hh).
apply (srz_msteps_restricted_T segs (w_H W) HH Hwx (w_A W) ms msr' model T Hcov Hwf Hinv Hh Hms).
intros model' Hinv' Hsame Hcl. apply (Hk model' Hsame Hcl).
- apply (AI_same segs (w_H W) (w_A W) model model'); [split; auto | exact Hsame | exact Hinv'].
- exact HK.
Qed.
End e.
End d.
Arguments SRr segs W c Q : clear implicits.
Arguments world segs : clear implicits.
Arguments mkW segs w_H w_A w_Hoff w_Awf : clear implicits.
Arguments wle {segs} W W'.
Arguments w_H {segs} w.
Arguments w_A {segs} w.
Arguments w_Hoff {segs} w.
Arguments w_Awf {segs} w.
