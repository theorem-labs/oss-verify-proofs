(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0.
Import ListNotations.
Open Scope Z_scope.

Section CoarseView.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis Hoff : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Definition hid_same (ms ms' : machine_state) : Prop := forall a, H a = true -> ms_mem ms' a = ms_mem ms a.

Lemma mstep_restrict_lift : forall ms msr',
mstep segs (restrict H ms) msr' ->
mstep segs ms (unrestrict H (ms_mem ms) msr') /\ restrict H (unrestrict H (ms_mem ms) msr') = msr' /\
hid_same ms (unrestrict H (ms_mem ms) msr').
Proof.
intros ms msr' [Hsvc Hst]. rewrite restrict_svc_pending in Hsvc.
destruct (step_restrict_sound segs H Hoff Hwx ms msr' Hst) as (rep & Hsa & Hv & _ & _ & Hr).
split; [split; [exact Hsvc| exact (step_restrict_step segs H Hoff Hwx ms msr' Hst)]|]. split; [exact Hr|].
intros a Ha. rewrite unrestrict_mem. unfold munrestrict. rewrite Ha. reflexivity.
Qed.

Lemma msteps_restrict_lift : forall msr msr', msteps segs msr msr' ->
forall ms, restrict H ms = msr ->
exists ms', msteps segs ms ms' /\ restrict H ms' = msr' /\ hid_same ms ms'.
Proof.
intros msr msr' Hs. induction Hs as [msr | msr msr1 msr2 H1 _ IH]; intros ms E.
- exists ms. split; [apply msteps_refl|]. split; [exact E| intros a _; reflexivity].
- subst msr. destruct (mstep_restrict_lift ms msr1 H1) as (Hst & Hr & Hh).
destruct (IH _ Hr) as (ms' & Hs' & Hr' & Hh').
exists ms'. split; [eapply msteps_cons; eassumption|]. split; [exact Hr'|].
intros a Ha. rewrite (Hh' a Ha). exact (Hh a Ha).
Qed.

Theorem evt_restrict_lift : forall (Q : machine_state -> Prop) ms,
evt segs Q (restrict H ms) ->
evt segs (fun ms' => Q (restrict H ms') /\ hid_same ms ms') ms.
Proof.
intros Q ms (msr' & Hs & HQ).
destruct (msteps_restrict_lift _ _ Hs ms eq_refl) as (ms' & Hs' & Hr & Hh).
exists ms'. split; [exact Hs'|]. rewrite Hr. split; [exact HQ| exact Hh].
Qed.

End CoarseView.

Section NoneKeep.
Variable segs : list Segment.
Hypothesis Hwx : wx_segs_nowrap segs.

Definition offseg (y : word) : bool := match find_segment segs (bv_unsigned y) 1 with None => true | Some _ => false end.
Definition noneset (ms : machine_state) (y : word) : bool := offseg y && match ms_mem ms y with None => true | Some _ => false end.

Lemma noneset_off : forall ms, H_off_segments segs (noneset ms).
Proof. intros ms y Hy. unfold noneset, offseg in Hy. destruct (find_segment segs (bv_unsigned y) 1); [discriminate| reflexivity]. Qed.

Lemma noneset_hclean : forall ms, hclean (noneset ms) ms.
Proof. intros ms y Hy. unfold noneset in Hy. destruct (ms_mem ms y); [rewrite andb_false_r in Hy; discriminate| reflexivity]. Qed.

Lemma msteps_none_keep : forall ms ms', msteps segs ms ms' ->
forall y, offseg y = true -> ms_mem ms y = None -> ms_mem ms' y = None.
Proof.
intros ms ms' Hs.
assert (G : forall U, H_off_segments segs U -> hclean U ms -> hclean U ms').
{ intros U HU. induction Hs as [ms | ms ms1 ms2 H1 _ IH]; intros Hc; [exact Hc|].
apply IH. destruct H1 as [_ Hst]. exact (step_hclean segs U HU Hwx ms ms1 Hc Hst). }
intros y Ho Hn. apply (G (noneset ms) (noneset_off ms) (noneset_hclean ms) y). unfold noneset. rewrite Ho, Hn. reflexivity.
Qed.

Variable H : word -> bool.
Hypothesis Hoff : H_off_segments segs H.

Theorem evt_restrict_lift2 : forall (Q : machine_state -> Prop) ms,
evt segs Q (restrict H ms) ->
evt segs (fun ms' => Q (restrict H ms') /\ hid_same H ms ms' /\
(forall y, offseg y = true -> ms_mem ms y = None -> ms_mem ms' y = None)) ms.
Proof.
intros Q ms (msr' & Hs & HQ).
destruct (msteps_restrict_lift segs H Hoff Hwx _ _ Hs ms eq_refl) as (ms' & Hs' & Hr & Hh).
exists ms'. split; [exact Hs'|]. rewrite Hr. split; [exact HQ|]. split; [exact Hh|].
intros y Ho Hn. exact (msteps_none_keep ms ms' Hs' y Ho Hn).
Qed.

End NoneKeep.
