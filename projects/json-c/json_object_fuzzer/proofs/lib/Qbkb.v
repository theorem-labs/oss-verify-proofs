(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd QCUT QwAs QoAA QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0.
Export QoAA.
Import QCiC.Mq0.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Section Pure.
Variable segs : list Segment.
Context {ptr : Type}.

Definition aimp {R} (t : aprog ptr R) (Q : R -> machine_state -> Prop) (ms : machine_state) : Prop :=
match t with
| ARet r => evt segs (Q r) ms
| AUnr => True
| AMalloc _ _ => False
| AFree _ _ => False
end.

Lemma aimp_ARet {R} (r : R) Q ms : evt segs (Q r) ms -> aimp (ARet r) Q ms.
Proof. exact (fun H => H). Qed.
Lemma aimp_AUnr {R} (Q : R -> machine_state -> Prop) ms : aimp AUnr Q ms.
Proof. exact I. Qed.

Lemma aimp_evt {R} (t : aprog ptr R) Q P ms :
evt segs P ms -> (forall ms', P ms' -> aimp t Q ms') -> aimp t Q ms.
Proof.
intros H K. destruct t as [r| |n k|p k]; cbn.
- eapply evt_cut; [exact H|]. intros ms' HP. exact (K ms' HP).
- exact I.
- destruct H as (ms1 & _ & HP). exact (K ms1 HP).
- destruct H as (ms1 & _ & HP). exact (K ms1 HP).
Qed.
Lemma aimp_prefix {R} (t : aprog ptr R) Q ms :
evt segs (fun ms' => aimp t Q ms') ms -> aimp t Q ms.
Proof. intros H. eapply aimp_evt; [exact H|]. intros ms' H'; exact H'. Qed.

Lemma aimp_mono {R} (t : aprog ptr R) (Q Q' : R -> machine_state -> Prop) ms :
aimp t Q ms -> (forall r ms', Q r ms' -> Q' r ms') -> aimp t Q' ms.
Proof. destruct t; cbn; auto. intros H K. eapply evt_mono; eauto. Qed.

Lemma aimp_apbind {A B} (t : aprog ptr A) (f : A -> aprog ptr B) Q ms :
aimp t (fun a ms' => aimp (f a) Q ms') ms -> aimp (apbind t f) Q ms.
Proof.
destruct t as [a| |n k|p k]; cbn; intros H.
- eapply aimp_prefix. exact H.
- exact I.
- destruct H.
- destruct H.
Qed.

Lemma aimp_ateq {A} (t u : aprog ptr A) : ateq t u -> forall Q ms, aimp t Q ms <-> aimp u Q ms.
Proof. induction 1; intros Q ms; cbn; tauto. Qed.

Section StateLayer.
Context {St : Type}.
Local Notation AM := (AM ptr St).
Implicit Types (σ : St).

Lemma aimp_abind {A B} (m : AM A) (f : A -> AM B) σ Q ms :
aimp (m σ) (fun r ms' => aimp (f (fst r) (snd r)) Q ms') ms -> aimp (abind m f σ) Q ms.
Proof. intros H. unfold abind. apply aimp_apbind. exact H. Qed.

Lemma aimp_abind_assoc {A B C} (m : AM A) (f : A -> AM B) (g : B -> AM C) σ Q ms :
aimp (abind m (fun a => abind (f a) g) σ) Q ms -> aimp (abind (abind m f) g σ) Q ms.
Proof.
intros H. unfold abind in *.
apply (proj2 (aimp_ateq _ _ (apbind_assoc (m σ) (fun p => f (fst p) (snd p)) (fun p => g (fst p) (snd p))) Q ms)).
exact H.
Qed.

Lemma aimp_aret {A} (a : A) σ Q ms : evt segs (Q (a, σ)) ms -> aimp (aret a σ) Q ms.
Proof. exact (fun H => H). Qed.
Lemma aimp_aunr {A} σ (Q : A * St -> machine_state -> Prop) ms : aimp (aunr (A:=A) σ) Q ms.
Proof. exact I. Qed.

Lemma aimp_head_ret {A} (m : AM A) σ σ' (a : A) Q ms :
m σ = ARet (a, σ') -> evt segs (Q (a, σ')) ms -> aimp (m σ) Q ms.
Proof. intros -> H. exact H. Qed.
Lemma aimp_head_unr {A} (m : AM A) σ (Q : A * St -> machine_state -> Prop) ms :
m σ = AUnr -> aimp (m σ) Q ms.
Proof. intros ->. exact I. Qed.

Lemma aimp_aloop_S {X R} fuel (body : X -> AM (X + R)) x σ Q ms :
aimp (body x σ) (fun r ms' => match fst r with
| inl x' => aimp (aloop fuel body x' (snd r)) Q ms'
| inr v => evt segs (Q (v, snd r)) ms'
end) ms ->
aimp (aloop (S fuel) body x σ) Q ms.
Proof.
intros H. cbn [aloop]. apply aimp_abind. eapply aimp_mono; [exact H|].
intros [[x'|v] σ'] ms'; cbn [fst snd]; intros H'; [exact H'|]. exact H'.
Qed.
Lemma aimp_aloop_O {X R} (body : X -> AM (X + R)) x σ Q ms : aimp (aloop O body x σ) Q ms.
Proof. exact I. Qed.

Lemma aimp_abind_aloop_S {X R B} fuel (body : X -> AM (X + R)) (x : X) (K : R -> AM B) σ Q ms :
aimp (abind (body x) (fun r σ' => abind (match r with inl x' => aloop fuel body x' | inr v => aret v end) K σ') σ) Q ms ->
aimp (abind (aloop (S fuel) body x) K σ) Q ms.
Proof. intros H. cbn [aloop]. apply aimp_abind_assoc. exact H. Qed.
Lemma aimp_abind_aloop_O {X R B} (body : X -> AM (X + R)) (x : X) (K : R -> AM B) σ Q ms :
aimp (abind (aloop O body x) K σ) Q ms.
Proof. cbn [aloop]. rewrite abind_aunr_eq. exact I. Qed.
End StateLayer.
End Pure.

Arguments aimp segs {ptr R} t Q ms.

Section BridgeP.
Variable segs : list Segment.

End BridgeP.

Ltac pprefix := apply aimp_prefix.
Ltac phere := apply evt_done.

Ltac pstep1 :=
lazymatch goal with

| |- aimp _ (abind (abind _ _) _ _) _ _ => apply aimp_abind_assoc
| |- aimp _ (abind aget _ _) _ _ => rewrite abind_aget_eq
| |- aimp _ (abind (aput _) _ _) _ _ => rewrite abind_aput_eq
| |- aimp _ (abind (aupd _) _ _) _ _ => rewrite abind_aupd_eq
| |- aimp _ (abind (aret _) _ _) _ _ => rewrite abind_aret_eq
| |- aimp _ (abind aunr _ _) _ _ => rewrite abind_aunr_eq; apply aimp_AUnr
| |- aimp _ (abind (aassert ?b) _ _) _ _ =>
first [ rewrite (abind_aassert_true b) by massert_tac
| fail 1 "pstep: cannot prove the assertion" b "(use passert_case or prove it first)" ]
| |- aimp _ (abind (awhen ?b _) _ _) _ _ =>
first [ rewrite (abind_awhen_true b) by massert_tac
| rewrite (abind_awhen_false b) by massert_tac
| fail 1 "pstep: cannot decide the awhen guard" b ]
| |- aimp _ (abind ?m _ ?σ) _ _ =>
first [ erewrite (abind_eq_ret m) by (solve [eauto 4 with mstep_eqs])
| erewrite (abind_eq_unr m) by (solve [eauto 4 with mstep_eqs]); apply aimp_AUnr
| fail 1 "pstep: no equation for the head" m "(prove [" m σ "= ARet ..] and rewrite abind_eq_ret, or unfold it)" ]

| |- aimp _ (aret _ _) _ _ => apply aimp_aret
| |- aimp _ (ARet _) _ _ => apply aimp_ARet
| |- aimp _ (aunr _) _ _ => apply aimp_aunr
| |- aimp _ AUnr _ _ => apply aimp_AUnr
| |- aimp _ (aget ?σ) _ _ => change (aget σ) with (ARet (σ, σ)); apply aimp_ARet
| |- aimp _ (aput ?σ1 ?σ) _ _ => change (aput σ1 σ) with (ARet (tt, σ1)); apply aimp_ARet
| |- aimp _ (aupd ?g ?σ) _ _ => change (aupd g σ) with (ARet (tt, g σ)); apply aimp_ARet
| |- aimp _ (aassert ?b ?σ) _ _ =>
first [ rewrite (aassert_true_eq b σ) by massert_tac; apply aimp_ARet
| fail 1 "pstep: cannot prove the assertion" b ]
| |- aimp _ (AMalloc _ _) _ _ => fail "pstep: at a malloc node — not an allocation-free tree"
| |- aimp _ (AFree _ _) _ _ => fail "pstep: at a free node — not an allocation-free tree"
| |- aimp _ (?m ?σ) _ _ =>
first [ eapply (aimp_head_unr _ m σ); solve [eauto 4 with mstep_eqs]
| eapply (aimp_head_ret _ m σ); [solve [eauto 4 with mstep_eqs] | ]
| fail 1 "pstep: no equation for" m ]
| |- _ => fail "pstep: goal is not [aimp _ _ _ _]"
end.

Ltac pclean := cbn beta iota delta [fst snd].
Ltac pstep := pstep1; try pclean.
Ltac psteps := repeat pstep.

Ltac passert_case H :=
lazymatch goal with
| |- aimp _ (abind (aassert ?b) _ _) _ _ =>
destruct b eqn:H; [ rewrite (abind_aassert_true _ _ _ eq_refl) | rewrite (abind_aassert_false _ _ _ eq_refl); apply aimp_AUnr ]
end.

Ltac pret := first [ apply aimp_aret | apply aimp_ARet ].

Ltac ploop_S := first [ apply aimp_aloop_S | eapply aimp_abind_aloop_S ].
Ltac ploop_O := first [ apply aimp_aloop_O | eapply aimp_abind_aloop_O ].
Ltac ploop k := destruct k as [|k]; [ ploop_O | ploop_S ].
End Mq0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoAA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QoAA.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Section Pure.
Variable segs : list Segment.
Context {ptr : Type}.

Definition aimp {R} (t : aprog ptr R) (Q : R -> machine_state -> Prop) (ms : machine_state) : Prop :=
match t with
| ARet r => evt segs (Q r) ms
| AUnr => True
| AMalloc _ _ => False
| AFree _ _ => False
end.

Lemma aimp_ARet {R} (r : R) Q ms : evt segs (Q r) ms -> aimp (ARet r) Q ms.
Proof. exact (fun H => H). Qed.
Lemma aimp_AUnr {R} (Q : R -> machine_state -> Prop) ms : aimp AUnr Q ms.
Proof. exact I. Qed.

Lemma aimp_evt {R} (t : aprog ptr R) Q P ms :
evt segs P ms -> (forall ms', P ms' -> aimp t Q ms') -> aimp t Q ms.
Proof.
intros H K. destruct t as [r| |n k|p k]; cbn.
- eapply evt_cut; [exact H|]. intros ms' HP. exact (K ms' HP).
- exact I.
- destruct H as (ms1 & _ & HP). exact (K ms1 HP).
- destruct H as (ms1 & _ & HP). exact (K ms1 HP).
Qed.
Lemma aimp_prefix {R} (t : aprog ptr R) Q ms :
evt segs (fun ms' => aimp t Q ms') ms -> aimp t Q ms.
Proof. intros H. eapply aimp_evt; [exact H|]. intros ms' H'; exact H'. Qed.

Lemma aimp_mono {R} (t : aprog ptr R) (Q Q' : R -> machine_state -> Prop) ms :
aimp t Q ms -> (forall r ms', Q r ms' -> Q' r ms') -> aimp t Q' ms.
Proof. destruct t; cbn; auto. intros H K. eapply evt_mono; eauto. Qed.

Lemma aimp_apbind {A B} (t : aprog ptr A) (f : A -> aprog ptr B) Q ms :
aimp t (fun a ms' => aimp (f a) Q ms') ms -> aimp (apbind t f) Q ms.
Proof.
destruct t as [a| |n k|p k]; cbn; intros H.
- eapply aimp_prefix. exact H.
- exact I.
- destruct H.
- destruct H.
Qed.

Lemma aimp_ateq {A} (t u : aprog ptr A) : ateq t u -> forall Q ms, aimp t Q ms <-> aimp u Q ms.
Proof. induction 1; intros Q ms; cbn; tauto. Qed.

Section StateLayer.
Context {St : Type}.
Local Notation AM := (AM ptr St).
Implicit Types (σ : St).

Lemma aimp_abind {A B} (m : AM A) (f : A -> AM B) σ Q ms :
aimp (m σ) (fun r ms' => aimp (f (fst r) (snd r)) Q ms') ms -> aimp (abind m f σ) Q ms.
Proof. intros H. unfold abind. apply aimp_apbind. exact H. Qed.

Lemma aimp_abind_assoc {A B C} (m : AM A) (f : A -> AM B) (g : B -> AM C) σ Q ms :
aimp (abind m (fun a => abind (f a) g) σ) Q ms -> aimp (abind (abind m f) g σ) Q ms.
Proof.
intros H. unfold abind in *.
apply (proj2 (aimp_ateq _ _ (apbind_assoc (m σ) (fun p => f (fst p) (snd p)) (fun p => g (fst p) (snd p))) Q ms)).
exact H.
Qed.

Lemma aimp_aret {A} (a : A) σ Q ms : evt segs (Q (a, σ)) ms -> aimp (aret a σ) Q ms.
Proof. exact (fun H => H). Qed.
Lemma aimp_aunr {A} σ (Q : A * St -> machine_state -> Prop) ms : aimp (aunr (A:=A) σ) Q ms.
Proof. exact I. Qed.

Lemma aimp_head_ret {A} (m : AM A) σ σ' (a : A) Q ms :
m σ = ARet (a, σ') -> evt segs (Q (a, σ')) ms -> aimp (m σ) Q ms.
Proof. intros -> H. exact H. Qed.
Lemma aimp_head_unr {A} (m : AM A) σ (Q : A * St -> machine_state -> Prop) ms :
m σ = AUnr -> aimp (m σ) Q ms.
Proof. intros ->. exact I. Qed.

Lemma aimp_aloop_S {X R} fuel (body : X -> AM (X + R)) x σ Q ms :
aimp (body x σ) (fun r ms' => match fst r with
| inl x' => aimp (aloop fuel body x' (snd r)) Q ms'
| inr v => evt segs (Q (v, snd r)) ms'
end) ms ->
aimp (aloop (S fuel) body x σ) Q ms.
Proof.
intros H. cbn [aloop]. apply aimp_abind. eapply aimp_mono; [exact H|].
intros [[x'|v] σ'] ms'; cbn [fst snd]; intros H'; [exact H'|]. exact H'.
Qed.
Lemma aimp_aloop_O {X R} (body : X -> AM (X + R)) x σ Q ms : aimp (aloop O body x σ) Q ms.
Proof. exact I. Qed.

Lemma aimp_abind_aloop_S {X R B} fuel (body : X -> AM (X + R)) (x : X) (K : R -> AM B) σ Q ms :
aimp (abind (body x) (fun r σ' => abind (match r with inl x' => aloop fuel body x' | inr v => aret v end) K σ') σ) Q ms ->
aimp (abind (aloop (S fuel) body x) K σ) Q ms.
Proof. intros H. cbn [aloop]. apply aimp_abind_assoc. exact H. Qed.
Lemma aimp_abind_aloop_O {X R B} (body : X -> AM (X + R)) (x : X) (K : R -> AM B) σ Q ms :
aimp (abind (aloop O body x) K σ) Q ms.
Proof. cbn [aloop]. rewrite abind_aunr_eq. exact I. Qed.
End StateLayer.
End Pure.

Arguments aimp segs {ptr R} t Q ms.

Section BridgeP.
Variable segs : list Segment.

End BridgeP.

Ltac pprefix := apply aimp_prefix.
Ltac phere := apply evt_done.

Ltac pstep1 :=
lazymatch goal with

| |- aimp _ (abind (abind _ _) _ _) _ _ => apply aimp_abind_assoc
| |- aimp _ (abind aget _ _) _ _ => rewrite abind_aget_eq
| |- aimp _ (abind (aput _) _ _) _ _ => rewrite abind_aput_eq
| |- aimp _ (abind (aupd _) _ _) _ _ => rewrite abind_aupd_eq
| |- aimp _ (abind (aret _) _ _) _ _ => rewrite abind_aret_eq
| |- aimp _ (abind aunr _ _) _ _ => rewrite abind_aunr_eq; apply aimp_AUnr
| |- aimp _ (abind (aassert ?b) _ _) _ _ =>
first [ rewrite (abind_aassert_true b) by massert_tac
| fail 1 "pstep: cannot prove the assertion" b "(use passert_case or prove it first)" ]
| |- aimp _ (abind (awhen ?b _) _ _) _ _ =>
first [ rewrite (abind_awhen_true b) by massert_tac
| rewrite (abind_awhen_false b) by massert_tac
| fail 1 "pstep: cannot decide the awhen guard" b ]
| |- aimp _ (abind ?m _ ?σ) _ _ =>
first [ erewrite (abind_eq_ret m) by (solve [eauto 4 with mstep_eqs])
| erewrite (abind_eq_unr m) by (solve [eauto 4 with mstep_eqs]); apply aimp_AUnr
| fail 1 "pstep: no equation for the head" m "(prove [" m σ "= ARet ..] and rewrite abind_eq_ret, or unfold it)" ]

| |- aimp _ (aret _ _) _ _ => apply aimp_aret
| |- aimp _ (ARet _) _ _ => apply aimp_ARet
| |- aimp _ (aunr _) _ _ => apply aimp_aunr
| |- aimp _ AUnr _ _ => apply aimp_AUnr
| |- aimp _ (aget ?σ) _ _ => change (aget σ) with (ARet (σ, σ)); apply aimp_ARet
| |- aimp _ (aput ?σ1 ?σ) _ _ => change (aput σ1 σ) with (ARet (tt, σ1)); apply aimp_ARet
| |- aimp _ (aupd ?g ?σ) _ _ => change (aupd g σ) with (ARet (tt, g σ)); apply aimp_ARet
| |- aimp _ (aassert ?b ?σ) _ _ =>
first [ rewrite (aassert_true_eq b σ) by massert_tac; apply aimp_ARet
| fail 1 "pstep: cannot prove the assertion" b ]
| |- aimp _ (AMalloc _ _) _ _ => fail "pstep: at a malloc node — not an allocation-free tree"
| |- aimp _ (AFree _ _) _ _ => fail "pstep: at a free node — not an allocation-free tree"
| |- aimp _ (?m ?σ) _ _ =>
first [ eapply (aimp_head_unr _ m σ); solve [eauto 4 with mstep_eqs]
| eapply (aimp_head_ret _ m σ); [solve [eauto 4 with mstep_eqs] | ]
| fail 1 "pstep: no equation for" m ]
| |- _ => fail "pstep: goal is not [aimp _ _ _ _]"
end.

Ltac pclean := cbn beta iota delta [fst snd].
Ltac pstep := pstep1; try pclean.
Ltac psteps := repeat pstep.

Ltac passert_case H :=
lazymatch goal with
| |- aimp _ (abind (aassert ?b) _ _) _ _ =>
destruct b eqn:H; [ rewrite (abind_aassert_true _ _ _ eq_refl) | rewrite (abind_aassert_false _ _ _ eq_refl); apply aimp_AUnr ]
end.

Ltac pret := first [ apply aimp_aret | apply aimp_ARet ].

Ltac ploop_S := first [ apply aimp_aloop_S | eapply aimp_abind_aloop_S ].
Ltac ploop_O := first [ apply aimp_aloop_O | eapply aimp_abind_aloop_O ].
Ltac ploop k := destruct k as [|k]; [ ploop_O | ploop_S ].
