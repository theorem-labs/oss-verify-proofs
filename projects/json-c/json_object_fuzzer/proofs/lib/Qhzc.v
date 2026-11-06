(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q67d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgp5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgp5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7t6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7t6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoeL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoeL.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5fc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5fc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Definition bptr_eqb (a b : bptr) : bool := aptr_eqb (fst a) (fst b) && (snd a =? snd b).

Lemma bptr_eqb_spec : forall a b, bptr_eqb a b = true <-> a = b.
Proof.
intros [a1 a2] [b1 b2]. unfold bptr_eqb. cbn [fst snd]. rewrite andb_true_iff, aptr_eqb_eq, Z.eqb_eq.
split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma bptr_eqb_refl : forall a, bptr_eqb a a = true.
Proof. intros a. apply (proj2 (bptr_eqb_spec a a)). reflexivity. Qed.

Local Notation MP := (Qpj5.Mq1.M PState).

Fixpoint interp {A} (t : aprog bptr A) : MP A :=
match t with
| ARet a => mret a
| AUnr => munr
| AMalloc n k => mbind (raw_malloc n) (fun r => interp (k r))
| AFree p k => mbind (raw_free p) (fun _ => interp k)
end.

Section StateLayer.
Context {St : Type}.
Lemma interp_aret {A} (a : A) (s : St) : interp (aret a s) = mret (a, s). Proof. reflexivity. Qed.

Lemma interp_aloop_S {X R} fuel (body : X -> AM bptr St (X + R)) x (s : St) :
interp (aloop (S fuel) body x s)
= interp (abind (body x) (fun r => match r with inl x' => aloop fuel body x' | inr v => aret v end) s).
Proof. reflexivity. Qed.

End StateLayer.

Section Machine.
Variable segs : list Segment.
Local Notation impl := (Qc6I.impl segs (at_node segs)).
Local Notation implM := (@Qpj5.Mq1.implM PState segs).

Lemma impl_bind_inv {R S} (t : itree node R) (f : R -> itree node S) Q ms :
impl (Qc6I.bind node t f) Q ms -> impl t (fun r ms' => impl (f r) Q ms') ms.
Proof.
revert ms. induction t as [r|n k IH]; intros ms H; cbn [Qc6I.bind] in H; cbn.
- apply evt_done. exact H.
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
Qed.

Lemma impl_ebind_inv {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) Q ms :
impl (ebind t f) (epost Q) ms -> impl t (epost (fun a ms' => impl (f a) (epost Q) ms')) ms.
Proof.
intros H. unfold ebind in H. apply impl_bind_inv in H.
eapply impl_mono; [exact H|]. intros [|a] ms'; cbn; auto.
Qed.

Lemma implM_bind_inv {A B} (m : MP A) (f : A -> MP B) s Q ms :
implM (mbind m f) s Q ms -> implM m s (fun a s' ms' => implM (f a) s' Q ms') ms.
Proof.
intros H. unfold Qpj5.Mq1.implM, mbind in *. apply impl_ebind_inv in H.
eapply impl_epost_mono; [exact H|]. intros [a s'] ms'; cbn. exact (fun K => K).
Qed.

Lemma implM_ret_inv {A} (a : A) s Q ms : implM (mret a) s Q ms -> evt segs (Q a s) ms.
Proof. intros H. exact H. Qed.

Lemma implM_interp_apbind {A B} (m : aprog bptr A) (f : A -> aprog bptr B) :
forall s Q1 Q ms,
implM (interp m) s Q1 ms ->
(forall a s' ms', Q1 a s' ms' -> implM (interp (f a)) s' Q ms') ->
implM (interp (apbind m f)) s Q ms.
Proof.
induction m as [a| |n k IH|p k IH]; intros s Q1 Q ms Hm Hf; cbn [apbind interp].
- apply implM_ret_inv in Hm. eapply implM_evt; [exact Hm|]. intros ms' H'. exact (Hf _ _ _ H').
- apply implM_unr.
- cbn [interp] in Hm. apply implM_bind_inv in Hm. eapply implM_bind; [exact Hm|].
intros r s' ms' H'. cbn beta in H'. eapply IH; [exact H'| exact Hf].
- cbn [interp] in Hm. apply implM_bind_inv in Hm. eapply implM_bind; [exact Hm|].
intros r s' ms' H'. cbn beta in H'. eapply IH; [exact H'| exact Hf].
Qed.

Lemma implM_interp_abind {St A B} (m : AM bptr St A) (f : A -> AM bptr St B) (st : St) :
forall s Q1 Q ms,
implM (interp (m st)) s Q1 ms ->
(forall (r : A * St) s' ms', Q1 r s' ms' -> implM (interp (f (fst r) (snd r))) s' Q ms') ->
implM (interp (abind m f st)) s Q ms.
Proof. intros s Q1 Q ms Hm Hf. unfold abind. eapply implM_interp_apbind; [exact Hm|]. intros [a st'] s' ms' H'. exact (Hf _ _ _ H'). Qed.

Lemma implM_interp_aloop_S {St X R} fuel (body : X -> AM bptr St (X + R)) x (st : St) s Q ms :
implM (interp (body x st)) s
(fun r s' ms' => match fst r with
| inl x' => implM (interp (aloop fuel body x' (snd r))) s' Q ms'
| inr v => evt segs (Q (v, snd r) s') ms'
end) ms ->
implM (interp (aloop (S fuel) body x st)) s Q ms.
Proof.
intros H. rewrite interp_aloop_S. eapply implM_interp_abind; [exact H|].
intros [[x'|v] st'] s' ms' H'; cbn [fst snd] in H' |- *; [exact H'|].
rewrite interp_aret. apply implM_ret. exact H'.
Qed.
End Machine.

