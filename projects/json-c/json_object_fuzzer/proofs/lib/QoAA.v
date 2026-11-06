(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q67d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhzc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhzc.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Section Eqs.
Context {ptr St : Type}.
Local Notation AM := (@AM ptr St).

Lemma abind_aget_eq {B} (f : St -> AM B) (s : St) : abind aget f s = f s s.
Proof. reflexivity. Qed.
Lemma abind_aput_eq {B} (f : unit -> AM B) (s s1 : St) : abind (aput s1) f s = f tt s1.
Proof. reflexivity. Qed.
Lemma abind_aupd_eq {B} (g : St -> St) (f : unit -> AM B) (s : St) : abind (aupd g) f s = f tt (g s).
Proof. reflexivity. Qed.
Lemma abind_aret_eq {A B} (a : A) (f : A -> AM B) (s : St) : abind (aret a) f s = f a s.
Proof. reflexivity. Qed.
Lemma abind_aunr_eq {A B} (f : A -> AM B) (s : St) : abind (aunr (A:=A)) f s = AUnr.
Proof. reflexivity. Qed.
Lemma abind_aassert_true {B} (b : bool) (f : unit -> AM B) (s : St) : b = true -> abind (aassert b) f s = f tt s.
Proof. intros ->. reflexivity. Qed.
Lemma abind_aassert_false {B} (b : bool) (f : unit -> AM B) (s : St) : b = false -> abind (aassert b) f s = AUnr.
Proof. intros ->. reflexivity. Qed.
Lemma abind_awhen_true {B} (b : bool) (m : AM unit) (f : unit -> AM B) (s : St) : b = true -> abind (awhen b m) f s = abind m f s.
Proof. intros ->. reflexivity. Qed.
Lemma abind_awhen_false {B} (b : bool) (m : AM unit) (f : unit -> AM B) (s : St) : b = false -> abind (awhen b m) f s = f tt s.
Proof. intros ->. reflexivity. Qed.
Lemma aassert_true_eq (b : bool) (s : St) : b = true -> aassert (ptr:=ptr) b s = ARet (tt, s).
Proof. intros ->. reflexivity. Qed.

Lemma abind_eq_ret {A B} (m : AM A) (f : A -> AM B) (s s' : St) (a : A) :
m s = ARet (a, s') -> abind m f s = f a s'.
Proof. intros E. unfold abind. rewrite E. reflexivity. Qed.
Lemma abind_eq_unr {A B} (m : AM A) (f : A -> AM B) (s : St) :
m s = AUnr -> abind m f s = AUnr.
Proof. intros E. unfold abind. rewrite E. reflexivity. Qed.
Lemma abind_eq_free {A B} (m : AM A) (f : A -> AM B) (s s' : St) (p : ptr) (a : A) :
m s = AFree p (ARet (a, s')) -> abind m f s = AFree p (f a s').
Proof. intros E. unfold abind. rewrite E. reflexivity. Qed.

Lemma abind_amalloc_eq {B} n (f : option ptr -> AM B) (s : St) :
abind (amalloc n) f s = AMalloc n (fun r => f r s).
Proof. reflexivity. Qed.
Lemma abind_afree_eq {B} p (f : unit -> AM B) (s : St) :
abind (afree p) f s = AFree p (f tt s).
Proof. reflexivity. Qed.

End Eqs.

Section Machine.
Variable segs : list Segment.
Local Notation implM := (@Qpj5.Mq1.implM PState segs).

Lemma implM_prefix {A} (c : Qpj5.Mq1.M PState A) s Q ms :
evt segs (fun ms' => implM c s Q ms') ms -> implM c s Q ms.
Proof. intros H. eapply implM_evt; [exact H|]. intros ms' H'. exact H'. Qed.

Lemma implM_interp_ateq {A} (t u : aprog bptr A) :
ateq t u -> forall s Q ms, implM (interp t) s Q ms <-> implM (interp u) s Q ms.
Proof.
induction 1 as [a| |n k k' HK IH|p k k' HK IH]; intros s Q ms.
- tauto.
- tauto.
- cbn [interp]. split; intros H; apply implM_bind_inv in H; (eapply implM_bind; [exact H|]);
intros r s' ms' H'; cbn beta in H'; apply IH; exact H'.
- cbn [interp]. split; intros H; apply implM_bind_inv in H; (eapply implM_bind; [exact H|]);
intros r s' ms' H'; cbn beta in H'; apply IH; exact H'.
Qed.

Lemma implM_abind_assoc {St A B C} (m : AM bptr St A) (f : A -> AM bptr St B) (g : B -> AM bptr St C) (σ : St) s Q ms :
implM (interp (abind m (fun a => abind (f a) g) σ)) s Q ms ->
implM (interp (abind (abind m f) g σ)) s Q ms.
Proof.
intros H. unfold abind in *.
apply (proj2 (implM_interp_ateq _ _ (apbind_assoc (m σ) (fun p => f (fst p) (snd p)) (fun p => g (fst p) (snd p))) s Q ms)).
exact H.
Qed.

Lemma implM_aret {St A} (a : A) (σ : St) s Q ms :
evt segs (Q (a, σ) s) ms -> implM (interp (aret (ptr:=bptr) a σ)) s Q ms.
Proof. intros H. rewrite interp_aret. apply implM_ret. exact H. Qed.
Lemma implM_ARet {St A} (a : A) (σ : St) s Q ms :
evt segs (Q (a, σ) s) ms -> implM (interp (ARet (ptr:=bptr) (a, σ))) s Q ms.
Proof. intros H. cbn [interp]. apply implM_ret. exact H. Qed.

Lemma implM_head_ret {St A} (m : AM bptr St A) (σ σ' : St) (a : A) s Q ms :
m σ = ARet (a, σ') -> evt segs (Q (a, σ') s) ms -> implM (interp (m σ)) s Q ms.
Proof. intros -> H. cbn [interp]. apply implM_ret. exact H. Qed.
Lemma implM_head_unr {St A} (m : AM bptr St A) (σ : St) s (Q : A * St -> PState -> machine_state -> Prop) ms :
m σ = AUnr -> implM (interp (m σ)) s Q ms.
Proof. intros ->. cbn [interp]. apply implM_unr. Qed.

Lemma implM_AUnr {A} s Q ms : implM (interp (@AUnr bptr A)) s Q ms.
Proof. cbn [interp]. apply implM_unr. Qed.
Lemma implM_aunr {St A} (σ : St) s Q ms : implM (interp (aunr (ptr:=bptr) (St:=St) (A:=A) σ)) s Q ms.
Proof. apply implM_AUnr. Qed.

Lemma implM_AMalloc {A} n (k : option bptr -> aprog bptr A) s Q1 Q ms :
implM (raw_malloc n) s Q1 ms ->
(forall r s' ms', Q1 r s' ms' -> implM (interp (k r)) s' Q ms') ->
implM (interp (AMalloc n k)) s Q ms.
Proof. intros H K. cbn [interp]. eapply implM_bind; [exact H| exact K]. Qed.
Lemma implM_AFree {A} p (k : aprog bptr A) s Q1 Q ms :
implM (raw_free p) s Q1 ms ->
(forall r s' ms', Q1 r s' ms' -> implM (interp k) s' Q ms') ->
implM (interp (AFree p k)) s Q ms.
Proof. intros H K. cbn [interp]. eapply implM_bind; [exact H| intros r s' ms' H'; apply (K r); exact H']. Qed.

End Machine.

Create HintDb mstep_eqs discriminated.

Ltac mprefix := apply implM_prefix.
Ltac mhere := apply evt_done.

Ltac massert_tac :=
first [ assumption
| reflexivity
| symmetry; assumption
| solve [eauto 2 with mstep_eqs]
| solve [apply Is_true_eq_true; auto]
| lia ].

Ltac mstep_skip_ret m σ := fail.

Ltac mstep1 :=
lazymatch goal with

| |- Qpj5.Mq1.implM _ (interp (abind (abind _ _) _ _)) _ _ _ => apply implM_abind_assoc
| |- Qpj5.Mq1.implM _ (interp (abind aget _ _)) _ _ _ => rewrite abind_aget_eq
| |- Qpj5.Mq1.implM _ (interp (abind (aput _) _ _)) _ _ _ => rewrite abind_aput_eq
| |- Qpj5.Mq1.implM _ (interp (abind (aupd _) _ _)) _ _ _ => rewrite abind_aupd_eq
| |- Qpj5.Mq1.implM _ (interp (abind (aret _) _ _)) _ _ _ => rewrite abind_aret_eq
| |- Qpj5.Mq1.implM _ (interp (abind aunr _ _)) _ _ _ => rewrite abind_aunr_eq; apply implM_AUnr
| |- Qpj5.Mq1.implM _ (interp (abind (aassert ?b) _ _)) _ _ _ =>
first [ rewrite (abind_aassert_true b) by massert_tac
| fail 1 "mstep: cannot prove the assertion" b "(use massert_case or prove it first)" ]
| |- Qpj5.Mq1.implM _ (interp (abind (awhen ?b _) _ _)) _ _ _ =>
first [ rewrite (abind_awhen_true b) by massert_tac
| rewrite (abind_awhen_false b) by massert_tac
| fail 1 "mstep: cannot decide the awhen guard" b ]
| |- Qpj5.Mq1.implM _ (interp (abind ?m _ ?σ)) _ _ _ =>
first [ tryif mstep_skip_ret m σ then fail else erewrite (abind_eq_ret m) by (solve [eauto 4 with mstep_eqs])
| erewrite (abind_eq_unr m) by (solve [eauto 4 with mstep_eqs]); apply implM_AUnr
| erewrite (abind_eq_free m) by (solve [eauto 4 with mstep_eqs])
| fail 1 "mstep: no equation for the head" m "(prove [" m σ "= ARet ..] and rewrite abind_eq_ret, or unfold it)" ]

| |- Qpj5.Mq1.implM _ (interp (aret _ _)) _ _ _ => apply implM_aret
| |- Qpj5.Mq1.implM _ (interp (ARet (_, _))) _ _ _ => apply implM_ARet
| |- Qpj5.Mq1.implM _ (interp (aunr _)) _ _ _ => apply implM_aunr
| |- Qpj5.Mq1.implM _ (interp AUnr) _ _ _ => apply implM_AUnr
| |- Qpj5.Mq1.implM _ (interp (aget ?σ)) _ _ _ => change (aget σ) with (ARet (ptr:=bptr) (σ, σ)); apply implM_ARet
| |- Qpj5.Mq1.implM _ (interp (aput ?σ1 ?σ)) _ _ _ => change (aput σ1 σ) with (ARet (ptr:=bptr) (tt, σ1)); apply implM_ARet
| |- Qpj5.Mq1.implM _ (interp (aupd ?g ?σ)) _ _ _ => change (aupd g σ) with (ARet (ptr:=bptr) (tt, g σ)); apply implM_ARet
| |- Qpj5.Mq1.implM _ (interp (aassert ?b ?σ)) _ _ _ =>
first [ rewrite (aassert_true_eq b σ) by massert_tac; apply implM_ARet
| fail 1 "mstep: cannot prove the assertion" b ]
| |- Qpj5.Mq1.implM _ (interp (AMalloc _ _)) _ _ _ => fail "mstep: at a malloc node (use mbind_malloc / the malloc spec)"
| |- Qpj5.Mq1.implM _ (interp (AFree _ _)) _ _ _ => fail "mstep: at a free node (use mbind_free / the free spec)"
| |- Qpj5.Mq1.implM _ (interp (?m ?σ)) _ _ _ =>
first [ eapply (implM_head_unr _ m σ); solve [eauto 4 with mstep_eqs]
| eapply (implM_head_ret _ m σ); [solve [eauto 4 with mstep_eqs] | ]
| fail 1 "mstep: no equation for" m ]
| |- _ => fail "mstep: goal is not [implM _ (interp _) _ _ _]"
end.

Ltac mclean := cbn beta iota delta [fst snd].
Ltac mstep := mstep1; try mclean.
Ltac msteps := repeat mstep.

Ltac massert_case H :=
lazymatch goal with
| |- Qpj5.Mq1.implM _ (interp (abind (aassert ?b) _ _)) _ _ _ =>
destruct b eqn:H; [ rewrite (abind_aassert_true _ _ _ eq_refl) | rewrite (abind_aassert_false _ _ _ eq_refl); apply implM_AUnr ]
end.

Ltac mret := first [ apply implM_aret | apply implM_ARet ].

Ltac mbind_malloc :=
lazymatch goal with
| |- Qpj5.Mq1.implM _ (interp (abind (amalloc _) _ _)) _ _ _ => rewrite abind_amalloc_eq; eapply implM_AMalloc
| |- Qpj5.Mq1.implM _ (interp (amalloc ?n ?σ)) _ _ _ => change (amalloc n σ) with (AMalloc n (fun r => ARet (ptr:=bptr) (r, σ))); eapply implM_AMalloc
| |- Qpj5.Mq1.implM _ (interp (AMalloc _ _)) _ _ _ => eapply implM_AMalloc
end.
Ltac mbind_free :=
lazymatch goal with
| |- Qpj5.Mq1.implM _ (interp (abind (afree _) _ _)) _ _ _ => rewrite abind_afree_eq; eapply implM_AFree
| |- Qpj5.Mq1.implM _ (interp (afree ?p ?σ)) _ _ _ => change (afree p σ) with (AFree p (ARet (ptr:=bptr) (tt, σ))); eapply implM_AFree
| |- Qpj5.Mq1.implM _ (interp (AFree _ _)) _ _ _ => eapply implM_AFree
end.

Section Loops.
Context (segs : list Segment).
Local Notation implM := (@Qpj5.Mq1.implM PState segs).

Lemma implM_abind_aloop_S {St X R B} fuel (body : X -> AM bptr St (X + R)) (x : X) (K : R -> AM bptr St B) (σ : St) s Q ms :
implM (interp (abind (body x)
(fun r σ' => abind (match r with inl x' => aloop fuel body x' | inr v => aret v end) K σ') σ)) s Q ms ->
implM (interp (abind (aloop (S fuel) body x) K σ)) s Q ms.
Proof. intros H. cbn [aloop]. apply implM_abind_assoc. exact H. Qed.

Lemma implM_abind_aloop_O {St X R B} (body : X -> AM bptr St (X + R)) (x : X) (K : R -> AM bptr St B) (σ : St) s Q ms :
implM (interp (abind (aloop O body x) K σ)) s Q ms.
Proof. cbn [aloop]. rewrite abind_aunr_eq. apply implM_AUnr. Qed.

Lemma implM_aloop_O {St X R} (body : X -> AM bptr St (X + R)) (x : X) (σ : St) s Q ms :
implM (interp (aloop O body x σ)) s Q ms.
Proof. cbn [aloop]. apply implM_aunr. Qed.
End Loops.

Ltac mloop_S := first [ apply implM_interp_aloop_S | eapply implM_abind_aloop_S ].

Ltac mloop_O := first [ apply implM_aloop_O | eapply implM_abind_aloop_O ].

Ltac mloop k := destruct k as [|k]; [ mloop_O | mloop_S ].
