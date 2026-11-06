(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO0j.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK15 YM02.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YO0i YO0f YO0g YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0d_cf YO03_cf.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition OKC {A} (X : Z) (P : A -> Prop) (t : itree astate A) : Prop := roomcf X t /\ leaves P t.
Lemma OKC_bind_y {A B} X (P : A * astate -> Prop) (Q : B * astate -> Prop) (m : M A) (f : A -> M B) s :
OKC X P (m s) -> (forall a s' tr, yields (m s) tr (a, s') -> P (a, s') -> OKC X Q (f a s')) -> OKC X Q (bind m f s).
Proof using.
intros [Hr Hl] Hf. unfold bind. split.
- eapply roomcf_ibind_yields; [exact Hr | exact Hl |]. intros tr [a s'] Hy HP. apply (proj1 (Hf a s' tr Hy HP)).
- eapply leaves_ibind_yields; [exact Hl|]. intros tr [a s'] Hy HP. apply (proj2 (Hf a s' tr Hy HP)).
Qed.
Lemma OKC_mono {A} X (P Q : A -> Prop) t : (forall a, P a -> Q a) -> OKC X P t -> OKC X Q t.
Proof using. intros H [Hr Hl]. split; [exact Hr | eapply leaves_mono; eauto]. Qed.
Lemma OKC_ret {A} X (a : A) s (Q : A * astate -> Prop) : Q (a, s) -> OKC X Q (ret a s).
Proof using. intros H. split; [exact I | exact H]. Qed.
Lemma OKC_fail {A} X f s (Q : A * astate -> Prop) : OKC X Q (fail f s).
Proof using. split; exact I. Qed.
Lemma OKC_modify X f s (Q : unit * astate -> Prop) : Q (tt, f s) -> OKC X Q (modify f s).
Proof using. intros H. split; [exact I | exact H]. Qed.
Lemma OKC_if {A} X (c : bool) (m1 m2 : M A) s Q : OKC X Q (m1 s) -> OKC X Q (m2 s) -> OKC X Q ((if c then m1 else m2) s).
Proof using. destruct c; auto. Qed.
Lemma OKC_ask_room X q s (Q : bool * astate -> Prop) :
(charged q = true -> live_bytes s + req_len q <= X) -> (forall b, Q (b, s)) -> OKC X Q (ask q s).
Proof using.
intros Hg HQ. split.
- cbn. split; [exact Hg | intros; exact I].
- cbn. intros z _. apply HQ.
Qed.
Lemma OKC_ask_free X q s (Q : bool * astate -> Prop) :
charged q = false -> (forall b, Q (b, s)) -> OKC X Q (ask q s).
Proof using. intros Hq HQ. apply OKC_ask_room; [intros E; rewrite Hq in E; discriminate E | exact HQ]. Qed.
Lemma leaves_TT {A} (t : itree astate A) : leaves (fun _ => True) t.
Proof using. induction t as [a | q snap k IH | e]; cbn; [exact I | intros z _; apply IH | exact I]. Qed.
Lemma OKC_presR_TT {A} X (m : M A) s : presR m -> OKC X (fun _ => True) (m s).
Proof using. intros H. split; [exact (H X s) | apply leaves_TT]. Qed.
End j.
Ltac x_get := match goal with |- OKC ?X ?P (bind get ?k ?s0) => change (OKC X P (k s0 s0)); cbv beta end.
Ltac x_put := match goal with |- OKC ?X ?P (bind (put ?s1) ?k ?s0) => change (OKC X P (k tt s1)); cbv beta end.
Ltac x_modify := match goal with |- OKC ?X ?P (bind (modify ?f) ?k ?s0) => change (OKC X P (k tt (f s0))); cbv beta end.
Ltac x_ret := match goal with |- OKC ?X ?P (bind (ret ?a) ?k ?s0) => change (OKC X P (k a s0)); cbv beta end.
Ltac rq_get H := match type of H with reqs_ok (bind get ?k ?s0) => change (reqs_ok (k s0 s0)) in H; cbv beta in H end.
Ltac rq_put H := match type of H with reqs_ok (bind (put ?s1) ?k ?s0) => change (reqs_ok (k tt s1)) in H; cbv beta in H end.
Ltac rq_modify H := match type of H with reqs_ok (bind (modify ?f) ?k ?s0) => change (reqs_ok (k tt (f s0))) in H; cbv beta in H end.
Ltac rq_bind H Hm Hf := pose proof (reqs_ok_mbind_inv _ _ _ H) as [Hm Hf]; clear H.
Ltac rq_new_region H :=
match type of H with reqs_ok (bind (new_region ?k ?len) ?K ?s0) =>
change (reqs_ok (K (length (st_regions s0)) (set_regions (st_regions s0 ++ [mkRegion k len [] true]) s0))) in H end.
