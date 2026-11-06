(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Fixpoint in_leaves {R} (t : itree node R) (r : R) : Prop :=
match t with
| Ret r' => r' = r
| Vis n k => exists rsp, in_leaves (k rsp) r
end.

Lemma in_leaves_bind : forall {A B} (t : itree node A) (f : A -> itree node B) r,
in_leaves (X1bs.bind node t f) r -> exists a, in_leaves t a /\ in_leaves (f a) r.
Proof.
intros A B t. induction t as [a|n k IH]; intros f r H; cbn in *.
- exists a. auto.
- destruct H as [rsp H]. destruct (IH rsp f r H) as (a & Ha & Hr). exists a. split; [exists rsp; exact Ha| exact Hr].
Qed.

Lemma in_leaves_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) b,
in_leaves (ebind t f) (Ok b) -> exists a, in_leaves t (Ok a) /\ in_leaves (f a) (Ok b).
Proof.
intros A B t f b H. unfold ebind in H. apply in_leaves_bind in H. destruct H as ([|a] & Ha & Hb); cbn in Hb.
- discriminate Hb.
- exists a. auto.
Qed.

Lemma in_leaves_mbind : forall {St A B : Type} (m : M St A) (f : A -> M St B) (s : St) (b : B) s',
in_leaves (mbind m f s) (Ok (b, s')) -> exists a s1, in_leaves (m s) (Ok (a, s1)) /\ in_leaves (f a s1) (Ok (b, s')).
Proof.
intros St A B m f s b s' H. unfold mbind in H. apply in_leaves_ebind in H. destruct H as ([a s1] & H1 & H2). exists a, s1. auto.
Qed.

Lemma in_leaves_mret : forall {St A : Type} (a : A) (s : St) r, in_leaves (mret (St:=St) a s) r -> r = Ok (a, s).
Proof. intros St A a s r H. cbn in H. symmetry. exact H. Qed.

Section WithSegs.
Context {RCEIL : RunCeiling}.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.

#[using="Type"] Lemma impl_leaves : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) ms,
impl segs at_node t Q ms -> impl segs at_node t (fun r ms' => Q r ms' /\ in_leaves t r) ms.
Proof.
intros R t. induction t as [r|n k IH]; intros Q ms H; cbn in *.
- eapply evt_mono; [exact H|]. intros ms' HQ. auto.
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp.
eapply impl_mono; [apply IH; apply Hk|]. intros r ms' [HQ HL]. split; [exact HQ|]. exists rsp. exact HL.
Qed.

End WithSegs.

Lemma implM_leaves : forall segs {St A : Type} (m : M St A) (s : St) (Q : A -> St -> machine_state -> Prop) ms,
implM segs m s Q ms -> implM segs m s (fun a s' ms' => Q a s' ms' /\ in_leaves (m s) (Ok (a, s'))) ms.
Proof.
intros segs St A m s Q ms H. unfold implM in *. eapply impl_mono; [apply impl_leaves; exact H|].
intros [|[a s']] ms'; cbn; auto.
Qed.
