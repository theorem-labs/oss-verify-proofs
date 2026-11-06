(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK0j YK15 YQ0b YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Variable segs : list Segment.
Lemma amreal_after_SRr {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
SRr segs W c (fun W1 c1 => amreal segs t W1 c1 Q) -> amreal segs t W c Q.
Proof.
intros t W c Q H. eapply amreal_SRr_pre; [img_try (img_exact H)|]. intros W' c' _ HQ. img_exact HQ.
Qed.
Lemma amrealE_after_SRrF {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
SRrF segs W c (fun W1 c1 => amrealE segs t W1 c1 Q) -> amrealE segs t W c Q.
Proof.
intros t W c Q H. eapply amrealE_SRr_pre; [img_try (img_exact H)|]. intros W' c' _ HQ. img_exact HQ.
Qed.
Lemma amreal_bind {A R} : forall (t : itree astate A) (f : A -> itree astate R) W c (Q : R -> world segs -> config -> Prop),
amreal segs t W c (fun a W1 c1 => amreal segs (f a) W1 c1 Q) -> amreal segs (ibind t f) W c Q.
Proof.
intros t f W c Q H. eapply amreal_ibind; [img_try (img_exact H)|]. intros a W' c' HP. img_exact HP.
Qed.
Lemma amrealE_bind {A R} : forall (t : itree astate A) (f : A -> itree astate R) W c (Q : R -> world segs -> config -> Prop),
amrealE segs t W c (fun a W1 c1 => amrealE segs (f a) W1 c1 Q) -> amrealE segs (ibind t f) W c Q.
Proof.
intros t f W c Q H. eapply amrealE_ibind; [img_try (img_exact H)|]. intros a W' c' HP. img_exact HP.
Qed.
Lemma amreal_mbind {A R} : forall (m : M A) (g : A -> M R) s W c (Q : R * astate -> world segs -> config -> Prop),
amreal segs (m s) W c (fun r W1 c1 => amreal segs (g (fst r) (snd r)) W1 c1 Q) -> amreal segs (bind m g s) W c Q.
Proof.
intros m g s W c Q H. unfold bind. img_apply amreal_bind. eapply amreal_mono; [|img_try (img_exact H)]. intros [a s'] W' c' HR. img_exact HR.
Qed.
Lemma amrealE_mbind_ {A R} : forall (m : M A) (g : A -> M R) s W c (Q : R * astate -> world segs -> config -> Prop),
amrealE segs (m s) W c (fun r W1 c1 => amrealE segs (g (fst r) (snd r)) W1 c1 Q) -> amrealE segs (bind m g s) W c Q.
Proof.
intros m g s W c Q H. unfold bind. img_apply amrealE_bind. eapply amrealE_mono; [|img_try (img_exact H)]. intros [a s'] W' c' HR. img_exact HR.
Qed.
End b.
