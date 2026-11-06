(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFfj.v (donor image sha256 7093581aab04), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0s YK0i YK15 YP09 YO0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Variable segs : list Segment.
Lemma amreal_after_SRr {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
SRr segs W c (fun W1 c1 => amreal segs t W1 c1 Q) -> amreal segs t W c Q.
Proof.
intros t W c Q H. destruct t as [r | q snap k | pc | f]; cbn [amreal] in *.
- eapply SRr_bind; [exact H|]. intros W' c' _ HQ. exact HQ.
- eapply SRr_bind; [exact H|]. intros W' c' _ HQ. exact HQ.
- intros HI. apply (H HI t_nil). intros W' c' _ HI' HQ. exact (HQ HI').
- exact I.
Qed.
Lemma amreal_bind {A R} : forall (t : itree astate A) (f : A -> itree astate R) W c (Q : R -> world segs -> config -> Prop),
amreal segs t W c (fun a W1 c1 => amreal segs (f a) W1 c1 Q) -> amreal segs (ibind t f) W c Q.
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros f W c Q H; cbn [ibind amreal] in *.
- exact (amreal_after_SRr _ _ _ _ H).
- eapply SRr_mono; [exact H|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; apply IH; exact (H8 i Hi)).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. apply IH. exact HR.
- exact H.
- exact I.
Qed.
Lemma amreal_mbind {A R} : forall (m : M A) (g : A -> M R) s W c (Q : R * astate -> world segs -> config -> Prop),
amreal segs (m s) W c (fun r W1 c1 => amreal segs (g (fst r) (snd r)) W1 c1 Q) -> amreal segs (bind m g s) W c Q.
Proof.
intros m g s W c Q H. unfold bind. apply amreal_bind. eapply amreal_mono; [|exact H]. intros [a s'] W' c' HR. exact HR.
Qed.
End b.
